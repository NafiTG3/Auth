import os
import re
import hmac
import time
import json
import struct
import base64
import hashlib
import sqlite3
import logging
import datetime
from io import BytesIO
from urllib.parse import urlparse, parse_qs, unquote

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    ApplicationBuilder, CommandHandler, CallbackQueryHandler,
    MessageHandler, ConversationHandler, ContextTypes, filters
)
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from pyzbar.pyzbar import decode as qr_decode
from PIL import Image

logging.basicConfig(format="%(asctime)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger(__name__)

# ── States ────────────────────────────────────────────────
(
    AUTH_MENU,
    SIGNUP_PASSWORD, SIGNUP_CONFIRM,
    LOGIN_ID, LOGIN_PASSWORD,
    TOTP_MENU,
    ADD_WAITING, ADD_MANUAL_NAME, ADD_MANUAL_SECRET,
    EDIT_PICK, EDIT_ACTION, EDIT_RENAME_INPUT,
    CHANGE_PW_OLD, CHANGE_PW_NEW, CHANGE_PW_CONFIRM,
    DELETE_ACCOUNT_CONFIRM,
    EXPORT_PW_INPUT, IMPORT_WAITING,
    TZ_INPUT,
) = range(19)

DB_PATH     = os.environ.get("DB_PATH", "auth.db")
SERVER_KEY  = os.environ.get("ENCRYPTION_KEY", "").encode()
PBKDF2_ITER = 1_000_000   # 1 million iterations

# ── DB ────────────────────────────────────────────────────
def get_db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    with get_db() as conn:
        conn.execute("""CREATE TABLE IF NOT EXISTS users (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            vault_id      TEXT    UNIQUE NOT NULL,
            telegram_id   INTEGER UNIQUE NOT NULL,
            password_hash BLOB    NOT NULL,
            pw_salt       BLOB    NOT NULL,
            timezone      TEXT    DEFAULT 'UTC',
            created_at    INTEGER DEFAULT (strftime('%s','now')))""")
        conn.execute("""CREATE TABLE IF NOT EXISTS sessions (
            telegram_id INTEGER PRIMARY KEY,
            vault_id    TEXT    NOT NULL,
            created_at  INTEGER DEFAULT (strftime('%s','now')))""")
        conn.execute("""CREATE TABLE IF NOT EXISTS totp_accounts (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            vault_id   TEXT NOT NULL,
            name       TEXT NOT NULL,
            issuer     TEXT,
            secret_enc BLOB NOT NULL,
            salt       BLOB NOT NULL,
            iv         BLOB NOT NULL,
            created_at INTEGER DEFAULT (strftime('%s','now')))""")
        conn.commit()

# ── Crypto ────────────────────────────────────────────────
def generate_vault_id(telegram_id: int) -> str:
    """12-char cryptographic hash from telegram_id + SERVER_KEY."""
    raw = hashlib.sha256(
        f"bv_{telegram_id}_v2".encode() + SERVER_KEY
    ).digest()
    # Base62 alphabet for clean readable hash
    alphabet = "abcdefghijklmnopqrstuvwxyz0123456789"
    num = int.from_bytes(raw, "big")
    chars = []
    for _ in range(12):
        chars.append(alphabet[num % len(alphabet)])
        num //= len(alphabet)
    return "".join(chars)

def hash_password(password: str, salt: bytes) -> bytes:
    kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=PBKDF2_ITER)
    return kdf.derive(password.encode())

def derive_enc_key(password: str, vault_id: str, salt: bytes) -> bytes:
    material = (password + vault_id).encode() + SERVER_KEY
    kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=PBKDF2_ITER)
    return kdf.derive(material)

def encrypt_secret(secret: str, password: str, vault_id: str):
    salt = os.urandom(16); iv = os.urandom(12)
    ct   = AESGCM(derive_enc_key(password, vault_id, salt)).encrypt(iv, secret.encode(), None)
    return ct, salt, iv

def decrypt_secret(ct, salt, iv, password, vault_id) -> str:
    return AESGCM(derive_enc_key(password, vault_id, bytes(salt))).decrypt(bytes(iv), bytes(ct), None).decode()

# ── TOTP ──────────────────────────────────────────────────
def clean_secret(s: str) -> str:
    """Normalize secret: strip spaces, dashes, dots; uppercase."""
    return re.sub(r"[\s\-\.\,]", "", s).upper()

def _b32(s: str) -> bytes:
    s = clean_secret(s)
    return base64.b32decode(s + "=" * ((8 - len(s) % 8) % 8))

def validate_secret(s: str) -> tuple[bool, str]:
    """Returns (is_valid, cleaned_secret). Tries to auto-fix common issues."""
    cleaned = clean_secret(s)
    # Check base32 charset
    if not re.match(r"^[A-Z2-7]+=*$", cleaned):
        # Try to fix common substitutions: 0->O, 1->I/L, 8->B
        fixed = cleaned.replace("0","O").replace("1","I").replace("8","B")
        fixed = re.sub(r"[^A-Z2-7]", "", fixed)
        if not fixed:
            return False, ""
        cleaned = fixed
    # Validate length (must be multiple of 8 after padding)
    padded = cleaned + "=" * ((8 - len(cleaned) % 8) % 8)
    try:
        base64.b32decode(padded)
        return True, cleaned
    except Exception:
        return False, ""

def totp_now(secret: str):
    key    = _b32(secret)
    ts     = int(time.time())
    remain = 30 - (ts % 30)
    msg    = struct.pack(">Q", ts // 30)
    h      = hmac.new(key, msg, hashlib.sha1).digest()
    offset = h[-1] & 0x0F
    code   = struct.unpack(">I", h[offset:offset+4])[0] & 0x7FFFFFFF
    return str(code % 1_000_000).zfill(6), remain

# ── Session ───────────────────────────────────────────────
def get_session(tid):
    with get_db() as c:
        r = c.execute("SELECT vault_id FROM sessions WHERE telegram_id=?", (tid,)).fetchone()
    return r["vault_id"] if r else None

def set_session(tid, vault_id):
    with get_db() as c:
        c.execute("DELETE FROM sessions WHERE vault_id=? AND telegram_id!=?", (vault_id, tid))
        c.execute("INSERT INTO sessions (telegram_id,vault_id) VALUES (?,?) "
                  "ON CONFLICT(telegram_id) DO UPDATE SET vault_id=excluded.vault_id,"
                  "created_at=strftime('%s','now')", (tid, vault_id))
        c.commit()

def clear_session(tid):
    with get_db() as c:
        c.execute("DELETE FROM sessions WHERE telegram_id=?", (tid,)); c.commit()

def get_user(vault_id):
    with get_db() as c:
        return c.execute("SELECT * FROM users WHERE vault_id=?", (vault_id,)).fetchone()

def get_user_by_tid(tid):
    with get_db() as c:
        return c.execute("SELECT * FROM users WHERE telegram_id=?", (tid,)).fetchone()

# ── Helpers ───────────────────────────────────────────────
def em(text) -> str:
    if not text: return ""
    return re.sub(r"([_*\[\]()~`>#+\-=|{}.!\\])", r"\\\1", str(text))

def bar(remain):
    f = int(remain / 3)
    return "▓" * f + "░" * (10 - f)

def fmt_time(ts, tz_str="UTC"):
    try:
        import zoneinfo
        tz = zoneinfo.ZoneInfo(tz_str)
        dt = datetime.datetime.fromtimestamp(ts, tz=tz)
    except Exception:
        dt = datetime.datetime.utcfromtimestamp(ts)
        tz_str = "UTC"
    return dt.strftime(f"%d %b %Y, %I:%M %p ({tz_str})")

def parse_tz_offset(raw: str) -> str | None:
    """Parse +6:00 / -5:30 style into Etc/GMT offset or return None if invalid."""
    raw = raw.strip()
    m = re.match(r"^([+-])(\d{1,2}):(\d{2})$", raw)
    if not m:
        m = re.match(r"^([+-])(\d{1,2})$", raw)
        if not m: return None
        sign, h, mn = m.group(1), int(m.group(2)), 0
    else:
        sign, h, mn = m.group(1), int(m.group(2)), int(m.group(3))
    if h > 14 or mn not in (0, 30, 45): return None
    # Etc/GMT sign is inverted
    etc_sign = "-" if sign == "+" else "+"
    if mn == 0:
        return f"Etc/GMT{etc_sign}{h}"
    # For non-zero minutes use fixed offset string stored as-is
    return f"UTC{sign}{h:02d}:{mn:02d}"

def parse_otpauth(uri):
    try:
        p = urlparse(uri)
        if p.scheme != "otpauth": return None
        label  = unquote(p.path.lstrip("/"))
        params = parse_qs(p.query)
        secret = params.get("secret", [None])[0]
        issuer = params.get("issuer", [None])[0]
        if ":" in label:
            parts = label.split(":", 1); issuer = issuer or parts[0].strip(); name = parts[1].strip()
        else:
            name = label.strip()
        if not secret: return None
        ok, cleaned = validate_secret(secret)
        if not ok: return None
        return {"name": name, "issuer": issuer or "", "secret": cleaned}
    except Exception:
        return None

# ── Keyboards ─────────────────────────────────────────────
def kb_auth():
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("🆕 Sign Up", callback_data="auth_signup"),
        InlineKeyboardButton("🔑 Login",   callback_data="auth_login"),
    ]])

def kb_main():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Add New TOTP",  callback_data="add_totp"),
         InlineKeyboardButton("📋 List of TOTP", callback_data="list_totp")],
        [InlineKeyboardButton("✏️ Edit TOTP",    callback_data="edit_totp"),
         InlineKeyboardButton("👤 Profile",       callback_data="profile")],
        [InlineKeyboardButton("⚙️ Settings",      callback_data="settings")],
    ])

def kb_settings():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔑 Change Password", callback_data="change_pw")],
        [InlineKeyboardButton("📥 Import Vault",    callback_data="import_vault")],
        [InlineKeyboardButton("📤 Export Vault",    callback_data="export_vault")],
        [InlineKeyboardButton("🗑 Delete Account",  callback_data="delete_account")],
        [InlineKeyboardButton("🚪 Logout",           callback_data="logout")],
        [InlineKeyboardButton("🏠 Main Menu",        callback_data="main_menu")],
    ])

def kb_cancel():
    return InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="cancel_to_menu")]])

def kb_confirm_danger(yes_cb, no_cb="main_menu"):
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Yes, confirm", callback_data=yes_cb),
        InlineKeyboardButton("❌ Cancel",        callback_data=no_cb),
    ]])

# ── /start ────────────────────────────────────────────────
async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid   = update.effective_user.id
    vault = get_session(uid)
    if vault:
        name = update.effective_user.first_name or "User"
        await update.message.reply_text(
            f"👋 Welcome back, *{em(name)}*\\!\n\nChoose an option:",
            parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    await update.message.reply_text(
        "🛡 *BlockVeil Authenticator*\n\n"
        "Secure TOTP manager with AES\\-256\\-GCM encryption\\.\n"
        "Even server admins cannot read your codes\\.\n\n"
        "Please *Sign Up* or *Login* to continue\\.",
        parse_mode="MarkdownV2", reply_markup=kb_auth())
    return AUTH_MENU

# ── SIGN UP ───────────────────────────────────────────────
async def signup_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    uid = update.effective_user.id
    if get_user_by_tid(uid):
        await q.edit_message_text(
            "⚠️ *This Telegram account already has a vault\\.* Use *Login*\\.",
            parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    vault_id = generate_vault_id(uid)
    ctx.user_data["signup_vault_id"] = vault_id
    await q.edit_message_text(
        "🆕 *Create Your Account*\n\n"
        "Your unique *BV Vault ID* \\(auto\\-generated\\):\n\n"
        f"`{em(vault_id)}`\n\n"
        "📌 *Save this ID\\!* You need it to login from other devices\\.\n\n"
        "Set a *password* \\(minimum 6 characters\\):",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return SIGNUP_PASSWORD

async def signup_password(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try: await update.message.delete()
    except: pass
    if len(pw) < 6:
        await update.message.reply_text("⚠️ Minimum 6 characters\\. Try again:",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return SIGNUP_PASSWORD
    ctx.user_data["signup_pw"] = pw
    await update.message.reply_text("🔒 *Confirm your password:*",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return SIGNUP_CONFIRM

async def signup_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    confirm = update.message.text.strip()
    try: await update.message.delete()
    except: pass
    pw = ctx.user_data.get("signup_pw", "")
    if confirm != pw:
        await update.message.reply_text("❌ Passwords do not match\\. Enter password again:",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return SIGNUP_PASSWORD
    uid      = update.effective_user.id
    vault_id = ctx.user_data.get("signup_vault_id")
    if get_user_by_tid(uid):
        ctx.user_data.clear()
        await update.message.reply_text("⚠️ Account already exists\\. Use *Login*\\.",
            parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    salt = os.urandom(16)
    with get_db() as c:
        c.execute("INSERT INTO users (vault_id,telegram_id,password_hash,pw_salt) VALUES (?,?,?,?)",
            (vault_id, uid, hash_password(pw, salt), salt))
        c.commit()
    set_session(uid, vault_id)
    ctx.user_data["password"] = pw
    ctx.user_data["vault_id"] = vault_id
    await update.message.reply_text(
        "✅ *Account created\\!*\n\n"
        f"🔑 *Your BV Vault ID:*\n`{em(vault_id)}`\n\n"
        "⚠️ _Save your BV Vault ID safely\\._\n\nYou are now logged in\\.",
        parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

# ── LOGIN ─────────────────────────────────────────────────
async def login_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    uid = update.effective_user.id
    await q.edit_message_text(
        "🔑 *Login*\n\n"
        "Choose how to login:",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("📱 Login with My Telegram", callback_data="login_auto")],
            [InlineKeyboardButton("🔑 Login with BV Vault ID", callback_data="login_manual")],
            [InlineKeyboardButton("❌ Cancel", callback_data="cancel_to_menu")],
        ]))
    return LOGIN_ID

async def login_auto(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    uid      = update.effective_user.id
    vault_id = generate_vault_id(uid)
    if not get_user(vault_id):
        await q.edit_message_text(
            "❌ No account found for this Telegram account\\.\n\nPlease *Sign Up* first\\.",
            parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    ctx.user_data["login_vault_id"] = vault_id
    await q.edit_message_text("🔒 *Enter your password:*",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return LOGIN_PASSWORD

async def login_manual(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    await q.edit_message_text(
        "🔑 *Enter your BV Vault ID:*\n\n_12\\-character ID from your account_",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return LOGIN_ID

async def login_id(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    text = update.message.text.strip().lower().replace(" ", "")
    try: await update.message.delete()
    except: pass
    if not get_user(text):
        await update.message.reply_text("❌ BV Vault ID not found\\. Check and try again\\.",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return LOGIN_ID
    ctx.user_data["login_vault_id"] = text
    await update.message.reply_text("🔒 *Enter your password:*",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return LOGIN_PASSWORD

async def login_password(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try: await update.message.delete()
    except: pass
    uid = update.effective_user.id
    vid = ctx.user_data.get("login_vault_id")
    u   = get_user(vid)
    if not u:
        await update.message.reply_text("❌ Session expired\\.", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    if not hmac.compare_digest(hash_password(pw, bytes(u["pw_salt"])), bytes(u["password_hash"])):
        await update.message.reply_text("❌ Wrong password\\. Try again:",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return LOGIN_PASSWORD
    set_session(uid, vid)
    ctx.user_data["password"] = pw
    ctx.user_data["vault_id"] = vid
    name = update.effective_user.first_name or "User"
    await update.message.reply_text(
        f"✅ *Logged in\\!* Welcome, *{em(name)}*\\.",
        parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

# ── SETTINGS ──────────────────────────────────────────────
async def settings_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    await q.edit_message_text("⚙️ *Settings*\n\nChoose an option:",
        parse_mode="MarkdownV2", reply_markup=kb_settings())
    return TOTP_MENU

async def logout(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    clear_session(update.effective_user.id)
    ctx.user_data.clear()
    await q.edit_message_text("🚪 *Logged out\\.* Your data remains encrypted in the vault\\.",
        parse_mode="MarkdownV2", reply_markup=kb_auth())
    return AUTH_MENU

# ── TOTP: ADD ─────────────────────────────────────────────
async def add_totp_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    if not get_session(update.effective_user.id):
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text(
        "➕ *Add New TOTP*\n\n"
        "📷 Send a *QR code image*\n"
        "🔗 Paste an `otpauth://` URI\n"
        "⌨️ Type `manual` to enter manually\n\n"
        "_Your message will be auto\\-deleted after processing_",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return ADD_WAITING

async def handle_add_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    vault = get_session(uid); pw = ctx.user_data.get("password")
    if not vault or not pw:
        await update.message.reply_text("🔒 Session expired\\. /start", parse_mode="MarkdownV2")
        return AUTH_MENU
    # QR image
    file_obj = None
    if update.message.photo:
        file_obj = await update.message.photo[-1].get_file()
    elif update.message.document and update.message.document.mime_type.startswith("image"):
        file_obj = await update.message.document.get_file()
    if file_obj:
        try: await update.message.delete()
        except: pass
        bio = BytesIO(); await file_obj.download_to_memory(bio); bio.seek(0)
        try:
            decoded = qr_decode(Image.open(bio))
            if not decoded:
                await update.message.reply_text("⚠️ No QR code found\\. Try a clearer image\\.",
                    parse_mode="MarkdownV2", reply_markup=kb_cancel())
                return ADD_WAITING
            data = parse_otpauth(decoded[0].data.decode("utf-8"))
            if not data:
                await update.message.reply_text("⚠️ Not a valid TOTP QR\\.",
                    parse_mode="MarkdownV2", reply_markup=kb_cancel())
                return ADD_WAITING
            return await _save_totp(update, vault, data, pw)
        except Exception as e:
            logger.error(f"QR error: {e}")
            await update.message.reply_text("⚠️ Could not read image\\.",
                parse_mode="MarkdownV2", reply_markup=kb_cancel())
            return ADD_WAITING
    text = update.message.text.strip()
    if text.lower() == "manual":
        await update.message.reply_text("⌨️ Enter *account name*:",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return ADD_MANUAL_NAME
    if text.startswith("otpauth://"):
        try: await update.message.delete()
        except: pass
        data = parse_otpauth(text)
        if not data:
            await update.message.reply_text("⚠️ Invalid URI\\.",
                parse_mode="MarkdownV2", reply_markup=kb_cancel())
            return ADD_WAITING
        return await _save_totp(update, vault, data, pw)
    await update.message.reply_text(
        "⚠️ Send QR image, `otpauth://` URI, or type `manual`\\.",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return ADD_WAITING

async def handle_manual_name(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    name = update.message.text.strip()
    if not name:
        await update.message.reply_text("⚠️ Name cannot be empty\\.", parse_mode="MarkdownV2")
        return ADD_MANUAL_NAME
    ctx.user_data["pending_name"] = name
    await update.message.reply_text(
        f"✅ Name: *{em(name)}*\n\n"
        "Enter *Base32 secret key*:\n"
        "_Spaces and dashes are auto\\-removed_\n\n"
        "Example: `JBSWY3DPEHPK3PXP`\n"
        "Also works: `JBSW Y3DP EHPK 3PXP`",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return ADD_MANUAL_SECRET

async def handle_manual_secret(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    raw    = update.message.text.strip()
    uid    = update.effective_user.id
    vault  = get_session(uid)
    pw     = ctx.user_data.get("password")
    try: await update.message.delete()
    except: pass
    ok, secret = validate_secret(raw)
    if not ok:
        await update.message.reply_text(
            "⚠️ *Invalid secret key\\.*\n\n"
            "Secret must be Base32 \\(letters A\\-Z and digits 2\\-7\\)\\.\n"
            "Common issues:\n"
            "• Letter O vs digit 0\n"
            "• Letter I/L vs digit 1\n\n"
            "Please check and try again:",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return ADD_MANUAL_SECRET
    try: totp_now(secret)
    except Exception:
        await update.message.reply_text("⚠️ Secret key is invalid\\. Cannot generate OTP\\.",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return ADD_MANUAL_SECRET
    name = ctx.user_data.pop("pending_name", "Unknown")
    return await _save_totp(update, vault, {"name": name, "issuer": "", "secret": secret}, pw)

async def _save_totp(update, vault_id, data, pw):
    ct, salt, iv = encrypt_secret(data["secret"], pw, vault_id)
    with get_db() as c:
        c.execute("INSERT INTO totp_accounts (vault_id,name,issuer,secret_enc,salt,iv) VALUES (?,?,?,?,?,?)",
            (vault_id, data["name"], data.get("issuer",""), ct, salt, iv))
        c.commit()
    code, remain = totp_now(data["secret"])
    await update.message.reply_text(
        f"✅ *{em(data['name'])}* added\\!\n\n"
        f"🔢 `{code[:3]} {code[3:]}`\n"
        f"⏱ {bar(remain)} {remain}s\n\n"
        f"🔒 _Encrypted with AES\\-256\\-GCM_",
        parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

# ── TOTP: LIST (live update via Refresh) ──────────────────
async def list_totp(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    uid = update.effective_user.id; vault = get_session(uid); pw = ctx.user_data.get("password")
    if not vault:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    if not pw:
        await q.edit_message_text("🔒 Session expired\\. /start and login again\\.",
            parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    with get_db() as c:
        rows = c.execute(
            "SELECT id,name,issuer,secret_enc,salt,iv FROM totp_accounts WHERE vault_id=? ORDER BY name",
            (vault,)).fetchall()
    if not rows:
        await q.edit_message_text("📋 *Your TOTP Accounts*\n\nNo accounts yet\\.",
            parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    ts     = int(time.time())
    remain = 30 - (ts % 30)
    lines  = [f"📋 *Your TOTP Accounts*\n_⏱ Codes refresh every 30s — tap 🔄 to update_\n_Next refresh in: {remain}s_\n"]
    kb     = []
    for row in rows:
        try:
            secret = decrypt_secret(row["secret_enc"], row["salt"], row["iv"], pw, vault)
            code, rem = totp_now(secret)
            issuer_part = f" \\| {em(row['issuer'])}" if row["issuer"] else ""
            lines.append(f"🔑 *{em(row['name'])}*{issuer_part}\n   `{code[:3]} {code[3:]}` {bar(rem)} {rem}s\n")
        except Exception as e:
            logger.error(f"Decrypt error: {e}")
            lines.append(f"⚠️ *{em(row['name'])}* — error\n")
    kb.append([InlineKeyboardButton("🔄 Refresh codes", callback_data="list_totp")])
    kb.append([InlineKeyboardButton("🏠 Main Menu",     callback_data="main_menu")])
    await q.edit_message_text("\n".join(lines), parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup(kb))
    return TOTP_MENU

# ── TOTP: EDIT (rename + delete combined) ─────────────────
async def edit_totp_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    uid = update.effective_user.id; vault = get_session(uid)
    if not vault:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    with get_db() as c:
        rows = c.execute("SELECT id,name FROM totp_accounts WHERE vault_id=? ORDER BY name", (vault,)).fetchall()
    if not rows:
        await q.edit_message_text("No TOTP accounts found\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    kb = [[InlineKeyboardButton(row["name"], callback_data=f"editpick_{row['id']}")] for row in rows]
    kb.append([InlineKeyboardButton("❌ Cancel", callback_data="main_menu")])
    await q.edit_message_text("✏️ *Edit TOTP*\n\nSelect an account:",
        parse_mode="MarkdownV2", reply_markup=InlineKeyboardMarkup(kb))
    return EDIT_PICK

async def edit_pick(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    acc_id = int(q.data.split("_")[1])
    uid = update.effective_user.id; vault = get_session(uid)
    with get_db() as c:
        row = c.execute("SELECT name FROM totp_accounts WHERE id=? AND vault_id=?", (acc_id, vault)).fetchone()
    if not row:
        await q.edit_message_text("⚠️ Account not found\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    ctx.user_data["edit_id"] = acc_id
    ctx.user_data["edit_name"] = row["name"]
    await q.edit_message_text(
        f"✏️ *{em(row['name'])}*\n\nWhat do you want to do?",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("✏️ Rename", callback_data="edit_action_rename")],
            [InlineKeyboardButton("🗑 Delete",  callback_data="edit_action_delete")],
            [InlineKeyboardButton("❌ Cancel",  callback_data="edit_totp")],
        ]))
    return EDIT_ACTION

async def edit_action(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    action = q.data.split("_")[2]
    if action == "rename":
        await q.edit_message_text("✏️ Enter the *new name*:",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return EDIT_RENAME_INPUT
    elif action == "delete":
        name = ctx.user_data.get("edit_name", "")
        await q.edit_message_text(
            f"🗑 Delete *{em(name)}*?\n\n_This cannot be undone\\._",
            parse_mode="MarkdownV2",
            reply_markup=kb_confirm_danger("edit_action_delete_confirm", "edit_totp"))
        return EDIT_ACTION

async def edit_delete_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    uid = update.effective_user.id; vault = get_session(uid)
    acc_id = ctx.user_data.pop("edit_id", None)
    name   = ctx.user_data.pop("edit_name", "")
    if acc_id:
        with get_db() as c:
            c.execute("DELETE FROM totp_accounts WHERE id=? AND vault_id=?", (acc_id, vault))
            c.commit()
    await q.edit_message_text(f"✅ *{em(name)}* deleted\\.",
        parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

async def edit_rename_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    new_name = update.message.text.strip()
    uid = update.effective_user.id; vault = get_session(uid)
    acc_id = ctx.user_data.pop("edit_id", None)
    ctx.user_data.pop("edit_name", None)
    if not new_name or not acc_id:
        await update.message.reply_text("⚠️ Invalid name\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    with get_db() as c:
        c.execute("UPDATE totp_accounts SET name=? WHERE id=? AND vault_id=?", (new_name, acc_id, vault))
        c.commit()
    await update.message.reply_text(f"✅ Renamed to *{em(new_name)}*\\.",
        parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

# ── PROFILE ───────────────────────────────────────────────
async def show_profile(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    uid = update.effective_user.id; vault = get_session(uid)
    if not vault:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    u = get_user_by_tid(uid)
    if not u:
        await q.edit_message_text("⚠️ Profile not found\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    tg   = update.effective_user
    name = ((tg.first_name or "") + " " + (tg.last_name or "")).strip() or "Unknown"
    tz   = u["timezone"] or "UTC"
    with get_db() as c:
        totp_count = c.execute("SELECT COUNT(*) as n FROM totp_accounts WHERE vault_id=?", (vault,)).fetchone()["n"]
    created_str = fmt_time(u["created_at"], tz)
    text = (
        f"👤 *Profile*\n\n"
        f"*Name:* {em(name)}\n\n"
        f"*Telegram ID:*\n`{uid}`\n\n"
        f"*BV Vault ID:*\n`{em(vault)}`\n\n"
        f"*TOTP Accounts:* {totp_count}\n\n"
        f"*Timezone:* {em(tz)}\n\n"
        f"*Account Created:*\n{em(created_str)}"
    )
    await q.edit_message_text(text, parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🌐 Change Timezone", callback_data="change_tz")],
            [InlineKeyboardButton("🏠 Main Menu",        callback_data="main_menu")],
        ]))
    return TOTP_MENU

# ── CHANGE TIMEZONE ───────────────────────────────────────
async def change_tz_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    await q.edit_message_text(
        "🌐 *Change Timezone*\n\n"
        "Enter UTC offset format:\n\n"
        "`\\+6:00` \\— Bangladesh \\(UTC\\+6\\)\n"
        "`\\+5:30` \\— India\n"
        "`\\+0:00` \\— UK / UTC\n"
        "`\\-5:00` \\— US East\n"
        "`\\-8:00` \\— US Pacific\n"
        "`\\+8:00` \\— China / Singapore\n"
        "`\\+9:00` \\— Japan / Korea\n\n"
        "_Supported minutes: :00, :30, :45_",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return TZ_INPUT

async def change_tz_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text.strip()
    uid = update.effective_user.id
    tz_str = parse_tz_offset(raw)
    if not tz_str:
        await update.message.reply_text(
            f"⚠️ Invalid format\\. Use `\\+6:00` or `\\-5:30` style\\.",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return TZ_INPUT
    # Verify it works
    try:
        import zoneinfo
        zoneinfo.ZoneInfo(tz_str)
    except Exception:
        # Store as raw offset string for fmt_time fallback
        pass
    with get_db() as c:
        c.execute("UPDATE users SET timezone=? WHERE telegram_id=?", (tz_str, uid)); c.commit()
    await update.message.reply_text(
        f"✅ Timezone set to *{em(raw)}*\\.",
        parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

# ── CHANGE PASSWORD ───────────────────────────────────────
async def change_pw_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    if not get_session(update.effective_user.id):
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text("🔑 *Change Password*\n\nEnter your *current password*:",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return CHANGE_PW_OLD

async def change_pw_old(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try: await update.message.delete()
    except: pass
    uid = update.effective_user.id; vault = get_session(uid); u = get_user(vault)
    if not u or not hmac.compare_digest(hash_password(pw, bytes(u["pw_salt"])), bytes(u["password_hash"])):
        await update.message.reply_text("❌ Wrong current password\\. Try again:",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return CHANGE_PW_OLD
    ctx.user_data["old_pw_verified"] = True
    await update.message.reply_text("✅ Verified\\. Enter your *new password* \\(min 6 chars\\):",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return CHANGE_PW_NEW

async def change_pw_new(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    new_pw = update.message.text.strip()
    try: await update.message.delete()
    except: pass
    if len(new_pw) < 6:
        await update.message.reply_text("⚠️ Minimum 6 characters\\.", parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return CHANGE_PW_NEW
    ctx.user_data["new_pw"] = new_pw
    await update.message.reply_text("🔒 *Confirm new password:*", parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return CHANGE_PW_CONFIRM

async def change_pw_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    confirm = update.message.text.strip()
    try: await update.message.delete()
    except: pass
    new_pw = ctx.user_data.get("new_pw", "")
    if confirm != new_pw:
        await update.message.reply_text("❌ Passwords do not match\\.", parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return CHANGE_PW_NEW
    uid    = update.effective_user.id; vault = get_session(uid)
    old_pw = ctx.user_data.get("password", "")
    with get_db() as c:
        rows = c.execute("SELECT id,secret_enc,salt,iv FROM totp_accounts WHERE vault_id=?", (vault,)).fetchall()
        for row in rows:
            try:
                secret = decrypt_secret(row["secret_enc"], row["salt"], row["iv"], old_pw, vault)
                ct, s, iv = encrypt_secret(secret, new_pw, vault)
                c.execute("UPDATE totp_accounts SET secret_enc=?,salt=?,iv=? WHERE id=?", (ct, s, iv, row["id"]))
            except Exception as e:
                logger.error(f"Re-encrypt error: {e}")
        new_salt = os.urandom(16)
        c.execute("UPDATE users SET password_hash=?,pw_salt=? WHERE vault_id=?",
            (hash_password(new_pw, new_salt), new_salt, vault))
        c.commit()
    ctx.user_data["password"] = new_pw
    ctx.user_data.pop("new_pw", None); ctx.user_data.pop("old_pw_verified", None)
    await update.message.reply_text(
        "✅ *Password changed\\!* All TOTP secrets re\\-encrypted\\.",
        parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

# ── EXPORT VAULT ──────────────────────────────────────────
async def export_vault_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    if not get_session(update.effective_user.id):
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text(
        "📤 *Export Vault*\n\n"
        "Enter your *current password* to confirm export\\.\n\n"
        "_Your backup will be AES\\-256\\-GCM encrypted\\._",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return EXPORT_PW_INPUT

async def export_pw_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try: await update.message.delete()
    except: pass
    uid = update.effective_user.id; vault = get_session(uid)
    u   = get_user(vault)
    if not u or not hmac.compare_digest(hash_password(pw, bytes(u["pw_salt"])), bytes(u["password_hash"])):
        await update.message.reply_text("❌ Wrong password\\. Export cancelled\\.",
            parse_mode="MarkdownV2", reply_markup=kb_settings())
        return TOTP_MENU
    with get_db() as c:
        rows = c.execute("SELECT name,issuer,secret_enc,salt,iv FROM totp_accounts WHERE vault_id=?", (vault,)).fetchall()
    if not rows:
        await update.message.reply_text("No TOTP accounts to export\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    entries = []
    for row in rows:
        try:
            secret = decrypt_secret(row["secret_enc"], row["salt"], row["iv"], pw, vault)
            entries.append({"name": row["name"], "issuer": row["issuer"] or "", "secret": secret})
        except Exception as e:
            logger.error(f"Export decrypt error: {e}")
    plain       = json.dumps({"vault_id": vault, "accounts": entries}, ensure_ascii=False).encode()
    export_salt = os.urandom(16); export_iv = os.urandom(12)
    export_key  = derive_enc_key(pw, vault, export_salt)
    ct          = AESGCM(export_key).encrypt(export_iv, plain, None)
    payload     = export_salt + export_iv + ct
    bio         = BytesIO(payload); bio.name = "blockveil_backup.bvault"
    await update.message.reply_document(
        document=bio, filename="blockveil_backup.bvault",
        caption="🔒 *BlockVeil Encrypted Vault Backup*\n\nUse 📥 Import Vault to restore\\.\nKeep this file and your password safe\\.",
        parse_mode="MarkdownV2")
    await update.message.reply_text("✅ *Vault exported successfully\\!*",
        parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

# ── IMPORT VAULT ──────────────────────────────────────────
async def import_vault_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    if not get_session(update.effective_user.id):
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text(
        "📥 *Import Vault*\n\n"
        "Send your *\\.bvault* backup file\\.\n\n"
        "_Accounts will be merged into your current vault\\.\n"
        "Duplicates will be skipped\\._",
        parse_mode="MarkdownV2", reply_markup=kb_cancel())
    return IMPORT_WAITING

async def import_vault_file(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id; vault = get_session(uid); pw = ctx.user_data.get("password")
    if not vault or not pw:
        await update.message.reply_text("Session expired\\. /start", parse_mode="MarkdownV2")
        return AUTH_MENU
    if not update.message.document:
        await update.message.reply_text("⚠️ Please send a *.bvault* file\\.", parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return IMPORT_WAITING
    bio = BytesIO()
    f   = await update.message.document.get_file()
    await f.download_to_memory(bio)
    payload = bio.getvalue()
    if len(payload) < 28:
        await update.message.reply_text("⚠️ Invalid backup file\\.", parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return IMPORT_WAITING
    try:
        export_salt = payload[:16]; export_iv = payload[16:28]; ct = payload[28:]
        export_key  = derive_enc_key(pw, vault, export_salt)
        plain       = AESGCM(export_key).decrypt(export_iv, ct, None)
        data        = json.loads(plain.decode())
        accounts    = data.get("accounts", [])
    except Exception:
        await update.message.reply_text(
            "❌ *Decryption failed\\.* Wrong password or corrupted file\\.",
            parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return IMPORT_WAITING
    imported = 0; skipped = 0
    with get_db() as c:
        existing = {r["name"] for r in c.execute("SELECT name FROM totp_accounts WHERE vault_id=?", (vault,)).fetchall()}
        for acc in accounts:
            if acc["name"] in existing: skipped += 1; continue
            try:
                ok, secret = validate_secret(acc["secret"])
                if not ok: skipped += 1; continue
                totp_now(secret)
                ct2, s2, iv2 = encrypt_secret(secret, pw, vault)
                c.execute("INSERT INTO totp_accounts (vault_id,name,issuer,secret_enc,salt,iv) VALUES (?,?,?,?,?,?)",
                    (vault, acc["name"], acc.get("issuer",""), ct2, s2, iv2))
                imported += 1
            except Exception as e:
                logger.error(f"Import error: {e}"); skipped += 1
        c.commit()
    await update.message.reply_text(
        f"✅ *Import complete\\!*\n\n"
        f"Imported: *{imported}*\nSkipped: *{skipped}* \\(duplicates or errors\\)",
        parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

# ── DELETE ACCOUNT ────────────────────────────────────────
async def delete_account_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    await q.edit_message_text(
        "🗑 *Delete Account*\n\n"
        "⚠️ *Permanently deletes your account and ALL TOTP data\\.*\n\n"
        "This action *cannot be undone*\\. Are you sure?",
        parse_mode="MarkdownV2",
        reply_markup=kb_confirm_danger("delete_account_confirm", "settings"))
    return DELETE_ACCOUNT_CONFIRM

async def delete_account_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    uid = update.effective_user.id; vault = get_session(uid)
    if vault:
        with get_db() as c:
            c.execute("DELETE FROM totp_accounts WHERE vault_id=?", (vault,))
            c.execute("DELETE FROM users WHERE vault_id=?", (vault,))
            c.execute("DELETE FROM sessions WHERE telegram_id=?", (uid,))
            c.commit()
    ctx.user_data.clear()
    await q.edit_message_text("🗑 *Account deleted\\.* All data permanently removed\\.",
        parse_mode="MarkdownV2", reply_markup=kb_auth())
    return AUTH_MENU

# ── CANCEL / MENU ─────────────────────────────────────────
async def cancel_to_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    for k in ["pending_name","signup_pw","new_pw","edit_id","edit_name"]:
        ctx.user_data.pop(k, None)
    uid = update.effective_user.id; vault = get_session(uid)
    if vault:
        await q.edit_message_text("Choose an option:", reply_markup=kb_main())
        return TOTP_MENU
    await q.edit_message_text("🛡 *BlockVeil Authenticator*\n\nPlease login or sign up\\.",
        parse_mode="MarkdownV2", reply_markup=kb_auth())
    return AUTH_MENU

async def main_menu_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    await q.edit_message_text("Choose an option:", reply_markup=kb_main())
    return TOTP_MENU

# ── MAIN ──────────────────────────────────────────────────
def main():
    if not SERVER_KEY:
        raise RuntimeError("ENCRYPTION_KEY environment variable not set")
    init_db()
    token = os.environ["BOT_TOKEN"]
    app   = ApplicationBuilder().token(token).build()

    conv = ConversationHandler(
        entry_points=[CommandHandler("start", start)],
        states={
            AUTH_MENU: [
                CallbackQueryHandler(signup_start,  pattern="^auth_signup$"),
                CallbackQueryHandler(login_start,   pattern="^auth_login$"),
            ],
            SIGNUP_PASSWORD:  [MessageHandler(filters.TEXT & ~filters.COMMAND, signup_password),  CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            SIGNUP_CONFIRM:   [MessageHandler(filters.TEXT & ~filters.COMMAND, signup_confirm),   CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            LOGIN_ID: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, login_id),
                CallbackQueryHandler(login_auto,   pattern="^login_auto$"),
                CallbackQueryHandler(login_manual, pattern="^login_manual$"),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            LOGIN_PASSWORD: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, login_password),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            TOTP_MENU: [
                CallbackQueryHandler(add_totp_start,        pattern="^add_totp$"),
                CallbackQueryHandler(list_totp,             pattern="^list_totp$"),
                CallbackQueryHandler(edit_totp_start,       pattern="^edit_totp$"),
                CallbackQueryHandler(show_profile,          pattern="^profile$"),
                CallbackQueryHandler(settings_menu,         pattern="^settings$"),
                CallbackQueryHandler(export_vault_start,    pattern="^export_vault$"),
                CallbackQueryHandler(import_vault_start,    pattern="^import_vault$"),
                CallbackQueryHandler(change_pw_start,       pattern="^change_pw$"),
                CallbackQueryHandler(delete_account_start,  pattern="^delete_account$"),
                CallbackQueryHandler(logout,                pattern="^logout$"),
                CallbackQueryHandler(main_menu_cb,          pattern="^main_menu$"),
                CallbackQueryHandler(change_tz_start,       pattern="^change_tz$"),
                CallbackQueryHandler(edit_pick,             pattern="^editpick_\\d+$"),
                CallbackQueryHandler(edit_action,           pattern="^edit_action_(rename|delete)$"),
                CallbackQueryHandler(edit_delete_confirm,   pattern="^edit_action_delete_confirm$"),
            ],
            ADD_WAITING:       [MessageHandler(filters.PHOTO | filters.Document.IMAGE, handle_add_input), MessageHandler(filters.TEXT & ~filters.COMMAND, handle_add_input), CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            ADD_MANUAL_NAME:   [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_manual_name),   CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            ADD_MANUAL_SECRET: [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_manual_secret), CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            EDIT_PICK:   [CallbackQueryHandler(edit_pick,   pattern="^editpick_\\d+$"), CallbackQueryHandler(main_menu_cb, pattern="^main_menu$")],
            EDIT_ACTION: [
                CallbackQueryHandler(edit_action,         pattern="^edit_action_(rename|delete)$"),
                CallbackQueryHandler(edit_delete_confirm, pattern="^edit_action_delete_confirm$"),
                CallbackQueryHandler(edit_totp_start,     pattern="^edit_totp$"),
            ],
            EDIT_RENAME_INPUT: [MessageHandler(filters.TEXT & ~filters.COMMAND, edit_rename_input), CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            CHANGE_PW_OLD:     [MessageHandler(filters.TEXT & ~filters.COMMAND, change_pw_old),     CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            CHANGE_PW_NEW:     [MessageHandler(filters.TEXT & ~filters.COMMAND, change_pw_new),     CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            CHANGE_PW_CONFIRM: [MessageHandler(filters.TEXT & ~filters.COMMAND, change_pw_confirm), CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            DELETE_ACCOUNT_CONFIRM: [
                CallbackQueryHandler(delete_account_confirm, pattern="^delete_account_confirm$"),
                CallbackQueryHandler(settings_menu,          pattern="^settings$"),
            ],
            EXPORT_PW_INPUT: [MessageHandler(filters.TEXT & ~filters.COMMAND, export_pw_input), CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            IMPORT_WAITING:  [MessageHandler(filters.Document.ALL, import_vault_file), CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
            TZ_INPUT:        [MessageHandler(filters.TEXT & ~filters.COMMAND, change_tz_input), CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$")],
        },
        fallbacks=[CommandHandler("start", start)],
        allow_reentry=True,
        per_chat=True,
    )
    app.add_handler(conv)
    logger.info("BlockVeil Auth Bot started.")
    app.run_polling(drop_pending_updates=True)

if __name__ == "__main__":
    main()
