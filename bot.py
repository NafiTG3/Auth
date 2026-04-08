import os, re, hmac, time, json, struct, base64, hashlib, sqlite3, logging, datetime, secrets, string, asyncio
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

# ── States ─────────────────────────────────────────────────
(
    AUTH_MENU,
    SIGNUP_PASSWORD, SIGNUP_CONFIRM,
    LOGIN_CHOICE, LOGIN_ID_INPUT, LOGIN_PASSWORD,
    RESET_ID_INPUT, RESET_OTP_INPUT, RESET_NEW_PW, RESET_NEW_PW_CONFIRM,
    RESET_SECURE_KEY_INPUT,
    TOTP_MENU,
    ADD_WAITING, ADD_MANUAL_NAME, ADD_MANUAL_SECRET,
    EDIT_PICK, EDIT_ACTION, EDIT_RENAME_INPUT,
    CHANGE_PW_OLD, CHANGE_PW_NEW, CHANGE_PW_CONFIRM,
    SETTINGS_RESET_OTP, SETTINGS_RESET_PW, SETTINGS_RESET_PW_CONFIRM,
    DELETE_ACCOUNT_PASSWORD, DELETE_ACCOUNT_CONFIRM,
    EXPORT_PW1_INPUT, EXPORT_PW2_INPUT,
    IMPORT_FILE_WAIT, IMPORT_PW_INPUT,
    TZ_INPUT,
    SHOW_SECRET_PW,
    SECURE_KEY_VIEW_PW,
) = range(33)   # fixed count

DB_PATH            = os.environ.get("DB_PATH", "auth.db")
SERVER_KEY         = os.environ.get("ENCRYPTION_KEY", "").encode()
PBKDF2_ITER        = 1_000_000
OTP_TTL            = 60
MAX_RESET_ATTEMPTS = 3
FREEZE_HOURS       = 18
ALERT_VISIBLE_HOURS = 72

# ── DB ─────────────────────────────────────────────────────
def get_db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    with get_db() as c:
        c.execute("""CREATE TABLE IF NOT EXISTS users (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            vault_id      TEXT    UNIQUE NOT NULL,
            telegram_id   INTEGER UNIQUE NOT NULL,
            password_hash BLOB    NOT NULL,
            pw_salt       BLOB    NOT NULL,
            tg_name       TEXT    DEFAULT '',
            timezone      TEXT    DEFAULT 'UTC',
            created_at    INTEGER DEFAULT (strftime('%s','now')))""")
        c.execute("""CREATE TABLE IF NOT EXISTS sessions (
            telegram_id INTEGER PRIMARY KEY,
            vault_id    TEXT    NOT NULL,
            created_at  INTEGER DEFAULT (strftime('%s','now')))""")
        c.execute("""CREATE TABLE IF NOT EXISTS totp_accounts (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            vault_id   TEXT NOT NULL,
            name       TEXT NOT NULL,
            issuer     TEXT DEFAULT '',
            secret_enc BLOB NOT NULL,
            salt       BLOB NOT NULL,
            iv         BLOB NOT NULL,
            sk_enc     BLOB,
            sk_salt    BLOB,
            sk_iv      BLOB,
            created_at INTEGER DEFAULT (strftime('%s','now')))""")
        c.execute("""CREATE TABLE IF NOT EXISTS reset_otps (
            vault_id   TEXT    NOT NULL,
            otp        TEXT    NOT NULL,
            expires_at INTEGER NOT NULL,
            used       INTEGER DEFAULT 0)""")
        c.execute("""CREATE TABLE IF NOT EXISTS reset_attempts (
            vault_id     TEXT    PRIMARY KEY,
            attempts     INTEGER DEFAULT 0,
            frozen_until INTEGER DEFAULT 0)""")
        c.execute("""CREATE TABLE IF NOT EXISTS login_alerts (
            alert_id   TEXT    PRIMARY KEY,
            owner_id   INTEGER NOT NULL,
            vault_id   TEXT    NOT NULL,
            message_id INTEGER NOT NULL,
            chat_id    INTEGER NOT NULL,
            created_at INTEGER NOT NULL)""")

        # Migrations
        for col, defval in [("tg_name", "''"), ("timezone", "'UTC'")]:
            try:
                c.execute(f"ALTER TABLE users ADD COLUMN {col} TEXT DEFAULT {defval}")
            except Exception:
                pass

        for col in [("sk_enc", "BLOB"), ("sk_salt", "BLOB"), ("sk_iv", "BLOB")]:
            try:
                c.execute(f"ALTER TABLE users ADD COLUMN {col[0]} {col[1]}")
            except Exception:
                pass

        for col in [("sk_enc", "BLOB"), ("sk_salt", "BLOB"), ("sk_iv", "BLOB")]:
            try:
                c.execute(f"ALTER TABLE totp_accounts ADD COLUMN {col[0]} {col[1]}")
            except Exception:
                pass

        c.commit()

# ── Crypto ─────────────────────────────────────────────────
def gen_vault_id(telegram_id: int) -> str:
    raw      = hashlib.sha256(f"bv_{telegram_id}_v2".encode() + SERVER_KEY).digest()
    alphabet = "abcdefghijklmnopqrstuvwxyz0123456789"
    num      = int.from_bytes(raw, "big")
    chars    = []
    for _ in range(12):
        chars.append(alphabet[num % len(alphabet)])
        num //= len(alphabet)
    return "".join(chars)

def hash_pw(password: str, salt: bytes) -> bytes:
    return PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=PBKDF2_ITER).derive(password.encode())

def enc_key(password: str, vault_id: str, salt: bytes) -> bytes:
    return PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=PBKDF2_ITER).derive(
        (password + vault_id).encode() + SERVER_KEY
    )

def encrypt(secret: str, password: str, vault_id: str):
    salt = os.urandom(16)
    iv   = os.urandom(12)
    ct   = AESGCM(enc_key(password, vault_id, salt)).encrypt(iv, secret.encode(), None)
    return ct, salt, iv

def decrypt(ct, salt, iv, password, vault_id) -> str:
    return AESGCM(enc_key(password, vault_id, bytes(salt))).decrypt(bytes(iv), bytes(ct), None).decode()

def export_enc_key(password: str, salt: bytes) -> bytes:
    return PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=310_000).derive(password.encode())

def export_encrypt(data: bytes, password: str) -> bytes:
    salt = os.urandom(16)
    iv   = os.urandom(12)
    ct   = AESGCM(export_enc_key(password, salt)).encrypt(iv, data, None)
    return salt + iv + ct

def export_decrypt(payload: bytes, password: str) -> bytes:
    salt = payload[:16]; iv = payload[16:28]; ct = payload[28:]
    return AESGCM(export_enc_key(password, salt)).decrypt(iv, ct, None)

# ── Secure Key crypto ───────────────────────────────────────
def gen_secure_key() -> str:
    return secrets.token_hex(32)

def sk_enc_key(secure_key_hex: str, vault_id: str, salt: bytes) -> bytes:
    material = (secure_key_hex + vault_id).encode() + SERVER_KEY
    return PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=200_000).derive(material)

def sk_encrypt_totp(totp_plain_bytes: bytes, secure_key_hex: str, vault_id: str):
    salt = os.urandom(16)
    iv   = os.urandom(12)
    ct   = AESGCM(sk_enc_key(secure_key_hex, vault_id, salt)).encrypt(iv, totp_plain_bytes, None)
    return ct, salt, iv

def sk_decrypt_totp(sk_ct: bytes, sk_salt: bytes, sk_iv: bytes, secure_key_hex: str, vault_id: str) -> bytes:
    return AESGCM(sk_enc_key(secure_key_hex, vault_id, bytes(sk_salt))).decrypt(
        bytes(sk_iv), bytes(sk_ct), None
    )

def store_user_secure_key(vault_id: str, secure_key_hex: str, password: str):
    ct, salt, iv = encrypt(secure_key_hex, password, vault_id)
    with get_db() as c:
        c.execute(
            "UPDATE users SET sk_enc=?, sk_salt=?, sk_iv=? WHERE vault_id=?",
            (ct, salt, iv, vault_id),
        )
        c.commit()

def load_user_secure_key(vault_id: str, password: str) -> str | None:
    with get_db() as c:
        row = c.execute(
            "SELECT sk_enc, sk_salt, sk_iv FROM users WHERE vault_id=?", (vault_id,)
        ).fetchone()
    if not row or not row["sk_enc"]:
        return None
    try:
        return decrypt(row["sk_enc"], row["sk_salt"], row["sk_iv"], password, vault_id)
    except Exception:
        return None

def verify_secure_key_by_totp(vault_id: str, candidate_hex: str) -> bool:
    with get_db() as c:
        row = c.execute(
            "SELECT sk_enc, sk_salt, sk_iv FROM totp_accounts WHERE vault_id=? AND sk_enc IS NOT NULL LIMIT 1",
            (vault_id,)
        ).fetchone()
    if not row:
        return False
    try:
        sk_decrypt_totp(row["sk_enc"], row["sk_salt"], row["sk_iv"], candidate_hex.strip(), vault_id)
        return True
    except Exception:
        return False

# ── TOTP ───────────────────────────────────────────────────
def clean_secret(s: str) -> str:
    return re.sub(r"[\s\-\.\,\_]", "", s).upper()

def validate_secret(s: str):
    c = clean_secret(s)
    c = re.sub(r"[^A-Z2-7]", "", c.replace("0", "O").replace("1", "I").replace("8", "B"))
    if len(c) < 8:
        return False, ""
    try:
        base64.b32decode(c + "=" * ((8 - len(c) % 8) % 8))
        return True, c
    except Exception:
        return False, ""

def totp_now(secret: str):
    c  = clean_secret(secret)
    k  = base64.b32decode(c + "=" * ((8 - len(c) % 8) % 8))
    ts = int(time.time())
    remain = 30 - (ts % 30)
    h   = hmac.new(k, struct.pack(">Q", ts // 30), hashlib.sha1).digest()
    off = h[-1] & 0xF
    code = str(struct.unpack(">I", h[off:off+4])[0] & 0x7FFFFFFF % 1_000_000).zfill(6)
    return code, remain

def parse_otpauth(uri: str):
    try:
        p      = urlparse(uri)
        if p.scheme != "otpauth":
            return None
        label  = unquote(p.path.lstrip("/"))
        params = parse_qs(p.query)
        secret = params.get("secret", [None])[0]
        issuer = params.get("issuer", [None])[0]
        name   = label.split(":", 1)[1].strip() if ":" in label else label.strip()
        issuer = issuer or (label.split(":", 1)[0].strip() if ":" in label else "")
        if not secret:
            return None
        ok, c = validate_secret(secret)
        if not ok:
            return None
        return {"name": name, "issuer": issuer, "secret": c}
    except Exception:
        return None

# ── OTP (cryptographic, unpredictable) ────────────────────
def gen_otp() -> str:
    raw    = secrets.token_bytes(32)
    digest = hashlib.sha3_256(raw + SERVER_KEY + str(time.time_ns()).encode()).hexdigest()
    b62    = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
    num    = int(digest, 16)
    chars  = []
    for _ in range(8):
        chars.append(b62[num % 62])
        num //= 62
    return "".join(chars)

def store_otp(vault_id: str, otp: str):
    otp_hmac = hmac.new(SERVER_KEY, otp.encode(), hashlib.sha256).hexdigest()
    with get_db() as c:
        c.execute("DELETE FROM reset_otps WHERE vault_id=?", (vault_id,))
        c.execute("INSERT INTO reset_otps (vault_id,otp,expires_at) VALUES (?,?,?)",
                  (vault_id, otp_hmac, int(time.time()) + OTP_TTL))
        c.commit()

def verify_otp(vault_id: str, otp: str) -> bool:
    with get_db() as c:
        row = c.execute(
            "SELECT otp,expires_at,used FROM reset_otps WHERE vault_id=? ORDER BY expires_at DESC LIMIT 1",
            (vault_id,)
        ).fetchone()
    if not row:
        return False
    if row["used"] or int(time.time()) > row["expires_at"]:
        return False
    otp_hmac = hmac.new(SERVER_KEY, otp.strip().encode(), hashlib.sha256).hexdigest()
    return hmac.compare_digest(row["otp"], otp_hmac)

def mark_otp_used(vault_id: str):
    with get_db() as c:
        c.execute("UPDATE reset_otps SET used=1 WHERE vault_id=?", (vault_id,))
        c.commit()

# ── Rate limiting ───────────────────────────────────────────
def record_reset_attempt(vault_id: str) -> bool:
    now = int(time.time())
    with get_db() as c:
        row = c.execute("SELECT attempts, frozen_until FROM reset_attempts WHERE vault_id=?", (vault_id,)).fetchone()
        if row and row["frozen_until"] > now:
            return True
        attempts     = (row["attempts"] if row else 0) + 1
        frozen_until = now + FREEZE_HOURS * 3600 if attempts >= MAX_RESET_ATTEMPTS else 0
        c.execute("INSERT OR REPLACE INTO reset_attempts (vault_id, attempts, frozen_until) VALUES (?,?,?)",
                  (vault_id, attempts, frozen_until))
        c.commit()
        return frozen_until > now

def reset_attempts_clear(vault_id: str):
    with get_db() as c:
        c.execute("DELETE FROM reset_attempts WHERE vault_id=?", (vault_id,))
        c.commit()

def is_reset_frozen(vault_id: str) -> bool:
    with get_db() as c:
        row = c.execute("SELECT frozen_until FROM reset_attempts WHERE vault_id=?", (vault_id,)).fetchone()
        return bool(row and row["frozen_until"] > int(time.time()))

def get_freeze_remaining(vault_id: str) -> int:
    with get_db() as c:
        row = c.execute("SELECT frozen_until FROM reset_attempts WHERE vault_id=?", (vault_id,)).fetchone()
        if row and row["frozen_until"] > int(time.time()):
            return row["frozen_until"] - int(time.time())
    return 0

# ── MarkdownV2 escaping (FIXED) ────────────────────────────
def em(t) -> str:
    """Escape special characters for Telegram MarkdownV2."""
    if not t:
        return ""
    # List of special characters: _ * [ ] ( ) ~ ` > # + - = | { } . ! \
    # We need to escape each with a backslash
    special_chars = r"_*[]()~`>#+\-=|{}.!\\"
    # Escape each character
    escaped = []
    for ch in str(t):
        if ch in special_chars:
            escaped.append("\\" + ch)
        else:
            escaped.append(ch)
    return "".join(escaped)

def bar(r) -> str:
    f = int(r / 3)
    return "▓" * f + "░" * (10 - f)

def fmt_time(ts, tz="UTC") -> str:
    try:
        import zoneinfo
        dt = datetime.datetime.fromtimestamp(ts, tz=zoneinfo.ZoneInfo(tz))
    except Exception:
        dt = datetime.datetime.utcfromtimestamp(ts)
        tz = "UTC"
    return dt.strftime(f"%d %b %Y, %I:%M %p ({tz})")

def parse_tz(raw: str):
    m = re.match(r"^([+-])(\d{1,2})(?::(\d{2}))?$", raw.strip())
    if not m:
        return None
    sign, h, mn = m.group(1), int(m.group(2)), int(m.group(3) or 0)
    if h > 14 or mn not in (0, 30, 45):
        return None
    es = "-" if sign == "+" else "+"
    return f"Etc/GMT{es}{h}" if mn == 0 else f"UTC{sign}{h:02d}:{mn:02d}"

# ── Keyboards ───────────────────────────────────────────────
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
        [InlineKeyboardButton("🔑 Change Password",   callback_data="change_pw")],
        [InlineKeyboardButton("🔓 Reset Password",    callback_data="settings_reset_pw")],
        [InlineKeyboardButton("🛡 View Secure Key",   callback_data="view_secure_key")],
        [InlineKeyboardButton("📤 Export Vault",      callback_data="export_vault")],
        [InlineKeyboardButton("📥 Import Vault",      callback_data="import_vault")],
        [InlineKeyboardButton("🗑 Delete Account",    callback_data="delete_account")],
        [InlineKeyboardButton("🚪 Logout",             callback_data="logout")],
        [InlineKeyboardButton("🏠 Main Menu",          callback_data="main_menu")],
    ])

def kb_cancel():
    return InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="cancel_to_menu")]])

def kb_danger(yes_cb, no_cb="main_menu"):
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Confirm", callback_data=yes_cb),
        InlineKeyboardButton("❌ Cancel",  callback_data=no_cb),
    ]])

def kb_reset_secure_key():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("⏭ Skip to no restore", callback_data="reset_sk_skip")],
        [InlineKeyboardButton("❌ Cancel",              callback_data="cancel_to_menu")],
    ])

# ── Login Alert System ──────────────────────────────────────
async def send_login_alert(bot, owner_id: int, vault_id: str, new_telegram_id: int, new_username: str):
    now      = int(time.time())
    alert_id = f"{vault_id}_{now}"
    dt       = datetime.datetime.utcfromtimestamp(now)
    time_str = dt.strftime("%I:%M %p, %d %b %Y") + " UTC"
    text = (
        f"⚠️ *New Login Detected*\n\n"
        f"Your vault `{em(vault_id)}` was accessed from a different Telegram account\\.\n\n"
        f"*Accessor:* @{em(new_username)} \\(ID: `{new_telegram_id}`\\)\n"
        f"*Time:* {em(time_str)}\n\n"
        f"If this was you, tap *It's me*\\. "
        f"Otherwise tap *Not me* to immediately log out all sessions\\."
    )
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ It's me",              callback_data=f"alert_ack_{alert_id}"),
        InlineKeyboardButton("🚨 Not me - Log out all", callback_data=f"alert_logout_{alert_id}"),
    ]])
    try:
        msg = await bot.send_message(
            chat_id=owner_id,
            text=text,
            parse_mode="MarkdownV2",
            reply_markup=kb,
        )
        with get_db() as c:
            c.execute(
                "INSERT INTO login_alerts (alert_id,owner_id,vault_id,message_id,chat_id,created_at) VALUES (?,?,?,?,?,?)",
                (alert_id, owner_id, vault_id, msg.message_id, owner_id, now),
            )
            c.commit()
        async def _auto_delete():
            await asyncio.sleep(ALERT_VISIBLE_HOURS * 3600)
            try:
                await msg.delete()
            except Exception:
                pass
            with get_db() as c:
                c.execute("DELETE FROM login_alerts WHERE alert_id=?", (alert_id,))
                c.commit()
        asyncio.create_task(_auto_delete())
        logger.info(f"Login alert sent to owner {owner_id} for vault {vault_id}")
    except Exception as e:
        logger.error(f"Failed to send login alert to owner {owner_id}: {e}")

async def handle_alert_ack(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer("Acknowledged. No action taken.")
    alert_id = q.data[len("alert_ack_"):]
    with get_db() as c:
        c.execute("DELETE FROM login_alerts WHERE alert_id=?", (alert_id,))
        c.commit()
    try:
        await q.message.delete()
    except Exception:
        pass

async def handle_alert_logout(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer("Logging out all sessions...")
    alert_id = q.data[len("alert_logout_"):]
    with get_db() as c:
        row = c.execute("SELECT vault_id FROM login_alerts WHERE alert_id=?", (alert_id,)).fetchone()
        if not row:
            await q.edit_message_text("⚠️ Alert expired or already processed\\.", parse_mode="MarkdownV2")
            return
        vault_id = row["vault_id"]
        c.execute("DELETE FROM sessions WHERE vault_id=?", (vault_id,))
        c.execute("DELETE FROM login_alerts WHERE alert_id=?", (alert_id,))
        c.commit()
    await q.edit_message_text(
        "✅ *All sessions logged out\\.* You may now change your password if needed\\.",
        parse_mode="MarkdownV2",
    )

# ── Session Helpers ─────────────────────────────────────────
def get_session(tid) -> str | None:
    with get_db() as c:
        r = c.execute("SELECT vault_id FROM sessions WHERE telegram_id=?", (tid,)).fetchone()
    return r["vault_id"] if r else None

def set_session(tid, vault_id):
    with get_db() as c:
        c.execute("DELETE FROM sessions WHERE vault_id=? AND telegram_id!=?", (vault_id, tid))
        c.execute(
            "INSERT INTO sessions (telegram_id,vault_id) VALUES (?,?) "
            "ON CONFLICT(telegram_id) DO UPDATE SET vault_id=excluded.vault_id,created_at=strftime('%s','now')",
            (tid, vault_id),
        )
        c.commit()

def clear_session(tid):
    with get_db() as c:
        c.execute("DELETE FROM sessions WHERE telegram_id=?", (tid,))
        c.commit()

def get_user(vault_id):
    with get_db() as c:
        return c.execute("SELECT * FROM users WHERE vault_id=?", (vault_id,)).fetchone()

def get_user_by_tid(tid):
    with get_db() as c:
        return c.execute("SELECT * FROM users WHERE telegram_id=?", (tid,)).fetchone()

def find_user_by_id_or_vault(raw: str):
    raw = raw.strip()
    u   = get_user(raw.lower())
    if u:
        return u
    if raw.isdigit():
        with get_db() as c:
            return c.execute("SELECT * FROM users WHERE telegram_id=?", (int(raw),)).fetchone()
    return None

def update_tg_name(vault_id: str, tg_user):
    u = get_user(vault_id)
    if not u or tg_user.id != u["telegram_id"]:
        return
    name = ((tg_user.first_name or "") + " " + (tg_user.last_name or "")).strip()
    if name:
        with get_db() as c:
            c.execute("UPDATE users SET tg_name=? WHERE vault_id=?", (name, vault_id))
            c.commit()

# ── /start ──────────────────────────────────────────────────
async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    uid   = update.effective_user.id
    vault = get_session(uid)
    if vault:
        u = get_user(vault)
        if u:
            update_tg_name(vault, update.effective_user)
            display_name = u["tg_name"] if u["tg_name"] else (update.effective_user.first_name or "User")
            await update.message.reply_text(
                f"👋 Welcome back, *{em(display_name)}*\\!\n\nChoose an option:",
                parse_mode="MarkdownV2",
                reply_markup=kb_main(),
            )
            return TOTP_MENU
    await update.message.reply_text(
        "🛡 *BV Authenticator*\n\n"
        "Secure TOTP manager with AES\\-256\\-GCM encryption\\.\n"
        "Server admins cannot read your codes\\.\n\n"
        "Please *Sign Up* or *Login* to continue\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_auth(),
    )
    return AUTH_MENU

# ── SIGN UP ─────────────────────────────────────────────────
async def signup_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    if get_user_by_tid(uid):
        await q.edit_message_text(
            "⚠️ *This Telegram account already has a vault\\.* Use *Login*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU
    vid = gen_vault_id(uid)
    ctx.user_data["signup_vid"] = vid
    await q.edit_message_text(
        "🆕 *Create Your Account*\n\n"
        "Your *BV Vault ID* \\(auto\\-generated\\):\n\n"
        f"`{em(vid)}`\n\n"
        "📌 *Save this ID\\!* You need it to login from other devices\\.\n\n"
        "Set a *password* \\(minimum 6 characters\\):",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return SIGNUP_PASSWORD

async def signup_pw(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    if len(pw) < 6:
        await update.message.reply_text(
            "⚠️ Minimum 6 characters\\. Try again:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return SIGNUP_PASSWORD
    ctx.user_data["signup_pw"] = pw
    await update.message.reply_text(
        "🔒 *Confirm your password:*",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return SIGNUP_CONFIRM

async def signup_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    confirm = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    pw  = ctx.user_data.get("signup_pw", "")
    vid = ctx.user_data.get("signup_vid")
    uid = update.effective_user.id
    if confirm != pw:
        await update.message.reply_text(
            "❌ Passwords do not match\\. Enter password again:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return SIGNUP_PASSWORD
    if get_user_by_tid(uid):
        ctx.user_data.clear()
        await update.message.reply_text(
            "⚠️ Account already exists\\. Use *Login*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU

    salt    = os.urandom(16)
    tg_name = ((update.effective_user.first_name or "") + " " + (update.effective_user.last_name or "")).strip()

    with get_db() as c:
        c.execute(
            "INSERT INTO users (vault_id,telegram_id,password_hash,pw_salt,tg_name) VALUES (?,?,?,?,?)",
            (vid, uid, hash_pw(pw, salt), salt, tg_name),
        )
        c.commit()

    secure_key = gen_secure_key()
    store_user_secure_key(vid, secure_key, pw)

    set_session(uid, vid)
    ctx.user_data["password"] = pw
    ctx.user_data["vault_id"] = vid

    sk_display = " ".join(secure_key[i:i+8] for i in range(0, len(secure_key), 8))

    sk_msg = await update.message.reply_text(
        "🛡 *Your Secure Key*\n\n"
        f"`{em(sk_display)}`\n\n"
        "⚠️ *CRITICAL: Save this key somewhere safe RIGHT NOW\\.*\n\n"
        "This key is shown *only once*\\. It is *permanent* and *cannot be changed or removed*\\.\n\n"
        "You will need it if you ever reset your password from the login screen \\(without being logged in\\)\\. "
        "Without it, your TOTP data *cannot be restored* after such a reset\\.\n\n"
        "_This message auto\\-deletes in 5 minutes\\._",
        parse_mode="MarkdownV2",
    )

    await update.message.reply_text(
        "✅ *Account created\\!*\n\n"
        f"🔑 *Your BV Vault ID:*\n`{em(vid)}`\n\n"
        "⚠️ _Save your BV Vault ID and Secure Key safely\\._\n\nYou are now logged in\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )

    async def _delete_sk_msg():
        await asyncio.sleep(300)
        try:
            await sk_msg.delete()
        except Exception:
            pass
    asyncio.create_task(_delete_sk_msg())

    return TOTP_MENU

# ── LOGIN ───────────────────────────────────────────────────
async def login_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "🔑 *Login*\n\nChoose how to login:",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("📱 Login with My Telegram",            callback_data="login_auto")],
            [InlineKeyboardButton("🔑 Login with Vault/Telegram User ID", callback_data="login_manual")],
            [InlineKeyboardButton("🔓 Forgot Password?",                   callback_data="reset_pw_start")],
            [InlineKeyboardButton("❌ Cancel",                              callback_data="cancel_to_menu")],
        ]),
    )
    return LOGIN_CHOICE

async def login_auto(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    vid = gen_vault_id(uid)
    if not get_user(vid):
        await q.edit_message_text(
            "❌ No account found for this Telegram account\\. Please *Sign Up*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU
    ctx.user_data["login_vid"] = vid
    await q.edit_message_text(
        "🔒 *Enter your password:*",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return LOGIN_PASSWORD

async def login_manual_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "🔑 *Enter your BV Vault ID or Telegram User ID:*\n\n"
        "_BV Vault ID: 12\\-character alphanumeric code_\n"
        "_Telegram User ID: your numeric user ID_",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return LOGIN_ID_INPUT

async def login_id_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    u = find_user_by_id_or_vault(raw)
    if not u:
        await update.message.reply_text(
            "❌ *ID not found\\.* Check and try again\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return LOGIN_ID_INPUT
    ctx.user_data["login_vid"] = u["vault_id"]
    await update.message.reply_text(
        "🔒 *Enter your password:*",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return LOGIN_PASSWORD

async def login_pw(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw  = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    uid = update.effective_user.id
    vid = ctx.user_data.get("login_vid")
    u   = get_user(vid)
    if not u:
        await update.message.reply_text(
            "❌ Session expired\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU
    if not hmac.compare_digest(hash_pw(pw, bytes(u["pw_salt"])), bytes(u["password_hash"])):
        await update.message.reply_text(
            "❌ Wrong password\\. Try again:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return LOGIN_PASSWORD

    if uid != u["telegram_id"]:
        new_username = update.effective_user.username or str(uid)
        asyncio.create_task(
            send_login_alert(ctx.bot, u["telegram_id"], vid, uid, new_username)
        )

    set_session(uid, vid)
    if uid == u["telegram_id"]:
        update_tg_name(vid, update.effective_user)
    ctx.user_data["password"] = pw
    ctx.user_data["vault_id"] = vid
    owner_name = u["tg_name"] if u["tg_name"] else "User"
    await update.message.reply_text(
        f"✅ *Logged in\\!* Welcome to vault of *{em(owner_name)}*\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    return TOTP_MENU

# ── PASSWORD RESET (unauthenticated path) ───────────────────
async def reset_pw_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "🔓 *Password Reset*\n\n"
        "Send your *BV Vault ID* or *Telegram User ID*\\.\n"
        "A one\\-time code will be sent to the *vault owner's Telegram account* \\(valid 60 seconds\\)\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return RESET_ID_INPUT

async def reset_id_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    u = find_user_by_id_or_vault(raw)
    if not u:
        await update.message.reply_text(
            "❌ ID not found\\. Try again:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return RESET_ID_INPUT
    vid = u["vault_id"]
    if is_reset_frozen(vid):
        remaining = get_freeze_remaining(vid)
        h, m      = remaining // 3600, (remaining % 3600) // 60
        await update.message.reply_text(
            f"⚠️ *Account temporarily frozen* due to too many failed attempts\\.\n\n"
            f"Try again in *{h}h {m}m*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return RESET_ID_INPUT
    otp = gen_otp()
    store_otp(vid, otp)
    ctx.user_data["reset_vid"] = vid
    try:
        await ctx.bot.send_message(
            chat_id=u["telegram_id"],
            text=(
                f"🔐 *Password Reset OTP*\n\n"
                f"Someone requested a password reset for your vault\\.\n\n"
                f"Your one\\-time code:\n`{otp}`\n\n"
                f"⏱ Valid for *60 seconds*\\.\n_Do not share this with anyone\\._"
            ),
            parse_mode="MarkdownV2",
        )
        await update.message.reply_text(
            "✅ *OTP sent to the vault owner's Telegram account\\!*\n\n"
            "The owner must share the OTP with you\\. Enter it here:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
    except Exception as e:
        logger.error(f"Failed to send reset OTP to {u['telegram_id']}: {e}")
        await update.message.reply_text(
            "⚠️ *Failed to send OTP\\.* The vault owner must /start the bot first\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return RESET_ID_INPUT
    return RESET_OTP_INPUT

async def reset_otp_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    otp = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    vid = ctx.user_data.get("reset_vid")
    if not verify_otp(vid, otp):
        frozen = record_reset_attempt(vid)
        if frozen:
            h, m = get_freeze_remaining(vid) // 3600, (get_freeze_remaining(vid) % 3600) // 60
            await update.message.reply_text(
                f"⚠️ *Too many failed attempts\\.* Account frozen for *{h}h {m}m*\\.",
                parse_mode="MarkdownV2",
                reply_markup=kb_auth(),
            )
            ctx.user_data.pop("reset_vid", None)
            return AUTH_MENU
        with get_db() as c:
            row      = c.execute("SELECT attempts FROM reset_attempts WHERE vault_id=?", (vid,)).fetchone()
            attempts = row["attempts"] if row else 0
            left     = max(0, MAX_RESET_ATTEMPTS - attempts)
        await update.message.reply_text(
            f"❌ *Invalid or expired OTP\\.* {left} attempt\\(s\\) remaining before freeze\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return RESET_OTP_INPUT
    reset_attempts_clear(vid)
    mark_otp_used(vid)
    ctx.user_data["reset_otp_verified"] = True

    with get_db() as c:
        totp_count = c.execute(
            "SELECT COUNT(*) as n FROM totp_accounts WHERE vault_id=?", (vid,)
        ).fetchone()["n"]

    await update.message.reply_text(
        "✅ *OTP verified\\!*\n\n"
        "🛡 *Secure Key Required*\n\n"
        f"Your vault has *{totp_count} TOTP account\\(s\\)*\\.\n\n"
        "Enter your *Secure Key* to restore all TOTP data after the password reset\\.\n\n"
        "The Secure Key is the 64\\-character hex code shown when you created your account\\.\n\n"
        "_If you do not have your Secure Key, tap the button below\\.\n"
        "Skipping will permanently delete ALL your TOTP accounts\\._",
        parse_mode="MarkdownV2",
        reply_markup=kb_reset_secure_key(),
    )
    return RESET_SECURE_KEY_INPUT

async def reset_secure_key_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    candidate = update.message.text.strip().replace(" ", "")
    try:
        await update.message.delete()
    except Exception:
        pass
    vid = ctx.user_data.get("reset_vid")

    if not re.match(r"^[0-9a-fA-F]{64}$", candidate):
        await update.message.reply_text(
            "❌ *Invalid Secure Key format\\.* It should be 64 hex characters\\.\n\n"
            "Check your saved copy and try again\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_reset_secure_key(),
        )
        return RESET_SECURE_KEY_INPUT

    if not verify_secure_key_by_totp(vid, candidate):
        await update.message.reply_text(
            "❌ *Secure Key does not match\\.* Try again, or skip to lose all TOTP data\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_reset_secure_key(),
        )
        return RESET_SECURE_KEY_INPUT

    ctx.user_data["reset_secure_key"] = candidate
    await update.message.reply_text(
        "✅ *Secure Key verified\\!* Your TOTP data will be restored\\.\n\n"
        "Now enter your *new password* \\(min 6 chars\\):",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return RESET_NEW_PW

async def reset_sk_skip(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    ctx.user_data["reset_sk_skipped"] = True
    await q.edit_message_text(
        "⚠️ *Skip Secure Key*\n\n"
        "By skipping, ALL your TOTP accounts will be *permanently deleted*\\.\n\n"
        "Your account remains, but all TOTP data is gone forever\\.\n\n"
        "Enter your *new password* \\(min 6 chars\\) to continue:",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return RESET_NEW_PW

async def reset_new_pw(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    if len(pw) < 6:
        await update.message.reply_text(
            "⚠️ Minimum 6 characters\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return RESET_NEW_PW
    ctx.user_data["reset_new_pw"] = pw
    await update.message.reply_text(
        "🔒 *Confirm new password:*",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return RESET_NEW_PW_CONFIRM

async def reset_new_pw_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    confirm = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    new_pw = ctx.user_data.get("reset_new_pw", "")
    vid    = ctx.user_data.get("reset_vid")
    if confirm != new_pw:
        await update.message.reply_text(
            "❌ Passwords do not match\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return RESET_NEW_PW

    secure_key  = ctx.user_data.get("reset_secure_key")
    sk_skipped  = ctx.user_data.get("reset_sk_skipped", False)
    new_salt    = os.urandom(16)
    reenc_ok    = 0
    reenc_fail  = 0
    deleted_cnt = 0

    with get_db() as c:
        rows = c.execute(
            "SELECT id, secret_enc, salt, iv, sk_enc, sk_salt, sk_iv "
            "FROM totp_accounts WHERE vault_id=?", (vid,)
        ).fetchall()

        if sk_skipped:
            c.execute("DELETE FROM totp_accounts WHERE vault_id=?", (vid,))
            deleted_cnt = len(rows)
        elif secure_key:
            for row in rows:
                try:
                    if row["sk_enc"]:
                        plain_secret_bytes = sk_decrypt_totp(
                            row["sk_enc"], row["sk_salt"], row["sk_iv"], secure_key, vid
                        )
                        plain_secret = plain_secret_bytes.decode()
                        new_ct, new_s, new_iv = encrypt(plain_secret, new_pw, vid)
                        new_sk_ct, new_sk_s, new_sk_iv = sk_encrypt_totp(
                            plain_secret.encode(), secure_key, vid
                        )
                        c.execute(
                            "UPDATE totp_accounts SET secret_enc=?, salt=?, iv=?, "
                            "sk_enc=?, sk_salt=?, sk_iv=? WHERE id=?",
                            (new_ct, new_s, new_iv, new_sk_ct, new_sk_s, new_sk_iv, row["id"]),
                        )
                        reenc_ok += 1
                    else:
                        c.execute("DELETE FROM totp_accounts WHERE id=?", (row["id"],))
                        reenc_fail += 1
                except Exception as e:
                    logger.error(f"Re-encrypt TOTP with secure key during reset: {e}")
                    c.execute("DELETE FROM totp_accounts WHERE id=?", (row["id"],))
                    reenc_fail += 1
        else:
            c.execute("DELETE FROM totp_accounts WHERE vault_id=?", (vid,))
            deleted_cnt = len(rows)

        c.execute(
            "UPDATE users SET password_hash=?, pw_salt=? WHERE vault_id=?",
            (hash_pw(new_pw, new_salt), new_salt, vid),
        )
        if secure_key:
            ct, s, iv = encrypt(secure_key, new_pw, vid)
            c.execute(
                "UPDATE users SET sk_enc=?, sk_salt=?, sk_iv=? WHERE vault_id=?",
                (ct, s, iv, vid),
            )
        c.commit()

    for k in ("reset_vid", "reset_new_pw", "reset_otp_verified",
              "reset_secure_key", "reset_sk_skipped"):
        ctx.user_data.pop(k, None)

    if sk_skipped or deleted_cnt > 0:
        result_msg = (
            "✅ *Password reset successful\\!*\n\n"
            f"⚠️ _All {em(str(deleted_cnt))} TOTP accounts were deleted because no Secure Key was provided\\._\n\n"
            "Login with your new password\\."
        )
    elif reenc_fail > 0:
        result_msg = (
            "✅ *Password reset successful\\!*\n\n"
            f"🔒 _{reenc_ok} TOTP secret\\(s\\) restored successfully\\._\n"
            f"⚠️ _{reenc_fail} TOTP secret\\(s\\) could not be restored and were removed\\._\n\n"
            "Login with your new password\\."
        )
    else:
        result_msg = (
            "✅ *Password reset successful\\!*\n\n"
            f"🔒 _All {reenc_ok} TOTP secret\\(s\\) restored with your Secure Key\\._\n\n"
            "Login with your new password\\."
        )

    await update.message.reply_text(
        result_msg,
        parse_mode="MarkdownV2",
        reply_markup=kb_auth(),
    )
    return AUTH_MENU

# ── SETTINGS RESET (while LOGGED IN) ────────────────────────
async def settings_reset_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    vault = get_session(uid)
    if not vault:
        await q.edit_message_text("Session expired\\.", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    u = get_user(vault)
    if not u:
        await q.edit_message_text("User not found\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    otp = gen_otp()
    store_otp(vault, otp)
    try:
        await ctx.bot.send_message(
            chat_id=u["telegram_id"],
            text=(
                f"🔐 *Password Reset OTP*\n\n"
                f"Your one\\-time code:\n`{otp}`\n\n"
                f"⏱ Valid for *60 seconds*\\."
            ),
            parse_mode="MarkdownV2",
        )
        await q.edit_message_text(
            "✅ *OTP sent\\!*\n\nEnter the OTP here:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
    except Exception as e:
        logger.error(f"Settings reset OTP send failed: {e}")
        await q.edit_message_text(
            "⚠️ *Failed to send OTP\\.* The vault owner must /start the bot first\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return TOTP_MENU
    return SETTINGS_RESET_OTP

async def settings_reset_otp(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    otp   = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    uid   = update.effective_user.id
    vault = get_session(uid)
    if not verify_otp(vault, otp):
        frozen = record_reset_attempt(vault)
        if frozen:
            h, m = get_freeze_remaining(vault) // 3600, (get_freeze_remaining(vault) % 3600) // 60
            await update.message.reply_text(
                f"⚠️ *Too many failed attempts\\.* Account frozen for *{h}h {m}m*\\.",
                parse_mode="MarkdownV2",
                reply_markup=kb_cancel(),
            )
            return TOTP_MENU
        with get_db() as c:
            row      = c.execute("SELECT attempts FROM reset_attempts WHERE vault_id=?", (vault,)).fetchone()
            attempts = row["attempts"] if row else 0
            left     = max(0, MAX_RESET_ATTEMPTS - attempts)
        await update.message.reply_text(
            f"❌ Invalid OTP\\. {left} attempt\\(s\\) remaining\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return SETTINGS_RESET_OTP
    reset_attempts_clear(vault)
    mark_otp_used(vault)
    await update.message.reply_text(
        "✅ Verified\\! Enter *new password* \\(min 6 chars\\):",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return SETTINGS_RESET_PW

async def settings_reset_pw_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    if len(pw) < 6:
        await update.message.reply_text(
            "⚠️ Minimum 6 characters\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return SETTINGS_RESET_PW
    ctx.user_data["sreset_pw"] = pw
    await update.message.reply_text(
        "🔒 *Confirm new password:*",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return SETTINGS_RESET_PW_CONFIRM

async def settings_reset_pw_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    confirm = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    new_pw = ctx.user_data.pop("sreset_pw", "")
    uid    = update.effective_user.id
    vault  = get_session(uid)
    old_pw = ctx.user_data.get("password", "")
    if confirm != new_pw:
        await update.message.reply_text(
            "❌ Passwords do not match\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return SETTINGS_RESET_PW
    with get_db() as c:
        rows = c.execute(
            "SELECT id, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?", (vault,)
        ).fetchall()
        for row in rows:
            try:
                secret    = decrypt(row["secret_enc"], row["salt"], row["iv"], old_pw, vault)
                ct, s, iv = encrypt(secret, new_pw, vault)
                sk = load_user_secure_key(vault, old_pw)
                if sk:
                    sk_ct, sk_s, sk_iv = sk_encrypt_totp(secret.encode(), sk, vault)
                    c.execute(
                        "UPDATE totp_accounts SET secret_enc=?, salt=?, iv=?, "
                        "sk_enc=?, sk_salt=?, sk_iv=? WHERE id=?",
                        (ct, s, iv, sk_ct, sk_s, sk_iv, row["id"]),
                    )
                else:
                    c.execute(
                        "UPDATE totp_accounts SET secret_enc=?, salt=?, iv=? WHERE id=?",
                        (ct, s, iv, row["id"]),
                    )
            except Exception as e:
                logger.error(f"Re-encrypt TOTP during settings reset: {e}")
        new_salt = os.urandom(16)
        c.execute(
            "UPDATE users SET password_hash=?, pw_salt=? WHERE vault_id=?",
            (hash_pw(new_pw, new_salt), new_salt, vault),
        )
        sk = load_user_secure_key(vault, old_pw)
        if sk:
            ct, s, iv = encrypt(sk, new_pw, vault)
            c.execute(
                "UPDATE users SET sk_enc=?, sk_salt=?, sk_iv=? WHERE vault_id=?",
                (ct, s, iv, vault),
            )
        c.commit()
    ctx.user_data["password"] = new_pw
    await update.message.reply_text(
        "✅ *Password reset\\! All TOTP secrets re\\-encrypted\\.*",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    return TOTP_MENU

# ── VIEW SECURE KEY (from settings) ─────────────────────────
async def view_secure_key_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    if not get_session(uid):
        await q.edit_message_text("Session expired\\.", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text(
        "🛡 *View Secure Key*\n\n"
        "Enter your *account password* to reveal your Secure Key:\n\n"
        "_The Secure Key will auto\\-delete after 60 seconds\\._",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return SECURE_KEY_VIEW_PW

async def view_secure_key_pw(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    uid   = update.effective_user.id
    vault = get_session(uid)
    u     = get_user(vault)
    if not u:
        await update.message.reply_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    if not hmac.compare_digest(hash_pw(pw, bytes(u["pw_salt"])), bytes(u["password_hash"])):
        await update.message.reply_text(
            "❌ *Wrong password\\.*",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU
    sk = load_user_secure_key(vault, pw)
    if not sk:
        await update.message.reply_text(
            "⚠️ *Secure Key not found\\.* Your account may have been created before this feature\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU
    sk_display = " ".join(sk[i:i+8] for i in range(0, len(sk), 8))
    msg = await update.message.reply_text(
        f"🛡 *Your Secure Key*\n\n"
        f"`{em(sk_display)}`\n\n"
        "⚠️ *Save this somewhere safe\\.*\n"
        "_This message auto\\-deletes in 60 seconds\\._",
        parse_mode="MarkdownV2",
    )
    await update.message.reply_text(
        "✅ Secure Key revealed\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    async def _del():
        await asyncio.sleep(60)
        try:
            await msg.delete()
        except Exception:
            pass
    asyncio.create_task(_del())
    return TOTP_MENU

# ── LOGOUT ──────────────────────────────────────────────────
async def logout(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    clear_session(update.effective_user.id)
    ctx.user_data.clear()
    await q.edit_message_text(
        "🚪 *Logged out\\.* Your data remains encrypted in the vault\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_auth(),
    )
    return AUTH_MENU

# ── SETTINGS MENU ───────────────────────────────────────────
async def settings_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "⚙️ *Settings*\n\nChoose an option:",
        parse_mode="MarkdownV2",
        reply_markup=kb_settings(),
    )
    return TOTP_MENU

# ── PROFILE ─────────────────────────────────────────────────
async def show_profile(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    vault = get_session(uid)
    if not vault:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    u = get_user(vault)
    if not u:
        await q.edit_message_text("⚠️ Profile not found\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    owner_name = u["tg_name"] if u["tg_name"] else "Unknown"
    tz         = u["timezone"] or "UTC"
    has_sk     = "✅ Active" if u["sk_enc"] else "❌ Not set"
    with get_db() as c:
        cnt = c.execute("SELECT COUNT(*) as n FROM totp_accounts WHERE vault_id=?", (vault,)).fetchone()["n"]
    text = (
        f"👤 *Vault Owner Profile*\n\n"
        f"*Owner Name:* {em(owner_name)}\n\n"
        f"*Owner Telegram ID:*\n`{u['telegram_id']}`\n\n"
        f"*BV Vault ID:*\n`{em(vault)}`\n\n"
        f"*TOTP Accounts:* {cnt}\n\n"
        f"*Secure Key:* {em(has_sk)}\n\n"
        f"*Timezone:* {em(tz)}\n\n"
        f"*Account Created:*\n{em(fmt_time(u['created_at'], tz))}"
    )
    await q.edit_message_text(
        text,
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🌐 Change Timezone", callback_data="change_tz")],
            [InlineKeyboardButton("🏠 Main Menu",        callback_data="main_menu")],
        ]),
    )
    return TOTP_MENU

# ── TIMEZONE ────────────────────────────────────────────────
async def change_tz_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "🌐 *Change Timezone*\n\n"
        "Enter UTC offset:\n\n"
        "`\\+6:00` \\- Bangladesh\n"
        "`\\+5:30` \\- India\n"
        "`\\+0:00` \\- UTC\n"
        "`\\-5:00` \\- US East\n"
        "`\\+8:00` \\- China/SG\n"
        "`\\+9:00` \\- Japan/Korea",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return TZ_INPUT

async def change_tz_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text.strip()
    tz  = parse_tz(raw)
    if not tz:
        await update.message.reply_text(
            "⚠️ Invalid\\. Use `\\+6:00` or `\\-5:30` format\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return TZ_INPUT
    with get_db() as c:
        c.execute("UPDATE users SET timezone=? WHERE telegram_id=?", (tz, update.effective_user.id))
        c.commit()
    await update.message.reply_text(
        f"✅ Timezone set to *{em(raw)}*\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    return TOTP_MENU

# ── CHANGE PASSWORD ─────────────────────────────────────────
async def change_pw_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "🔑 *Change Password*\n\nEnter your *current password:*",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return CHANGE_PW_OLD

async def change_pw_old(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    uid   = update.effective_user.id
    vault = get_session(uid)
    u     = get_user(vault)
    if not u or not hmac.compare_digest(hash_pw(pw, bytes(u["pw_salt"])), bytes(u["password_hash"])):
        await update.message.reply_text(
            "❌ Wrong password\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return CHANGE_PW_OLD
    await update.message.reply_text(
        "✅ Verified\\. Enter *new password* \\(min 6 chars\\):",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return CHANGE_PW_NEW

async def change_pw_new(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    if len(pw) < 6:
        await update.message.reply_text(
            "⚠️ Minimum 6 characters\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return CHANGE_PW_NEW
    ctx.user_data["new_pw"] = pw
    await update.message.reply_text(
        "🔒 *Confirm new password:*",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return CHANGE_PW_CONFIRM

async def change_pw_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    confirm = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    new_pw = ctx.user_data.pop("new_pw", "")
    if confirm != new_pw:
        await update.message.reply_text(
            "❌ Passwords do not match\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return CHANGE_PW_NEW
    uid    = update.effective_user.id
    vault  = get_session(uid)
    old_pw = ctx.user_data.get("password", "")
    with get_db() as c:
        rows = c.execute(
            "SELECT id, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?", (vault,)
        ).fetchall()
        for row in rows:
            try:
                secret    = decrypt(row["secret_enc"], row["salt"], row["iv"], old_pw, vault)
                ct, s, iv = encrypt(secret, new_pw, vault)
                sk = load_user_secure_key(vault, old_pw)
                if sk:
                    sk_ct, sk_s, sk_iv = sk_encrypt_totp(secret.encode(), sk, vault)
                    c.execute(
                        "UPDATE totp_accounts SET secret_enc=?, salt=?, iv=?, "
                        "sk_enc=?, sk_salt=?, sk_iv=? WHERE id=?",
                        (ct, s, iv, sk_ct, sk_s, sk_iv, row["id"]),
                    )
                else:
                    c.execute(
                        "UPDATE totp_accounts SET secret_enc=?, salt=?, iv=? WHERE id=?",
                        (ct, s, iv, row["id"]),
                    )
            except Exception as e:
                logger.error(f"Re-encrypt TOTP during change_pw: {e}")
        ns = os.urandom(16)
        c.execute(
            "UPDATE users SET password_hash=?, pw_salt=? WHERE vault_id=?",
            (hash_pw(new_pw, ns), ns, vault),
        )
        sk = load_user_secure_key(vault, old_pw)
        if sk:
            ct, s, iv = encrypt(sk, new_pw, vault)
            c.execute(
                "UPDATE users SET sk_enc=?, sk_salt=?, sk_iv=? WHERE vault_id=?",
                (ct, s, iv, vault),
            )
        c.commit()
    ctx.user_data["password"] = new_pw
    await update.message.reply_text(
        "✅ *Password changed\\! All TOTP secrets re\\-encrypted\\.*",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    return TOTP_MENU

# ── ADD TOTP ────────────────────────────────────────────────
async def add_totp_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if not get_session(update.effective_user.id):
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text(
        "➕ *Add New TOTP*\n\n"
        "Send any of the following:\n"
        "📷 *QR code image*\n"
        "🔗 `otpauth://` URI\n"
        "🔑 *Base32 secret key* \\(spaces/dashes auto\\-removed\\)\n"
        "⌨️ Type `manual` to enter step by step\n\n"
        "_Your message will be auto\\-deleted_",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return ADD_WAITING

async def _do_save_totp(update, vault, data, pw):
    ct, salt, iv = encrypt(data["secret"], pw, vault)
    sk = load_user_secure_key(vault, pw)
    if sk:
        sk_ct, sk_s, sk_iv = sk_encrypt_totp(data["secret"].encode(), sk, vault)
    else:
        sk_ct = sk_s = sk_iv = None
    with get_db() as c:
        c.execute(
            "INSERT INTO totp_accounts (vault_id, name, issuer, secret_enc, salt, iv, "
            "sk_enc, sk_salt, sk_iv) VALUES (?,?,?,?,?,?,?,?,?)",
            (vault, data["name"], data.get("issuer", ""), ct, salt, iv, sk_ct, sk_s, sk_iv),
        )
        c.commit()
    code, remain = totp_now(data["secret"])
    issuer_line  = f"\n_{em(data['issuer'])}_" if data.get("issuer") else ""
    await update.message.reply_text(
        f"✅ *{em(data['name'])}* added\\!{issuer_line}\n\n"
        f"🔢 `{code[:3]} {code[3:]}`\n"
        f"⏱ {bar(remain)} {remain}s\n\n"
        f"🔒 _Encrypted with AES\\-256\\-GCM \\+ Secure Key_",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    return TOTP_MENU

async def _process_input(update, ctx, vault, pw):
    file_obj = None
    if update.message.photo:
        file_obj = await update.message.photo[-1].get_file()
    elif (update.message.document
          and update.message.document.mime_type
          and update.message.document.mime_type.startswith("image")):
        file_obj = await update.message.document.get_file()
    if file_obj:
        try:
            await update.message.delete()
        except Exception:
            pass
        bio = BytesIO()
        await file_obj.download_to_memory(bio)
        bio.seek(0)
        try:
            decoded = qr_decode(Image.open(bio))
            if decoded:
                data = parse_otpauth(decoded[0].data.decode("utf-8"))
                if data:
                    return await _do_save_totp(update, vault, data, pw), True
            await update.message.reply_text(
                "⚠️ No valid TOTP QR found in image\\.",
                parse_mode="MarkdownV2",
                reply_markup=kb_cancel(),
            )
        except Exception as e:
            logger.error(f"QR decode error: {e}")
            await update.message.reply_text(
                "⚠️ Could not read image\\.",
                parse_mode="MarkdownV2",
                reply_markup=kb_cancel(),
            )
        return None, True
    if not update.message.text:
        return None, False
    text = update.message.text.strip()
    if text.startswith("otpauth://"):
        try:
            await update.message.delete()
        except Exception:
            pass
        data = parse_otpauth(text)
        if data:
            return await _do_save_totp(update, vault, data, pw), True
        await update.message.reply_text(
            "⚠️ Invalid otpauth URI\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return None, True
    ok, cleaned = validate_secret(text)
    if ok and len(cleaned) >= 8:
        try:
            totp_now(cleaned)
            try:
                await update.message.delete()
            except Exception:
                pass
            ctx.user_data["pending_secret"] = cleaned
            await update.message.reply_text(
                "✅ *Secret key detected\\!*\n\n"
                "Enter an *account name*:\n_Example: GitHub, Google, Discord_",
                parse_mode="MarkdownV2",
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("❌ Cancel", callback_data="global_add_cancel"),
                ]]),
            )
            return None, True
        except Exception:
            pass
    return None, False

async def handle_add_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    if not vault or not pw:
        await update.message.reply_text("Session expired\\. /start", parse_mode="MarkdownV2")
        return AUTH_MENU
    if update.message.text and update.message.text.strip().lower() == "manual":
        await update.message.reply_text(
            "⌨️ Enter *account name:*",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return ADD_MANUAL_NAME
    result, handled = await _process_input(update, ctx, vault, pw)
    if result is not None:
        return result
    if handled:
        return ADD_WAITING
    await update.message.reply_text(
        "⚠️ *Could not recognize input\\.*\n\n"
        "Send: QR image, `otpauth://` URI, Base32 secret, or type `manual`",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return ADD_WAITING

async def handle_manual_name(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    name = update.message.text.strip()
    if not name:
        await update.message.reply_text("⚠️ Name cannot be empty\\.", parse_mode="MarkdownV2")
        return ADD_MANUAL_NAME
    preloaded = ctx.user_data.pop("pending_secret", None)
    if preloaded:
        uid   = update.effective_user.id
        vault = get_session(uid)
        pw    = ctx.user_data.get("password")
        return await _do_save_totp(update, vault, {"name": name, "issuer": "", "secret": preloaded}, pw)
    ctx.user_data["pending_name"] = name
    await update.message.reply_text(
        f"✅ Name: *{em(name)}*\n\n"
        "Enter *Base32 secret key:*\n_Spaces and dashes auto\\-removed_",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return ADD_MANUAL_SECRET

async def handle_manual_secret(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    raw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    ok, cleaned = validate_secret(raw)
    if not ok:
        await update.message.reply_text(
            "⚠️ *Invalid secret key\\.* Must be Base32 \\(A\\-Z, 2\\-7\\)\\.\n\nTry again:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return ADD_MANUAL_SECRET
    try:
        totp_now(cleaned)
    except Exception:
        await update.message.reply_text(
            "⚠️ *Secret key failed TOTP test\\.* Try again:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return ADD_MANUAL_SECRET
    name = ctx.user_data.pop("pending_name", "Unknown")
    return await _do_save_totp(update, vault, {"name": name, "issuer": "", "secret": cleaned}, pw)

# ── LIST TOTP ────────────────────────────────────────────────
async def list_totp(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    if not vault or not pw:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    with get_db() as c:
        rows = c.execute(
            "SELECT name, issuer, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=? ORDER BY name",
            (vault,)
        ).fetchall()
    if not rows:
        await q.edit_message_text(
            "📋 *No TOTP accounts yet\\.*\n\nUse ➕ Add New TOTP to add one\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU
    lines = []
    for row in rows:
        try:
            secret   = decrypt(row["secret_enc"], row["salt"], row["iv"], pw, vault)
            code, rm = totp_now(secret)
            label    = f"_{em(row['issuer'])}_  " if row["issuer"] else ""
            lines.append(
                f"{label}*{em(row['name'])}*\n"
                f"`{code[:3]} {code[3:]}` {bar(rm)} {rm}s"
            )
        except Exception as e:
            logger.error(f"List TOTP decrypt error: {e}")
            lines.append(f"*{em(row['name'])}*\n_\\[Decrypt error\\]_")
    text = "📋 *Your TOTP Codes*\n\n" + "\n\n".join(lines)
    await q.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb_main())
    return TOTP_MENU

# ── EDIT TOTP (FIXED) ───────────────────────────────────────
async def edit_totp_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    vault = get_session(uid)
    if not vault:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    try:
        with get_db() as c:
            rows = c.execute(
                "SELECT id, name FROM totp_accounts WHERE vault_id=? ORDER BY name", (vault,)
            ).fetchall()
        if not rows:
            await q.edit_message_text("No TOTP accounts found\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
            return TOTP_MENU
        kb = []
        for r in rows:
            # Button text does not need Markdown escaping; but we use raw name
            kb.append([InlineKeyboardButton(r["name"], callback_data=f"editpick_{r['id']}")])
        kb.append([InlineKeyboardButton("❌ Cancel", callback_data="main_menu")])
        await q.edit_message_text(
            "✏️ *Edit TOTP* \\-\\- Select account:",
            parse_mode="MarkdownV2",
            reply_markup=InlineKeyboardMarkup(kb),
        )
        return EDIT_PICK
    except Exception as e:
        logger.error(f"Edit TOTP error: {e}")
        await q.edit_message_text(
            f"⚠️ An error occurred: {em(str(e))}\\. Please try again later\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU

async def edit_pick(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q      = update.callback_query
    await q.answer()
    try:
        acc_id = int(q.data.split("_")[1])
    except:
        await q.answer("Invalid selection.", show_alert=True)
        return TOTP_MENU
    uid    = update.effective_user.id
    vault  = get_session(uid)
    with get_db() as c:
        row = c.execute(
            "SELECT name FROM totp_accounts WHERE id=? AND vault_id=?", (acc_id, vault)
        ).fetchone()
    if not row:
        await q.edit_message_text("⚠️ Account not found\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    ctx.user_data["edit_id"]   = acc_id
    ctx.user_data["edit_name"] = row["name"]
    await q.edit_message_text(
        f"✏️ *{em(row['name'])}*\n\nWhat would you like to do?",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("✏️ Rename",         callback_data="edit_action_rename")],
            [InlineKeyboardButton("🗑 Delete",           callback_data="edit_action_delete")],
            [InlineKeyboardButton("🔍 Show Secret Key", callback_data="edit_action_showsecret")],
            [InlineKeyboardButton("❌ Cancel",           callback_data="edit_totp")],
        ]),
    )
    return EDIT_ACTION

async def edit_action(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q      = update.callback_query
    await q.answer()
    parts = q.data.split("_")
    if len(parts) < 3:
        await q.answer("Invalid action.", show_alert=True)
        return EDIT_ACTION
    action = parts[2]
    if action == "rename":
        await q.edit_message_text(
            "✏️ Enter *new name:*",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return EDIT_RENAME_INPUT
    elif action == "showsecret":
        name = ctx.user_data.get("edit_name", "")
        await q.edit_message_text(
            f"🔍 *Show Secret Key*\n\n"
            f"Account: *{em(name)}*\n\n"
            "🔒 Enter your *account password* to reveal the secret key:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return SHOW_SECRET_PW
    else:  # delete
        name = ctx.user_data.get("edit_name", "")
        await q.edit_message_text(
            f"🗑 Delete *{em(name)}*?\n\n_This cannot be undone\\._",
            parse_mode="MarkdownV2",
            reply_markup=kb_danger("edit_action_delete_confirm", "edit_totp"),
        )
        return EDIT_ACTION  # stay in EDIT_ACTION for confirmation

async def edit_delete_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q      = update.callback_query
    await q.answer()
    uid    = update.effective_user.id
    vault  = get_session(uid)
    acc_id = ctx.user_data.pop("edit_id", None)
    name   = ctx.user_data.pop("edit_name", "")
    if acc_id:
        with get_db() as c:
            c.execute("DELETE FROM totp_accounts WHERE id=? AND vault_id=?", (acc_id, vault))
            c.commit()
    await q.edit_message_text(
        f"✅ *{em(name)}* deleted\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    return TOTP_MENU

async def edit_rename_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    new_name = update.message.text.strip()
    uid      = update.effective_user.id
    vault    = get_session(uid)
    acc_id   = ctx.user_data.pop("edit_id", None)
    ctx.user_data.pop("edit_name", None)
    if not new_name or not acc_id:
        await update.message.reply_text("⚠️ Invalid\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    with get_db() as c:
        c.execute("UPDATE totp_accounts SET name=? WHERE id=? AND vault_id=?", (new_name, acc_id, vault))
        c.commit()
    await update.message.reply_text(
        f"✅ Renamed to *{em(new_name)}*\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    return TOTP_MENU

# ── SHOW SECRET KEY (for edit) ─────────────────────────────
async def show_secret_pw(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    uid    = update.effective_user.id
    vault  = get_session(uid)
    acc_id = ctx.user_data.get("edit_id")
    name   = ctx.user_data.get("edit_name", "")
    u = get_user(vault)
    if not u:
        await update.message.reply_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    if not hmac.compare_digest(hash_pw(pw, bytes(u["pw_salt"])), bytes(u["password_hash"])):
        await update.message.reply_text(
            "❌ *Wrong password\\.* Secret key not revealed\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        ctx.user_data.pop("edit_id", None)
        ctx.user_data.pop("edit_name", None)
        return TOTP_MENU
    with get_db() as c:
        row = c.execute(
            "SELECT secret_enc, salt, iv FROM totp_accounts WHERE id=? AND vault_id=?",
            (acc_id, vault),
        ).fetchone()
    if not row:
        await update.message.reply_text(
            "⚠️ Account not found\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        ctx.user_data.pop("edit_id", None)
        ctx.user_data.pop("edit_name", None)
        return TOTP_MENU
    try:
        secret = decrypt(row["secret_enc"], row["salt"], row["iv"], pw, vault)
    except Exception as e:
        logger.error(f"Decrypt for show_secret failed: {e}")
        await update.message.reply_text(
            "❌ *Failed to decrypt secret key\\.*",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        ctx.user_data.pop("edit_id", None)
        ctx.user_data.pop("edit_name", None)
        return TOTP_MENU
    ctx.user_data.pop("edit_id", None)
    ctx.user_data.pop("edit_name", None)
    msg = await update.message.reply_text(
        f"🔍 *Secret Key \\-\\- {em(name)}*\n\n"
        f"`{em(secret)}`\n\n"
        "⚠️ _This message will be automatically deleted in 30 seconds\\._",
        parse_mode="MarkdownV2",
    )
    await update.message.reply_text(
        "✅ Secret key revealed\\. Keep it safe\\!",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    async def _delete_secret_msg():
        await asyncio.sleep(30)
        try:
            await msg.delete()
        except Exception:
            pass
    asyncio.create_task(_delete_secret_msg())
    return TOTP_MENU

# ── EXPORT VAULT ────────────────────────────────────────────
async def export_vault_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if not get_session(update.effective_user.id):
        await q.edit_message_text("Session expired\\.", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text(
        "📤 *Export Vault*\n\n*Step 1:* Enter your *account password* to verify:",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return EXPORT_PW1_INPUT

async def export_pw1_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    uid   = update.effective_user.id
    vault = get_session(uid)
    u     = get_user(vault)
    if not u or not hmac.compare_digest(hash_pw(pw, bytes(u["pw_salt"])), bytes(u["password_hash"])):
        await update.message.reply_text(
            "❌ Wrong account password\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return EXPORT_PW1_INPUT
    await update.message.reply_text(
        "*Step 2:* Enter a *file encryption password*\\.\n\n"
        "_This password protects the backup file\\.\n"
        "Anyone importing this file will need it\\._",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return EXPORT_PW2_INPUT

async def export_pw2_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    file_pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    if len(file_pw) < 4:
        await update.message.reply_text(
            "⚠️ Minimum 4 characters\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return EXPORT_PW2_INPUT
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password", "")
    with get_db() as c:
        rows = c.execute(
            "SELECT name, issuer, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?", (vault,)
        ).fetchall()
    if not rows:
        await update.message.reply_text(
            "No TOTP accounts to export\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU
    entries = []
    for row in rows:
        try:
            secret = decrypt(row["secret_enc"], row["salt"], row["iv"], pw, vault)
            entries.append({"name": row["name"], "issuer": row["issuer"] or "", "secret": secret})
        except Exception as e:
            logger.error(f"Export decrypt: {e}")
    plain   = json.dumps({"version": 2, "vault_id": vault, "accounts": entries}, ensure_ascii=False).encode()
    payload = export_encrypt(plain, file_pw)
    bio     = BytesIO(payload)
    bio.name = "bv_backup.bvault"
    msg = await update.message.reply_document(
        document=bio,
        filename="bv_backup.bvault",
        caption=(
            "🔒 *BV Authenticator Encrypted Vault Backup*\n\n"
            "Import with 📥 Import Vault\\.\n"
            "Share the *file encryption password* with the importer\\.\n\n"
            "_This file will be auto\\-deleted in 60 seconds\\._"
        ),
        parse_mode="MarkdownV2",
    )
    await update.message.reply_text(
        "✅ *Vault exported\\!*",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    async def _delete_file():
        await asyncio.sleep(60)
        try:
            await msg.delete()
        except Exception:
            pass
    asyncio.create_task(_delete_file())
    return TOTP_MENU

# ── IMPORT VAULT ────────────────────────────────────────────
async def import_vault_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    if not get_session(update.effective_user.id):
        await q.edit_message_text("Session expired\\.", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text(
        "📥 *Import Vault*\n\n"
        "Send your *\\.bvault* backup file\\.\n\n"
        "_You will need the file's encryption password\\.\n"
        "Works with backups from any user\\._",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return IMPORT_FILE_WAIT

async def import_file_recv(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not update.message.document:
        await update.message.reply_text(
            "⚠️ Please send a *\\.bvault* file\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return IMPORT_FILE_WAIT
    bio = BytesIO()
    f   = await update.message.document.get_file()
    await f.download_to_memory(bio)
    payload = bio.getvalue()
    if len(payload) < 28:
        await update.message.reply_text(
            "⚠️ Invalid file\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return IMPORT_FILE_WAIT
    ctx.user_data["import_payload"] = payload
    await update.message.reply_text(
        "🔒 Enter the *file encryption password:*\n"
        "_The password used when this file was exported_",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return IMPORT_PW_INPUT

async def import_pw_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    file_pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    payload = ctx.user_data.pop("import_payload", None)
    if not payload:
        await update.message.reply_text(
            "⚠️ Session expired\\. Send file again\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return IMPORT_FILE_WAIT
    try:
        plain    = export_decrypt(payload, file_pw)
        data     = json.loads(plain.decode())
        accounts = data.get("accounts", [])
    except Exception:
        await update.message.reply_text(
            "❌ *Wrong password or corrupted file\\.*",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        ctx.user_data["import_payload"] = payload
        return IMPORT_PW_INPUT
    uid      = update.effective_user.id
    vault    = get_session(uid)
    pw       = ctx.user_data.get("password", "")
    imported = 0
    skipped  = 0
    with get_db() as c:
        existing = {r["name"] for r in c.execute(
            "SELECT name FROM totp_accounts WHERE vault_id=?", (vault,)
        ).fetchall()}
        for acc in accounts:
            if acc["name"] in existing:
                skipped += 1
                continue
            try:
                ok, secret = validate_secret(acc["secret"])
                if not ok:
                    skipped += 1
                    continue
                totp_now(secret)
                ct, s, iv = encrypt(secret, pw, vault)
                sk = load_user_secure_key(vault, pw)
                if sk:
                    sk_ct, sk_s, sk_iv = sk_encrypt_totp(secret.encode(), sk, vault)
                else:
                    sk_ct = sk_s = sk_iv = None
                c.execute(
                    "INSERT INTO totp_accounts (vault_id, name, issuer, secret_enc, salt, iv, "
                    "sk_enc, sk_salt, sk_iv) VALUES (?,?,?,?,?,?,?,?,?)",
                    (vault, acc["name"], acc.get("issuer", ""), ct, s, iv, sk_ct, sk_s, sk_iv),
                )
                imported += 1
            except Exception as e:
                logger.error(f"Import entry: {e}")
                skipped += 1
        c.commit()
    await update.message.reply_text(
        f"✅ *Import complete\\!*\n\nImported: *{imported}*\nSkipped: *{skipped}* \\(duplicates/errors\\)",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    return TOTP_MENU

# ── DELETE ACCOUNT ─────────────────────────────────────────
async def delete_account_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    if not get_session(uid):
        await q.edit_message_text("Session expired\\.", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text(
        "🗑 *Delete Account*\n\n"
        "⚠️ *This will permanently delete your account and ALL TOTP data\\.*\n\n"
        "Enter your *current password* to continue:",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return DELETE_ACCOUNT_PASSWORD

async def delete_account_password(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pw = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    uid   = update.effective_user.id
    vault = get_session(uid)
    if not vault:
        await update.message.reply_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    u = get_user(vault)
    if not u:
        await update.message.reply_text("User not found\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    if not hmac.compare_digest(hash_pw(pw, bytes(u["pw_salt"])), bytes(u["password_hash"])):
        await update.message.reply_text(
            "❌ *Wrong password\\.* Account deletion cancelled\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU
    ctx.user_data["delete_vault"] = vault
    ctx.user_data["delete_owner"] = u["telegram_id"]
    await update.message.reply_text(
        "⚠️ *FINAL WARNING*\n\n"
        "This action *cannot be undone*\\. All TOTP data will be lost forever\\.\n\n"
        "Type exactly `YES DELETE` to confirm, or tap Cancel:",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return DELETE_ACCOUNT_CONFIRM

async def delete_account_confirm(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    text = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    if text != "YES DELETE":
        await update.message.reply_text(
            "❌ Confirmation failed\\. Account *not* deleted\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        ctx.user_data.pop("delete_vault", None)
        ctx.user_data.pop("delete_owner", None)
        return TOTP_MENU
    uid      = update.effective_user.id
    vault    = ctx.user_data.pop("delete_vault", None) or get_session(uid)
    owner_id = ctx.user_data.pop("delete_owner", None)
    if vault:
        with get_db() as c:
            c.execute("DELETE FROM totp_accounts WHERE vault_id=?",  (vault,))
            c.execute("DELETE FROM reset_otps WHERE vault_id=?",     (vault,))
            c.execute("DELETE FROM reset_attempts WHERE vault_id=?", (vault,))
            c.execute("DELETE FROM sessions WHERE vault_id=?",       (vault,))
            c.execute("DELETE FROM login_alerts WHERE vault_id=?",   (vault,))
            c.execute("DELETE FROM users WHERE vault_id=?",          (vault,))
            c.commit()
    clear_session(uid)
    ctx.user_data.clear()
    if owner_id:
        try:
            await ctx.bot.send_message(
                chat_id=owner_id,
                text=(
                    "🗑 *Account Deleted*\n\n"
                    f"Your vault `{em(vault)}` has been permanently deleted\\.\n"
                    "All TOTP data has been erased\\.\n\n"
                    "_If you did not perform this action, contact support immediately\\._"
                ),
                parse_mode="MarkdownV2",
            )
        except Exception as e:
            logger.error(f"Failed to notify owner {owner_id} of deletion: {e}")
    await update.message.reply_text(
        "🗑 *Account permanently deleted\\.* All data has been removed\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_auth(),
    )
    return AUTH_MENU

# ── GLOBAL AUTO-DETECT ──────────────────────────────────────
async def global_auto_detect(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    if not vault or not pw:
        return
    if ctx.user_data.get("_global_add") and update.message.text:
        name   = update.message.text.strip()
        secret = ctx.user_data.pop("pending_secret", None)
        ctx.user_data.pop("_global_add", None)
        if name and secret:
            ct, salt, iv = encrypt(secret, pw, vault)
            sk = load_user_secure_key(vault, pw)
            if sk:
                sk_ct, sk_s, sk_iv = sk_encrypt_totp(secret.encode(), sk, vault)
            else:
                sk_ct = sk_s = sk_iv = None
            with get_db() as c:
                c.execute(
                    "INSERT INTO totp_accounts (vault_id, name, issuer, secret_enc, salt, iv, "
                    "sk_enc, sk_salt, sk_iv) VALUES (?,?,?,?,?,?,?,?,?)",
                    (vault, name, "", ct, salt, iv, sk_ct, sk_s, sk_iv),
                )
                c.commit()
            code, remain = totp_now(secret)
            await update.message.reply_text(
                f"✅ *{em(name)}* added\\!\n\n"
                f"🔢 `{code[:3]} {code[3:]}`\n"
                f"⏱ {bar(remain)} {remain}s\n\n"
                f"🔒 _Encrypted with AES\\-256\\-GCM \\+ Secure Key_",
                parse_mode="MarkdownV2",
                reply_markup=kb_main(),
            )
        return
    result, handled = await _process_input(update, ctx, vault, pw)
    if handled and result is None and ctx.user_data.get("pending_secret"):
        ctx.user_data["_global_add"] = True

async def global_add_cancel(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    ctx.user_data.pop("pending_secret", None)
    ctx.user_data.pop("_global_add", None)
    await q.edit_message_text("❌ Cancelled\\.", parse_mode="MarkdownV2", reply_markup=kb_main())

# ── CANCEL / MENU ───────────────────────────────────────────
async def cancel_to_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    for k in [
        "pending_name", "signup_pw", "new_pw", "edit_id", "edit_name",
        "pending_secret", "_global_add", "reset_vid", "sreset_pw",
        "import_payload", "delete_vault", "delete_owner",
        "reset_secure_key", "reset_sk_skipped", "reset_new_pw", "reset_otp_verified",
    ]:
        ctx.user_data.pop(k, None)
    uid   = update.effective_user.id
    vault = get_session(uid)
    if vault:
        await q.edit_message_text("Choose an option:", reply_markup=kb_main())
        return TOTP_MENU
    await q.edit_message_text(
        "🛡 *BV Authenticator*\n\nPlease login or sign up\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_auth(),
    )
    return AUTH_MENU

async def main_menu_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.edit_message_text("Choose an option:", reply_markup=kb_main())
    return TOTP_MENU

# ── MAIN ────────────────────────────────────────────────────
def main():
    if not SERVER_KEY:
        raise RuntimeError("ENCRYPTION_KEY environment variable is not set")
    init_db()
    token = os.environ["BOT_TOKEN"]
    app   = ApplicationBuilder().token(token).build()
    private = filters.ChatType.PRIVATE

    conv = ConversationHandler(
        entry_points=[CommandHandler("start", start, filters=private)],
        states={
            AUTH_MENU: [
                CallbackQueryHandler(signup_start, pattern="^auth_signup$"),
                CallbackQueryHandler(login_start,  pattern="^auth_login$"),
            ],
            SIGNUP_PASSWORD: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, signup_pw),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            SIGNUP_CONFIRM: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, signup_confirm),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            LOGIN_CHOICE: [
                CallbackQueryHandler(login_auto,         pattern="^login_auto$"),
                CallbackQueryHandler(login_manual_start, pattern="^login_manual$"),
                CallbackQueryHandler(reset_pw_start,     pattern="^reset_pw_start$"),
                CallbackQueryHandler(cancel_to_menu,     pattern="^cancel_to_menu$"),
            ],
            LOGIN_ID_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, login_id_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            LOGIN_PASSWORD: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, login_pw),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            RESET_ID_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, reset_id_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            RESET_OTP_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, reset_otp_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            RESET_SECURE_KEY_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, reset_secure_key_input),
                CallbackQueryHandler(reset_sk_skip,  pattern="^reset_sk_skip$"),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            RESET_NEW_PW: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, reset_new_pw),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            RESET_NEW_PW_CONFIRM: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, reset_new_pw_confirm),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            TOTP_MENU: [
                CallbackQueryHandler(add_totp_start,       pattern="^add_totp$"),
                CallbackQueryHandler(list_totp,            pattern="^list_totp$"),
                CallbackQueryHandler(edit_totp_start,      pattern="^edit_totp$"),
                CallbackQueryHandler(show_profile,         pattern="^profile$"),
                CallbackQueryHandler(settings_menu,        pattern="^settings$"),
                CallbackQueryHandler(change_pw_start,      pattern="^change_pw$"),
                CallbackQueryHandler(settings_reset_start, pattern="^settings_reset_pw$"),
                CallbackQueryHandler(view_secure_key_start, pattern="^view_secure_key$"),
                CallbackQueryHandler(export_vault_start,   pattern="^export_vault$"),
                CallbackQueryHandler(import_vault_start,   pattern="^import_vault$"),
                CallbackQueryHandler(delete_account_start, pattern="^delete_account$"),
                CallbackQueryHandler(logout,               pattern="^logout$"),
                CallbackQueryHandler(main_menu_cb,         pattern="^main_menu$"),
                CallbackQueryHandler(change_tz_start,      pattern="^change_tz$"),
                CallbackQueryHandler(edit_pick,            pattern=r"^editpick_\d+$"),
                CallbackQueryHandler(edit_action,          pattern=r"^edit_action_(rename|delete|showsecret)$"),
                CallbackQueryHandler(edit_delete_confirm,  pattern="^edit_action_delete_confirm$"),
                CallbackQueryHandler(global_add_cancel,    pattern="^global_add_cancel$"),
            ],
            ADD_WAITING: [
                MessageHandler(private & (filters.PHOTO | filters.Document.IMAGE), handle_add_input),
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, handle_add_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            ADD_MANUAL_NAME: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, handle_manual_name),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            ADD_MANUAL_SECRET: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, handle_manual_secret),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            EDIT_PICK: [
                CallbackQueryHandler(edit_pick,    pattern=r"^editpick_\d+$"),
                CallbackQueryHandler(main_menu_cb, pattern="^main_menu$"),
            ],
            EDIT_ACTION: [
                CallbackQueryHandler(edit_action,         pattern=r"^edit_action_(rename|delete|showsecret)$"),
                CallbackQueryHandler(edit_delete_confirm, pattern="^edit_action_delete_confirm$"),
                CallbackQueryHandler(edit_totp_start,     pattern="^edit_totp$"),
            ],
            EDIT_RENAME_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, edit_rename_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            SHOW_SECRET_PW: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, show_secret_pw),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            CHANGE_PW_OLD: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, change_pw_old),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            CHANGE_PW_NEW: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, change_pw_new),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            CHANGE_PW_CONFIRM: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, change_pw_confirm),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            SETTINGS_RESET_OTP: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, settings_reset_otp),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            SETTINGS_RESET_PW: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, settings_reset_pw_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            SETTINGS_RESET_PW_CONFIRM: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, settings_reset_pw_confirm),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            DELETE_ACCOUNT_PASSWORD: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, delete_account_password),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            DELETE_ACCOUNT_CONFIRM: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, delete_account_confirm),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            EXPORT_PW1_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, export_pw1_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            EXPORT_PW2_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, export_pw2_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            IMPORT_FILE_WAIT: [
                MessageHandler(private & filters.Document.ALL, import_file_recv),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            IMPORT_PW_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, import_pw_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            TZ_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, change_tz_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            SECURE_KEY_VIEW_PW: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, view_secure_key_pw),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
        },
        fallbacks=[CommandHandler("start", start, filters=private)],
        allow_reentry=True,
        per_chat=True,
    )

    app.add_handler(conv)
    app.add_handler(CallbackQueryHandler(global_add_cancel,  pattern="^global_add_cancel$"))
    app.add_handler(CallbackQueryHandler(handle_alert_ack,   pattern="^alert_ack_"))
    app.add_handler(CallbackQueryHandler(handle_alert_logout, pattern="^alert_logout_"))
    app.add_handler(MessageHandler(private & (filters.PHOTO | filters.Document.IMAGE), global_auto_detect))
    app.add_handler(MessageHandler(private & filters.TEXT & ~filters.COMMAND, global_auto_detect))

    logger.info("BV Authenticator Bot started.")
    app.run_polling(drop_pending_updates=True)

if __name__ == "__main__":
    main()
