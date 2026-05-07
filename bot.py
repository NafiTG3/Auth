import os, re, hmac, time, json, struct, base64, hashlib, sqlite3, logging, datetime, secrets, string, asyncio
import datetime as _dt
from zoneinfo import ZoneInfo as _ZoneInfo
from io import BytesIO
from urllib.parse import urlparse, parse_qs, unquote

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    ApplicationBuilder, CommandHandler, CallbackQueryHandler,
    MessageHandler, ConversationHandler, ContextTypes, filters
)
from utils import SlidingWindowRateLimiter, RateLimitedRetrySender
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from argon2.low_level import hash_secret_raw, Type as Argon2Type
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
    NOTE_INPUT,           # new: typing note for a TOTP account
    IMPORT_OVERRIDE_WAIT, # new: waiting for merge/replace choice during import
    SEARCH_TOTP_INPUT,    # new: typing search query for TOTP search
    OFFLINE_AUTO_BACKUP,  # new: offline auto-backup settings menu
    SIGNUP_TERMS,         # new: terms & privacy agreement screen before signup
    CAPTCHA_VERIFY,       # new: image CAPTCHA verification before signup
    LOGIN_CAPTCHA,        # new: image CAPTCHA verification before login
) = range(40)

DB_PATH             = os.environ.get("DB_PATH", "auth.db")
SERVER_KEY          = os.environ.get("ENCRYPTION_KEY", "").encode()
BOT_USERNAME        = os.environ.get("BOT_USERNAME", "TotpNafiBot")  # set without @
ADMIN_GROUP_ID      = int(os.environ.get("GROUP_ID", "0"))           # admin group
PBKDF2_ITER         = 1_000_000
OTP_TTL             = 60
MAX_RESET_ATTEMPTS  = 3
FREEZE_HOURS        = 18
ALERT_VISIBLE_HOURS = 72
SHARE_LINK_TTL      = 600   # 10 minutes
MAX_LOGIN_ATTEMPTS  = 5     # max failed logins before freeze
LOGIN_FREEZE_HOURS  = 18    # freeze duration
TOTP_PER_PAGE       = 5     # TOTP entries per page in list view
MAX_TOTP_PER_VAULT  = 200   # max TOTP accounts per vault
MAX_TOTP_DUPLICATE  = 15    # max duplicate TOTP entries allowed per vault
TOTP_ADD_ENABLED    = True  # global toggle: False = no user can add new TOTP accounts
SHARE_MAX_TOTP      = 5     # maximum TOTPs a user can share at once
NOTE_MAX_LEN        = 10    # max note characters
BACKUP_REMINDER_WEEKLY  = "weekly"
BACKUP_REMINDER_MONTHLY = "monthly"
BD_TZ = "Asia/Dhaka"       # Bangladesh timezone for admin panel

# Admin-configurable defaults for offline backup schedule (weekday: Monday=0..Sunday=6)
DEFAULT_OFFLINE_BACKUP_WEEKDAY      = 5    # Saturday (default)
DEFAULT_OFFLINE_BACKUP_MONTHLY_DATE = 1    # 1st of each month (default)

# Admin-configurable defaults for backup reminder schedule
DEFAULT_REMINDER_WEEKDAY      = 5    # Saturday (default)
DEFAULT_REMINDER_MONTHLY_DATE = 1    # 1st of each month (default)

_WEEKDAY_MAP = {
    "monday": 0, "tuesday": 1, "wednesday": 2, "thursday": 3,
    "friday": 4, "saturday": 5, "sunday": 6,
}

# ── Rate limit constants ────────────────────────────────────
TOTP_NAME_MAX_LEN      = 20    # max TOTP account name length
MAX_DAILY_LOGINS       = 7     # max successful logins per day per telegram_id
MAX_WEEKLY_SIGNUPS     = 2     # max signups per week per telegram_id
MAX_LIFETIME_VAULTS    = 5     # max distinct vaults a telegram_id can ever login to
MAX_TOTP_PER_MINUTE    = 20    # max TOTP accounts added in 1 minute per vault

# ── Bot-wide toggleable settings (stored in memory + DB bot_settings table) ──
_bot_settings: dict = {
    "maintenance": False,
    "signup_enabled": True,
    "login_enabled": True,
    "public_export_limit": 2,
    "public_import_limit": 3,
    "public_export_enabled": True,
    "public_import_enabled": True,
    "donate_message": None,
}

# ── In-memory session password cache for auto-backup ─────────
# Populated on login/signup, cleared on logout. Never persisted to DB.
_session_pw_cache: dict = {}   # vault_id -> plaintext password

def _oab_pw_enc_key(vault_id: str) -> bytes:
    """Derive a 32-byte AES key for encrypting the backup password in DB.
    Uses SERVER_KEY + vault_id so it is unique per vault and tied to the server."""
    salt = hashlib.sha256(SERVER_KEY + b":oabpw:" + vault_id.encode()).digest()[:16]
    return PBKDF2HMAC(
        algorithm=hashes.SHA256(), length=32, salt=salt, iterations=100_000
    ).derive(SERVER_KEY + vault_id.encode())

def _oab_store_password(telegram_id: int, vault_id: str, password: str):
    """Encrypt and persist the user's password for offline auto-backup."""
    key  = _oab_pw_enc_key(vault_id)
    iv   = os.urandom(12)
    salt = os.urandom(16)   # stored but not used for key (kept for schema compat)
    ct   = AESGCM(key).encrypt(iv, password.encode(), None)
    with get_db() as c:
        c.execute(
            "INSERT INTO auto_backup_settings (telegram_id, pw_enc, pw_salt, pw_iv) VALUES (?,?,?,?) "
            "ON CONFLICT(telegram_id) DO UPDATE SET pw_enc=excluded.pw_enc, "
            "pw_salt=excluded.pw_salt, pw_iv=excluded.pw_iv",
            (telegram_id, ct, salt, iv),
        )
        c.commit()

def _oab_load_password(telegram_id: int, vault_id: str) -> str | None:
    """Load and decrypt the stored backup password. Returns None if not available."""
    with get_db() as c:
        row = c.execute(
            "SELECT pw_enc, pw_iv FROM auto_backup_settings WHERE telegram_id=?",
            (telegram_id,)
        ).fetchone()
    if not row or not row["pw_enc"]:
        return None
    try:
        key = _oab_pw_enc_key(vault_id)
        return AESGCM(key).decrypt(bytes(row["pw_iv"]), bytes(row["pw_enc"]), None).decode()
    except Exception as e:
        logger.warning(f"_oab_load_password failed for {telegram_id}: {e}")
        return None

# ── Rate Limit Helpers ──────────────────────────────────────

def _today_bucket() -> str:
    """Return current UTC date string YYYY-MM-DD for daily buckets."""
    return datetime.datetime.utcnow().strftime("%Y-%m-%d")

def _week_bucket() -> str:
    """Return current ISO week string YYYY-WNN for weekly buckets."""
    d = datetime.datetime.utcnow()
    return d.strftime("%Y-W%W")

def check_daily_login_limit(telegram_id: int) -> bool:
    """Returns True if the user has NOT exceeded MAX_DAILY_LOGINS today."""
    today = _today_bucket()
    with get_db() as c:
        row = c.execute(
            "SELECT count, day_bucket FROM daily_login_counts WHERE telegram_id=?",
            (telegram_id,)
        ).fetchone()
    if not row or row["day_bucket"] != today:
        return True   # fresh day or no record
    return row["count"] < MAX_DAILY_LOGINS

def record_daily_login(telegram_id: int):
    """Increment today's login counter for a telegram_id."""
    today = _today_bucket()
    with get_db() as c:
        row = c.execute(
            "SELECT count, day_bucket FROM daily_login_counts WHERE telegram_id=?",
            (telegram_id,)
        ).fetchone()
        if not row or row["day_bucket"] != today:
            c.execute(
                "INSERT INTO daily_login_counts (telegram_id, count, day_bucket) VALUES (?,?,?) "
                "ON CONFLICT(telegram_id) DO UPDATE SET count=1, day_bucket=excluded.day_bucket",
                (telegram_id, 1, today),
            )
        else:
            c.execute(
                "UPDATE daily_login_counts SET count=count+1 WHERE telegram_id=?",
                (telegram_id,)
            )
        c.commit()

def check_weekly_signup_limit(telegram_id: int) -> bool:
    """Returns True if the user has NOT exceeded MAX_WEEKLY_SIGNUPS this week."""
    week = _week_bucket()
    with get_db() as c:
        row = c.execute(
            "SELECT count, week_bucket FROM weekly_signup_counts WHERE telegram_id=?",
            (telegram_id,)
        ).fetchone()
    if not row or row["week_bucket"] != week:
        return True
    return row["count"] < MAX_WEEKLY_SIGNUPS

def record_weekly_signup(telegram_id: int):
    """Increment this week's signup counter for a telegram_id."""
    week = _week_bucket()
    with get_db() as c:
        row = c.execute(
            "SELECT count, week_bucket FROM weekly_signup_counts WHERE telegram_id=?",
            (telegram_id,)
        ).fetchone()
        if not row or row["week_bucket"] != week:
            c.execute(
                "INSERT INTO weekly_signup_counts (telegram_id, count, week_bucket) VALUES (?,?,?) "
                "ON CONFLICT(telegram_id) DO UPDATE SET count=1, week_bucket=excluded.week_bucket",
                (telegram_id, 1, week),
            )
        else:
            c.execute(
                "UPDATE weekly_signup_counts SET count=count+1 WHERE telegram_id=?",
                (telegram_id,)
            )
        c.commit()

def check_vault_login_limit(telegram_id: int, vault_id: str) -> bool:
    """Returns True if the telegram_id can login to this vault.
    Allowed if vault already in history OR total distinct vaults < MAX_LIFETIME_VAULTS."""
    with get_db() as c:
        # Check if this vault is already known for this telegram_id
        known = c.execute(
            "SELECT 1 FROM vault_login_history WHERE telegram_id=? AND vault_id=?",
            (telegram_id, vault_id)
        ).fetchone()
        if known:
            return True
        # Count distinct vaults ever logged in from this telegram_id
        cnt = c.execute(
            "SELECT COUNT(*) AS n FROM vault_login_history WHERE telegram_id=?",
            (telegram_id,)
        ).fetchone()["n"]
    return cnt < MAX_LIFETIME_VAULTS

def record_vault_login(telegram_id: int, vault_id: str):
    """Record this (telegram_id, vault_id) pair in history."""
    with get_db() as c:
        c.execute(
            "INSERT OR IGNORE INTO vault_login_history (telegram_id, vault_id) VALUES (?,?)",
            (telegram_id, vault_id),
        )
        c.commit()

def is_user_signup_disabled(telegram_id: int) -> bool:
    """Returns True if this specific Telegram ID has been individually blocked from signup."""
    with get_db() as c:
        row = c.execute(
            "SELECT 1 FROM user_signup_disabled WHERE telegram_id=?", (telegram_id,)
        ).fetchone()
    return row is not None

def set_user_signup_disabled(telegram_id: int, disabled: bool):
    """Enable or disable signup for a specific Telegram ID."""
    with get_db() as c:
        if disabled:
            c.execute(
                "INSERT OR IGNORE INTO user_signup_disabled (telegram_id) VALUES (?)",
                (telegram_id,)
            )
        else:
            c.execute(
                "DELETE FROM user_signup_disabled WHERE telegram_id=?",
                (telegram_id,)
            )
        c.commit()

def get_all_signup_disabled_users() -> list:
    """Return list of all telegram_ids with signup individually disabled."""
    with get_db() as c:
        rows = c.execute(
            "SELECT telegram_id FROM user_signup_disabled ORDER BY disabled_at DESC"
        ).fetchall()
    return [r["telegram_id"] for r in rows]


# ── Activity Log System ────────────────────────────────────────────────────

import collections as _collections
_activity_log: _collections.deque = _collections.deque(maxlen=5000)  # last 5000 events in RAM

def bot_log(category: str, event: str, **kwargs):
    """Record a structured activity log entry. Stored in RAM ring buffer."""
    try:
        now_bd = _dt.datetime.now(_BDT)
        ts_str = now_bd.strftime("%Y-%m-%d %H:%M:%S BDT")
        kv_parts = "  ".join(f"{k}={v}" for k, v in kwargs.items())
        line = f"[{ts_str}] [{category}] [{event}]"
        if kv_parts:
            line += f"  {kv_parts}"
        _activity_log.append((now_bd.timestamp(), line))
    except Exception:
        pass  # logging must never crash the bot


# ── CAPTCHA helpers ────────────────────────────────────────────────────────

import random as _random
import io     as _io

CAPTCHA_MAX_FAILS = 3
CAPTCHA_BAN_HOURS = 6

def _gen_captcha_image(question: str) -> bytes:
    """Generate a simple math question image using Pillow. Returns PNG bytes."""
    from PIL import Image, ImageDraw, ImageFont
    img  = Image.new("RGB", (280, 90), color=(240, 240, 245))
    draw = ImageDraw.Draw(img)
    # Noise dots
    for _ in range(200):
        x = _random.randint(0, 279)
        y = _random.randint(0, 89)
        draw.point((x, y), fill=(_random.randint(150, 210),) * 3)
    # Noise lines
    for _ in range(6):
        draw.line(
            [(_random.randint(0, 279), _random.randint(0, 89)),
             (_random.randint(0, 279), _random.randint(0, 89))],
            fill=(_random.randint(180, 220),) * 3, width=1
        )
    # Text
    try:
        font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", 36)
    except Exception:
        font = ImageFont.load_default()
    draw.text((30, 22), question, fill=(30, 30, 120), font=font)
    buf = _io.BytesIO()
    img.save(buf, format="PNG")
    return buf.getvalue()


def make_captcha() -> dict:
    """Generate a math CAPTCHA with +, -, ×, ÷ operators.
    Returns {question, answer, choices, image_bytes}.
    """
    op_sym, op_fn = _random.choice([
        ("+", lambda a, b: a + b),
        ("-", lambda a, b: a - b),
        ("*", lambda a, b: a * b),   # * shown in image, easy to type in buttons
        ("/", lambda a, b: a // b),  # / shown in image, easy to type in buttons
    ])
    if op_sym == "+":
        a, b = _random.randint(1, 15), _random.randint(1, 15)
    elif op_sym == "-":
        a = _random.randint(5, 20)
        b = _random.randint(1, a)          # ensure a >= b so result >= 0
    elif op_sym == "*":
        a, b = _random.randint(2, 9), _random.randint(2, 9)
    else:  # /
        b = _random.randint(2, 9)
        a = b * _random.randint(2, 9)      # ensure exact division
    answer   = op_fn(a, b)
    question = f"{a} {op_sym} {b} = ?"
    # 3 wrong choices, distinct, non-negative, != answer
    # For larger answers (multiplication), use wider deltas
    max_delta = max(5, answer // 3)
    wrongs = set()
    attempts = 0
    while len(wrongs) < 3 and attempts < 100:
        attempts += 1
        delta = _random.randint(-max_delta, max_delta)
        if delta == 0:
            continue
        wrong = answer + delta
        if wrong > 0 and wrong != answer:
            wrongs.add(wrong)
    choices = list(wrongs) + [answer]
    _random.shuffle(choices)
    return {
        "question":    question,
        "answer":      answer,
        "choices":     choices,
        "image_bytes": _gen_captcha_image(question),
    }


def check_captcha_ban(telegram_id: int) -> int:
    """Returns remaining ban seconds if user is banned, else 0."""
    now = int(time.time())
    with get_db() as c:
        row = c.execute(
            "SELECT banned_until FROM captcha_attempts WHERE telegram_id=?", (telegram_id,)
        ).fetchone()
    if not row:
        return 0
    return max(0, row["banned_until"] - now)


def record_captcha_fail(telegram_id: int) -> bool:
    """Record a CAPTCHA failure. Returns True if user is now banned."""
    now = int(time.time())
    with get_db() as c:
        row = c.execute(
            "SELECT fail_count FROM captcha_attempts WHERE telegram_id=?", (telegram_id,)
        ).fetchone()
        fails = (row["fail_count"] if row else 0) + 1
        ban_until = now + CAPTCHA_BAN_HOURS * 3600 if fails >= CAPTCHA_MAX_FAILS else 0
        c.execute(
            "INSERT INTO captcha_attempts (telegram_id, fail_count, banned_until) VALUES (?,?,?) "
            "ON CONFLICT(telegram_id) DO UPDATE SET fail_count=excluded.fail_count, banned_until=excluded.banned_until",
            (telegram_id, fails, ban_until),
        )
        c.commit()
    return ban_until > 0


def reset_captcha_fails(telegram_id: int):
    """Clear CAPTCHA failure count after successful signup."""
    with get_db() as c:
        c.execute("DELETE FROM captcha_attempts WHERE telegram_id=?", (telegram_id,))
        c.commit()


# ── OTP Request Rate-Limit helpers ─────────────────────────────────────────

OTP_HOURLY_LIMIT = 2   # max OTP requests per hour
OTP_DAILY_LIMIT  = 5   # max OTP requests per 24h

def check_otp_request_limit(vault_id: str) -> tuple:
    """Check if vault can request an OTP.
    Returns (allowed: bool, wait_seconds: int, reason: str).
    """
    now = int(time.time())
    hour_ago  = now - 3600
    day_ago   = now - 86400

    # Cleanup old records first
    with get_db() as c:
        c.execute("DELETE FROM otp_request_log WHERE requested_at < ?", (day_ago,))
        c.commit()

    with get_db() as c:
        hourly = c.execute(
            "SELECT COUNT(*) AS n, MIN(requested_at) AS oldest FROM otp_request_log "
            "WHERE vault_id=? AND requested_at >= ?", (vault_id, hour_ago)
        ).fetchone()
        daily = c.execute(
            "SELECT COUNT(*) AS n, MIN(requested_at) AS oldest FROM otp_request_log "
            "WHERE vault_id=? AND requested_at >= ?", (vault_id, day_ago)
        ).fetchone()

    if hourly["n"] >= OTP_HOURLY_LIMIT:
        wait = max(0, (hourly["oldest"] or now) + 3600 - now)
        return False, wait, "hourly"
    if daily["n"] >= OTP_DAILY_LIMIT:
        wait = max(0, (daily["oldest"] or now) + 86400 - now)
        return False, wait, "daily"
    return True, 0, ""


def record_otp_request(vault_id: str):
    """Insert a new OTP request record."""
    with get_db() as c:
        c.execute(
            "INSERT INTO otp_request_log (vault_id) VALUES (?)", (vault_id,)
        )
        c.commit()


# ── Telegram Ban helpers ───────────────────────────────────────────────────

def is_telegram_banned(telegram_id: int) -> bool:
    """Returns True if this Telegram ID is banned from using the bot."""
    with get_db() as c:
        row = c.execute(
            "SELECT 1 FROM telegram_banned WHERE telegram_id=?", (telegram_id,)
        ).fetchone()
    return row is not None

def set_telegram_ban(telegram_id: int, username: str, banned: bool):
    """Ban or unban a Telegram ID."""
    with get_db() as c:
        if banned:
            c.execute(
                "INSERT OR REPLACE INTO telegram_banned (telegram_id, tg_username) VALUES (?,?)",
                (telegram_id, username or "")
            )
        else:
            c.execute(
                "DELETE FROM telegram_banned WHERE telegram_id=?", (telegram_id,)
            )
        c.commit()

def get_all_banned_users() -> list:
    """Return all banned telegram entries as list of dicts."""
    with get_db() as c:
        rows = c.execute(
            "SELECT telegram_id, tg_username, banned_at FROM telegram_banned ORDER BY banned_at DESC"
        ).fetchall()
    return [dict(r) for r in rows]


# ── Statistics helpers ─────────────────────────────────────────────────────
_BDT = _ZoneInfo("Asia/Dhaka")

def _bdt_day_start(days_ago: int = 0) -> int:
    """Return Unix timestamp of BDT midnight N days ago.
    Uses explicit datetime construction to avoid zoneinfo DST/fold issues with replace().
    """
    now_bdt  = _dt.datetime.now(_BDT)
    target   = now_bdt.date() - _dt.timedelta(days=days_ago)
    midnight = _dt.datetime(target.year, target.month, target.day,
                            0, 0, 0, tzinfo=_BDT)
    return int(midnight.timestamp())

def _bdt_week_start() -> int:
    """Return Unix timestamp of last Saturday BDT 00:00.
    weekday(): Mon=0, Tue=1, Wed=2, Thu=3, Fri=4, Sat=5, Sun=6
    days_since_sat = (weekday - 5) % 7
      Sat=5 -> 0  (today is Saturday)
      Sun=6 -> 1  (yesterday was Saturday)
      Mon=0 -> 2  (2 days ago was Saturday)
      ...
    """
    now_bdt        = _dt.datetime.now(_BDT)
    days_since_sat = (now_bdt.weekday() - 5) % 7
    sat_date       = now_bdt.date() - _dt.timedelta(days=days_since_sat)
    sat_midnight   = _dt.datetime(sat_date.year, sat_date.month, sat_date.day,
                                  0, 0, 0, tzinfo=_BDT)
    return int(sat_midnight.timestamp())

def _bdt_month_start() -> int:
    """Return Unix timestamp of 1st day of current BDT month at 00:00."""
    now_bdt  = _dt.datetime.now(_BDT)
    first    = _dt.datetime(now_bdt.year, now_bdt.month, 1,
                            0, 0, 0, tzinfo=_BDT)
    return int(first.timestamp())

def record_stat(event_type: str, telegram_id: int = 0, vault_id: str = ""):
    """Insert one event row into stats_events."""
    try:
        with get_db() as c:
            c.execute(
                "INSERT INTO stats_events (event_type, telegram_id, vault_id) VALUES (?,?,?)",
                (event_type, telegram_id, vault_id)
            )
            c.commit()
    except Exception as e:
        logger.warning(f"record_stat({event_type}): {e}")

def _count_stat(event_type: str, since_ts: int) -> int:
    """Count events of a given type since a Unix timestamp."""
    with get_db() as c:
        row = c.execute(
            "SELECT COUNT(*) AS n FROM stats_events WHERE event_type=? AND ts>=?",
            (event_type, since_ts)
        ).fetchone()
    return row["n"] if row else 0

def _count_disabled_net(since_ts: int) -> int:
    """Count accounts that are STILL disabled (not re-enabled) in a period."""
    with get_db() as c:
        row = c.execute(
            "SELECT COUNT(*) AS n FROM stats_events WHERE event_type='account_disabled' AND ts>=?",
            (since_ts,)
        ).fetchone()
        disabled = row["n"] if row else 0
        row2 = c.execute(
            "SELECT COUNT(*) AS n FROM stats_events WHERE event_type='account_enabled' AND ts>=?",
            (since_ts,)
        ).fetchone()
        enabled = row2["n"] if row2 else 0
    return max(0, disabled - enabled)

def _count_active(since_ts: int) -> int:
    """Count distinct users who had any session (vault active) since since_ts."""
    with get_db() as c:
        row = c.execute(
            "SELECT COUNT(DISTINCT telegram_id) AS n FROM stats_events "
            "WHERE event_type='user_active' AND ts>=?",
            (since_ts,)
        ).fetchone()
    return row["n"] if row else 0

def _build_stats_text(label: str, since_ts: int, include_active: bool = True) -> str:
    """Build a formatted statistics message for the given time window."""
    new_join  = _count_stat("signup",              since_ts)
    active    = _count_active(since_ts) if include_active else None
    disabled  = _count_disabled_net(since_ts)
    deleted   = _count_stat("account_deleted",     since_ts)
    totp_add  = _count_stat("totp_added",          since_ts)
    login_ok  = _count_stat("login_success",       since_ts)
    login_fail= _count_stat("login_fail",          since_ts)
    reset_ok  = _count_stat("reset_success",       since_ts)
    reset_skip= _count_stat("reset_success_skip",  since_ts)
    reset_fail= _count_stat("reset_fail",          since_ts)

    lines = [f"📊 *{label} Statistics*"]
    lines.append(f"👥 New Joined       : {new_join} User")
    if include_active:
        lines.append(f"🟢 Active Users     : {active} User")
    lines.append(f"🔒 Disabled Accts   : {disabled} Account")
    lines.append(f"🗑 Deleted Accts    : {deleted} Account")
    lines.append(f"🔐 TOTP Added       : {totp_add} TOTP")
    lines.append(f"✅ Login Success    : {login_ok} Success")
    lines.append(f"❌ Login Failed     : {login_fail} Failed")
    lines.append(f"✅ Reset Success    : {reset_ok} Success")
    lines.append(f"⏭ Reset w/ Skip    : {reset_skip} Success")
    lines.append(f"❌ Reset Failed     : {reset_fail} Failed")
    return "\n".join(lines)


def is_user_login_disabled(telegram_id: int) -> bool:
    """Returns True if this specific Telegram ID has been individually blocked from login."""
    with get_db() as c:
        row = c.execute(
            "SELECT 1 FROM user_login_disabled WHERE telegram_id=?", (telegram_id,)
        ).fetchone()
    return row is not None

def set_user_login_disabled(telegram_id: int, disabled: bool):
    """Enable or disable login for a specific Telegram ID."""
    with get_db() as c:
        if disabled:
            c.execute(
                "INSERT OR IGNORE INTO user_login_disabled (telegram_id) VALUES (?)",
                (telegram_id,)
            )
        else:
            c.execute(
                "DELETE FROM user_login_disabled WHERE telegram_id=?",
                (telegram_id,)
            )
        c.commit()

def get_all_login_disabled_users() -> list:
    """Return list of all telegram_ids with login individually disabled."""
    with get_db() as c:
        rows = c.execute(
            "SELECT telegram_id FROM user_login_disabled ORDER BY disabled_at DESC"
        ).fetchall()
    return [r["telegram_id"] for r in rows]


def get_vault_custom_limits(vault_id: str):
    """Return (max_per_vault, max_per_min) for a vault.
    Returns None for each field if no custom limit is set (fall back to global)."""
    with get_db() as c:
        row = c.execute(
            "SELECT max_per_vault, max_per_min FROM vault_custom_limits WHERE vault_id=?",
            (vault_id,)
        ).fetchone()
    if not row:
        return None, None
    return row["max_per_vault"], row["max_per_min"]

def get_effective_vault_max(vault_id: str) -> int:
    """Return the effective max TOTP per vault for this vault (custom or global)."""
    custom, _ = get_vault_custom_limits(vault_id)
    return custom if custom is not None else MAX_TOTP_PER_VAULT

def get_effective_per_min_limit(vault_id: str) -> int:
    """Return the effective per-minute TOTP limit for this vault (custom or global)."""
    _, custom = get_vault_custom_limits(vault_id)
    return custom if custom is not None else MAX_TOTP_PER_MINUTE

def set_vault_max_limit(vault_id: str, limit: int):
    """Set a custom max TOTP per vault limit for a specific vault."""
    with get_db() as c:
        c.execute(
            "INSERT INTO vault_custom_limits (vault_id, max_per_vault) VALUES (?,?) "
            "ON CONFLICT(vault_id) DO UPDATE SET max_per_vault=excluded.max_per_vault",
            (vault_id, limit)
        )
        c.commit()

def set_vault_per_min_limit(vault_id: str, limit: int):
    """Set a custom per-minute TOTP limit for a specific vault."""
    with get_db() as c:
        c.execute(
            "INSERT INTO vault_custom_limits (vault_id, max_per_min) VALUES (?,?) "
            "ON CONFLICT(vault_id) DO UPDATE SET max_per_min=excluded.max_per_min",
            (vault_id, limit)
        )
        c.commit()

# ── Export / Import limit helpers ─────────────────────────────────────────────

def get_public_export_limit() -> int:
    return int(_bot_settings.get("public_export_limit", 2))

def get_public_import_limit() -> int:
    return int(_bot_settings.get("public_import_limit", 3))

def is_public_export_enabled() -> bool:
    return bool(_bot_settings.get("public_export_enabled", True))

def is_public_import_enabled() -> bool:
    return bool(_bot_settings.get("public_import_enabled", True))

def get_vault_ei_limits(vault_id: str) -> tuple:
    """Return (export_limit, import_limit) for a vault, or (None, None) if not set."""
    with get_db() as c:
        row = c.execute(
            "SELECT export_limit, import_limit FROM vault_ei_limits WHERE vault_id=?", (vault_id,)
        ).fetchone()
    if row:
        return row["export_limit"], row["import_limit"]
    return None, None

def get_effective_export_limit(vault_id: str) -> int:
    """Return the effective daily export limit for this vault (specific > public)."""
    specific, _ = get_vault_ei_limits(vault_id)
    return specific if specific is not None else get_public_export_limit()

def get_effective_import_limit(vault_id: str) -> int:
    """Return the effective daily import limit for this vault (specific > public)."""
    _, specific = get_vault_ei_limits(vault_id)
    return specific if specific is not None else get_public_import_limit()

def set_vault_export_limit(vault_id: str, limit: int):
    with get_db() as c:
        c.execute(
            "INSERT INTO vault_ei_limits (vault_id, export_limit) VALUES (?,?) "
            "ON CONFLICT(vault_id) DO UPDATE SET export_limit=excluded.export_limit",
            (vault_id, limit)
        )
        c.commit()

def set_vault_import_limit(vault_id: str, limit: int):
    with get_db() as c:
        c.execute(
            "INSERT INTO vault_ei_limits (vault_id, import_limit) VALUES (?,?) "
            "ON CONFLICT(vault_id) DO UPDATE SET import_limit=excluded.import_limit",
            (vault_id, limit)
        )
        c.commit()

def _today_utc() -> str:
    return datetime.datetime.utcnow().strftime("%Y-%m-%d")

def get_ei_usage(vault_id: str, action: str) -> int:
    """Return how many times today this vault has done export or import."""
    with get_db() as c:
        row = c.execute(
            "SELECT count FROM vault_ei_usage WHERE vault_id=? AND action=? AND day=?",
            (vault_id, action, _today_utc())
        ).fetchone()
    return row["count"] if row else 0

def record_ei_usage(vault_id: str, action: str):
    """Increment daily usage count for export or import."""
    day = _today_utc()
    with get_db() as c:
        c.execute(
            "INSERT INTO vault_ei_usage (vault_id, action, day, count) VALUES (?,?,?,1) "
            "ON CONFLICT(vault_id, action, day) DO UPDATE SET count=count+1",
            (vault_id, action, day)
        )
        c.commit()

def check_export_allowed(vault_id: str) -> tuple:
    """Returns (allowed: bool, reason: str or None)."""
    if not is_public_export_enabled():
        return False, "disabled"
    limit = get_effective_export_limit(vault_id)
    used  = get_ei_usage(vault_id, "export")
    if used >= limit:
        return False, "limit"
    return True, None

def check_import_allowed(vault_id: str) -> tuple:
    """Returns (allowed: bool, reason: str or None)."""
    if not is_public_import_enabled():
        return False, "disabled"
    limit = get_effective_import_limit(vault_id)
    used  = get_ei_usage(vault_id, "import")
    if used >= limit:
        return False, "limit"
    return True, None

# ── End export/import helpers ──────────────────────────────────────────────────

# Per-vault asyncio lock: ensures scans for the same vault are processed one at a time.
# 100 images sent at once → each waits its turn → limit check happens BEFORE each scan.
_vault_add_locks: dict = {}

def _get_vault_lock(vault_id: str):
    """Return the asyncio.Lock for this vault (creates one if needed)."""
    if vault_id not in _vault_add_locks:
        _vault_add_locks[vault_id] = asyncio.Lock()
    return _vault_add_locks[vault_id]


def check_totp_add_rate(vault_id: str) -> bool:
    """Check-only (non-consuming). True if under per-minute limit."""
    now       = int(time.time())
    eff_limit = get_effective_per_min_limit(vault_id)
    with get_db() as c:
        row = c.execute(
            "SELECT count, window_start FROM totp_add_rate WHERE vault_id=?",
            (vault_id,)
        ).fetchone()
    if not row or now - row["window_start"] >= 60:
        return True
    return row["count"] < eff_limit


async def check_and_record_totp_add(vault_id: str) -> bool:
    """Async atomic check-and-increment under a per-vault asyncio.Lock.
    Returns True if allowed (and increments counter), False if limit exceeded.
    When 100 images arrive simultaneously, each awaits the lock so they process
    one at a time — limit check always happens BEFORE the scan for each one.
    """
    lock = _get_vault_lock(vault_id)
    async with lock:
        now       = int(time.time())
        eff_limit = get_effective_per_min_limit(vault_id)
        with get_db() as c:
            row = c.execute(
                "SELECT count, window_start FROM totp_add_rate WHERE vault_id=?",
                (vault_id,)
            ).fetchone()
            if not row or now - row["window_start"] >= 60:
                current = 0
            else:
                current = row["count"]
            if current >= eff_limit:
                return False  # limit exceeded, scan skipped
            # Increment
            if current == 0:
                c.execute(
                    "INSERT INTO totp_add_rate (vault_id, count, window_start) VALUES (?,?,?) "
                    "ON CONFLICT(vault_id) DO UPDATE SET count=1, window_start=excluded.window_start",
                    (vault_id, 1, now),
                )
            else:
                c.execute(
                    "UPDATE totp_add_rate SET count=count+1 WHERE vault_id=?",
                    (vault_id,)
                )
            c.commit()
        return True


def record_totp_add(vault_id: str):
    """Legacy increment (used after check_totp_add_rate separately). Prefer check_and_record_totp_add."""
    now = int(time.time())
    with get_db() as c:
        row = c.execute(
            "SELECT count, window_start FROM totp_add_rate WHERE vault_id=?",
            (vault_id,)
        ).fetchone()
        if not row or now - row["window_start"] >= 60:
            c.execute(
                "INSERT INTO totp_add_rate (vault_id, count, window_start) VALUES (?,?,?) "
                "ON CONFLICT(vault_id) DO UPDATE SET count=1, window_start=excluded.window_start",
                (vault_id, 1, now),
            )
        else:
            c.execute(
                "UPDATE totp_add_rate SET count=count+1 WHERE vault_id=?",
                (vault_id,)
            )
        c.commit()

def _auto_suffix_name(vault_id: str, requested_name: str) -> str:
    """If 'Google' already exists, return 'Google 1', 'Google 2', etc."""
    base = requested_name.strip()[:TOTP_NAME_MAX_LEN]
    with get_db() as c:
        existing = {
            r["name"] for r in c.execute(
                "SELECT name FROM totp_accounts WHERE vault_id=?", (vault_id,)
            ).fetchall()
        }
    if base not in existing:
        return base
    for i in range(1, 1000):
        candidate = f"{base[:TOTP_NAME_MAX_LEN - len(str(i)) - 1]} {i}"
        if candidate not in existing:
            return candidate
    return base  # fallback (should never happen)

# ── DB ─────────────────────────────────────────────────────
import threading as _threading

_db_local = _threading.local()   # one persistent connection per thread

def _get_thread_conn() -> sqlite3.Connection:
    """Return a long-lived, WAL-enabled SQLite connection for the current thread.
    Opens once per thread, reuses afterwards — eliminates per-call connect overhead.
    check_same_thread=False is safe here because we use thread-local storage.
    """
    conn = getattr(_db_local, "conn", None)
    if conn is None:
        conn = sqlite3.connect(
            DB_PATH,
            timeout=30.0,
            check_same_thread=False,   # safe: one conn per thread via _db_local
        )
        conn.row_factory = sqlite3.Row
        # WAL mode: readers never block writers, writers never block readers
        conn.execute("PRAGMA journal_mode=WAL")
        # Larger cache = fewer disk reads
        conn.execute("PRAGMA cache_size=-8000")   # 8 MB per thread
        # Sync less aggressively (WAL already protects durability)
        conn.execute("PRAGMA synchronous=NORMAL")
        _db_local.conn = conn
    return conn


class _DB:
    """Context manager that wraps the thread-local connection.
    Commits on clean exit, rolls back on exception, never closes the connection
    (it stays alive for the thread lifetime for performance).
    """
    def __enter__(self) -> sqlite3.Connection:
        self._conn = _get_thread_conn()
        return self._conn

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            try:
                self._conn.commit()
            except Exception as e:
                logger.warning(f"DB commit failed: {e}")
        else:
            try:
                self._conn.rollback()
            except Exception:
                pass
        return False   # do NOT suppress exceptions

    # Allow using _DB instance directly (legacy callers do `with get_db() as c: c.execute(...)`)
    def execute(self, *a, **kw):
        return _get_thread_conn().execute(*a, **kw)

    def commit(self):
        _get_thread_conn().commit()


def get_db() -> "_DB":
    return _DB()

def init_db():
    # Enable WAL mode at startup (persists in DB file, applies to all future connections)
    _startup_conn = sqlite3.connect(DB_PATH, timeout=30.0)
    _startup_conn.execute("PRAGMA journal_mode=WAL")
    _startup_conn.execute("PRAGMA synchronous=NORMAL")
    _startup_conn.commit()
    _startup_conn.close()

    with get_db() as c:
        c.execute("""CREATE TABLE IF NOT EXISTS users (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            vault_id      TEXT    UNIQUE NOT NULL,
            telegram_id   INTEGER UNIQUE NOT NULL,
            password_hash BLOB    NOT NULL,
            pw_salt       BLOB    NOT NULL,
            tg_name       TEXT    DEFAULT '',
            tg_username   TEXT    DEFAULT '',
            timezone      TEXT    DEFAULT 'UTC',
            kdf_type      TEXT    DEFAULT 'pbkdf2',
            mk_enc        BLOB,
            mk_salt       BLOB,
            mk_iv         BLOB,
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
            note       TEXT DEFAULT '',
            account_type TEXT DEFAULT 'totp',
            hotp_counter INTEGER DEFAULT 0,
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
        c.execute("""CREATE TABLE IF NOT EXISTS share_links (
            token       TEXT    PRIMARY KEY,
            vault_id    TEXT    NOT NULL,
            totp_ids    TEXT    NOT NULL,
            secrets_enc TEXT    NOT NULL,
            names       TEXT    NOT NULL,
            expires_at  INTEGER NOT NULL,
            created_at  INTEGER DEFAULT (strftime('%s','now')))""")

        # New: track failed login attempts per vault to prevent brute-force
        c.execute("""CREATE TABLE IF NOT EXISTS login_attempts (
            vault_id     TEXT    PRIMARY KEY,
            attempts     INTEGER DEFAULT 0,
            frozen_until INTEGER DEFAULT 0)""")

        # New: backup reminder preferences per user
        c.execute("""CREATE TABLE IF NOT EXISTS backup_reminders (
            telegram_id INTEGER PRIMARY KEY,
            frequency   TEXT    DEFAULT 'weekly',
            last_sent   INTEGER DEFAULT 0,
            enabled     INTEGER DEFAULT 1)""")

        # New: bot-wide settings (maintenance mode, signup/login toggles)
        c.execute("""CREATE TABLE IF NOT EXISTS bot_settings (
            key   TEXT PRIMARY KEY,
            value TEXT NOT NULL)""")

        # New: offline auto-backup preferences per user
        c.execute("""CREATE TABLE IF NOT EXISTS auto_backup_settings (
            telegram_id  INTEGER PRIMARY KEY,
            enabled      INTEGER DEFAULT 0,
            frequency    TEXT    DEFAULT 'weekly',
            last_weekly  INTEGER DEFAULT 0,
            last_monthly INTEGER DEFAULT 0,
            pw_enc       BLOB,
            pw_salt      BLOB,
            pw_iv        BLOB)""")

        # New: daily login counter per telegram_id
        c.execute("""CREATE TABLE IF NOT EXISTS daily_login_counts (
            telegram_id  INTEGER PRIMARY KEY,
            count        INTEGER DEFAULT 0,
            day_bucket   TEXT    DEFAULT '')""")

        # New: weekly signup counter per telegram_id
        c.execute("""CREATE TABLE IF NOT EXISTS weekly_signup_counts (
            telegram_id  INTEGER PRIMARY KEY,
            count        INTEGER DEFAULT 0,
            week_bucket  TEXT    DEFAULT '')""")

        # New: lifetime distinct vault logins per telegram_id
        c.execute("""CREATE TABLE IF NOT EXISTS vault_login_history (
            telegram_id  INTEGER NOT NULL,
            vault_id     TEXT    NOT NULL,
            PRIMARY KEY  (telegram_id, vault_id))""")

        # New: TOTP add rate limiting per vault (1-minute window)
        c.execute("""CREATE TABLE IF NOT EXISTS totp_add_rate (
            vault_id     TEXT    PRIMARY KEY,
            count        INTEGER DEFAULT 0,
            window_start INTEGER DEFAULT 0)""")

        # Per-vault custom limits (overrides global MAX_TOTP_PER_VAULT / MAX_TOTP_PER_MINUTE)
        c.execute("""CREATE TABLE IF NOT EXISTS vault_custom_limits (
            vault_id      TEXT    PRIMARY KEY,
            max_per_vault INTEGER DEFAULT NULL,
            max_per_min   INTEGER DEFAULT NULL)""")

        # Per-user specific signup disable (blocks signup for specific Telegram IDs
        # regardless of global public signup toggle)
        c.execute("""CREATE TABLE IF NOT EXISTS user_signup_disabled (
            telegram_id   INTEGER PRIMARY KEY,
            disabled_at   INTEGER DEFAULT (strftime('%s','now')))""")

        # Per-user specific login disable (blocks login for specific Telegram IDs
        # regardless of global public login toggle)
        c.execute("""CREATE TABLE IF NOT EXISTS user_login_disabled (
            telegram_id   INTEGER PRIMARY KEY,
            disabled_at   INTEGER DEFAULT (strftime('%s','now')))""")

        # OTP request rate-limiting log (tracks reset OTP requests)
        c.execute("""CREATE TABLE IF NOT EXISTS otp_request_log (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            vault_id     TEXT    NOT NULL,
            requested_at INTEGER DEFAULT (strftime('%s','now')))""")
        try:
            c.execute("CREATE INDEX IF NOT EXISTS idx_otp_req ON otp_request_log (vault_id, requested_at)")
        except Exception:
            pass

        # CAPTCHA failure tracking for signup
        c.execute("""CREATE TABLE IF NOT EXISTS captcha_attempts (
            telegram_id  INTEGER PRIMARY KEY,
            fail_count   INTEGER DEFAULT 0,
            banned_until INTEGER DEFAULT 0)""")

        # Telegram-level ban (blocks all bot interaction except broadcast)
        c.execute("""CREATE TABLE IF NOT EXISTS telegram_banned (
            telegram_id   INTEGER PRIMARY KEY,
            tg_username   TEXT    DEFAULT '',
            banned_at     INTEGER DEFAULT (strftime('%s','now')))""")

        # Statistics event log - records all key events with BDT-aligned timestamps
        c.execute("""CREATE TABLE IF NOT EXISTS stats_events (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            event_type  TEXT    NOT NULL,
            telegram_id INTEGER DEFAULT 0,
            vault_id    TEXT    DEFAULT '',
            ts          INTEGER DEFAULT (strftime('%s','now')))""")
        try:
            c.execute("CREATE INDEX IF NOT EXISTS idx_stats_ts ON stats_events (ts)")
            c.execute("CREATE INDEX IF NOT EXISTS idx_stats_type ON stats_events (event_type, ts)")
        except Exception:
            pass

        # Per-vault custom export/import limits (overrides public limit)
        c.execute("""CREATE TABLE IF NOT EXISTS vault_ei_limits (
            vault_id        TEXT    PRIMARY KEY,
            export_limit    INTEGER DEFAULT NULL,
            import_limit    INTEGER DEFAULT NULL)""")

        # Daily export/import usage tracking per vault
        c.execute("""CREATE TABLE IF NOT EXISTS vault_ei_usage (
            vault_id        TEXT    NOT NULL,
            action          TEXT    NOT NULL,
            day             TEXT    NOT NULL,
            count           INTEGER DEFAULT 0,
            PRIMARY KEY (vault_id, action, day))""")

        # Migrations
        for col, defval in [("tg_name", "''"), ("timezone", "'UTC'"), ("tg_username", "''")]:
            try:
                c.execute(f"ALTER TABLE users ADD COLUMN {col} TEXT DEFAULT {defval}")
            except Exception:
                pass

        # Argon2id + Master Key migration columns
        for col, coltype, defval in [
            ("kdf_type", "TEXT",    "'pbkdf2'"),
            ("mk_enc",   "BLOB",    "NULL"),
            ("mk_salt",  "BLOB",    "NULL"),
            ("mk_iv",    "BLOB",    "NULL"),
        ]:
            try:
                stmt = f"ALTER TABLE users ADD COLUMN {col} {coltype}"
                if defval != "NULL":
                    stmt += f" DEFAULT {defval}"
                c.execute(stmt)
            except Exception:
                pass

        # Migrate auto_backup_settings: add encrypted password columns
        for col, coltype in [("pw_enc", "BLOB"), ("pw_salt", "BLOB"), ("pw_iv", "BLOB")]:
            try:
                c.execute(f"ALTER TABLE auto_backup_settings ADD COLUMN {col} {coltype}")
            except Exception:
                pass

        # Migrate users: add sk_verifier for secure key verification without password
        try:
            c.execute("ALTER TABLE users ADD COLUMN sk_verifier TEXT DEFAULT ''")
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

        # Migrate new columns to totp_accounts
        for col, coltype, default in [
            ("note",         "TEXT",    "''"),
            ("account_type", "TEXT",    "'totp'"),
            ("hotp_counter", "INTEGER", "0"),
        ]:
            try:
                c.execute(f"ALTER TABLE totp_accounts ADD COLUMN {col} {coltype} DEFAULT {default}")
            except Exception:
                pass

        # Migrate users table: account_disabled, last_seen, total_disabled_count
        for col, coltype, default in [
            ("account_disabled", "INTEGER", "0"),
            ("total_disabled_count", "INTEGER", "0"),
            ("last_seen",        "INTEGER", "0"),
        ]:
            try:
                c.execute(f"ALTER TABLE users ADD COLUMN {col} {coltype} DEFAULT {default}")
            except Exception:
                pass

        c.commit()

        # Load bot_settings into memory
        _load_bot_settings(c)


# ── Bot Settings (maintenance, signup/login toggles) ───────
def _load_bot_settings(conn=None):
    """Load persisted settings from DB into in-memory dict."""
    try:
        if conn:
            rows = conn.execute("SELECT key, value FROM bot_settings").fetchall()
        else:
            with get_db() as c2:
                rows = c2.execute("SELECT key, value FROM bot_settings").fetchall()
        for row in rows:
            if row["key"] in _bot_settings:
                val = row["value"]
                if val in ("true", "false"):
                    _bot_settings[row["key"]] = val == "true"
                elif val == "null" or val == "None":
                    _bot_settings[row["key"]] = None
                elif val.lstrip("-").isdigit():
                    _bot_settings[row["key"]] = int(val)
                else:
                    _bot_settings[row["key"]] = val
    except Exception:
        pass

def _save_setting(key: str, value):
    _bot_settings[key] = value
    str_val = "true" if value is True else ("false" if value is False else str(value))
    with get_db() as c:
        c.execute("INSERT OR REPLACE INTO bot_settings (key, value) VALUES (?,?)", (key, str_val))
        c.commit()

def is_maintenance() -> bool:
    return bool(_bot_settings.get("maintenance", False))

def is_signup_enabled() -> bool:
    return bool(_bot_settings.get("signup_enabled", True))

def is_login_enabled() -> bool:
    return bool(_bot_settings.get("login_enabled", True))

def is_admin_group(chat_id: int) -> bool:
    return ADMIN_GROUP_ID != 0 and chat_id == ADMIN_GROUP_ID

MAINTENANCE_MSG = (
    "\U0001f527 *BV Authenticator is currently under maintenance\\.* \\n\\n"
    "We\'re working to improve your experience \u2014 please check back shortly\\.\\n\\n"
    "Thank you for your patience\\."
)

def update_last_seen(telegram_id: int):
    with get_db() as c:
        c.execute(
            "UPDATE users SET last_seen=? WHERE telegram_id=?",
            (int(time.time()), telegram_id)
        )
        c.commit()

def fmt_bd_time(ts: int) -> str:
    """Format timestamp in Bangladesh time (UTC+6)."""
    try:
        import zoneinfo
        dt = datetime.datetime.fromtimestamp(ts, tz=zoneinfo.ZoneInfo(BD_TZ))
    except Exception:
        dt = datetime.datetime.utcfromtimestamp(ts) + datetime.timedelta(hours=6)
    return dt.strftime("%Y/%m/%d-%H:%M:%S")

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

# ── Argon2id parameters (OWASP recommended) ────────────────
ARGON2_TIME_COST   = 3
ARGON2_MEMORY_COST = 65536   # 64 MB
ARGON2_PARALLELISM = 1
ARGON2_HASH_LEN    = 32

def _argon2id_hash(password: str, salt: bytes) -> bytes:
    """Derive a 32-byte key/hash using Argon2id."""
    return hash_secret_raw(
        secret=password.encode(),
        salt=salt,
        time_cost=ARGON2_TIME_COST,
        memory_cost=ARGON2_MEMORY_COST,
        parallelism=ARGON2_PARALLELISM,
        hash_len=ARGON2_HASH_LEN,
        type=Argon2Type.ID,
    )

def hash_pw(password: str, salt: bytes, kdf: str = "argon2id") -> bytes:
    """Hash password for authentication check.
    kdf='argon2id' for new users, 'pbkdf2' for legacy compatibility."""
    if kdf == "argon2id":
        return _argon2id_hash(password, salt)
    return PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=PBKDF2_ITER).derive(password.encode())

def _pw_wrap_key(password: str, salt: bytes) -> bytes:
    """Derive a 32-byte AES key from password to wrap/unwrap the master key.
    Always uses Argon2id — the master key wrapping is always modern KDF."""
    return _argon2id_hash(password, salt)

def _pw_wrap_key_legacy(password: str, vault_id: str, salt: bytes) -> bytes:
    """Legacy PBKDF2 key derivation for existing users without master key."""
    return PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=PBKDF2_ITER).derive(
        (password + vault_id).encode() + SERVER_KEY
    )

# ── Master Key helpers ──────────────────────────────────────
def gen_master_key() -> bytes:
    """Generate a fresh 32-byte random master key for a new vault."""
    return os.urandom(32)

def wrap_master_key(master_key: bytes, password: str) -> tuple:
    """Encrypt master_key with password → (mk_enc, mk_salt, mk_iv)."""
    salt = os.urandom(16)
    iv   = os.urandom(12)
    wrap_key = _pw_wrap_key(password, salt)
    ct   = AESGCM(wrap_key).encrypt(iv, master_key, None)
    return ct, salt, iv

def unwrap_master_key(mk_enc: bytes, mk_salt: bytes, mk_iv: bytes, password: str) -> bytes:
    """Decrypt master_key using password."""
    wrap_key = _pw_wrap_key(password, bytes(mk_salt))
    return AESGCM(wrap_key).decrypt(bytes(mk_iv), bytes(mk_enc), None)

def load_master_key(vault_id: str, password: str) -> bytes | None:
    """Load and unwrap the master key for a vault. Returns None if not migrated yet."""
    with get_db() as c:
        row = c.execute(
            "SELECT mk_enc, mk_salt, mk_iv FROM users WHERE vault_id=?", (vault_id,)
        ).fetchone()
    if not row or not row["mk_enc"]:
        return None
    try:
        return unwrap_master_key(row["mk_enc"], row["mk_salt"], row["mk_iv"], password)
    except Exception:
        return None

# ── Symmetric encryption (uses master_key) ─────────────────
def enc_key(password: str, vault_id: str, salt: bytes) -> bytes:
    """Legacy PBKDF2 key derivation — only used for old accounts without master key."""
    return _pw_wrap_key_legacy(password, vault_id, salt)

def encrypt(secret: str, password_or_mk: str | bytes, vault_id: str):
    """Encrypt a secret.
    If password_or_mk is bytes → it's a master_key (new path).
    If str → it's a password (legacy path)."""
    salt = os.urandom(16)
    iv   = os.urandom(12)
    if isinstance(password_or_mk, bytes):
        # New path: master key directly as AES key (no KDF needed)
        key = password_or_mk
    else:
        # Legacy path: derive key from password
        key = enc_key(password_or_mk, vault_id, salt)
    ct = AESGCM(key).encrypt(iv, secret.encode(), None)
    return ct, salt, iv

def decrypt(ct, salt, iv, password_or_mk: str | bytes, vault_id: str) -> str:
    """Decrypt a secret.
    If password_or_mk is bytes → master_key (new path).
    If str → password (legacy path)."""
    if isinstance(password_or_mk, bytes):
        key = password_or_mk
    else:
        key = enc_key(password_or_mk, vault_id, bytes(salt))
    return AESGCM(key).decrypt(bytes(iv), bytes(ct), None).decode()

def _get_vault_key(vault_id: str, password: str) -> bytes | str:
    """Return master_key (bytes) if available, else password (str) for legacy path."""
    mk = load_master_key(vault_id, password)
    return mk if mk is not None else password

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


# ── Share Link crypto ───────────────────────────────────────
def share_link_aes_key(token: str) -> bytes:
    """Derive unique 32-byte AES key from SERVER_KEY + token (per-link)."""
    material = f"share:{token}".encode() + SERVER_KEY
    salt     = hashlib.sha256(material).digest()[:16]
    return PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=100_000).derive(material)

def share_encrypt_secret(secret: str, token: str) -> dict:
    """Encrypt a TOTP plaintext secret for storage in share_links."""
    key = share_link_aes_key(token)
    iv  = os.urandom(12)
    ct  = AESGCM(key).encrypt(iv, secret.encode(), None)
    return {"ct": ct.hex(), "iv": iv.hex()}

def share_decrypt_secret(enc: dict, token: str) -> str:
    """Decrypt a TOTP secret from share_links storage."""
    key = share_link_aes_key(token)
    ct  = bytes.fromhex(enc["ct"])
    iv  = bytes.fromhex(enc["iv"])
    return AESGCM(key).decrypt(iv, ct, None).decode()

def gen_share_token() -> str:
    """Generate a cryptographically random URL-safe 43-char token."""
    return base64.urlsafe_b64encode(secrets.token_bytes(32)).rstrip(b"=").decode()

def purge_expired_share_links():
    """Remove expired share links. Called on bot startup."""
    with get_db() as c:
        c.execute("DELETE FROM share_links WHERE expires_at <= ?", (int(time.time()),))
        c.commit()

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
    """Store secure key encrypted with master_key (or password for legacy)."""
    vault_key = _get_vault_key(vault_id, password)
    ct, salt, iv = encrypt(secure_key_hex, vault_key, vault_id)
    with get_db() as c:
        c.execute(
            "UPDATE users SET sk_enc=?, sk_salt=?, sk_iv=? WHERE vault_id=?",
            (ct, salt, iv, vault_id),
        )
        c.commit()

def load_user_secure_key(vault_id: str, password: str) -> str | None:
    """Load and decrypt the secure key using master_key or password (legacy)."""
    with get_db() as c:
        row = c.execute(
            "SELECT sk_enc, sk_salt, sk_iv FROM users WHERE vault_id=?", (vault_id,)
        ).fetchone()
    if not row or not row["sk_enc"]:
        return None
    vault_key = _get_vault_key(vault_id, password)
    try:
        return decrypt(row["sk_enc"], row["sk_salt"], row["sk_iv"], vault_key, vault_id)
    except Exception:
        return None

def verify_secure_key_by_totp(vault_id: str, candidate_hex: str) -> bool:
    """Verify the Secure Key against users table sk_enc OR totp_accounts sk_enc.
    Falls back gracefully when the user has no TOTP entries."""
    candidate = candidate_hex.strip()
    # Primary: try to decrypt any TOTP entry's sk_enc with the candidate
    with get_db() as c:
        totp_rows = c.execute(
            "SELECT sk_enc, sk_salt, sk_iv FROM totp_accounts "
            "WHERE vault_id=? AND sk_enc IS NOT NULL LIMIT 3",
            (vault_id,)
        ).fetchall()
    for row in totp_rows:
        try:
            sk_decrypt_totp(row["sk_enc"], row["sk_salt"], row["sk_iv"], candidate, vault_id)
            return True   # Successfully decrypted = correct key
        except Exception:
            continue
    if totp_rows:
        return False  # Had TOTP entries but none decrypted = wrong key
    # No TOTP entries at all — verify using users.sk_enc HMAC verifier
    with get_db() as c:
        row = c.execute(
            "SELECT sk_verifier FROM users WHERE vault_id=?", (vault_id,)
        ).fetchone()
    if row and row["sk_verifier"]:
        expected = hmac.new(SERVER_KEY, candidate.encode(), hashlib.sha256).hexdigest()
        return hmac.compare_digest(row["sk_verifier"], expected)
    # No verifier stored (old account) and no TOTP entries.
    # Reject: cannot verify the key, so we cannot safely accept any input.
    # The user should skip secure key and lose TOTP data (there are none anyway).
    return False

# ── TOTP ───────────────────────────────────────────────────
def clean_secret(s: str) -> str:
    return re.sub(r"[\s\-\\.\,\_]", "", s).upper()

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
    code = str((struct.unpack(">I", h[off:off+4])[0] & 0x7FFFFFFF) % 1_000_000).zfill(6)
    return code, remain



def generate_code(secret: str):
    """
    Generate current and next TOTP code.
    Returns (code_str, remaining_seconds, next_code_str).
    """
    code, remain = totp_now(secret)
    # Next code (next 30s window)
    c   = clean_secret(secret)
    k   = base64.b32decode(c + "=" * ((8 - len(c) % 8) % 8))
    ts  = int(time.time())
    counter_next = ts // 30 + 1
    h   = hmac.new(k, struct.pack(">Q", counter_next), hashlib.sha1).digest()
    off = h[-1] & 0xF
    next_code = str((struct.unpack(">I", h[off:off+4])[0] & 0x7FFFFFFF) % 1_000_000).zfill(6)
    return code, remain, next_code

def parse_otpauth(uri: str):
    try:
        p      = urlparse(uri)
        if p.scheme != "otpauth":
            return None
        otp_type = p.netloc.lower()  # "totp" or "hotp"
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
        # Only TOTP is supported
        if otp_type != "totp":
            return None
        # Enforce name length limit (QR names auto-truncated silently)
        name = name[:TOTP_NAME_MAX_LEN]
        return {"name": name, "issuer": issuer, "secret": c,
                "account_type": "totp", "hotp_counter": 0}
    except Exception:
        return None

# ── OTP (cryptographic, unpredictable) ────────────────────
def gen_otp() -> str:
    raw    = secrets.token_bytes(32)
    digest = hashlib.sha3_256(raw + SERVER_KEY + str(time.time_ns()).encode()).hexdigest()
    b62    = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
    num    = int(digest, 16)
    chars  = []
    for _ in range(10):
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
    """Record failed reset attempt. Returns True if temporarily disabled.
    On threshold: sets frozen_until AND account_disabled=1.
    """
    now = int(time.time())
    with get_db() as c:
        row = c.execute("SELECT attempts, frozen_until FROM reset_attempts WHERE vault_id=?", (vault_id,)).fetchone()
        if row and row["frozen_until"] > now:
            return True
        attempts     = (row["attempts"] if row else 0) + 1
        frozen_until = now + FREEZE_HOURS * 3600 if attempts >= MAX_RESET_ATTEMPTS else 0
        c.execute("INSERT OR REPLACE INTO reset_attempts (vault_id, attempts, frozen_until) VALUES (?,?,?)",
                  (vault_id, attempts, frozen_until))
        if frozen_until > now:
            c.execute(
                "UPDATE users SET account_disabled=1, "
                "total_disabled_count=COALESCE(total_disabled_count,0)+1 "
                "WHERE vault_id=?", (vault_id,)
            )
        c.commit()
        return frozen_until > now

def reset_attempts_clear(vault_id: str):
    """Clear reset attempts after successful reset. Also re-enables account if no login freeze."""
    with get_db() as c:
        c.execute("DELETE FROM reset_attempts WHERE vault_id=?", (vault_id,))
        # Re-enable account if login freeze is also gone
        row_l = c.execute(
            "SELECT frozen_until FROM login_attempts WHERE vault_id=?", (vault_id,)
        ).fetchone()
        login_still_frozen = bool(row_l and row_l["frozen_until"] > int(time.time()))
        if not login_still_frozen:
            c.execute(
                "UPDATE users SET account_disabled=0 WHERE vault_id=? "
                "AND account_disabled=1", (vault_id,)
            )
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
    """Parse user timezone input like +6, -5:30, +5:45 into a valid IANA tz string.
    Uses fixed-offset IANA names: Etc/GMT signs are INVERTED (POSIX convention),
    so we use a direct UTC±HH:MM approach via zoneinfo fixed offsets instead."""
    m = re.match(r"^([+-])(\d{1,2})(?::(\d{2}))?$", raw.strip())
    if not m:
        return None
    sign, h, mn = m.group(1), int(m.group(2)), int(m.group(3) or 0)
    if h > 14 or mn not in (0, 30, 45):
        return None
    # Use Etc/GMT only for whole-hour offsets (Etc/GMT inverts sign: +6 -> Etc/GMT-6 = UTC+6)
    # For half-hour and quarter-hour offsets, use well-known IANA zone names where possible.
    tz_map = {
        (+5, 30): "Asia/Kolkata",
        (+5, 45): "Asia/Kathmandu",
        (+6, 0):  "Asia/Dhaka",
        (+6, 30): "Asia/Rangoon",
        (+9, 30): "Australia/Darwin",
        (+10, 30): "Australia/Adelaide",
        (+12, 45): "Pacific/Chatham",
    }
    offset_h = h if sign == "+" else -h
    named = tz_map.get((offset_h, mn))
    if named:
        return named
    if mn == 0:
        # Etc/GMT uses INVERTED sign: Etc/GMT-6 = UTC+6
        etc_sign = "-" if sign == "+" else "+"
        return f"Etc/GMT{etc_sign}{h}"
    # For other fractional offsets, use a fixed-offset string zoneinfo can parse
    return f"UTC{sign}{h:02d}:{mn:02d}"

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
        [InlineKeyboardButton("☕ Buy me a coffee", callback_data="donate")],
    ])

def kb_settings():
    """Main settings menu — 3 sections + Main Menu."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔐 Security & Access",  callback_data="settings_security")],
        [InlineKeyboardButton("💾 Backup & Restore",   callback_data="settings_backup")],
        [InlineKeyboardButton("☕ Buy me a Coffee",     callback_data="donate")],
        [InlineKeyboardButton("⚙️ Account",            callback_data="settings_account")],
        [InlineKeyboardButton("🏠 Main Menu",          callback_data="main_menu")],
    ])

def kb_settings_security():
    """Security & Access sub-menu."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔑 Change Password",  callback_data="change_pw")],
        [InlineKeyboardButton("🔓 Reset Password",   callback_data="settings_reset_pw")],
        [InlineKeyboardButton("🛡 View Secure Key",  callback_data="view_secure_key")],
        [InlineKeyboardButton("⬅️ Back",             callback_data="settings")],
        [InlineKeyboardButton("🏠 Home",              callback_data="main_menu")],
    ])

def kb_settings_backup():
    """Backup & Restore sub-menu."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📤 Export Vault",       callback_data="export_vault")],
        [InlineKeyboardButton("📥 Import Vault",       callback_data="import_vault")],
        [InlineKeyboardButton("💾 Offline Auto Backup", callback_data="offline_auto_backup")],
        [InlineKeyboardButton("🔔 Backup Reminder",    callback_data="backup_reminder")],
        [InlineKeyboardButton("⬅️ Back",              callback_data="settings")],
        [InlineKeyboardButton("🏠 Home",               callback_data="main_menu")],
    ])

def kb_settings_account():
    """Account sub-menu."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🚪 Logout",         callback_data="logout")],
        [InlineKeyboardButton("🗑 Delete Account", callback_data="delete_account")],
        [InlineKeyboardButton("⬅️ Back",          callback_data="settings")],
        [InlineKeyboardButton("🏠 Home",           callback_data="main_menu")],
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


def build_share_selection_kb(
    rows: list, selected: set, page: int = 0, total_pages: int = 1,
    all_rows: list = None
) -> InlineKeyboardMarkup:
    """Paginated checkbox keyboard for Share Codes (5 items per page).
    Max SHARE_MAX_TOTP (5) can be selected at once.
    """
    buttons = []
    n_selected = len(selected)
    for row in rows:
        tid   = row["id"]
        check = "✅ " if tid in selected else "☐ "
        buttons.append([InlineKeyboardButton(
            f"{check}{row['name']}",
            callback_data=f"share_toggle_{tid}",
        )])
    # Navigation row
    if total_pages > 1:
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("⬅️", callback_data=f"share_pg_{page-1}"))
        nav.append(InlineKeyboardButton(f"{page+1}/{total_pages}", callback_data="list_noop"))
        if page < total_pages - 1:
            nav.append(InlineKeyboardButton("➡️", callback_data=f"share_pg_{page+1}"))
        buttons.append(nav)
    # Select All / Unselect All row (only show Unselect All if something selected)
    if n_selected > 0:
        buttons.append([InlineKeyboardButton("☐ Unselect All", callback_data="share_unselect_all")])
    else:
        buttons.append([InlineKeyboardButton("✅ Select All", callback_data="share_select_all")])
    # Action row
    action_row = []
    if 0 < n_selected <= SHARE_MAX_TOTP:
        action_row.append(InlineKeyboardButton(
            f"🔗 Share Selected ({n_selected}/{SHARE_MAX_TOTP})",
            callback_data="share_generate",
        ))
    elif n_selected > SHARE_MAX_TOTP:
        # Show limit warning instead of share button
        action_row.append(InlineKeyboardButton(
            f"⚠️ Max {SHARE_MAX_TOTP} allowed ({n_selected} selected)",
            callback_data="share_limit_warn",
        ))
    action_row.append(InlineKeyboardButton("⬅️ Back", callback_data="main_menu"))
    buttons.append(action_row)
    return InlineKeyboardMarkup(buttons)

def build_totp_list_kb() -> InlineKeyboardMarkup:
    """Bottom keyboard for the TOTP list view."""
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🔄 Refresh",     callback_data="list_totp"),
            InlineKeyboardButton("📁 Share Codes", callback_data="share_codes_open"),
        ],
        [InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")],
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
    name     = ((tg_user.first_name or "") + " " + (tg_user.last_name or "")).strip()
    username = tg_user.username or ""
    with get_db() as c:
        c.execute(
            "UPDATE users SET tg_name=?, tg_username=? WHERE vault_id=?",
            (name or u["tg_name"], username, vault_id),
        )
        c.commit()

# ── /start ──────────────────────────────────────────────────
async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not update.message:
        return
    uid  = update.effective_user.id
    # Ban check: silently ignore all banned users (no response)
    if is_telegram_banned(uid):
        try:
            await update.message.delete()
        except Exception:
            pass
        return AUTH_MENU
    # Auto-delete the /start command message
    asyncio.create_task(auto_delete_msg(update.message, delay=3))
    # Update last_seen for any active user
    update_last_seen(uid)
    # Handle deep link: /start <share_token>
    if ctx.args:
        token = ctx.args[0].strip()
        await handle_share_view(update, token)
        vault = get_session(uid)
        if vault:
            return TOTP_MENU
        return AUTH_MENU
    # Maintenance mode: block all users
    if is_maintenance():
        await update.message.reply_text(
            MAINTENANCE_MSG, parse_mode="MarkdownV2"
        )
        return AUTH_MENU
    vault = get_session(uid)
    if vault:
        u = get_user(vault)
        if u:
            # Check if account is disabled
            if u["account_disabled"]:
                await update.message.reply_text(
                    "🚫 *Your account has been disabled\\.* Please contact support\\.",
                    parse_mode="MarkdownV2",
                )
                return AUTH_MENU
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
    """Show Terms & Privacy screen before proceeding to account creation."""
    q   = update.callback_query
    await q.answer()
    if is_maintenance():
        await q.edit_message_text(MAINTENANCE_MSG, parse_mode="MarkdownV2")
        return AUTH_MENU
    if not is_signup_enabled():
        await q.edit_message_text(
            "⚠️ *Sign Up is currently disabled\\.* Please try again later\\.",
            parse_mode="MarkdownV2", reply_markup=kb_auth()
        )
        return AUTH_MENU
    uid = update.effective_user.id
    # Per-user specific signup block (overrides global toggle)
    if is_user_signup_disabled(uid):
        await q.edit_message_text(
            "⚠️ *Sign Up is not available for your account\\.* Please contact support.",
            parse_mode="MarkdownV2", reply_markup=kb_auth()
        )
        return AUTH_MENU
    if get_user_by_tid(uid):
        await q.edit_message_text(
            "⚠️ *This Telegram account already has a vault\\.* Use *Login*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU
    # Weekly signup limit: max 2 signups per Telegram account per week
    if not check_weekly_signup_limit(uid):
        await q.edit_message_text(
            "⚠️ *Weekly sign\\-up limit reached\\.* You can create a maximum of "
            f"*{MAX_WEEKLY_SIGNUPS}* accounts per week from one Telegram account\\.\n\n"
            "Please try again next week\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU
    # Show Terms & Privacy screen
    await q.edit_message_text(
        "📋 *Terms \\& Privacy*\n\n"
        "By creating an account you agree to our terms of service and privacy policy\\.\n\n"
        "• Your TOTP secrets are encrypted with *AES\\-256\\-GCM* using your password\\.\n"
        "• We never store your plaintext secrets or passwords\\.\n"
        "• Your data is linked to your Telegram account\\.\n"
        "• You are responsible for keeping your Vault ID and Secure Key safe\\.\n"
        "• We reserve the right to disable accounts that violate our terms\\.\n\n"
        "[📖 Read Full Privacy Policy](https://antonysrm\\.com/totp/privacy)",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [
                InlineKeyboardButton("✅ I Agree",  callback_data="signup_agree"),
                InlineKeyboardButton("❌ Decline",  callback_data="signup_decline"),
            ],
        ]),
    )
    return SIGNUP_TERMS

async def signup_terms_agreed(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """User agreed to terms — show CAPTCHA before proceeding to signup."""
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id

    # Check CAPTCHA ban
    ban_remaining = check_captcha_ban(uid)
    if ban_remaining > 0:
        h = ban_remaining // 3600
        m = (ban_remaining % 3600) // 60
        await q.edit_message_text(
            f"⛔ *Too many failed verifications\\.*\n\n"
            f"You can try signing up again in *{h}h {m}m*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU

    # Generate CAPTCHA
    cap = make_captcha()
    ctx.user_data["captcha_answer"] = cap["answer"]
    choices = cap["choices"]
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(str(c), callback_data=f"captcha_{c}") for c in choices],
        [InlineKeyboardButton("⬅️ Back", callback_data="signup_back_to_terms")],
    ])
    # Delete the terms message first
    try:
        await q.message.delete()
    except Exception:
        pass
    await q.message.reply_photo(
        photo=cap["image_bytes"],
        caption="🔢 *Verify you are human*\n\nSolve the math question above and tap the correct answer\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb,
    )
    return CAPTCHA_VERIFY


async def captcha_check(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle CAPTCHA button click."""
    q = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    try:
        chosen = int(q.data.split("_")[1])
    except (IndexError, ValueError):
        return CAPTCHA_VERIFY
    correct = ctx.user_data.get("captcha_answer")
    if chosen == correct:
        # CAPTCHA passed — clear fails and proceed to signup
        reset_captcha_fails(uid)
        ctx.user_data.pop("captcha_answer", None)
        vid = gen_vault_id(uid)
        ctx.user_data["signup_vid"] = vid
        try:
            await q.message.delete()
        except Exception:
            pass
        await q.message.reply_text(
            "✅ *Verified\\!*\n\n"
            "🆕 *Create Your Account*\n\n"
            "Your *BV Vault ID* \\(auto\\-generated\\):\n\n"
            f"`{em(vid)}`\n\n"
            "📌 *Save this ID\\!* You need it to login from other devices\\.\n\n"
            "Set a *password* \\(minimum 6 characters\\):",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return SIGNUP_PASSWORD
    else:
        # Wrong answer — record fail and regenerate or ban
        banned = record_captcha_fail(uid)
        if banned:
            try:
                await q.message.delete()
            except Exception:
                pass
            await q.message.reply_text(
                f"⛔ *Too many failed verifications\\.*\n\n"
                f"You cannot sign up for *{CAPTCHA_BAN_HOURS} hours*\\.",
                parse_mode="MarkdownV2",
                reply_markup=kb_auth(),
            )
            return AUTH_MENU
        # Generate new CAPTCHA
        cap = make_captcha()
        ctx.user_data["captcha_answer"] = cap["answer"]
        choices = cap["choices"]
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton(str(c), callback_data=f"captcha_{c}") for c in choices],
            [InlineKeyboardButton("⬅️ Back", callback_data="signup_back_to_terms")],
        ])
        try:
            await q.message.delete()
        except Exception:
            pass
        await q.message.reply_photo(
            photo=cap["image_bytes"],
            caption="❌ *Wrong answer\\. Try again\\!*\n\n🔢 Solve the math question above\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb,
        )
        return CAPTCHA_VERIFY

async def signup_terms_declined(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """User declined terms — go back to auth menu."""
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "❌ *Sign up cancelled\\.* You must agree to the terms to create an account\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_auth(),
    )
    return AUTH_MENU

async def signup_back_to_terms(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Back from captcha to terms screen during signup."""
    q = update.callback_query
    await q.answer()
    ctx.user_data.pop("captcha_answer", None)
    try:
        await q.message.delete()
    except Exception:
        pass
    await q.message.reply_text(
        "📜 *Terms of Service*\n\nPlease read our terms before signing up\\.",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ I Agree", callback_data="signup_agree")],
            [InlineKeyboardButton("❌ Decline", callback_data="signup_decline")],
        ]),
    )
    return SIGNUP_TERMS


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
    tg_name     = ((update.effective_user.first_name or "") + " " + (update.effective_user.last_name or "")).strip()
    tg_username = update.effective_user.username or ""

    # Generate master key for this vault (new architecture)
    master_key       = gen_master_key()
    mk_enc, mk_salt, mk_iv = wrap_master_key(master_key, pw)

    with get_db() as c:
        c.execute(
            "INSERT INTO users (vault_id,telegram_id,password_hash,pw_salt,tg_name,tg_username,"
            "kdf_type,mk_enc,mk_salt,mk_iv) VALUES (?,?,?,?,?,?,?,?,?,?)",
            (vid, uid, hash_pw(pw, salt, "argon2id"), salt, tg_name, tg_username,
             "argon2id", mk_enc, mk_salt, mk_iv),
        )
        c.commit()

    # Store secure key encrypted with master_key (not password)
    secure_key = gen_secure_key()
    store_user_secure_key(vid, secure_key, pw)
    # Store HMAC verifier so secure key can be verified without password
    sk_verifier = hmac.new(SERVER_KEY, secure_key.encode(), hashlib.sha256).hexdigest()
    with get_db() as c:
        c.execute("UPDATE users SET sk_verifier=? WHERE vault_id=?", (sk_verifier, vid))
        c.commit()

    set_session(uid, vid)
    ctx.user_data["password"] = pw
    ctx.user_data["vault_id"] = vid
    _session_pw_cache[vid] = pw             # RAM cache for auto-backup
    _oab_store_password(uid, vid, pw)       # DB encrypted store for auto-backup
    record_weekly_signup(uid)               # track weekly signup count
    record_stat("signup", telegram_id=uid, vault_id=vid)  # stats tracking
    bot_log("AUTH", "SIGNUP_OK", tg_id=uid, vault=vid, name=tg_name)
    record_vault_login(uid, vid)            # track lifetime vault access

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
    if is_maintenance():
        await q.edit_message_text(MAINTENANCE_MSG, parse_mode="MarkdownV2")
        return AUTH_MENU
    if not is_login_enabled():
        await q.edit_message_text(
            "⚠️ *Login is currently disabled\\.* Please try again later\\.",
            parse_mode="MarkdownV2", reply_markup=kb_auth()
        )
        return AUTH_MENU
    uid = update.effective_user.id
    if is_user_login_disabled(uid):
        await q.edit_message_text(
            "⚠️ *Login is not available for your account\\.* Please contact support\\.",
            parse_mode="MarkdownV2", reply_markup=kb_auth()
        )
        return AUTH_MENU
    # Show CAPTCHA before login choice (same system as signup)
    ban_remaining = check_captcha_ban(uid)
    if ban_remaining > 0:
        h = ban_remaining // 3600
        m = (ban_remaining % 3600) // 60
        await q.edit_message_text(
            f"⛔ *Too many failed verifications\\.*\n\n"
            f"You can try logging in again in *{h}h {m}m*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU
    cap = make_captcha()
    ctx.user_data["login_captcha_answer"] = cap["answer"]
    choices = cap["choices"]
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(str(c), callback_data=f"login_captcha_{c}") for c in choices],
        [InlineKeyboardButton("⬅️ Back", callback_data="cancel_to_menu")],
    ])
    try:
        await q.message.delete()
    except Exception:
        pass
    await q.message.reply_photo(
        photo=cap["image_bytes"],
        caption="🔢 *Verify you are human*\n\nSolve the math question above and tap the correct answer\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb,
    )
    return LOGIN_CAPTCHA

async def login_captcha_check(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle CAPTCHA button click during login flow."""
    q = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    try:
        chosen = int(q.data.split("_")[2])
    except (IndexError, ValueError):
        return LOGIN_CAPTCHA
    correct = ctx.user_data.get("login_captcha_answer")
    if chosen == correct:
        # CAPTCHA passed — clear fails and show login choice menu
        reset_captcha_fails(uid)
        ctx.user_data.pop("login_captcha_answer", None)
        try:
            await q.message.delete()
        except Exception:
            pass
        await q.message.reply_text(
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
    else:
        banned = record_captcha_fail(uid)
        if banned:
            try:
                await q.message.delete()
            except Exception:
                pass
            await q.message.reply_text(
                f"⛔ *Too many failed verifications\\.*\n\n"
                f"You cannot log in for *{CAPTCHA_BAN_HOURS} hours*\\.",
                parse_mode="MarkdownV2",
                reply_markup=kb_auth(),
            )
            return AUTH_MENU
        cap = make_captcha()
        ctx.user_data["login_captcha_answer"] = cap["answer"]
        choices = cap["choices"]
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton(str(c), callback_data=f"login_captcha_{c}") for c in choices],
            [InlineKeyboardButton("⬅️ Back", callback_data="cancel_to_menu")],
        ])
        try:
            await q.message.delete()
        except Exception:
            pass
        await q.message.reply_photo(
            photo=cap["image_bytes"],
            caption="❌ *Wrong answer\\. Try again\\!*\n\n🔢 Solve the math question above\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb,
        )
        return LOGIN_CAPTCHA


async def login_auto(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    vid = gen_vault_id(uid)
    u   = get_user(vid)
    if not u:
        await q.edit_message_text(
            "❌ No account found for this Telegram account\\. Please *Sign Up*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU
    # Block disabled AND temporarily frozen accounts
    if u["account_disabled"] or is_login_frozen(u["vault_id"]) or is_reset_frozen(u["vault_id"]):
        await q.edit_message_text(
            "🚫 *This account has been disabled\\.* Please contact support\\.",
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
    # Block disabled AND temporarily frozen accounts
    if u["account_disabled"] or is_login_frozen(u["vault_id"]) or is_reset_frozen(u["vault_id"]):
        await update.message.reply_text(
            "🚫 *This account has been disabled\\.* Please contact support\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU
    ctx.user_data["login_vid"] = u["vault_id"]
    await update.message.reply_text(
        "🔒 *Enter your password:*",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return LOGIN_PASSWORD

# ── Login Rate Limiting ────────────────────────────────────
def record_login_failure(vault_id: str) -> bool:
    """Record a failed login attempt. Returns True if account is now temporarily disabled.
    On threshold: sets frozen_until AND account_disabled=1 so it shows as Disabled everywhere.
    """
    now = int(time.time())
    with get_db() as c:
        row = c.execute(
            "SELECT attempts, frozen_until FROM login_attempts WHERE vault_id=?", (vault_id,)
        ).fetchone()
        if row and row["frozen_until"] > now:
            return True  # already disabled
        attempts     = (row["attempts"] if row else 0) + 1
        frozen_until = now + LOGIN_FREEZE_HOURS * 3600 if attempts >= MAX_LOGIN_ATTEMPTS else 0
        c.execute(
            "INSERT OR REPLACE INTO login_attempts (vault_id, attempts, frozen_until) VALUES (?,?,?)",
            (vault_id, attempts, frozen_until),
        )
        if frozen_until > now:
            # Mark account as disabled; increment total_disabled_count
            c.execute(
                "UPDATE users SET account_disabled=1, "
                "total_disabled_count=COALESCE(total_disabled_count,0)+1 "
                "WHERE vault_id=?", (vault_id,)
            )
        c.commit()
        return frozen_until > now

def clear_login_failures(vault_id: str):
    with get_db() as c:
        c.execute("DELETE FROM login_attempts WHERE vault_id=?", (vault_id,))
        # Re-enable account if it was disabled only by a login freeze (not manually)
        # We only clear if reset_attempts is also not frozen
        row_r = c.execute(
            "SELECT frozen_until FROM reset_attempts WHERE vault_id=?", (vault_id,)
        ).fetchone()
        reset_still_frozen = bool(row_r and row_r["frozen_until"] > int(time.time()))
        if not reset_still_frozen:
            c.execute(
                "UPDATE users SET account_disabled=0 WHERE vault_id=? "
                "AND account_disabled=1", (vault_id,)
            )
        c.commit()

def is_login_frozen(vault_id: str) -> bool:
    with get_db() as c:
        row = c.execute("SELECT frozen_until FROM login_attempts WHERE vault_id=?", (vault_id,)).fetchone()
        return bool(row and row["frozen_until"] > int(time.time()))

def get_login_freeze_remaining(vault_id: str) -> int:
    with get_db() as c:
        row = c.execute("SELECT frozen_until, attempts FROM login_attempts WHERE vault_id=?", (vault_id,)).fetchone()
        if row and row["frozen_until"] > int(time.time()):
            return row["frozen_until"] - int(time.time()), row["attempts"]
    return 0, 0

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

    # Final safety net: block disabled accounts even if they reached password step
    if u["account_disabled"]:
        await update.message.reply_text(
            "🚫 *This account has been disabled\\.* Please contact support\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU

    # Check if account is frozen due to too many failed login attempts
    if is_login_frozen(vid):
        remaining, _ = get_login_freeze_remaining(vid)
        h, m = remaining // 3600, (remaining % 3600) // 60
        await update.message.reply_text(
            f"🔒 *Account temporarily disabled\\.* Too many failed login attempts\\.\n\n"
            f"Try again in *{h}h {m}m*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU

    kdf_type = u["kdf_type"] or "pbkdf2"
    computed = await asyncio.to_thread(hash_pw, pw, bytes(u["pw_salt"]), kdf_type)
    if not hmac.compare_digest(computed, bytes(u["password_hash"])):
        # Record failed attempt and check freeze
        frozen = record_login_failure(vid)
        record_stat("login_fail", telegram_id=uid, vault_id=vid)
        if frozen:
            remaining, _ = get_login_freeze_remaining(vid)
            h, m = remaining // 3600, (remaining % 3600) // 60
            bot_log("AUTH", "LOGIN_FAIL", tg_id=uid, vault=vid, reason="account_frozen")
            bot_log("SECURITY", "LOGIN_FREEZE", tg_id=uid, vault=vid, failed_attempts=MAX_LOGIN_ATTEMPTS, frozen_hours=LOGIN_FREEZE_HOURS)
            await update.message.reply_text(
                f"🔒 *Account disabled for {h}h {m}m* due to {MAX_LOGIN_ATTEMPTS} failed attempts\\.\n\n"
                "Please wait or use *Forgot Password* to reset\\.",
                parse_mode="MarkdownV2",
                reply_markup=kb_auth(),
            )
        else:
            _, attempts = get_login_freeze_remaining(vid)
            # get attempts without freeze context
            with get_db() as c:
                row = c.execute("SELECT attempts FROM login_attempts WHERE vault_id=?", (vid,)).fetchone()
                attempts = row["attempts"] if row else 1
            left = max(0, MAX_LOGIN_ATTEMPTS - attempts)
            await update.message.reply_text(
                f"❌ Wrong password\\. *{left} attempt\\(s\\) remaining* before being disabled\\.\n\nTry again:",
                parse_mode="MarkdownV2",
                reply_markup=kb_cancel(),
            )
        return LOGIN_PASSWORD

    # Successful login: clear any failed attempt records
    clear_login_failures(vid)
    update_last_seen(uid)

    # Daily login limit: max 7 successful logins per day per telegram_id
    if not check_daily_login_limit(uid):
        await update.message.reply_text(
            f"⚠️ *Daily login limit reached\\.* Maximum *{MAX_DAILY_LOGINS}* logins per day allowed\\.\n\n"
            "Please try again tomorrow\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU

    # Lifetime vault limit: a telegram_id can access at most 5 distinct vaults ever
    if not check_vault_login_limit(uid, vid):
        await update.message.reply_text(
            f"⚠️ *Vault access limit reached\\.* A single Telegram account can access "
            f"at most *{MAX_LIFETIME_VAULTS}* different vaults lifetime\\.\n\n"
            "Contact support if you believe this is an error\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU

    # Record this login
    record_daily_login(uid)
    record_vault_login(uid, vid)
    record_stat("login_success", telegram_id=uid, vault_id=vid)
    record_stat("user_active",   telegram_id=uid, vault_id=vid)
    bot_log("AUTH", "LOGIN_OK", tg_id=uid, vault=vid, method="manual")

    # ── Auto-upgrade legacy users to Argon2id + Master Key ──────
    kdf_type = u["kdf_type"] or "pbkdf2"
    has_mk   = bool(u["mk_enc"])
    if kdf_type != "argon2id" or not has_mk:
        try:
            new_salt = os.urandom(16)
            new_pw_hash = hash_pw(pw, new_salt, "argon2id")
            master_key  = gen_master_key()
            mk_enc, mk_salt, mk_iv = wrap_master_key(master_key, pw)
            with get_db() as c:
                c.execute(
                    "UPDATE users SET password_hash=?, pw_salt=?, kdf_type=?, "
                    "mk_enc=?, mk_salt=?, mk_iv=? WHERE vault_id=?",
                    (new_pw_hash, new_salt, "argon2id", mk_enc, mk_salt, mk_iv, vid),
                )
                c.commit()
            # Re-encrypt all TOTP secrets with master_key (migrate from password-based)
            with get_db() as c:
                totp_rows = c.execute(
                    "SELECT id, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?", (vid,)
                ).fetchall()
                for row in totp_rows:
                    try:
                        plain = decrypt(row["secret_enc"], row["salt"], row["iv"], _get_vault_key(vid, pw), vid)
                        new_ct, new_s, new_iv = encrypt(plain, master_key, vid)
                        c.execute(
                            "UPDATE totp_accounts SET secret_enc=?, salt=?, iv=? WHERE id=?",
                            (new_ct, new_s, new_iv, row["id"]),
                        )
                    except Exception as e:
                        logger.error(f"MK migration TOTP {row['id']}: {e}")
                # Also re-encrypt sk_enc (secure key) with master_key
                sk = load_user_secure_key(vid, pw)  # load with old method before migration
                if sk:
                    sk_ct, sk_s, sk_iv = encrypt(sk, master_key, vid)
                    c.execute(
                        "UPDATE users SET sk_enc=?, sk_salt=?, sk_iv=? WHERE vault_id=?",
                        (sk_ct, sk_s, sk_iv, vid),
                    )
                c.commit()
            logger.info(f"Auto-upgraded vault {vid} to Argon2id + MasterKey")
        except Exception as e:
            logger.error(f"Auto-upgrade failed for {vid}: {e}")
    # ────────────────────────────────────────────────────────────

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
    _session_pw_cache[vid] = pw             # RAM cache for auto-backup
    _oab_store_password(uid, vid, pw)       # DB encrypted store for auto-backup
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

    # Block password reset for disabled accounts
    if u["account_disabled"]:
        await update.message.reply_text(
            "🚫 *This account has been disabled\\.*\n\n"
            "Password reset is not allowed for disabled accounts\\. "
            "Please contact support\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU

    # Block password reset while login is frozen (brute-force lockout)
    if is_login_frozen(vid):
        remaining, _ = get_login_freeze_remaining(vid)
        h, m = remaining // 3600, (remaining % 3600) // 60
        await update.message.reply_text(
            f"🔒 *Account disabled due to too many failed login attempts\\.*\n\n"
            f"Password reset is blocked until the disable period expires\\.\n"
            f"Try again in *{h}h {m}m*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU

    # Block password reset while already reset-frozen
    if is_reset_frozen(vid):
        remaining = get_freeze_remaining(vid)
        h, m      = remaining // 3600, (remaining % 3600) // 60
        await update.message.reply_text(
            f"⚠️ *Account temporarily disabled* due to too many failed reset attempts\\.\n\n"
            f"Try again in *{h}h {m}m*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return RESET_ID_INPUT

    # OTP request rate-limit check (2/hour, 5/24h)
    allowed, wait_secs, reason = check_otp_request_limit(vid)
    if not allowed:
        wait_h = wait_secs // 3600
        wait_m = (wait_secs % 3600) // 60
        wait_s = wait_secs % 60
        if reason == "hourly":
            await update.message.reply_text(
                f"⏳ *Too many OTP requests\\.* You can request at most {OTP_HOURLY_LIMIT} OTPs per hour\\.\\n\n"
                f"Please wait *{wait_h}h {wait_m}m {wait_s}s* and try again\\.",
                parse_mode="MarkdownV2",
                reply_markup=kb_cancel(),
            )
        else:
            await update.message.reply_text(
                f"⏳ *Daily OTP limit reached\\.* You can request at most {OTP_DAILY_LIMIT} OTPs per 24 hours\\.\n\n"
                f"Please wait *{wait_h}h {wait_m}m {wait_s}s* before trying again\\.",
                parse_mode="MarkdownV2",
                reply_markup=kb_cancel(),
            )
        return RESET_ID_INPUT

    otp = gen_otp()
    store_otp(vid, otp)
    record_otp_request(vid)   # track this request for rate-limiting
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
        # Resolve telegram_id for stats
        _u_rst = get_user(vid)
        _tid_rst = _u_rst["telegram_id"] if _u_rst else 0
        record_stat("reset_fail", telegram_id=_tid_rst, vault_id=vid)
        if frozen:
            h, m = get_freeze_remaining(vid) // 3600, (get_freeze_remaining(vid) % 3600) // 60
            await update.message.reply_text(
                f"⚠️ *Too many failed attempts\\.* Account disabled for *{h}h {m}m*\\.",
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
            f"❌ *Invalid or expired OTP\\.* {left} attempt\\(s\\) remaining before being disabled\\.",
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
            # User skipped secure key: permanently delete ALL TOTP accounts
            c.execute("DELETE FROM totp_accounts WHERE vault_id=?", (vid,))
            deleted_cnt = len(rows)
            # Generate brand-new master key and secure key
            new_secure_key = gen_secure_key()
            new_master_key = gen_master_key()
            new_mk_enc, new_mk_salt, new_mk_iv = wrap_master_key(new_master_key, new_pw)
            ct_sk, s_sk, iv_sk = encrypt(new_secure_key, new_master_key, vid)
            new_verifier = hmac.new(SERVER_KEY, new_secure_key.encode(), hashlib.sha256).hexdigest()
            c.execute(
                "UPDATE users SET password_hash=?, pw_salt=?, kdf_type=?, "
                "mk_enc=?, mk_salt=?, mk_iv=?, sk_enc=?, sk_salt=?, sk_iv=?, sk_verifier=? WHERE vault_id=?",
                (hash_pw(new_pw, new_salt, "argon2id"), new_salt, "argon2id",
                 new_mk_enc, new_mk_salt, new_mk_iv, ct_sk, s_sk, iv_sk, new_verifier, vid),
            )
            c.commit()
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

        # For sk_skipped path, password + new secure key already updated above.
        # For secure_key or no-sk-at-all paths, update password now.
        if not sk_skipped:
            ns = os.urandom(16)
            # Check if user has master key - if so, need to re-wrap it
            u_row = c.execute("SELECT mk_enc, mk_salt, mk_iv FROM users WHERE vault_id=?", (vid,)).fetchone()
            if u_row and u_row["mk_enc"] and secure_key:
                # Unauthenticated reset with secure key: we cannot unwrap old mk_enc
                # (requires old password). Instead generate new master key and re-encrypt
                # TOTP with it (we already have plaintext secrets from sk_decrypt above).
                new_master_key = gen_master_key()
                new_mk_enc, new_mk_salt, new_mk_iv = wrap_master_key(new_master_key, new_pw)
                # Re-encrypt all already-re-encrypted TOTP secrets with new master key
                totp_rows2 = c.execute(
                    "SELECT id, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?", (vid,)
                ).fetchall()
                for tr in totp_rows2:
                    try:
                        # These are now encrypted with new_pw (done above), re-encrypt with mk
                        plain2 = decrypt(tr["secret_enc"], tr["salt"], tr["iv"], new_pw, vid)
                        nct, ns2, niv = encrypt(plain2, new_master_key, vid)
                        c.execute("UPDATE totp_accounts SET secret_enc=?, salt=?, iv=? WHERE id=?",
                                  (nct, ns2, niv, tr["id"]))
                    except Exception:
                        pass
                # Store sk encrypted with new master key
                sk_nct, sk_ns, sk_niv = encrypt(secure_key, new_master_key, vid)
                c.execute(
                    "UPDATE users SET password_hash=?, pw_salt=?, kdf_type=?, "
                    "mk_enc=?, mk_salt=?, mk_iv=?, sk_enc=?, sk_salt=?, sk_iv=? WHERE vault_id=?",
                    (hash_pw(new_pw, ns, "argon2id"), ns, "argon2id",
                     new_mk_enc, new_mk_salt, new_mk_iv, sk_nct, sk_ns, sk_niv, vid),
                )
            else:
                c.execute(
                    "UPDATE users SET password_hash=?, pw_salt=?, kdf_type=? WHERE vault_id=?",
                    (hash_pw(new_pw, ns, "argon2id"), ns, "argon2id", vid),
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

    # Update auto-backup stored password after reset (use vault owner's telegram_id)
    u_owner = get_user(vid)
    if u_owner:
        _oab_store_password(u_owner["telegram_id"], vid, new_pw)

    # Resolve owner for stats
    _u_rst_ok = get_user(vid)
    _tid_rst_ok = _u_rst_ok["telegram_id"] if _u_rst_ok else 0

    if sk_skipped or deleted_cnt > 0:
        record_stat("reset_success_skip", telegram_id=_tid_rst_ok, vault_id=vid)
        result_msg = (
            "✅ *Password reset successful\\!*\n\n"
            f"⚠️ _All {em(str(deleted_cnt))} TOTP accounts were permanently deleted \\(Secure Key not provided\\)\\._\n\n"
            "🔑 A *new Secure Key* has been generated for your vault\\.\n"
            "You will see it after logging in via Settings → View Secure Key\\.\n\n"
            "Login with your new password\\."
        )
    elif reenc_fail > 0:
        record_stat("reset_success", telegram_id=_tid_rst_ok, vault_id=vid)
        result_msg = (
            "✅ *Password reset successful\\!*\n\n"
            f"🔒 _{reenc_ok} TOTP secret\\(s\\) restored successfully\\._\n"
            f"⚠️ _{reenc_fail} TOTP secret\\(s\\) could not be restored and were removed\\._\n\n"
            "Login with your new password\\."
        )
    else:
        record_stat("reset_success", telegram_id=_tid_rst_ok, vault_id=vid)
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
                f"Someone requested a password reset for your vault\\.\n\n"
                f"Your one\\-time code:\n`{otp}`\n\n"
                f"⏱ Valid for *60 seconds*\\.\n_Do not share this with anyone\\._"
            ),
            parse_mode="MarkdownV2",
        )
        await q.edit_message_text(
            "✅ *OTP sent to your Telegram account\\!*\n\n"
            "Enter the one\\-time code here:",
            parse_mode="MarkdownV2",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="settings_security")]]),
        )
    except Exception as e:
        logger.error(f"Settings reset OTP send failed: {e}")
        await q.edit_message_text(
            "⚠️ *Failed to send OTP\\.* Please try again\\.",
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
                f"⚠️ *Too many failed attempts\\.* Account disabled for *{h}h {m}m*\\.",
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
        u = c.execute("SELECT mk_enc, mk_salt, mk_iv FROM users WHERE vault_id=?", (vault,)).fetchone()
    if u and u["mk_enc"]:
        # New architecture: only re-wrap master key
        try:
            master_key = unwrap_master_key(u["mk_enc"], u["mk_salt"], u["mk_iv"], old_pw)
            new_mk_enc, new_mk_salt, new_mk_iv = wrap_master_key(master_key, new_pw)
            ns = os.urandom(16)
            with get_db() as c:
                c.execute(
                    "UPDATE users SET password_hash=?, pw_salt=?, kdf_type=?, "
                    "mk_enc=?, mk_salt=?, mk_iv=? WHERE vault_id=?",
                    (hash_pw(new_pw, ns, "argon2id"), ns, "argon2id",
                     new_mk_enc, new_mk_salt, new_mk_iv, vault),
                )
                c.commit()
        except Exception as e:
            logger.error(f"settings_reset master key rewrap: {e}")
            await update.message.reply_text(
                "❌ Password reset failed\\. Please try again\\.",
                parse_mode="MarkdownV2", reply_markup=kb_main()
            )
            return TOTP_MENU
    else:
        # Legacy path
        with get_db() as c:
            rows = c.execute(
                "SELECT id, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?", (vault,)
            ).fetchall()
            for row in rows:
                try:
                    secret    = decrypt(row["secret_enc"], row["salt"], row["iv"], _get_vault_key(vault, old_pw), vault)
                    ct, s, iv = encrypt(secret, new_pw, vault)
                    c.execute("UPDATE totp_accounts SET secret_enc=?, salt=?, iv=? WHERE id=?",
                              (ct, s, iv, row["id"]))
                except Exception as e:
                    logger.error(f"Re-encrypt TOTP settings_reset (legacy): {e}")
            new_salt = os.urandom(16)
            c.execute(
                "UPDATE users SET password_hash=?, pw_salt=? WHERE vault_id=?",
                (hash_pw(new_pw, new_salt, "argon2id"), new_salt, vault),
            )
            sk = load_user_secure_key(vault, old_pw)
            if sk:
                ct, s, iv = encrypt(sk, new_pw, vault)
                c.execute("UPDATE users SET sk_enc=?, sk_salt=?, sk_iv=? WHERE vault_id=?",
                          (ct, s, iv, vault))
            c.commit()
    ctx.user_data["password"] = new_pw
    _session_pw_cache[vault] = new_pw
    _oab_store_password(uid, vault, new_pw)
    await update.message.reply_text(
        "✅ *Password reset\\!*",
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
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="settings_security")]]),
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
    _kdf_vsk = u["kdf_type"] or "pbkdf2"
    _comp_vsk = await asyncio.to_thread(hash_pw, pw, bytes(u["pw_salt"]), _kdf_vsk)
    if not hmac.compare_digest(_comp_vsk, bytes(u["password_hash"])):
        await update.message.reply_text("❌ *Wrong password\\.*", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    sk = await asyncio.to_thread(load_user_secure_key, vault, pw)
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
    uid   = update.effective_user.id
    vault = get_session(uid)
    if vault:
        _session_pw_cache.pop(vault, None)   # clear cached password for auto-backup
    clear_session(uid)
    ctx.user_data.clear()
    await q.edit_message_text(
        "🚪 *Logged out\\.* Your data remains encrypted in the vault\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_auth(),
    )
    return AUTH_MENU

# ── SETTINGS MENU ───────────────────────────────────────────
DONATE_ADDRESS = "0xfE88De8A32A56ca157725305cB71074cE3A07034"
DONATE_LINK    = "https://nowpayments.io/donation/antonysrm"


async def show_donate(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()

    raw = _bot_settings.get("donate_message")
    if raw:
        try:
            data = json.loads(raw)
            text = data.get("text", "No Payments Method Available")
            entities_list = data.get("entities", [])
            from telegram import MessageEntity
            entities = [MessageEntity(**e) for e in entities_list] if entities_list else None
        except Exception:
            text = "No Payments Method Available"
            entities = None
    else:
        text = "No Payments Method Available"
        entities = None

    back_kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("⬅️ Back", callback_data="settings")],
    ])

    try:
        await q.edit_message_text(
            text=text,
            entities=entities,
            reply_markup=back_kb,
        )
    except Exception:
        try:
            await q.message.delete()
        except Exception:
            pass
        await ctx.bot.send_message(
            chat_id=update.effective_chat.id,
            text=text,
            entities=entities,
            reply_markup=back_kb,
        )

    return TOTP_MENU

async def settings_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "⚙️ *Settings*\n\nChoose a section:",
        parse_mode="MarkdownV2",
        reply_markup=kb_settings(),
    )
    return TOTP_MENU

async def settings_security_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Security & Access sub-menu."""
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "🔐 *Security \\& Access*\n\nManage your password and secure key\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_settings_security(),
    )
    return TOTP_MENU

async def settings_backup_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Backup & Restore sub-menu."""
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "💾 *Backup \\& Restore*\n\nExport, import, and schedule automatic backups\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_settings_backup(),
    )
    return TOTP_MENU

async def settings_account_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Account sub-menu."""
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(
        "⚙️ *Account*\n\nManage your session and account\\.",
        parse_mode="MarkdownV2",
        reply_markup=kb_settings_account(),
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
            [InlineKeyboardButton("💰 Support Us",       callback_data="donate")],
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
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="settings_security")]]),
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
    if not u:
        await update.message.reply_text("❌ Wrong password\\.", parse_mode="MarkdownV2", reply_markup=kb_cancel())
        return CHANGE_PW_OLD
    _kdf_cpw = u["kdf_type"] or "pbkdf2"
    _computed_cpw = await asyncio.to_thread(hash_pw, pw, bytes(u["pw_salt"]), _kdf_cpw)
    if not hmac.compare_digest(_computed_cpw, bytes(u["password_hash"])):
        await update.message.reply_text("❌ Wrong password\\.", parse_mode="MarkdownV2", reply_markup=kb_cancel())
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
        u = c.execute("SELECT mk_enc, mk_salt, mk_iv, kdf_type, pw_salt, sk_enc, sk_salt, sk_iv "
                      "FROM users WHERE vault_id=?", (vault,)).fetchone()
    if u and u["mk_enc"]:
        # New architecture: only re-wrap the master key with new password
        try:
            def _rewrap():
                mk  = unwrap_master_key(u["mk_enc"], u["mk_salt"], u["mk_iv"], old_pw)
                enc, salt, iv = wrap_master_key(mk, new_pw)
                ns  = os.urandom(16)
                new_hash = hash_pw(new_pw, ns, "argon2id")
                return enc, salt, iv, ns, new_hash
            new_mk_enc, new_mk_salt, new_mk_iv, ns, new_hash = await asyncio.to_thread(_rewrap)
            with get_db() as c:
                c.execute(
                    "UPDATE users SET password_hash=?, pw_salt=?, kdf_type=?, "
                    "mk_enc=?, mk_salt=?, mk_iv=? WHERE vault_id=?",
                    (new_hash, ns, "argon2id", new_mk_enc, new_mk_salt, new_mk_iv, vault),
                )
                c.commit()
        except Exception as e:
            logger.error(f"change_pw master key rewrap failed: {e}")
            await update.message.reply_text(
                "❌ Password change failed\\. Please try again\\.",
                parse_mode="MarkdownV2", reply_markup=kb_main()
            )
            return TOTP_MENU
    else:
        # Legacy path: re-encrypt all TOTP secrets and sk with new password
        processing_msg = await update.message.reply_text("⏳ Updating password, please wait...")
        def _legacy_reencrypt():
            old_vk = _get_vault_key(vault, old_pw)   # compute once
            with get_db() as c:
                rows = c.execute(
                    "SELECT id, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?", (vault,)
                ).fetchall()
                for row in rows:
                    try:
                        secret    = decrypt(row["secret_enc"], row["salt"], row["iv"], old_vk, vault)
                        ct, s, iv = encrypt(secret, new_pw, vault)
                        c.execute("UPDATE totp_accounts SET secret_enc=?, salt=?, iv=? WHERE id=?",
                                  (ct, s, iv, row["id"]))
                    except Exception as e:
                        logger.error(f"Re-encrypt TOTP during change_pw (legacy): {e}")
                ns = os.urandom(16)
                c.execute(
                    "UPDATE users SET password_hash=?, pw_salt=? WHERE vault_id=?",
                    (hash_pw(new_pw, ns, "argon2id"), ns, vault),
                )
                sk = load_user_secure_key(vault, old_pw)
                if sk:
                    ct, s, iv = encrypt(sk, new_pw, vault)
                    c.execute("UPDATE users SET sk_enc=?, sk_salt=?, sk_iv=? WHERE vault_id=?",
                              (ct, s, iv, vault))
                c.commit()
        await asyncio.to_thread(_legacy_reencrypt)
        try:
            await processing_msg.delete()
        except Exception:
            pass
    ctx.user_data["password"] = new_pw
    _session_pw_cache[vault] = new_pw
    _oab_store_password(uid, vault, new_pw)
    await update.message.reply_text(
        "✅ *Password changed\\!*",
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
    # Maintenance mode blocks TOTP add too
    if is_maintenance():
        await q.edit_message_text(MAINTENANCE_MSG, parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    # Global TOTP add toggle check
    if not TOTP_ADD_ENABLED:
        await q.edit_message_text(
            "⚠️ *Adding new TOTP accounts is currently disabled\\.*",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU
    await q.edit_message_text(
        "➕ *Add New TOTP*\n\n"
        "Send any of the following:\n"
        "📷 *QR code image*\n"
        "🔗 `otpauth://` URI\n"
        "🔑 *Base32 secret key* \\(spaces/dashes auto\\-removed\\)\n"
        "⌨️ Type `manual` to enter step by step\n\n"
        "_Your message will be auto\\-deleted_",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="main_menu")]]),
    )
    return ADD_WAITING

async def _do_save_totp(update, vault, data, pw):
    acc_type = "totp"
    hotp_ctr = 0
    note     = (data.get("note", "") or "")[:NOTE_MAX_LEN]

    # Vault TOTP limit
    with get_db() as _lc:
        _vcnt = _lc.execute(
            "SELECT COUNT(*) AS n FROM totp_accounts WHERE vault_id=?", (vault,)
        ).fetchone()["n"]
    _eff_vault_max = get_effective_vault_max(vault)
    if _vcnt >= _eff_vault_max:
        await update.message.reply_text(
            f"Vault full! Maximum {_eff_vault_max} TOTP accounts per vault. "
            "Please delete some before adding new ones."
        )
        return TOTP_MENU

    # Per-minute rate limit: atomic check+increment prevents race conditions
    if not await check_and_record_totp_add(vault):
        _eff_per_min = get_effective_per_min_limit(vault)
        await update.message.reply_text(
            f"⚠️ *Too many accounts added\\.*\n\n"
            f"Maximum *{_eff_per_min}* TOTP accounts can be added per minute\\.\n"
            "Please wait a moment and try again\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU

    # Auto-suffix name if duplicate name, enforce max 20 chars
    final_name = _auto_suffix_name(vault, data["name"])
    vault_key = await asyncio.to_thread(_get_vault_key, vault, pw)  # derive key (Argon2 blocking, run in thread)
    ct, salt, iv = encrypt(data["secret"], vault_key, vault)
    sk = load_user_secure_key(vault, pw)
    if sk:
        sk_ct, sk_s, sk_iv = sk_encrypt_totp(data["secret"].encode(), sk, vault)
    else:
        sk_ct = sk_s = sk_iv = None
    with get_db() as c:
        c.execute(
            "INSERT INTO totp_accounts (vault_id, name, issuer, secret_enc, salt, iv, "
            "sk_enc, sk_salt, sk_iv, note, account_type, hotp_counter) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
            (vault, final_name, data.get("issuer", ""), ct, salt, iv,
             sk_ct, sk_s, sk_iv, note, acc_type, hotp_ctr),
        )
        c.commit()

    record_stat("totp_added", vault_id=vault)
    bot_log("TOTP", "TOTP_ADDED", vault=vault, name=data.get("name","?"), method="manual_or_qr")

    # Show different name if it was auto-suffixed
    display_name = final_name
    suffix_note  = ""
    if final_name != data["name"].strip():
        suffix_note = f"\n_\\(Renamed to avoid duplicate: {em(final_name)}\\)_"

    try:
        code, remain, _ = generate_code(data["secret"])
    except Exception:
        code, remain = "------", 30
    issuer_line = f"\n_{em(data['issuer'])}_" if data.get("issuer") else ""
    time_info   = f"{bar(remain)} {remain}s"
    await update.message.reply_text(
        f"✅ *{em(display_name)}* added\\!{issuer_line}{suffix_note}\n\n"
        f"🔢 `{code}`\n"
        f"⏱ {time_info}\n\n"
        f"🔒 _Encrypted with AES\\-256\\-GCM \\+ Secure Key_",
        parse_mode="MarkdownV2",
        reply_markup=kb_main(),
    )
    return TOTP_MENU

async def _process_input(update, ctx, vault, pw):
    # If TOTP add is disabled globally, block all input methods
    if not TOTP_ADD_ENABLED:
        await update.message.reply_text(
            "⚠️ *Adding new TOTP accounts is currently disabled\\.*",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU, True
    # Check vault limit BEFORE downloading/scanning the QR image (saves bandwidth + CPU)
    _is_image = bool(
        update.message.photo or (
            update.message.document
            and update.message.document.mime_type
            and update.message.document.mime_type.startswith("image")
        )
    )
    if _is_image:
        with get_db() as _lc_pre:
            _vcnt_pre = _lc_pre.execute(
                "SELECT COUNT(*) AS n FROM totp_accounts WHERE vault_id=?", (vault,)
            ).fetchone()["n"]
        _eff_max_pre = get_effective_vault_max(vault)
        if _vcnt_pre >= _eff_max_pre:
            try:
                await update.message.delete()
            except Exception:
                pass
            await update.message.reply_text(
                f"Vault full! Maximum {_eff_max_pre} TOTP accounts per vault. "
                "Please delete some before adding new ones."
            )
            return TOTP_MENU, True
        # Also check per-minute rate before downloading
        if not check_totp_add_rate(vault):
            try:
                await update.message.delete()
            except Exception:
                pass
            _eff_min_pre = get_effective_per_min_limit(vault)
            await update.message.reply_text(
                f"⚠️ Too many accounts added. Maximum {_eff_min_pre} per minute. Try again shortly."
            )
            return TOTP_MENU, True
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
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="add_totp")]]),
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
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="main_menu")]]),
    )
    return ADD_WAITING

async def handle_manual_name(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    name = update.message.text.strip()
    try:
        await update.message.delete()
    except Exception:
        pass
    if not name:
        await update.message.reply_text(
            "⚠️ Name cannot be empty\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return ADD_MANUAL_NAME
    if len(name) > TOTP_NAME_MAX_LEN:
        await update.message.reply_text(
            f"⚠️ Name too long\\. Maximum *{TOTP_NAME_MAX_LEN}* characters allowed\\.\n\n"
            "Please enter a shorter name:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
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
        totp_now(cleaned)  # validation: must be valid base32 decodable
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
def build_list_page_kb(page: int, total_pages: int) -> InlineKeyboardMarkup:
    """Navigation keyboard for paginated TOTP list."""
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅️ Back", callback_data=f"list_page_{page-1}"))
    nav.append(InlineKeyboardButton(f"{page+1}/{total_pages}", callback_data="list_noop"))
    if page < total_pages - 1:
        nav.append(InlineKeyboardButton("Next ➡️", callback_data=f"list_page_{page+1}"))
    rows = [nav] if nav else []
    rows.append([
        InlineKeyboardButton("🔄 Refresh",     callback_data=f"list_page_{page}"),
        InlineKeyboardButton("🔍 Search",      callback_data="search_totp_open"),
        InlineKeyboardButton("📁 Share",       callback_data="share_codes_open"),
    ])
    rows.append([InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")])
    return InlineKeyboardMarkup(rows)

async def _render_list_page(q_or_msg, vault: str, pw: str, page: int, is_edit: bool = True):
    """Render one page of TOTP list with the new card format."""
    with get_db() as c:
        rows = c.execute(
            "SELECT id, name, issuer, secret_enc, salt, iv, note, account_type, hotp_counter "
            "FROM totp_accounts WHERE vault_id=? ORDER BY name",
            (vault,)
        ).fetchall()
    total = len(rows)
    if total == 0:
        text = "📋 *No TOTP accounts yet\\.*\n\nUse ➕ Add New TOTP to add one\\."
        kb   = kb_main()
        if is_edit:
            await q_or_msg.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
        else:
            await q_or_msg.reply_text(text, parse_mode="MarkdownV2", reply_markup=kb)
        return

    total_pages = max(1, (total + TOTP_PER_PAGE - 1) // TOTP_PER_PAGE)
    page        = max(0, min(page, total_pages - 1))
    chunk       = rows[page * TOTP_PER_PAGE : (page + 1) * TOTP_PER_PAGE]

    def _decrypt_page():
        vault_key = _get_vault_key(vault, pw)   # one Argon2/PBKDF2 call for whole page
        _entries  = []
        for i, row in enumerate(chunk, start=page * TOTP_PER_PAGE + 1):
            try:
                secret    = decrypt(row["secret_enc"], row["salt"], row["iv"], vault_key, vault)
                note      = (row["note"] or "").strip()
                code, remain, next_code = generate_code(secret)
                time_line = f"{bar(remain)} {remain}s"
                next_line = f"Next code: `{next_code}`" if next_code else ""
                note_line = f"Note: {em(note)}" if note else ""
                name_line = f"*{i}\\. {em(row['name'])}*"
                if row["issuer"]:
                    name_line += f" \\| _{em(row['issuer'])}_"
                block = [name_line, f"Current Code: `{code}` {time_line}"]
                if next_line: block.append(next_line)
                if note_line: block.append(note_line)
                _entries.append("\n".join(block))
            except Exception as e:
                logger.error(f"List TOTP error: {e}")
                _entries.append(f"*{i}\\. {em(row['name'])}*\n_\\[Decrypt error\\]_")
        return _entries
    entries = await asyncio.to_thread(_decrypt_page)

    header = f"📋 *Your TOTP Codes* \\({page+1}/{total_pages}\\)\n\n"
    text   = header + "\n\n".join(entries)
    kb     = build_list_page_kb(page, total_pages)
    if is_edit:
        await q_or_msg.edit_message_text(text, parse_mode="MarkdownV2", reply_markup=kb)
    else:
        await q_or_msg.reply_text(text, parse_mode="MarkdownV2", reply_markup=kb)

async def list_totp(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    if not vault or not pw:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    page = ctx.user_data.get("list_page", 0)
    await _render_list_page(q, vault, pw, page)
    return TOTP_MENU

async def list_page_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle page navigation buttons in list view."""
    q = update.callback_query
    await q.answer()
    if q.data == "list_noop":
        return TOTP_MENU
    try:
        page = int(q.data.split("_")[2])
    except (IndexError, ValueError):
        page = 0
    ctx.user_data["list_page"] = page
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    if not vault or not pw:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await _render_list_page(q, vault, pw, page)
    return TOTP_MENU


# ── SHARE CODES: Open folder ─────────────────────────────────
async def share_codes_open(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Open the Share Codes folder with checkbox selection (paginated, 5/page)."""
    q     = update.callback_query
    await q.answer()
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    if not vault or not pw:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    with get_db() as c:
        all_rows_raw = c.execute(
            "SELECT id, name FROM totp_accounts WHERE vault_id=? ORDER BY name", (vault,)
        ).fetchall()
    if not all_rows_raw:
        await q.edit_message_text(
            "📁 *Share Codes*\n\n⚠️ No TOTP accounts to share\\.",
            parse_mode="MarkdownV2",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")]]),
        )
        return TOTP_MENU
    all_rows  = [{"id": r["id"], "name": r["name"]} for r in all_rows_raw]
    per_pg    = 5
    tpg       = max(1, (len(all_rows) + per_pg - 1) // per_pg)
    ctx.user_data["share_all"]      = all_rows
    ctx.user_data["share_rows"]     = all_rows[:per_pg]
    ctx.user_data["share_pg"]       = 0
    ctx.user_data["share_tpg"]      = tpg
    ctx.user_data["share_selected"] = set()
    await q.edit_message_text(
        "📁 *Share Codes*\n\n"
        "Select the accounts you want to share\\.\n"
        "Tap an account to toggle\\. Then tap *🔗 Share Selected*\\.\n\n"
        "_The generated link is valid for *10 minutes*\\.\n"
        "Only the TOTP code is visible \\(no secret keys\\)\\._",
        parse_mode="MarkdownV2",
        reply_markup=build_share_selection_kb(
            all_rows[:per_pg], ctx.user_data["share_selected"],
            page=0, total_pages=tpg, all_rows=all_rows
        ),
    )
    return TOTP_MENU

async def share_toggle(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Toggle a TOTP account in/out of the share selection (max SHARE_MAX_TOTP)."""
    q = update.callback_query
    try:
        totp_id = int(q.data.split("_")[2])
    except (IndexError, ValueError):
        await q.answer()
        return TOTP_MENU
    selected: set = ctx.user_data.get("share_selected", set())
    rows           = ctx.user_data.get("share_all", ctx.user_data.get("share_rows", []))
    if totp_id in selected:
        selected.discard(totp_id)
        await q.answer()
    else:
        if len(selected) >= SHARE_MAX_TOTP:
            await q.answer(f"Maximum {SHARE_MAX_TOTP} accounts allowed per share.", show_alert=True)
            return TOTP_MENU
        selected.add(totp_id)
        await q.answer()
    ctx.user_data["share_selected"] = selected
    all_rows_list = ctx.user_data.get("share_all", [])
    _pg  = ctx.user_data.get("share_pg", 0)
    _tpg = ctx.user_data.get("share_tpg", 1)
    per_pg = 5
    rows = all_rows_list[_pg*per_pg:(_pg+1)*per_pg]  # বর্তমান পেজের ৫টা আইটেম
    try:
        await q.edit_message_reply_markup(
            reply_markup=build_share_selection_kb(rows, selected, page=_pg, total_pages=_tpg, all_rows=all_rows_list),
        )
    except Exception:
        pass
    return TOTP_MENU

async def share_pg_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Page navigation for share selection."""
    q = update.callback_query
    await q.answer()
    try:
        pg = int(q.data.split("_")[-1])
    except (IndexError, ValueError):
        pg = 0
    all_rows = ctx.user_data.get("share_all", [])
    per_pg   = 5
    tpg      = ctx.user_data.get("share_tpg", 1)
    pg       = max(0, min(pg, tpg - 1))
    chunk    = all_rows[pg * per_pg:(pg + 1) * per_pg]
    ctx.user_data["share_rows"] = chunk
    ctx.user_data["share_pg"]   = pg
    selected = ctx.user_data.get("share_selected", set())
    all_rows = ctx.user_data.get("share_all", chunk)
    try:
        await q.edit_message_reply_markup(
            reply_markup=build_share_selection_kb(chunk, selected, page=pg, total_pages=tpg, all_rows=all_rows),
        )
    except Exception:
        pass
    return TOTP_MENU


async def share_select_all(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Select all TOTP accounts for sharing."""
    q = update.callback_query
    await q.answer()
    all_rows = ctx.user_data.get("share_all", ctx.user_data.get("share_rows", []))
    ctx.user_data["share_all"]  = all_rows
    ctx.user_data["share_selected"] = {r["id"] for r in all_rows}
    pg  = ctx.user_data.get("share_pg", 0)
    tpg = ctx.user_data.get("share_tpg", 1)
    per_pg = 5
    chunk = all_rows[pg * per_pg:(pg + 1) * per_pg]
    ctx.user_data["share_rows"] = chunk
    try:
        await q.edit_message_reply_markup(
            reply_markup=build_share_selection_kb(
                chunk, ctx.user_data["share_selected"],
                page=pg, total_pages=tpg, all_rows=all_rows
            )
        )
    except Exception:
        pass
    return TOTP_MENU


async def share_limit_warn(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show alert when user tries to share more than SHARE_MAX_TOTP accounts."""
    q = update.callback_query
    await q.answer(
        f"You can share at most {SHARE_MAX_TOTP} accounts at once. "
        f"Please deselect some before sharing.",
        show_alert=True,
    )
    return TOTP_MENU


async def share_unselect_all(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Deselect all TOTP accounts."""
    q = update.callback_query
    await q.answer()
    all_rows = ctx.user_data.get("share_all", ctx.user_data.get("share_rows", []))
    ctx.user_data["share_all"]      = all_rows
    ctx.user_data["share_selected"] = set()
    pg  = ctx.user_data.get("share_pg", 0)
    tpg = ctx.user_data.get("share_tpg", 1)
    per_pg = 5
    chunk = all_rows[pg * per_pg:(pg + 1) * per_pg]
    ctx.user_data["share_rows"] = chunk
    try:
        await q.edit_message_reply_markup(
            reply_markup=build_share_selection_kb(
                chunk, ctx.user_data["share_selected"],
                page=pg, total_pages=tpg, all_rows=all_rows
            )
        )
    except Exception:
        pass
    return TOTP_MENU


async def share_generate(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Build the share link for selected TOTP accounts."""
    q     = update.callback_query
    await q.answer()
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    if not vault or not pw:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    selected: set = ctx.user_data.get("share_selected", set())
    rows           = ctx.user_data.get("share_rows", [])
    if not selected:
        await q.answer("No accounts selected.", show_alert=True)
        return TOTP_MENU
    if len(selected) > SHARE_MAX_TOTP:
        await q.answer(f"Maximum {SHARE_MAX_TOTP} accounts allowed per share.", show_alert=True)
        return TOTP_MENU
    # Use share_all (all pages), not just current page rows
    all_rows_for_share = ctx.user_data.get("share_all", rows)
    selected_ids = [r["id"] for r in all_rows_for_share if r["id"] in selected]
    id_to_name   = {r["id"]: r["name"] for r in all_rows_for_share if r["id"] in selected}
    with get_db() as c:
        placeholders = ",".join("?" * len(selected_ids))
        db_rows = c.execute(
            f"SELECT id, secret_enc, salt, iv FROM totp_accounts "
            f"WHERE vault_id=? AND id IN ({placeholders})",
            [vault] + selected_ids,
        ).fetchall()
    if not db_rows:
        await q.answer("Could not load selected accounts.", show_alert=True)
        return TOTP_MENU
    # Generate token first (needed for per-link key derivation)
    token       = gen_share_token()
    secrets_enc = []
    final_ids   = []
    final_names = []
    _vk_share = await asyncio.to_thread(_get_vault_key, vault, pw)
    for db_row in db_rows:
        try:
            plain = decrypt(db_row["secret_enc"], db_row["salt"], db_row["iv"], _vk_share, vault)
            enc   = share_encrypt_secret(plain, token)
            secrets_enc.append(enc)
            final_ids.append(db_row["id"])
            final_names.append(id_to_name.get(db_row["id"], "Unknown"))
        except Exception as e:
            logger.error(f"Share encrypt error for totp_id={db_row['id']}: {e}")
    if not secrets_enc:
        await q.answer("Could not encrypt secrets. Try again.", show_alert=True)
        return TOTP_MENU
    expires_at = int(time.time()) + SHARE_LINK_TTL
    with get_db() as c:
        c.execute(
            "INSERT INTO share_links (token, vault_id, totp_ids, secrets_enc, names, expires_at) "
            "VALUES (?,?,?,?,?,?)",
            (token, vault, json.dumps(final_ids), json.dumps(secrets_enc),
             json.dumps(final_names), expires_at),
        )
        c.commit()
    async def _cleanup():
        await asyncio.sleep(SHARE_LINK_TTL + 5)
        with get_db() as c2:
            c2.execute("DELETE FROM share_links WHERE token=?", (token,))
            c2.commit()
    asyncio.create_task(_cleanup())
    share_url  = f"https://t.me/{ctx.bot.username}?start={token}"
    exp_min = SHARE_LINK_TTL // 60
    # Build account list: show 5 per line for readability
    if len(final_names) > 5:
        name_lines = []
        for i in range(0, len(final_names), 5):
            chunk_names = final_names[i:i+5]
            # Numbered entries per chunk of 5
            for j, n in enumerate(chunk_names):
                name_lines.append(f"{i+j+1}\\. {em(n)}")
        names_text = "\n".join(name_lines)
        acct_block = f"📋 *Accounts \\({len(final_names)}\\):*\n{names_text}"
    else:
        name_lines = [f"{i+1}\\. {em(n)}" for i, n in enumerate(final_names)]
        names_text = "\n".join(name_lines)
        acct_block = f"📋 *Accounts:*\n{names_text}"
    await q.edit_message_text(
        f"🔗 *Share Link Generated\\!*\n\n"
        f"{acct_block}\n\n"
        f"⏳ *Expires in:* {exp_min} minutes\n\n"
        f"`{em(share_url)}`\n\n"
        "_Anyone with this link can view the TOTP codes for 10 minutes\\.\n"
        "No secret keys or personal info is revealed\\._",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🔗 Open Link", url=share_url)],
            [InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")],
        ]),
    )
    ctx.user_data.pop("share_selected", None)
    ctx.user_data.pop("share_rows", None)
    return TOTP_MENU

async def share_cancel(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    ctx.user_data.pop("share_selected", None)
    ctx.user_data.pop("share_rows", None)
    await q.edit_message_text("Choose an option:", reply_markup=kb_main())
    return TOTP_MENU

# ── Share View (deep link handler) ───────────────────────────
async def handle_share_view(update: Update, token: str):
    """Show live TOTP codes for a valid share link."""
    with get_db() as c:
        row = c.execute(
            "SELECT * FROM share_links WHERE token=? AND expires_at > ?",
            (token, int(time.time())),
        ).fetchone()
    if not row:
        await update.message.reply_text(
            "❌ *This share link has expired or is invalid\\.*\n\n"
            "_Links are valid for 10 minutes only\\._",
            parse_mode="MarkdownV2",
        )
        return
    names       = json.loads(row["names"])
    secrets_enc = json.loads(row["secrets_enc"])
    expires_at  = row["expires_at"]
    remaining_s = max(0, expires_at - int(time.time()))
    rem_min     = remaining_s // 60
    rem_sec     = remaining_s % 60
    entries = []
    for i, (name, enc) in enumerate(zip(names, secrets_enc)):
        try:
            secret             = share_decrypt_secret(enc, token)
            code, rm, nxt     = generate_code(secret)
            entries.append(
                f"*{em(name)}*\n"
                f"Current Code: `{code}` {bar(rm)} {rm}s\n"
                f"Next code: `{nxt}`"
            )
        except Exception as e:
            logger.error(f"Share view decrypt error idx={i}: {e}")
            entries.append(f"*{em(name)}*\n_\\[Unavailable\\]_")

    refresh_url = f"https://t.me/{update.get_bot().username}?start={token}"
    exp_line    = f"\n\n⏳ Link expires in *{rem_min}m {rem_sec}s*\\.\n_Tap below to refresh codes\\._"
    kb          = InlineKeyboardMarkup([[InlineKeyboardButton("🔄 Refresh Codes", url=refresh_url)]])

    # Send in chunks of 5 to avoid Telegram 4096-char message limit
    per_page = 5
    chunks   = [entries[i:i+per_page] for i in range(0, len(entries), per_page)]
    total_pg = len(chunks)

    for pg_idx, chunk in enumerate(chunks):
        pg_label = f" (Page {pg_idx+1}/{total_pg})" if total_pg > 1 else ""
        header   = f"📋 *Shared TOTP Codes{em(pg_label)}*\n\n"
        body     = "\n\n".join(chunk)
        # Only add expiry line on last page
        suffix   = exp_line if pg_idx == total_pg - 1 else ""
        text     = header + body + suffix
        if pg_idx == total_pg - 1:
            msg = await update.message.reply_text(text, parse_mode="MarkdownV2", reply_markup=kb)
        else:
            msg = await update.message.reply_text(text, parse_mode="MarkdownV2")
        asyncio.create_task(auto_delete_msg(msg, delay=remaining_s + 5))

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
        page     = ctx.user_data.get("edit_pg", 0)
        per_pg   = 5
        total    = len(rows)
        total_pg = max(1, (total + per_pg - 1) // per_pg)
        page     = max(0, min(page, total_pg - 1))
        chunk    = rows[page * per_pg:(page + 1) * per_pg]
        kb = [[InlineKeyboardButton(r['name'], callback_data=f"editpick_{r['id']}")] for r in chunk]
        if total_pg > 1:
            nav = []
            if page > 0:
                nav.append(InlineKeyboardButton("⬅️", callback_data=f"edit_pg_{page-1}"))
            nav.append(InlineKeyboardButton(f"{page+1}/{total_pg}", callback_data="list_noop"))
            if page < total_pg - 1:
                nav.append(InlineKeyboardButton("➡️", callback_data=f"edit_pg_{page+1}"))
            kb.append(nav)
        kb.append([InlineKeyboardButton("⬅️ Back", callback_data="main_menu")])
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

async def edit_pg_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Page navigation for edit TOTP list."""
    q = update.callback_query
    await q.answer()
    try:
        page = int(q.data.split("_")[-1])
    except (IndexError, ValueError):
        page = 0
    ctx.user_data["edit_pg"] = page
    uid   = update.effective_user.id
    vault = get_session(uid)
    if not vault:
        await q.edit_message_text("Session expired. /start", reply_markup=kb_auth())
        return AUTH_MENU
    with get_db() as c:
        rows = c.execute(
            "SELECT id, name FROM totp_accounts WHERE vault_id=? ORDER BY name", (vault,)
        ).fetchall()
    per_pg   = 5
    total_pg = max(1, (len(rows) + per_pg - 1) // per_pg)
    page     = max(0, min(page, total_pg - 1))
    chunk    = rows[page * per_pg:(page + 1) * per_pg]
    kb = [[InlineKeyboardButton(r['name'], callback_data=f"editpick_{r['id']}")] for r in chunk]
    if total_pg > 1:
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("⬅️", callback_data=f"edit_pg_{page-1}"))
        nav.append(InlineKeyboardButton(f"{page+1}/{total_pg}", callback_data="list_noop"))
        if page < total_pg - 1:
            nav.append(InlineKeyboardButton("➡️", callback_data=f"edit_pg_{page+1}"))
        kb.append(nav)
    kb.append([InlineKeyboardButton("⬅️ Back", callback_data="main_menu")])
    await q.edit_message_text(
        "✏️ *Edit TOTP* \\-\\- Select account:",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup(kb),
    )
    return EDIT_PICK


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
            [InlineKeyboardButton("📝 Note",            callback_data="edit_action_note")],
            [InlineKeyboardButton("⬅️ Back",             callback_data="edit_totp")],
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
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="edit_totp")]]),
        )
        return EDIT_RENAME_INPUT
    elif action == "showsecret":
        name = ctx.user_data.get("edit_name", "")
        await q.edit_message_text(
            f"🔍 *Show Secret Key*\n\n"
            f"Account: *{em(name)}*\n\n"
            "🔒 Enter your *account password* to reveal the secret key:",
            parse_mode="MarkdownV2",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="edit_totp")]]),
        )
        return SHOW_SECRET_PW
    elif action == "note":
        name   = ctx.user_data.get("edit_name", "")
        acc_id = ctx.user_data.get("edit_id")
        # Show current note
        current_note = ""
        if acc_id:
            with get_db() as c:
                r = c.execute("SELECT note FROM totp_accounts WHERE id=?", (acc_id,)).fetchone()
                current_note = (r["note"] or "").strip() if r else ""
        note_info = f"Current: _{em(current_note)}_\n\n" if current_note else ""
        await q.edit_message_text(
            f"📝 *Add Note to {em(name)}*\n\n"
            f"{note_info}"
            f"Enter a note \\(max *{NOTE_MAX_LEN}* characters\\)\\.\n"
            "Send a single space or `.` to clear the note:",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return NOTE_INPUT
    else:  # delete
        name = ctx.user_data.get("edit_name", "")
        await q.edit_message_text(
            f"🗑 Delete *{em(name)}*?\n\n_This cannot be undone\\._",
            parse_mode="MarkdownV2",
            reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ Confirm", callback_data="edit_action_delete_confirm")],
            [InlineKeyboardButton("⬅️ Back",   callback_data="edit_totp")],
        ]),
        )
        return EDIT_ACTION

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

async def note_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Save note (max NOTE_MAX_LEN chars) for a TOTP account."""
    raw    = update.message.text.strip()
    uid    = update.effective_user.id
    vault  = get_session(uid)
    acc_id = ctx.user_data.pop("edit_id", None)
    ctx.user_data.pop("edit_name", None)
    if not acc_id:
        await update.message.reply_text("⚠️ Session lost\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    # Clear note if user sends space or dot
    note = "" if raw in (".", " ", "") else raw[:NOTE_MAX_LEN]
    with get_db() as c:
        c.execute("UPDATE totp_accounts SET note=? WHERE id=? AND vault_id=?", (note, acc_id, vault))
        c.commit()
    if note:
        msg = f"✅ Note saved: _{em(note)}_"
    else:
        msg = "✅ Note cleared\\."
    await update.message.reply_text(msg, parse_mode="MarkdownV2", reply_markup=kb_main())
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
    _kdf_ssp = u["kdf_type"] or "pbkdf2"
    _comp_ssp = await asyncio.to_thread(hash_pw, pw, bytes(u["pw_salt"]), _kdf_ssp)
    if not hmac.compare_digest(_comp_ssp, bytes(u["password_hash"])):
        await update.message.reply_text(
            "❌ *Wrong password\\.* Secret key not revealed\\.",
            parse_mode="MarkdownV2", reply_markup=kb_main(),
        )
        ctx.user_data.pop("edit_id", None); ctx.user_data.pop("edit_name", None)
        return TOTP_MENU
    with get_db() as c:
        row = c.execute(
            "SELECT secret_enc, salt, iv FROM totp_accounts WHERE id=? AND vault_id=?",
            (acc_id, vault),
        ).fetchone()
    if not row:
        await update.message.reply_text("⚠️ Account not found\\.", parse_mode="MarkdownV2", reply_markup=kb_main())
        ctx.user_data.pop("edit_id", None); ctx.user_data.pop("edit_name", None)
        return TOTP_MENU
    try:
        _vk_ssp = await asyncio.to_thread(_get_vault_key, vault, pw)
        secret  = decrypt(row["secret_enc"], row["salt"], row["iv"], _vk_ssp, vault)
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
    uid = update.effective_user.id
    vault = get_session(uid)
    if not vault:
        await q.answer()
        await q.edit_message_text("Session expired\\.", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    allowed, reason = check_export_allowed(vault)
    if not allowed:
        if reason == "disabled":
            await q.answer(
                "Public TOTP export is temporarily disabled. You'll be notified when it's back on or please try again in a few hours.",
                show_alert=True,
            )
        else:
            await q.answer(
                "You have currently exceeded your daily Export limit, so please try again the next day.",
                show_alert=True,
            )
        return TOTP_MENU
    await q.answer()
    await q.edit_message_text(
        "📤 *Export Vault*\n\n*Step 1:* Enter your *account password* to verify:",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="settings_backup")]]),
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
    if not u:
        await update.message.reply_text(
            "❌ Wrong account password\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        return EXPORT_PW1_INPUT
    kdf_e   = u["kdf_type"] or "pbkdf2"
    computed_e = await asyncio.to_thread(hash_pw, pw, bytes(u["pw_salt"]), kdf_e)
    if not hmac.compare_digest(computed_e, bytes(u["password_hash"])):
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
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="settings_backup")]]),
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
    processing_msg = await update.message.reply_text("⏳ Preparing export...")

    def _build_export():
        vault_key = _get_vault_key(vault, pw)   # expensive once, reused for all entries
        _entries = []
        for row in rows:
            try:
                secret = decrypt(row["secret_enc"], row["salt"], row["iv"], vault_key, vault)
                _entries.append({"name": row["name"], "issuer": row["issuer"] or "", "secret": secret})
            except Exception as e:
                logger.error(f"Export decrypt: {e}")
        _plain = json.dumps({"version": 3, "vault_id": vault, "accounts": _entries}, ensure_ascii=False).encode()
        return export_encrypt(_plain, file_pw), _entries

    payload, entries = await asyncio.to_thread(_build_export)
    try:
        await processing_msg.delete()
    except Exception:
        pass
    # Timestamped filename: bv_backup_YYYYMMDD_HHMMSS.bvault
    ts_str   = datetime.datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    filename = f"bv_backup_{ts_str}.bvault"
    bio      = BytesIO(payload)
    bio.name = filename
    msg = await update.message.reply_document(
        document=bio,
        filename=filename,
        caption=(
            f"🔒 *BV Authenticator Encrypted Vault Backup*\n"
            f"📅 _{em(ts_str.replace('_', ' '))}_\n\n"
            "Import with 📥 Import Vault\\.\n"
            "Share the *file encryption password* with the importer\\.\n\n"
            "_This file will be auto\\-deleted in 60 seconds\\._"
        ),
        parse_mode="MarkdownV2",
    )
    record_ei_usage(vault, "export")
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
    uid = update.effective_user.id
    vault = get_session(uid)
    if not vault:
        await q.answer()
        await q.edit_message_text("Session expired\\.", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    allowed, reason = check_import_allowed(vault)
    if not allowed:
        if reason == "disabled":
            await q.answer(
                "Public TOTP Import is temporarily disabled. You'll be notified when it's back on or please try again in a few hours.",
                show_alert=True,
            )
        else:
            await q.answer(
                "You have currently exceeded your daily Import limit, so please try again the next day.",
                show_alert=True,
            )
        return TOTP_MENU
    await q.answer()
    await q.edit_message_text(
        "📥 *Import Vault*\n\n"
        "Send your *\\.bvault* backup file\\.\n\n"
        "_You will need the file's encryption password\\.\n"
        "Works with backups from any user\\._",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="settings_backup")]]),
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
    processing_msg = await update.message.reply_text("⏳ Decrypting file...")
    try:
        plain = await asyncio.to_thread(export_decrypt, payload, file_pw)
        data     = json.loads(plain.decode())
        accounts = data.get("accounts", [])
    except Exception:
        try:
            await processing_msg.delete()
        except Exception:
            pass
        await update.message.reply_text(
            "❌ *Wrong password or corrupted file\\.*",
            parse_mode="MarkdownV2",
            reply_markup=kb_cancel(),
        )
        ctx.user_data["import_payload"] = payload
        return IMPORT_PW_INPUT
    try:
        await processing_msg.delete()
    except Exception:
        pass
    if not accounts:
        await update.message.reply_text(
            "⚠️ No accounts found in backup file\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU
    uid   = update.effective_user.id
    vault = get_session(uid)
    # Vault limit check before importing
    file_total      = len(accounts)
    eff_max         = get_effective_vault_max(vault)
    with get_db() as _lc:
        current_count = _lc.execute(
            "SELECT COUNT(*) AS n FROM totp_accounts WHERE vault_id=?", (vault,)
        ).fetchone()["n"]
    available_slots = eff_max - current_count
    if available_slots <= 0 or file_total > available_slots:
        await update.message.reply_text(
            f"Import Failed : Vault Limit Exceeded\n\n"
            f"You're trying to import {file_total:,} TOTPs, but you only have {available_slots:,} free slots in your vault.\n\n"
            f"Your Vault Details :\n"
            f"- Total Capacity : {eff_max:,} TOTPs\n"
            f"- Currently Used : {current_count:,} TOTPs\n"
            f"- Available Space : {available_slots:,} TOTPs\n\n"
            f"What you can do :\n\n"
            f"1. Remove Some TOTPs from your Vault or import a file with up to {available_slots:,} TOTPs.\n"
            f"2. Contact the Support Team to request a limit increase.\n"
            f"3. Upgrade to Premium for more storage",
            reply_markup=kb_main(),
        )
        return TOTP_MENU
    # Directly import without duplicate prompt
    ctx.user_data["import_accounts"] = accounts
    return await _do_import(update, ctx, vault, accounts, mode="skip")

async def import_override_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle Skip / Replace choice for duplicate import entries."""
    q = update.callback_query
    await q.answer()
    mode     = q.data.split("_")[2]   # "skip" or "replace"
    uid      = update.effective_user.id
    vault    = get_session(uid)
    accounts = ctx.user_data.pop("import_accounts", [])
    if not accounts:
        await q.edit_message_text("⚠️ Session expired\\. Please try again\\.",
                                  parse_mode="MarkdownV2", reply_markup=kb_main())
        return TOTP_MENU
    # Route through a message-less import (callback context)
    await q.edit_message_text("⏳ Importing\\.\\.\\.\\.", parse_mode="MarkdownV2")
    return await _do_import(update, ctx, vault, accounts, mode=mode, reply_obj=q)

async def _do_import(update_or_cb, ctx, vault: str, accounts: list, mode: str = "skip", reply_obj=None):
    """
    mode = "skip"    → keep existing, skip duplicates
    mode = "replace" → overwrite existing with imported version
    """
    pw = ctx.user_data.get("password", "")

    # Compute expensive keys ONCE outside the loop (Argon2 / PBKDF2)
    vault_key = await asyncio.to_thread(_get_vault_key, vault, pw)
    sk        = await asyncio.to_thread(load_user_secure_key, vault, pw)

    imported = 0
    skipped  = 0
    replaced = 0

    def _do_all_crypto():
        nonlocal imported, skipped, replaced
        with get_db() as c:
            for acc in accounts:
                try:
                    ok, secret = validate_secret(acc.get("secret", ""))
                    if not ok:
                        nonlocal_skip()
                        continue
                    note  = (acc.get("note", "") or "")[:NOTE_MAX_LEN]
                    totp_now(secret)
                    ct, s, iv = encrypt(secret, vault_key, vault)
                    sk_ct = sk_s = sk_iv = None
                    if sk:
                        sk_ct, sk_s, sk_iv = sk_encrypt_totp(secret.encode(), sk, vault)
                    c.execute(
                        "INSERT INTO totp_accounts "
                        "(vault_id, name, issuer, secret_enc, salt, iv, sk_enc, sk_salt, sk_iv, "
                        "note, account_type, hotp_counter) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                        (vault, acc["name"], acc.get("issuer", ""), ct, s, iv,
                         sk_ct, sk_s, sk_iv, note, "totp", 0),
                    )
                    nonlocal_import()
                    record_stat("totp_added", vault_id=vault)
                except Exception as e:
                    logger.error(f"Import entry '{acc.get('name','?')}': {e}")
                    nonlocal_skip()
            c.commit()
    # nonlocal helpers (closures can't assign to outer nonlocal in nested def easily)
    _counts = [0, 0, 0]  # [imported, skipped, replaced]
    def nonlocal_import():  _counts[0] += 1
    def nonlocal_skip():    _counts[1] += 1
    def nonlocal_replace(): _counts[2] += 1

    await asyncio.to_thread(_do_all_crypto)
    imported, skipped, replaced = _counts
    lines = [f"✅ *Import complete\\!*\n"]
    if imported:
        lines.append(f"Added: *{imported}*")
    if replaced:
        lines.append(f"Replaced: *{replaced}*")
    if skipped:
        lines.append(f"Skipped: *{skipped}* \\(invalid/duplicate\\)")
    result_text = "\n".join(lines)
    record_ei_usage(vault, "import")
    if reply_obj and hasattr(reply_obj, "edit_message_text"):
        await reply_obj.edit_message_text(result_text, parse_mode="MarkdownV2", reply_markup=kb_main())
    elif update_or_cb.message:
        await update_or_cb.message.reply_text(result_text, parse_mode="MarkdownV2", reply_markup=kb_main())
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
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="settings_account")]]),
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
    kdf_del  = u["kdf_type"] or "pbkdf2"
    computed_del = await asyncio.to_thread(hash_pw, pw, bytes(u["pw_salt"]), kdf_del)
    if not hmac.compare_digest(computed_del, bytes(u["password_hash"])):
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
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("⬅️ Back", callback_data="settings_account")],
            [InlineKeyboardButton("🏠 Home", callback_data="main_menu")],
        ]),
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
            c.execute("DELETE FROM share_links WHERE vault_id=?",    (vault,))
            c.execute("DELETE FROM users WHERE vault_id=?",          (vault,))
            c.commit()
        record_stat("account_deleted", telegram_id=uid, vault_id=vault)
        bot_log("AUTH", "ACCOUNT_DELETED", tg_id=uid, vault=vault)
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
    """
    Handles QR/secret detection outside conversation state.
    Also auto-deletes ANY incoming private message (text, photo, document, etc.)
    after 30 seconds to prevent sensitive data accumulating in chat.
    """
    if not update.message:
        return
    uid   = update.effective_user.id
    # Silently ignore banned users
    if is_telegram_banned(uid):
        try:
            await update.message.delete()
        except Exception:
            pass
        bot_log("SECURITY", "BANNED_USER_BLOCKED", tg_id=uid)
        return
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    # Auto-delete the incoming message after 30s regardless of content
    asyncio.create_task(auto_delete_msg(update.message, delay=30))
    # Update last_seen for every message interaction
    if vault:
        update_last_seen(uid)
    # If TOTP add is globally disabled, block QR/otpauth detection here too
    if not TOTP_ADD_ENABLED and vault and pw:
        return
    if not vault or not pw:
        return
    # QR/photo scan: check vault limits BEFORE scanning (saves CPU + prevents abuse)
    if update.message.photo or (
        update.message.document
        and update.message.document.mime_type
        and update.message.document.mime_type.startswith("image")
    ):
        if not TOTP_ADD_ENABLED:
            return  # TOTP add globally disabled
        with get_db() as _gad_c:
            _row_gad  = _gad_c.execute(
                "SELECT COUNT(*) AS n FROM totp_accounts WHERE vault_id=?", (vault,)
            ).fetchone()
            _vcnt_gad = _row_gad["n"] if _row_gad else 0
        _eff_max_gad = get_effective_vault_max(vault)
        if _vcnt_gad >= _eff_max_gad:
            return  # vault full - skip scan silently
        if not check_totp_add_rate(vault):
            return  # per-minute limit hit - skip scan (actual atomic increment in _do_save_totp)
    # ── # quick search (e.g. "#google") ────────────────────────
    if update.message.text and update.message.text.strip().startswith("#"):
        query = update.message.text.strip().lstrip("#").strip().lower()
        if query:
            with get_db() as c:
                rows = c.execute(
                    "SELECT id, name, issuer, secret_enc, salt, iv, note, account_type, hotp_counter "
                    "FROM totp_accounts WHERE vault_id=? ORDER BY name", (vault,)
                ).fetchall()
            matched = [
                r for r in rows
                if query in (r["name"] or "").lower() or query in (r["note"] or "").lower()
            ]
            if not matched:
                await update.message.reply_text(
                    f"🔍 No results for `{em(query)}`\\.",
                    parse_mode="MarkdownV2",
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")],
                    ]),
                )
                return
            def _hash_search_decrypt():
                vk = _get_vault_key(vault, pw)
                _entries = []
                for i, row in enumerate(matched, 1):
                    try:
                        secret    = decrypt(row["secret_enc"], row["salt"], row["iv"], vk, vault)
                        note      = (row["note"] or "").strip()
                        code, remain, next_code = generate_code(secret)
                        time_line = f"{bar(remain)} {remain}s"
                        name_line = f"*{i}\\. {em(row['name'])}*"
                        if row["issuer"]:
                            name_line += f" \\| _{em(row['issuer'])}_"
                        block = [name_line, f"Current Code: `{code}` {time_line}"]
                        if next_code: block.append(f"Next code: `{next_code}`")
                        if note:      block.append(f"Note: {em(note)}")
                        _entries.append("\n".join(block))
                    except Exception as e:
                        logger.error(f"Hash-search decrypt: {e}")
                        _entries.append(f"*{i}\\. {em(row['name'])}*\n_\\[Decrypt error\\]_")
                return _entries
            entries = await asyncio.to_thread(_hash_search_decrypt)
            result_text = (
                f"🔍 *\\#search:* `{em(query)}` — *{len(matched)} found*\n\n"
                + "\n\n".join(entries)
            )
            await update.message.reply_text(
                result_text,
                parse_mode="MarkdownV2",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")],
                ]),
            )
            return
    # ── end # search ──────────────────────────────────────────

    if ctx.user_data.get("_global_add") and update.message.text:
        raw_name = update.message.text.strip()
        secret   = ctx.user_data.pop("pending_secret", None)
        issuer   = ctx.user_data.pop("pending_issuer", "")
        ctx.user_data.pop("_global_add", None)
        if not raw_name or not secret:
            return
        # Name length check
        if len(raw_name) > TOTP_NAME_MAX_LEN:
            await update.message.reply_text(
                f"⚠️ Name too long\\. Maximum *{TOTP_NAME_MAX_LEN}* characters\\.\n\nPlease try again with a shorter name:",
                parse_mode="MarkdownV2",
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("❌ Cancel", callback_data="global_add_cancel"),
                ]]),
            )
            ctx.user_data["pending_secret"] = secret
            ctx.user_data["pending_issuer"] = issuer
            ctx.user_data["_global_add"]    = True
            return
        # Use _do_save_totp so vault full, per-minute limit, duplicate, SK — all handled identically
        data = {"name": raw_name, "issuer": issuer, "secret": secret, "note": ""}
        await _do_save_totp(update, vault, data, pw)
        return
    result, handled = await _process_input(update, ctx, vault, pw)
    if handled and result is None and ctx.user_data.get("pending_secret"):
        ctx.user_data["_global_add"] = True
    # result may be TOTP_MENU or AUTH_MENU if an error occurred — nothing more to do

async def global_add_cancel(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    ctx.user_data.pop("pending_secret", None)
    ctx.user_data.pop("pending_issuer", None)
    ctx.user_data.pop("_global_add", None)
    await q.edit_message_text("❌ Cancelled\\.", parse_mode="MarkdownV2", reply_markup=kb_main())

# ── CANCEL / MENU ───────────────────────────────────────────
# ── AUTO-DELETE USER MESSAGES ──────────────────────────────
async def auto_delete_msg(message, delay: int = 30):
    """Delete a message after `delay` seconds. Used for sensitive inputs."""
    await asyncio.sleep(delay)
    try:
        await message.delete()
    except Exception:
        pass

# ── SEARCH TOTP ────────────────────────────────────────────
async def search_totp_open(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Open the search prompt for TOTP accounts."""
    q = update.callback_query
    await q.answer()
    uid   = update.effective_user.id
    vault = get_session(uid)
    if not vault:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    await q.edit_message_text(
        "🔍 *Search TOTP*\n\n"
        "Type `#` followed by your search term\\.\n\n"
        "Examples:\n"
        "`#google` — search by name\n"
        "`#backup note` — search in notes too\n\n"
        "_Matches name and note of all your accounts\\._",
        parse_mode="MarkdownV2",
        reply_markup=kb_cancel(),
    )
    return SEARCH_TOTP_INPUT

async def search_totp_input(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle the search query and show matching TOTP accounts."""
    text = update.message.text.strip()
    # Auto-delete the user's search message after 30s
    asyncio.create_task(auto_delete_msg(update.message, delay=30))
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    if not vault or not pw:
        await update.message.reply_text("Session expired\\. /start", parse_mode="MarkdownV2")
        return AUTH_MENU
    # Remove leading '#' and clean query
    query = text.lstrip("#").strip().lower()
    if not query:
        await update.message.reply_text(
            "⚠️ Empty search\\. Use `#name` to search\\.",
            parse_mode="MarkdownV2", reply_markup=kb_cancel()
        )
        return SEARCH_TOTP_INPUT
    with get_db() as c:
        rows = c.execute(
            "SELECT id, name, issuer, secret_enc, salt, iv, note, account_type, hotp_counter "
            "FROM totp_accounts WHERE vault_id=? ORDER BY name", (vault,)
        ).fetchall()
    # Match against name and note (case-insensitive)
    matched = [
        r for r in rows
        if query in (r["name"] or "").lower() or query in (r["note"] or "").lower()
    ]
    if not matched:
        await update.message.reply_text(
            f"🔍 No results for `{em(query)}`\\.",
            parse_mode="MarkdownV2",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🔍 Search Again", callback_data="search_totp_open")],
                [InlineKeyboardButton("🏠 Main Menu",    callback_data="main_menu")],
            ]),
        )
        return TOTP_MENU
    def _search_decrypt():
        vk = _get_vault_key(vault, pw)
        _entries = []
        for i, row in enumerate(matched, 1):
            try:
                secret    = decrypt(row["secret_enc"], row["salt"], row["iv"], vk, vault)
                note      = (row["note"] or "").strip()
                code, remain, next_code = generate_code(secret)
                time_line = f"{bar(remain)} {remain}s"
                next_line = f"Next code: `{next_code}`" if next_code else ""
                note_line = f"Note: {em(note)}" if note else ""
                name_line = f"*{i}\\. {em(row['name'])}*"
                if row["issuer"]:
                    name_line += f" \\| _{em(row['issuer'])}_"
                block = [name_line, f"Current Code: `{code}` {time_line}"]
                if next_line: block.append(next_line)
                if note_line: block.append(note_line)
                _entries.append("\n".join(block))
            except Exception as e:
                logger.error(f"Search TOTP decrypt error: {e}")
                _entries.append(f"*{i}\\. {em(row['name'])}*\n_\\[Decrypt error\\]_")
        return _entries
    entries = await asyncio.to_thread(_search_decrypt)
    result_text = (
        f"🔍 *Results for* `{em(query)}` *— {len(matched)} found*\n\n"
        + "\n\n".join(entries)
    )
    await update.message.reply_text(
        result_text,
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🔍 Search Again", callback_data="search_totp_open")],
            [InlineKeyboardButton("🏠 Main Menu",    callback_data="main_menu")],
        ]),
    )
    return TOTP_MENU

# ── ADMIN: helpers ──────────────────────────────────────────
def _is_admin_msg(update: Update) -> bool:
    """True if the message comes from the configured admin group."""
    return (
        ADMIN_GROUP_ID != 0
        and update.effective_chat is not None
        and update.effective_chat.id == ADMIN_GROUP_ID
    )

def _adm_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("👤 User Info",      callback_data="adm_user_info"),
         InlineKeyboardButton("🔧 Maintenance",    callback_data="adm_maintenance")],
        [InlineKeyboardButton("📝 Signup Control", callback_data="adm_signup"),
         InlineKeyboardButton("🔑 Login Control",  callback_data="adm_login")],
        [InlineKeyboardButton("📢 Broadcast",      callback_data="adm_broadcast"),
         InlineKeyboardButton("🔢 TOTP Limit",     callback_data="adm_totp_limit")],
        [InlineKeyboardButton("🛡 User Control",   callback_data="adm_user_control"),
         InlineKeyboardButton("📊 Statistics",     callback_data="adm_statistics")],
        [InlineKeyboardButton("💾 Backup",         callback_data="adm_backup"),
         InlineKeyboardButton("📋 Log",            callback_data="adm_log")],
        [InlineKeyboardButton("🔍 Check Abuse",    callback_data="adm_check_abuse")],
        [InlineKeyboardButton("💸 Donate",          callback_data="adm_donate")],
    ])


async def admin_group_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not _is_admin_msg(update): return
    asyncio.create_task(auto_delete_msg(update.message, delay=30))
    _admin_import_pending.pop(update.effective_chat.id, None)
    msg = await update.message.reply_text(
        "👋 *Welcome to Dashboard*",
        parse_mode="MarkdownV2", reply_markup=_adm_kb(),
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_maintenance_view_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show current maintenance status with toggle button (entry point from dashboard)."""
    q = update.callback_query; await q.answer()
    currently_on = is_maintenance()

    if currently_on:
        status_text  = "🔧 *Maintenance Mode: ON*\\n\\nUsers are currently blocked\\."
        toggle_label = "🟢 Turn OFF Maintenance"
    else:
        status_text  = "✅ *Maintenance Mode: OFF*\\n\\nBot is live for users\\."
        toggle_label = "🔴 Turn ON Maintenance"

    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(toggle_label, callback_data="adm_maintenance_toggle")],
        [InlineKeyboardButton("⬅️ Back",    callback_data="adm_back")],
    ])
    msg = await q.message.reply_text(status_text, parse_mode="MarkdownV2", reply_markup=kb)
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_maintenance_toggle_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Actually toggle the maintenance state when the toggle button is pressed."""
    q = update.callback_query; await q.answer()
    new_state = not is_maintenance()
    _save_setting("maintenance", new_state)

    if new_state:
        status_text  = "🔧 *Maintenance Mode: ON*\\n\\nUsers are currently blocked\\."
        toggle_label = "🟢 Turn OFF Maintenance"
    else:
        status_text  = "✅ *Maintenance Mode: OFF*\\n\\nBot is live for users\\."
        toggle_label = "🔴 Turn ON Maintenance"

    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(toggle_label, callback_data="adm_maintenance_toggle")],
        [InlineKeyboardButton("⬅️ Back",    callback_data="adm_back")],
    ])
    msg = await q.message.reply_text(status_text, parse_mode="MarkdownV2", reply_markup=kb)
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_statistics_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show Statistics sub-menu: Today / Weekly / Monthly / Lifetime / Back."""
    q = update.callback_query; await q.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("📅 Today",    callback_data="adm_stats_today")],
        [InlineKeyboardButton("📆 Weekly",   callback_data="adm_stats_weekly")],
        [InlineKeyboardButton("🗓 Monthly",  callback_data="adm_stats_monthly")],
        [InlineKeyboardButton("♾ Lifetime", callback_data="adm_stats_lifetime")],
        [InlineKeyboardButton("⬅️ Back",     callback_data="adm_back")],
    ])
    msg = await q.message.reply_text(
        "📊 Statistics\n\nSelect a time period to view stats.",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_stats_today_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show today's statistics (BDT 00:00 to now)."""
    q = update.callback_query; await q.answer()
    since   = _bdt_day_start(0)
    text    = _build_stats_text("Today", since, include_active=True)
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="adm_statistics")]])
    msg = await q.message.reply_text(text, reply_markup=kb)
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_stats_weekly_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show weekly statistics (last Saturday BDT 00:00 to now)."""
    q = update.callback_query; await q.answer()
    since   = _bdt_week_start()
    text    = _build_stats_text("Weekly", since, include_active=True)
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="adm_statistics")]])
    msg = await q.message.reply_text(text, reply_markup=kb)
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_stats_monthly_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show monthly statistics (1st of current month BDT 00:00 to now)."""
    q = update.callback_query; await q.answer()
    since   = _bdt_month_start()
    text    = _build_stats_text("Monthly", since, include_active=True)
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="adm_statistics")]])
    msg = await q.message.reply_text(text, reply_markup=kb)
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_stats_lifetime_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show lifetime statistics (all time, no active user count)."""
    q = update.callback_query; await q.answer()
    since = 0  # all time
    # Lifetime active = distinct users who ever had a session
    with get_db() as c:
        row = c.execute(
            "SELECT COUNT(DISTINCT telegram_id) AS n FROM vault_login_history"
        ).fetchone()
    lifetime_active = row["n"] if row else 0

    new_join   = _count_stat("signup",             since)
    disabled   = _count_stat("account_disabled",   since)
    enabled    = _count_stat("account_enabled",    since)
    net_dis    = max(0, disabled - enabled)
    deleted    = _count_stat("account_deleted",    since)
    totp_add   = _count_stat("totp_added",         since)
    login_ok   = _count_stat("login_success",      since)
    login_fail = _count_stat("login_fail",         since)
    reset_ok   = _count_stat("reset_success",      since)
    reset_skip = _count_stat("reset_success_skip", since)
    reset_fail = _count_stat("reset_fail",         since)

    lines = [
        "📊 *Lifetime Statistics*\n",
        f"👥 Total Users Joined  : {new_join} User",
        f"🟢 Active Users (ever) : {lifetime_active} User",
        f"🔒 Disabled Accounts   : {net_dis} Account",
        f"🗑 Deleted Accounts    : {deleted} Account",
        f"🔐 Total TOTP Added    : {totp_add} TOTP",
        f"✅ Login Success       : {login_ok} Success",
        f"❌ Login Failed        : {login_fail} Failed",
        f"✅ Reset Success       : {reset_ok} Success",
        f"⏭ Reset w/ Skip       : {reset_skip} Success",
        f"❌ Reset Failed        : {reset_fail} Failed",
    ]
    text = "\n".join(lines)
    kb   = InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Back", callback_data="adm_statistics")]])
    msg  = await q.message.reply_text(text, reply_markup=kb)
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_user_control_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show User Control sub-menu with 7 buttons."""
    q = update.callback_query; await q.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Account Enable",          callback_data="adm_uc_enable")],
        [InlineKeyboardButton("🚫 Account Disable",         callback_data="adm_uc_disable")],
        [InlineKeyboardButton("📋 Disabled ID List",        callback_data="adm_uc_disabled_list")],
        [InlineKeyboardButton("🔨 Telegram ID Ban",         callback_data="adm_uc_ban")],
        [InlineKeyboardButton("✅ Telegram ID Unban",       callback_data="adm_uc_unban")],
        [InlineKeyboardButton("📋 Telegram Ban ID List",    callback_data="adm_uc_ban_list")],
        [InlineKeyboardButton("⬅️ Back",                    callback_data="adm_back")],
    ])
    msg = await q.message.reply_text("🛡 User Control\n\nManage accounts and bans.", reply_markup=kb)
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_uc_enable_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for identifier to enable an account."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_uc_enable_wait"}
    msg = await q.message.reply_text(
        "Please provide the Vault ID, Telegram ID or Username of the ID you want to enable."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_uc_disable_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for identifier to disable an account."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_uc_disable_wait"}
    msg = await q.message.reply_text(
        "Please provide the Vault ID, Telegram ID or Username of the ID you want to Disable."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_uc_disabled_list_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Export list of disabled accounts as txt file."""
    q = update.callback_query; await q.answer()
    chat_id = update.effective_chat.id
    with get_db() as c:
        rows = c.execute(
            "SELECT vault_id, telegram_id, tg_username, account_disabled FROM users "
            "WHERE account_disabled=1 ORDER BY vault_id"
        ).fetchall()
    if not rows:
        msg = await q.message.reply_text("No disabled accounts found.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    lines = ["Disabled Accounts List", f"Total: {len(rows)}", "=" * 40]
    for r in rows:
        uname = f"@{r['tg_username']}" if r["tg_username"] else "(no username)"
        lines.append(f"Vault: {r['vault_id']}  |  TG: {r['telegram_id']}  |  {uname}")
    bio = BytesIO("\n".join(lines).encode("utf-8"))
    bio.name = "disabled_accounts.txt"
    await ctx.bot.send_document(
        chat_id=chat_id, document=bio, filename="disabled_accounts.txt",
        caption=f"📋 {len(rows)} disabled account(s)."
    )


async def adm_uc_ban_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for Telegram ID or username to ban."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_uc_ban_wait"}
    msg = await q.message.reply_text(
        "Please provide the username or user ID of the Telegram ID you want to ban."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_uc_unban_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for Telegram ID or username to unban."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_uc_unban_wait"}
    msg = await q.message.reply_text(
        "Please provide the username or user ID of the Telegram ID you want to unban."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_uc_ban_list_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Export list of banned Telegram IDs as txt file."""
    q = update.callback_query; await q.answer()
    chat_id  = update.effective_chat.id
    banned   = get_all_banned_users()
    if not banned:
        msg = await q.message.reply_text("No banned users found.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    lines = ["Telegram Banned ID List", f"Total: {len(banned)}", "=" * 40]
    for b in banned:
        uname    = f"@{b['tg_username']}" if b["tg_username"] else "(no username)"
        ban_date = datetime.datetime.fromtimestamp(b["banned_at"]).strftime("%Y-%m-%d %H:%M UTC")
        lines.append(f"TG: {b['telegram_id']}  |  {uname}  |  Banned: {ban_date}")
    bio = BytesIO("\n".join(lines).encode("utf-8"))
    bio.name = "banned_users.txt"
    await ctx.bot.send_document(
        chat_id=chat_id, document=bio, filename="banned_users.txt",
        caption=f"📋 {len(banned)} banned user(s)."
    )


async def adm_backup_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show Backup sub-menu with 5 buttons."""
    q = update.callback_query; await q.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("💾 Backup All Data",          callback_data="adm_backup_all")],
        [InlineKeyboardButton("📥 Restore All Data",         callback_data="adm_backup_restore")],
        [InlineKeyboardButton("👤 Backup Specific User Data",callback_data="adm_backup_specific")],
        [InlineKeyboardButton("🔧 User Backup Control",      callback_data="adm_backup_user_control")],
        [InlineKeyboardButton("⬅️ Back",                     callback_data="adm_back")],
    ])
    msg = await q.message.reply_text(
        "💾 Backup & Restore\n\nChoose an option below.", reply_markup=kb
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_backup_all_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin for encryption password to backup all data."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_backup_pw_wait"}
    msg = await q.message.reply_text(
        "Enter the password you want to use for file encryption."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_backup_restore_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin to send the encrypted backup file."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_backup_restore_file"}
    msg = await q.message.reply_text("Send your encrypted data file here.")
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_backup_specific_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for Vault ID or Telegram ID to export specific user data."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_backup_specific_wait"}
    msg = await q.message.reply_text(
        "Provide the Telegram user ID or vault ID of the user whose vault you want to export."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_backup_user_control_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """User Backup Control: Offline Backup / Backup Reminder / Back."""
    q = update.callback_query; await q.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("💾 Offline Backup",   callback_data="adm_buc_offline")],
        [InlineKeyboardButton("🔔 Backup Reminder",  callback_data="adm_buc_reminder")],
        [InlineKeyboardButton("⬅️ Back",             callback_data="adm_backup")],
    ])
    msg = await q.message.reply_text(
        "🔧 User Backup Control\n\nManage default schedules for all users.",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_buc_offline_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Offline Backup sub-menu: Weekly Day / Monthly Date / Back."""
    q = update.callback_query; await q.answer()
    wd  = list(_WEEKDAY_MAP.keys())[DEFAULT_OFFLINE_BACKUP_WEEKDAY].capitalize()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(f"📅 Weekly Offline Backup Day  ({wd})",       callback_data="adm_buc_offline_weekly")],
        [InlineKeyboardButton(f"📆 Monthly Offline Backup Date  ({DEFAULT_OFFLINE_BACKUP_MONTHLY_DATE}th)", callback_data="adm_buc_offline_monthly")],
        [InlineKeyboardButton("⬅️ Back", callback_data="adm_backup_user_control")],
    ])
    msg = await q.message.reply_text(
        f"💾 Offline Backup Schedule\n\n"
        f"Weekly backup day: {wd}\n"
        f"Monthly backup date: {DEFAULT_OFFLINE_BACKUP_MONTHLY_DATE}\n\n"
        f"Backups run at 20:00 BDT for users with offline backup enabled.",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_buc_offline_weekly_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for weekly offline backup day."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_buc_offline_weekly_wait"}
    msg = await q.message.reply_text(
        "Which day would you like to set as the default for weekly offline backups? "
        "Please write the full name of the day in English. "
        "For example: 'Saturday', 'Sunday'"
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_buc_offline_monthly_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for monthly offline backup date."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_buc_offline_monthly_wait"}
    msg = await q.message.reply_text(
        "Which Date would you like to set as the default for monthly backups? "
        "Please write in integer."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_buc_reminder_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Backup Reminder sub-menu: Weekly Day / Monthly Date / Back."""
    q = update.callback_query; await q.answer()
    wd  = list(_WEEKDAY_MAP.keys())[DEFAULT_REMINDER_WEEKDAY].capitalize()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(f"📅 Weekly Reminder Day  ({wd})",        callback_data="adm_buc_reminder_weekly")],
        [InlineKeyboardButton(f"📆 Monthly Reminder Date  ({DEFAULT_REMINDER_MONTHLY_DATE}th)", callback_data="adm_buc_reminder_monthly")],
        [InlineKeyboardButton("⬅️ Back", callback_data="adm_backup_user_control")],
    ])
    msg = await q.message.reply_text(
        f"🔔 Backup Reminder Schedule\n\n"
        f"Weekly reminder day: {wd}\n"
        f"Monthly reminder date: {DEFAULT_REMINDER_MONTHLY_DATE}\n\n"
        f"Reminders sent at 20:00 BDT for users with reminders enabled.",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_buc_reminder_weekly_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for weekly reminder day."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_buc_reminder_weekly_wait"}
    msg = await q.message.reply_text(
        "Which day would you like to set as the default for weekly reminders? "
        "Please write the full name of the day in English. "
        "For example: 'Saturday', 'Sunday'"
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_buc_reminder_monthly_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for monthly reminder date."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_buc_reminder_monthly_wait"}
    msg = await q.message.reply_text(
        "Which Date would you like to set as the default for monthly reminders? "
        "Please write in integer."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_log_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Export last 24h activity log as a .txt file to admin group."""
    q = update.callback_query; await q.answer()
    chat_id  = update.effective_chat.id
    now_ts   = _dt.datetime.now(_BDT).timestamp()
    cutoff   = now_ts - 86400  # 24 hours

    # Filter log entries from last 24h
    entries = [line for ts, line in _activity_log if ts >= cutoff]

    if not entries:
        msg = await q.message.reply_text("No activity in the last 24 hours.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    header_lines = [
        "=" * 60,
        f"BOT ACTIVITY LOG - Last 24 Hours",
        f"Generated: {_dt.datetime.now(_BDT).strftime('%Y-%m-%d %H:%M:%S BDT')}",
        f"Total entries: {len(entries)}",
        "=" * 60,
        "",
    ]
    content_bytes = ("\n".join(header_lines + entries) + "\n").encode("utf-8")
    bio      = BytesIO(content_bytes)
    bio.name = "bot_activity_log.txt"
    fname    = f"bot_log_{_dt.datetime.now(_BDT).strftime('%Y%m%d_%H%M')}.txt"
    await ctx.bot.send_document(
        chat_id=chat_id,
        document=bio,
        filename=fname,
        caption=f"📋 Activity log: last 24h ({len(entries)} entries)",
    )


async def adm_noop_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.callback_query.answer("Coming soon!", show_alert=False)


async def adm_user_info_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    chat_id = update.effective_chat.id
    _admin_import_pending[chat_id] = {"step": "adm_user_info_wait"}
    msg = await q.message.reply_text(
        "Send User Vault ID, Telegram User ID or @Username to fetch user details."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_totp_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    totp_add_label = "✅ TOTP Add: ON" if TOTP_ADD_ENABLED else "🚫 TOTP Add: OFF"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("🔢 Vault Max Limit",              callback_data="adm_vault_limit")],
        [InlineKeyboardButton("⏱ Per Minute Limit",              callback_data="adm_min_limit")],
        [InlineKeyboardButton("👤 Specific User Vault Max Limit",callback_data="adm_specific_vault_max")],
        [InlineKeyboardButton("⏱ Specific User Vault Per Minute Limit", callback_data="adm_specific_vault_min")],
        [InlineKeyboardButton(totp_add_label,                    callback_data="adm_totp_onoff")],
        [InlineKeyboardButton("📦 TOTP Export & Import",         callback_data="adm_ei_menu")],
        [InlineKeyboardButton("⬅️ Back",                         callback_data="adm_back")],
    ])
    totp_status = "ON (users can add TOTP)" if TOTP_ADD_ENABLED else "OFF (no new TOTP allowed)"
    await q.message.reply_text(
        f"TOTP Limit Settings\n\nGlobal Vault Max: {MAX_TOTP_PER_VAULT} per vault\n"
        f"Global Per-Minute: {MAX_TOTP_PER_MINUTE} per vault/min\n"
        f"TOTP Add: {totp_status}\n\n"
        f"Use Specific User buttons to override limits for individual vaults.",
        reply_markup=kb,
    )


async def adm_totp_onoff_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Toggle TOTP add on/off globally. When OFF, no user can add new TOTP accounts
    via any method (button, QR code, otpauth URI, manual entry)."""
    q = update.callback_query; await q.answer()
    new_state = not TOTP_ADD_ENABLED
    globals()["TOTP_ADD_ENABLED"] = new_state
    status    = "ON" if new_state else "OFF"
    action    = "enabled" if new_state else "disabled"
    totp_add_label = "✅ TOTP Add: ON" if new_state else "🚫 TOTP Add: OFF"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("🔢 Vault Max Limit",              callback_data="adm_vault_limit")],
        [InlineKeyboardButton("⏱ Per Minute Limit",              callback_data="adm_min_limit")],
        [InlineKeyboardButton("👤 Specific User Vault Max Limit",callback_data="adm_specific_vault_max")],
        [InlineKeyboardButton("⏱ Specific User Vault Per Minute Limit", callback_data="adm_specific_vault_min")],
        [InlineKeyboardButton(totp_add_label,                    callback_data="adm_totp_onoff")],
        [InlineKeyboardButton("⬅️ Back",                         callback_data="adm_back")],
    ])
    msg = await q.message.reply_text(
        f"✅ TOTP Add has been {action}.\n\nTOTP Add is now: {status}",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))



# ── ADMIN: Export & Import menu (10 buttons) ──────────────────────────────────

def _ei_menu_kb() -> InlineKeyboardMarkup:
    """Build the Export & Import admin menu keyboard with live on/off labels."""
    exp_label = "✅ Public Export: ON"  if is_public_export_enabled()  else "🚫 Public Export: OFF"
    imp_label = "✅ Public Import: ON"  if is_public_import_enabled()  else "🚫 Public Import: OFF"
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📤 Public Vault Export Limit",        callback_data="adm_ei_pub_exp_limit")],
        [InlineKeyboardButton("📥 Public Vault Import Limit",        callback_data="adm_ei_pub_imp_limit")],
        [InlineKeyboardButton("🔒 Specific Vault Export Limit",      callback_data="adm_ei_spec_exp_limit")],
        [InlineKeyboardButton("🔓 Specific Vault Import Limit",      callback_data="adm_ei_spec_imp_limit")],
        [InlineKeyboardButton("📋 Specific Vault Export Limit List", callback_data="adm_ei_spec_exp_list")],
        [InlineKeyboardButton("📋 Specific Vault Import Limit List", callback_data="adm_ei_spec_imp_list")],
        [InlineKeyboardButton(exp_label,                             callback_data="adm_ei_pub_exp_toggle")],
        [InlineKeyboardButton(imp_label,                             callback_data="adm_ei_pub_imp_toggle")],
        [InlineKeyboardButton("⬅️ Back",                             callback_data="adm_totp_limit")],
        [InlineKeyboardButton("🏠 Home",                             callback_data="adm_back")],
    ])


async def adm_ei_menu_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show Export & Import admin menu."""
    q = update.callback_query; await q.answer()
    exp_lim = get_public_export_limit()
    imp_lim = get_public_import_limit()
    msg = await q.message.reply_text(
        f"📦 TOTP Export & Import Settings\n\n"
        f"Public Export limit : {exp_lim}/day\n"
        f"Public Import limit : {imp_lim}/day\n"
        f"Public Export       : {'ON' if is_public_export_enabled() else 'OFF'}\n"
        f"Public Import       : {'ON' if is_public_import_enabled() else 'OFF'}",
        reply_markup=_ei_menu_kb(),
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_ei_pub_exp_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin for new public daily export limit."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_ei_pub_exp_limit_wait"}
    msg = await q.message.reply_text(
        "Please enter and send the number you want to set as the Vault Export limit for the Public Vault."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_ei_pub_imp_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin for new public daily import limit."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_ei_pub_imp_limit_wait"}
    msg = await q.message.reply_text(
        "Please enter and send the number you want to set as the Vault Import limit for the Public Vault."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_ei_spec_exp_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin for Vault/Telegram ID to set specific export limit."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_ei_spec_exp_id_wait"}
    msg = await q.message.reply_text(
        "Please provide the Vault ID or Telegram ID of the specific vault "
        "for which you want to set the export limit."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_ei_spec_imp_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin for Vault/Telegram ID to set specific import limit."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_ei_spec_imp_id_wait"}
    msg = await q.message.reply_text(
        "Please provide the Vault ID or Telegram ID of the specific vault "
        "for which you want to set the import limit."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_ei_spec_exp_list_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Send a TXT file listing all vaults with specific export limits."""
    q = update.callback_query; await q.answer()
    with get_db() as c:
        rows = c.execute(
            "SELECT vault_id, export_limit FROM vault_ei_limits WHERE export_limit IS NOT NULL ORDER BY vault_id"
        ).fetchall()
    if not rows:
        msg = await q.message.reply_text("No specific vault export limits set yet.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    lines = ["Vault ID               | Export Limit/day", "-" * 40]
    for r in rows:
        lines.append(f"{r['vault_id']:<22} | {r['export_limit']}")
    txt = "\n".join(lines).encode()
    bio = BytesIO(txt)
    bio.name = "specific_export_limits.txt"
    msg = await q.message.reply_document(document=bio, filename="specific_export_limits.txt")
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_ei_spec_imp_list_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Send a TXT file listing all vaults with specific import limits."""
    q = update.callback_query; await q.answer()
    with get_db() as c:
        rows = c.execute(
            "SELECT vault_id, import_limit FROM vault_ei_limits WHERE import_limit IS NOT NULL ORDER BY vault_id"
        ).fetchall()
    if not rows:
        msg = await q.message.reply_text("No specific vault import limits set yet.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    lines = ["Vault ID               | Import Limit/day", "-" * 40]
    for r in rows:
        lines.append(f"{r['vault_id']:<22} | {r['import_limit']}")
    txt = "\n".join(lines).encode()
    bio = BytesIO(txt)
    bio.name = "specific_import_limits.txt"
    msg = await q.message.reply_document(document=bio, filename="specific_import_limits.txt")
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_ei_pub_exp_toggle_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Toggle public export on/off."""
    q = update.callback_query; await q.answer()
    new_state = not is_public_export_enabled()
    _save_setting("public_export_enabled", new_state)
    status = "ON" if new_state else "OFF"
    msg = await q.message.reply_text(
        f"✅ Public Export is now {status}.",
        reply_markup=_ei_menu_kb(),
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_ei_pub_imp_toggle_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Toggle public import on/off."""
    q = update.callback_query; await q.answer()
    new_state = not is_public_import_enabled()
    _save_setting("public_import_enabled", new_state)
    status = "ON" if new_state else "OFF"
    msg = await q.message.reply_text(
        f"✅ Public Import is now {status}.",
        reply_markup=_ei_menu_kb(),
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))

# ── End Export & Import admin handlers ────────────────────────────────────────

async def adm_totp_dup_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin for new TOTP duplicate limit."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_totp_dup_limit_wait"}
    msg = await q.message.reply_text(
        f"Write in numbers how many Duplicate you want to keep per TOTP.\n"
        f"(Current: {MAX_TOTP_DUPLICATE})"
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_vault_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_vault_limit_wait"}
    msg = await q.message.reply_text(
        "Set maximum TOTP limit per vault. Enter a number.\n\n"
        "Default: 200 TOTP per user\n\n"
        "To change the limit, send the new maximum number of TOTP entries allowed per user."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_min_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_min_limit_wait"}
    msg = await q.message.reply_text(
        "Set maximum TOTP limit per minute per vault. Enter a number.\n\n"
        "Default: 20 TOTP/min per user\n\n"
        "To change the rate limit, send the new maximum number of TOTP entries allowed per minute per user."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_specific_vault_max_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin to identify which vault they want to set a custom max limit for."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_specific_vault_max_id"}
    msg = await q.message.reply_text(
        "Enter the User ID, @Username, or Vault ID of the specific user "
        "to change their TOTP Vault Max limit."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_specific_vault_min_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin to identify which vault they want to set a custom per-min limit for."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_specific_vault_min_id"}
    msg = await q.message.reply_text(
        "Enter the User ID, @Username, or Vault ID of the specific user "
        "to change their TOTP Vault per minute limit."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_signup_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show Signup Control menu with 4 buttons."""
    q = update.callback_query; await q.answer()
    pub_status = "ON" if is_signup_enabled() else "OFF"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(f"🌐 Public Sign-Up  (currently {pub_status})", callback_data="adm_signup_public_toggle")],
        [InlineKeyboardButton("👤 Specific Signup",                           callback_data="adm_specific_signup")],
        [InlineKeyboardButton("📋 Specific Signup Off User List",             callback_data="adm_signup_off_list")],
        [InlineKeyboardButton(f"📊 Weekly Signup Limit  (currently {MAX_WEEKLY_SIGNUPS}/wk)", callback_data="adm_weekly_signup_limit")],
        [InlineKeyboardButton("⬅️ Back",                                      callback_data="adm_back")],
    ])
    msg = await q.message.reply_text(
        f"📝 Signup Control\n\nPublic Sign-Up: {pub_status}\nWeekly Signup Limit: {MAX_WEEKLY_SIGNUPS}/week\n"
        "Use the buttons below to manage signup settings.",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_weekly_signup_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin how many signups per week to allow."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_weekly_signup_limit_wait"}
    msg = await q.message.reply_text(
        f"Write in numbers how many signups you want to keep per week.\n"
        f"(Current: {MAX_WEEKLY_SIGNUPS}/week)"
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_signup_public_toggle_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Toggle global public signup on/off."""
    q = update.callback_query; await q.answer()
    new_state = not is_signup_enabled()
    _save_setting("signup_enabled", new_state)
    pub_status = "ON" if new_state else "OFF"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(f"🌐 Public Sign-Up  (currently {pub_status})", callback_data="adm_signup_public_toggle")],
        [InlineKeyboardButton("👤 Specific Signup",                           callback_data="adm_specific_signup")],
        [InlineKeyboardButton("📋 Specific Signup Off User List",             callback_data="adm_signup_off_list")],
        [InlineKeyboardButton("⬅️ Back",                                      callback_data="adm_back")],
    ])
    action_word = "enabled" if new_state else "disabled"
    msg = await q.message.reply_text(
        f"✅ Public Sign-Up has been {action_word}.\n\nPublic Sign-Up: {pub_status}",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_specific_signup_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show Specific Signup sub-menu: Enable / Disable / Back."""
    q = update.callback_query; await q.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Signup Enable",  callback_data="adm_specific_signup_enable")],
        [InlineKeyboardButton("🚫 Signup Disable", callback_data="adm_specific_signup_disable")],
        [InlineKeyboardButton("⬅️ Back",           callback_data="adm_signup")],
    ])
    msg = await q.message.reply_text(
        "👤 Specific Signup Control\n\n"
        "Enable or disable signup for a specific user by Telegram ID or @username.",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_specific_signup_enable_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for Telegram ID/@username to enable signup."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_specific_signup_enable_wait"}
    msg = await q.message.reply_text(
        "Enter the Telegram ID or @username to Enable signup for that user."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_specific_signup_disable_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for Telegram ID/@username to disable signup."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_specific_signup_disable_wait"}
    msg = await q.message.reply_text(
        "Enter the Telegram ID or @username to disable signup for that user."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_signup_off_list_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Send a .txt file listing all users with specific signup disabled."""
    q = update.callback_query; await q.answer()
    chat_id    = update.effective_chat.id
    disabled_ids = get_all_signup_disabled_users()
    if not disabled_ids:
        msg = await q.message.reply_text("No users with specific signup disabled.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    # Fetch usernames from DB
    lines_out = []
    with get_db() as c:
        for tid in disabled_ids:
            row = c.execute(
                "SELECT tg_username, telegram_id FROM users WHERE telegram_id=?", (tid,)
            ).fetchone()
            if row:
                uname = f"@{row['tg_username']}" if row["tg_username"] else "(no username)"
                lines_out.append(f"{row['telegram_id']}  {uname}")
            else:
                lines_out.append(f"{tid}  (not registered)")
    content_bytes = (
        f"Specific Signup Disabled Users\n"
        f"Total: {len(disabled_ids)}\n"
        + "=" * 40 + "\n"
        + "\n".join(lines_out) + "\n"
    ).encode("utf-8")
    bio      = BytesIO(content_bytes)
    bio.name = "signup_disabled_users.txt"
    await ctx.bot.send_document(
        chat_id=chat_id,
        document=bio,
        filename="signup_disabled_users.txt",
        caption=f"📋 {len(disabled_ids)} user(s) with specific signup disabled.",
    )


async def adm_login_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show Login Control menu with 4 buttons."""
    q = update.callback_query; await q.answer()
    pub_status = "ON" if is_login_enabled() else "OFF"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(f"🌐 Public Login  (currently {pub_status})", callback_data="adm_login_public_toggle")],
        [InlineKeyboardButton("👤 Specific Login",                          callback_data="adm_specific_login")],
        [InlineKeyboardButton("📋 Specific Login Off User List",            callback_data="adm_login_off_list")],
        [InlineKeyboardButton(f"📊 Daily Login Limit  (currently {MAX_DAILY_LOGINS}/day)", callback_data="adm_daily_login_limit")],
        [InlineKeyboardButton("⬅️ Back",                                    callback_data="adm_back")],
    ])
    msg = await q.message.reply_text(
        f"🔑 Login Control\n\nPublic Login: {pub_status}\nDaily Login Limit: {MAX_DAILY_LOGINS}/day\n"
        "Use the buttons below to manage login settings.",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_daily_login_limit_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin how many logins per day to allow."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_daily_login_limit_wait"}
    msg = await q.message.reply_text(
        f"Write in numbers how many login you want to keep per day.\n"
        f"(Current: {MAX_DAILY_LOGINS}/day)"
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_login_public_toggle_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Toggle global public login on/off."""
    q = update.callback_query; await q.answer()
    new_state = not is_login_enabled()
    _save_setting("login_enabled", new_state)
    pub_status = "ON" if new_state else "OFF"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(f"🌐 Public Login  (currently {pub_status})", callback_data="adm_login_public_toggle")],
        [InlineKeyboardButton("👤 Specific Login",                          callback_data="adm_specific_login")],
        [InlineKeyboardButton("📋 Specific Login Off User List",            callback_data="adm_login_off_list")],
        [InlineKeyboardButton("⬅️ Back",                                    callback_data="adm_back")],
    ])
    action_word = "enabled" if new_state else "disabled"
    msg = await q.message.reply_text(
        f"✅ Public Login has been {action_word}.\n\nPublic Login: {pub_status}",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_specific_login_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show Specific Login sub-menu: Enable / Disable / Back."""
    q = update.callback_query; await q.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Login Enable",  callback_data="adm_specific_login_enable")],
        [InlineKeyboardButton("🚫 Login Disable", callback_data="adm_specific_login_disable")],
        [InlineKeyboardButton("⬅️ Back",          callback_data="adm_login")],
    ])
    msg = await q.message.reply_text(
        "👤 Specific Login Control\n\n"
        "Enable or disable login for a specific user by Telegram ID or @username.",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_specific_login_enable_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for Telegram ID/@username to enable login."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_specific_login_enable_wait"}
    msg = await q.message.reply_text(
        "Enter the Telegram ID or @username to Enable login for that user."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_specific_login_disable_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask for Telegram ID/@username to disable login."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_specific_login_disable_wait"}
    msg = await q.message.reply_text(
        "Enter the Telegram ID or @username to disable login for that user."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


async def adm_login_off_list_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Send a .txt file listing all users with specific login disabled."""
    q = update.callback_query; await q.answer()
    chat_id      = update.effective_chat.id
    disabled_ids = get_all_login_disabled_users()
    if not disabled_ids:
        msg = await q.message.reply_text("No users with specific login disabled.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    lines_out = []
    with get_db() as c:
        for tid in disabled_ids:
            row = c.execute(
                "SELECT tg_username, telegram_id FROM users WHERE telegram_id=?", (tid,)
            ).fetchone()
            if row:
                uname = f"@{row['tg_username']}" if row["tg_username"] else "(no username)"
                lines_out.append(f"{row['telegram_id']}  {uname}")
            else:
                lines_out.append(f"{tid}  (not registered)")
    content_bytes = (
        "Specific Login Disabled Users\n"
        f"Total: {len(disabled_ids)}\n"
        + "=" * 40 + "\n"
        + "\n".join(lines_out) + "\n"
    ).encode("utf-8")
    bio      = BytesIO(content_bytes)
    bio.name = "login_disabled_users.txt"
    await ctx.bot.send_document(
        chat_id=chat_id,
        document=bio,
        filename="login_disabled_users.txt",
        caption=f"📋 {len(disabled_ids)} user(s) with specific login disabled.",
    )


async def adm_account_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Entry point for User Account management from dashboard."""
    q = update.callback_query; await q.answer()
    chat_id = update.effective_chat.id
    _admin_import_pending[chat_id] = {"step": "adm_account_wait"}
    msg = await q.message.reply_text(
        "Send the Vault ID, Telegram User ID, or @Username of the user."
        "\n\nI will show their account status with options to enable or disable it.",
        parse_mode=None,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_account_action_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Handle disable/enable button press for a specific user account."""
    q = update.callback_query; await q.answer()
    data = q.data  # "adm_account_disable:vault_id" or "adm_account_enable:vault_id"
    parts = data.split(":", 1)
    if len(parts) != 2:
        return
    action, vault_id = parts[0], parts[1]
    with get_db() as c:
        u = c.execute("SELECT * FROM users WHERE vault_id=?", (vault_id,)).fetchone()
        if not u:
            await q.message.reply_text("User not found.")
            return
        flag = 1 if action == "adm_account_disable" else 0
        if flag:
            c.execute(
                "UPDATE users SET account_disabled=1, "
                "total_disabled_count=COALESCE(total_disabled_count,0)+1 WHERE vault_id=?",
                (vault_id,)
            )
            c.execute("DELETE FROM sessions WHERE vault_id=?", (vault_id,))
        else:
            c.execute("UPDATE users SET account_disabled=0 WHERE vault_id=?", (vault_id,))
        c.commit()
    if flag:
        _session_pw_cache.pop(vault_id, None)
    # Record stats event
    _tid_acct = u["telegram_id"] if u else 0
    record_stat("account_disabled" if flag else "account_enabled",
                telegram_id=_tid_acct, vault_id=vault_id)
    word = "DISABLED" if flag else "ENABLED"
    note = " All active sessions cleared." if flag else ""
    resp = await q.message.reply_text(
        f"✅ Account `{vault_id}` ({u['tg_username'] or u['telegram_id']}) has been {word}.{note}"
    )
    asyncio.create_task(auto_delete_msg(resp, delay=120))
    try:
        if flag:
            await q.bot.send_message(
                chat_id=u["telegram_id"],
                text="🚫 *Your account has been disabled by an administrator\\.*\\n\\n"
                     "_Your data is safe and has not been deleted\\._",
                parse_mode="MarkdownV2",
            )
        else:
            await q.bot.send_message(
                chat_id=u["telegram_id"],
                text="✅ *Your account has been re\\-enabled\\. You can log in again\\.*",
                parse_mode="MarkdownV2",
            )
    except Exception:
        pass


async def adm_broadcast_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Entry point: admin clicked Broadcast from dashboard."""
    q = update.callback_query; await q.answer()
    chat_id = update.effective_chat.id
    _admin_import_pending[chat_id] = {"step": "adm_broadcast_wait"}
    msg = await q.message.reply_text("Send your broadcast message here.")
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_back_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    _admin_import_pending.pop(update.effective_chat.id, None)
    await q.message.reply_text(
        "👋 *Welcome to Dashboard*",
        parse_mode="MarkdownV2", reply_markup=_adm_kb(),
    )



# ── ADMIN: Donate ──────────────────────────────────────────────────────────────

async def adm_donate_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show donate admin menu with Set Donate Message button."""
    q = update.callback_query; await q.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✉️ Set Donate Message", callback_data="adm_set_donate_msg")],
        [InlineKeyboardButton("⬅️ Back",               callback_data="adm_back")],
    ])
    msg = await q.message.reply_text("💸 Donate Settings", reply_markup=kb)
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_set_donate_msg_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Ask admin to send the new donate message."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_set_donate_msg_wait"}
    msg = await q.message.reply_text("Set your Payments Message")
    asyncio.create_task(auto_delete_msg(msg, delay=120))

# ── End Donate admin handlers ──────────────────────────────────────────────────

# ── ADMIN: Check Abuse ──────────────────────────────────────

async def adm_check_abuse_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Step 1: Show 'Check User based Abuse' button."""
    q = update.callback_query; await q.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("👤 Check User based Abuse", callback_data="adm_check_user_abuse")],
        [InlineKeyboardButton("⬅️ Back", callback_data="adm_back")],
    ])
    msg = await q.message.reply_text("🔍 Check Abuse\n\nSelect an abuse check type.", reply_markup=kb)
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_check_user_abuse_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Step 2: Show 'Check User TOTP Duplicate' button."""
    q = update.callback_query; await q.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("🔁 Check User TOTP Duplicate", callback_data="adm_check_totp_dup")],
        [InlineKeyboardButton("⬅️ Back", callback_data="adm_check_abuse")],
    ])
    msg = await q.message.reply_text(
        "👤 Check User based Abuse\n\nSelect the type of user abuse check.",
        reply_markup=kb,
    )
    asyncio.create_task(auto_delete_msg(msg, delay=300))


async def adm_check_totp_dup_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Step 3: Ask for Vault ID or Telegram ID to check TOTP duplicate percentage."""
    q = update.callback_query; await q.answer()
    _admin_import_pending[update.effective_chat.id] = {"step": "adm_totp_dup_check_wait"}
    msg = await q.message.reply_text(
        "Please provide the Vault ID or Telegram ID of the user for whom you want to check "
        "the total TOTP duplicate percentage."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=120))


def _admin_full_export_key(password: str, salt: bytes) -> bytes:
    return PBKDF2HMAC(
        algorithm=hashes.SHA256(), length=32, salt=salt, iterations=310_000
    ).derive(password.encode())

def _admin_encrypt(data: bytes, password: str) -> bytes:
    salt = os.urandom(16); iv = os.urandom(12)
    ct   = AESGCM(_admin_full_export_key(password, salt)).encrypt(iv, data, None)
    return salt + iv + ct

def _admin_decrypt(payload: bytes, password: str) -> bytes:
    salt = payload[:16]; iv = payload[16:28]; ct = payload[28:]
    return AESGCM(_admin_full_export_key(password, salt)).decrypt(iv, ct, None)

def _get_user_by_username(username: str):
    """Resolve @username -> user row using stored tg_username column."""
    uname = username.lstrip("@").lower()
    with get_db() as c:
        return c.execute(
            "SELECT * FROM users WHERE LOWER(tg_username)=?", (uname,)
        ).fetchone()

def _resolve_user(raw: str):
    """Resolve vault_id, telegram_id, or @username to a user row."""
    raw = raw.strip()
    u   = get_user(raw.lower())           # vault_id
    if u: return u
    if raw.isdigit():
        with get_db() as c:
            u = c.execute("SELECT * FROM users WHERE telegram_id=?", (int(raw),)).fetchone()
        if u: return u
    if raw.startswith("@") or not raw.isdigit():
        u = _get_user_by_username(raw)
        if u: return u
    return None

def _fmt_user_info(u) -> str:
    """Build the admin /user info block. Returns plain text (not Markdown)."""
    try:
        vault_id    = u["vault_id"]
        tid         = u["telegram_id"]
        tg_name     = u["tg_name"] or "Unknown"
        try:
            tg_username = u["tg_username"] or ""
        except (KeyError, IndexError):
            tg_username = ""
        username_str = f"@{tg_username}" if tg_username else f"(no username, ID: {tid})"
        created_at  = fmt_bd_time(u["created_at"]) if u["created_at"] else "N/A"
        # Last seen: show time + how long ago for accuracy
        try:
            ls_ts = u["last_seen"]
            if ls_ts:
                ls_fmt  = fmt_bd_time(ls_ts)
                ago_sec = int(time.time()) - ls_ts
                if ago_sec < 60:
                    ago_str = "just now"
                elif ago_sec < 3600:
                    ago_str = f"{ago_sec // 60}m ago"
                elif ago_sec < 86400:
                    ago_str = f"{ago_sec // 3600}h {(ago_sec % 3600) // 60}m ago"
                else:
                    ago_str = f"{ago_sec // 86400}d ago"
                last_seen = f"{ls_fmt} ({ago_str})"
            else:
                last_seen = "Never"
        except (KeyError, TypeError):
            last_seen = "Never"
        try:
            acct_disabled = bool(u["account_disabled"])
        except (KeyError, TypeError):
            acct_disabled = False
        # Check temporary freeze (login or reset)
        now_ts = int(time.time())
        with get_db() as _fc:
            _li = _fc.execute("SELECT frozen_until FROM login_attempts WHERE vault_id=?", (vault_id,)).fetchone()
            _ri = _fc.execute("SELECT frozen_until FROM reset_attempts WHERE vault_id=?", (vault_id,)).fetchone()
        login_frozen_until  = (_li["frozen_until"]  if _li  and _li["frozen_until"]  > now_ts else 0)
        reset_frozen_until  = (_ri["frozen_until"]  if _ri  and _ri["frozen_until"]  > now_ts else 0)
        is_temp_frozen      = (login_frozen_until > 0 or reset_frozen_until > 0)
        if acct_disabled:
            status = "ID Disabled"
        elif is_temp_frozen:
            # Show which type of freeze and remaining time
            if login_frozen_until > 0:
                rem = login_frozen_until - now_ts
                h, m = rem // 3600, (rem % 3600) // 60
                status = f"ID Disabled (login freeze, {h}h {m}m remaining)"
            else:
                rem = reset_frozen_until - now_ts
                h, m = rem // 3600, (rem % 3600) // 60
                status = f"ID Disabled (reset freeze, {h}h {m}m remaining)"
        else:
            status = "Active"
        try:
            total_disabled = u["total_disabled_count"] or 0
        except (KeyError, TypeError):
            total_disabled = 0
        with get_db() as c:
            totp_cnt = c.execute(
                "SELECT COUNT(*) AS n FROM totp_accounts WHERE vault_id=?", (vault_id,)
            ).fetchone()["n"]
            br = c.execute(
                "SELECT frequency, enabled FROM backup_reminders WHERE telegram_id=?", (tid,)
            ).fetchone()
            ab = c.execute(
                "SELECT enabled, frequency FROM auto_backup_settings WHERE telegram_id=?", (tid,)
            ).fetchone()
            la = c.execute(
                "SELECT attempts FROM login_attempts WHERE vault_id=?", (vault_id,)
            ).fetchone()
            ra = c.execute(
                "SELECT attempts FROM reset_attempts WHERE vault_id=?", (vault_id,)
            ).fetchone()
            # Count secret-based duplicates: same secret_enc (before decryption we count same salt+iv pairs)
            # Fast approach: count distinct (name,issuer) pairs that share same secret_enc bytes
    

        # Backup Reminder status — default is ON/Weekly if no row exists
        if br is None:
            reminder_status = "On - Weekly (default)"
        elif br["enabled"]:
            reminder_status = f"On - {br['frequency'].capitalize()}"
        else:
            reminder_status = "Off"
        # Offline Auto Backup status
        auto_backup_status = "Off"
        if ab and ab["enabled"]:
            auto_backup_status = f"On - {ab['frequency'].capitalize()}"
        failed_login = la["attempts"] if la else 0
        failed_reset = ra["attempts"] if ra else 0
        return (
            f"Vault ID       : {vault_id}\n"
            f"Telegram       : {username_str}\n"
            f"Telegram ID    : {tid}\n"
            f"Name           : {tg_name}\n\n"
            f"Total TOTP     : {totp_cnt} Account(s)\n"

            f"Created        : {created_at}\n\n"
            f"Last Online    : {last_seen}\n\n"
            f"Account Status : {status}\n"
            f"Total Disabled : {total_disabled}\n\n"
            f"Reminder       : {reminder_status}\n"
            f"Auto Backup    : {auto_backup_status}\n\n"
            f"Failed Logins  : {failed_login}\n\n"
            f"Failed Resets  : {failed_reset}"
        )
    except Exception as e:
        logger.error(f"_fmt_user_info error: {e}")
        return f"[Error building user info: {e}]"

# ── ADMIN COMMANDS ──────────────────────────────────────────
# admin_maintenance command removed - maintenance is now controlled via
# the Dashboard button (adm_maintenance_view_cb / adm_maintenance_toggle_cb).

# admin_signup_toggle command removed - signup is now managed via Dashboard Signup Control button.

# admin_login_toggle command removed - login is now managed via Dashboard Login Control button.

async def admin_user_info(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """/user <vault_id|telegram_id|@username>"""
    if not _is_admin_msg(update):
        return
    asyncio.create_task(auto_delete_msg(update.message, delay=60))
    # In groups, Telegram appends @BotUsername to the command: "/user@BotName arg"
    # So we must strip the bot mention before extracting the argument.
    raw_text = (update.message.text or "").strip()
    # Remove the command prefix including any @mention: "/user@BotName" -> ""
    # Then grab everything after the first whitespace as the argument.
    command_part = raw_text.split()[0] if raw_text else ""   # e.g. "/user" or "/user@BotName"
    arg_part = raw_text[len(command_part):].strip()          # everything after the command
    if not arg_part:
        msg = await update.message.reply_text(
            "Usage: /user <vault_id | telegram_id | @username>"
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    try:
        u = _resolve_user(arg_part)
        if not u:
            msg = await update.message.reply_text(f"❌ User not found: {arg_part}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        info = _fmt_user_info(u)
        msg  = await update.message.reply_text(f"👤 User Info\n\n{info}")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
    except Exception as e:
        logger.error(f"admin_user_info error for '{arg_part}': {e}")
        msg = await update.message.reply_text(f"❌ Error fetching user info: {e}")
        asyncio.create_task(auto_delete_msg(msg, delay=60))

# admin_account_disable command removed - account management is via Dashboard User Account button.

# admin_broadcast command removed - broadcast is now controlled via
# the Dashboard Broadcast button (adm_broadcast_cb / admin_broadcast_recv).

# admin_export and admin_import commands removed - backup/restore is now
# managed via the Dashboard Backup button (adm_backup_cb and sub-callbacks).

# Admin pending state dict (kept here for reference by all step handlers)
# Global rate limiter: max 28 API calls per second (Telegram limit is 30, keep 2 buffer)
outbound_limiter = SlidingWindowRateLimiter(max_calls=28)
# Retry sender with rate limiting and up to 3 retries on flood/network errors
retry_sender = RateLimitedRetrySender(outbound_limiter, max_retries=3)


_admin_import_pending: dict = {}   # chat_id -> {step: str, ...}

async def admin_group_message_handler(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Unified handler for ALL non-command messages in the admin group.
    Dispatches based on _admin_import_pending step so every step works correctly
    regardless of message type (text, photo, video, document, forward, etc.).
    """
    if not _is_admin_msg(update):
        return
    chat_id = update.effective_chat.id
    state   = _admin_import_pending.get(chat_id, {})
    step    = state.get("step", "")

    # ── Broadcast: any message type ──────────────────────────────────────
    if step == "adm_broadcast_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=10))
        with get_db() as c:
            users = c.execute("SELECT telegram_id FROM users").fetchall()
        total    = len(users)
        sent     = 0
        failed   = 0
        failed_ids: list[int] = []
        progress_msg = await update.message.reply_text(
            f"📢 Broadcasting to {total} user(s)... please wait."
        )
        for row in users:
            tid = row["telegram_id"]
            try:
                await retry_sender.send(update.message.copy, chat_id=tid)
                sent += 1
            except Exception:
                failed += 1
                failed_ids.append(tid)
        try:
            await progress_msg.delete()
        except Exception:
            pass
        summary = (
            f"📢 Broadcast complete!\n\n"
            f"✅ Successfully sent: {sent}\n"
            f"❌ Failed: {failed}\n"
            f"👥 Total users: {total}"
        )
        await update.message.reply_text(summary)
        if failed_ids:
            lines_txt     = "\n".join(str(tid) for tid in failed_ids)
            header        = "Broadcast Failed - Telegram User IDs\n"
            header       += f"Total failed: {failed}\n"
            header       += "=" * 40 + "\n"
            content_bytes = (header + lines_txt + "\n").encode("utf-8")
            bio           = BytesIO(content_bytes)
            bio.name      = "broadcast_failed_ids.txt"
            await retry_sender.send(
                ctx.bot.send_document,
                chat_id=chat_id,
                document=bio,
                filename="broadcast_failed_ids.txt",
                caption=f"⚠️ {failed} user(s) could not be reached. Their Telegram IDs are listed above.",
            )
        return

    # ── Backup All: admin typed the encryption password ─────────────────
    if step == "adm_backup_pw_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if len(raw) > 150:
            msg = await update.message.reply_text(
                "Password must be 150 characters or less. Please try again."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        if not raw:
            msg = await update.message.reply_text("Password cannot be empty.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        progress = await update.message.reply_text("⏳ Creating backup, please wait...")
        _backup_tables = [
            "users",
            "totp_accounts",
            "sessions",
            "reset_otps",
            "reset_attempts",
            "login_alerts",
            "share_links",
            "login_attempts",
            "backup_reminders",
            "bot_settings",
            "auto_backup_settings",
            "daily_login_counts",
            "weekly_signup_counts",
            "vault_login_history",
            "totp_add_rate",
            "vault_custom_limits",
            "user_signup_disabled",
            "user_login_disabled",
            "otp_request_log",
            "captcha_attempts",
            "telegram_banned",
            "stats_events",
            "vault_ei_limits",
            "vault_ei_usage",
        ]
        dump = {}
        with get_db() as c:
            for tbl in _backup_tables:
                try:
                    rows = c.execute(f"SELECT * FROM {tbl}").fetchall()
                    dump[tbl] = [dict(r) for r in rows]
                except Exception as e:
                    logger.warning(f"Backup table {tbl}: {e}")
        plain   = json.dumps(dump, ensure_ascii=False, default=str).encode()
        payload = _admin_encrypt(plain, raw)
        ts_str  = datetime.datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        fname   = f"bv_backup_{ts_str}.bvadmin"
        bio     = BytesIO(payload); bio.name = fname
        try:
            await progress.delete()
        except Exception:
            pass
        await ctx.bot.send_document(
            chat_id=chat_id, document=bio, filename=fname,
            caption=(
                f"💾 Full DB Backup\n"
                f"📅 {ts_str} UTC\n"
                f"🔑 Encrypted with your provided password.\n\n"
                f"Use the Restore button to import."
            ),
        )
        return

    # ── Restore: admin sent the encrypted backup file ─────────────────────
    if step == "adm_backup_restore_file":
        if not update.message.document:
            msg = await update.message.reply_text("⚠️ Please send a .bvadmin backup file.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        asyncio.create_task(auto_delete_msg(update.message, delay=60))
        bio = BytesIO()
        f   = await update.message.document.get_file()
        await f.download_to_memory(bio)
        _admin_import_pending[chat_id] = {"step": "adm_backup_restore_pw", "payload": bio.getvalue()}
        msg = await update.message.reply_text(
            "🔒 File received. Now send the encryption password."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=120))
        return

    # ── Restore: admin typed decryption password ──────────────────────────
    if step == "adm_backup_restore_pw":
        payload = state.get("payload", b"")
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        try:
            plain = _admin_decrypt(payload, raw)
            dump  = json.loads(plain.decode())
        except Exception:
            msg = await update.message.reply_text(
                "❌ Wrong password or corrupted file. Restore cancelled."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        progress = await update.message.reply_text("⏳ Restoring data, please wait...")
        _restore_tables = [
            "users",
            "totp_accounts",
            "sessions",
            "reset_otps",
            "reset_attempts",
            "login_alerts",
            "share_links",
            "login_attempts",
            "backup_reminders",
            "bot_settings",
            "auto_backup_settings",
            "daily_login_counts",
            "weekly_signup_counts",
            "vault_login_history",
            "totp_add_rate",
            "vault_custom_limits",
            "user_signup_disabled",
            "user_login_disabled",
            "otp_request_log",
            "captcha_attempts",
            "telegram_banned",
            "stats_events",
            "vault_ei_limits",
            "vault_ei_usage",
        ]
        restored = []
        with get_db() as c:
            for tbl in _restore_tables:
                if tbl not in dump:
                    continue
                try:
                    c.execute(f"DELETE FROM {tbl}")
                    rows = dump[tbl]
                    if rows:
                        cols = ", ".join(rows[0].keys())
                        placeholders = ", ".join("?" for _ in rows[0])
                        for row in rows:
                            c.execute(
                                f"INSERT OR REPLACE INTO {tbl} ({cols}) VALUES ({placeholders})",
                                list(row.values()),
                            )
                    restored.append(tbl)
                except Exception as e:
                    logger.warning(f"Restore table {tbl}: {e}")
            c.commit()
        _load_bot_settings()
        try:
            await progress.delete()
        except Exception:
            pass
        await ctx.bot.send_message(
            chat_id=chat_id,
            text=f"✅ Restore complete. Tables restored: {', '.join(restored)}",
        )
        return

    # ── Backup Specific User: admin typed vault id or telegram id ─────────
    if step == "adm_backup_specific_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        vault_id = u["vault_id"]
        # Export user's TOTP vault same way user self-exports (password = user's current vault password)
        with get_db() as c:
            totp_rows = c.execute(
                "SELECT name, issuer, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?",
                (vault_id,)
            ).fetchall()
        if not totp_rows:
            msg = await update.message.reply_text(f"No TOTP accounts found for vault {vault_id}.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        # Use live password from RAM cache (same as auto-backup)
        live_pw = _session_pw_cache.get(vault_id)
        if not live_pw:
            msg = await update.message.reply_text(
                f"Cannot export: user {vault_id} has no active session.\n"
                "User must log in at least once for their password to be available."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=120))
            return
        progress = await update.message.reply_text("⏳ Building vault export...")
        def _build_specific_export():
            vault_key = _get_vault_key(vault_id, live_pw)
            entries = []
            for row in totp_rows:
                try:
                    secret = decrypt(row["secret_enc"], row["salt"], row["iv"], vault_key, vault_id)
                    entries.append({"name": row["name"], "issuer": row["issuer"] or "", "secret": secret})
                except Exception as e:
                    logger.error(f"Specific export decrypt {vault_id}/{row['name']}: {e}")
            plain = json.dumps({"version": 3, "vault_id": vault_id, "accounts": entries}, ensure_ascii=False).encode()
            return export_encrypt(plain, live_pw), len(entries)
        payload, exported_cnt = await asyncio.to_thread(_build_specific_export)
        try:
            await progress.delete()
        except Exception:
            pass
        ts_str = datetime.datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        fname  = f"bv_backup_{ts_str}.bvault"
        bio    = BytesIO(payload); bio.name = fname
        uname  = f"@{u['tg_username']}" if u["tg_username"] else str(u["telegram_id"])
        await ctx.bot.send_document(
            chat_id=chat_id, document=bio, filename=fname,
            caption=(
                f"👤 User Vault Export\n"
                f"Vault: {vault_id}\n"
                f"User: {uname}\n"
                f"TOTP entries: {exported_cnt}\n"
                f"🔑 Encrypted with user's current account password.\n"
                f"User can import this file with 📥 Import Vault."
            ),
        )
        return

    # ── Import: wait for .bvadmin file ───────────────────────────────────
    if step == "wait_file":
        if not update.message.document:
            msg = await update.message.reply_text("⚠️ Please send a .bvadmin file.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        asyncio.create_task(auto_delete_msg(update.message, delay=60))
        bio = BytesIO()
        f   = await update.message.document.get_file()
        await f.download_to_memory(bio)
        _admin_import_pending[chat_id] = {"step": "wait_password", "payload": bio.getvalue()}
        msg = await update.message.reply_text("🔒 File received. Now send the encryption password.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    # ── All text-only steps below ─────────────────────────────────────────
    # For non-text messages with no matching step, silently ignore
    raw = (update.message.text or "").strip()
    if not raw and step not in ("adm_broadcast_wait", "wait_file"):
        return

    if step == "adm_user_info_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
        else:
            # Run _fmt_user_info in thread so _get_vault_key (Argon2) doesn't block event loop
            info_text = await asyncio.to_thread(_fmt_user_info, u)
            msg = await update.message.reply_text(f"User Info\n\n{info_text}")
        asyncio.create_task(auto_delete_msg(msg, delay=120))
        return

    if step == "adm_account_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        vault_id = u["vault_id"]
        disabled = bool(u["account_disabled"]) if "account_disabled" in u.keys() else False
        status   = "DISABLED" if disabled else "ENABLED"
        action_label  = "✅ Enable Account"  if disabled else "🚫 Disable Account"
        action_data   = f"adm_account_enable:{vault_id}" if disabled else f"adm_account_disable:{vault_id}"
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton(action_label, callback_data=action_data)],
            [InlineKeyboardButton("⬅️ Back",    callback_data="adm_back")],
        ])
        info_text = _fmt_user_info(u)
        msg = await update.message.reply_text(
            f"🔐 User Account\n\n{info_text}\n\nCurrent status: {status}",
            reply_markup=kb,
        )
        asyncio.create_task(auto_delete_msg(msg, delay=300))
        return

    if step == "adm_uc_enable_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        vault_id = u["vault_id"]
        if not u["account_disabled"]:
            msg = await update.message.reply_text(
                f"Account {vault_id} is already enabled."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        with get_db() as c:
            c.execute("UPDATE users SET account_disabled=0 WHERE vault_id=?", (vault_id,))
            # Also clear any temporary login/reset freezes
            c.execute("UPDATE login_attempts SET frozen_until=0, attempts=0 WHERE vault_id=?", (vault_id,))
            c.execute("UPDATE reset_attempts SET frozen_until=0, attempts=0 WHERE vault_id=?", (vault_id,))
            c.commit()
        record_stat("account_enabled", telegram_id=u["telegram_id"], vault_id=vault_id)
        try:
            await ctx.bot.send_message(
                chat_id=u["telegram_id"],
                text="✅ *Your account has been re\\-enabled\\. You can log in again\\.*",
                parse_mode="MarkdownV2",
            )
        except Exception:
            pass
        msg = await update.message.reply_text(
            f"✅ Account {vault_id} ({u['tg_username'] or u['telegram_id']}) has been ENABLED."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_uc_disable_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        vault_id = u["vault_id"]
        if u["account_disabled"]:
            msg = await update.message.reply_text(
                f"Account {vault_id} is already disabled."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        with get_db() as c:
            c.execute(
                "UPDATE users SET account_disabled=1, "
                "total_disabled_count=COALESCE(total_disabled_count,0)+1 WHERE vault_id=?",
                (vault_id,)
            )
            c.execute("DELETE FROM sessions WHERE vault_id=?", (vault_id,))
            c.commit()
        _session_pw_cache.pop(vault_id, None)
        record_stat("account_disabled", telegram_id=u["telegram_id"], vault_id=vault_id)
        try:
            await ctx.bot.send_message(
                chat_id=u["telegram_id"],
                text="🚫 *Your account has been disabled by an administrator\\.*\\n\\n"
                     "_Your data is safe and has not been deleted\\._",
                parse_mode="MarkdownV2",
            )
        except Exception:
            pass
        msg = await update.message.reply_text(
            f"🚫 Account {vault_id} ({u['tg_username'] or u['telegram_id']}) has been DISABLED."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_uc_ban_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        raw_strip = raw.lstrip("@")
        tid_resolved = None
        uname_resolved = ""
        if raw.isdigit():
            tid_resolved = int(raw)
            # try to get username from users table
            with get_db() as c:
                row = c.execute(
                    "SELECT tg_username FROM users WHERE telegram_id=?", (tid_resolved,)
                ).fetchone()
            uname_resolved = row["tg_username"] if row else ""
        else:
            with get_db() as c:
                row = c.execute(
                    "SELECT telegram_id, tg_username FROM users WHERE tg_username=?", (raw_strip,)
                ).fetchone()
            if row:
                tid_resolved   = row["telegram_id"]
                uname_resolved = row["tg_username"]
        if not tid_resolved:
            msg = await update.message.reply_text(
                f"User not found: {raw}\nOnly registered users can be looked up by @username."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        if is_telegram_banned(tid_resolved):
            msg = await update.message.reply_text(
                f"Telegram ID {tid_resolved} is already banned."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_telegram_ban(tid_resolved, uname_resolved, True)
        # Notify the user
        try:
            await ctx.bot.send_message(
                chat_id=tid_resolved,
                text="🚫 Your Telegram ID has been banned from this bot."
            )
        except Exception:
            pass
        uname_str = f"@{uname_resolved}" if uname_resolved else str(tid_resolved)
        msg = await update.message.reply_text(
            f"🔨 Telegram ID {tid_resolved} ({uname_str}) has been BANNED."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_uc_unban_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        raw_strip    = raw.lstrip("@")
        tid_resolved = None
        uname_resolved = ""
        if raw.isdigit():
            tid_resolved = int(raw)
        else:
            with get_db() as c:
                row = c.execute(
                    "SELECT telegram_id, tg_username FROM users WHERE tg_username=?", (raw_strip,)
                ).fetchone()
            if row:
                tid_resolved   = row["telegram_id"]
                uname_resolved = row["tg_username"]
            else:
                # also check banned table directly
                with get_db() as c:
                    row = c.execute(
                        "SELECT telegram_id, tg_username FROM telegram_banned WHERE tg_username=?",
                        (raw_strip,)
                    ).fetchone()
                if row:
                    tid_resolved   = row["telegram_id"]
                    uname_resolved = row["tg_username"]
        if not tid_resolved:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        if not is_telegram_banned(tid_resolved):
            msg = await update.message.reply_text(
                f"Telegram ID {tid_resolved} is not currently banned."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_telegram_ban(tid_resolved, uname_resolved, False)
        uname_str = f"@{uname_resolved}" if uname_resolved else str(tid_resolved)
        msg = await update.message.reply_text(
            f"✅ Telegram ID {tid_resolved} ({uname_str}) has been UNBANNED."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_specific_login_enable_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        raw_strip    = raw.lstrip("@")
        tid_resolved = None
        if raw.isdigit():
            tid_resolved = int(raw)
        else:
            with get_db() as c:
                row = c.execute(
                    "SELECT telegram_id FROM users WHERE tg_username=?", (raw_strip,)
                ).fetchone()
            if row:
                tid_resolved = row["telegram_id"]
        if not tid_resolved:
            msg = await update.message.reply_text(
                f"User not found: {raw}\nOnly registered users can be looked up by @username."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_user_login_disabled(tid_resolved, False)
        msg = await update.message.reply_text(
            f"✅ Login enabled for Telegram ID {tid_resolved}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_specific_login_disable_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        raw_strip    = raw.lstrip("@")
        tid_resolved = None
        if raw.isdigit():
            tid_resolved = int(raw)
        else:
            with get_db() as c:
                row = c.execute(
                    "SELECT telegram_id FROM users WHERE tg_username=?", (raw_strip,)
                ).fetchone()
            if row:
                tid_resolved = row["telegram_id"]
        if not tid_resolved:
            msg = await update.message.reply_text(
                f"User not found: {raw}\nOnly registered users can be looked up by @username."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_user_login_disabled(tid_resolved, True)
        msg = await update.message.reply_text(
            f"🚫 Login disabled for Telegram ID {tid_resolved}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_specific_signup_enable_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        # Resolve by telegram_id or @username (no vault needed)
        raw_strip = raw.lstrip("@")
        tid_resolved = None
        if raw.isdigit():
            tid_resolved = int(raw)
        else:
            # Try to find by username in users table
            with get_db() as c:
                row = c.execute(
                    "SELECT telegram_id FROM users WHERE tg_username=?", (raw_strip,)
                ).fetchone()
            if row:
                tid_resolved = row["telegram_id"]
        if not tid_resolved:
            msg = await update.message.reply_text(
                f"User not found: {raw}\nOnly registered users can be looked up by @username."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_user_signup_disabled(tid_resolved, False)
        msg = await update.message.reply_text(
            f"✅ Signup enabled for Telegram ID {tid_resolved}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_specific_signup_disable_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        raw_strip = raw.lstrip("@")
        tid_resolved = None
        if raw.isdigit():
            tid_resolved = int(raw)
        else:
            with get_db() as c:
                row = c.execute(
                    "SELECT telegram_id FROM users WHERE tg_username=?", (raw_strip,)
                ).fetchone()
            if row:
                tid_resolved = row["telegram_id"]
        if not tid_resolved:
            msg = await update.message.reply_text(
                f"User not found: {raw}\nOnly registered users can be looked up by @username."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_user_signup_disabled(tid_resolved, True)
        msg = await update.message.reply_text(
            f"🚫 Signup disabled for Telegram ID {tid_resolved}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_totp_dup_check_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        vault_id = u["vault_id"]
        with get_db() as c:
            totp_rows = c.execute(
                "SELECT id, name, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?",
                (vault_id,)
            ).fetchall()
        total = len(totp_rows)
        if total == 0:
            msg = await update.message.reply_text(
                f"Vault {vault_id} has no TOTP accounts. Duplicate check: 0%."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=120))
            return
        live_pw = _session_pw_cache.get(vault_id)
        if not live_pw:
            live_pw = _oab_load_password(u["telegram_id"], vault_id)
        if not live_pw:
            msg = await update.message.reply_text(
                f"Cannot check TOTP duplicates for vault {vault_id}.\n"
                "User must log in at least once for their password to be available."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=120))
            return
        progress = await update.message.reply_text("Decrypting TOTP entries, please wait...")
        def _decrypt_and_check():
            vault_key = _get_vault_key(vault_id, live_pw)
            secret_hashes = []
            failed = 0
            for row in totp_rows:
                try:
                    plain = decrypt(row["secret_enc"], row["salt"], row["iv"], vault_key, vault_id)
                    normalized = clean_secret(plain)
                    secret_hashes.append(hashlib.sha256(normalized.encode()).hexdigest())
                except Exception:
                    failed += 1
            return secret_hashes, failed
        secret_hashes, failed = await asyncio.to_thread(_decrypt_and_check)
        try:
            await progress.delete()
        except Exception:
            pass
        decrypted_count = len(secret_hashes)
        if decrypted_count == 0:
            msg = await update.message.reply_text(
                f"Could not decrypt any TOTP entries for vault {vault_id}.\n"
                f"Total entries: {total}, Failed: {failed}"
            )
            asyncio.create_task(auto_delete_msg(msg, delay=120))
            return
        from collections import Counter
        hash_counts = Counter(secret_hashes)
        unique_secrets = len(hash_counts)
        duplicate_entries = decrypted_count - unique_secrets
        dup_percent = (duplicate_entries / decrypted_count) * 100 if decrypted_count > 0 else 0
        uname_str = f"@{u['tg_username']}" if u["tg_username"] else str(u["telegram_id"])
        result_lines = [
            f"TOTP Duplicate Report",
            f"Vault      : {vault_id}",
            f"User       : {uname_str}",
            f"",
            f"Total TOTP       : {total}",
            f"Decrypted OK     : {decrypted_count}",
            f"Unique Secrets   : {unique_secrets}",
            f"Duplicate Entries: {duplicate_entries}",
            f"",
            f"Duplicate %: {dup_percent:.1f}%",
        ]
        if failed > 0:
            result_lines.append(f"(Failed to decrypt: {failed} entries)")
        result_text = "\n".join(result_lines)
        msg = await update.message.reply_text(result_text)
        asyncio.create_task(auto_delete_msg(msg, delay=300))
        return

    if step == "adm_buc_offline_weekly_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        day_lower = raw.strip().lower()
        if day_lower not in _WEEKDAY_MAP:
            msg = await update.message.reply_text(
                "Invalid day. Please write the full English name, e.g. 'Saturday'."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        globals()["DEFAULT_OFFLINE_BACKUP_WEEKDAY"] = _WEEKDAY_MAP[day_lower]
        msg = await update.message.reply_text(
            f"✅ Weekly offline backup day set to {raw.strip().capitalize()}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_buc_offline_monthly_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or not (1 <= int(raw) <= 28):
            msg = await update.message.reply_text("Invalid date. Enter a number between 1 and 28.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        globals()["DEFAULT_OFFLINE_BACKUP_MONTHLY_DATE"] = int(raw)
        msg = await update.message.reply_text(
            f"✅ Monthly offline backup date set to {raw}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_buc_reminder_weekly_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        day_lower = raw.strip().lower()
        if day_lower not in _WEEKDAY_MAP:
            msg = await update.message.reply_text(
                "Invalid day. Please write the full English name, e.g. 'Saturday'."
            )
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        globals()["DEFAULT_REMINDER_WEEKDAY"] = _WEEKDAY_MAP[day_lower]
        msg = await update.message.reply_text(
            f"✅ Weekly reminder day set to {raw.strip().capitalize()}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_buc_reminder_monthly_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or not (1 <= int(raw) <= 28):
            msg = await update.message.reply_text("Invalid date. Enter a number between 1 and 28.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        globals()["DEFAULT_REMINDER_MONTHLY_DATE"] = int(raw)
        msg = await update.message.reply_text(
            f"✅ Monthly reminder date set to {raw}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_weekly_signup_limit_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        globals()["MAX_WEEKLY_SIGNUPS"] = int(raw)
        msg = await update.message.reply_text(
            f"✅ Weekly signup limit updated to {raw} signups/week."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_daily_login_limit_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        globals()["MAX_DAILY_LOGINS"] = int(raw)
        msg = await update.message.reply_text(
            f"✅ Daily login limit updated to {raw} logins/day."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_totp_dup_limit_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        globals()["MAX_TOTP_DUPLICATE"] = int(raw)
        msg = await update.message.reply_text(
            f"✅ TOTP duplicate limit updated to {raw}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_set_donate_msg_wait":
        _admin_import_pending.pop(chat_id, None)
        raw_text = update.message.text or ""
        entities = update.message.entities
        entities_data = [e.to_dict() for e in entities] if entities else []
        donate_json = json.dumps({"text": raw_text, "entities": entities_data})
        _save_setting("donate_message", donate_json)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        success_msg = await ctx.bot.send_message(
            chat_id=chat_id,
            text="Donate message saved successfully.",
        )
        asyncio.create_task(auto_delete_msg(success_msg, delay=10))
        return


    if step == "adm_ei_pub_exp_limit_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        _save_setting("public_export_limit", int(raw))
        msg = await update.message.reply_text(
            f"✅ Public vault daily export limit set to {raw}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_ei_pub_imp_limit_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        _save_setting("public_import_limit", int(raw))
        msg = await update.message.reply_text(
            f"✅ Public vault daily import limit set to {raw}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_ei_spec_exp_id_wait":
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        vault_id = u["vault_id"]
        cur_exp, _ = get_vault_ei_limits(vault_id)
        cur_label = cur_exp if cur_exp is not None else get_public_export_limit()
        _admin_import_pending[chat_id] = {"step": "adm_ei_spec_exp_val_wait", "vault_id": vault_id}
        msg = await update.message.reply_text(
            f"This vault currently has a limit of {cur_label} exports. "
            f"Please enter in numbers how many times you want to set it."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=120))
        return

    if step == "adm_ei_spec_exp_val_wait":
        vault_id = _admin_import_pending.get(chat_id, {}).get("vault_id")
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1 or not vault_id:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_vault_export_limit(vault_id, int(raw))
        msg = await update.message.reply_text(
            f"✅ Vault {vault_id} daily export limit set to {raw}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_ei_spec_imp_id_wait":
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        vault_id = u["vault_id"]
        _, cur_imp = get_vault_ei_limits(vault_id)
        cur_label = cur_imp if cur_imp is not None else get_public_import_limit()
        _admin_import_pending[chat_id] = {"step": "adm_ei_spec_imp_val_wait", "vault_id": vault_id}
        msg = await update.message.reply_text(
            f"This vault currently has a limit of {cur_label} imports. "
            f"Please enter in numbers how many times you want to set it."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=120))
        return

    if step == "adm_ei_spec_imp_val_wait":
        vault_id = _admin_import_pending.get(chat_id, {}).get("vault_id")
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1 or not vault_id:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_vault_import_limit(vault_id, int(raw))
        msg = await update.message.reply_text(
            f"✅ Vault {vault_id} daily import limit set to {raw}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return


    if step == "adm_vault_limit_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        globals()["MAX_TOTP_PER_VAULT"] = int(raw)
        with get_db() as _c:
            custom_count = _c.execute(
                "SELECT COUNT(*) AS n FROM vault_custom_limits WHERE max_per_vault IS NOT NULL"
            ).fetchone()["n"]
        note = f" ({custom_count} vault(s) with custom limit are not affected.)" if custom_count else ""
        msg = await update.message.reply_text(
            f"Global vault max TOTP limit updated to {raw} per vault.{note}"
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_min_limit_wait":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        globals()["MAX_TOTP_PER_MINUTE"] = int(raw)
        with get_db() as _c:
            custom_count = _c.execute(
                "SELECT COUNT(*) AS n FROM vault_custom_limits WHERE max_per_min IS NOT NULL"
            ).fetchone()["n"]
        note = f" ({custom_count} vault(s) with custom per-minute limit are not affected.)" if custom_count else ""
        msg = await update.message.reply_text(
            f"Global per-minute TOTP limit updated to {raw} per vault/min.{note}"
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_specific_vault_max_id":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        vault_id  = u["vault_id"]
        cur_limit = get_effective_vault_max(vault_id)
        _admin_import_pending[chat_id] = {"step": "adm_specific_vault_max_wait", "vault_id": vault_id}
        msg = await update.message.reply_text(
            f"Set Maximum TOTP Limit for This Vault\n\n"
            f"Current default: {cur_limit} TOTP entries for this Vault.\n\n"
            f"To update the limit, enter a new number. This will be the maximum "
            f"TOTP entries allowed for this user."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=120))
        return

    if step == "adm_specific_vault_max_wait":
        vault_id = state.get("vault_id", "")
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_vault_max_limit(vault_id, int(raw))
        msg = await update.message.reply_text(
            f"Custom vault max limit set to {raw} TOTP entries for vault {vault_id}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step == "adm_specific_vault_min_id":
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        u = _resolve_user(raw)
        if not u:
            msg = await update.message.reply_text(f"User not found: {raw}")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        vault_id  = u["vault_id"]
        cur_limit = get_effective_per_min_limit(vault_id)
        _admin_import_pending[chat_id] = {"step": "adm_specific_vault_min_wait", "vault_id": vault_id}
        msg = await update.message.reply_text(
            f"Set Maximum Per minute TOTP Limit for This Vault\n\n"
            f"Current default: {cur_limit} TOTP/Min entries for this Vault.\n\n"
            f"To update the limit, enter a new number. This will be the maximum "
            f"per minute TOTP entries allowed for this user."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=120))
        return

    if step == "adm_specific_vault_min_wait":
        vault_id = state.get("vault_id", "")
        _admin_import_pending.pop(chat_id, None)
        asyncio.create_task(auto_delete_msg(update.message, delay=5))
        if not raw.isdigit() or int(raw) < 1:
            msg = await update.message.reply_text("Invalid. Send a positive integer.")
            asyncio.create_task(auto_delete_msg(msg, delay=60))
            return
        set_vault_per_min_limit(vault_id, int(raw))
        msg = await update.message.reply_text(
            f"Custom per-minute limit set to {raw} TOTP/min for vault {vault_id}."
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return

    if step != "wait_password":
        return
    password = raw
    try:
        await update.message.delete()
    except Exception:
        pass
    payload = state.get("payload", b"")
    try:
        plain = _admin_decrypt(payload, password)
        dump  = json.loads(plain.decode())
    except Exception:
        await ctx.bot.send_message(chat_id=chat_id, text="❌ Wrong password or corrupted file.")
        _admin_import_pending.pop(chat_id, None)
        return
    _admin_import_pending.pop(chat_id, None)
    tables = [
        "users",
        "totp_accounts",
        "sessions",
        "reset_otps",
        "reset_attempts",
        "login_alerts",
        "share_links",
        "login_attempts",
        "backup_reminders",
        "bot_settings",
        "auto_backup_settings",
        "daily_login_counts",
        "weekly_signup_counts",
        "vault_login_history",
        "totp_add_rate",
        "vault_custom_limits",
        "user_signup_disabled",
        "user_login_disabled",
        "otp_request_log",
        "captcha_attempts",
        "telegram_banned",
        "stats_events",
        "vault_ei_limits",
        "vault_ei_usage",
    ]
    with get_db() as c:
        for tbl in tables:
            if tbl not in dump:
                continue
            try:
                c.execute(f"DELETE FROM {tbl}")
                rows = dump[tbl]
                if rows:
                    cols = ", ".join(rows[0].keys())
                    placeholders = ", ".join("?" for _ in rows[0])
                    for row in rows:
                        c.execute(
                            f"INSERT OR REPLACE INTO {tbl} ({cols}) VALUES ({placeholders})",
                            list(row.values()),
                        )
            except Exception as e:
                logger.warning(f"Admin import table {tbl}: {e}")
        c.commit()
    _load_bot_settings()
    await ctx.bot.send_message(
        chat_id=chat_id,
        text=f"✅ Import complete. Tables restored: {', '.join(tables)}",
    )

async def admin_userall_export(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """/userall -- send a .txt file listing all users with @username."""
    if not _is_admin_msg(update):
        return
    asyncio.create_task(auto_delete_msg(update.message, delay=60))
    with get_db() as c:
        rows = c.execute(
            "SELECT u.telegram_id, u.tg_name, u.tg_username, u.vault_id, u.account_disabled, "
            "COUNT(t.id) AS totp_cnt "
            "FROM users u LEFT JOIN totp_accounts t ON u.vault_id=t.vault_id "
            "GROUP BY u.vault_id ORDER BY u.created_at",
        ).fetchall()
    if not rows:
        msg = await update.message.reply_text("No users found.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    lines = []
    for i, r in enumerate(rows, 1):
        uname  = f"@{r['tg_username']}" if r["tg_username"] else f"(ID:{r['telegram_id']})"
        status = "DISABLED" if r["account_disabled"] else "Active"
        lines.append(
            f"{i} | {uname} | {r['vault_id']} | {r['totp_cnt']} TOTP | {status}"
        )
    content = "\n".join(lines)
    ts_str  = datetime.datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    fname   = f"bv_users_{ts_str}.txt"
    bio     = BytesIO(content.encode())
    bio.name = fname
    await update.message.reply_document(
        document=bio,
        filename=fname,
        caption=f"👥 All Users Export -- {len(rows)} total\n📅 {ts_str}",
    )

# ── OFFLINE AUTO BACKUP ────────────────────────────────────
async def offline_auto_backup_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show Offline Auto Backup settings page."""
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    with get_db() as c:
        row = c.execute(
            "SELECT enabled, frequency FROM auto_backup_settings WHERE telegram_id=?", (uid,)
        ).fetchone()
    enabled = bool(row["enabled"]) if row else False
    freq    = row["frequency"] if row else "weekly"
    status_icon = "🟢 ON" if enabled else "🔴 OFF"
    freq_lbl    = "📅 Weekly \\(Every Saturday, 20:00 BDT\\)" if freq == "weekly" \
                  else "📆 Monthly \\(1st Sunday, 18:00 BDT\\)"
    toggle_lbl  = "🔕 Turn OFF" if enabled else "🔔 Turn ON"
    switch_lbl  = "📆 Switch to Monthly" if freq == "weekly" else "📅 Switch to Weekly"
    await q.edit_message_text(
        "💾 *Offline Auto Backup*\n\n"
        f"Status: *{status_icon}*\n"
        f"Schedule: {freq_lbl}\n\n"
        "When enabled, your vault is automatically exported and sent to you as an encrypted "
        "*\\.bvault* file\\.\n\n"
        "🔑 The file is encrypted with *your current account password*\\.\n"
        "🗑 The backup message auto\\-deletes *3 days* after being sent\\.\n\n"
        "_Default: OFF_",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton(toggle_lbl, callback_data="oab_toggle")],
            [InlineKeyboardButton(switch_lbl, callback_data="oab_freq")],
            [InlineKeyboardButton("⬅️ Back", callback_data="settings_backup")],
            [InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")],
        ]),
    )
    return TOTP_MENU

async def oab_toggle(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Toggle offline auto-backup on/off."""
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    with get_db() as c:
        row = c.execute(
            "SELECT enabled FROM auto_backup_settings WHERE telegram_id=?", (uid,)
        ).fetchone()
        new_enabled = 0 if (row and row["enabled"]) else 1
        c.execute(
            "INSERT INTO auto_backup_settings (telegram_id, enabled) VALUES (?,?) "
            "ON CONFLICT(telegram_id) DO UPDATE SET enabled=excluded.enabled",
            (uid, new_enabled),
        )
        c.commit()
    # When enabling, immediately store the current password so backup works from this session
    if new_enabled == 1:
        pw    = ctx.user_data.get("password")
        vault = get_session(uid)
        if pw and vault:
            _oab_store_password(uid, vault, pw)
    return await offline_auto_backup_menu(update, ctx)

async def oab_freq(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Switch auto-backup frequency between weekly and monthly."""
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    with get_db() as c:
        row = c.execute(
            "SELECT frequency FROM auto_backup_settings WHERE telegram_id=?", (uid,)
        ).fetchone()
        cur     = row["frequency"] if row else "weekly"
        new_frq = "monthly" if cur == "weekly" else "weekly"
        c.execute(
            "INSERT INTO auto_backup_settings (telegram_id, frequency) VALUES (?,?) "
            "ON CONFLICT(telegram_id) DO UPDATE SET frequency=excluded.frequency",
            (uid, new_frq),
        )
        c.commit()
    return await offline_auto_backup_menu(update, ctx)


async def run_auto_backup_for_user(bot, tid: int, vault_id: str, freq_label: str):
    """
    Build and send an encrypted .bvault backup to a user's Telegram chat.
    Password is loaded from DB (encrypted). Falls back to RAM cache if DB not yet populated.
    """
    try:
        # Load password: prefer RAM cache (fresher), fall back to DB store
        live_pw = _session_pw_cache.get(vault_id) or _oab_load_password(tid, vault_id)

        if not live_pw:
            # Password not available at all — user never logged in after feature was added
            try:
                import zoneinfo
                bd_now = datetime.datetime.now(tz=zoneinfo.ZoneInfo(BD_TZ))
            except Exception:
                bd_now = datetime.datetime.utcnow() + datetime.timedelta(hours=6)
            bd_str = bd_now.strftime("%d %b %Y, %I:%M %p (BDT)")
            await retry_sender.send(
                bot.send_message,
                chat_id=tid,
                text=(
                    "💾 *Auto Backup \\— Action Required*\n\n"
                    f"📅 _{em(bd_str)}_\n\n"
                    "Your scheduled auto\\-backup could not run\\.\n\n"
                    "Please /start the bot, log in once, and your backup will work "
                    "automatically from the next scheduled window\\."
                ),
                parse_mode="MarkdownV2",
            )
            # Mark as attempted so we don't spam every hour
            col = "last_weekly" if freq_label == "weekly" else "last_monthly"
            with get_db() as c:
                c.execute(
                    f"INSERT INTO auto_backup_settings (telegram_id, {col}) VALUES (?,?) "
                    f"ON CONFLICT(telegram_id) DO UPDATE SET {col}=excluded.{col}",
                    (tid, int(time.time())),
                )
                c.commit()
            return

        with get_db() as c:
            totp_rows = c.execute(
                "SELECT name, issuer, secret_enc, salt, iv, note, account_type, hotp_counter "
                "FROM totp_accounts WHERE vault_id=?",
                (vault_id,)
            ).fetchall()

        if not totp_rows:
            logger.info(f"Auto-backup: no TOTP accounts for vault {vault_id}, skipping.")
            return

        entries = []
        for row in totp_rows:
            try:
                secret = decrypt(row["secret_enc"], row["salt"], row["iv"], live_pw, vault_id)
                entries.append({
                    "name":         row["name"],
                    "issuer":       row["issuer"] or "",
                    "secret":       secret,
                    "note":         row["note"] or "",
                    "account_type": row["account_type"] or "totp",
                    "hotp_counter": row["hotp_counter"] or 0,
                })
            except Exception as e:
                logger.error(f"Auto-backup decrypt error for {vault_id}/{row['name']}: {e}")

        if not entries:
            logger.warning(f"Auto-backup: all decrypt failed for vault {vault_id} — password may have changed")
            # Password mismatch means user changed password without triggering a new store.
            # Clear the stale DB password so next login re-stores the correct one.
            with get_db() as c:
                c.execute(
                    "UPDATE auto_backup_settings SET pw_enc=NULL, pw_salt=NULL, pw_iv=NULL "
                    "WHERE telegram_id=?", (tid,)
                )
                c.commit()
            return

        plain = json.dumps({
            "version":     3,
            "vault_id":    vault_id,
            "accounts":    entries,
            "backup_type": "auto",
        }, ensure_ascii=False).encode()

        payload = await asyncio.to_thread(export_encrypt, plain, live_pw)

        try:
            import zoneinfo
            bd_now = datetime.datetime.now(tz=zoneinfo.ZoneInfo(BD_TZ))
        except Exception:
            bd_now = datetime.datetime.utcnow() + datetime.timedelta(hours=6)
        bd_str   = bd_now.strftime("%d %b %Y, %I:%M %p (BDT)")
        ts_str   = datetime.datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        filename = f"bv_autobackup_{freq_label}_{ts_str}.bvault"
        bio      = BytesIO(payload)
        bio.name = filename

        AUTO_DELETE_SECONDS = 3 * 24 * 3600   # 3 days

        msg = await retry_sender.send(
            bot.send_document,
            chat_id=tid,
            document=bio,
            filename=filename,
            caption=(
                f"💾 *BV Auto Backup \\— {em(freq_label.capitalize())}*\n"
                f"📅 _{em(bd_str)}_\n\n"
                f"Vault: `{em(vault_id)}`\n"
                f"Accounts backed up: *{len(entries)}*\n\n"
                "🔑 *Encrypted with your current account password\\.*\n"
                "Use 📥 Import Vault to restore\\.\n\n"
                "_This message auto\\-deletes in 3 days\\._"
            ),
            parse_mode="MarkdownV2",
        )

        # Schedule auto-delete after 3 days
        async def _auto_delete_backup():
            await asyncio.sleep(AUTO_DELETE_SECONDS)
            try:
                await msg.delete()
            except Exception:
                pass
        asyncio.create_task(_auto_delete_backup())

        # Update last sent timestamp
        col = "last_weekly" if freq_label == "weekly" else "last_monthly"
        with get_db() as c:
            c.execute(
                f"INSERT INTO auto_backup_settings (telegram_id, {col}) VALUES (?,?) "
                f"ON CONFLICT(telegram_id) DO UPDATE SET {col}=excluded.{col}",
                (tid, int(time.time())),
            )
            c.commit()
        logger.info(f"Auto-backup sent to {tid} (vault {vault_id}, {freq_label})")

    except Exception as e:
        logger.error(f"Auto-backup failed for {tid}: {e}")


async def send_auto_backups(app):
    """
    Job callback: check who needs a weekly or monthly auto-backup and send it.
    Weekly:  Every Saturday, BD time 20:00
    Monthly: DEFAULT_OFFLINE_BACKUP_MONTHLY_DATE (default 1st) of month, BD time 20:00
    Runs every 5 minutes; checks if current BDT time is within the target window.
    """
    try:
        import zoneinfo
        now_bd = datetime.datetime.now(tz=zoneinfo.ZoneInfo(BD_TZ))
    except Exception:
        now_bd = datetime.datetime.utcnow() + datetime.timedelta(hours=6)

    weekday = now_bd.weekday()   # Monday=0, Saturday=5, Sunday=6
    hour    = now_bd.hour
    minute  = now_bd.minute
    day     = now_bd.day

    # Weekly window: admin-configured day at 20:00 BDT
    is_weekly_window  = (weekday == DEFAULT_OFFLINE_BACKUP_WEEKDAY and hour == 20 and minute < 10)
    # Monthly window: admin-configured date at 20:00 BDT
    is_monthly_window = (day == DEFAULT_OFFLINE_BACKUP_MONTHLY_DATE and hour == 20 and minute < 10)

    if not is_weekly_window and not is_monthly_window:
        return

    now_ts = int(time.time())
    with get_db() as c:
        rows = c.execute(
            "SELECT telegram_id, frequency, last_weekly, last_monthly "
            "FROM auto_backup_settings WHERE enabled=1"
        ).fetchall()

    for row in rows:
        owner_tid = row["telegram_id"]
        freq      = row["frequency"]
        with get_db() as c:
            u = c.execute("SELECT vault_id FROM users WHERE telegram_id=?", (owner_tid,)).fetchone()
        if not u:
            continue
        vault_id = u["vault_id"]
        # Always send to vault owner (owner_tid). The file is encrypted with the owner's
        # password, so only they can open it. Sending to a random active session risks
        # delivering to a device the owner may no longer use.
        tid = owner_tid

        if is_weekly_window and freq == "weekly":
            if now_ts - (row["last_weekly"] or 0) < 6 * 24 * 3600:
                continue
            asyncio.create_task(run_auto_backup_for_user(app.bot, tid, vault_id, "weekly"))

        elif is_monthly_window and freq == "monthly":
            if now_ts - (row["last_monthly"] or 0) < 25 * 24 * 3600:
                continue
            asyncio.create_task(run_auto_backup_for_user(app.bot, tid, vault_id, "monthly"))


# ── BACKUP REMINDER ─────────────────────────────────────────
async def backup_reminder_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Show backup reminder settings from Settings menu."""
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    with get_db() as c:
        row = c.execute(
            "SELECT frequency, enabled FROM backup_reminders WHERE telegram_id=?", (uid,)
        ).fetchone()
    freq    = row["frequency"] if row else BACKUP_REMINDER_WEEKLY
    enabled = bool(row["enabled"]) if row else True
    status  = "🟢 Enabled" if enabled else "🔴 Disabled"
    freq_lbl = "📅 Weekly" if freq == BACKUP_REMINDER_WEEKLY else "📆 Monthly"
    await q.edit_message_text(
        f"🔔 *Backup Reminder*\n\n"
        f"Status: {em(status)}\n"
        f"Frequency: {em(freq_lbl)}\n\n"
        "_Regular backups protect your TOTP data\\._",
        parse_mode="MarkdownV2",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton(
                "🔕 Disable" if enabled else "🔔 Enable",
                callback_data="backup_rem_toggle",
            )],
            [InlineKeyboardButton(
                "📆 Switch to Monthly" if freq == BACKUP_REMINDER_WEEKLY else "📅 Switch to Weekly",
                callback_data="backup_rem_freq",
            )],
            [InlineKeyboardButton("⬅️ Back", callback_data="settings_backup")],
        ]),
    )
    return TOTP_MENU

async def backup_rem_toggle(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    with get_db() as c:
        row = c.execute("SELECT enabled FROM backup_reminders WHERE telegram_id=?", (uid,)).fetchone()
        # Default is enabled=1 (on). If no row, current state is ON, so toggling means OFF.
        current = bool(row["enabled"]) if row else True
        new_enabled = 0 if current else 1
        c.execute(
            "INSERT INTO backup_reminders (telegram_id, enabled) VALUES (?,?) "
            "ON CONFLICT(telegram_id) DO UPDATE SET enabled=excluded.enabled",
            (uid, new_enabled),
        )
        c.commit()
    return await backup_reminder_menu(update, ctx)

async def backup_rem_freq(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
    with get_db() as c:
        row     = c.execute("SELECT frequency FROM backup_reminders WHERE telegram_id=?", (uid,)).fetchone()
        cur     = row["frequency"] if row else BACKUP_REMINDER_WEEKLY
        new_frq = BACKUP_REMINDER_MONTHLY if cur == BACKUP_REMINDER_WEEKLY else BACKUP_REMINDER_WEEKLY
        c.execute(
            "INSERT INTO backup_reminders (telegram_id, frequency) VALUES (?,?) "
            "ON CONFLICT(telegram_id) DO UPDATE SET frequency=excluded.frequency",
            (uid, new_frq),
        )
        c.commit()
    return await backup_reminder_menu(update, ctx)

async def send_backup_reminders(app):
    """
    Job callback: send backup reminders to users who are due.
    Runs every 5 minutes. Fires on admin-configured day/date at 20:00 BDT.
    Only sends to users with reminders enabled.
    """
    try:
        now_bd = _dt.datetime.now(_BDT)
    except Exception:
        now_bd = _dt.datetime.utcnow() + _dt.timedelta(hours=6)

    weekday = now_bd.weekday()
    hour    = now_bd.hour
    minute  = now_bd.minute
    day     = now_bd.day

    # Weekly window: admin-configured day at 20:00 BDT
    is_weekly_window  = (weekday == DEFAULT_REMINDER_WEEKDAY and hour == 20 and minute < 10)
    # Monthly window: admin-configured date at 20:00 BDT
    is_monthly_window = (day == DEFAULT_REMINDER_MONTHLY_DATE and hour == 20 and minute < 10)

    if not is_weekly_window and not is_monthly_window:
        return

    now_ts = int(time.time())
    with get_db() as c:
        rows = c.execute("""
            SELECT u.telegram_id,
                   COALESCE(br.frequency, 'weekly')  AS frequency,
                   COALESCE(br.enabled,  1)           AS enabled,
                   COALESCE(br.last_sent, 0)          AS last_sent
            FROM users u
            LEFT JOIN backup_reminders br ON br.telegram_id = u.telegram_id
        """).fetchall()

    for row in rows:
        if not row["enabled"]:
            continue
        freq = row["frequency"]
        # Only fire on the matching window
        if freq == BACKUP_REMINDER_WEEKLY and not is_weekly_window:
            continue
        if freq == BACKUP_REMINDER_MONTHLY and not is_monthly_window:
            continue
        # Don't double-send within 6 hours
        if now_ts - (row["last_sent"] or 0) < 6 * 3600:
            continue
        tid = row["telegram_id"]
        try:
            await retry_sender.send(
                app.bot.send_message,
                chat_id=tid,
                text=(
                    "🔔 *Backup Reminder*\n\n"
                    "It's time to export your vault backup\\!\n\n"
                    "Go to ⚙️ Settings → 📤 Export Vault\\.\n"
                    "_Regular backups keep your TOTP data safe\\._"
                ),
                parse_mode="MarkdownV2",
            )
            with get_db() as c:
                c.execute(
                    "INSERT INTO backup_reminders (telegram_id, last_sent) VALUES (?,?) "
                    "ON CONFLICT(telegram_id) DO UPDATE SET last_sent=excluded.last_sent",
                    (tid, now_ts),
                )
                c.commit()
        except Exception as e:
            logger.warning(f"Backup reminder failed for {tid}: {e}")

async def cancel_to_menu(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    for k in [
        "pending_name", "signup_pw", "new_pw", "edit_id", "edit_name",
        "pending_secret", "_global_add", "reset_vid", "sreset_pw",
        "import_payload", "delete_vault", "delete_owner",
        "reset_secure_key", "reset_sk_skipped", "reset_new_pw", "reset_otp_verified",
        "share_selected", "share_rows",
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
    uid = update.effective_user.id
    update_last_seen(uid)
    await q.edit_message_text("Choose an option:", reply_markup=kb_main())
    return TOTP_MENU

# ── MAIN ────────────────────────────────────────────────────
def main():
    if not SERVER_KEY:
        raise RuntimeError("ENCRYPTION_KEY environment variable is not set")
    init_db()
    purge_expired_share_links()
    token   = os.environ["BOT_TOKEN"]
    app = (
        ApplicationBuilder()
        .token(token)
        # Allow multiple updates to be processed concurrently (different users don't block each other)
        .concurrent_updates(True)
        # More worker threads for concurrent handler execution
        .pool_timeout(30.0)
        .connect_timeout(30.0)
        .read_timeout(30.0)
        .write_timeout(30.0)
        .build()
    )
    private = filters.ChatType.PRIVATE
    group   = filters.ChatType.GROUPS

    conv = ConversationHandler(
        entry_points=[CommandHandler("start", start, filters=private)],
        states={
            AUTH_MENU: [
                CallbackQueryHandler(signup_start,  pattern="^auth_signup$"),
                CallbackQueryHandler(login_start,   pattern="^auth_login$"),
            ],
            SIGNUP_TERMS: [
                CallbackQueryHandler(signup_terms_agreed,  pattern="^signup_agree$"),
                CallbackQueryHandler(signup_terms_declined, pattern="^signup_decline$"),
            ],
            CAPTCHA_VERIFY: [
                CallbackQueryHandler(captcha_check,        pattern="^captcha_"),
                CallbackQueryHandler(signup_back_to_terms, pattern="^signup_back_to_terms$"),
            ],
            SIGNUP_PASSWORD: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, signup_pw),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            SIGNUP_CONFIRM: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, signup_confirm),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            LOGIN_CAPTCHA: [
                CallbackQueryHandler(login_captcha_check, pattern="^login_captcha_"),
                CallbackQueryHandler(cancel_to_menu,      pattern="^cancel_to_menu$"),
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
                CallbackQueryHandler(add_totp_start,        pattern="^add_totp$"),
                CallbackQueryHandler(list_totp,             pattern="^list_totp$"),
                CallbackQueryHandler(list_page_cb,          pattern=r"^list_page_\d+$"),
                CallbackQueryHandler(list_page_cb,          pattern="^list_noop$"),
                CallbackQueryHandler(search_totp_open,      pattern="^search_totp_open$"),
                CallbackQueryHandler(edit_totp_start,       pattern="^edit_totp$"),
                CallbackQueryHandler(show_profile,          pattern="^profile$"),
                CallbackQueryHandler(settings_menu,           pattern="^settings$"),
                CallbackQueryHandler(settings_security_menu,  pattern="^settings_security$"),
                CallbackQueryHandler(settings_backup_menu,    pattern="^settings_backup$"),
                CallbackQueryHandler(settings_account_menu,   pattern="^settings_account$"),
                CallbackQueryHandler(change_pw_start,       pattern="^change_pw$"),
                CallbackQueryHandler(settings_reset_start,  pattern="^settings_reset_pw$"),
                CallbackQueryHandler(view_secure_key_start, pattern="^view_secure_key$"),
                CallbackQueryHandler(export_vault_start,    pattern="^export_vault$"),
                CallbackQueryHandler(import_vault_start,    pattern="^import_vault$"),
                CallbackQueryHandler(delete_account_start,  pattern="^delete_account$"),
                CallbackQueryHandler(logout,                pattern="^logout$"),
                CallbackQueryHandler(main_menu_cb,          pattern="^main_menu$"),
                CallbackQueryHandler(show_donate,           pattern="^donate$"),
                CallbackQueryHandler(share_pg_cb,           pattern=r"^share_pg_\d+$"),
                CallbackQueryHandler(edit_pg_cb,            pattern=r"^edit_pg_\d+$"),
                CallbackQueryHandler(change_tz_start,       pattern="^change_tz$"),
                CallbackQueryHandler(edit_pick,             pattern=r"^editpick_\d+$"),
                CallbackQueryHandler(edit_action,           pattern=r"^edit_action_(rename|delete|showsecret|note)$"),
                CallbackQueryHandler(edit_delete_confirm,   pattern="^edit_action_delete_confirm$"),
                CallbackQueryHandler(global_add_cancel,     pattern="^global_add_cancel$"),
                # Backup reminder
                CallbackQueryHandler(backup_reminder_menu,    pattern="^backup_reminder$"),
                CallbackQueryHandler(backup_rem_toggle,       pattern="^backup_rem_toggle$"),
                CallbackQueryHandler(backup_rem_freq,         pattern="^backup_rem_freq$"),
                # Offline Auto Backup
                CallbackQueryHandler(offline_auto_backup_menu, pattern="^offline_auto_backup$"),
                CallbackQueryHandler(oab_toggle,               pattern="^oab_toggle$"),
                CallbackQueryHandler(oab_freq,                 pattern="^oab_freq$"),
                # Import override
                CallbackQueryHandler(import_override_cb,    pattern="^import_mode_(skip|replace)$"),
                # Share Codes
                CallbackQueryHandler(share_codes_open,      pattern="^share_codes_open$"),
                CallbackQueryHandler(share_toggle,          pattern=r"^share_toggle_\d+$"),
                CallbackQueryHandler(share_generate,        pattern="^share_generate$"),
            CallbackQueryHandler(share_limit_warn,      pattern="^share_limit_warn$"),
                CallbackQueryHandler(share_cancel,          pattern="^share_cancel$"),
                CallbackQueryHandler(share_select_all,     pattern="^share_select_all$"),
                CallbackQueryHandler(share_unselect_all,   pattern="^share_unselect_all$"),
            ],
            SEARCH_TOTP_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, search_totp_input),
                CallbackQueryHandler(cancel_to_menu,    pattern="^cancel_to_menu$"),
                CallbackQueryHandler(search_totp_open,  pattern="^search_totp_open$"),
            ],
            ADD_WAITING: [
                MessageHandler(private & (filters.PHOTO | filters.Document.IMAGE), handle_add_input),
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, handle_add_input),
                CallbackQueryHandler(main_menu_cb,   pattern="^main_menu$"),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            ADD_MANUAL_NAME: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, handle_manual_name),
                CallbackQueryHandler(add_totp_start,  pattern="^add_totp$"),
                CallbackQueryHandler(cancel_to_menu,  pattern="^cancel_to_menu$"),
            ],
            ADD_MANUAL_SECRET: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, handle_manual_secret),
                CallbackQueryHandler(add_totp_start,  pattern="^add_totp$"),
                CallbackQueryHandler(cancel_to_menu,  pattern="^cancel_to_menu$"),
            ],
            EDIT_PICK: [
                CallbackQueryHandler(edit_pick,    pattern=r"^editpick_\d+$"),
                CallbackQueryHandler(edit_pg_cb,   pattern=r"^edit_pg_\d+$"),
                CallbackQueryHandler(list_page_cb, pattern="^list_noop$"),
                CallbackQueryHandler(main_menu_cb, pattern="^main_menu$"),
            ],
            EDIT_ACTION: [
                CallbackQueryHandler(edit_action,         pattern=r"^edit_action_(rename|delete|showsecret|note)$"),
                CallbackQueryHandler(edit_delete_confirm, pattern="^edit_action_delete_confirm$"),
                CallbackQueryHandler(edit_totp_start,     pattern="^edit_totp$"),
            ],
            EDIT_RENAME_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, edit_rename_input),
                CallbackQueryHandler(edit_totp_start, pattern="^edit_totp$"),
                CallbackQueryHandler(cancel_to_menu,  pattern="^cancel_to_menu$"),
            ],
            NOTE_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, note_input),
                CallbackQueryHandler(edit_totp_start, pattern="^edit_totp$"),
                CallbackQueryHandler(cancel_to_menu,  pattern="^cancel_to_menu$"),
            ],
            SHOW_SECRET_PW: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, show_secret_pw),
                CallbackQueryHandler(edit_totp_start,  pattern="^edit_totp$"),
                CallbackQueryHandler(cancel_to_menu,   pattern="^cancel_to_menu$"),
            ],
            CHANGE_PW_OLD: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, change_pw_old),
                CallbackQueryHandler(settings_security_menu, pattern="^settings_security$"),
                CallbackQueryHandler(cancel_to_menu,         pattern="^cancel_to_menu$"),
            ],
            CHANGE_PW_NEW: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, change_pw_new),
                CallbackQueryHandler(settings_security_menu, pattern="^settings_security$"),
                CallbackQueryHandler(cancel_to_menu,         pattern="^cancel_to_menu$"),
            ],
            CHANGE_PW_CONFIRM: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, change_pw_confirm),
                CallbackQueryHandler(settings_security_menu, pattern="^settings_security$"),
                CallbackQueryHandler(cancel_to_menu,         pattern="^cancel_to_menu$"),
            ],
            SETTINGS_RESET_OTP: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, settings_reset_otp),
                CallbackQueryHandler(settings_security_menu, pattern="^settings_security$"),
                CallbackQueryHandler(cancel_to_menu,         pattern="^cancel_to_menu$"),
            ],
            SETTINGS_RESET_PW: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, settings_reset_pw_input),
                CallbackQueryHandler(settings_security_menu, pattern="^settings_security$"),
                CallbackQueryHandler(cancel_to_menu,         pattern="^cancel_to_menu$"),
            ],
            SETTINGS_RESET_PW_CONFIRM: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, settings_reset_pw_confirm),
                CallbackQueryHandler(settings_security_menu, pattern="^settings_security$"),
                CallbackQueryHandler(cancel_to_menu,         pattern="^cancel_to_menu$"),
            ],
            DELETE_ACCOUNT_PASSWORD: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, delete_account_password),
                CallbackQueryHandler(settings_account_menu, pattern="^settings_account$"),
                CallbackQueryHandler(cancel_to_menu,        pattern="^cancel_to_menu$"),
            ],
            DELETE_ACCOUNT_CONFIRM: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, delete_account_confirm),
                CallbackQueryHandler(settings_account_menu, pattern="^settings_account$"),
                CallbackQueryHandler(main_menu_cb,          pattern="^main_menu$"),
                CallbackQueryHandler(cancel_to_menu,        pattern="^cancel_to_menu$"),
            ],
            EXPORT_PW1_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, export_pw1_input),
                CallbackQueryHandler(settings_backup_menu, pattern="^settings_backup$"),
                CallbackQueryHandler(cancel_to_menu,       pattern="^cancel_to_menu$"),
            ],
            EXPORT_PW2_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, export_pw2_input),
                CallbackQueryHandler(settings_backup_menu, pattern="^settings_backup$"),
                CallbackQueryHandler(cancel_to_menu,       pattern="^cancel_to_menu$"),
            ],
            IMPORT_FILE_WAIT: [
                MessageHandler(private & filters.Document.ALL, import_file_recv),
                CallbackQueryHandler(settings_backup_menu, pattern="^settings_backup$"),
                CallbackQueryHandler(cancel_to_menu,       pattern="^cancel_to_menu$"),
            ],
            IMPORT_PW_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, import_pw_input),
                CallbackQueryHandler(settings_backup_menu, pattern="^settings_backup$"),
                CallbackQueryHandler(cancel_to_menu,       pattern="^cancel_to_menu$"),
            ],
            IMPORT_OVERRIDE_WAIT: [
                CallbackQueryHandler(import_override_cb, pattern="^import_mode_(skip|replace)$"),
                CallbackQueryHandler(cancel_to_menu,     pattern="^cancel_to_menu$"),
            ],
            TZ_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, change_tz_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            SECURE_KEY_VIEW_PW: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, view_secure_key_pw),
                CallbackQueryHandler(settings_security_menu, pattern="^settings_security$"),
                CallbackQueryHandler(cancel_to_menu,         pattern="^cancel_to_menu$"),
            ],
        },
        fallbacks=[CommandHandler("start", start, filters=private)],
        allow_reentry=True,
        per_chat=True,
    )

    # ── User (private) handlers ────────────────────────────────
    app.add_handler(conv)
    app.add_handler(CallbackQueryHandler(global_add_cancel,   pattern="^global_add_cancel$"))
    app.add_handler(CallbackQueryHandler(handle_alert_ack,    pattern="^alert_ack_"))
    app.add_handler(CallbackQueryHandler(handle_alert_logout, pattern="^alert_logout_"))
    # Auto-delete all incoming private messages (photos, docs, text outside conversation)
    app.add_handler(MessageHandler(
        private & (filters.PHOTO | filters.Document.ALL | filters.TEXT) & ~filters.COMMAND,
        global_auto_detect,
    ))

    # ── Admin (group) commands ─────────────────────────────────
    if ADMIN_GROUP_ID != 0:
        admin_filter = filters.Chat(chat_id=ADMIN_GROUP_ID)
        # Admin group handlers use group=-1 to ensure they fire before user handlers
        app.add_handler(CommandHandler("start",        admin_group_start,     filters=admin_filter), group=-1)
        # /login command removed - login is now managed via Dashboard Login Control button.
        app.add_handler(CommandHandler("userall",      admin_userall_export,  filters=admin_filter))
        # Dashboard callback handlers
        # NOTE: CallbackQueryHandler does NOT support a 'filters' kwarg in PTB v20+.
        # We wrap each callback so it silently ignores calls from outside the admin group.
        def _admin_cbq_guard(handler_fn):
            """Decorator that enforces admin_filter for CallbackQueryHandlers."""
            async def _guarded(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
                if update.effective_chat and update.effective_chat.id != ADMIN_GROUP_ID:
                    await update.callback_query.answer()  # acknowledge but do nothing
                    return
                await handler_fn(update, ctx)
            return _guarded

        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_noop_cb),                  pattern="^adm_noop$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_log_cb),                  pattern="^adm_log$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_backup_cb),                   pattern="^adm_backup$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_backup_all_cb),               pattern="^adm_backup_all$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_backup_restore_cb),           pattern="^adm_backup_restore$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_backup_specific_cb),          pattern="^adm_backup_specific$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_backup_user_control_cb),      pattern="^adm_backup_user_control$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_buc_offline_cb),              pattern="^adm_buc_offline$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_buc_offline_weekly_cb),       pattern="^adm_buc_offline_weekly$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_buc_offline_monthly_cb),      pattern="^adm_buc_offline_monthly$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_buc_reminder_cb),             pattern="^adm_buc_reminder$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_buc_reminder_weekly_cb),      pattern="^adm_buc_reminder_weekly$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_buc_reminder_monthly_cb),     pattern="^adm_buc_reminder_monthly$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_user_control_cb),        pattern="^adm_user_control$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_uc_enable_cb),           pattern="^adm_uc_enable$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_uc_disable_cb),          pattern="^adm_uc_disable$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_uc_disabled_list_cb),    pattern="^adm_uc_disabled_list$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_uc_ban_cb),              pattern="^adm_uc_ban$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_uc_unban_cb),            pattern="^adm_uc_unban$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_uc_ban_list_cb),         pattern="^adm_uc_ban_list$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_statistics_cb),          pattern="^adm_statistics$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_stats_today_cb),         pattern="^adm_stats_today$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_stats_weekly_cb),        pattern="^adm_stats_weekly$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_stats_monthly_cb),       pattern="^adm_stats_monthly$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_stats_lifetime_cb),      pattern="^adm_stats_lifetime$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_maintenance_view_cb),    pattern="^adm_maintenance$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_maintenance_toggle_cb),  pattern="^adm_maintenance_toggle$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_signup_cb),                    pattern="^adm_signup$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_signup_public_toggle_cb),     pattern="^adm_signup_public_toggle$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_specific_signup_cb),          pattern="^adm_specific_signup$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_specific_signup_enable_cb),   pattern="^adm_specific_signup_enable$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_specific_signup_disable_cb),  pattern="^adm_specific_signup_disable$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_signup_off_list_cb),          pattern="^adm_signup_off_list$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_login_cb),                    pattern="^adm_login$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_login_public_toggle_cb),      pattern="^adm_login_public_toggle$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_specific_login_cb),           pattern="^adm_specific_login$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_specific_login_enable_cb),    pattern="^adm_specific_login_enable$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_specific_login_disable_cb),   pattern="^adm_specific_login_disable$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_login_off_list_cb),           pattern="^adm_login_off_list$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_account_action_cb),           pattern="^adm_account_(disable|enable):.+$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_broadcast_cb),           pattern="^adm_broadcast$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_user_info_cb),           pattern="^adm_user_info$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_totp_limit_cb),        pattern="^adm_totp_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_totp_dup_limit_cb),   pattern="^adm_totp_dup_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_totp_onoff_cb),      pattern="^adm_totp_onoff$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_weekly_signup_limit_cb), pattern="^adm_weekly_signup_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_daily_login_limit_cb),   pattern="^adm_daily_login_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_vault_limit_cb),       pattern="^adm_vault_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_min_limit_cb),         pattern="^adm_min_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_specific_vault_max_cb),pattern="^adm_specific_vault_max$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_specific_vault_min_cb),pattern="^adm_specific_vault_min$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_back_cb),              pattern="^adm_back$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_donate_cb),              pattern="^adm_donate$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_set_donate_msg_cb),      pattern="^adm_set_donate_msg$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_check_abuse_cb),          pattern="^adm_check_abuse$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_check_user_abuse_cb),     pattern="^adm_check_user_abuse$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_check_totp_dup_cb),       pattern="^adm_check_totp_dup$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_ei_menu_cb),              pattern="^adm_ei_menu$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_ei_pub_exp_limit_cb),     pattern="^adm_ei_pub_exp_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_ei_pub_imp_limit_cb),     pattern="^adm_ei_pub_imp_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_ei_spec_exp_limit_cb),    pattern="^adm_ei_spec_exp_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_ei_spec_imp_limit_cb),    pattern="^adm_ei_spec_imp_limit$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_ei_spec_exp_list_cb),     pattern="^adm_ei_spec_exp_list$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_ei_spec_imp_list_cb),     pattern="^adm_ei_spec_imp_list$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_ei_pub_exp_toggle_cb),    pattern="^adm_ei_pub_exp_toggle$"))
        app.add_handler(CallbackQueryHandler(_admin_cbq_guard(adm_ei_pub_imp_toggle_cb),    pattern="^adm_ei_pub_imp_toggle$"))
        # Admin group message handler: group=-1 gives it priority over user handlers
        app.add_handler(MessageHandler(
            admin_filter & ~filters.COMMAND, admin_group_message_handler
        ), group=-1)

    # ── Job queue: daily backup reminders + hourly auto-backup ──
    jq = app.job_queue
    if jq:
        async def _reminder_job(ctx2):
            await send_backup_reminders(app)

        async def _autobackup_job(ctx2):
            await send_auto_backups(app)

        jq.run_repeating(
            _reminder_job,
            interval=300,
            first=60,
            name="backup_reminder_job",
        )
        # Auto-backup: runs every 5 minutes, checks if it's the right BDT time window
        jq.run_repeating(
            _autobackup_job,
            interval=300,
            first=60,
            name="auto_backup_job",
        )

    logger.info("BV Authenticator Bot started.")
    app.run_polling(drop_pending_updates=True)

if __name__ == "__main__":
    main()
