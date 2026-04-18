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
) = range(38)

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
TOTP_PER_PAGE       = 10    # TOTP entries per page in list view
NOTE_MAX_LEN        = 10    # max note characters
BACKUP_REMINDER_WEEKLY  = "weekly"
BACKUP_REMINDER_MONTHLY = "monthly"
BD_TZ = "Asia/Dhaka"       # Bangladesh timezone for admin panel

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

def check_totp_add_rate(vault_id: str) -> bool:
    """Returns True if vault has NOT exceeded MAX_TOTP_PER_MINUTE in the last 60 seconds."""
    now = int(time.time())
    with get_db() as c:
        row = c.execute(
            "SELECT count, window_start FROM totp_add_rate WHERE vault_id=?",
            (vault_id,)
        ).fetchone()
    if not row or now - row["window_start"] >= 60:
        return True   # window expired or no record
    return row["count"] < MAX_TOTP_PER_MINUTE

def record_totp_add(vault_id: str):
    """Increment the per-minute TOTP add counter for a vault."""
    now = int(time.time())
    with get_db() as c:
        row = c.execute(
            "SELECT count, window_start FROM totp_add_rate WHERE vault_id=?",
            (vault_id,)
        ).fetchone()
        if not row or now - row["window_start"] >= 60:
            # Start fresh window
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
class _DB:
    """SQLite connection context manager that commits AND closes on exit."""
    def __init__(self):
        self._conn = sqlite3.connect(DB_PATH, timeout=10.0, check_same_thread=True)
        self._conn.row_factory = sqlite3.Row
    def __enter__(self):
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
        try:
            self._conn.close()
        except Exception:
            pass
        return False
    def execute(self, *a, **kw):
        return self._conn.execute(*a, **kw)
    def close(self):
        try:
            self._conn.close()
        except Exception:
            pass

def get_db() -> "_DB":
    return _DB()

def init_db():
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

        # Migrate users table: account_disabled, last_seen
        for col, coltype, default in [
            ("account_disabled", "INTEGER", "0"),
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
        db = conn if conn else get_db()
        rows = db.execute("SELECT key, value FROM bot_settings").fetchall()
        for row in rows:
            if row["key"] in _bot_settings:
                val = row["value"]
                if val in ("true", "false"):
                    _bot_settings[row["key"]] = val == "true"
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
    ])

def kb_settings():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔑 Change Password",   callback_data="change_pw")],
        [InlineKeyboardButton("🔓 Reset Password",    callback_data="settings_reset_pw")],
        [InlineKeyboardButton("🛡 View Secure Key",   callback_data="view_secure_key")],
        [InlineKeyboardButton("📤 Export Vault",      callback_data="export_vault")],
        [InlineKeyboardButton("📥 Import Vault",      callback_data="import_vault")],
        [InlineKeyboardButton("🔔 Backup Reminder",   callback_data="backup_reminder")],
        [InlineKeyboardButton("💾 Offline Auto Backup", callback_data="offline_auto_backup")],
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


def build_share_selection_kb(rows: list, selected: set) -> InlineKeyboardMarkup:
    """
    Checkbox-style keyboard for Share Codes folder.
    rows: list of dicts with 'id' and 'name'.
    selected: set of selected totp account IDs.
    """
    buttons = []
    for row in rows:
        tid   = row["id"]
        check = "✅ " if tid in selected else "☐ "
        buttons.append([InlineKeyboardButton(
            f"{check}{row['name']}",
            callback_data=f"share_toggle_{tid}",
        )])
    action_row = []
    if selected:
        action_row.append(InlineKeyboardButton(
            f"🔗 Share Selected ({len(selected)})",
            callback_data="share_generate",
        ))
    action_row.append(InlineKeyboardButton("❌ Cancel", callback_data="share_cancel"))
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
    """User agreed to terms — proceed to vault ID + password setup."""
    q   = update.callback_query
    await q.answer()
    uid = update.effective_user.id
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
    u   = get_user(vid)
    if not u:
        await q.edit_message_text(
            "❌ No account found for this Telegram account\\. Please *Sign Up*\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_auth(),
        )
        return AUTH_MENU
    # Block disabled accounts before they even enter password
    if u["account_disabled"]:
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
    # Block disabled accounts before password entry
    if u["account_disabled"]:
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
    """Record a failed login attempt. Returns True if account is now frozen."""
    now = int(time.time())
    with get_db() as c:
        row = c.execute(
            "SELECT attempts, frozen_until FROM login_attempts WHERE vault_id=?", (vault_id,)
        ).fetchone()
        if row and row["frozen_until"] > now:
            return True  # already frozen
        attempts     = (row["attempts"] if row else 0) + 1
        frozen_until = now + LOGIN_FREEZE_HOURS * 3600 if attempts >= MAX_LOGIN_ATTEMPTS else 0
        c.execute(
            "INSERT OR REPLACE INTO login_attempts (vault_id, attempts, frozen_until) VALUES (?,?,?)",
            (vault_id, attempts, frozen_until),
        )
        c.commit()
        return frozen_until > now

def clear_login_failures(vault_id: str):
    with get_db() as c:
        c.execute("DELETE FROM login_attempts WHERE vault_id=?", (vault_id,))
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

    if not hmac.compare_digest(hash_pw(pw, bytes(u["pw_salt"]), u["kdf_type"] or "pbkdf2"), bytes(u["password_hash"])):
        # Record failed attempt and check freeze
        frozen = record_login_failure(vid)
        if frozen:
            remaining, _ = get_login_freeze_remaining(vid)
            h, m = remaining // 3600, (remaining % 3600) // 60
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
                        plain = decrypt(row["secret_enc"], row["salt"], row["iv"], pw, vid)
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

    if sk_skipped or deleted_cnt > 0:
        result_msg = (
            "✅ *Password reset successful\\!*\n\n"
            f"⚠️ _All {em(str(deleted_cnt))} TOTP accounts were permanently deleted \\(Secure Key not provided\\)\\._\n\n"
            "🔑 A *new Secure Key* has been generated for your vault\\.\n"
            "You will see it after logging in via Settings → View Secure Key\\.\n\n"
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
            reply_markup=kb_cancel(),
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
                    secret    = decrypt(row["secret_enc"], row["salt"], row["iv"], old_pw, vault)
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
        u = c.execute("SELECT mk_enc, mk_salt, mk_iv, kdf_type, pw_salt, sk_enc, sk_salt, sk_iv "
                      "FROM users WHERE vault_id=?", (vault,)).fetchone()
    if u and u["mk_enc"]:
        # New architecture: only re-wrap the master key with new password
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
            logger.error(f"change_pw master key rewrap failed: {e}")
            await update.message.reply_text(
                "❌ Password change failed\\. Please try again\\.",
                parse_mode="MarkdownV2", reply_markup=kb_main()
            )
            return TOTP_MENU
    else:
        # Legacy path: re-encrypt all TOTP secrets and sk with new password
        with get_db() as c:
            rows = c.execute(
                "SELECT id, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?", (vault,)
            ).fetchall()
            for row in rows:
                try:
                    secret    = decrypt(row["secret_enc"], row["salt"], row["iv"], old_pw, vault)
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
    acc_type = "totp"
    hotp_ctr = 0
    note     = (data.get("note", "") or "")[:NOTE_MAX_LEN]

    # Per-minute rate limit: max 20 TOTP additions per minute
    if not check_totp_add_rate(vault):
        await update.message.reply_text(
            f"⚠️ *Too many accounts added\\.*\n\n"
            f"Maximum *{MAX_TOTP_PER_MINUTE}* TOTP accounts can be added per minute\\.\n"
            "Please wait a moment and try again\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU

    # Auto-suffix name if duplicate, enforce max 20 chars
    final_name = _auto_suffix_name(vault, data["name"])

    vault_key = _get_vault_key(vault, pw)
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

    record_totp_add(vault)

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

    entries = []
    for i, row in enumerate(chunk, start=page * TOTP_PER_PAGE + 1):
        try:
            secret = decrypt(row["secret_enc"], row["salt"], row["iv"], pw, vault)
            note     = (row["note"] or "").strip()
            code, remain, next_code = generate_code(secret)

            # Format TOTP code: "123 456"
            code_fmt  = code
            time_line = f"{bar(remain)} {remain}s"

            # Next code display
            next_line = f"Next code: `{next_code}`" if next_code else ""

            note_line = f"Note: {em(note)}" if note else ""

            # Build entry block
            name_line = f"*{i}\\. {em(row['name'])}*"
            if row["issuer"]:
                name_line += f" \\| _{em(row['issuer'])}_"

            block = [name_line, f"Current Code: `{code}` {time_line}"]
            if next_line:
                block.append(next_line)
            if note_line:
                block.append(note_line)
            entries.append("\n".join(block))
        except Exception as e:
            logger.error(f"List TOTP error: {e}")
            entries.append(f"*{i}\\. {em(row['name'])}*\n_\\[Decrypt error\\]_")

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
    """Open the Share Codes folder with checkbox selection."""
    q     = update.callback_query
    await q.answer()
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    if not vault or not pw:
        await q.edit_message_text("Session expired\\. /start", parse_mode="MarkdownV2", reply_markup=kb_auth())
        return AUTH_MENU
    with get_db() as c:
        rows = c.execute(
            "SELECT id, name FROM totp_accounts WHERE vault_id=? ORDER BY name", (vault,)
        ).fetchall()
    if not rows:
        await q.edit_message_text(
            "📁 *Share Codes*\n\n⚠️ No TOTP accounts to share\\.",
            parse_mode="MarkdownV2",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")]]),
        )
        return TOTP_MENU
    ctx.user_data["share_rows"]     = [{"id": r["id"], "name": r["name"]} for r in rows]
    ctx.user_data["share_selected"] = set()
    await q.edit_message_text(
        "📁 *Share Codes*\n\n"
        "Select the accounts you want to share\\.\n"
        "Tap an account to toggle\\. Then tap *🔗 Share Selected*\\.\n\n"
        "_The generated link is valid for *10 minutes*\\.\n"
        "Only the TOTP code is visible \\(no secret keys\\)\\._",
        parse_mode="MarkdownV2",
        reply_markup=build_share_selection_kb(ctx.user_data["share_rows"], ctx.user_data["share_selected"]),
    )
    return TOTP_MENU

async def share_toggle(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Toggle a TOTP account in/out of the share selection."""
    q = update.callback_query
    await q.answer()
    try:
        totp_id = int(q.data.split("_")[2])
    except (IndexError, ValueError):
        return TOTP_MENU
    selected: set = ctx.user_data.get("share_selected", set())
    rows           = ctx.user_data.get("share_rows", [])
    if totp_id in selected:
        selected.discard(totp_id)
    else:
        selected.add(totp_id)
    ctx.user_data["share_selected"] = selected
    try:
        await q.edit_message_reply_markup(
            reply_markup=build_share_selection_kb(rows, selected),
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
    selected_ids = [r["id"] for r in rows if r["id"] in selected]
    id_to_name   = {r["id"]: r["name"] for r in rows if r["id"] in selected}
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
    for db_row in db_rows:
        try:
            plain = decrypt(db_row["secret_enc"], db_row["salt"], db_row["iv"], pw, vault)
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
    share_url  = f"https://t.me/{BOT_USERNAME}?start={token}"
    names_text = ", ".join(em(n) for n in final_names)
    exp_min    = SHARE_LINK_TTL // 60
    await q.edit_message_text(
        f"🔗 *Share Link Generated\\!*\n\n"
        f"📋 *Accounts:* {names_text}\n"
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
    lines = []
    for i, (name, enc) in enumerate(zip(names, secrets_enc)):
        try:
            secret   = share_decrypt_secret(enc, token)
            code, rm = totp_now(secret)
            lines.append(
                f"*{em(name)}*\n"
                f"`{code}` {bar(rm)} {rm}s"
            )
        except Exception as e:
            logger.error(f"Share view decrypt error idx={i}: {e}")
            lines.append(f"*{em(name)}*\n_\\[Unavailable\\]_")
    refresh_url = f"https://t.me/{BOT_USERNAME}?start={token}"
    text = (
        "📋 *Shared TOTP Codes*\n\n"
        + "\n\n".join(lines)
        + f"\n\n⏳ Link expires in *{rem_min}m {rem_sec}s*\\.\n"
        "_Tap below to refresh codes\\._"
    )
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔄 Refresh Codes", url=refresh_url)]])
    await update.message.reply_text(text, parse_mode="MarkdownV2", reply_markup=kb)

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
            [InlineKeyboardButton("📝 Note",            callback_data="edit_action_note")],
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
            reply_markup=kb_danger("edit_action_delete_confirm", "edit_totp"),
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
    plain   = json.dumps({"version": 3, "vault_id": vault, "accounts": entries}, ensure_ascii=False).encode()
    payload = export_encrypt(plain, file_pw)
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
    if not accounts:
        await update.message.reply_text(
            "⚠️ No accounts found in backup file\\.",
            parse_mode="MarkdownV2",
            reply_markup=kb_main(),
        )
        return TOTP_MENU
    # Check for duplicates
    uid   = update.effective_user.id
    vault = get_session(uid)
    with get_db() as c:
        existing_names = {r["name"] for r in c.execute(
            "SELECT name FROM totp_accounts WHERE vault_id=?", (vault,)
        ).fetchall()}
    duplicates = [a["name"] for a in accounts if a["name"] in existing_names]
    ctx.user_data["import_accounts"] = accounts
    if duplicates:
        dup_list = "\n".join(f"• {em(n)}" for n in duplicates[:10])
        more     = f"\n\\.\\.\\. and {len(duplicates)-10} more" if len(duplicates) > 10 else ""
        await update.message.reply_text(
            f"📥 *Import* — *{len(accounts)}* accounts found\\.\n\n"
            f"⚠️ *{len(duplicates)} duplicate\\(s\\):*\n{dup_list}{more}\n\n"
            "Choose how to handle duplicates:",
            parse_mode="MarkdownV2",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("⏭ Skip duplicates",   callback_data="import_mode_skip")],
                [InlineKeyboardButton("🔄 Replace duplicates", callback_data="import_mode_replace")],
                [InlineKeyboardButton("❌ Cancel",             callback_data="cancel_to_menu")],
            ]),
        )
        return IMPORT_OVERRIDE_WAIT
    # No duplicates: import all directly
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
    pw       = ctx.user_data.get("password", "")
    imported = 0
    skipped  = 0
    replaced = 0
    with get_db() as c:
        # Build duplicate lookup: {(name, secret_sha256_hex): id}
        # This correctly handles same-name different-secret and same-secret different-name
        existing_rows = c.execute(
            "SELECT id, name, secret_enc, salt, iv FROM totp_accounts WHERE vault_id=?", (vault,)
        ).fetchall()
        # For duplicate detection, decrypt existing secrets and hash them
        existing_by_name   = {r["name"]: r["id"] for r in existing_rows}  # name -> id (for replace)
        existing_secrets   = set()    # sha256(secret) set
        # Track which entries had decrypt failures - these are protected from overwrite
        undecryptable_names = set()
        for r in existing_rows:
            try:
                plain = decrypt(r["secret_enc"], r["salt"], r["iv"], pw, vault)
                existing_secrets.add(hashlib.sha256(plain.encode()).hexdigest())
            except Exception as e:
                logger.warning(f"Import duplicate check: decrypt failed for '{r['name']}': {e}")
                # Cannot read this entry - protect it from being overwritten
                undecryptable_names.add(r["name"])

        sk = load_user_secure_key(vault, pw)
        for acc in accounts:
            try:
                ok, secret = validate_secret(acc.get("secret", ""))
                if not ok:
                    skipped += 1
                    continue
                note     = (acc.get("note", "") or "")[:NOTE_MAX_LEN]
                totp_now(secret)   # sanity check
                secret_hash = hashlib.sha256(secret.encode()).hexdigest()
                vault_key = _get_vault_key(vault, pw)
                ct, s, iv = encrypt(secret, vault_key, vault)
                sk_ct = sk_s = sk_iv = None
                if sk:
                    sk_ct, sk_s, sk_iv = sk_encrypt_totp(secret.encode(), sk, vault)

                # Duplicate = same name AND same secret
                name_exists   = acc["name"] in existing_by_name
                secret_exists = secret_hash in existing_secrets

                if name_exists and acc["name"] in undecryptable_names:
                    # Existing entry could not be decrypted — never overwrite it, skip safely
                    skipped += 1
                elif name_exists and secret_exists:
                    # True duplicate: same name + same secret
                    if mode == "replace":
                        c.execute(
                            "UPDATE totp_accounts SET issuer=?, secret_enc=?, salt=?, iv=?, "
                            "sk_enc=?, sk_salt=?, sk_iv=?, note=?, account_type='totp', hotp_counter=0 "
                            "WHERE id=?",
                            (acc.get("issuer", ""), ct, s, iv, sk_ct, sk_s, sk_iv,
                             note, existing_by_name[acc["name"]]),
                        )
                        replaced += 1
                    else:
                        skipped += 1
                else:
                    # Not a true duplicate: add as new entry
                    c.execute(
                        "INSERT INTO totp_accounts "
                        "(vault_id, name, issuer, secret_enc, salt, iv, sk_enc, sk_salt, sk_iv, "
                        "note, account_type, hotp_counter) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                        (vault, acc["name"], acc.get("issuer", ""), ct, s, iv,
                         sk_ct, sk_s, sk_iv, note, "totp", 0),
                    )
                    existing_secrets.add(secret_hash)
                    imported += 1
            except Exception as e:
                logger.error(f"Import entry '{acc.get('name','?')}': {e}")
                skipped += 1
        c.commit()
    lines = [f"✅ *Import complete\\!*\n"]
    if imported:
        lines.append(f"Added: *{imported}*")
    if replaced:
        lines.append(f"Replaced: *{replaced}*")
    if skipped:
        lines.append(f"Skipped: *{skipped}* \\(invalid/duplicate\\)")
    result_text = "\n".join(lines)
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
            c.execute("DELETE FROM share_links WHERE vault_id=?",    (vault,))
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
    """
    Handles QR/secret detection outside conversation state.
    Also auto-deletes ANY incoming private message (text, photo, document, etc.)
    after 30 seconds to prevent sensitive data accumulating in chat.
    """
    if not update.message:
        return
    uid   = update.effective_user.id
    vault = get_session(uid)
    pw    = ctx.user_data.get("password")
    # Auto-delete the incoming message after 30s regardless of content
    asyncio.create_task(auto_delete_msg(update.message, delay=30))
    # Update last_seen for every message interaction
    if vault:
        update_last_seen(uid)
    if not vault or not pw:
        return

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
            entries = []
            for i, row in enumerate(matched, 1):
                try:
                    secret   = decrypt(row["secret_enc"], row["salt"], row["iv"], pw, vault)
                    note     = (row["note"] or "").strip()
                    code, remain, next_code = generate_code(secret)
                    code_fmt  = code
                    time_line = f"{bar(remain)} {remain}s"
                    nf = next_code if next_code else ""
                    name_line = f"*{i}\\. {em(row['name'])}*"
                    if row["issuer"]:
                        name_line += f" \\| _{em(row['issuer'])}_"
                    block = [name_line, f"Current Code: `{code}` {time_line}"]
                    if nf:
                        block.append(f"Next code: `{nf}`")
                    if note:
                        block.append(f"Note: {em(note)}")
                    entries.append("\n".join(block))
                except Exception as e:
                    logger.error(f"Hash-search decrypt: {e}")
                    entries.append(f"*{i}\\. {em(row['name'])}*\n_\\[Decrypt error\\]_")
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
        ctx.user_data.pop("_global_add", None)
        if raw_name and secret:
            # Rate limit check
            if not check_totp_add_rate(vault):
                await update.message.reply_text(
                    f"⚠️ *Too many accounts added\\.*\n\n"
                    f"Maximum *{MAX_TOTP_PER_MINUTE}* TOTP accounts can be added per minute\\.",
                    parse_mode="MarkdownV2",
                    reply_markup=kb_main(),
                )
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
                ctx.user_data["_global_add"]    = True
                return
            name = _auto_suffix_name(vault, raw_name)
            vault_key = _get_vault_key(vault, pw)
            ct, salt, iv = encrypt(secret, vault_key, vault)
            sk = load_user_secure_key(vault, pw)
            if sk:
                sk_ct, sk_s, sk_iv = sk_encrypt_totp(secret.encode(), sk, vault)
            else:
                sk_ct = sk_s = sk_iv = None
            with get_db() as c:
                c.execute(
                    "INSERT INTO totp_accounts (vault_id, name, issuer, secret_enc, salt, iv, "
                    "sk_enc, sk_salt, sk_iv, note, account_type, hotp_counter) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                    (vault, name, "", ct, salt, iv, sk_ct, sk_s, sk_iv, "", "totp", 0),
                )
                c.commit()
            record_totp_add(vault)
            try:
                code, remain, _ = generate_code(secret)
            except Exception:
                code, remain = "------", 30
            suffix_note = f"\n_\\(Renamed: {em(name)}\\)_" if name != raw_name else ""
            await update.message.reply_text(
                f"✅ *{em(name)}* added\\!{suffix_note}\n\n"
                f"🔢 `{code}`\n"
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
    entries = []
    for i, row in enumerate(matched, 1):
        try:
            secret = decrypt(row["secret_enc"], row["salt"], row["iv"], pw, vault)
            note     = (row["note"] or "").strip()
            code, remain, next_code = generate_code(secret)
            code_fmt  = code
            time_line = f"{bar(remain)} {remain}s"
            next_line = f"Next code: `{next_code}`" if next_code else ""
            note_line = f"Note: {em(note)}" if note else ""
            name_line = f"*{i}\\. {em(row['name'])}*"
            if row["issuer"]:
                name_line += f" \\| _{em(row['issuer'])}_"
            block = [name_line, f"Current Code: `{code}` {time_line}"]
            if next_line:
                block.append(next_line)
            if note_line:
                block.append(note_line)
            entries.append("\n".join(block))
        except Exception as e:
            logger.error(f"Search TOTP decrypt error: {e}")
            entries.append(f"*{i}\\. {em(row['name'])}*\n_\\[Decrypt error\\]_")
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
            status = "Disabled" if u["account_disabled"] else "Active"
        except (KeyError, TypeError):
            status = "Active"
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
            f"Total TOTP     : {totp_cnt} Account(s)\n\n"
            f"Created        : {created_at}\n\n"
            f"Last Online    : {last_seen}\n\n"
            f"Account Status : {status}\n\n"
            f"Reminder       : {reminder_status}\n"
            f"Auto Backup    : {auto_backup_status}\n\n"
            f"Failed Logins  : {failed_login}\n\n"
            f"Failed Resets  : {failed_reset}"
        )
    except Exception as e:
        logger.error(f"_fmt_user_info error: {e}")
        return f"[Error building user info: {e}]"

# ── ADMIN COMMANDS ──────────────────────────────────────────
async def admin_maintenance(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """
    /maintenance on   -- enable maintenance mode
    /maintenance off  -- disable maintenance mode
    """
    if not _is_admin_msg(update):
        return
    # Strip bot @mention from group commands: "/maintenance@Bot on" -> state="on"
    raw_text     = (update.message.text or "").strip()
    command_part = raw_text.split()[0] if raw_text else ""
    state        = raw_text[len(command_part):].strip().lower()
    if state == "on":
        _save_setting("maintenance", True)
        msg = await update.message.reply_text("🔧 Maintenance mode ON. Users are blocked.")
    elif state == "off":
        _save_setting("maintenance", False)
        msg = await update.message.reply_text("✅ Maintenance mode OFF. Bot is live.")
    else:
        cur = "ON" if is_maintenance() else "OFF"
        msg = await update.message.reply_text(
            f"Usage: /maintenance on|off\nCurrent: {cur}"
        )
    asyncio.create_task(auto_delete_msg(msg, delay=60))
    asyncio.create_task(auto_delete_msg(update.message, delay=60))

async def admin_signup_toggle(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """/signup on|off"""
    if not _is_admin_msg(update):
        return
    # Strip bot @mention from group command text
    raw_text     = (update.message.text or "").strip()
    command_part = raw_text.split()[0] if raw_text else ""
    state        = raw_text[len(command_part):].strip().lower()
    if state == "on":
        _save_setting("signup_enabled", True)
        msg = await update.message.reply_text("✅ Sign-up ENABLED.")
    elif state == "off":
        _save_setting("signup_enabled", False)
        msg = await update.message.reply_text("🚫 Sign-up DISABLED.")
    else:
        cur = "ON" if is_signup_enabled() else "OFF"
        msg = await update.message.reply_text(f"Usage: /signup on|off\nCurrent: {cur}")
    asyncio.create_task(auto_delete_msg(msg, delay=60))
    asyncio.create_task(auto_delete_msg(update.message, delay=60))

async def admin_login_toggle(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """/login on|off"""
    if not _is_admin_msg(update):
        return
    # Strip bot @mention from group command text
    raw_text     = (update.message.text or "").strip()
    command_part = raw_text.split()[0] if raw_text else ""
    state        = raw_text[len(command_part):].strip().lower()
    if state == "on":
        _save_setting("login_enabled", True)
        msg = await update.message.reply_text("✅ Login ENABLED.")
    elif state == "off":
        _save_setting("login_enabled", False)
        msg = await update.message.reply_text("🚫 Login DISABLED.")
    else:
        cur = "ON" if is_login_enabled() else "OFF"
        msg = await update.message.reply_text(f"Usage: /login on|off\nCurrent: {cur}")
    asyncio.create_task(auto_delete_msg(msg, delay=60))
    asyncio.create_task(auto_delete_msg(update.message, delay=60))

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

async def admin_account_disable(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """/account disable|enable <vault_id|tid|@username>"""
    if not _is_admin_msg(update):
        return
    asyncio.create_task(auto_delete_msg(update.message, delay=60))
    # Strip bot @mention from group command text: "/account@BotName disable arg" -> "disable arg"
    raw_text     = (update.message.text or "").strip()
    command_part = raw_text.split()[0] if raw_text else ""
    arg_str      = raw_text[len(command_part):].strip()   # "disable abc123" or "enable @user"
    arg_parts    = arg_str.split(None, 1)                 # ["disable", "abc123"]
    if len(arg_parts) < 2 or arg_parts[0].lower() not in ("disable", "enable"):
        msg = await update.message.reply_text(
            "Usage: /account disable <vault_id|tid|@username>\n"
            "       /account enable  <vault_id|tid|@username>"
        )
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    action = arg_parts[0].lower()
    raw    = arg_parts[1].strip()
    u      = _resolve_user(raw)
    if not u:
        msg = await update.message.reply_text(f"❌ User not found: {raw}")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    flag = 1 if action == "disable" else 0
    with get_db() as c:
        c.execute("UPDATE users SET account_disabled=? WHERE vault_id=?", (flag, u["vault_id"]))
        if flag:
            c.execute("DELETE FROM sessions WHERE vault_id=?", (u["vault_id"],))
        c.commit()
    if flag:
        _session_pw_cache.pop(u["vault_id"], None)
    word = "DISABLED" if flag else "ENABLED"
    note = "\nAll active sessions cleared." if flag else ""
    resp = await update.message.reply_text(
        f"✅ Account `{u['vault_id']}` ({u['tg_username'] or u['telegram_id']}) has been {word}.{note}"
    )
    asyncio.create_task(auto_delete_msg(resp, delay=60))
    try:
        if flag:
            await ctx.bot.send_message(
                chat_id=u["telegram_id"],
                text="🚫 *Your account has been disabled by an administrator\\.*\n\n"
                     "_Your data is safe and has not been deleted\\._",
                parse_mode="MarkdownV2",
            )
        else:
            await ctx.bot.send_message(
                chat_id=u["telegram_id"],
                text="✅ *Your account has been re\\-enabled\\. You can log in again\\.*",
                parse_mode="MarkdownV2",
            )
    except Exception as e:
        logger.warning(f"Could not notify user {u['telegram_id']}: {e}")

async def admin_broadcast(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """/broadcast <message>  OR  reply to a message with /broadcast"""
    if not _is_admin_msg(update):
        return
    asyncio.create_task(auto_delete_msg(update.message, delay=60))
    with get_db() as c:
        users = c.execute("SELECT telegram_id FROM users").fetchall()
    reply_to = update.message.reply_to_message
    text_msg  = " ".join(ctx.args) if ctx.args else None
    sent = 0; failed = 0
    for row in users:
        tid = row["telegram_id"]
        try:
            if reply_to:
                await reply_to.copy(chat_id=tid)
            elif text_msg:
                await ctx.bot.send_message(chat_id=tid, text=text_msg)
            else:
                continue
            sent += 1
        except Exception:
            failed += 1
    msg = await update.message.reply_text(
        f"📢 Broadcast complete.\nSent: {sent}  |  Failed: {failed}"
    )
    asyncio.create_task(auto_delete_msg(msg, delay=60))

async def admin_export(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """
    /export <password>
    Exports the entire DB as an encrypted .bvadmin file to the admin group.
    """
    if not _is_admin_msg(update):
        return
    asyncio.create_task(auto_delete_msg(update.message, delay=60))
    if not ctx.args:
        msg = await update.message.reply_text("Usage: /export <encryption_password>")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    password = ctx.args[0]
    tables = [
        "users", "totp_accounts", "sessions", "reset_otps",
        "reset_attempts", "login_alerts", "share_links",
        "login_attempts", "backup_reminders", "bot_settings",
        "auto_backup_settings",
    ]
    dump = {}
    with get_db() as c:
        for tbl in tables:
            try:
                rows = c.execute(f"SELECT * FROM {tbl}").fetchall()
                dump[tbl] = [dict(r) for r in rows]
            except Exception as e:
                logger.warning(f"Admin export table {tbl}: {e}")
    plain   = json.dumps(dump, ensure_ascii=False, default=str).encode()
    payload = _admin_encrypt(plain, password)
    ts_str  = datetime.datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    fname   = f"bv_admin_export_{ts_str}.bvadmin"
    bio     = BytesIO(payload)
    bio.name = fname
    await update.message.reply_document(
        document=bio,
        filename=fname,
        caption=(
            f"🔒 BV Authenticator -- Full DB Export\n"
            f"📅 {ts_str}\n"
            f"🔑 Encrypted with the password you provided.\n\n"
            f"Use /import to restore."
        ),
    )

# Admin import state: waiting for the .bvadmin file
_admin_import_pending: dict = {}   # chat_id → {"password": str}

async def admin_import(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """/import  -- starts the import process in the admin group."""
    if not _is_admin_msg(update):
        return
    asyncio.create_task(auto_delete_msg(update.message, delay=60))
    chat_id = update.effective_chat.id
    _admin_import_pending[chat_id] = {"step": "wait_file"}
    msg = await update.message.reply_text(
        "📥 Admin Import\n\nSend the .bvadmin backup file now."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=60))

async def admin_import_file_recv(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Receive the .bvadmin file in admin group during /import flow."""
    if not _is_admin_msg(update):
        return
    chat_id = update.effective_chat.id
    state   = _admin_import_pending.get(chat_id, {})
    if state.get("step") != "wait_file":
        return
    if not update.message.document:
        msg = await update.message.reply_text("⚠️ Please send a .bvadmin file.")
        asyncio.create_task(auto_delete_msg(msg, delay=60))
        return
    asyncio.create_task(auto_delete_msg(update.message, delay=60))
    bio = BytesIO()
    f   = await update.message.document.get_file()
    await f.download_to_memory(bio)
    _admin_import_pending[chat_id] = {"step": "wait_password", "payload": bio.getvalue()}
    msg = await update.message.reply_text(
        "🔒 File received. Now send the encryption password."
    )
    asyncio.create_task(auto_delete_msg(msg, delay=60))

async def admin_import_password(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """Receive the decryption password for admin import."""
    if not _is_admin_msg(update):
        return
    chat_id = update.effective_chat.id
    state   = _admin_import_pending.get(chat_id, {})
    if state.get("step") != "wait_password":
        return
    password = update.message.text.strip()
    # Delete the password message immediately
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
    tables = list(dump.keys())
    with get_db() as c:
        for tbl, rows in dump.items():
            for row in rows:
                if not rows:
                    continue
                cols  = ", ".join(row.keys())
                phs   = ", ".join("?" for _ in row)
                try:
                    c.execute(
                        f"INSERT OR REPLACE INTO {tbl} ({cols}) VALUES ({phs})",
                        list(row.values()),
                    )
                except Exception as e:
                    logger.warning(f"Admin import row into {tbl}: {e}")
        c.commit()
    # Reload bot settings from DB
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
            [InlineKeyboardButton("⚙️ Settings", callback_data="settings")],
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
            await bot.send_message(
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

        payload = export_encrypt(plain, live_pw)

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

        msg = await bot.send_document(
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
    Monthly: First Sunday of month, BD time 18:00
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

    # Weekly window:  Saturday 20:00-20:09 BDT
    is_weekly_window  = (weekday == 5 and hour == 20 and minute < 10)
    # Monthly window: first Sunday (day<=7) 18:00-18:09 BDT
    is_monthly_window = (weekday == 6 and day <= 7 and hour == 18 and minute < 10)

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
            [InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")],
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
    Called by job queue once per day.
    Default state: enabled=1, weekly. Users with no row in backup_reminders get weekly reminders.
    """
    now     = int(time.time())
    week_s  = 7  * 24 * 3600
    month_s = 30 * 24 * 3600

    # Get all users; LEFT JOIN with backup_reminders to include users with no preference row
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
        freq     = row["frequency"]
        interval = week_s if freq == BACKUP_REMINDER_WEEKLY else month_s
        if now - row["last_sent"] < interval:
            continue
        tid = row["telegram_id"]
        try:
            await app.bot.send_message(
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
                    (tid, now),
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
    app     = ApplicationBuilder().token(token).build()
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
                CallbackQueryHandler(add_totp_start,        pattern="^add_totp$"),
                CallbackQueryHandler(list_totp,             pattern="^list_totp$"),
                CallbackQueryHandler(list_page_cb,          pattern=r"^list_page_\d+$"),
                CallbackQueryHandler(list_page_cb,          pattern="^list_noop$"),
                CallbackQueryHandler(search_totp_open,      pattern="^search_totp_open$"),
                CallbackQueryHandler(edit_totp_start,       pattern="^edit_totp$"),
                CallbackQueryHandler(show_profile,          pattern="^profile$"),
                CallbackQueryHandler(settings_menu,         pattern="^settings$"),
                CallbackQueryHandler(change_pw_start,       pattern="^change_pw$"),
                CallbackQueryHandler(settings_reset_start,  pattern="^settings_reset_pw$"),
                CallbackQueryHandler(view_secure_key_start, pattern="^view_secure_key$"),
                CallbackQueryHandler(export_vault_start,    pattern="^export_vault$"),
                CallbackQueryHandler(import_vault_start,    pattern="^import_vault$"),
                CallbackQueryHandler(delete_account_start,  pattern="^delete_account$"),
                CallbackQueryHandler(logout,                pattern="^logout$"),
                CallbackQueryHandler(main_menu_cb,          pattern="^main_menu$"),
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
                CallbackQueryHandler(share_cancel,          pattern="^share_cancel$"),
            ],
            SEARCH_TOTP_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, search_totp_input),
                CallbackQueryHandler(cancel_to_menu,    pattern="^cancel_to_menu$"),
                CallbackQueryHandler(search_totp_open,  pattern="^search_totp_open$"),
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
                CallbackQueryHandler(edit_action,         pattern=r"^edit_action_(rename|delete|showsecret|note)$"),
                CallbackQueryHandler(edit_delete_confirm, pattern="^edit_action_delete_confirm$"),
                CallbackQueryHandler(edit_totp_start,     pattern="^edit_totp$"),
            ],
            EDIT_RENAME_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, edit_rename_input),
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
            ],
            NOTE_INPUT: [
                MessageHandler(private & filters.TEXT & ~filters.COMMAND, note_input),
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
                CallbackQueryHandler(cancel_to_menu, pattern="^cancel_to_menu$"),
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
        app.add_handler(CommandHandler("maintenance",  admin_maintenance,     filters=admin_filter))
        app.add_handler(CommandHandler("signup",       admin_signup_toggle,   filters=admin_filter))
        app.add_handler(CommandHandler("login",        admin_login_toggle,    filters=admin_filter))
        app.add_handler(CommandHandler("user",         admin_user_info,       filters=admin_filter))
        app.add_handler(CommandHandler("account",      admin_account_disable, filters=admin_filter))
        app.add_handler(CommandHandler("broadcast",    admin_broadcast,       filters=admin_filter))
        app.add_handler(CommandHandler("export",       admin_export,          filters=admin_filter))
        app.add_handler(CommandHandler("import",       admin_import,          filters=admin_filter))
        app.add_handler(CommandHandler("userall",      admin_userall_export,  filters=admin_filter))
        # Admin import: receive file and password in group
        app.add_handler(MessageHandler(
            admin_filter & filters.Document.ALL, admin_import_file_recv
        ))
        app.add_handler(MessageHandler(
            admin_filter & filters.TEXT & ~filters.COMMAND, admin_import_password
        ))

    # ── Job queue: daily backup reminders + hourly auto-backup ──
    jq = app.job_queue
    if jq:
        async def _reminder_job(ctx2):
            await send_backup_reminders(app)

        async def _autobackup_job(ctx2):
            await send_auto_backups(app)

        jq.run_repeating(
            _reminder_job,
            interval=86400,
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
