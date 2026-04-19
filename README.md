<div align="center">

<br>

```
██████╗ ██╗      ██████╗  ██████╗██╗  ██╗██╗   ██╗███████╗██╗██╗
██╔══██╗██║     ██╔═══██╗██╔════╝██║ ██╔╝██║   ██║██╔════╝██║██║
██████╔╝██║     ██║   ██║██║     █████╔╝ ██║   ██║█████╗  ██║██║
██╔══██╗██║     ██║   ██║██║     ██╔═██╗ ╚██╗ ██╔╝██╔══╝  ██║██║
██████╔╝███████╗╚██████╔╝╚██████╗██║  ██╗ ╚████╔╝ ███████╗██║███████╗
╚═════╝ ╚══════╝ ╚═════╝  ╚═════╝╚═╝  ╚═╝  ╚═══╝  ╚══════╝╚═╝╚══════╝
```

### BLOCKVEIL Authenticator

**Your two-factor codes. Encrypted. Private. Inside Telegram.**

<br>

[![Telegram](https://img.shields.io/badge/Open%20in%20Telegram-2CA5E0?style=for-the-badge&logo=telegram&logoColor=white)](https://t.me/TotpNafiBot)
&nbsp;
[![Encryption](https://img.shields.io/badge/AES--256--GCM-Encrypted-22c55e?style=for-the-badge&logo=gnuprivacyguard&logoColor=white)](https://en.wikipedia.org/wiki/Galois/Counter_Mode)
&nbsp;
[![Python](https://img.shields.io/badge/Python-3.11+-3776AB?style=for-the-badge&logo=python&logoColor=white)](https://python.org)

<br>

</div>

---

<br>

## What is BlockVeil Authenticator?

BlockVeil Authenticator is a Telegram bot that stores and generates your two-factor authentication (2FA / TOTP) codes. Instead of a separate app on your phone, everything lives inside a conversation with the bot, protected by strong end-to-end encryption.

Your codes belong to you. The server never sees them.

<br>

---

<br>

## Why use it?

Most authenticator apps are tied to a single device. Lose your phone and you lose everything. BV Authenticator is different: your vault is encrypted and stored in the cloud, accessible from any Telegram account you authorize, with a backup system that works automatically in the background.

<br>

| Problem with other apps | How BV Authenticator handles it |
|---|---|
| Tied to one device | Access from any Telegram session |
| No backup until it's too late | Scheduled auto-backup to your Telegram DM |
| Difficult to share a code temporarily | 10-minute share link, no account needed |
| Switching phones means manual re-entry | Import your encrypted vault file anywhere |
| Closed source, unknown encryption | Open codebase, documented encryption layer |

<br>

---

<br>

## Security

Security is the only reason this bot exists. Every decision in its design reflects that.

<br>

### Encryption that the server cannot break

Your TOTP secrets are encrypted using **AES-256-GCM** before they ever touch the database. The encryption key is derived from your password using **Argon2id**, the winner of the Password Hashing Competition and the current recommendation from OWASP.

The server stores only ciphertext. Even with full database access, there is no way to recover your secrets without your password.

```
Your Password
      |
      | Argon2id  (64 MB RAM, 3 iterations)
      v
  Wrap Key  ------>  unlocks  ------>  Master Key (random, per vault)
                                            |
                                            | AES-256-GCM
                                            v
                                     Encrypted TOTP Secrets
```

<br>

### Argon2id parameters

Argon2id is configured to the OWASP recommended settings. This makes brute-force attacks computationally expensive even with dedicated hardware.

```
Time cost    : 3 iterations
Memory cost  : 64 MB per hash
Parallelism  : 1
Output       : 32 bytes
```

<br>

### The Secure Key

When you create a vault, a 64-character **Secure Key** is generated and shown to you once. Save it.

This key independently re-encrypts every TOTP secret you store, so if you ever forget your password and need to reset it, your codes can still be recovered. Without the Secure Key, a password reset permanently deletes all your TOTP accounts. This is intentional. We cannot recover your data for you, and neither can anyone else.

<br>

### Password hygiene in the chat

Every message you send containing a password or secret is deleted from the Telegram chat immediately after it is processed. Messages that reveal sensitive information (your Secure Key, a raw TOTP secret) are automatically deleted after 30 to 60 seconds. The chat stays clean so sensitive content does not accumulate.

<br>

### Cross-device login alerts

If your vault is accessed from a different Telegram account, the vault owner receives an alert in real time with the option to immediately log out all sessions. This protects shared-access scenarios and detects unauthorized access without any server-side monitoring of your content.

<br>

### Brute-force protection

Failed password attempts are counted and enforced at the account level. After 5 consecutive wrong passwords the account is frozen for 18 hours. Password reset attempts follow the same pattern with a 3-attempt limit before a freeze. These limits survive restarts because they are persisted in the database, not held in memory.

<br>

---

<br>

## Features

<br>

### Add your accounts, your way

You can add a TOTP account by sending a QR code image directly in the chat, pasting an `otpauth://` URI, typing a raw Base32 secret key, or going through a manual step-by-step prompt. All four methods produce the same result: an encrypted entry in your vault that generates live codes.

<br>

### Live codes with a countdown

The list view shows your current code, a visual countdown bar, and the next code in the upcoming 30-second window. You never have to tap refresh at the wrong moment.

```
Google        | gmail.com
Current Code: 482 910   ▓▓▓▓▓▓░░░░ 19s
Next code:    037 441
```

<br>

### Search without scrolling

Type `#google` anywhere in the chat, even outside any menu, and the bot instantly returns matching accounts by name or note. No navigation required.

<br>

### Short notes per account

Each account can carry a short label (up to 10 characters) to distinguish duplicates or add context. Useful when you have multiple Google or Microsoft accounts.

<br>

### Share a code without sharing a secret

The Share Codes feature generates a temporary link valid for 10 minutes. Anyone who opens it sees the live TOTP codes for the accounts you selected. They never see the secret key, the vault, or any account information. The link is encrypted per-token and deleted from the server after it expires.

<br>

### Export and import your vault

You can export your entire vault as an encrypted `.bvault` file protected by a separate file password of your choice. This file can be imported into any BV Authenticator vault, by you or anyone you share it with. Imports handle duplicate accounts gracefully with a Skip or Replace choice.

<br>

### Automatic backups on a schedule

Offline Auto Backup sends an encrypted `.bvault` file to your Telegram DM automatically, on a weekly or monthly schedule. The file is encrypted with your current account password. It auto-deletes from your chat after 3 days to keep things clean. No manual action required.

<br>

### Backup reminders

If you prefer to export manually, the bot can send you a weekly or monthly reminder nudge. Configurable in Settings, disabled by default.

<br>

---

<br>

## What data we collect

This section is direct and complete. No legal language.

<br>

| What | Why | Plaintext accessible to us? |
|---|---|---|
| Your Telegram user ID | To identify your vault | Yes |
| Your Telegram name and username | To display in your profile | Yes |
| Your TOTP secrets | To generate your codes | **No. AES-256-GCM encrypted.** |
| Your password | To authenticate you | **No. Argon2id hash only.** |
| Your Secure Key | For password reset restore | **No. AES-256-GCM encrypted.** |
| Your timezone preference | To display timestamps in your local time | Yes |
| Login timestamps | To show Last Online in your profile | Yes |
| Failed login counts | For brute-force protection | Yes (count only, no passwords) |

<br>

We do not collect:

- The plaintext of any TOTP secret, ever
- Your plaintext password at any point, including during authentication
- Any data beyond what is listed above
- Any analytics, tracking, or behavioral data

Your vault is linked to your Telegram account. Deleting your account through the bot removes all rows associated with your vault ID from every table in the database permanently. This cannot be undone.

<br>

---

<br>

## Use cases

<br>

**You switch phones often.** No migration process. Log in from any Telegram session and your vault is there, fully decrypted with your password.

**You share a device with someone.** Your vault is protected by a password they do not know. The Secure Key adds a second layer for recovery. Cross-device login triggers an alert you control.

**You manage 2FA for a team.** Export an encrypted vault file, share the file password separately, and the recipient imports it into their own vault. Each person has their own encrypted copy.

**You want passive protection without thinking about it.** Enable Offline Auto Backup and a `.bvault` file appears in your DMs on a schedule. If anything happens to the server, you have a local copy of everything.

**You need to show someone a code without handing them your phone.** Generate a Share Link. It shows live codes for 10 minutes, then disappears.

<br>

---

<br>

## Encryption libraries used

| Library | Purpose |
|---|---|
| `cryptography` | AES-256-GCM encryption/decryption via `hazmat` primitives, PBKDF2-SHA256 for export/share key derivation |
| `argon2-cffi` | Argon2id password hashing and master key derivation |
| `pyzbar` + `Pillow` | QR code image decoding |
| `python-telegram-bot` | Telegram Bot API framework |

<br>

---

<br>

## Self-hosting

BlockVeil Authenticator is fully self-hostable. The codebase is a single Python file. You bring your own Telegram bot token, set an encryption key, and deploy. Railway deployment is supported out of the box with the included Dockerfile.

The bot requires no external services beyond Telegram itself. Everything runs locally against a SQLite database.

Refer to the deployment documentation in this repository for environment variable configuration and Railway setup instructions.

<br>

---

<br>

<div align="center">

*Your codes are yours. We cannot read them. That is the point.*

<br>

[![Open in Telegram](https://img.shields.io/badge/Open%20BV%20Authenticator-2CA5E0?style=for-the-badge&logo=telegram&logoColor=white)](https://t.me/TotpNafiBot)

<br>

</div>
