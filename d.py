#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════
   INTEGRATED FIREBASE & LINK SORTER BOT v3.5 (NO CAPS)
═══════════════════════════════════════════════════════════════════
Routing rule:
  • Online devices ≥ 1  → GROUP_CHAT_ID   (group 1)
  • Online devices == 0 → GROUP_CHAT_ID3  (group 3)
  • No Firebase found   → GROUP_CHAT_ID2  (group 2)

No caps anywhere:
  • Every Firebase in a TXT is checked
  • Every panel URL inside a TXT is deep-scanned
  • Every URL in a message is processed
  • /adminscan and /adminlist return the full list
═══════════════════════════════════════════════════════════════════
"""

import os
import json
import re
import logging
import asyncio
import urllib.request
import urllib.error
import urllib.parse
import base64
import zipfile
import tempfile
from datetime import datetime
from typing import List, Dict, Optional, Set, Tuple
from collections import defaultdict

import requests
from telegram import Update, Chat
from telegram.ext import (
    Application, CommandHandler, MessageHandler, filters, ContextTypes
)
from telegram.error import TelegramError

# ── Logging ──────────────────────────────────────────────────
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logger = logging.getLogger(__name__)

# ── Config (same as sorter1.py + GROUP_CHAT_ID3) ─────────────
STORAGE_FILE        = 'data_storage.json'
GROUP_CHAT_ID       = int(os.getenv('GROUP_CHAT_ID', '-1001234567890'))   # Group 1: Online ≥ 1
GROUP_CHAT_ID2      = int(os.getenv('GROUP_CHAT_ID2', '-1001234567891'))  # Group 2: No Firebase found
GROUP_CHAT_ID3      = int(os.getenv('GROUP_CHAT_ID3', '-1001234567892'))  # Group 3: Online == 0
ADMIN_USER_IDS      = [int(x) for x in os.getenv('ADMIN_IDS', '123,456').split(',')]
SESSION_TIMEOUT     = 20
MAX_ITEMS           = 150
PANEL_TIMEOUT       = 10

# ── Tuning (only delays / chunk sizes — NOT caps) ────────────
GROUP_SEND_DELAY    = 0.7     # seconds between group sends (Telegram flood protection)
MAX_MSG_CHARS       = 3500    # chunk size for user replies (Telegram 4096 limit)
CONCURRENCY         = 8       # parallel checks — avoids overloading the network

# ── Regex Patterns ───────────────────────────────────────────
FIREBASE_REGEX = re.compile(
    r'https?://[^\s"\'<>]+\.(?:firebaseio\.com|firebasedatabase\.app)[^\s"\'<>]*',
    re.IGNORECASE
)

LINK_REGEX = re.compile(
    r'https?://[^\s"\'<>]+(?:panel|admin|dashboard|cpanel|login|signin|manage|control|api)[^\s"\'<>]*',
    re.IGNORECASE
)

URL_REGEX = re.compile(
    r'https?://[^\s"\'<>]+',
    re.IGNORECASE
)


# ══════════════════════════════════════════════════════════════════════════
#   DATA MANAGER WITH SOURCE TRACKING
# ══════════════════════════════════════════════════════════════════════════

class DataManager:
    """Manages all data with source tracking"""

    def __init__(self, storage_file: str):
        self.storage_file = storage_file
        self.items = {}
        self.sent_to_group = set()
        self.group_message_counter = 0
        self.load()

    def load(self):
        if os.path.exists(self.storage_file):
            try:
                with open(self.storage_file, 'r') as f:
                    data = json.load(f)
                    self.items = data.get('items', {})
                    self.sent_to_group = set(data.get('sent_to_group', []))
                    self.group_message_counter = data.get('group_message_counter', 0)
            except:
                pass

    def save(self):
        try:
            with open(self.storage_file, 'w') as f:
                json.dump({
                    'items': self.items,
                    'sent_to_group': list(self.sent_to_group),
                    'group_message_counter': self.group_message_counter
                }, f, indent=2)
        except Exception as e:
            logger.error(f"Save error: {e}")

    def add(self, url: str, user_id: int, item_type: str, source: str = "direct") -> Tuple[bool, bool]:
        is_new = url not in self.items

        if is_new:
            self.items[url] = {
                'user_id': user_id,
                'type': item_type,
                'source': source,
                'status': {},
                'sent_to_group': False,
                'timestamp': datetime.now().isoformat()
            }
            self.save()
        else:
            if self.items[url]['source'] != source:
                self.items[url]['source'] = source
                self.save()

        is_sent = url in self.sent_to_group
        return is_new, is_sent

    def set_status(self, url: str, status: dict):
        if url in self.items:
            self.items[url]['status'] = status
            self.save()

    def mark_sent_to_group(self, url: str):
        self.sent_to_group.add(url)
        if url in self.items:
            self.items[url]['sent_to_group'] = True
        self.save()

    def get_user_items(self, user_id: int) -> List[str]:
        return [url for url, info in self.items.items() if info['user_id'] == user_id]

    def all_urls(self) -> List[str]:
        return list(self.items.keys())

    def count(self) -> int:
        return len(self.items)

    def get_next_group_number(self) -> int:
        self.group_message_counter += 1
        self.save()
        return self.group_message_counter


dm = DataManager(STORAGE_FILE)


# ══════════════════════════════════════════════════════════════════════════
#   MESSAGE CHUNKING HELPER  (splits long replies — not a cap)
# ══════════════════════════════════════════════════════════════════════════

def chunk_message(text: str, size: int = MAX_MSG_CHARS) -> List[str]:
    """Split text into chunks that fit Telegram's 4096-char limit."""
    if len(text) <= size:
        return [text]

    chunks = []
    current = ""

    for line in text.split("\n"):
        if len(current) + len(line) + 1 > size:
            if current:
                chunks.append(current.rstrip())
            current = line + "\n"
        else:
            current += line + "\n"

    if current.strip():
        chunks.append(current.rstrip())

    return chunks


async def send_chunked(bot, text: str, chat_id: int):
    """Send text split into chunks. Sends ALL chunks — nothing truncated."""
    chunks = chunk_message(text)
    for chunk in chunks:
        await bot.send_message(
            chat_id=chat_id,
            text=chunk,
            parse_mode='Markdown',
            disable_web_page_preview=True
        )
        if len(chunks) > 1:
            await asyncio.sleep(0.4)
# ══════════════════════════════════════════════════════════════════════════
#   FIREBASE EXTRACTION ENGINE
# ══════════════════════════════════════════════════════════════════════════

def _normalize(url: str) -> str:
    url = url.strip()
    if url.endswith('/'):
        url = url.rstrip('/')
    return url


def extract_urls_from_binary(data_bytes: bytes) -> Set[str]:
    """Extract hidden Firebase URLs from binary / text data."""
    found = set()
    try:
        strings = re.findall(b'[\x20-\x7E]{4,}', data_bytes)
        for s in strings:
            try:
                text = s.decode('utf-8', errors='ignore')

                matches = re.findall(
                    r'https?://[a-zA-Z0-9_.-]+(?:firebaseio\.com|firebasedatabase\.app)',
                    text
                )
                for m in matches:
                    if "your-project" not in m:
                        found.add(_normalize(m))

                domains = re.findall(
                    r'[a-zA-Z0-9_-]+-default-rtdb\.[a-z0-9.-]+',
                    text
                )
                for d in domains:
                    if not d.startswith("http"):
                        d = "https://" + d
                    if "your-project" not in d:
                        found.add(_normalize(d))
            except:
                pass
    except:
        pass
    return found


def extract_firebase_from_apk(apk_path: str) -> Set[str]:
    """Extract Firebase from APK using deep binary string mining."""
    found = set()
    try:
        with zipfile.ZipFile(apk_path, 'r') as zf:
            for file_info in zf.filelist:
                if file_info.file_size > 2 * 1024 * 1024:
                    continue
                try:
                    data = zf.read(file_info.filename)
                    urls = extract_urls_from_binary(data)
                    found.update(urls)
                except:
                    pass
    except Exception as e:
        logger.error(f"APK extraction error: {e}")
    return found


def extract_firebase_from_url(target_url: str) -> Set[str]:
    """Deep web panel scan: query params + main page + linked JS files."""
    found: Set[str] = set()

    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Linux; Android 14; Mobile) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36"
        )
    }

    try:
        if not target_url.startswith("http"):
            target_url = "https://" + target_url

        # 1. Query params
        try:
            parsed_url = urllib.parse.urlparse(target_url)
            query_params = urllib.parse.parse_qs(parsed_url.query)
            for _, values in query_params.items():
                for val in values:
                    try:
                        padding = '=' * (-len(val) % 4)
                        dec = base64.b64decode(val + padding).decode('utf-8', errors='ignore')
                        found.update(extract_urls_from_binary(dec.encode()))
                    except:
                        pass
                    found.update(extract_urls_from_binary(val.encode()))
        except:
            pass

        # 2. Main page
        response = requests.get(
            target_url, headers=headers, timeout=15, allow_redirects=True
        )
        found.update(extract_urls_from_binary(response.content))

        # 3. Linked JS files
        try:
            js_files = re.findall(
                r'src=["\']([^"\']+\.js[^"\']*)["\']', response.text
            )
        except:
            js_files = []

        parsed_base = urllib.parse.urlparse(target_url)
        for js in js_files:
            if not js.startswith("http"):
                js_url = f"{parsed_base.scheme}://{parsed_base.netloc}" + (
                    js if js.startswith('/') else '/' + js
                )
            else:
                js_url = js
            try:
                js_resp = requests.get(js_url, headers=headers, timeout=10)
                found.update(extract_urls_from_binary(js_resp.content))
            except:
                pass

    except Exception as e:
        logger.debug(f"URL extraction error for {target_url}: {e}")

    return found


def extract_from_txt_file(raw_bytes: bytes) -> Tuple[Set[str], Set[str]]:
    """Parse a .txt file → (direct_firebase_urls, panel_urls). NO CAP."""
    firebase_urls: Set[str] = set()
    panel_urls: Set[str] = set()

    firebase_urls.update(extract_urls_from_binary(raw_bytes))

    try:
        text = raw_bytes.decode('utf-8', errors='ignore')
    except:
        text = ""

    for u in URL_REGEX.findall(text):
        u_norm = _normalize(u)
        if FIREBASE_REGEX.match(u_norm):
            firebase_urls.add(u_norm)
        else:
            panel_urls.add(u_norm)

    return firebase_urls, panel_urls


def source_emoji(source: str) -> str:
    emojis = {
        'direct': '📌',
        'extracted_link': '🔗',
        'extracted_apk': '📦',
        'extracted_txt': '📄'
    }
    return emojis.get(source, '❓')


# ══════════════════════════════════════════════════════════════════════════
#   ONLINE DEVICE COUNTER
# ══════════════════════════════════════════════════════════════════════════

def is_online_device(data) -> bool:
    if not isinstance(data, dict):
        return False
    for key in ("status", "state", "online", "isOnline", "connected", "isConnected"):
        v = data.get(key)
        if v is True or v == 1:
            return True
        if isinstance(v, str) and v.strip().lower() in {
            "true", "online", "connected", "active", "ready"
        }:
            return True
    return False


def count_online_devices(fb_url: str) -> int:
    try:
        url = fb_url.rstrip("/") + "/clients.json"
        headers = {'User-Agent': 'Mozilla/5.0'}
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=8) as resp:
            raw = resp.read().decode('utf-8', errors='ignore')
        data = json.loads(raw)
        if not isinstance(data, dict):
            return 0
        return sum(1 for v in data.values() if is_online_device(v))
    except Exception:
        return 0


def status_tag(status: dict) -> str:
    if not status:
        return "⏳ Pending check"
    if status.get('error') and not status.get('active'):
        return f"❌ Error: {status['error']}"
    active = status.get('active', False)
    online = status.get('online', 0)
    marker = "✅ ACTIVE" if active else "❌ INACTIVE"
    return f"{marker}  •  🟢 Online: {online}"


# ══════════════════════════════════════════════════════════════════════════
#   URL CHECKING
# ══════════════════════════════════════════════════════════════════════════

def check_url(url: str) -> dict:
    try:
        headers = {'User-Agent': 'Mozilla/5.0'}
        req = urllib.request.Request(url, headers=headers)

        with urllib.request.urlopen(req, timeout=5) as response:
            response.read(10240)
            online = count_online_devices(url)
            return {
                'active': True,
                'online': online,
                'timestamp': datetime.now().isoformat()
            }

    except urllib.error.HTTPError as e:
        if e.code in [401, 403]:
            online = count_online_devices(url)
            return {
                'active': True,
                'protected': True,
                'online': online,
                'error': f"HTTP {e.code} - Protected",
                'timestamp': datetime.now().isoformat()
            }
        return {
            'active': False,
            'online': 0,
            'error': f"HTTP {e.code}",
            'timestamp': datetime.now().isoformat()
        }

    except (urllib.error.URLError, Exception) as e:
        return {
            'active': False,
            'online': 0,
            'error': type(e).__name__,
            'timestamp': datetime.now().isoformat()
        }


async def check_url_async(url: str) -> dict:
    return await asyncio.to_thread(check_url, url)


async def check_many_urls(urls: List[str]) -> Dict[str, dict]:
    """
    Check ALL urls concurrently, but limited by semaphore to avoid
    network overload (this is throttling, not a cap — every URL is checked).
    """
    sem = asyncio.Semaphore(CONCURRENCY)

    async def _one(u):
        async with sem:
            return await check_url_async(u)

    tasks = [_one(u) for u in urls]
    results = await asyncio.gather(*tasks, return_exceptions=True)

    return {
        url: (result if isinstance(result, dict) else {'active': False, 'online': 0, 'error': 'Exception'})
        for url, result in zip(urls, results)
    }


def get_https_variant(url: str) -> str:
    if url.startswith("http://"):
        return "https://" + url[7:]
    return url


# ══════════════════════════════════════════════════════════════════════════
#   SMART GROUP SENDER  (routing by online count)
# ══════════════════════════════════════════════════════════════════════════

def pick_target_group(status: dict) -> int:
    online = int(status.get('online', 0) or 0)
    if online >= 1:
        return GROUP_CHAT_ID
    return GROUP_CHAT_ID3


async def send_firebase_to_group(bot, url: str, status: dict, user_id: int):
    target_group = pick_target_group(status)
    online = int(status.get('online', 0) or 0)

    try:
        msg_number = dm.get_next_group_number()

        if online >= 1:
            header = f"#{msg_number} 🔥 *Firebase with ACTIVE devices*"
        else:
            header = f"#{msg_number} 💤 *Firebase with NO active devices*"

        group_msg = (
            f"{header}\n"
            f"`{url}`\n"
            f"{status_tag(status)}\n"
            f"👤 By: `{user_id}`"
        )

        await bot.send_message(
            chat_id=target_group,
            text=group_msg,
            parse_mode='Markdown',
            disable_web_page_preview=True
        )
        dm.mark_sent_to_group(url)

        if online >= 1:
            logger.info(f"✅ Firebase → GROUP 1 (online={online}): {url}")
        else:
            logger.info(f"✅ Firebase → GROUP 3 (online=0): {url}")

        await asyncio.sleep(GROUP_SEND_DELAY)

    except TelegramError as e:
        logger.error(f"❌ Group send error: {e}")
# ══════════════════════════════════════════════════════════════════════════
#   COMMAND HANDLERS
# ══════════════════════════════════════════════════════════════════════════

async def cmd_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "📥 *Send Webpanel, APK, TXT or Firebase URL*\n"
        "I'll check the *active device numbers* on that Firebase.",
        parse_mode='Markdown'
    )


async def handle_message(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.message.from_user.id

    # ── Document (APK / TXT) ──
    if update.message.document:
        file = update.message.document
        fname = (file.file_name or "").lower()

        is_apk = fname.endswith('.apk') or file.mime_type == 'application/vnd.android.package-archive'
        is_txt = fname.endswith('.txt') or (file.mime_type or '').startswith('text/')

        if not (is_apk or is_txt):
            await update.message.reply_text("❌ Only .apk or .txt files supported")
            return

        wait_msg = await update.message.reply_text(
            f"📦 *Processing {'APK' if is_apk else 'TXT'}...*",
            parse_mode='Markdown'
        )

        try:
            tg_file = await ctx.bot.get_file(file.file_id)
            raw = bytes(await tg_file.download_as_bytearray())

            if is_apk:
                with tempfile.NamedTemporaryFile(delete=False, suffix='.apk') as tmp:
                    tmp.write(raw)
                    tmp_path = tmp.name

                found_firebase = extract_firebase_from_apk(tmp_path)
                try: os.remove(tmp_path)
                except: pass
                source_tag = "extracted_apk"
                label = "APK"
            else:
                direct_fb, panel_urls = extract_from_txt_file(raw)
                found_firebase = set(direct_fb)
                source_tag = "extracted_txt"
                label = "TXT"

                # ── Deep-scan ALL panel URLs (no cap) ──
                panel_list = list(panel_urls)   # ← no slicing
                if panel_list:
                    await wait_msg.edit_text(
                        f"🔎 *Deep-scanning {len(panel_list)} panel URL(s) from TXT...*\n"
                        f"Already found {len(found_firebase)} Firebase directly in text.",
                        parse_mode='Markdown'
                    )
                for idx, p in enumerate(panel_list, 1):
                    try:
                        extra = await asyncio.to_thread(extract_firebase_from_url, p)
                        found_firebase.update(extra)
                    except:
                        pass
                    if idx % 5 == 0:
                        try:
                            await wait_msg.edit_text(
                                f"🔎 *Deep-scanning panels:* {idx}/{len(panel_list)}...\n"
                                f"Firebase found so far: {len(found_firebase)}",
                                parse_mode='Markdown'
                            )
                        except:
                            pass

            if not found_firebase:
                try:
                    msg_number = dm.get_next_group_number()
                    group_msg = (
                        f"#{msg_number} 📦 *No Firebase Found in {label}*\n"
                        f"👤 User: {uid}"
                    )
                    await ctx.bot.send_message(
                        chat_id=GROUP_CHAT_ID2,
                        text=group_msg,
                        parse_mode='Markdown',
                        disable_web_page_preview=True
                    )
                except TelegramError as e:
                    logger.error(f"❌ Group send error: {e}")

                await wait_msg.edit_text(f"❌ No Firebase found in {label}")
                return

            total = len(found_firebase)

            await wait_msg.edit_text(
                f"🔍 *Checking {total} Firebase(s)...*\n"
                f"Please wait — every URL will be checked.",
                parse_mode='Markdown'
            )

            msg = f"📦 *{label} Analysis* - Found {total} Firebase(s)\n\n"
            done = 0

            # Process EVERY Firebase (no cap)
            for url in list(found_firebase):
                is_new, is_sent = dm.add(url, uid, "firebase", source_tag)
                result = await check_url_async(url)
                dm.set_status(url, result)

                msg += f"🔍 `{url}`\n   {status_tag(result)}\n\n"

                if not is_sent:
                    await send_firebase_to_group(ctx.bot, url, result, uid)

                done += 1
                if done % 10 == 0:
                    try:
                        await wait_msg.edit_text(
                            f"🔍 *Progress:* {done}/{total} checked...",
                            parse_mode='Markdown'
                        )
                    except:
                        pass

            try:
                await wait_msg.delete()
            except:
                pass

            # Send the full report (chunked only due to Telegram's char limit)
            await send_chunked(ctx.bot, msg, chat_id=update.effective_chat.id)

        except Exception as e:
            logger.error(f"Error: {e}")
            await update.message.reply_text(f"❌ Error: {str(e)[:60]}", parse_mode='Markdown')

        finally:
            try:
                await wait_msg.delete()
            except:
                pass

    # ── Text / URLs ──
    elif update.message.text:
        text = update.message.text

        urls = URL_REGEX.findall(text)
        if not urls:
            return

        wait_msg = await update.message.reply_text("🔗 *Analyzing...*", parse_mode='Markdown')

        try:
            user_response = ""

            # Process EVERY URL in the message (no cap)
            for url in urls:
                urls_to_check = [url]
                https_variant = get_https_variant(url)
                if https_variant != url:
                    urls_to_check.append(https_variant)

                for check_url in urls_to_check:
                    is_firebase = bool(FIREBASE_REGEX.match(check_url))

                    if is_firebase:
                        result = await check_url_async(check_url)
                        is_new, is_sent = dm.add(check_url, uid, "firebase", "direct")
                        dm.set_status(check_url, result)

                        if not is_sent:
                            await send_firebase_to_group(ctx.bot, check_url, result, uid)

                        user_response += (
                            f"🔐 *Firebase Status*\n{status_tag(result)}\n`{check_url}`\n\n"
                        )

                    else:
                        extracted = await asyncio.to_thread(
                            extract_firebase_from_url, check_url
                        )

                        if extracted:
                            user_response += (
                                f"🔗 *Deep Panel Scan* — Found {len(extracted)} Firebase(s)\n"
                                f"🌐 Target: `{check_url}`\n\n"
                            )
                            # Process EVERY extracted Firebase (no cap)
                            for fb_url in list(extracted):
                                is_new, is_sent = dm.add(fb_url, uid, "firebase", "extracted_link")
                                result = await check_url_async(fb_url)
                                dm.set_status(fb_url, result)

                                user_response += f"🔍 `{fb_url}`\n   {status_tag(result)}\n\n"

                                if not is_sent:
                                    await send_firebase_to_group(ctx.bot, fb_url, result, uid)
                        else:
                            try:
                                msg_number = dm.get_next_group_number()
                                group_msg = (
                                    f"#{msg_number} ❌ *No Firebase Found*\n"
                                    f"🔗 Source: `{check_url}`"
                                )
                                await ctx.bot.send_message(
                                    chat_id=GROUP_CHAT_ID2,
                                    text=group_msg,
                                    parse_mode='Markdown',
                                    disable_web_page_preview=True
                                )
                            except TelegramError as e:
                                logger.error(f"❌ Group send error: {e}")

                            user_response += f"🔗 No Firebase found in: `{check_url}`\n\n"

            try:
                await wait_msg.delete()
            except:
                pass

            if user_response:
                await send_chunked(ctx.bot, user_response, chat_id=update.effective_chat.id)

        except Exception as e:
            logger.error(f"Error: {e}")
            await update.message.reply_text(f"❌ Error: {str(e)[:60]}", parse_mode='Markdown')

        finally:
            try:
                await wait_msg.delete()
            except:
                pass
# ══════════════════════════════════════════════════════════════════════════
#   ADMIN HANDLERS
# ══════════════════════════════════════════════════════════════════════════

async def cmd_admin_scan(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.message.from_user.id
    if uid not in ADMIN_USER_IDS:
        logger.debug(f"Unauthorized admin attempt by {uid}")
        return

    logger.info(f"✅ Admin {uid} executed: adminscan")

    all_urls = dm.all_urls()
    if not all_urls:
        await update.message.reply_text("📭 No data", parse_mode='Markdown')
        return

    wait = await update.message.reply_text("🔄 *Scanning all items...*", parse_mode='Markdown')

    results = await check_many_urls(all_urls)

    active = [(u, results[u]) for u in all_urls if results[u].get('active')]
    inactive = [(u, results[u]) for u in all_urls if not results[u].get('active')]

    try:
        await wait.delete()
    except:
        pass

    summary = (
        f"📊 *COMPLETE SCAN SUMMARY*\n"
        f"{'═' * 40}\n\n"
        f"✅ ACTIVE: {len(active)}\n"
        f"❌ INACTIVE: {len(inactive)}\n"
        f"📦 TOTAL: {len(all_urls)}\n\n"
    )
    await update.message.reply_text(summary, parse_mode='Markdown', disable_web_page_preview=True)

    # Full listing (no cap)
    body = ""
    if active:
        body += f"✅ *ACTIVE ITEMS:*\n\n"
        for i, (u, res) in enumerate(active, 1):
            body += f"{i}. `{u}`\n   {status_tag(res)}\n\n"

    if inactive:
        body += f"\n❌ *INACTIVE ITEMS:*\n\n"
        for i, (u, res) in enumerate(inactive, 1):
            body += f"{i}. `{u}`\n   {status_tag(res)}\n\n"

    if body:
        await send_chunked(ctx.bot, body, chat_id=update.effective_chat.id)


async def cmd_admin_list(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.message.from_user.id
    if uid not in ADMIN_USER_IDS:
        logger.debug(f"Unauthorized admin attempt by {uid}")
        return

    logger.info(f"✅ Admin {uid} executed: adminlist")

    all_urls = dm.all_urls()
    if not all_urls:
        await update.message.reply_text("📭 No data", parse_mode='Markdown')
        return

    header = f"📋 *ALL ITEMS* ({len(all_urls)} total)\n\n"
    body = ""
    for i, url in enumerate(all_urls, 1):   # no slice
        item_info = dm.items[url]
        source = item_info.get('source', 'unknown')
        body += f"{i}. `{url}`\n   User: {item_info['user_id']} | Source: {source_emoji(source)}\n\n"

    await send_chunked(ctx.bot, header + body, chat_id=update.effective_chat.id)


async def cmd_admin_status(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.message.from_user.id
    if uid not in ADMIN_USER_IDS:
        logger.debug(f"Unauthorized admin attempt by {uid}")
        return

    logger.info(f"✅ Admin {uid} executed: adminstatus")

    msg = (
        f"📊 *BOT STATUS*\n\n"
        f"Total Items: {dm.count()}\n"
        f"Sent to Group: {len(dm.sent_to_group)}\n"
        f"Pending: {dm.count() - len(dm.sent_to_group)}\n"
    )

    await update.message.reply_text(msg, parse_mode='Markdown')


# ══════════════════════════════════════════════════════════════════════════
#   MAIN
# ══════════════════════════════════════════════════════════════════════════

def main():
    TOKEN = os.getenv('TELEGRAM_BOT_TOKEN', '')

    if not TOKEN:
        print("❌ TELEGRAM_BOT_TOKEN not set!")
        return

    app = Application.builder().token(TOKEN).build()

    app.add_handler(CommandHandler('start', cmd_start))
    app.add_handler(CommandHandler('adminscan', cmd_admin_scan))
    app.add_handler(CommandHandler('adminlist', cmd_admin_list))
    app.add_handler(CommandHandler('adminstatus', cmd_admin_status))

    app.add_handler(MessageHandler(
        filters.Document.ALL | (filters.TEXT & ~filters.COMMAND),
        handle_message
    ))

    print("""
    ╔════════════════════════════════════════════╗
    ║        SORTER BOT v3.5 STARTING            ║
    ║  NO CAPS — checks every Firebase           ║
    ╚════════════════════════════════════════════╝
    """)
    print(f"✅ Bot initialized")
    print(f"👥 Admins: {ADMIN_USER_IDS}")
    print(f"📤 Group 1 (online ≥ 1): {GROUP_CHAT_ID}")
    print(f"📤 Group 2 (no Firebase): {GROUP_CHAT_ID2}")
    print(f"📤 Group 3 (online == 0): {GROUP_CHAT_ID3}")
    print(f"📊 Storage: {STORAGE_FILE}")
    print(f"⏱  Group send delay: {GROUP_SEND_DELAY}s")
    print(f"⚡ Concurrency: {CONCURRENCY} parallel checks")
    print("\n🆕 v3.5 — CAPS REMOVED:")
    print("  • ✅ Every Firebase in TXT is checked (no 15-cap)")
    print("  • ✅ Every panel URL in TXT is deep-scanned (no 20-cap)")
    print("  • ✅ Every URL in a message is processed (no 10-cap)")
    print("  • ✅ /adminscan and /adminlist return full lists (no 15/30 cap)")
    print("  • ✅ Only technical delays kept (rate-limit + Telegram char split)")
    print("\nPress Ctrl+C to stop\n")

    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == '__main__':
    main()
