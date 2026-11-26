import os
import sys
import json
import base64
import ssl
import gzip
import time
import urllib3
import requests
import binascii
import asyncio
import aiohttp
import threading
import pickle
import random
from io import BytesIO
from datetime import datetime, timezone
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor

from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from google.protobuf.json_format import MessageToJson
from flask import Flask, request, jsonify
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

try:
    import orjson
    def _json_loads(s): return orjson.loads(s)
    def _json_dumps(o): return orjson.dumps(o).decode('utf-8')
    JSON_FAST = True
except ImportError:
    def _json_loads(s): return json.loads(s)
    def _json_dumps(o): return json.dumps(o)
    JSON_FAST = False

BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ACCOUNT_DIR = os.path.join(BASE_DIR, "ACCOUNT")
sys.path.insert(0, BASE_DIR)

from SHAPPNO import MajoRLoGinrEs_pb2, like_pb2, like_count_pb2, like_uid_generator_pb2 as uid_generator_pb2, visit_count_pb2
VisitInfo = visit_count_pb2.Info
from byte import encrypt_api as byte_encrypt_api, Encrypt_ID

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ============================================================
# ⚡ PERFORMANCE TUNING (শুধু এখানে বদলান)
# ============================================================
MAX_CONCURRENT_TOKENS   = 60
MAX_CONCURRENT_LIKES    = 80
MAX_CONCURRENT_VISITS   = 400

TOKEN_TIMEOUT_TOTAL     = 12
TOKEN_MAX_ATTEMPTS      = 2
TOKEN_RETRY_SLEEP       = 0.3

OAUTH_TIMEOUT_TOTAL     = 6
LIKE_TIMEOUT_TOTAL      = 5
LIKE_TIMEOUT_CONNECT    = 2

VISIT_TIMEOUT_TOTAL     = 8
VISIT_TIMEOUT_CONNECT   = 3

CHECK_TOKEN_PARALLEL    = 5
PROGRESS_EVERY          = 50

TOKEN_EXPIRY_HOURS      = 5

VISIT_TARGET_DEFAULT    = 15000
VISIT_BATCH_SIZE        = 500

# ============================================================
# CONFIG — MajorLogin
# ============================================================
MajorLoginHost  = "loginbp.ppmainecoonghj.com"
MajorLoginPath  = "/MajorLogin"
FreeFireVersion = "OB55"

GUEST_URL     = "https://100067.connect.garena.com/api/v2/oauth/guest/token:grant"
CLIENT_ID     = 100067
CLIENT_SECRET = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"

AES_KEY = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
AES_IV  = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])

RESPONSE_HEADER_LEN = 64
DEFAULT_REGION      = "BD"
DEFAULT_LANG        = "bn"

# ============================================================
# GLOBAL EXECUTORS & SESSIONS
# ============================================================
MAJOR_LOGIN_EXECUTOR = ThreadPoolExecutor(
    max_workers=MAX_CONCURRENT_TOKENS * 3,
    thread_name_prefix="majorlogin",
)

_major_login_session = requests.Session()
_major_login_session.verify = False
_adapter = HTTPAdapter(
    pool_connections=MAX_CONCURRENT_TOKENS * 3,
    pool_maxsize=MAX_CONCURRENT_TOKENS * 3,
    max_retries=Retry(total=0),
)
_major_login_session.mount("https://", _adapter)
_major_login_session.mount("http://", _adapter)

# ============================================================
# STORAGE / KEYS
# ============================================================
_default_storage = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
STORAGE_DIR = os.environ.get("STORAGE_DIR", _default_storage)
os.makedirs(STORAGE_DIR, exist_ok=True)

KEY_LIKE1 = os.environ.get("KEY_LIKE1", "shappno_codexx")
KEY_LIKE2 = os.environ.get("KEY_LIKE2", "fhhxxx")
KEY_LIKE3 = os.environ.get("KEY_LIKE3", "shappno_083737xx")
KEY_LIKE4 = os.environ.get("KEY_LIKE4", "shappno736363")

TOKEN_CACHE = {}
FAILED_TOKENS = {}
TOKEN_LOCK = threading.Lock()

tracker = defaultdict(lambda: [0, 0])
liked_cache = defaultdict(set)
TRACKER_LOCK = threading.Lock()

VISIT_TOKEN_CACHE = {}
VISIT_LOCK = threading.Lock()

BANGLADESH_OFFSET = 6 * 3600

# ============================================================
# PERSISTENT STORAGE
# ============================================================
def save_data():
    try:
        os.makedirs(STORAGE_DIR, exist_ok=True)
        with TRACKER_LOCK:
            with open(f'{STORAGE_DIR}/tracker_data.pkl', 'wb') as f:
                pickle.dump(dict(tracker), f)
            with open(f'{STORAGE_DIR}/liked_cache.pkl', 'wb') as f:
                pickle.dump({k: list(v) for k, v in liked_cache.items()}, f)
            with open(f'{STORAGE_DIR}/token_cache.pkl', 'wb') as f:
                pickle.dump(dict(TOKEN_CACHE), f)
            with open(f'{STORAGE_DIR}/failed_tokens.pkl', 'wb') as f:
                pickle.dump(dict(FAILED_TOKENS), f)
            with open(f'{STORAGE_DIR}/visit_token_cache.pkl', 'wb') as f:
                pickle.dump(dict(VISIT_TOKEN_CACHE), f)
    except Exception as e:
        print(f"Error saving data: {e}")

def load_data():
    global tracker, liked_cache, TOKEN_CACHE, FAILED_TOKENS, VISIT_TOKEN_CACHE
    try:
        os.makedirs(STORAGE_DIR, exist_ok=True)
        if os.path.exists(f'{STORAGE_DIR}/tracker_data.pkl'):
            with open(f'{STORAGE_DIR}/tracker_data.pkl', 'rb') as f:
                tracker.update(pickle.load(f))
        if os.path.exists(f'{STORAGE_DIR}/liked_cache.pkl'):
            with open(f'{STORAGE_DIR}/liked_cache.pkl', 'rb') as f:
                for k, v in pickle.load(f).items():
                    liked_cache[k] = set(v)
        if os.path.exists(f'{STORAGE_DIR}/token_cache.pkl'):
            with open(f'{STORAGE_DIR}/token_cache.pkl', 'rb') as f:
                TOKEN_CACHE.update(pickle.load(f))
        if os.path.exists(f'{STORAGE_DIR}/failed_tokens.pkl'):
            with open(f'{STORAGE_DIR}/failed_tokens.pkl', 'rb') as f:
                FAILED_TOKENS.update(pickle.load(f))
        if os.path.exists(f'{STORAGE_DIR}/visit_token_cache.pkl'):
            with open(f'{STORAGE_DIR}/visit_token_cache.pkl', 'rb') as f:
                VISIT_TOKEN_CACHE.update(pickle.load(f))
        print(f"✅ Data loaded: {len(TOKEN_CACHE)} like-tokens, {len(VISIT_TOKEN_CACHE)} visit-tokens")
    except Exception as e:
        print(f"Error loading data: {e}")

# ============================================================
# LOAD ACCOUNTS — LIKE (সব TXT format: uid:password line-by-line)
# ============================================================
def load_accounts(server_name, account_pool=1):
   
    try:
        region_file = "ind" if server_name in {"IND","BR","US","SAC","NA"} else "bd"
        filename = os.path.join(ACCOUNT_DIR, f"like_{int(account_pool)}_{region_file}.txt")

        if not os.path.exists(filename):
            print(f"⚠️ File not found: {filename}")
            return []

        accounts = []
        seen_uids = set()

        with open(filename, "r", encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                if ':' in line:
                    parts = line.split(':', 1)
                    uid, password = parts[0].strip(), parts[1].strip()
                    if uid and password and uid.isdigit() and uid not in seen_uids:
                        seen_uids.add(uid)
                        accounts.append({"uid": uid, "password": password})

        print(f"Loaded {len(accounts)} accounts from {filename}")
        return accounts

    except Exception as e:
        print(f"Error loading accounts from {filename}: {e}")
        return []

# ============================================================
# LOAD ACCOUNTS — VISIT (JSON)
# ============================================================
def load_visit_accounts(server_name):
    try:
        filename = os.path.join(ACCOUNT_DIR, "visit_ind.txt" if server_name in {"IND","BR","US","SAC","NA"} else "visit_bd.txt")
        if not os.path.exists(filename):
            print(f"⚠️ Visit accounts file not found: {filename}")
            return []

        with open(filename, "r", encoding='utf-8') as f:
            content = f.read().strip()

        accounts = []
        seen_uids = set()

        try:
            data = _json_loads(content)
            if isinstance(data, list):
                for item in data:
                    if isinstance(item, dict):
                        uid = str(item.get("uid", "")).strip()
                        password = str(item.get("password", "")).strip()
                        if uid and password and uid.isdigit() and uid not in seen_uids:
                            seen_uids.add(uid)
                            accounts.append({"uid": uid, "password": password})
            elif isinstance(data, dict):
                if "uid" in data and "password" in data:
                    uid = str(data["uid"]).strip()
                    password = str(data["password"]).strip()
                    if uid and password and uid.isdigit():
                        accounts.append({"uid": uid, "password": password})
                else:
                    for uid, password in data.items():
                        uid_s, pass_s = str(uid).strip(), str(password).strip()
                        if uid_s and pass_s and uid_s.isdigit() and uid_s not in seen_uids:
                            seen_uids.add(uid_s)
                            accounts.append({"uid": uid_s, "password": pass_s})
        except Exception:
            for line in content.splitlines():
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                if ':' in line:
                    parts = line.split(':', 1)
                    uid, password = parts[0].strip(), parts[1].strip()
                    if uid and password and uid.isdigit() and uid not in seen_uids:
                        seen_uids.add(uid)
                        accounts.append({"uid": uid, "password": password})

        print(f"Loaded {len(accounts)} visit-accounts from {filename}")
        return accounts

    except Exception as e:
        print(f"Error loading visit accounts: {e}")
        return []

# ============================================================
# PROTOBUF ENCODER
# ============================================================
def encode_varint(num: int) -> bytes:
    out = []
    while True:
        b = num & 0x7F
        num >>= 7
        if num:
            b |= 0x80
        out.append(b)
        if not num:
            break
    return bytes(out)

def create_field(num, val):
    if isinstance(val, bool):
        return encode_varint((num << 3) | 0) + encode_varint(int(val))
    if isinstance(val, int):
        return encode_varint((num << 3) | 0) + encode_varint(val)
    if isinstance(val, (str, bytes)):
        v = val.encode() if isinstance(val, str) else val
        return encode_varint((num << 3) | 2) + encode_varint(len(v)) + v
    if isinstance(val, dict):
        nested = create_packet(val)
        return encode_varint((num << 3) | 2) + encode_varint(len(nested)) + nested
    return b""

def create_packet(fields: dict) -> bytes:
    return b"".join(create_field(k, v) for k, v in fields.items())

def encrypt_api(plain_hex: str) -> str:
    plain = bytes.fromhex(plain_hex)
    cipher = AES.new(AES_KEY, AES.MODE_CBC, AES_IV)
    return cipher.encrypt(pad(plain, AES.block_size)).hex()

def _aes_decrypt(data: bytes) -> bytes:
    try:
        cipher = AES.new(AES_KEY, AES.MODE_CBC, AES_IV)
        dec = cipher.decrypt(data)
        padlen = dec[-1]
        if 1 <= padlen <= 16 and all(b == padlen for b in dec[-padlen:]):
            dec = dec[:-padlen]
        return dec
    except Exception:
        return b""

def decode_response(resp: bytes):
    def _try_parse(blob):
        if not blob: return None
        try:
            m = MajoRLoGinrEs_pb2.MajorLoginRes()
            m.ParseFromString(blob)
            if m.account_id > 0 and (m.lock_region or m.noti_region or m.token):
                return m
        except Exception:
            pass
        return None

    m = _try_parse(resp)
    if m: return m, "plaintext proto", resp
    if len(resp) > RESPONSE_HEADER_LEN:
        m = _try_parse(resp[RESPONSE_HEADER_LEN:])
        if m: return m, f"plaintext (skip {RESPONSE_HEADER_LEN}B)", resp[RESPONSE_HEADER_LEN:]
    if len(resp) >= 16 and len(resp) % 16 == 0:
        dec = _aes_decrypt(resp)
        if dec:
            m = _try_parse(dec)
            if m: return m, "AES-CBC", dec
            if len(dec) > RESPONSE_HEADER_LEN:
                m = _try_parse(dec[RESPONSE_HEADER_LEN:])
                if m: return m, f"AES-CBC (skip {RESPONSE_HEADER_LEN}B)", dec[RESPONSE_HEADER_LEN:]
    return None, "unknown", resp

def decode_jwt(token: str) -> dict:
    try:
        if not token or not isinstance(token, str): return {}
        parts = token.split(".")
        if len(parts) != 3: return {}
        payload_b64 = parts[1] + "=" * (-len(parts[1]) % 4)
        raw = base64.urlsafe_b64decode(payload_b64)
        return _json_loads(raw.decode("utf-8"))
    except Exception:
        return {}

def build_major_login_body(access_token, open_id, region=DEFAULT_REGION, lang=DEFAULT_LANG) -> bytes:
    fields = {
        3: datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        4: "free fire", 5: 1, 7: "1.132.4",
        8: "Android OS 15 / API-35 (AP3A.240617.008/T.R4T2.24e2a71-650ec)",
        9: "Handheld", 10: "airtel now cirkle", 11: "WIFI",
        12: 1666, 13: 750, 14: "360", 15: "ARM64 FP ASIMD AES | 2000 | 8",
        16: 7723, 17: "Mali-G52 MC2",
        18: "OpenGL ES 3.2 v1.r49p1-03bet0.19498e0ae1d5dac223383c39a2e58f04",
        19: "Google|3744f365-78fe-424a-871e-f77a0a095356",
        20: "103.109.214.50", 21: lang, 22: open_id, 23: "8", 24: "Handheld",
        25: "realme RMX3710", 26: region, 29: access_token, 30: 1,
        41: "airtel now cirkle", 42: "WIFI",
        57: "7428b253defc164018c604a1ebbfebdf",
        60: 225554, 61: 155321, 62: 733, 64: 155845, 65: 225554, 66: 155845, 67: 225554,
        73: 2, 74: "/data/app/~~ln8dFa29BUuPBtG4A-WwXQ==/com.dts.freefireth-tXx7bnxvKbykwJzwnEHs2Q==/lib/arm64",
        76: 1,
        77: "b8e0cd5e295eee42f5860d3c86e483dd|/data/app/~~ln8dFa29BUuPBtG4A-WwXQ==/com.dts.freefireth-tXx7bnxvKbykwJzwnEHs2Q==/base.apk",
        78: 3, 79: 2, 81: "64", 83: "2019121229", 85: 3, 86: "OpenGLES2", 87: 8191, 88: 8, 92: 9754,
        93: "android",
        94: "KqsHT+PFj/2sTPjf+unI9C5rnnStUzOFVqOADw9TI8tgL2bTnmzrBM/dEzyqy4BtAVua+w9mgLRIMrjXa67/qXm0pz5uQWsxC6sd8Um7OmMNHRmy",
        95: 111207, 96: '{"cur_rate":[60,45,90],"support_etc2":false}', 97: 1, 99: "4", 100: "4",
        102: "4455414f055f5f0336", 104: 52972, 105: 1,
        106: "https://dl-bs.ggpolarbear.com/live/ABHotUpdates/|https://core-bs.ggpolarbear.com/live/ABHotUpdates/|6b2078db9d22dd98f8e9386a39af8462",
        107: "c8e41b7a93f02d56e1a94c7b8203f5d1",
    }
    return create_packet(fields)

# ============================================================
# MAJOR LOGIN — single account token (for internal check)
# ============================================================
async def _async_oauth(session, uid, password):
    headers = {
        "User-Agent": "GarenaMSDK/4.0.42(M2006C3LII ;Android 10;en;IN;app 1.126.2 2019120816;)",
        "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8",
    }
    payload = {
        "client_id": CLIENT_ID, "client_secret": CLIENT_SECRET, "client_type": 2,
        "password": password, "response_type": "token", "uid": int(uid),
    }
    try:
        async with session.post(
            GUEST_URL, headers=headers, json=payload,
            timeout=aiohttp.ClientTimeout(total=OAUTH_TIMEOUT_TOTAL, connect=3)
        ) as r:
            if r.status == 200:
                j = await r.json()
                if j.get("code") == 0:
                    d = j.get("data", {}) or {}
                    return d.get("access_token"), d.get("open_id")
    except Exception:
        pass
    return None, None


def _sync_major_login(access_token, open_id, region=DEFAULT_REGION, lang=DEFAULT_LANG):
    try:
        plaintext = build_major_login_body(access_token, open_id, region, lang)
        body = bytes.fromhex(encrypt_api(plaintext.hex()))
        r = _major_login_session.post(
            f"https://{MajorLoginHost}{MajorLoginPath}",
            data=body,
            headers={
                'User-Agent': 'UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)',
                'Accept': '*/*',
                'Accept-Encoding': 'deflate, gzip',
                'Authorization': 'Bearer',
                'X-Ga': 'v1 1',
                'X-Ga-Sv': '1789556611',
                'Releaseversion': FreeFireVersion,
                'Content-Type': 'application/x-www-form-urlencoded',
                'X-Unity-Version': '2018.4.12f1',
            },
            timeout=TOKEN_TIMEOUT_TOTAL,
        )
        if r.status_code in (200, 201):
            raw = r.content
            if r.headers.get("Content-Encoding") == "gzip":
                with gzip.GzipFile(fileobj=BytesIO(raw)) as f:
                    raw = f.read()
            return raw, None
        return None, f"HTTP {r.status_code}"
    except Exception as e:
        return None, str(e)


async def generate_jwt_token(session, uid, password, region=DEFAULT_REGION, lang=DEFAULT_LANG):
    """Internal helper — like check_token-এর জন্য"""
    loop = asyncio.get_event_loop()
    for attempt in range(TOKEN_MAX_ATTEMPTS):
        try:
            at, oid = await _async_oauth(session, uid, password)
            if not at or not oid:
                if attempt < TOKEN_MAX_ATTEMPTS - 1:
                    await asyncio.sleep(TOKEN_RETRY_SLEEP)
                continue

            raw, err = await loop.run_in_executor(
                MAJOR_LOGIN_EXECUTOR, _sync_major_login, at, oid, region, lang
            )
            if not raw:
                if attempt < TOKEN_MAX_ATTEMPTS - 1:
                    await asyncio.sleep(TOKEN_RETRY_SLEEP)
                continue

            res, mode, _ = decode_response(raw)
            if not res or not res.token:
                if attempt < TOKEN_MAX_ATTEMPTS - 1:
                    await asyncio.sleep(TOKEN_RETRY_SLEEP)
                continue

            token = res.token
            try:
                payload = decode_jwt(token)
                exp = payload.get("exp", int(time.time()) + (TOKEN_EXPIRY_HOURS * 3600))
            except Exception:
                exp = int(time.time()) + (TOKEN_EXPIRY_HOURS * 3600)

            expires_at = datetime.fromtimestamp(exp, tz=timezone.utc)
            TOKEN_CACHE[uid] = {"token": token, "expires_at": expires_at}
            VISIT_TOKEN_CACHE[uid] = {"token": token, "expires_at": expires_at}
            if uid in FAILED_TOKENS:
                del FAILED_TOKENS[uid]
            return token

        except asyncio.TimeoutError:
            pass
        except aiohttp.ClientError:
            pass
        except Exception:
            pass

        if attempt < TOKEN_MAX_ATTEMPTS - 1:
            await asyncio.sleep(TOKEN_RETRY_SLEEP)

    FAILED_TOKENS[uid] = {'timestamp': time.time()}
    return None

# ============================================================
# ⚡ TWO-PHASE BATCH TOKEN GENERATION
# ============================================================
async def generate_tokens_batch(accounts, region=DEFAULT_REGION, lang=DEFAULT_LANG):
    if not accounts:
        return {}

    total = len(accounts)
    print(f"🔥 {total} accounts → 2-phase token gen (OAuth + MajorLogin)")

    # ========== PHASE 1: সব OAuth parallel ==========
    oauth_results = {}
    sem_oauth = asyncio.Semaphore(MAX_CONCURRENT_TOKENS)

    connector_oauth = aiohttp.TCPConnector(
        limit=MAX_CONCURRENT_TOKENS * 2,
        limit_per_host=MAX_CONCURRENT_TOKENS * 2,
        ttl_dns_cache=1800,
        enable_cleanup_closed=True,
        force_close=False,
        keepalive_timeout=60,
    )

    start = time.time()
    oauth_done = {"n": 0, "ok": 0}

    async with aiohttp.ClientSession(connector=connector_oauth) as session:
        async def do_oauth(acc):
            async with sem_oauth:
                at, oid = await _async_oauth(session, acc['uid'], acc['password'])
                oauth_done["n"] += 1
                if at and oid:
                    oauth_results[acc['uid']] = (at, oid)
                    oauth_done["ok"] += 1
                if oauth_done["n"] % PROGRESS_EVERY == 0:
                    print(f"  [OAuth] {oauth_done['n']}/{total} "
                          f"(ok: {oauth_done['ok']}) ({round(time.time()-start,1)}s)")
                return (acc['uid'], at, oid)

        tasks = [asyncio.create_task(do_oauth(acc)) for acc in accounts]

        failed_oauth_uids = []
        for fut in asyncio.as_completed(tasks):
            try:
                uid, at, oid = await fut
                if not (at and oid):
                    failed_oauth_uids.append(uid)
            except Exception:
                pass

        if failed_oauth_uids:
            print(f"🔄 Retrying {len(failed_oauth_uids)} failed OAuth...")
            uid_to_acc = {acc['uid']: acc for acc in accounts}
            retry_tasks = [
                asyncio.create_task(do_oauth(uid_to_acc[uid]))
                for uid in failed_oauth_uids if uid in uid_to_acc
            ]
            for fut in asyncio.as_completed(retry_tasks):
                try: await fut
                except Exception: pass

    oauth_elapsed = round(time.time() - start, 2)
    print(f"✅ OAuth done: {len(oauth_results)}/{total} in {oauth_elapsed}s")

    if not oauth_results:
        print("❌ No OAuth success — aborting")
        return {}

    # ========== PHASE 2: সব MajorLogin parallel ==========
    tokens = {}
    sem_major = asyncio.Semaphore(MAX_CONCURRENT_TOKENS)
    major_start = time.time()
    major_done = {"n": 0, "ok": 0}

    loop = asyncio.get_event_loop()

    async def do_major(uid, at, oid):
        async with sem_major:
            try:
                raw, err = await loop.run_in_executor(
                    MAJOR_LOGIN_EXECUTOR, _sync_major_login, at, oid, region, lang
                )
                major_done["n"] += 1
                if raw:
                    res, mode, _ = decode_response(raw)
                    if res and res.token:
                        token = res.token
                        try:
                            payload = decode_jwt(token)
                            exp = payload.get("exp", int(time.time()) + (TOKEN_EXPIRY_HOURS * 3600))
                        except Exception:
                            exp = int(time.time()) + (TOKEN_EXPIRY_HOURS * 3600)

                        expires_at = datetime.fromtimestamp(exp, tz=timezone.utc)
                        TOKEN_CACHE[uid] = {"token": token, "expires_at": expires_at}
                        VISIT_TOKEN_CACHE[uid] = {"token": token, "expires_at": expires_at}
                        if uid in FAILED_TOKENS:
                            del FAILED_TOKENS[uid]
                        tokens[uid] = token
                        major_done["ok"] += 1
                        if major_done["n"] % PROGRESS_EVERY == 0:
                            print(f"  [Major] {major_done['n']}/{len(oauth_results)} "
                                  f"(ok: {major_done['ok']}) ({round(time.time()-major_start,1)}s)")
                        return True
                FAILED_TOKENS[uid] = {'timestamp': time.time()}
                return False
            except Exception:
                FAILED_TOKENS[uid] = {'timestamp': time.time()}
                return False

    major_tasks = [
        asyncio.create_task(do_major(uid, at, oid))
        for uid, (at, oid) in oauth_results.items()
    ]
    for fut in asyncio.as_completed(major_tasks):
        try: await fut
        except Exception: pass

    major_elapsed = round(time.time() - major_start, 2)
    total_elapsed = round(time.time() - start, 2)
    print(f"✅ MajorLogin done: {len(tokens)}/{len(oauth_results)} in {major_elapsed}s")
    # One final retry pass for every UID/password pair that failed the first complete run.
    missing_accounts = [acc for acc in accounts if acc["uid"] not in tokens]
    if missing_accounts:
        print(f"🔁 Final JWT retry pass: {len(missing_accounts)} failed accounts")
        retry_connector = aiohttp.TCPConnector(
            limit=MAX_CONCURRENT_TOKENS * 2, ttl_dns_cache=1800
        )
        async with aiohttp.ClientSession(connector=retry_connector) as retry_session:
            retry_sem = asyncio.Semaphore(MAX_CONCURRENT_TOKENS)
            async def retry_one(acc):
                async with retry_sem:
                    tok = await generate_jwt_token(
                        retry_session, acc["uid"], acc["password"], region, lang
                    )
                    if tok:
                        tokens[acc["uid"]] = tok
                    return tok
            await asyncio.gather(*(retry_one(acc) for acc in missing_accounts),
                                 return_exceptions=True)

    total_elapsed = round(time.time() - start, 2)
    print(f"🎉 Total: {len(tokens)}/{total} tokens in {total_elapsed}s "
          f"(OAuth {oauth_elapsed}s + Major {major_elapsed}s + final retry)")
    return tokens

# ============================================================
# LIKE SENDING
# ============================================================
async def send_like(session, encrypted_uid, token, url):
    try:
        edata = bytes.fromhex(encrypted_uid)
        headers = {
            'User-Agent': "Dalvik/2.1.0 (Linux; U; Android 9; ASUS_Z01QD Build/PI)",
            'Authorization': f"Bearer {token}",
            'Content-Type': "application/x-www-form-urlencoded",
            'X-GA': "v1 1", 'ReleaseVersion': "OB55"
        }
        async with session.post(
            url, data=edata, headers=headers,
            timeout=aiohttp.ClientTimeout(total=LIKE_TIMEOUT_TOTAL, connect=LIKE_TIMEOUT_CONNECT)
        ) as response:
            return response.status
    except Exception:
        return 500

async def send_likes_batch(target_uid, encrypted_uid, accounts_with_tokens, url):
    if not accounts_with_tokens:
        return 0, 0
    semaphore = asyncio.Semaphore(MAX_CONCURRENT_LIKES)
    successful = 0
    failed = 0
    connector = aiohttp.TCPConnector(
        limit=MAX_CONCURRENT_LIKES * 3,
        limit_per_host=MAX_CONCURRENT_LIKES * 3,
        ttl_dns_cache=1800,
        enable_cleanup_closed=True,
        force_close=False,
        keepalive_timeout=60,
        use_dns_cache=True,
    )
    async with aiohttp.ClientSession(connector=connector) as session:
        async def send_one(acc, token):
            nonlocal successful, failed
            status = await send_like(session, encrypted_uid, token, url)
            if status == 200:
                with TRACKER_LOCK:
                    liked_cache[target_uid].add(acc['uid'])
                successful += 1
            else:
                failed += 1
        async def limited(acc, token):
            async with semaphore:
                await send_one(acc, token)
        tasks = [asyncio.create_task(limited(acc, tok)) for acc, tok in accounts_with_tokens]
        for fut in asyncio.as_completed(tasks):
            try: await fut
            except Exception: pass
    return successful, failed

async def send_all_likes(target_uid, server_name, url, accounts, encrypted_uid):
    if not accounts:
        return {'success': 0, 'failed': 0, 'total': 0, 'already_liked': 0}

    with TRACKER_LOCK:
        already_liked = liked_cache.get(target_uid, set())
        fresh = [acc for acc in accounts if acc['uid'] not in already_liked]

    print(f"Total: {len(accounts)}, Fresh: {len(fresh)}, Already liked: {len(already_liked)}")
    if not fresh:
        return {'success': 0, 'failed': 0, 'total': len(accounts),
                'already_liked': len(already_liked), 'fresh_used': 0}

    random.shuffle(fresh)
    need_tokens = []
    have_tokens = []
    for acc in fresh:
        if acc['uid'] in TOKEN_CACHE:
            cached = TOKEN_CACHE[acc['uid']]
            remaining = (cached["expires_at"] - datetime.now(timezone.utc)).total_seconds()
            if remaining > 0:
                have_tokens.append((acc, cached["token"]))
                continue
        need_tokens.append(acc)

    print(f"📊 Valid tokens: {len(have_tokens)} | Need: {len(need_tokens)}")

    tokens_dict = {}
    if need_tokens:
        print(f"🔄 Generating {len(need_tokens)} tokens...")
        region = server_name if server_name in {"IND","BR","US","SAC","NA"} else "BD"
        tokens_dict = await generate_tokens_batch(need_tokens, region=region)
        save_data()

    all_ready = list(have_tokens)
    for acc in fresh:
        if acc['uid'] in tokens_dict and tokens_dict[acc['uid']]:
            all_ready.append((acc, tokens_dict[acc['uid']]))

    print(f"✅ {len(all_ready)} accounts ready")
    if not all_ready:
        return {'success': 0, 'failed': len(fresh), 'total': len(accounts)}

    print(f"🚀 Sending {len(all_ready)} likes (limit {MAX_CONCURRENT_LIKES})...")
    start = time.time()
    successful, failed = await send_likes_batch(target_uid, encrypted_uid, all_ready, url)
    print(f"✅ Likes: {successful} ok, {failed} failed in {round(time.time()-start,2)}s")

    save_data()
    return {
        'success': successful, 'failed': failed, 'total': len(accounts),
        'already_liked': len(already_liked), 'fresh_used': len(all_ready)
    }

def get_valid_token_sync(uid):
    if uid in TOKEN_CACHE:
        cached = TOKEN_CACHE[uid]
        remaining = (cached["expires_at"] - datetime.now(timezone.utc)).total_seconds()
        if remaining > 0:
            return cached["token"]
    return None

def get_valid_visit_token_sync(uid):
    if uid in VISIT_TOKEN_CACHE:
        cached = VISIT_TOKEN_CACHE[uid]
        remaining = (cached["expires_at"] - datetime.now(timezone.utc)).total_seconds()
        if remaining > 0:
            return cached["token"]
    return None

# ============================================================
# AES / PROTOBUF (like system)
# ============================================================
def encrypt_message(plaintext):
    key = b'Yg&tc%DEuh6%Zc^8'
    iv = b'6oyZDr22E3ychjM%'
    cipher = AES.new(key, AES.MODE_CBC, iv)
    padded = pad(plaintext, AES.block_size)
    return binascii.hexlify(cipher.encrypt(padded)).decode('utf-8')

def enc(uid):
    message = uid_generator_pb2.uid_generator()
    message.krishna_ = int(uid)
    message.teamXdarks = 1
    return encrypt_message(message.SerializeToString())

def decode_protobuf(binary):
    try:
        items = like_count_pb2.Info()
        items.ParseFromString(binary)
        return items
    except Exception:
        return None

def get_player_info(encrypted_uid, server_name, token):
    if server_name == "IND":
        url = "https://client.ind.freefiremobile.com/GetPlayerPersonalShow"
    elif server_name in {"BR","US","SAC","NA"}:
        url = "https://client.us.freefiremobile.com/GetPlayerPersonalShow"
    else:
        url = "https://clientbp.ppmainecoonghj.com/GetPlayerPersonalShow"

    headers = {
        'User-Agent': "Dalvik/2.1.0 (Linux; U; Android 9; ASUS_Z01QD Build/PI)",
        'Authorization': f"Bearer {token}",
        'Content-Type': "application/x-www-form-urlencoded",
        'X-GA': "v1 1", 'ReleaseVersion': "OB55"
    }
    try:
        r = requests.post(url, data=bytes.fromhex(encrypted_uid), headers=headers, verify=False, timeout=8)
        if r.status_code != 200:
            print(f"❌ GetPlayerInfo {r.status_code}")
            return None
        return decode_protobuf(r.content)
    except Exception as e:
        print(f"❌ Request Exception: {e}")
        return None

# ============================================================
# VISIT SYSTEM
# ============================================================
def get_visit_url(server_name):
    if server_name == "IND":
        return "https://client.ind.freefiremobile.com/GetPlayerPersonalShow"
    elif server_name in {"BR","US","SAC","NA"}:
        return "https://client.us.freefiremobile.com/GetPlayerPersonalShow"
    else:
        return "https://clientbp.ppmainecoonghj.com/GetPlayerPersonalShow"


def build_visit_payload(uid):
    try:
        encrypted_id = Encrypt_ID(str(uid))
        if not encrypted_id:
            return None
        hex_plain = "08" + encrypted_id + "1801"
        encrypted_hex = byte_encrypt_api(hex_plain)
        return bytes.fromhex(encrypted_hex)
    except Exception as e:
        print(f"❌ build_visit_payload error: {e}")
        return None


def parse_visit_response(response_data):
    try:
        info = VisitInfo()
        info.ParseFromString(response_data)
        return {
            "uid": info.AccountInfo.UID if info.AccountInfo.UID else 0,
            "nickname": info.AccountInfo.PlayerNickname if info.AccountInfo.PlayerNickname else "",
            "likes": info.AccountInfo.Likes if info.AccountInfo.Likes else 0,
            "region": info.AccountInfo.PlayerRegion if info.AccountInfo.PlayerRegion else "",
            "level": info.AccountInfo.Levels if info.AccountInfo.Levels else 0
        }
    except Exception as e:
        print(f"❌ visit parse error: {e}")
        return None


async def send_visit(session, url, token, data):
    headers = {
        "ReleaseVersion": "OB55",
        "X-GA": "v1 1",
        "Authorization": f"Bearer {token}",
        "Host": url.replace("https://", "").split("/")[0]
    }
    try:
        async with session.post(
            url, headers=headers, data=data, ssl=False,
            timeout=aiohttp.ClientTimeout(total=VISIT_TIMEOUT_TOTAL, connect=VISIT_TIMEOUT_CONNECT)
        ) as resp:
            if resp.status == 200:
                response_data = await resp.read()
                return True, response_data
            return False, None
    except Exception:
        return False, None


async def send_visits_parallel(target_uid, server_name, accounts, target_success=VISIT_TARGET_DEFAULT):
    if not accounts:
        return {"error": "No visit accounts"}

    url = get_visit_url(server_name)
    region = server_name if server_name in {"IND","BR","US","SAC","NA"} else "BD"

    print(f"🔑 Preparing tokens for {len(accounts)} visit accounts...")

    accounts_with_tokens = []
    accounts_need_tokens = []
    for acc in accounts:
        cached_tok = get_valid_visit_token_sync(acc['uid'])
        if cached_tok:
            accounts_with_tokens.append((acc, cached_tok))
        else:
            accounts_need_tokens.append(acc)

    print(f"📊 Visit tokens: {len(accounts_with_tokens)} cached | {len(accounts_need_tokens)} need")

    if accounts_need_tokens:
        print(f"🔄 Generating {len(accounts_need_tokens)} visit tokens...")
        tokens_dict = await generate_tokens_batch(accounts_need_tokens, region=region)
        for acc in accounts_need_tokens:
            if acc['uid'] in tokens_dict and tokens_dict[acc['uid']]:
                accounts_with_tokens.append((acc, tokens_dict[acc['uid']]))
        save_data()

    if not accounts_with_tokens:
        return {"error": "No valid visit tokens"}

    tokens_list = [tok for _, tok in accounts_with_tokens]
    print(f"✅ {len(tokens_list)} visit tokens ready")

    visit_data = build_visit_payload(target_uid)
    if not visit_data:
        return {"error": "Failed to build visit payload (invalid UID?)"}

    total_success = 0
    total_sent = 0
    first_success_response = None
    player_info = None

    connector = aiohttp.TCPConnector(
        limit=MAX_CONCURRENT_VISITS * 2,
        limit_per_host=MAX_CONCURRENT_VISITS * 2,
        ttl_dns_cache=1800,
        enable_cleanup_closed=True,
        force_close=False,
        keepalive_timeout=60,
    )

    start = time.time()
    semaphore = asyncio.Semaphore(MAX_CONCURRENT_VISITS)

    async with aiohttp.ClientSession(connector=connector) as session:
        while total_success < target_success:
            batch_size = min(target_success - total_success, VISIT_BATCH_SIZE)
            if batch_size <= 0:
                break

            async def one_visit(idx):
                async with semaphore:
                    tok = tokens_list[(total_sent + idx) % len(tokens_list)]
                    return await send_visit(session, url, tok, visit_data)

            tasks = [asyncio.create_task(one_visit(i)) for i in range(batch_size)]
            results = await asyncio.gather(*tasks, return_exceptions=True)

            if first_success_response is None:
                for res in results:
                    if isinstance(res, tuple) and res[0] and res[1]:
                        first_success_response = res[1]
                        player_info = parse_visit_response(res[1])
                        break

            batch_success = sum(1 for r in results if isinstance(r, tuple) and r[0])
            total_success += batch_success
            total_sent += batch_size

            elapsed = round(time.time() - start, 2)
            print(f"  [Visit] Batch: {batch_size}, Success: {batch_success}, "
                  f"Total: {total_success}/{target_success}, Elapsed: {elapsed}s")

            if batch_success == 0:
                print(f"⚠️ Batch of {batch_size} all failed — refreshing tokens...")
                with VISIT_LOCK:
                    for acc in accounts:
                        VISIT_TOKEN_CACHE.pop(acc['uid'], None)
                tokens_dict = await generate_tokens_batch(accounts, region=region)
                tokens_list = [t for t in tokens_dict.values() if t]
                if not tokens_list:
                    print(f"❌ No tokens after refresh — aborting")
                    break

    elapsed = round(time.time() - start, 2)
    print(f"✅ Visit done: {total_success}/{target_success} in {elapsed}s ({total_sent} sent)")

    return {
        "total_success": total_success,
        "total_sent": total_sent,
        "target": target_success,
        "elapsed": elapsed,
        "player_info": player_info,
    }


# ============================================================
# MAIN LIKE REQUEST
# ============================================================
def process_like_request(uid, server_name, client_ip, account_pool=1, api_key=None):
    expected_key = {1: KEY_LIKE1, 2: KEY_LIKE2, 3: KEY_LIKE3, 4: KEY_LIKE4}.get(int(account_pool))
    if api_key != expected_key:
        return jsonify({"error": "Invalid API Key"}), 403
    if not uid or not server_name:
        return jsonify({"error": "UID and server_name required"}), 400

    valid_servers = ["IND","BR","US","SAC","NA","BD","RU","ME","ID"]
    if server_name not in valid_servers:
        return jsonify({"error": f"Invalid server. Use: {valid_servers}"}), 400

    accounts = load_accounts(server_name, account_pool)
    if not accounts:
        return jsonify({"error": f"No accounts for {server_name}."}), 500

    check_token = None
    for account in accounts:
        tok = get_valid_token_sync(account['uid'])
        if tok:
            check_token = tok
            break

    if not check_token:
        region = server_name if server_name in {"IND","BR","US","SAC","NA"} else "BD"
        # Generate tokens for the complete pool; generate_tokens_batch performs
        # one final retry for every UID/password that failed its first full pass.
        token_map = asyncio.run(generate_tokens_batch(accounts, region=region))
        check_token = next(iter(token_map.values()), None)

    if not check_token:
        return jsonify({"error": "Token generation failed."}), 500

    encrypted_uid = enc(uid)
    before = get_player_info(encrypted_uid, server_name, check_token)
    if before is None:
        return jsonify({"error": "Invalid UID or server"}), 200

    try:
        before_data = _json_loads(MessageToJson(before))
        before_like = int(before_data['AccountInfo'].get('Likes', 0))
    except Exception:
        return jsonify({"error": "Data parsing failed"}), 200

    if server_name == "IND":
        like_url = "https://client.ind.freefiremobile.com/LikeProfile"
    elif server_name in {"BR","US","SAC","NA"}:
        like_url = "https://client.us.freefiremobile.com/LikeProfile"
    else:
        like_url = "https://clientbp.ppmainecoonghj.com/LikeProfile"

    asyncio.run(send_all_likes(uid, server_name, like_url, accounts, encrypted_uid))

    after = get_player_info(encrypted_uid, server_name, check_token)
    if after is None:
        return jsonify({"error": "Could not verify likes."}), 200

    try:
        after_data = _json_loads(MessageToJson(after))
        after_like = int(after_data['AccountInfo']['Likes'])
        player_id = int(after_data['AccountInfo']['UID'])
        player_name = str(after_data['AccountInfo']['PlayerNickname'])
        like_given = after_like - before_like

        if like_given > 0:
            with TRACKER_LOCK:
                tracker[client_ip][0] += 1
        save_data()

        return jsonify({
            "success": True,
            "LikesGivenByAPI": like_given,
            "LikesafterCommand": after_like,
            "LikesbeforeCommand": before_like,
            "PlayerNickname": player_name,
            "UID": player_id,
            "status": 1 if like_given > 0 else 2
        })
    except Exception as e:
        return jsonify({"error": str(e), "status": 0}), 500

# ============================================================
# VISIT ENDPOINT
# ============================================================
def handle_visit():
    uid = request.args.get("uid", "").strip()
    server_name = request.args.get("server_name", "BD").upper()
    target = request.args.get("target", str(VISIT_TARGET_DEFAULT))

    if not uid or not uid.isdigit():
        return jsonify({"error": "Invalid UID"}), 400

    valid_servers = ["IND","BR","US","SAC","NA","BD","RU","ME","ID"]
    if server_name not in valid_servers:
        return jsonify({"error": f"Invalid server. Use: {valid_servers}"}), 400

    try:
        target_success = int(target)
    except ValueError:
        target_success = VISIT_TARGET_DEFAULT

    accounts = load_visit_accounts(server_name)
    if not accounts:
        return jsonify({"error": f"No visit accounts for {server_name}. Check visit_bd.txt / visit_ind.txt"}), 500

    print(f"🚀 Visit request: UID={uid}, Server={server_name}, Target={target_success}")

    result = asyncio.run(send_visits_parallel(uid, server_name, accounts, target_success))

    if "error" in result:
        return jsonify({"error": result["error"]}), 500

    player_info = result.get("player_info")
    if player_info:
        return jsonify({
            "fail": target_success - result["total_success"],
            "level": player_info.get("level", 0),
            "likes": player_info.get("likes", 0),
            "nickname": player_info.get("nickname", ""),
            "region": player_info.get("region", ""),
            "success": result["total_success"],
            "uid": player_info.get("uid", 0),
            "total_sent": result["total_sent"],
            "elapsed": result["elapsed"],
        }), 200
    else:
        return jsonify({
            "error": "Could not decode player info",
            "success": result["total_success"],
            "total_sent": result["total_sent"],
            "elapsed": result["elapsed"],
        }), 500

# ============================================================
# ENDPOINTS
# ============================================================
def handle_like1():
    return process_like_request(
        request.args.get("uid"),
        request.args.get("server_name", "").upper(),
        request.remote_addr, account_pool=1, api_key=request.args.get("key")
    )

def handle_like2():
    return process_like_request(
        request.args.get("uid"),
        request.args.get("server_name", "").upper(),
        request.remote_addr, account_pool=2, api_key=request.args.get("key")
    )

def handle_like3():
    return process_like_request(
        request.args.get("uid"),
        request.args.get("server_name", "").upper(),
        request.remote_addr, account_pool=3, api_key=request.args.get("key")
    )

def handle_like4():
    return process_like_request(
        request.args.get("uid"),
        request.args.get("server_name", "").upper(),
        request.remote_addr, account_pool=4, api_key=request.args.get("key")
    )

# ============================================================
# STARTUP
# ============================================================
load_data()

