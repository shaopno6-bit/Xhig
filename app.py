import re
import io
import asyncio
import time
import httpx
import json
import threading
import shutil
import random
import binascii
from collections import defaultdict
from functools import wraps
from flask import Flask, request, jsonify, make_response, Response, Blueprint, current_app
from flask_cors import CORS
from cachetools import TTLCache
from typing import Tuple
import jwt as pyjwt
from SHAPPNO import FreeFire_pb2, main_pb2, AccountPersonalShow_pb2, GetWishListItems_pb2
from SHAPPNO import MajoRLoGinrEs_pb2
from SHAPPNO import RemoveFriend_Req_pb2, uid_generator_pb2
from SHAPPNO import ReqCLan_pb2, QuitClanReq_pb2
from SHAPPNO import nick_data_pb2
from SHAPPNO import data_pb2 as profile_item_pb2
from google.protobuf import json_format, message
from google.protobuf.message import Message
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad as crypto_pad
import base64
import os
import sys
import ssl
import gzip
import http.client
import urllib3
import requests
from io import BytesIO
import datetime
from datetime import datetime as dt, timezone, timedelta, time as dt_time
from byte import Encrypt_ID, encrypt_api
from PIL import Image, ImageDraw, ImageFont, ImageFilter
from concurrent.futures import ThreadPoolExecutor, as_completed
import logging
import hashlib
import unicodedata
from functools import lru_cache
from urllib.parse import urlencode
from types import SimpleNamespace
import aiohttp

logging.basicConfig(level=logging.INFO)


MAIN_KEY = base64.b64decode('WWcmdGMlREV1aDYlWmNeOA==')
MAIN_IV = base64.b64decode('Nm95WkRyMjJFM3ljaGpNJQ==')
RELEASEVERSION = "OB55"
USERAGENT = "Dalvik/2.1.0 (Linux; U; Android 13; CPH2095 Build/RKQ1.211119.001)"
SUPPORTED_REGIONS = {"IND", "BR", "US", "SAC", "NA", "SG", "RU", "ID", "TW", "VN", "TH", "ME", "PK", "CIS", "BD", "EUROPE"}

REGION_PRIORITY = ["ME", "IND", "BR"]

REGION_BASE_URLS = {
    "IND": ["https://client.ind.freefiremobile.com"],
    "BR":  ["https://client.us.freefiremobile.com"],
    "US":  ["https://client.us.freefiremobile.com"],
    "SAC": ["https://client.us.freefiremobile.com"],
    "NA":  ["https://client.us.freefiremobile.com"],
}
DEFAULT_BASE_URLS = [
    "https://clientbp.ggpolarbear.com",
    "https://clientbp.ppmainecoonghj.com",
]

FREEFIRE_UPDATE_URL = "https://clientbp.ppmainecoonghj.com/UpdateSocialBasicInfo"
BIO_KEY = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
BIO_IV  = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])

ICON_API_URL = "https://star-icon-png.lovable.app/png?icon_id={}"
IMAGE_REQUEST_TIMEOUT = 15
PNG_API = os.environ.get("PNG_API", "https://cucivk.vercel.app/getpng?pngid={id}")

# LIKE + VISIT integration. Edit these keys here when needed.
LIKE_API_KEY_1 = os.environ.get("KEY_LIKE1", "shappno_codex")
LIKE_API_KEY_2 = os.environ.get("KEY_LIKE2", "shappno_801xx")
LIKE_API_KEY_3 = os.environ.get("KEY_LIKE3", "shappno_094xx")
LIKE_API_KEY_4 = os.environ.get("KEY_LIKE4", "shappno_077xx")

from SHAPPNO import like_visit_engine as like_visit
like_visit.KEY_LIKE1 = LIKE_API_KEY_1
like_visit.KEY_LIKE2 = LIKE_API_KEY_2
like_visit.KEY_LIKE3 = LIKE_API_KEY_3
like_visit.KEY_LIKE4 = LIKE_API_KEY_4

app = Flask(__name__)
CORS(app)
app.secret_key = os.environ.get("SHAPPNO_SESSION_SECRET") or os.urandom(32)

# Admin controls and lightweight usage counters. The settings file is deliberately
# outside the generated data directory so clearing runtime data does not reset keys/lock.
ADMIN_PASSWORD = "14444446555"
ADMIN_SETTINGS_PATH = os.path.join(os.path.dirname(__file__), ".shappno_admin_settings.json")
_ADMIN_LOCK = threading.RLock()
_ADMIN_STATE = {"locked": False, "like_key_1": LIKE_API_KEY_1, "like_key_2": LIKE_API_KEY_2,
                "like_key_3": LIKE_API_KEY_3, "like_key_4": LIKE_API_KEY_4,
                "api_calls": 0, "like_calls": 0, "likes_given": 0, "endpoint_calls": {}}

def _load_admin_state():
    try:
        with open(ADMIN_SETTINGS_PATH, "r", encoding="utf-8") as f:
            saved = json.load(f)
        for key in ("locked", "like_key_1", "like_key_2", "like_key_3", "like_key_4", "api_calls", "like_calls", "likes_given", "endpoint_calls"):
            if key in saved:
                _ADMIN_STATE[key] = saved[key]
    except (OSError, ValueError, TypeError):
        pass
    like_visit.KEY_LIKE1 = _ADMIN_STATE["like_key_1"]
    like_visit.KEY_LIKE2 = _ADMIN_STATE["like_key_2"]
    like_visit.KEY_LIKE3 = _ADMIN_STATE["like_key_3"]
    like_visit.KEY_LIKE4 = _ADMIN_STATE["like_key_4"]

def _save_admin_state():
    tmp = ADMIN_SETTINGS_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(_ADMIN_STATE, f, ensure_ascii=False, indent=2)
    os.replace(tmp, ADMIN_SETTINGS_PATH)

_load_admin_state()

@app.before_request
def _request_log_start():
    request._shappno_started_at = time.perf_counter()

@app.after_request
def _compact_api_log(response):
    try:
        path = request.path
        if path != "/" and not path.startswith("/admin-shappno"):
            elapsed = (time.perf_counter() - getattr(request, "_shappno_started_at", time.perf_counter())) * 1000
            uid = request.args.get("uid", "")
            uid_note = f" uid={uid[:24]}" if uid else ""
            app.logger.info("API %s %s -> %s %.0fms%s", request.method, path, response.status_code, elapsed, uid_note)
    except Exception:
        app.logger.exception("API request logging failed")
    return response

@app.before_request
def _admin_lock_gate():
    path = request.path
    if path.startswith("/admin-shappno") or False:
        return None
    with _ADMIN_LOCK:
        locked = bool(_ADMIN_STATE.get("locked"))
    if locked:
        if path == "/":
            return Response("<!doctype html><title>SHAPPNO Locked</title><meta name='viewport' content='width=device-width,initial-scale=1'><body style='margin:0;background:#080d1b;color:#fff;font:16px system-ui;display:grid;place-items:center;min-height:100vh'><main style='text-align:center;padding:32px'><h1>SHAPPNO IS LOCKED</h1><p>Website access is temporarily disabled by the administrator.</p></main></body>", 503, mimetype="text/html")
        return jsonify({"status": "locked", "message": "API service is temporarily disabled by administrator."}), 503
    return None

@app.after_request
def _record_api_usage(response):
    if request.path.startswith("/admin-shappno") or request.path == "/":
        return response
    try:
        with _ADMIN_LOCK:
            _ADMIN_STATE["api_calls"] = int(_ADMIN_STATE.get("api_calls", 0)) + 1
            counts = _ADMIN_STATE.setdefault("endpoint_calls", {})
            counts[request.path] = int(counts.get(request.path, 0)) + 1
            if request.path in ("/like", "/like2", "/like3", "/like4"):
                _ADMIN_STATE["like_calls"] = int(_ADMIN_STATE.get("like_calls", 0)) + 1
                if response.status_code < 400:
                    body = response.get_json(silent=True) if hasattr(response, "get_json") else None
                    if isinstance(body, dict):
                        given = body.get("LikesGivenByAPI", body.get("likes_given", body.get("likesGiven", 0)))
                        try: _ADMIN_STATE["likes_given"] = int(_ADMIN_STATE.get("likes_given", 0)) + max(0, int(given or 0))
                        except (TypeError, ValueError): pass
            # Persist counters on a short cadence to keep admin stats across restarts.
            if _ADMIN_STATE["api_calls"] % 5 == 0:
                _save_admin_state()
    except Exception:
        app.logger.exception("Could not record API usage")
    return response

cache = TTLCache(maxsize=200, ttl=300)
_CACHE_LOCK = threading.RLock()
cached_tokens = defaultdict(dict)
uid_region_cache = {}


def pad(text: bytes) -> bytes:
    padding_length = AES.block_size - (len(text) % AES.block_size)
    return text + bytes([padding_length] * padding_length)

def aes_cbc_encrypt(key: bytes, iv: bytes, plaintext: bytes) -> bytes:
    aes = AES.new(key, AES.MODE_CBC, iv)
    return aes.encrypt(pad(plaintext))

def decode_protobuf(encoded_data: bytes, message_type: message.Message) -> message.Message:
    instance = message_type()
    instance.ParseFromString(encoded_data)
    return instance

async def json_to_proto(json_data: str, proto_message: Message) -> bytes:
    json_format.ParseDict(json.loads(json_data), proto_message)
    return proto_message.SerializeToString()

def _candidate_servers(region: str, major_server: str):
    candidates = []
    if major_server:
        candidates.append(major_server.rstrip("/"))
    r = (region or "").upper()
    for url in REGION_BASE_URLS.get(r, []):
        if url not in candidates:
            candidates.append(url)
    for url in DEFAULT_BASE_URLS:
        if url not in candidates:
            candidates.append(url)
    return candidates


def get_account_credentials(region: str) -> str:
    r = region.upper()
    if r == "IND":
        return "uid=5896244318&password=shappno_fhFKeaZi"
    elif r == "ME":
        return "uid=5845633224&password=shappno_bqKurBcU"
    elif r in {"BR", "US", "SAC", "NA"}:
        return "uid=5119668284&password=57A9EF8FD80654681B3C6E806EB6CF94187D236A735DFF3AF0EBA638748EF5E0"
    else:
        return "uid=5845633224&password=shappno_bqKurBcU"


urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

MajorLoginHost = "loginbp.ppmainecoonghj.com"
MajorLoginPath = "/MajorLogin"
FreeFireVersion = RELEASEVERSION
GUEST_URL = "https://100067.connect.garena.com/api/v2/oauth/guest/token:grant"
CLIENT_ID = 100067
CLIENT_SECRET = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"
JWT_AES_KEY = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
JWT_AES_IV = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])
RESPONSE_HEADER_LEN = 64

def _jwt_encode_varint(num: int) -> bytes:
    if num < 0:
        raise ValueError("Number must be non-negative")
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

def _jwt_create_field(num, val):
    if isinstance(val, bool):
        return _jwt_encode_varint((num << 3) | 0) + _jwt_encode_varint(int(val))
    if isinstance(val, int):
        return _jwt_encode_varint((num << 3) | 0) + _jwt_encode_varint(val)
    if isinstance(val, (str, bytes)):
        v = val.encode() if isinstance(val, str) else val
        return _jwt_encode_varint((num << 3) | 2) + _jwt_encode_varint(len(v)) + v
    if isinstance(val, dict):
        nested = _jwt_create_packet(val)
        return _jwt_encode_varint((num << 3) | 2) + _jwt_encode_varint(len(nested)) + nested
    return b""

def _jwt_create_packet(fields: dict) -> bytes:
    return b"".join(_jwt_create_field(k, v) for k, v in fields.items())

def _jwt_encrypt_api(plain: bytes) -> bytes:
    cipher = AES.new(JWT_AES_KEY, AES.MODE_CBC, JWT_AES_IV)
    pad_len = AES.block_size - (len(plain) % AES.block_size)
    return cipher.encrypt(plain + bytes([pad_len] * pad_len))

def _jwt_decrypt_response(data: bytes) -> bytes:
    try:
        cipher = AES.new(JWT_AES_KEY, AES.MODE_CBC, JWT_AES_IV)
        dec = cipher.decrypt(data)
        pad_len = dec[-1]
        if 1 <= pad_len <= 16 and all(b == pad_len for b in dec[-pad_len:]):
            dec = dec[:-pad_len]
        return dec
    except Exception:
        return b""

def _jwt_decode_response(resp: bytes):
    def try_parse(blob):
        if not blob:
            return None
        try:
            msg = MajoRLoGinrEs_pb2.MajorLoginRes()
            msg.ParseFromString(blob)
            if msg.account_id > 0 and (msg.lock_region or msg.noti_region or msg.token):
                return msg
        except Exception:
            pass
        return None
    msg = try_parse(resp)
    if msg:
        return msg, "plaintext proto"
    if len(resp) > RESPONSE_HEADER_LEN:
        msg = try_parse(resp[RESPONSE_HEADER_LEN:])
        if msg:
            return msg, "plaintext proto (skip signature)"
    if len(resp) >= 16 and len(resp) % 16 == 0:
        dec = _jwt_decrypt_response(resp)
        msg = try_parse(dec) if dec else None
        if msg:
            return msg, "AES-CBC"
        if dec and len(dec) > RESPONSE_HEADER_LEN:
            msg = try_parse(dec[RESPONSE_HEADER_LEN:])
            if msg:
                return msg, "AES-CBC (skip signature)"
    return None, "unknown"

def _jwt_decode_token(token: str) -> dict:
    try:
        parts = token.split(".")
        if len(parts) != 3:
            return {}
        payload = parts[1] + "=" * (-len(parts[1]) % 4)
        return json.loads(base64.urlsafe_b64decode(payload).decode("utf-8"))
    except Exception:
        return {}

def _jwt_build_login_body(access_token, open_id, region="BD", lang="bn"):
    fields = {
        3: dt.now().strftime("%Y-%m-%d %H:%M:%S"), 4: "free fire", 5: 1,
        7: "1.132.4",
        8: "Android OS 15 / API-35 (AP3A.240617.008/T.R4T2.24e2a71-650ec)",
        9: "Handheld", 10: "airtel now cirkle", 11: "WIFI", 12: 1666,
        13: 750, 14: "360", 15: "ARM64 FP ASIMD AES | 2000 | 8",
        16: 7723, 17: "Mali-G52 MC2",
        18: "OpenGL ES 3.2 v1.r49p1-03bet0.19498e0ae1d5dac223383c39a2e58f04",
        19: "Google|3744f365-78fe-424a-871e-f77a0a095356", 20: "103.109.214.50",
        21: lang, 22: open_id, 23: "8", 24: "Handheld", 25: "realme RMX3710",
        26: region, 29: access_token, 30: 1, 41: "airtel now cirkle",
        42: "WIFI", 57: "7428b253defc164018c604a1ebbfebdf",
        60: 225554, 61: 155321, 62: 733, 64: 155845, 65: 225554,
        66: 155845, 67: 225554, 73: 2,
        74: "/data/app/~~ln8dFa29BUuPBtG4A-WwXQ==/com.dts.freefireth-tXx7bnxvKbykwJzwnEHs2Q==/lib/arm64",
        76: 1,
        77: "b8e0cd5e295eee42f5860d3c86e483dd|/data/app/~~ln8dFa29BUuPBtG4A-WwXQ==/com.dts.freefireth-tXx7bnxvKbykwJzwnEHs2Q==/base.apk",
        78: 3, 79: 2, 81: "64", 83: "2019121229", 85: 3, 86: "OpenGLES2",
        87: 8191, 88: 8, 92: 9754, 93: "android",
        94: "KqsHT+PFj/2sTPjf+unI9C5rnnStUzOFVqOADw9TI8tgL2bTnmzrBM/dEzyqy4BtAVua+w9mgLRIMrjXa67/qXm0pz5uQWsxC6sd8Um7OmMNHRmy",
        95: 111207, 96: '{"cur_rate":[60,45,90],"support_etc2":false}',
        97: 1, 99: "4", 100: "4", 102: "4455414f055f5f0336", 104: 52972,
        105: 1,
        106: "https://dl-bs.ggpolarbear.com/live/ABHotUpdates/|https://core-bs.ggpolarbear.com/live/ABHotUpdates/|6b2078db9d22dd98f8e9386a39af8462",
        107: "c8e41b7a93f02d56e1a94c7b8203f5d1",
    }
    return _jwt_create_packet(fields)

def get_user_access_token(uid, password):
    headers = {
        "User-Agent": "GarenaMSDK/4.0.42(M2006C3LII ;Android 10;en;IN;app 1.126.2 2019120816;)",
        "Accept": "application/json", "Content-Type": "application/json; charset=utf-8",
        "Connection": "Keep-Alive",
    }
    payload = {
        "client_id": CLIENT_ID, "client_secret": CLIENT_SECRET, "client_type": 2,
        "password": password, "response_type": "token", "uid": int(uid),
    }
    try:
        response = requests.post(GUEST_URL, headers=headers, json=payload,
                                 verify=False, timeout=3)
        if response.status_code == 200:
            data = response.json()
            if data.get("code") == 0:
                result = data.get("data", {}) or {}
                return result.get("access_token"), result.get("open_id")
            print(f"[oauth] {response.status_code}")
        else:
            print(f"[oauth] {response.status_code}")
    except Exception:
        print("[oauth] err")
    return None, None

def major_login_request(access_token, open_id, region="BD", lang="bn"):
    try:
        plain = _jwt_build_login_body(access_token, open_id, region, lang)
        body = _jwt_encrypt_api(plain)
        ctx = ssl._create_unverified_context()
        conn = http.client.HTTPSConnection(MajorLoginHost, context=ctx, timeout=3)
        conn.request("POST", MajorLoginPath, body=body, headers={
            "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
            "Accept": "*/*", "Accept-Encoding": "deflate, gzip",
            "Authorization": "Bearer", "X-Ga": "v1 1", "X-Ga-Sv": "1789556611",
            "Releaseversion": FreeFireVersion,
            "Content-Type": "application/x-www-form-urlencoded",
            "X-Unity-Version": "2018.4.12f1",
        })
        response = conn.getresponse()
        raw = response.read()
        encoding = response.getheader("Content-Encoding")
        conn.close()
        if encoding == "gzip":
            with gzip.GzipFile(fileobj=BytesIO(raw)) as stream:
                raw = stream.read()
        if response.status in (200, 201):
            return raw, None
        return None, f"HTTP {response.status}"
    except Exception as exc:
        return None, str(exc)

def create_user_jwt(uid, password, region="BD", lang="bn", return_open_id=False):
    async def _make():
        last_error = "JWT generation failed"
        connector = aiohttp.TCPConnector(limit=4, ttl_dns_cache=1800)
        async with aiohttp.ClientSession(
            connector=connector,
            timeout=aiohttp.ClientTimeout(total=like_visit.TOKEN_TIMEOUT_TOTAL)
        ) as session:
            for attempt in range(like_visit.TOKEN_MAX_ATTEMPTS):
                try:
                    access_token, open_id = await like_visit._async_oauth(session, str(uid), str(password))
                    if not access_token or not open_id:
                        last_error = "OAuth failed"
                    else:
                        raw, error = await asyncio.get_running_loop().run_in_executor(
                            like_visit.MAJOR_LOGIN_EXECUTOR,
                            like_visit._sync_major_login,
                            access_token, open_id, (region or "BD").upper(), lang
                        )
                        if raw:
                            result, mode, _ = like_visit.decode_response(raw)
                            if result and result.token:
                                try:
                                    payload = like_visit.decode_jwt(result.token)
                                    exp = payload.get("exp", int(time.time()) + like_visit.TOKEN_EXPIRY_HOURS * 3600)
                                    expires_at = datetime.datetime.fromtimestamp(exp, tz=timezone.utc)
                                    cached = {"token": result.token, "expires_at": expires_at}
                                    like_visit.TOKEN_CACHE[str(uid)] = cached
                                    like_visit.VISIT_TOKEN_CACHE[str(uid)] = cached
                                    like_visit.FAILED_TOKENS.pop(str(uid), None)
                                except Exception:
                                    pass
                                return result, access_token, None, open_id
                            last_error = f"No JWT token ({mode})"
                        else:
                            last_error = error or "MajorLogin failed"
                except Exception as exc:
                    last_error = str(exc)
                if attempt < like_visit.TOKEN_MAX_ATTEMPTS - 1:
                    await asyncio.sleep(like_visit.TOKEN_RETRY_SLEEP)
        return None, None, last_error, None

    try:
        result = asyncio.run(_make())
    except RuntimeError:
        # Flask handlers are synchronous; this fallback supports callers from an active event loop.
        import concurrent.futures
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:
            result = pool.submit(lambda: asyncio.run(_make())).result()
    return result if return_open_id else result[:3]

def create_jwt_from_access_token(access_token, region="BD", lang="bn"):
    """Exchange an existing OAuth access token with the LIKE+VISIT MajorLogin implementation."""
    try:
        open_id = None
        try:
            parts = access_token.split(".")
            if len(parts) == 3:
                payload = parts[1] + "=" * (-len(parts[1]) % 4)
                data = json.loads(base64.urlsafe_b64decode(payload).decode("utf-8"))
                open_id = data.get("open_id") or data.get("openId") or data.get("sub")
        except Exception:
            pass
        if not open_id:
            return None, "Access token does not contain open_id; use uid/password or a JWT token."
        raw, error = like_visit._sync_major_login(access_token, open_id, (region or "BD").upper(), lang)
        if not raw:
            return None, error or "MajorLogin failed for access token."
        result, mode, _ = like_visit.decode_response(raw)
        if result and getattr(result, "token", None):
            return result, None
        return None, f"JWT token was not returned by MajorLogin ({mode})."
    except Exception as exc:
        return None, str(exc)


async def create_jwt(region: str):
    try:
        account = get_account_credentials(region)
        parts = dict(item.split("=", 1) for item in account.split("&") if "=" in item)
        result, _, error = await asyncio.to_thread(
            create_user_jwt, parts.get("uid", ""), parts.get("password", ""),
            region=region, lang="bn"
        )
        if error or not result:
            raise RuntimeError(error or "JWT generation failed")
        cached_tokens[region] = {
            "token": f"Bearer {result.token}",
            "region": result.lock_region or region,
            "server_url": result.server_url,
            "expires_at": time.time() + min(result.ttl or 25200, 25200)
        }
        print(f"[token] {region} ok")
    except Exception:
        print(f"[token] {region} fail")


async def initialize_tokens():
    pass

async def refresh_tokens_periodically():
    while True:
        await asyncio.sleep(25200)
        for r in list(cached_tokens.keys()):
            try:
                await create_jwt(r)
            except Exception:
                pass

async def get_token_info(region: str) -> Tuple[str, str, str]:
    info = cached_tokens.get(region)
    if info and time.time() < info.get('expires_at', 0):
        return info['token'], info['region'], info['server_url']
    await create_jwt(region)
    info = cached_tokens.get(region) or {}
    if not info.get('token'):
        await create_jwt(region)
        info = cached_tokens.get(region) or {}
    return info.get('token', ''), info.get('region', ''), info.get('server_url', '')



async def _fetch_endpoint(uid, unk, region, endpoint):
    payload = await json_to_proto(json.dumps({'a': uid, 'b': unk}), main_pb2.GetPlayerPersonalShow())
    data_enc = aes_cbc_encrypt(MAIN_KEY, MAIN_IV, payload)
    token, lock, major_server = await get_token_info(region)

    if not token:
        raise Exception(f"Token not available for region {region}")

    headers = {
        'User-Agent': USERAGENT,
        'Authorization': token,
        'Content-Type': "application/x-www-form-urlencoded",
        'X-GA': "v1 1",
        'ReleaseVersion': RELEASEVERSION,
    }

    candidates = _candidate_servers(region, major_server)
    last_error = None
    resp_content = None

    async with httpx.AsyncClient(timeout=20.0, verify=False) as client:
        for base in candidates:
            url = base.rstrip("/") + endpoint
            try:
                resp = await client.post(url, content=data_enc, headers=headers)
            except Exception:
                last_error = f"{base}: err"
                continue
            if resp.status_code == 200 and resp.content:
                resp_content = resp.content
                last_error = None
                break
            else:
                last_error = f"{base}: {resp.status_code}"

    if resp_content is None:
        raise Exception(f"All servers failed for {region}{endpoint}: {last_error}")

    try:
        res_data = json.loads(json_format.MessageToJson(
            decode_protobuf(resp_content, AccountPersonalShow_pb2.AccountPersonalShowInfo)))
    except Exception as pe:
        raise Exception(f"Decode error: {pe}")

    detected_region = (res_data.get('basicInfo', {}) or {}).get('region', '').upper()
    if (detected_region == "IND" or lock == "IND") and region != "IND":
        uid_region_cache[uid] = "IND"
        token2, _, major2 = await get_token_info("IND")
        if token2:
            headers['Authorization'] = token2
            async with httpx.AsyncClient(timeout=20.0, verify=False) as client:
                for base in _candidate_servers("IND", major2):
                    try:
                        resp = await client.post(base.rstrip("/") + endpoint,
                                                 content=data_enc, headers=headers)
                        if resp.status_code == 200 and resp.content:
                            res_data = json.loads(json_format.MessageToJson(
                                decode_protobuf(resp.content,
                                                AccountPersonalShow_pb2.AccountPersonalShowInfo)))
                            break
                    except Exception:
                        continue
    return res_data


async def GetAccountInformation(uid, unk, region, endpoint, allow_reroute=True):
    return await _fetch_endpoint(uid, unk, region, endpoint)



async def GetWishList(uid, region):
    req = GetWishListItems_pb2.CSGetWishListItemsReq()
    req.account_id = int(uid)
    req_json = json_format.MessageToJson(req)
    payload = await json_to_proto(req_json, GetWishListItems_pb2.CSGetWishListItemsReq())
    data_enc = aes_cbc_encrypt(MAIN_KEY, MAIN_IV, payload)

    token, lock, major_server = await get_token_info(region)
    if not token:
        raise Exception(f"Token not available for {region}")

    headers = {
        'User-Agent': USERAGENT,
        'Authorization': token,
        'Content-Type': "application/x-www-form-urlencoded",
        'X-GA': "v1 1",
        'ReleaseVersion': RELEASEVERSION,
    }

    candidates = _candidate_servers(region, major_server)
    last_error = None
    resp_content = None

    async with httpx.AsyncClient(timeout=20.0, verify=False) as client:
        for base in candidates:
            url = base.rstrip("/") + "/GetWishListItems"
            try:
                resp = await client.post(url, content=data_enc, headers=headers)
            except Exception:
                last_error = f"{base}: err"
                continue
            if resp.status_code == 200 and resp.content:
                resp_content = resp.content
                last_error = None
                break
            else:
                last_error = f"{base}: {resp.status_code}"

    if resp_content is None:
        raise Exception(f"Wishlist servers failed for {region}: {last_error}")

    res = GetWishListItems_pb2.CSGetWishListItemsRes()
    res.ParseFromString(resp_content)
    return json.loads(json_format.MessageToJson(res))



def get_br_rank_name(rp):
    try:
        rp = int(rp)
    except:
        return "N/A"
    if rp <= 999:
        if rp <= 0: return "Bronze I"
        if rp < 100: return "Bronze II"
        if rp < 200: return "Bronze III"
        if rp < 300: return "Silver I"
        if rp < 400: return "Silver II"
        if rp < 500: return "Silver III"
        if rp < 600: return "Gold I"
        if rp < 700: return "Gold II"
        if rp < 800: return "Gold III"
        if rp < 900: return "Gold IV"
        return "Platinum I"
    if rp < 1300: return "Silver I"
    if rp < 1400: return "Silver II"
    if rp < 1500: return "Silver III"
    if rp < 1600: return "Gold I"
    if rp < 1725: return "Gold I"
    if rp < 1850: return "Gold II"
    if rp < 1975: return "Gold III"
    if rp < 2100: return "Gold IV"
    if rp < 2225: return "Platinum I"
    if rp < 2350: return "Platinum II"
    if rp < 2475: return "Platinum III"
    if rp < 2600: return "Platinum IV"
    if rp < 2750: return "Platinum V"
    if rp < 2900: return "Diamond I"
    if rp < 3050: return "Diamond II"
    if rp < 3200: return "Diamond III"
    if rp < 3350: return "Diamond IV"
    if rp < 3500: return "Diamond V"
    if rp < 3800: return "Heroic"
    if rp < 4300: return "Heroic"
    if rp < 4900: return "Elite Heroic"
    if rp < 5500: return "Elite Heroic"
    if rp < 6300: return "Elite Heroic"
    if rp < 7100: return "Master"
    if rp < 8000: return "Master"
    if rp < 9000: return "Elite Master"
    return "Elite Master"

def get_br_rank_with_score(rp):
    try:
        return f"{get_br_rank_name(int(rp))} ({int(rp)})"
    except:
        return "N/A"

def get_cs_rank_name(rp):
    try:
        rp = int(rp)
    except:
        return "N/A"
    if rp <= 0: return "Bronze I"
    if rp < 100: return "Bronze I"
    if rp < 200: return "Bronze II"
    if rp < 300: return "Bronze III"
    if rp < 400: return "Silver I"
    if rp < 500: return "Silver II"
    if rp < 600: return "Silver III"
    if rp < 700: return "Gold I"
    if rp < 800: return "Gold II"
    if rp < 900: return "Gold III"
    if rp < 1000: return "Gold IV"
    if rp < 1100: return "Platinum I"
    if rp < 1200: return "Platinum II"
    if rp < 1300: return "Platinum III"
    if rp < 1400: return "Platinum IV"
    if rp < 1500: return "Platinum V"
    if rp < 1600: return "Diamond I"
    if rp < 1700: return "Diamond II"
    if rp < 1800: return "Diamond III"
    if rp < 1900: return "Diamond IV"
    if rp < 2000: return "Diamond V"
    if rp < 2500: return "Heroic"
    if rp < 3000: return "Elite Heroic"
    if rp < 3500: return "Master"
    return "Elite Master"

def get_cs_rank_with_score(rp):
    try:
        return f"{get_cs_rank_name(int(rp))} ({int(rp)})"
    except:
        return "N/A"

def add_rank_info(data):
    try:
        for k in ('basicInfo', 'captainBasicInfo'):
            block = data.get(k, {})
            if block:
                block['rank_name'] = get_br_rank_with_score(block.get('rankingPoints', 0))
                block['cs_rank_name'] = get_cs_rank_with_score(block.get('csRankingPoints', 0))
    except:
        pass
    return data

def format_timestamp_bst(timestamp):
    try:
        dt_obj = datetime.fromtimestamp(int(timestamp), tz=timezone.utc)
        bst = timezone(timedelta(hours=6))
        return dt_obj.astimezone(bst).strftime("%d %B %Y at %I:%M:%S %p") + " (BST)"
    except:
        return "Unknown"



def find_best_region(uid):
    if uid in uid_region_cache:
        return uid_region_cache[uid]

    for region in REGION_PRIORITY:
        if region not in SUPPORTED_REGIONS:
            continue
        try:
            tok, _, _ = asyncio.run(get_token_info(region))
            if not tok:
                continue
            data = asyncio.run(GetAccountInformation(uid, "7", region, "/GetPlayerPersonalShow"))
            basic = data.get('basicInfo', {}) or {}
            if basic.get('accountId'):
                real = (basic.get('region') or region).upper()
                uid_region_cache[uid] = real
                return real
        except Exception:
            continue
    return None

def resolve_region(uid, force_region=None):
    if force_region and force_region.upper() in SUPPORTED_REGIONS:
        r = force_region.upper()
        uid_region_cache[uid] = r
        return r
    return find_best_region(uid)

def add_equipped_items(data):
    try:
        basic = data.get('basicInfo', {})
        if basic:
            basic['equipped_items'] = {
                "weapon_skins": basic.get('weaponSkinShows', []),
                "pin_id": basic.get('pinId', 0),
                "banner_id": basic.get('bannerId', 0),
                "head_pic": basic.get('headPic', 0),
                "title": basic.get('title', 0),
                "badge_id": basic.get('badgeId', 0),
                "equipped_animation_id": basic.get('equippedAnimationId', 0)
            }
        profile = data.get('profileInfo', {})
        if profile:
            profile['equipped_items'] = {
                "avatar_id": profile.get('avatarId', 0),
                "skin_color": profile.get('skinColor', 0),
                "clothes": profile.get('clothes', []),
                "equipped_skills": profile.get('equipedSkills', []),
                "is_selected": profile.get('isSelected', False),
                "is_selected_awaken": profile.get('isSelectedAwaken', False),
                "equipped_animation_id": profile.get('equippedAnimationId', 0)
            }
        captain = data.get('captainBasicInfo', {})
        if captain:
            captain['equipped_items'] = {
                "weapon_skins": captain.get('weaponSkinShows', []),
                "pin_id": captain.get('pinId', 0),
                "banner_id": captain.get('bannerId', 0),
                "head_pic": captain.get('headPic', 0),
                "title": captain.get('title', 0),
                "badge_id": captain.get('badgeId', 0),
                "equipped_animation_id": captain.get('equippedAnimationId', 0)
            }
    except Exception:
        pass
    return data

def cached_endpoint(ttl=300):
    def decorator(fn):
        @wraps(fn)
        def wrapper(*a, **k):
            key = (request.path, tuple(sorted(request.args.items())))
            with _CACHE_LOCK:
                cached = cache.get(key)
            if cached is not None:
                return cached
            # Do the network/API work outside the lock so different requests
            # and endpoints remain able to execute concurrently.
            res = fn(*a, **k)
            with _CACHE_LOCK:
                cache[key] = res
            return res
        return wrapper
    return decorator


def _bio_enc_var(number: int) -> bytes:
    encoded = bytearray()
    while number > 127:
        encoded.append((number & 127) | 128)
        number >>= 7
    encoded.append(number)
    return bytes(encoded)


def _bio_enc_proto(field_map: dict) -> bytes:
    protobuf_bytes = b""
    for field_number, field_value in field_map.items():
        if isinstance(field_value, int):
            protobuf_bytes += _bio_enc_var((field_number << 3) | 0)
            protobuf_bytes += _bio_enc_var(field_value)
        elif isinstance(field_value, str):
            value_bytes = field_value.encode("utf-8")
            protobuf_bytes += _bio_enc_var((field_number << 3) | 2)
            protobuf_bytes += _bio_enc_var(len(value_bytes)) + value_bytes
        elif isinstance(field_value, bytes):
            protobuf_bytes += _bio_enc_var((field_number << 3) | 2)
            protobuf_bytes += _bio_enc_var(len(field_value)) + field_value
        else:
            raise TypeError(
                f"Unsupported bio field {field_number}: {type(field_value).__name__}"
            )
    return protobuf_bytes


def _bio_encrypt(data_bytes: bytes) -> bytes:
    cipher = AES.new(BIO_KEY, AES.MODE_CBC, BIO_IV)
    return cipher.encrypt(crypto_pad(data_bytes, AES.block_size))


def _upload_bio(jwt_token: str, bio_text: str):
    try:
        payload = {
            2: 1,
            5: "",
            6: "",
            8: bio_text,
            11: "",
            12: "",
            16: "",
        }
        encrypted_body = _bio_encrypt(_bio_enc_proto(payload))
        headers = {
            "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
            "Accept": "*/*",
            "Accept-Encoding": "deflate, gzip",
            "X-GA-SV": "1794472840",
            "Authorization": f"Bearer {jwt_token}",
            "X-GA": "v1 1",
            "ReleaseVersion": RELEASEVERSION,
            "Content-Type": "application/x-www-form-urlencoded",
            "X-Unity-Version": "2018.4.12f1",
            "Content-Length": str(len(encrypted_body)),
        }
        response = requests.post(
            FREEFIRE_UPDATE_URL,
            headers=headers,
            data=encrypted_body,
            timeout=30,
            verify=False,
        )
        return response.status_code, response.content
    except Exception as exc:
        return 500, str(exc).encode("utf-8")


def _bio_decode_nickname(encoded: str) -> str:
    try:
        SECRET = b"1e5898ccb8dfdd921f9bdea848768b64a201"
        raw = base64.b64decode(encoded)
        dec = bytearray()
        for i, b in enumerate(raw):
            dec.append(b ^ SECRET[i % len(SECRET)])
        return dec.decode('utf-8', errors='replace')
    except Exception:
        return encoded


def _decode_jwt_info(token: str):
    try:
        parts = token.split('.')
        if len(parts) != 3:
            return None, None, None
        payload_b64 = parts[1] + '=' * ((4 - len(parts[1]) % 4) % 4)
        payload = json.loads(base64.urlsafe_b64decode(payload_b64).decode('utf-8'))
        uid = payload.get("account_id")
        region = payload.get("lock_region")
        nickname = payload.get("nickname")
        if isinstance(nickname, str):
            nickname = _bio_decode_nickname(nickname)
        return str(uid) if uid else None, nickname, region
    except Exception:
        return None, None, None


def _get_jwt_via_uid_pass(uid: str, password: str, region_hint: str = None):
    # create_user_jwt already tries BD/ME/IND/BR concurrently. Calling it once
    # avoids repeating the same four-region fallback for each outer region.
    preferred = region_hint.upper() if region_hint and region_hint.upper() in SUPPORTED_REGIONS else "BD"
    try:
        result, access_token, error = create_user_jwt(uid, password, region=preferred)
        if error or not result:
            return {"error": error or "JWT generation failed"}
        return {
            "token": result.token,
            "access_token": access_token,
            "region": result.lock_region or preferred,
            "server_url": result.server_url,
        }
    except Exception as exc:
        return {"error": str(exc)}

def _get_jwt_via_access_token(access_token: str, region_hint: str = None):
    result, error = create_jwt_from_access_token(
        access_token, region=(region_hint or "BD").upper()
    )
    if error or not result:
        return {"error": error or "JWT generation failed"}
    return {
        "token": result.token,
        "access_token": access_token,
        "region": getattr(result, "lock_region", None) or region_hint or "BD",
        "server_url": getattr(result, "server_url", None),
    }


@app.route("/bio_upload", methods=["GET", "POST"])
def bio_upload_endpoint():
    bio = request.args.get("bio") or request.form.get("bio")
    if not bio:
        return jsonify({"status": "error", "code": 400,
                        "error": "Missing 'bio' parameter"}), 400

    jwt_token = request.args.get("jwt") or request.form.get("jwt")
    uid = request.args.get("uid") or request.form.get("uid")
    password = (request.args.get("pass") or request.args.get("password")
                or request.form.get("pass") or request.form.get("password"))
    access = request.args.get("access") or request.form.get("access")
    region_hint = request.args.get("region") or request.form.get("region")

    final_jwt = None
    login_method = None
    final_access_token = None
    final_open_id = None
    final_uid = None
    final_name = None
    final_region = None

    if jwt_token:
        login_method = "Direct JWT"
        final_jwt = jwt_token
        u, name, reg = _decode_jwt_info(jwt_token)
        final_uid, final_name, final_region = u, name, reg

    elif uid and password:
        login_method = "UID/Pass -> JWT"
        res = _get_jwt_via_uid_pass(uid, password, region_hint=region_hint)
        if "error" in res:
            return jsonify({
                "status": "error", "code": 401,
                "error": f"JWT generation failed: {res['error']}"
            }), 401
        final_jwt = res["token"]
        final_access_token = res.get("access_token")
        final_region = res.get("region")
        u, name, reg = _decode_jwt_info(final_jwt)
        final_uid = u or uid
        final_name = name
        if reg and not final_region:
            final_region = reg

    elif access:
        login_method = "Access token -> JWT"
        res = _get_jwt_via_access_token(access, region_hint=region_hint)
        if "error" in res:
            return jsonify({
                "status": "error", "code": 401,
                "error": f"JWT generation failed: {res['error']}"
            }), 401
        final_jwt = res["token"]
        final_access_token = res.get("access_token") or access
        final_region = res.get("region")
        if not res.get("opaque"):
            u, name, reg = _decode_jwt_info(final_jwt)
            final_uid = u
            final_name = name
            if reg and not final_region:
                final_region = reg

    else:
        return jsonify({
            "status": "error", "code": 400,
            "error": "Provide jwt=, or uid=+pass=, or access="
        }), 400

    if not final_jwt:
        return jsonify({"status": "error", "code": 500,
                        "error": "Could not obtain JWT"}), 500

    status_code, resp_bytes = _upload_bio(final_jwt, bio)

    if status_code == 200:
        status_text = "success"
    elif status_code == 401:
        status_text = "unauthorized"
    else:
        status_text = f"http_{status_code}"

    return jsonify({
        "status": status_text,
        "code": status_code,
        "login_method": login_method,
        "bio": bio,
        "uid": str(final_uid) if final_uid else None,
        "name": final_name,
        "region": final_region,
        "open_id": final_open_id,
        "access_token": final_access_token,
        "generated_jwt": final_jwt,
        "server_response_hex": binascii.hexlify(resp_bytes).decode("utf-8") if resp_bytes else "",
        "version": RELEASEVERSION,
    }), 200 if status_code == 200 else (400 if status_code == 401 else 500)



@app.route('/access')
def api_access():
    uid = request.args.get('uid', '').strip()
    password = request.args.get('pass', request.args.get('password', '')).strip()
    if not uid or not password:
        return jsonify({"status": "error", "message": "Missing uid or pass"}), 400
    if not uid.isdigit() or len(uid) < 8:
        return jsonify({"status": "error", "message": "Invalid UID format"}), 400
    access_token, open_id = get_user_access_token(uid, password)
    if not access_token:
        return jsonify({"status": "error", "message": "OAuth failed (check uid/password)"}), 400
    return jsonify({"status": "success", "access_token": access_token, "open_id": open_id}), 200


_API_TOKEN_RESPONSE_CACHE = {}
_API_TOKEN_RESPONSE_LOCK = threading.RLock()


@app.route('/token')
def api_token():
    started = time.time()
    uid = request.args.get('uid', '').strip()
    password = request.args.get('password', request.args.get('pass', '')).strip()
    region = (request.args.get('region', 'BD').strip().upper() or 'BD')
    if not uid or not password:
        return jsonify({"status": "error", "message": "Missing uid or password"}), 400
    if not uid.isdigit() or len(uid) < 8:
        return jsonify({"status": "error", "message": "Invalid UID format"}), 400
    cache_key = hashlib.sha256(f"{uid}:{password}:{region}".encode()).hexdigest()
    now = time.time()
    with _API_TOKEN_RESPONSE_LOCK:
        cached = _API_TOKEN_RESPONSE_CACHE.get(cache_key)
        if cached and cached["expires"] > now:
            payload = dict(cached["response"])
            payload["time"] = f"{time.time() - started:.2f}s"
            return jsonify(payload), 200
        if cached:
            _API_TOKEN_RESPONSE_CACHE.pop(cache_key, None)

    result, access_token, error, open_id = create_user_jwt(
        uid, password, region=region, return_open_id=True
    )
    if error or not result:
        return jsonify({"status": "error", "message": error or "JWT generation failed"}), 400
    jwt_payload = _jwt_decode_token(result.token)
    real_uid = str(jwt_payload.get("account_id", result.account_id or "N/A"))
    response_data = {
        "status": "success",
        "real_uid": real_uid,
        "access_token": access_token,
        "open_id": open_id,
        "token": result.token,
        "time": f"{time.time() - started:.2f}s"
    }
    # Keep the full response for 15 minutes at most, never beyond JWT expiry.
    token_exp = jwt_payload.get("exp")
    try:
        cache_expiry = min(now + 900, float(token_exp) - 60) if token_exp else now + 600
    except (TypeError, ValueError):
        cache_expiry = now + 600
    if cache_expiry > now:
        with _API_TOKEN_RESPONSE_LOCK:
            _API_TOKEN_RESPONSE_CACHE[cache_key] = {
                "response": dict(response_data),
                "expires": cache_expiry
            }
    return jsonify(response_data), 200



async def _try_regions(uid, force_region=None):
    if force_region and force_region.upper() in SUPPORTED_REGIONS:
        r = force_region.upper()
        try:
            data = await GetAccountInformation(uid, "7", r, "/GetPlayerPersonalShow")
            basic = data.get('basicInfo', {}) or {}
            if basic.get('accountId'):
                uid_region_cache[uid] = (basic.get('region') or r).upper()
                return r, data
        except Exception:
            pass

    last_err = None
    for r in REGION_PRIORITY:
        if r not in SUPPORTED_REGIONS:
            continue
        try:
            tok, _, _ = await get_token_info(r)
            if not tok:
                continue
            data = await GetAccountInformation(uid, "7", r, "/GetPlayerPersonalShow")
            basic = data.get('basicInfo', {}) or {}
            if basic.get('accountId'):
                uid_region_cache[uid] = (basic.get('region') or r).upper()
                return r, data
        except Exception as e:
            last_err = str(e)
            continue
    raise Exception(f"UID not found in ME/IND/BR. last_error={last_err}")



@app.route('/info')
@cached_endpoint()
def get_account_info():
    uid = request.args.get('uid')
    if not uid:
        return jsonify({"error": "Please provide UID."}), 400

    force = request.args.get('region')
    try:
        region, return_data = asyncio.run(_try_regions(uid, force))
    except Exception as e:
        return jsonify({"error": str(e)}), 404

    try:
        return_data = add_rank_info(return_data)
        return_data = add_equipped_items(return_data)

        if 'diamondCostRes' in return_data:
            del return_data['diamondCostRes']

        basic = return_data.get('basicInfo', {}) or {}
        if basic.get('createAt'):
            basic['createAt_bst'] = format_timestamp_bst(basic.get('createAt', '0'))
        if basic.get('lastLoginAt'):
            basic['lastLoginAt_bst'] = format_timestamp_bst(basic.get('lastLoginAt', '0'))

        return json.dumps(return_data, indent=2, ensure_ascii=False), 200, \
               {'Content-Type': 'application/json; charset=utf-8'}
    except Exception as e:
        return jsonify({"error": f"Failed to format info: {e}", "region": region}), 500



@app.route('/level')
@cached_endpoint(ttl=300)
def get_level_info():
    uid = request.args.get('uid')
    if not uid:
        return jsonify({"error": "Please provide UID."}), 400

    try:
        region, data = asyncio.run(_try_regions(uid, request.args.get('region')))
    except Exception as e:
        return jsonify({"error": str(e)}), 404

    try:
        basic = data.get('basicInfo', {}) or {}
        level = max(0, min(int(basic.get('level') or 0), 100))
        exp = max(0, int(basic.get('exp') or 0))
        # Cumulative EXP thresholds; each entry is the target for the next level.
        level_exp = [
            100, 300, 600, 1000, 1500, 2100, 2800, 3600, 4500, 5500,
            6600, 7800, 9100, 10500, 12000, 13600, 15300, 17100, 19000, 21000,
            23100, 25300, 27600, 30000, 32500, 35100, 37800, 40600, 43500, 46500,
            49600, 52800, 56100, 59500, 63000, 66600, 70300, 74100, 78000, 82000,
            86100, 90300, 94600, 99000, 103500, 108100, 112800, 117600, 122500, 127500,
            132600, 137800, 143100, 148500, 154000, 159600, 165300, 171100, 177000, 183000,
            189100, 195300, 201600, 208000, 214500, 221100, 227800, 234600, 241500, 248500,
            255600, 262800, 270100, 277500, 285000, 292600, 300300, 308100, 316000, 324000,
            332100, 340300, 348600, 357000, 365500, 374100, 382800, 391600, 400500, 409500,
            418600, 427800, 437100, 446500, 456000, 465600, 475300, 485100, 495000, 505000
        ]
        if level >= 100:
            next_level = None
            exp_start = level_exp[-1]
            exp_target = 0
            exp_to_next = 0
            progress = 100.0
            next_status = "MAX_LEVEL"
        elif level <= 0:
            next_level = 1
            exp_start = 0
            exp_target = level_exp[0]
            exp_to_next = max(0, exp_target - exp)
            progress = round(min(100.0, exp / max(1, exp_target) * 100), 2)
            next_status = "READY" if exp_to_next == 0 else "IN_PROGRESS"
        else:
            next_level = level + 1
            exp_start = level_exp[level - 2] if level > 1 else 0
            exp_target = level_exp[level - 1]
            exp_to_next = max(0, exp_target - exp)
            span = max(1, exp_target - exp_start)
            progress = round(max(0.0, min(100.0, (exp - exp_start) / span * 100)), 2)
            next_status = "READY" if exp_to_next == 0 else "IN_PROGRESS"

        # Free Fire Level 100 cumulative EXP requirement.
        # Keep the total target separate from the amount remaining for this account.
        total_exp_needed_for_level_100 = 32032284
        remaining_exp = max(0, total_exp_needed_for_level_100 - exp)
        return jsonify({
            "uid": uid,
            "username": basic.get('nickname', 'Unknown'),
            "region": basic.get('region', region),
            "level": level,
            "next_level": next_level,
            "next_level_status": next_status,
            "exp": exp,
            "exp_current_level_start": exp_start,
            "exp_needed_for_next_level": exp_target,
            "exp_to_next_level": exp_to_next,
            "level_progress_percent": progress,
            "likes": basic.get('liked', 0),
            "badge_count": basic.get('badgeCnt', 0),
            "total_exp_needed_for_level_100": total_exp_needed_for_level_100,
            "exp_remaining_for_level_100": remaining_exp
        }), 200
    except (TypeError, ValueError) as e:
        return jsonify({"error": f"Invalid level/EXP data: {e}"}), 500
    except Exception as e:
        return jsonify({"error": f"Failed to fetch level info: {e}"}), 500


@app.route('/region')
@cached_endpoint(ttl=300)
def get_region_info():
    uid = request.args.get('uid')
    if not uid:
        return jsonify({"error": "Please provide UID."}), 400

    try:
        region, data = asyncio.run(_try_regions(uid, request.args.get('region')))
    except Exception as e:
        return jsonify({"error": str(e)}), 404

    try:
        basic = data.get('basicInfo', {}) or {}
        return jsonify({
            "uid": uid,
            "username": basic.get('nickname', 'Unknown'),
            "region": basic.get('region', region),
            "level": basic.get('level', 0),
            "likes": basic.get('liked', 0),
            "created_at": format_timestamp_bst(basic.get('createAt', '0')),
            "last_login": format_timestamp_bst(basic.get('lastLoginAt', '0')),
            "has_elite_pass": basic.get('hasElitePass', False),
            "account_type": basic.get('accountType', 0),
            "season_id": basic.get('seasonId', 0),
            "release_version": basic.get('releaseVersion', 'Unknown')
        }), 200
    except Exception as e:
        return jsonify({"error": f"Failed to fetch region info: {e}"}), 500



@app.route('/leader')
@cached_endpoint(ttl=300)
def get_leader_info():
    uid = request.args.get('uid')
    if not uid:
        return jsonify({"error": "Please provide UID."}), 400

    try:
        region, user_data = asyncio.run(_try_regions(uid, request.args.get('region')))
    except Exception as e:
        return jsonify({"error": str(e)}), 404

    try:
        captain_basic = user_data.get('captainBasicInfo', {}) or {}
        clan_basic = user_data.get('clanBasicInfo', {}) or {}
        if not captain_basic or not clan_basic:
            return jsonify({"error": "User is not in a clan or no leader found."}), 404

        captain_uid = captain_basic.get('accountId')
        leader_data = asyncio.run(GetAccountInformation(
            captain_uid, "7", captain_basic.get('region') or region, "/GetPlayerPersonalShow"))
        leader_basic = leader_data.get('basicInfo', {}) or {}
        leader_profile = leader_data.get('profileInfo', {}) or {}

        return jsonify({
            "uid": captain_uid,
            "username": leader_basic.get('nickname', 'Unknown'),
            "region": leader_basic.get('region', region),
            "level": leader_basic.get('level', 0),
            "exp": leader_basic.get('exp', 0),
            "likes": leader_basic.get('liked', 0),
            "rank": leader_basic.get('rank', 0),
            "ranking_points": leader_basic.get('rankingPoints', 0),
            "rank_name": get_br_rank_with_score(leader_basic.get('rankingPoints', 0)),
            "cs_rank_name": get_cs_rank_with_score(leader_basic.get('csRankingPoints', 0)),
            "max_rank": leader_basic.get('maxRank', 0),
            "cs_rank": leader_basic.get('csRank', 0),
            "cs_ranking_points": leader_basic.get('csRankingPoints', 0),
            "badge_count": leader_basic.get('badgeCnt', 0),
            "badge_id": leader_basic.get('badgeId', 0),
            "title": leader_basic.get('title', 0),
            "banner_id": leader_basic.get('bannerId', 0),
            "head_pic": leader_basic.get('headPic', 0),
            "pin_id": leader_basic.get('pinId', 0),
            "has_elite_pass": leader_basic.get('hasElitePass', False),
            "account_type": leader_basic.get('accountType', 0),
            "season_id": leader_basic.get('seasonId', 0),
            "release_version": leader_basic.get('releaseVersion', 'Unknown'),
            "created_at": format_timestamp_bst(leader_basic.get('createAt', '0')),
            "last_login": format_timestamp_bst(leader_basic.get('lastLoginAt', 0)),
            "weapon_skins": leader_basic.get('weaponSkinShows', []),
            "equipped_items": {
                "avatar_id": leader_profile.get('avatarId', 0),
                "skin_color": leader_profile.get('skinColor', 0),
                "clothes": leader_profile.get('clothes', []),
                "equipped_skills": leader_profile.get('equipedSkills', []),
                "is_selected": leader_profile.get('isSelected', False),
                "is_selected_awaken": leader_profile.get('isSelectedAwaken', False),
                "pve_primary_weapon": leader_profile.get('pvePrimaryWeapon', 0),
                "equipped_animation_id": leader_profile.get('equippedAnimationId', 0)
            },
            "clan_name": clan_basic.get('clanName', 'Unknown'),
            "clan_id": clan_basic.get('clanId', 'Unknown'),
            "clan_level": clan_basic.get('clanLevel', 0),
            "clan_capacity": clan_basic.get('capacity', 0),
            "clan_members": clan_basic.get('memberNum', 0),
            "is_leader": True
        }), 200
    except Exception as e:
        return jsonify({"error": f"Failed to fetch leader info: {e}"}), 500


def _fetch_icon_image(item_id):
    if not item_id:
        return None
    try:
        response = requests.get(
            ICON_API_URL.format(item_id),
            timeout=IMAGE_REQUEST_TIMEOUT,
            verify=False
        )
        response.raise_for_status()
        return Image.open(BytesIO(response.content)).convert("RGBA")
    except (requests.RequestException, OSError, ValueError):
        return None


def _load_font(size, bold=False):
    candidates = (
        [
            "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
            "/usr/share/fonts/truetype/liberation2/LiberationSans-Bold.ttf"
        ]
        if bold else
        [
            "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
            "/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf"
        ]
    )
    for path in candidates:
        if os.path.exists(path):
            try:
                return ImageFont.truetype(path, size)
            except OSError:
                pass
    return ImageFont.load_default()


def _fit_image(img, size):
    img = img.copy()
    img.thumbnail((size, size), Image.LANCZOS)
    output = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    output.alpha_composite(
        img,
        ((size - img.width) // 2, (size - img.height) // 2)
    )
    return output


def _add_neon_stage(canvas):
    width, height = canvas.size
    glow = Image.new("RGBA", (width, height), (0, 0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.ellipse(
        (width * 0.28, height * 0.08, width * 0.72, height * 0.82),
        fill=(92, 28, 190, 38)
    )
    canvas.alpha_composite(glow.filter(ImageFilter.GaussianBlur(110)))


def _draw_centered_text(draw, text, y, font, fill, canvas_width, stroke_width=0):
    box = draw.textbbox((0, 0), text, font=font, stroke_width=stroke_width)
    text_width = box[2] - box[0]
    x = (canvas_width - text_width) // 2
    draw.text(
        (x, y),
        text,
        font=font,
        fill=fill,
        stroke_width=stroke_width,
        stroke_fill=(0, 0, 0, 220)
    )


def _make_hex_item(img, size=154):
    pad = 15
    icon = _fit_image(img, size - pad * 2)
    tile = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    points = [
        (size * 0.5, 2),
        (size - 3, size * 0.25),
        (size - 3, size * 0.75),
        (size * 0.5, size - 3),
        (3, size * 0.75),
        (3, size * 0.25)
    ]
    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).polygon(points, fill=255)
    panel = Image.new("RGBA", (size, size), (13, 8, 34, 230))
    panel.putalpha(mask)
    tile.alpha_composite(panel)
    tile.alpha_composite(
        icon,
        ((size - icon.width) // 2, (size - icon.height) // 2)
    )
    glow = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.line(points + [points[0]], fill=(174, 83, 255, 255), width=5, joint="curve")
    tile.alpha_composite(glow.filter(ImageFilter.GaussianBlur(7)))
    tile.alpha_composite(glow)
    return tile


def render_wishlist_grid(nickname, item_ids):
    tile_size = 110
    pad = 18
    header_h = 90
    cols = 6

    valid_items = []
    for iid in item_ids:
        icon = _fetch_icon_image(iid)
        if icon:
            valid_items.append(icon)

    rows = max(1, (len(valid_items) + cols - 1) // cols)
    width = cols * tile_size + (cols + 1) * pad
    height = header_h + rows * tile_size + (rows + 1) * pad

    canvas = Image.new("RGBA", (width, height), (10, 6, 24, 255))
    _add_neon_stage(canvas)

    draw = ImageDraw.Draw(canvas)
    title_font = _load_font(30, bold=True)
    sub_font = _load_font(18, bold=False)

    _draw_centered_text(draw, nickname, 20, title_font, (255, 225, 145, 255), width, 1)
    _draw_centered_text(
        draw,
        f"Wishlist Items: {len(valid_items)}",
        58,
        sub_font,
        (180, 220, 255, 255),
        width
    )

    for idx, icon in enumerate(valid_items):
        r = idx // cols
        c = idx % cols
        x = pad + c * (tile_size + pad)
        y = header_h + pad + r * (tile_size + pad)
        tile = _make_hex_item(icon, tile_size)
        canvas.alpha_composite(tile, (x, y))

    output = BytesIO()
    canvas.save(output, format="PNG", optimize=True)
    output.seek(0)
    return output.getvalue()


@app.route('/item', methods=['GET'])
def get_item_image():
    item_id = (request.args.get('id') or request.args.get('item-id') or '').strip()
    if not item_id:
        return jsonify({"error": "Please provide item ID. Example: /item?id=909000010"}), 400

    item_image = _fetch_icon_image(item_id)
    if item_image is None:
        return jsonify({"error": f"Item image not found for UID: {item_id}"}), 404

    output = BytesIO()
    item_image.save(output, format="PNG", optimize=True)
    output.seek(0)
    return Response(output.getvalue(), mimetype="image/png",
                    headers={"Cache-Control": "public, max-age=3600"})


@app.route('/wishlist')
def get_wishlist():
    uid = request.args.get('uid')
    if not uid:
        return jsonify({"error": "Please provide UID."}), 400

    try:
        region, info_data = asyncio.run(_try_regions(uid, request.args.get('region')))
    except Exception as e:
        return jsonify({"error": str(e)}), 404

    basic = info_data.get('basicInfo', {}) or {}
    real_region = (basic.get('region') or region or "IND").upper()
    nickname = str(basic.get('nickname') or uid)

    item_ids = []
    try:
        data = asyncio.run(GetWishList(uid, real_region))
        for it in data.get('items', []):
            iid = it.get('itemId') or it.get('item_id')
            if iid:
                item_ids.append(iid)
    except Exception as e:
        return jsonify({"error": f"Wishlist fetch failed: {e}"}), 500

    if not item_ids:
        return jsonify({
            "uid": uid,
            "username": nickname,
            "region": real_region,
            "total_items": 0,
            "note": "No wishlist items found"
        }), 200

    try:
        img_bytes = render_wishlist_grid(nickname, item_ids)
        return Response(img_bytes, mimetype="image/png")
    except Exception:
        app.logger.exception("Wishlist image generation failed")
        return jsonify({"error": "Image generation failed"}), 500


def decode_author_uid(token):
    try:
        decoded = pyjwt.decode(token, options={"verify_signature": False})
        return decoded.get("account_id") or decoded.get("sub")
    except Exception:
        return None


def get_server_from_token(token):
    try:
        decoded = pyjwt.decode(token, options={"verify_signature": False})
        lock_region = decoded.get("lock_region", "IND")
        return lock_region.upper()
    except Exception:
        return "IND"


def get_base_url(server_name):
    server_name = (server_name or "").upper()
    if server_name == "IND":
        return "https://client.ind.freefiremobile.com/"
    elif server_name in {"BR", "US", "SAC", "NA"}:
        return "https://client.us.freefiremobile.com/"
    else:
        return "https://clientbp.ppmainecoonghj.com/"


def create_info_protobuf(uid):
    message = uid_generator_pb2.uid_generator()
    message.saturn_ = int(uid)
    message.garena = 1
    return message.SerializeToString()


def get_player_info(target_uid, token, server_name=None):
    try:
        if not server_name:
            server_name = get_server_from_token(token)

        protobuf_data = create_info_protobuf(target_uid)
        encrypted_data = aes_cbc_encrypt(MAIN_KEY, MAIN_IV, protobuf_data).hex()
        endpoint = get_base_url(server_name) + "GetPlayerPersonalShow"

        headers = {
            'User-Agent': "Dalvik/2.1.0 (Linux; U; Android 9; ASUS_Z01QD Build/PI)",
            'Connection': "Keep-Alive",
            'Accept-Encoding': "gzip",
            'Authorization': f"Bearer {token}",
            'Content-Type': "application/x-www-form-urlencoded",
            'Expect': "100-continue",
            'X-Unity-Version': "2018.4.11f1",
            'X-GA': "v1 1",
            'ReleaseVersion': RELEASEVERSION
        }

        response = requests.post(endpoint, data=bytes.fromhex(encrypted_data),
                                 headers=headers, verify=False, timeout=10)

        if response.status_code != 200:
            return None

        info = AccountPersonalShow_pb2.AccountPersonalShowInfo()
        info.ParseFromString(response.content)
        return info
    except Exception as e:
        print(f"[PlayerInfo] Error: {e}")
        return None


def extract_player_info(info_data):
    if not info_data:
        return None
    try:
        basic_info = info_data.basic_info
        return {
            'uid': basic_info.account_id,
            'nickname': basic_info.nickname,
            'level': basic_info.level,
            'region': basic_info.region,
            'likes': basic_info.liked,
            'release_version': basic_info.release_version
        }
    except Exception:
        return None


def retry_operation(default_max_retries=10, default_delay=1):
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            max_retries = kwargs.pop("max_retries", default_max_retries)
            delay = kwargs.pop("delay", default_delay)
            last_exception = None
            for attempt in range(max_retries):
                try:
                    result = func(*args, **kwargs)
                    if result and result.get('status') == 'success':
                        return result
                    print(f"[Retry] Attempt {attempt + 1}/{max_retries} → "
                          f"status={result.get('status') if result else None}")
                except Exception as e:
                    last_exception = e
                    print(f"[Retry] Attempt {attempt + 1}/{max_retries} failed: {str(e)}")

                if attempt < max_retries - 1:
                    time.sleep(delay)

            if last_exception:
                return {
                    "status": "error",
                    "message": f"All {max_retries} attempts failed",
                    "error": str(last_exception)
                }
            return {
                "status": "error",
                "message": f"All {max_retries} attempts failed"
            }
        return wrapper
    return decorator


@retry_operation()
def remove_friend_with_retry(author_uid, target_uid, token, server_name=None):
    try:
        if not server_name:
            server_name = get_server_from_token(token)

        player_info = get_player_info(target_uid, token, server_name)

        msg = RemoveFriend_Req_pb2.RemoveFriend()
        msg.AuthorUid = int(author_uid)
        msg.TargetUid = int(target_uid)
        encrypted_bytes = aes_cbc_encrypt(MAIN_KEY, MAIN_IV, msg.SerializeToString())

        url = get_base_url(server_name) + "RemoveFriend"
        headers = {
            'Authorization': f"Bearer {token}",
            'User-Agent': "Dalvik/2.1.0 (Linux; U; Android 9)",
            'Content-Type': "application/x-www-form-urlencoded",
            'X-Unity-Version': "2018.4.11f1",
            'X-GA': "v1 1",
            'ReleaseVersion': RELEASEVERSION
        }

        res = requests.post(url, data=encrypted_bytes, headers=headers,
                            verify=False, timeout=10)

        player_data = extract_player_info(player_info)

        if res.status_code == 200:
            status = "success"
        else:
            status = "failed"
            raise Exception(f"HTTP {res.status_code}: {res.text[:200]}")

        return {
            "author_uid": author_uid,
            "nickname": player_data.get('nickname', 'Unknown') if player_data else "Unknown",
            "uid": str(target_uid),
            "level": player_data.get('level', 0) if player_data else 0,
            "likes": player_data.get('likes', 0) if player_data else 0,
            "region": player_data.get('region', 'Unknown') if player_data else "Unknown",
            "release_version": player_data.get('release_version', 'Unknown') if player_data else "Unknown",
            "status": status,
            "time": dt.now().strftime("%Y-%m-%d %H:%M:%S")
        }

    except Exception as e:
        print(f"[RemoveFriend] Error: {e}")
        raise e


@retry_operation()
def send_friend_request_with_retry(author_uid, target_uid, token, server_name=None):
    try:
        if not server_name:
            server_name = get_server_from_token(token)

        player_data = None
        try:
            info_region, info_response = asyncio.run(_try_regions(str(target_uid), server_name))
            basic = (info_response or {}).get("basicInfo", {}) or {}
            if basic:
                player_data = {
                    "uid": basic.get("accountId") or basic.get("uid") or str(target_uid),
                    "nickname": basic.get("nickname") or "Unknown",
                    "level": basic.get("level") or 0,
                    "region": basic.get("region") or info_region or server_name or "Unknown",
                    "likes": basic.get("liked", basic.get("likes", 0)) or 0,
                    "release_version": basic.get("releaseVersion") or basic.get("release_version") or "Unknown",
                }
        except Exception as info_error:
            app.logger.warning("[AddFriend] Player info lookup failed: %s", info_error)

        if not player_data:
            player_data = extract_player_info(get_player_info(target_uid, token, server_name))

        encrypted_id = Encrypt_ID(target_uid)
        payload = f"08a7c4839f1e10{encrypted_id}1801"
        encrypted_payload = encrypt_api(payload)

        url = get_base_url(server_name) + "RequestAddingFriend"
        headers = {
            "Authorization": f"Bearer {token}",
            "X-Unity-Version": "2018.4.11f1",
            "X-GA": "v1 1",
            "ReleaseVersion": RELEASEVERSION,
            "Content-Type": "application/x-www-form-urlencoded",
            "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 9)"
        }

        r = requests.post(url, headers=headers,
                          data=bytes.fromhex(encrypted_payload),
                          verify=False, timeout=10)

        if r.status_code == 200:
            status = "success"
        else:
            status = "failed"
            raise Exception(f"HTTP {r.status_code}: {r.text[:200]}")

        return {
            "author_uid": author_uid,
            "nickname": player_data.get('nickname') if player_data else "Unknown",
            "uid": target_uid,
            "level": player_data.get('level') if player_data else 0,
            "likes": player_data.get('likes') if player_data else 0,
            "region": player_data.get('region') if player_data else "Unknown",
            "release_version": player_data.get('release_version') if player_data else "Unknown",
            "status": status,
            "time": dt.now().strftime("%Y-%m-%d %H:%M:%S")
        }

    except Exception as e:
        print(f"[AddFriend] Error: {e}")
        raise e


@app.route('/add_friend', methods=['GET'])
def adding_friend_custom():
    uid = request.args.get('uid')
    password = request.args.get('password')
    friend_uid = request.args.get('friend_uid')
    server_name = request.args.get('server_name')  # optional

    if not uid or not password or not friend_uid:
        return jsonify({"status": "failed",
                        "message": "Missing uid, password, or friend_uid"}), 400

    if server_name:
        result, access_token, error = create_user_jwt(uid, password, region=server_name)
    else:
        result = None
        error = None
        for try_region in ["BD", "ME", "IND", "BR"]:
            result, access_token, error = create_user_jwt(uid, password, region=try_region)
            if result and result.token:
                break
            result = None

    if error or not result or not result.token:
        return jsonify({"status": "failed",
                        "message": f"JWT generation failed: {error or 'unknown'}"}), 400

    token = result.token
    author_uid = decode_author_uid(token) or str(result.account_id)
    if not author_uid:
        return jsonify({"status": "failed",
                        "message": "Invalid JWT token"}), 400

    actual_region = (result.lock_region or server_name or "IND").upper()
    response = send_friend_request_with_retry(author_uid, friend_uid, token, actual_region)
    return jsonify(response)


@app.route('/rv_friend', methods=['GET'])
def removing_friend_custom():
    uid = request.args.get('uid')
    password = request.args.get('password')
    friend_uid = request.args.get('friend_uid')
    server_name = request.args.get('server_name')  # optional

    if not uid or not password or not friend_uid:
        return jsonify({"status": "failed",
                        "message": "Missing uid, password, or friend_uid"}), 400

    if server_name:
        result, access_token, error = create_user_jwt(uid, password, region=server_name)
    else:
        result = None
        error = None
        for try_region in ["BD", "ME", "IND", "BR"]:
            result, access_token, error = create_user_jwt(uid, password, region=try_region)
            if result and result.token:
                break
            result = None

    if error or not result or not result.token:
        return jsonify({"status": "failed",
                        "message": f"JWT generation failed: {error or 'unknown'}"}), 400

    token = result.token
    author_uid = decode_author_uid(token) or str(result.account_id)
    if not author_uid:
        return jsonify({"status": "failed",
                        "message": "Invalid JWT token"}), 400

    actual_region = (result.lock_region or server_name or "IND").upper()
    response = remove_friend_with_retry(author_uid, friend_uid, token, actual_region)
    return jsonify(response)








SHAPPNO_REGION_CONFIG = {
    'bd':  {'domain': 'clientbp.ppmainecoonghj.com', 'file': os.path.join('ACCOUNT', 'spam_rq_bd.txt')},
    'ind': {'domain': 'client.ind.freefiremobile.com', 'file': os.path.join('ACCOUNT', 'spam_rq_ind.txt')},
}


def _shappno_load_accounts(region_key):
    try:
        config = SHAPPNO_REGION_CONFIG.get(region_key)
        if not config:
            app.logger.error(f"[shappno-send] Unknown region: {region_key}")
            return None
        token_file = config['file']
        if not os.path.isabs(token_file):
            token_file = os.path.join(os.path.dirname(__file__), token_file)
        if not os.path.exists(token_file):
            app.logger.error(f"[shappno-send] File not found: {token_file}")
            return None
        accounts = []
        with open(token_file, "r") as f:
            for line in f:
                line = line.strip()
                if line and ':' in line:
                    uid, pwd = line.split(':', 1)
                    if uid.strip() and pwd.strip():
                        accounts.append({"uid": uid.strip(), "password": pwd.strip()})
        app.logger.info(f"[shappno-send] [{region_key}] Loaded {len(accounts)} from {token_file}")
        return accounts
    except Exception as e:
        app.logger.error(f"[shappno-send] Load error: {e}")
        return None


def _shappno_get_internal_info(target_uid):
    try:
        region, data = asyncio.run(_try_regions(target_uid))
        basic = (data or {}).get('basicInfo', {}) or {}
        name = basic.get('nickname') or "N/A"
        level = basic.get('level', "N/A")
        return name, level
    except Exception as e:
        app.logger.warning(f"[shappno-send] internal info failed: {e}")
        return "N/A", "N/A"


def _shappno_one_account(acc, target_uid, region_key, server_name):
    uid = acc['uid']
    pwd = acc['password']
    try:
        result, _access, error = create_user_jwt(uid, pwd, region=region_key.upper())
        if error or not result or not result.token:
            return {"uid": uid, "status": "jwt_failed",
                    "error": error or "no token"}

        token = result.token
        author_uid = decode_author_uid(token) or str(result.account_id)
        if not author_uid:
            return {"uid": uid, "status": "jwt_failed",
                    "error": "invalid jwt"}

        actual_region = (result.lock_region or server_name or "IND").upper()

        resp = send_friend_request_with_retry(
            author_uid, target_uid, token, actual_region,
            max_retries=2, delay=1
        )

        return {
            "uid": uid,
            "author_uid": author_uid,
            "nickname": resp.get("nickname"),
            "region": actual_region,
            "status": resp.get("status", "failed"),
            "message": resp.get("message"),
        }
    except Exception as e:
        return {"uid": uid, "status": "exception", "error": str(e)}


@app.route("/shappno-send", methods=["GET"])
def shappno_send_endpoint():
    target_uid = request.args.get("uid")
    region_key = (request.args.get("region") or "bd").lower()

    if not target_uid:
        return jsonify({"error": "uid parameter required"}), 400
    if region_key not in SHAPPNO_REGION_CONFIG:
        return jsonify({
            "error": f"Invalid region. Supported: {list(SHAPPNO_REGION_CONFIG.keys())}"
        }), 400

    player_name, player_level = _shappno_get_internal_info(target_uid)

    accounts = _shappno_load_accounts(region_key)
    if not accounts:
        return jsonify({
            "PlayerName": player_name,
            "PlayerLevel": player_level,
            "UID": target_uid,
            "Region": region_key.upper(),
            "Success": 0,
            "Failed": 0,
            "Status": 2,
            "Message": f"No accounts found in {SHAPPNO_REGION_CONFIG[region_key]['file']}",
        }), 404

    server_name = SHAPPNO_REGION_CONFIG[region_key]['domain']
    app.logger.info(
        f"[shappno-send] region={region_key} accounts={len(accounts)} "
        f"(using /add_friend system, max_retries=2)"
    )

    results = {"success": 0, "failed": 0}
    lock = threading.Lock()

    def _worker(acc):
        r = _shappno_one_account(acc, target_uid, region_key, server_name)
        with lock:
            if r.get("status") == "success":
                results["success"] += 1
            else:
                results["failed"] += 1

    with ThreadPoolExecutor(max_workers=15) as executor:
        futures = [executor.submit(_worker, acc) for acc in accounts]
        for f in as_completed(futures):
            try:
                f.result(timeout=30)
            except Exception:
                pass

    app.logger.info(
        f"[shappno-send] [{region_key}] done: success={results['success']} "
        f"failed={results['failed']}"
    )

    return jsonify({
        "PlayerName": player_name,
        "PlayerLevel": player_level,
        "UID": target_uid,
        "Region": region_key.upper(),
        "Total": len(accounts),
        "Success": results["success"],
        "Failed": results["failed"],
        "Status": 1 if results["success"] > 0 else 2,
    }), 200


AVATAR_ZOOM = 1.26
AVATAR_SHIFT_Y = 0
AVATAR_SHIFT_X = 0
def _ensure_tokens_ready():
    return


# --- Embedded Dynamic Duo service (formerly duo_service.py) ---
_DUO_NAMESPACE = {"__name__": "_shappno_embedded_duo"}
exec(compile(r"""
# Dynamic Duo lookup service adapted from the supplied duo.py reference.
import os
import time
import requests
import urllib3
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from google.protobuf import descriptor_pool, symbol_database
from google.protobuf.internal import builder

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

GUEST_UID = os.environ.get("DUO_GUEST_UID", "5845631732")
GUEST_PASSWORD = os.environ.get("DUO_GUEST_PASSWORD", "shappno_VXPyL0ev")
AES_KEY = b"Yg&tc%DEuh6%Zc^8"
AES_IV = b"6oyZDr22E3ychjM%"
BASE_URL = "https://clientbp.ppmainecoonghj.com"
TOKEN_URL = os.environ.get("DUO_TOKEN_URL", "https://shappno-all-api.onrender.com/token")

_sym_db = symbol_database.Default()
DESCRIPTOR = descriptor_pool.Default().AddSerializedFile(
    b'\n\x1aSpidey_SpecialFriend.proto"\x87\x01\n\x0eDynamicDuoData'
    b'\x12\x13\n\x0bpartner_uid\x18\x01 \x01(\x03\x12\r\n\x05score\x18\x03'
    b' \x01(\x05\x12\x1a\n\x12creation_timestamp\x18\x04 \x01(\x03'
    b'\x12\x13\n\x0bdays_active\x18\x05 \x01(\x05\x12\x0e\n\x06status'
    b'\x18\x06 \x01(\x05J\x04\x08\x02\x10\x03J\x04\x08\x08\x10\tJ\x04\x08\t'
    b'\x10\n":\n\x15SpecialFriendResponse\x12!\n\x08duo_info\x18\x01'
    b' \x01(\x0b\x32\x0f.DynamicDuoDatab\x06proto3'
)
_globals = globals()
builder.BuildMessageAndEnumDescriptors(DESCRIPTOR, _globals)
builder.BuildTopDescriptorsAndMessages(DESCRIPTOR, "SpecialFriend_pb2", _globals)
SpecialFriendResponse = _globals["SpecialFriendResponse"]

_token_cache = {"token": None, "expires": 0}

def _enc(data):
    return AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(data, 16))

def _dec(data):
    try:
        return unpad(AES.new(AES_KEY, AES.MODE_CBC, AES_IV).decrypt(data), 16)
    except Exception:
        return data

def _build_uid_protobuf(uid):
    n = int(uid)
    result = bytearray()
    while n >= 0x80:
        result.append((n & 0x7f) | 0x80)
        n >>= 7
    result.append(n)
    return _enc(b"\x08" + bytes(result))

def _format_timestamp(ts):
    try:
        return time.strftime("%B %d, %Y at %I:%M %p", time.localtime(ts))
    except (ValueError, TypeError, OverflowError):
        return "Invalid Timestamp"

def fetch_jwt_token(force=False):
    now = time.time()
    if not force and _token_cache["token"] and _token_cache["expires"] > now + 60:
        return _token_cache["token"]
    try:
        response = requests.get(
            TOKEN_URL,
            params={"uid": GUEST_UID, "password": GUEST_PASSWORD},
            timeout=25,
        )
        if response.status_code == 200:
            data = response.json()
            token = data.get("token") or data.get("access_token")
            if token:
                _token_cache.update(token=token, expires=now + 3000)
                return token
    except Exception:
        pass
    return None

def _decode_protobuf_data(binary_data):
    try:
        if not binary_data or len(binary_data) < 2:
            return None, f"Empty Response ({len(binary_data) if binary_data else 0} bytes)"
        response = SpecialFriendResponse()
        response.ParseFromString(binary_data)
        if not response.HasField("duo_info"):
            return None, "No Dynamic Duo info found (UID may not have a duo partner)"
        duo = response.duo_info
        score = duo.score
        if score < 101: level = 1
        elif score < 301: level = 2
        elif score < 501: level = 3
        elif score < 801: level = 4
        elif score < 1201: level = 5
        else: level = 6
        return {
            "partner_uid": str(duo.partner_uid),
            "level": level,
            "score": score,
            "days_active": duo.days_active,
            "time_created": _format_timestamp(duo.creation_timestamp),
            "creation_timestamp": duo.creation_timestamp,
            "status": "Active" if getattr(duo, "status", 0) == 2 else "Inactive",
        }, None
    except Exception as exc:
        return None, f"Parsing Error: {exc}"

def fetch_duo(target_uid):
    token = fetch_jwt_token()
    if not token:
        return None, "Failed to generate JWT token"
    headers = {
        "Authorization": f"Bearer {token}",
        "Content-Type": "application/octet-stream",
        "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 11)",
        "X-GA": "v1 1",
        "ReleaseVersion": "OB55",
        "Connection": "Keep-Alive",
    }
    payload = _build_uid_protobuf(target_uid)
    try:
        response = requests.post(
            f"{BASE_URL}/GetSpecialFriendList",
            headers=headers,
            data=payload,
            timeout=20,
            verify=False,
        )
    except Exception as exc:
        return None, f"Request error: {type(exc).__name__}: {exc}"
    if response.status_code in (401, 403):
        token = fetch_jwt_token(force=True)
        if token:
            headers["Authorization"] = f"Bearer {token}"
            try:
                response = requests.post(
                    f"{BASE_URL}/GetSpecialFriendList",
                    headers=headers,
                    data=payload,
                    timeout=20,
                    verify=False,
                )
            except Exception as exc:
                return None, f"Request error: {type(exc).__name__}: {exc}"
    if response.status_code != 200:
        return None, f"HTTP {response.status_code}: {response.text[:150]}"
    if not response.content:
        return None, "Server returned empty body (0 bytes) — UID may have no duo"
    decrypted = _dec(response.content)
    if len(decrypted) < 2:
        return None, f"Decrypted payload too small ({len(decrypted)} bytes) — no duo data"
    return _decode_protobuf_data(decrypted)

""", "<embedded-duo-service>", "exec"), _DUO_NAMESPACE)
_fetch_new_duo = _DUO_NAMESPACE["fetch_duo"]


@app.route("/duo-ck", methods=["GET"])
@cached_endpoint(ttl=120)
def duo_ck_endpoint():
    uid = (request.args.get("uid") or "").strip()
    if not uid:
        return jsonify({"status": "error", "message": "Missing 'uid' parameter"}), 400
    if not uid.isdigit():
        return jsonify({"status": "error", "message": "UID must contain only numbers"}), 400
    try:
        data, err = _fetch_new_duo(uid)
    except Exception as exc:
        app.logger.exception("[duo] fetch failed")
        return jsonify({"status": "error", "uid": uid, "message": f"Server error: {exc}"}), 500
    if err or not data:
        no_duo = bool(err) and any(
            marker in err.lower()
            for marker in ("no dynamic duo", "no duo", "empty body", "no duo data")
        )
        if no_duo or (not err and not data):
            return jsonify({"status": "success", "uid": uid,
                            "message": "আপনার কোনো duo নাই", "data": None}), 200
        return jsonify({"status": "error", "uid": uid,
                        "message": err or "Duo information unavailable"}), 502
    return jsonify({"status": "success", "uid": uid, "data": data})


CLAN_REGION_SERVER_MAP = {
    "IND":     "https://client.ind.freefiremobile.com",
    "ME":      "https://clientbp.ppmainecoonghj.com",
    "BD":      "https://clientbp.ppmainecoonghj.com",
    "PK":      "https://clientbp.ppmainecoonghj.com",
    "SG":      "https://clientbp.ppmainecoonghj.com",
    "ID":      "https://clientbp.ppmainecoonghj.com",
    "RU":      "https://clientbp.ppmainecoonghj.com",
    "TH":      "https://clientbp.ppmainecoonghj.com",
    "VN":      "https://clientbp.ppmainecoonghj.com",
    "CIS":     "https://clientbp.ppmainecoonghj.com",
    "BR":      "https://client.us.freefiremobile.com",
    "US":      "https://client.us.freefiremobile.com",
    "NA":      "https://client.us.freefiremobile.com",
    "SAC":     "https://client.us.freefiremobile.com",
    "EUROPE":  "https://clientbp.ppmainecoonghj.com",
}
CLAN_DEFAULT_SERVER_URL = "https://clientbp.ppmainecoonghj.com"

CLAN_GAME_HEADERS = {
    "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 9)",
    "Connection": "Keep-Alive",
    "Accept-Encoding": "gzip",
    "Content-Type": "application/octet-stream",
    "X-Unity-Version": "2018.4.11f1",
    "X-GA": "v1 1",
    "ReleaseVersion": RELEASEVERSION,
    "Expect": "100-continue",
}


def _clan_get_server_url(region):
    r = (region or "ME").upper()
    return CLAN_REGION_SERVER_MAP.get(r, CLAN_DEFAULT_SERVER_URL)


def _clan_encrypt_payload(data):
    return aes_cbc_encrypt(MAIN_KEY, MAIN_IV, data)


def _clan_request_join(jwt_token, clan_id, region):
    server_url = _clan_get_server_url(region)
    msg = ReqCLan_pb2.MyMessage()
    msg.field_1 = int(clan_id)
    payload = _clan_encrypt_payload(msg.SerializeToString())

    headers = CLAN_GAME_HEADERS.copy()
    headers["Authorization"] = f"Bearer {jwt_token}"
    url = f"{server_url}/RequestJoinClan"

    r = requests.post(url, headers=headers, data=payload,
                      verify=False, timeout=20)
    return r.status_code, r.text


def _clan_quit(jwt_token, clan_id, region):
    server_url = _clan_get_server_url(region)
    msg = QuitClanReq_pb2.QuitClanReq()
    msg.field_1 = int(clan_id)
    payload = _clan_encrypt_payload(msg.SerializeToString())

    headers = CLAN_GAME_HEADERS.copy()
    headers["Authorization"] = f"Bearer {jwt_token}"
    url = f"{server_url}/QuitClan"

    r = requests.post(url, headers=headers, data=payload,
                      verify=False, timeout=20)
    return r.status_code, r.text


def _clan_resolve_login(jwt_token=None, uid=None, password=None, region_hint=None):
    if jwt_token:
        try:
            parts = jwt_token.split(".")
            if len(parts) == 3:
                payload_b64 = parts[1] + "=" * (-len(parts[1]) % 4)
                payload = json.loads(base64.urlsafe_b64decode(payload_b64).decode("utf-8"))
                acc_id = payload.get("account_id")
                nick = payload.get("nickname")
                lock = (payload.get("lock_region") or "").upper()
                if region_hint and region_hint.upper() in CLAN_REGION_SERVER_MAP:
                    disp = region_hint.upper()
                elif lock:
                    disp = lock
                else:
                    disp = "ME"
                return jwt_token, str(acc_id) if acc_id else None, nick, disp, "JWT"
        except Exception:
            pass
        return None, None, None, None, "Invalid JWT"

    if uid and password:
        try:
            if region_hint and region_hint.upper() in CLAN_REGION_SERVER_MAP:
                order = [region_hint.upper()]
            else:
                order = ["ME", "IND", "BR", "US"]

            last_err = None
            for r in order:
                result, _, error = create_user_jwt(uid, password, region=r)
                if error or not result or not result.token:
                    last_err = error or "JWT generation failed"
                    continue
                real_uid = str(result.account_id or "")
                real_region = (result.lock_region or r).upper()
                return result.token, real_uid, None, real_region, f"UID_PASS({r})"

            return None, None, None, None, f"JWT generation failed: {last_err}"
        except Exception as e:
            return None, None, None, None, f"Exception: {e}"

    return None, None, None, None, "No login credentials provided"


def _clan_do_action(action_name, action_func):
    try:
        clan_id = request.args.get("clan_id")
        jwt_token = request.args.get("jwt")
        uid = request.args.get("uid")
        password = request.args.get("pass") or request.args.get("password")
        region_hint = request.args.get("region")

        if not clan_id:
            return jsonify({"success": False, "error": "clan_id required"}), 400

        final_jwt, real_uid, name, region, method = _clan_resolve_login(
            jwt_token=jwt_token, uid=uid, password=password,
            region_hint=region_hint
        )
        if not final_jwt:
            return jsonify({"success": False, "error": method}), 400

        code, text = action_func(final_jwt, clan_id, region)

        return jsonify({
            "success": (code == 200),
            "action": action_name,
            "clan_id": clan_id,
            "uid": real_uid or uid,
            "name": name,
            "region": region,
            "login_method": method,
            "developer": "SHAPPNO",
            "telegram": "@SHAPPNO_04X",
            "api_version": RELEASEVERSION,
            "server_response": text
        }), 200 if code == 200 else 500
    except Exception as e:
        app.logger.exception(f"[clan] {action_name} failed")
        return jsonify({
            "success": False,
            "error": "internal_error",
            "detail": str(e),
            "type": type(e).__name__
        }), 500


@app.route("/request_clan", methods=["GET"])
def api_request_clan():
    return _clan_do_action("Join Clan", _clan_request_join)


@app.route("/quit_clan", methods=["GET"])
def api_quit_clan():
    return _clan_do_action("Quit Clan", _clan_quit)



NICK_REGION_URL = {
    "ME":      "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "BD":      "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "PK":      "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "SG":      "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "ID":      "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "RU":      "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "TH":      "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "VN":      "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "CIS":     "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "EUROPE":  "https://loginbp.ppmainecoonghj.com/MajorModifyNickname",
    "IND":     "https://client.ind.freefiremobile.com/MajorModifyNickname",
    "BR":      "https://client.us.freefiremobile.com/MajorModifyNickname",
    "US":      "https://client.us.freefiremobile.com/MajorModifyNickname",
    "NA":      "https://client.us.freefiremobile.com/MajorModifyNickname",
    "SAC":     "https://client.us.freefiremobile.com/MajorModifyNickname",
}
NICK_DEFAULT_URL = "https://loginbp.ppmainecoonghj.com/MajorModifyNickname"


def _nick_get_url(region):
    r = (region or "ME").upper()
    return NICK_REGION_URL.get(r, NICK_DEFAULT_URL)


def _nick_decode_ff_name(b64_str):
    try:
        key = b"1e5898ccb8dfdd921f9bdea848768b64a201"
        b64_str = b64_str.strip()
        b64_str += "=" * ((4 - len(b64_str) % 4) % 4)
        encrypted_bytes = base64.b64decode(b64_str)
        decrypted_bytes = bytearray()
        for i, byte in enumerate(encrypted_bytes):
            key_byte = key[i % len(key)]
            decrypted_bytes.append(byte ^ key_byte)
        return decrypted_bytes.decode('utf-8', errors='ignore')
    except Exception:
        return None


def _nick_extract_jwt_info(jwt_token):
    try:
        payload_b64 = jwt_token.split('.')[1]
        payload_b64 += "=" * ((4 - len(payload_b64) % 4) % 4)
        decoded = json.loads(base64.urlsafe_b64decode(payload_b64).decode('utf-8'))
        account_id = decoded.get("account_id")
        enc_nick = decoded.get("nickname")
        old_name = _nick_decode_ff_name(enc_nick) if enc_nick else "Unknown"
        region = decoded.get("lock_region", "Unknown")
        release_version = decoded.get("release_version", "Unknown")
        return account_id, old_name, region, release_version
    except Exception:
        return None, "Unknown", "Unknown", "Unknown"


def _nick_execute_change(jwt_token, target_name, auth_type, region_hint=None):
    account_id, old_name, region, release_version = _nick_extract_jwt_info(jwt_token)

    url_region = (region_hint or region or "ME").upper()

    candidate_urls = []
    primary = _nick_get_url(url_region)
    if primary not in candidate_urls:
        candidate_urls.append(primary)
    if NICK_DEFAULT_URL not in candidate_urls:
        candidate_urls.append(NICK_DEFAULT_URL)

    msg = nick_data_pb2.Message()
    msg.data = target_name.encode("utf-8")
    msg.timestamp = int(time.time() * 1000)
    encrypted_data = aes_cbc_encrypt(MAIN_KEY, MAIN_IV, msg.SerializeToString())

    request_headers = {
        "Expect": "100-continue",
        "Authorization": f"Bearer {jwt_token}",
        "X-Unity-Version": "2018.4.11f1",
        "X-GA": "v1 1",
        "ReleaseVersion": RELEASEVERSION,
        "Content-Type": "application/octet-stream",
        "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 11; SM-A305F Build/RP1A.200720.012)",
        "Connection": "Keep-Alive",
        "Accept-Encoding": "gzip",
    }

    last_response = None
    used_url = None
    for url in candidate_urls:
        try:
            resp = requests.post(url, data=encrypted_data, headers=request_headers,
                                 verify=False, timeout=15)
            last_response = resp
            used_url = url
            if resp.status_code == 200:
                break
        except Exception as e:
            app.logger.warning(f"[nick] {url} failed: {e}")
            continue

    if last_response is None:
        return jsonify({
            "metadata": {
                "author": "SHAPPNO",
                "timestamp": time.strftime("%Y-%m-%d %H:%M:%S")
            },
            "response_status": "ERROR",
            "error_message": "All nickname servers failed"
        }), 500

    success_flag = last_response.status_code == 200

    try:
        raw_text = last_response.content.decode('utf-8', errors='ignore')
        plaintext = ''.join(c for c in raw_text if ord(c) >= 32)
    except Exception:
        plaintext = last_response.text

    result = {
        "metadata": {
            "author": "SHAPPNO",
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S")
        },
        "response_status": "SUCCESS" if success_flag else "FAILED",
        "operation_message": "Nickname successfully changed!" if success_flag else "Failed to alter nickname.",
        "http_status_code": last_response.status_code,
        "used_url": used_url,
        "account_details": {
            "authentication_method": auth_type,
            "account_id": account_id,
            "old_name": old_name,
            "new_name": target_name,
            "region": url_region,
            "release_version": release_version,
        },
        "server_feedback": {
            "headers": dict(last_response.headers),
            "raw_hexadecimal": last_response.content.hex(),
            "plaintext_response": plaintext
        }
    }
    return jsonify(result), last_response.status_code


@app.route("/guest", methods=["GET"])
def api_nick_guest():
    uid = request.args.get("uid")
    pwd = request.args.get("password")
    name = request.args.get("name")
    region_hint = request.args.get("region")

    if not uid or not pwd or not name:
        return jsonify({
            "response_status": "ERROR",
            "error_message": "Missing uid, password, or name"
        }), 400

    if region_hint and region_hint.upper() in CLAN_REGION_SERVER_MAP:
        order = [region_hint.upper()]
    else:
        order = ["ME", "IND", "BR", "US"]

    last_err = None
    for r in order:
        result, _, error = create_user_jwt(uid, pwd, region=r)
        if error or not result or not result.token:
            last_err = error or "JWT generation failed"
            continue
        return _nick_execute_change(
            jwt_token=result.token,
            target_name=name,
            auth_type=f"UID_PASS({r})",
            region_hint=r
        )

    return jsonify({
        "response_status": "ERROR",
        "error_message": f"JWT generation failed: {last_err}"
    }), 401


@app.route("/jwt-to-change", methods=["GET"])
def api_nick_jwt():
    jwt_token = request.args.get("jwt")
    name = request.args.get("name")
    region_hint = request.args.get("region")

    if not jwt_token or not name:
        return jsonify({
            "response_status": "ERROR",
            "error_message": "Missing jwt or name"
        }), 400

    return _nick_execute_change(
        jwt_token=jwt_token,
        target_name=name,
        auth_type="JWT_DIRECT",
        region_hint=region_hint
    )


EMOTE_DATA_HEX = "CA F6 83 22 2A 25 C7 BE FE B5 1F 59 54 4D B3 13"
EMOTE_DATA = bytes.fromhex(EMOTE_DATA_HEX.replace(" ", ""))

EMOTE_REGION_SERVER_MAP = {
    "BD": "https://clientbp.ppmainecoonghj.com",
    "IND": "https://client.ind.freefiremobile.com",
    "PK": "https://clientbp.ppmainecoonghj.com",
    "ME": "https://clientbp.ppmainecoonghj.com",
    "VN": "https://clientbp.ppmainecoonghj.com",
    "SG": "https://clientbp.ppmainecoonghj.com",
    "ID": "https://clientbp.ppmainecoonghj.com",
    "TH": "https://clientbp.ppmainecoonghj.com",
    "BR": "https://client.us.freefiremobile.com",
    "NA": "https://client.us.freefiremobile.com",
    "US": "https://client.us.freefiremobile.com",
    "RU": "https://clientbp.ggpolarbear.com",
}

EMOTE_BASE_HEADERS = {
    "Accept-Encoding": "gzip",
    "Connection": "Keep-Alive",
    "Content-Type": "application/x-www-form-urlencoded",
    "Expect": "100-continue",
    "ReleaseVersion": RELEASEVERSION,
    "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 9; G011A Build/PI)",
    "X-GA": "v1 1",
    "X-Unity-Version": "2018.4.11f1",
}


def _emote_decode_jwt_payload(token):
    try:
        parts = token.split('.')
        if len(parts) != 3:
            return None
        payload_b64 = parts[1]
        payload_b64 += '=' * ((4 - len(payload_b64) % 4) % 4)
        payload_bytes = base64.urlsafe_b64decode(payload_b64)
        return json.loads(payload_bytes)
    except Exception:
        return None


def _emote_get_region(payload):
    return payload.get("noti_region") or payload.get("lock_region")


def _emote_get_real_uid(payload):
    return payload.get("account_id") or payload.get("external_uid")


def _emote_send_request(jwt, base_url):
    url = f"{base_url}/ChooseEmote"
    headers = EMOTE_BASE_HEADERS.copy()
    headers["Authorization"] = f"Bearer {jwt}"
    return requests.post(url, headers=headers, data=EMOTE_DATA, timeout=15, verify=False)


def _emote_perform_flow(jwt_token):
    payload = _emote_decode_jwt_payload(jwt_token)
    if not payload:
        return False, "invalid_jwt"

    region = _emote_get_region(payload)
    if not region:
        return False, "no_region"

    server_url = EMOTE_REGION_SERVER_MAP.get(region.upper())
    if not server_url:
        return False, "unsupported_region"

    try:
        resp = _emote_send_request(jwt_token, server_url)
    except requests.exceptions.RequestException:
        return False, "request_failed"

    if resp.status_code != 200:
        return False, f"http_{resp.status_code}"

    body_text = ""
    try:
        body_text = resp.content.decode('utf-8', errors='ignore')
    except Exception:
        pass

    if "BR_INVENTORY_NOT_ENOUGH_ITEMS" in body_text:
        return False, "emote_not_in_vault"

    return True, "ok"


@app.route('/emote-eq', methods=['GET'])
def api_emote_eq():
    if request.args.get('emote_enquip') is None:
        return jsonify({"result": "failed", "reason": "missing_emote_enquip"}), 400

    uid = request.args.get('uid')
    password = request.args.get('password')
    region_hint = request.args.get('region')

    if not uid or not password:
        return jsonify({"result": "failed", "reason": "missing_uid_or_password"}), 400

    if region_hint and region_hint.upper() in EMOTE_REGION_SERVER_MAP:
        order = [region_hint.upper()]
    else:
        order = ["ME", "IND", "BR", "US"]

    last_err = None
    for r in order:
        result, _, error = create_user_jwt(uid, password, region=r)
        if error or not result or not result.token:
            last_err = error or "JWT generation failed"
            continue

        payload = _emote_decode_jwt_payload(result.token)
        real_uid = _emote_get_real_uid(payload) if payload else None

        ok, reason = _emote_perform_flow(result.token)

        if ok:
            return jsonify({
                "result": "success",
                "uid": real_uid,
                "region": r,
            }), 200
        else:
            return jsonify({
                "result": "failed",
                "uid": real_uid,
                "reason": reason,
            }), 400

    return jsonify({
        "result": "failed",
        "reason": f"JWT generation failed: {last_err}",
    }), 401



@app.route('/decode', methods=['GET'])
def decode_jwt_endpoint():
    token = request.args.get('token')
    if not token:
        return jsonify({"error": "Token parameter is required"}), 400

    parts = token.split('.')
    if len(parts) != 3:
        return jsonify({"error": "Invalid JWT format"}), 400

    def decode_base64(data):
        try:
            data += '=' * (-len(data) % 4)  # Add padding
            return json.loads(base64.urlsafe_b64decode(data).decode('utf-8'))
        except Exception as e:
            return {"error": f"Failed to decode token: {str(e)}"}

    payload = decode_base64(parts[1])
    if "error" in payload:
        return jsonify(payload), 400

    try:
        if 'exp' in payload and isinstance(payload['exp'], (int, float)):
            payload['exp_date'] = datetime.utcfromtimestamp(payload['exp']).strftime('%Y-%m-%d %H:%M:%S')
        if 'lock_region_time' in payload and isinstance(payload['lock_region_time'], (int, float)):
            payload['lock_region_date'] = datetime.utcfromtimestamp(payload['lock_region_time']).strftime('%Y-%m-%d %H:%M:%S')
    except Exception:
        pass

    return jsonify(payload), 200





# ---------------- BAN CHECK (uses APISS JWT + INFO account credentials) ----------------
def _bc_varint(value):
    value = int(value)
    out = bytearray()
    while value > 0x7f:
        out.append((value & 0x7f) | 0x80)
        value >>= 7
    out.append(value)
    return bytes(out)

def _bc_encode_request(uid):
    fields = ((1, int(uid)), (2, 9), (3, 1), (4, 1))
    return b"".join(_bc_varint((field << 3) | 0) + _bc_varint(value)
                    for field, value in fields)

def _bc_read_varint(data, pos):
    value = shift = 0
    while pos < len(data):
        byte = data[pos]
        pos += 1
        value |= (byte & 0x7f) << shift
        if not byte & 0x80:
            return value, pos
        shift += 7
        if shift > 70:
            break
    raise ValueError("Invalid protobuf varint")

def _bc_decode_fields(data):
    """Decode protobuf wire fields while preserving nested message fields."""
    result = {}
    pos = 0
    while pos < len(data):
        tag, pos = _bc_read_varint(data, pos)
        field, wire = tag >> 3, tag & 7
        if not field:
            break
        if wire == 0:
            value, pos = _bc_read_varint(data, pos)
        elif wire == 1:
            if pos + 8 > len(data): break
            value, pos = data[pos:pos+8], pos+8
        elif wire == 2:
            size, pos = _bc_read_varint(data, pos)
            if size < 0 or pos + size > len(data): break
            value, pos = data[pos:pos+size], pos+size
        elif wire == 5:
            if pos + 4 > len(data): break
            value, pos = data[pos:pos+4], pos+4
        else:
            break
        key = str(field)
        if wire == 2:
            try:
                nested = _bc_decode_fields(value)
                # Player (1) and ban detail (81) are known nested messages,
                # including the valid empty-message case.
                if field in (1, 81) or nested:
                    value = nested
            except Exception:
                pass
        if key in result:
            if not isinstance(result[key], list):
                result[key] = [result[key]]
            result[key].append(value)
        else:
            result[key] = value
    return result

def _bc_format_timestamp(timestamp):
    try:
        ist = datetime.timezone(datetime.timedelta(hours=5, minutes=30))
        return datetime.datetime.fromtimestamp(int(timestamp), ist).strftime("%Y-%m-%d %H:%M:%S IST")
    except Exception:
        return None

def _bc_format_duration(seconds):
    seconds = max(0, int(seconds))
    days, seconds = divmod(seconds, 86400)
    hours, seconds = divmod(seconds, 3600)
    minutes, seconds = divmod(seconds, 60)
    parts = []
    if days: parts.append(f"{days} Days")
    if hours: parts.append(f"{hours} Hours")
    if minutes: parts.append(f"{minutes} Minutes")
    if seconds or not parts: parts.append(f"{seconds} Seconds")
    return ", ".join(parts)

async def _bc_fetch_ban_payload(uid, region):
    # APISS owns JWT generation/caching; no second login/JWT system is used here.
    token, locked_region, server_url = await get_token_info(region)
    if not token:
        raise RuntimeError(f"APISS JWT unavailable for region {region}")
    target_region = (locked_region or region or "BD").upper()
    candidates = _candidate_servers(target_region, server_url)
    request_body = _bc_encode_request(uid)
    encrypted = aes_cbc_encrypt(MAIN_KEY, MAIN_IV, request_body)
    headers = {
        "User-Agent": USERAGENT,
        "Authorization": token,
        "Content-Type": "application/x-www-form-urlencoded",
        "X-GA": "v1 1",
        "ReleaseVersion": RELEASEVERSION,
    }
    async with httpx.AsyncClient(timeout=15.0, verify=False) as client:
        last_error = None
        for base in candidates:
            try:
                response = await client.post(base.rstrip("/") + "/GetPlayerPersonalShow",
                                             content=encrypted, headers=headers)
                if response.status_code == 200 and response.content:
                    raw = response.content
                    # Some game responses prepend a 64-byte signature header.
                    for candidate in (raw, raw[64:] if len(raw) > 64 else b""):
                        decoded = _bc_decode_fields(candidate)
                        if decoded:
                            return decoded
                last_error = f"HTTP {response.status_code}"
            except Exception as exc:
                last_error = str(exc)
    raise RuntimeError(f"Ban-check game endpoint failed: {last_error or 'empty response'}")

def _bc_make_result(decoded, target_uid, info_data):
    top = decoded.get("1")
    if isinstance(top, list):
        top = top[0] if top else None
    if not isinstance(top, dict):
        return None
    ban_field = top.get("81")
    if isinstance(ban_field, list):
        ban_field = ban_field[0] if ban_field else None
    if not isinstance(ban_field, dict):
        ban_field = {}
    f4 = ban_field.get("4")
    f7 = ban_field.get("7")
    if isinstance(f4, list): f4 = f4[0] if f4 else None
    if isinstance(f7, list): f7 = f7[0] if f7 else None

    basic = (info_data or {}).get("basicInfo", {}) or {}
    # All identity/profile fields come from APISS /info, not the Ban Check payload.
    username = basic.get("nickname") or basic.get("userName") or ""
    region = basic.get("region") or ""
    level = int(basic.get("level") or 0)
    likes = int(basic.get("liked") or 0)

    banned = bool(ban_field)
    ban_ts = None
    since = None
    unban_time = None
    unban_ts = None
    status = "Not Banned"
    if banned:
        now = int(time.time())
        try:
            if f4 is not None:
                ban_ts = int(f4)
                since = _bc_format_duration(now - ban_ts)
        except (TypeError, ValueError):
            ban_ts = None
        if f7 is not None:
            status = "Temporary"
            try:
                remaining = max(0, int(f7))
                unban_time = _bc_format_duration(remaining)
                unban_ts = now + remaining
            except (TypeError, ValueError):
                pass
        else:
            status = "Permanent"

    return {
        "ok": True,
        "ban_date": _bc_format_timestamp(ban_ts) if ban_ts else "Unknown",
        "ban_date_ts": ban_ts,
        "banned": banned,
        "level": level,
        "likes": likes,
        "region": region,
        "since": since,
        "status": status,
        "uid": str(target_uid),
        "unban_time": unban_time,
        "unban_ts": unban_ts,
        "unban_date": _bc_format_timestamp(unban_ts) if unban_ts else None,
        "username": username,
    }

@app.route("/check", methods=["GET"])
def ban_check_endpoint():
    uid = (request.args.get("uid") or "").strip()
    if not uid.isdigit() or not 8 <= len(uid) <= 13:
        return jsonify({"ok": False, "error": "invalid uid (numeric, 8-13 digits)"}), 400
    try:
        # First resolve player profile via the same account credentials/JWT path as /info.
        region, info_data = asyncio.run(_try_regions(uid, None))
        decoded = asyncio.run(_bc_fetch_ban_payload(uid, region))
        result = _bc_make_result(decoded, uid, info_data)
        if not result:
            return jsonify({"ok": False, "error": "unexpected ban-check response format"}), 502
        return jsonify(result)
    except Exception as exc:
        logging.exception("Ban Check failed for uid=%s", uid)
        return jsonify({"ok": False, "error": str(exc)}), 502



# ── PROFILE ITEM API (integrated into APISS authentication) ────────────────
PROFILE_ITEM_URL = "https://clientbp.ppmainecoonghj.com/SetPlayerGalleryShowInfo"
PROFILE_ITEM_KEY = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
PROFILE_ITEM_IV = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])

def _profile_item_auth(args, body):
    uid = (args.get("uid") or body.get("uid") or "").strip()
    password = args.get("password") or body.get("password") or ""
    access_token = args.get("access") or args.get("access_token") or body.get("access") or body.get("access_token")
    jwt_token = args.get("jwt") or args.get("jwt_token") or body.get("jwt") or body.get("jwt_token")
    region = (args.get("region") or body.get("region") or "BD").upper()

    if uid and password:
        result, access, error = create_user_jwt(uid, password, region=region, lang="bn")
        if error or not result or not getattr(result, "token", None):
            raise RuntimeError(error or "Could not create JWT from UID/password.")
        token = result.token
        source = "uid_password"
    elif access_token:
        result, error = create_jwt_from_access_token(access_token, region=region, lang="bn")
        if error or not result or not getattr(result, "token", None):
            raise RuntimeError(error or "Could not create JWT from access token.")
        token = result.token
        source = "access_token"
    elif jwt_token:
        token = jwt_token.strip()
        source = "jwt"
    else:
        raise ValueError("Provide uid+password, access, or jwt.")

    token = token.removeprefix("Bearer ").strip()
    account_data = _jwt_decode_token(token) or {}
    account = {
        "uid": str(account_data.get("account_id") or account_data.get("external_uid") or uid or "Unknown"),
        "username": account_data.get("nickname") or account_data.get("user_name") or "Unknown",
        "region": account_data.get("noti_region") or account_data.get("lock_region") or region,
    }
    return token, source, account

def _profile_item_build_payload():
    data = profile_item_pb2.MainMessage()
    data.field_1 = 1
    container1 = data.field_2.add()
    container1.field_1 = 1
    items = [
        {"field_1": 2, "field_4": 1, "field_6": 212000000},
        {"field_1": 2, "field_4": 1, "field_5": 4, "field_6": 203000000},
        {"field_1": 2, "field_4": 1, "field_5": 2, "field_6": 212000000},
        {"field_1": 13, "field_3": 1, "field_6": 211000000},
        {"field_1": 13, "field_3": 1, "field_4": 2, "field_6": 211000000},
        {"field_1": 13, "field_3": 1, "field_5": 2, "field_6": 204000000},
        {"field_1": 13, "field_3": 1, "field_5": 4, "field_6": 205000000},
        {"field_1": 13, "field_3": 1, "field_4": 2, "field_5": 2, "field_6": 203000000},
        {"field_1": 13, "field_3": 1, "field_4": 2, "field_5": 4, "field_6": 211000000},
        {"field_1": 13, "field_3": 1, "field_4": 4, "field_6": 203000000},
        {"field_1": 13, "field_3": 1, "field_4": 4, "field_5": 2, "field_6": 204000000},
        {"field_1": 13, "field_3": 1, "field_4": 4, "field_5": 4, "field_6": 205000000},
        {"field_1": 13, "field_3": 1, "field_4": 6, "field_6": 203000000},
        {"field_1": 13, "field_3": 1, "field_4": 6, "field_5": 2, "field_6": 211000000},
        {"field_1": 13, "field_3": 1, "field_4": 6, "field_5": 4, "field_6": 204000000},
    ]
    for entry in items:
        item = container1.field_2.add()
        item.field_1 = entry["field_1"]
        for key in ("field_3", "field_4", "field_5"):
            if key in entry:
                setattr(item, key, entry[key])
        item.field_6.field_6 = entry["field_6"]

    container2 = data.field_2.add()
    container2.field_1 = 9
    item1 = container2.field_2.add()
    item1.field_4 = 3
    item1.field_6.field_14 = 3048205855
    item2 = container2.field_2.add()
    item2.field_4 = 3
    item2.field_5 = 3
    item2.field_6.field_14 = 3048205855
    return data.SerializeToString()

@app.route("/profile-item", methods=["GET", "POST"])
def profile_item_endpoint():
    args = request.args.to_dict()
    body = request.get_json(silent=True) or request.form.to_dict() or {}
    try:
        jwt_token, auth_source, account = _profile_item_auth(args, body)
        payload = _profile_item_build_payload()
        cipher = AES.new(PROFILE_ITEM_KEY, AES.MODE_CBC, PROFILE_ITEM_IV)
        encrypted = cipher.encrypt(crypto_pad(payload, AES.block_size))
        headers = {
            "Authorization": f"Bearer {jwt_token}",
            "X-Unity-Version": "2018.4.11f1",
            "X-GA": "v1 1",
            "ReleaseVersion": FreeFireVersion,
            "Content-Type": "application/octet-stream",
            "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 11; SM-A305F Build/RP1A.200720.012)",
            "Connection": "Keep-Alive",
        }
        response = requests.post(PROFILE_ITEM_URL, headers=headers, data=encrypted, timeout=30)
        if response.status_code == 200:
            return jsonify({
                "status": "success",
                "message": "Profile items updated successfully",
                "auth_source": auth_source,
                "ACCOUNT": account,
                "response": response.text,
            }), 200
        return jsonify({
            "status": "error",
            "message": f"Game server returned HTTP {response.status_code}",
            "auth_source": auth_source,
            "ACCOUNT": account,
            "response": response.text[:1000],
        }), 502
    except ValueError as exc:
        return jsonify({"status": "error", "message": str(exc)}), 400
    except Exception as exc:
        logging.exception("Profile Item request failed")
        return jsonify({"status": "error", "message": str(exc)}), 502


# --- LIKE + VISIT endpoints (same request/response handlers as LIKE+VISIT source) ---
@app.route("/like", methods=["GET"])
def merged_like_1():
    return like_visit.handle_like1()

@app.route("/like2", methods=["GET"])
def merged_like_2():
    return like_visit.handle_like2()

@app.route("/like3", methods=["GET"])
def merged_like_3():
    return like_visit.handle_like3()

@app.route("/like4", methods=["GET"])
def merged_like_4():
    return like_visit.handle_like4()

@app.route("/visit", methods=["GET"])
def merged_visit():
    return like_visit.handle_visit()


DASHBOARD_HTML = '<!DOCTYPE html>\n<html lang="en">\n<head>\n<meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">\n<meta name="theme-color" content="#090d20"><meta name="description" content="SHAPPNO API control center">\n<title>SHAPPNO — API Control Center</title>\n<style>\n:root{--bg:#080c1b;--panel:rgba(20,27,54,.76);--line:rgba(155,174,255,.17);--muted:#9ca9cb;--white:#f6f8ff;--cyan:#64e8ff;--violet:#a98bff;--green:#60f2b0;--red:#ff637d}\n*{box-sizing:border-box}html{scroll-behavior:smooth}body{margin:0;background:radial-gradient(ellipse at 12% 0%,#25245a 0,transparent 36%),radial-gradient(ellipse at 90% 15%,#123c59 0,transparent 30%),var(--bg);color:var(--white);font-family:Inter,ui-sans-serif,system-ui,-apple-system,Segoe UI,sans-serif;min-height:100vh;overflow-x:hidden}\nbody:before{content:"";position:fixed;inset:0;pointer-events:none;background-image:linear-gradient(rgba(255,255,255,.018) 1px,transparent 1px),linear-gradient(90deg,rgba(255,255,255,.018) 1px,transparent 1px);background-size:42px 42px;mask-image:linear-gradient(to bottom,black,transparent 80%)}\n.wrap{width:min(1420px,calc(100% - 34px));margin:auto;position:relative;z-index:1}\n.top{display:flex;align-items:center;justify-content:space-between;padding:24px 0}.brand{display:flex;gap:12px;align-items:center;font-weight:900;letter-spacing:2px}.logo{width:42px;height:42px;border-radius:14px;display:grid;place-items:center;background:linear-gradient(135deg,#62eaff,#a88bff);color:#071021;font-weight:1000;box-shadow:0 0 30px #65dfff55}\n.pill{border:1px solid var(--line);background:#ffffff09;border-radius:999px;padding:9px 13px;color:#b9c7e8;font-size:12px}.hero{padding:42px 0 32px;display:grid;grid-template-columns:1.4fr .6fr;gap:24px;align-items:center}.eyebrow{color:var(--cyan);font-size:11px;letter-spacing:3px;font-weight:800}.hero h1{font-size:clamp(38px,6vw,72px);line-height:.98;margin:14px 0 16px;letter-spacing:-3px}.grad{background:linear-gradient(90deg,#6ceaff,#a78bff 55%,#ff9fcf);background-clip:text;color:transparent}.hero p{max-width:660px;color:var(--muted);line-height:1.7;margin:0}.hero-side{border:1px solid var(--line);background:linear-gradient(145deg,#ffffff10,#ffffff04);border-radius:24px;padding:22px;box-shadow:0 20px 70px #0005;backdrop-filter:blur(18px)}.stat{font-size:38px;font-weight:900;letter-spacing:-2px}.stat small{font-size:13px;color:var(--muted);letter-spacing:0;font-weight:600}.side-row{display:flex;justify-content:space-between;color:var(--muted);font-size:12px;margin-top:14px}.bar{height:6px;border-radius:10px;background:#ffffff12;margin-top:8px;overflow:hidden}.bar i{display:block;width:100%;height:100%;background:linear-gradient(90deg,var(--cyan),var(--violet));border-radius:10px}\n.toolbar{display:flex;gap:12px;align-items:center;justify-content:space-between;margin:24px 0 16px;flex-wrap:wrap}.search{flex:1;min-width:220px;max-width:440px;background:#ffffff0a;border:1px solid var(--line);border-radius:14px;padding:13px 16px;color:white;outline:none}.search:focus,input:focus{border-color:#71dfff88;box-shadow:0 0 0 3px #71dfff15}.count{color:var(--muted);font-size:12px}\n.grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:16px;padding-bottom:34px}.api-card{--accent:#6ceaff;position:relative;overflow:hidden;border:1px solid var(--line);border-radius:21px;padding:19px;background:linear-gradient(145deg,rgba(28,37,72,.88),rgba(13,19,41,.88));box-shadow:0 12px 38px #0003;transition:transform .25s,border-color .25s,box-shadow .25s;backdrop-filter:blur(12px)}.api-card:before{content:"";position:absolute;top:0;left:0;right:0;height:2px;background:linear-gradient(90deg,transparent,var(--accent),transparent);opacity:.9}.api-card:hover{transform:translateY(-2px);border-color:color-mix(in srgb,var(--accent),transparent 48%);box-shadow:0 18px 42px #0005}.card-head{display:flex;justify-content:space-between;gap:10px;align-items:flex-start}.api-name{font-size:17px;font-weight:800}.path{display:inline-block;margin-top:7px;color:var(--accent);font:11px ui-monospace,monospace;background:#ffffff0a;border:1px solid #ffffff12;border-radius:7px;padding:5px 8px}.desc{color:var(--muted);font-size:12px;line-height:1.5;margin:12px 0 15px;min-height:18px}.method{font-size:10px;font-weight:900;letter-spacing:1px;border:1px solid #62eaff44;color:var(--cyan);padding:5px 8px;border-radius:7px}.fields{display:grid;grid-template-columns:1fr 1fr;gap:10px}.field label{display:block;color:#aebbdc;font-size:10px;margin:0 0 6px}.field select{width:100%;min-width:0;appearance:none;-webkit-appearance:none;border:1px solid #29436d;background:linear-gradient(145deg,#101d38,#091326);color:#eaf4ff;border-radius:11px;padding:11px 38px 11px 12px;font-size:12px;font-weight:700;outline:none;cursor:pointer;box-shadow:inset 0 1px 0 #ffffff0b;transition:border-color .2s,box-shadow .2s,background .2s}.field select:focus{border-color:#64e8ff;box-shadow:0 0 0 3px #64e8ff20;background:#132342}.field select option{background:#0b1428;color:#eaf4ff}.field.auth-mode{position:relative}.field.auth-mode:after{content:"⌄";position:absolute;right:14px;bottom:8px;color:#64e8ff;font-size:18px;pointer-events:none}.field input{width:100%;min-width:0;border:1px solid #ffffff18;background:#070d20a8;color:white;border-radius:10px;padding:10px;font-size:12px;outline:none}.actions{display:flex;gap:8px;margin-top:14px}.btn{border:0;border-radius:10px;padding:10px 13px;font-size:11px;font-weight:800;cursor:pointer;transition:.2s}.call{flex:1;color:#061020;background:linear-gradient(100deg,var(--accent),#b9a4ff)}.example{color:#c4cdef;background:#ffffff0d;border:1px solid #ffffff17}.btn:hover{filter:brightness(1.12);transform:translateY(-1px)}.btn:disabled{opacity:.55;cursor:wait;transform:none}.result{display:none;margin-top:13px;border:1px solid #ffffff16;background:#060a16;border-radius:12px;overflow:hidden}.result.show{display:block}.result-head{display:flex;justify-content:space-between;align-items:center;padding:9px 11px;color:#aab8dc;font-size:10px;border-bottom:1px solid #ffffff12}.result pre{white-space:pre-wrap;word-break:break-word;max-height:260px;overflow:auto;margin:0;padding:12px;color:#dce7ff;font:11px/1.6 ui-monospace,monospace}.result img{display:block;max-width:100%;max-height:260px;margin:10px auto;border-radius:8px}.copy{border:0;background:none;color:var(--cyan);cursor:pointer;font-size:10px}\n.logs{border:1px solid var(--line);border-radius:20px;background:#10172dba;padding:18px;margin:4px 0 42px}.log-title{display:flex;justify-content:space-between;align-items:center;margin-bottom:12px}.log-title h2{font-size:15px;margin:0}.log-list{display:flex;flex-direction:column;gap:7px;max-height:230px;overflow:auto}.log{display:flex;gap:10px;align-items:flex-start;padding:8px 10px;border-radius:9px;background:#ffffff06;font:11px ui-monospace,monospace}.log .time{color:#7f8eaf;white-space:nowrap}.log .msg{font-weight:800}.log .detail{color:#b9c6e3;white-space:pre-wrap;word-break:break-word}.footer{padding:20px 0 35px;text-align:center;color:#7180a4;font-size:11px}\n\n.splash{position:fixed;inset:0;z-index:1000;background:#070b19;display:grid;place-items:center;transition:opacity .8s,visibility .8s}.splash.hide{opacity:0;visibility:hidden}.splash-word{font-size:clamp(40px,10vw,100px);font-weight:1000;letter-spacing:8px;background:linear-gradient(110deg,#5feaff,#a58aff,#ff9bc8,#60f2b0,#5feaff);background-size:400% 100%;background-clip:text;color:transparent;animation:shine 2.2s linear infinite,zoom 1.2s ease both,glowPulse 1.8s ease-in-out infinite alternate,letterFloat 3.4s ease-in-out infinite;text-shadow:0 0 55px #6ceaff25;filter:drop-shadow(0 0 20px #6ceaff55);position:relative}\n.splash-word:after{content:"SHAPPNO";position:absolute;inset:0;background:linear-gradient(90deg,transparent,#ffffffd9,transparent);background-size:200% 100%;background-clip:text;color:transparent;animation:scan 2.8s ease-in-out infinite;mix-blend-mode:screen}\n@keyframes glowPulse{from{filter:drop-shadow(0 0 8px #6ceaff55)}to{filter:drop-shadow(0 0 34px #b58cffaa)}}\n@keyframes letterFloat{0%,100%{transform:translateY(0) scale(1)}50%{transform:translateY(-9px) scale(1.035)}}\n@keyframes scan{0%,15%{background-position:-120% 0}70%,100%{background-position:120% 0}}\n@keyframes shine{to{background-position:250%}}@keyframes zoom{from{opacity:0;transform:scale(.65);filter:blur(12px)}to{opacity:1;transform:scale(1);filter:blur(0)}}\n@media(max-width:1050px){.grid{grid-template-columns:repeat(2,minmax(0,1fr))}.hero{grid-template-columns:1fr .6fr}}@media(max-width:700px){.wrap{width:calc(100% - 22px)}.hero{grid-template-columns:1fr;padding-top:24px}.hero-side{display:none}.grid{grid-template-columns:1fr}.top{padding:16px 0}.hero h1{letter-spacing:-2px}.fields{gap:9px}.api-card{padding:16px}}\n\n.api-card{transition:transform .28s cubic-bezier(.2,.8,.2,1),border-color .28s,box-shadow .28s}\n.api-card:hover{transform:translateY(-2px)}\n.logo{animation:logoBreath 3s ease-in-out infinite;position:relative}.brand>span{background:linear-gradient(90deg,#f6f8ff,#69eaff,#c4a7ff,#f6f8ff);background-size:250%;background-clip:text;color:transparent;animation:shine 4s linear infinite}\n@keyframes logoBreath{0%,100%{box-shadow:0 0 18px #65dfff44,0 0 0 0 #65dfff22}50%{box-shadow:0 0 34px #65dfff99,0 0 0 7px #65dfff08}}\n.btn{position:relative;overflow:hidden}.btn:after{content:"";position:absolute;inset:-80% auto -80% -35%;width:28%;background:#ffffff55;transform:rotate(25deg);transition:left .45s}.btn:hover:after{left:125%}\n@media(max-width:700px){.hero{padding-bottom:18px}.api-card{border-radius:18px}.toolbar{margin-top:12px}}\n\n/* SHAPPNO refreshed interface */\n:root{--bg:#070b16;--panel:rgba(17,26,49,.82);--line:rgba(137,170,220,.19);--muted:#a8b6d1;--white:#f4f8ff;--cyan:#72e7ff;--violet:#a99bff;--green:#50e69b}\nbody{background:radial-gradient(ellipse at 8% -8%,#253b68 0,transparent 38%),radial-gradient(ellipse at 94% 8%,#123f49 0,transparent 32%),linear-gradient(145deg,#070b16,#0b1224 58%,#080d1b)}\n.top{padding:22px 0 18px}.logo{border-radius:50%;background:linear-gradient(145deg,#6fffd0,#19b879);color:#062418;box-shadow:0 0 22px #38e89a55}\n.pill{display:flex;align-items:center;gap:9px;background:#0d1c20;border-color:#36d88b55;color:#b8f8d7;font-weight:800;letter-spacing:1px}\n.online-dot{display:inline-block;width:9px;height:9px;border-radius:50%;background:#35e68b;box-shadow:0 0 0 4px #35e68b20,0 0 13px #35e68b;flex:0 0 auto}\n.hero{padding-top:36px}.hero-side,.api-card,.logs{background:linear-gradient(145deg,rgba(22,35,63,.92),rgba(10,18,36,.94));border-color:rgba(145,174,225,.2);box-shadow:0 16px 44px #0004}\n.api-card{border-radius:19px;transition:transform .2s ease,border-color .2s ease,box-shadow .2s ease}\n.api-card:hover{transform:translateY(-3px);box-shadow:0 18px 38px #0005}.auth-mode{padding:10px 11px;border:1px solid #64e8ff20;border-radius:13px;background:linear-gradient(135deg,#64e8ff0a,#a98bff08)}.auth-mode label{letter-spacing:1.2px!important;color:#80dff5!important}\n.search,.field input{background:#080f20;border-color:#ffffff1c}.search{border-radius:13px}\n.btn{border-radius:11px;letter-spacing:.35px}.call{background:linear-gradient(105deg,var(--accent),#c2b7ff)}\n.example{background:#ffffff0b}.result{background:#070c18}\n.urls-panel{display:flex;align-items:center;justify-content:space-between;gap:18px;margin:0 0 26px;padding:22px;border:1px solid #6fe7ff2b;border-radius:20px;background:linear-gradient(120deg,#10243a,#151b38 70%,#102b2c);box-shadow:0 16px 38px #0004}\n.urls-panel h2{font-size:18px;letter-spacing:.5px;margin:7px 0}.urls-panel p{font-size:12px;color:var(--muted);margin:0;line-height:1.5}\n.all-urls-btn{background:linear-gradient(110deg,#53e6b0,#69dfff);color:#061b20;padding:13px 19px;white-space:nowrap;box-shadow:0 7px 22px #38dca52a}\n\n\n\n\n\n@media(max-width:700px){.urls-panel{align-items:stretch;flex-direction:column}.all-urls-btn{width:100%}.splash-word{letter-spacing:6px}}\n\n\n/* Performance-friendly rendering for low-memory phones and concurrent users */\n.api-card,.hero-side,.logs{backdrop-filter:none!important;-webkit-backdrop-filter:none!important}\n.api-card{box-shadow:0 8px 22px #0003;transition:transform .14s ease,border-color .14s ease}\n.api-card:hover{box-shadow:0 10px 24px #0004;transform:translateY(-1px)}\n.btn{transition:filter .14s ease,transform .14s ease}\n@media(prefers-reduced-motion:reduce){*,*::before,*::after{animation-duration:.01ms!important;animation-iteration-count:1!important;scroll-behavior:auto!important;transition-duration:.01ms!important}}\n/* SHAPPNO motion pack + dashboard-wide visual refresh */\n.splash{background:#070b19;overflow:hidden}\n\n\n.splash-word{z-index:1;animation:shine 2.2s linear infinite,zoom 1.2s ease both,glowPulse 1.8s ease-in-out infinite alternate,letterFloat 3.4s ease-in-out infinite,wordTilt 5s ease-in-out infinite}\n.splash-word.mode-flip{animation:flipIn 1.15s cubic-bezier(.2,.8,.2,1) both,shine 2s linear infinite}.splash-word.mode-glitch{animation:glitchIn .9s steps(2,end) both,shine 2s linear infinite}.splash-word.mode-pop{animation:popIn .95s cubic-bezier(.16,1,.3,1) both,shine 2s linear infinite}.splash-word.mode-wave{animation:waveIn 1.2s ease both,shine 2s linear infinite}\n@keyframes orbitA{0%,100%{transform:scale(.88) rotate(0);opacity:.35}50%{transform:scale(1.08) rotate(160deg);opacity:.85}}@keyframes orbitB{0%,100%{transform:scale(1.1) rotate(0);opacity:.25}50%{transform:scale(.82) rotate(-150deg);opacity:.75}}\n@keyframes wordTilt{0%,100%{rotate:0deg}25%{rotate:-1.5deg}75%{rotate:1.5deg}}@keyframes flipIn{from{opacity:0;transform:perspective(700px) rotateX(-85deg) scale(.7);filter:blur(9px)}to{opacity:1;transform:perspective(700px) rotateX(0) scale(1);filter:blur(0)}}\n@keyframes glitchIn{0%{opacity:0;transform:translateX(-18px) skewX(18deg);text-shadow:5px 0 #ff5ca8,-5px 0 #5feaff}55%{opacity:1;transform:translateX(5px) skewX(-8deg)}100%{transform:translateX(0) skewX(0);text-shadow:none}}@keyframes popIn{0%{opacity:0;transform:scale(.15);filter:blur(18px)}70%{opacity:1;transform:scale(1.12)}100%{transform:scale(1);filter:blur(0)}}@keyframes waveIn{0%{opacity:0;transform:translateY(55px) rotateX(65deg);letter-spacing:22px}100%{opacity:1;transform:translateY(0) rotateX(0);letter-spacing:8px}}\n.api-card,.hero-side,.logs,.search,.field input,.pill,.btn,.result{backdrop-filter:blur(14px)}.api-card{animation:cardRise .65s both}.api-card:nth-child(3n+2){animation-delay:.07s}.api-card:nth-child(3n){animation-delay:.14s}\n@keyframes cardRise{from{opacity:0;transform:translateY(18px) scale(.985)}to{opacity:1;transform:translateY(0) scale(1)}}.field input{transition:border-color .22s,box-shadow .22s,background .22s,transform .22s}.field input:focus{transform:translateY(-1px);background:#0c1630}.search{transition:border-color .22s,box-shadow .22s,transform .22s}.search:focus{transform:translateY(-1px)}.btn:active{transform:scale(.97)}\n.result.show{animation:resultIn .3s ease both}@keyframes resultIn{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:translateY(0)}}@media(prefers-reduced-motion:reduce){*,*:before,*:after{animation-duration:.01ms!important;animation-iteration-count:1!important;scroll-behavior:auto!important;transition-duration:.01ms!important}}\n/* SHAPPNO visual refresh */\n.api-card{border:1px solid rgba(130,160,255,.22);background:linear-gradient(145deg,rgba(25,34,69,.92),rgba(12,18,39,.94));box-shadow:0 14px 38px rgba(0,0,0,.22);backdrop-filter:blur(14px)}\n.api-card:hover{border-color:rgba(100,232,255,.55);box-shadow:0 18px 46px rgba(34,190,255,.12);transform:translateY(-3px)}\n.btn{border:1px solid rgba(255,255,255,.12);box-shadow:0 7px 18px rgba(0,0,0,.18);transition:transform .2s,filter .2s,box-shadow .2s}\n.btn:hover{filter:brightness(1.12);box-shadow:0 10px 24px rgba(100,232,255,.16)}\n.field input,.field select,.search{border-color:rgba(145,170,255,.25);background:rgba(7,13,31,.78)}\n.result{border:1px solid rgba(100,232,255,.18);border-radius:14px}\n@media(max-width:700px){.wrap{width:min(100% - 22px,1420px)}.hero{gap:16px;padding-top:28px}.api-card{border-radius:18px}}\n\n:focus-visible{outline:2px solid var(--cyan);outline-offset:3px}\n.api-card{isolation:isolate}\n.api-card:after{content:"";position:absolute;inset:0;z-index:-1;pointer-events:none;background:radial-gradient(circle at 100% 0%,rgba(100,232,255,.075),transparent 42%)}\n.field input{width:100%;min-width:0;border:1px solid rgba(145,170,255,.25);border-radius:11px;padding:11px 12px;background:rgba(7,13,31,.78);color:var(--white);font-size:12px;outline:none}\n.field input:focus{border-color:var(--cyan);box-shadow:0 0 0 3px #64e8ff20}\n@media(max-width:1050px){.grid{grid-template-columns:repeat(2,minmax(0,1fr))}.hero{grid-template-columns:1fr}.hero-side{max-width:none}}\n@media(max-width:640px){.grid{grid-template-columns:1fr}.top{padding:17px 0}.hero h1{letter-spacing:-1.5px}.toolbar{align-items:stretch}.search{max-width:none;width:100%}.fields{grid-template-columns:1fr 1fr}.api-card{padding:16px}}\n</style></head>\n<body>\n<div class="splash" id="splash"><div class="splash-word">SHAPPNO</div></div>\n<div class="wrap">\n<header class="top"><div class="brand"><div class="logo">S</div><span>SHAPPNO <span style="color:#6ceaff">API</span></span></div><div class="pill"><span class="online-dot"></span>SYSTEM ONLINE</div></header>\n<section class="hero"><div><div class="eyebrow">POWERFUL · FAST · SIMPLE</div><h1>API CONTROL<br><span class="grad">CENTER.</span></h1></div><div class="hero-side"><div class="eyebrow">AVAILABLE ENDPOINTS</div><div class="stat"><span id="apiCount">26</span> <small>API SERVICES</small></div><div class="side-row"><span>API workspace</span><span>READY</span></div><div class="bar"><i></i></div><div class="side-row"><span>Live response viewer</span><span>ENABLED</span></div></div></section>\n<div class="toolbar"><input class="search" id="search" placeholder="⌕  Search API name or endpoint..." autocomplete="off"><span class="count" id="visibleCount"></span></div>\n<main class="grid" id="apiGrid"></main>\n<section class="urls-panel"><div><div class="eyebrow">QUICK COPY</div><h2>SHAPPNO API URLS</h2><p>ENJOY OUR APIS</p></div><button class="btn all-urls-btn" id="copyAllUrls">ALL URLS COPY</button></section>\n\n\n</div>\n<script>\nconst APIS=[{"name":"ACCESS TOKEN","path":"/access","desc":"Generate access token","fields":[["uid","UID","123456789"],["password","Password","YOUR_PASSWORD"]]},{"name":"JWT TOKEN","path":"/token","desc":"Create jwt token","fields":[["uid","UID","123456789"],["password","Password","YOUR_PASSWORD"]]},{"name":"PLAYER INFO","path":"/info","desc":"Full player profile and account details","fields":[["uid","UID","123456789"]]},{"name":"PROFILE ITEM","path":"/profile-item","desc":"Update profile gallery items using UID/password, access token, or JWT","authModes":[{"value":"uidpass","label":"UID + Password","fields":[["uid","UID","123456789"],["password","Password","YOUR_PASSWORD"],["region","Region (optional)","BD"]]},{"value":"access","label":"Access Token","fields":[["access","Access token","YOUR_ACCESS_TOKEN"],["region","Region (optional)","BD"]]},{"value":"jwt","label":"JWT Token","fields":[["jwt","JWT","YOUR_JWT"],["region","Region (optional)","BD"]]}],"fields":[["uid","UID","123456789"],["password","Password","YOUR_PASSWORD"],["region","Region (optional)","BD"]]},{"name":"BAN CHECK","path":"/check","desc":"Check account ban stands ","fields":[["uid","UID","123456789"]]},{"name":"LEVEL INFO","path":"/level","desc":"Player level information","fields":[["uid","UID","123456789"]]},{"name":"REGION INFO","path":"/region","desc":"Detect account region","fields":[["uid","UID","123456789"]]},{"name":"LEADER INFO","path":"/leader","desc":"Player leader information","fields":[["uid","UID","123456789"]]},{"name":"WISHLIST","path":"/wishlist","desc":"Get player wishlist items with photo","fields":[["uid","UID","123456789"]]},{"name":"OUTFIT","path":"/outfit","desc":"check player outfit","fields":[["uid","UID","123456789"]]},{"name":"ADD FRIEND","path":"/add_friend","desc":"add friend with friend request","fields":[["uid","Account UID","123456789"],["password","Account Password","YOUR_PASSWORD"],["friend_uid","Target UID","987654321"],["server_name","Server (optional)","BD"]]},{"name":"REMOVE FRIEND","path":"/rv_friend","desc":"Remove a friend from the account","fields":[["uid","Account UID","123456789"],["password","Account Password","YOUR_PASSWORD"],["friend_uid","Friend UID","987654321"],["server_name","Server (optional)","BD"]]},{"name":"SPAM RQ SEND","path":"/shappno-send","desc":"Send spam requests","fields":[["uid","Target UID","123456789"],["region","Region: bd / ind","bd"]]},{"name":"BANNER","path":"/banner","desc":"Check player banner","fields":[["uid","UID","123456789"]],"image":true},{"name":"DYNAMIC DUO","path":"/duo-ck","desc":"Dynamic Duo partner check","fields":[["uid","UID","123456789"]]},{"name":"JOIN GUILD","path":"/request_clan","desc":"Guild join request","authModes":[{"value":"uidpass","label":"UID + Password","fields":[["uid","UID","123456789"],["pass","Password","YOUR_PASSWORD"],["region","Region (optional)","BD"]]},{"value":"jwt","label":"JWT Token","fields":[["jwt","JWT","YOUR_JWT"],["region","Region (optional)","BD"]]}],"commonFields":[["clan_id","Clan ID","123456"]],"fields":[["clan_id","Clan ID","123456"],["uid","UID","123456789"],["pass","Password","YOUR_PASSWORD"],["region","Region (optional)","BD"]]},{"name":"QUIT GUILD","path":"/quit_clan","desc":"Leave a guild","authModes":[{"value":"uidpass","label":"UID + Password","fields":[["uid","UID","123456789"],["pass","Password","YOUR_PASSWORD"],["region","Region (optional)","BD"]]},{"value":"jwt","label":"JWT Token","fields":[["jwt","JWT","YOUR_JWT"],["region","Region (optional)","BD"]]}],"commonFields":[["clan_id","Clan ID","123456"]],"fields":[["clan_id","Clan ID","123456"],["uid","UID","123456789"],["pass","Password","YOUR_PASSWORD"],["region","Region (optional)","BD"]]},{"name":"GUEST NICKNAME CHANGE","path":"/guest","desc":"Guest account nickname change","fields":[["uid","UID","123456789"],["password","Password","YOUR_PASSWORD"],["name","Nickname","SHAPPNO"],["region","Region (optional)","BD"]]},{"name":"JWT TO NICKNAME CHANGE","path":"/jwt-to-change","desc":"Change nickname using JWT","fields":[["jwt","JWT","YOUR_JWT"],["name","New nickname","SHAPPNO"],["region","Region (optional)","BD"]]},{"name":"EMOTE EQUIP","path":"/emote-eq","desc":"Equip an emote","fields":[["uid","UID","123456789"],["password","Password","YOUR_PASSWORD"],["emote_enquip","Emote value","1"],["region","Region (optional)","BD"]]},{"name":"JWT DECODE","path":"/decode","desc":"decode your jwt","fields":[["token","JWT Token","YOUR_JWT"]]},{"name":"ITEM ","path":"/item","desc":"Get an item icon image by item ID","fields":[["id","Item ID","909000010"]],"image":true},{"name":"BIO UPLOAD","path":"/bio_upload","desc":"Update account bio using JWT, access token, or UID/password","authModes":[{"value":"uidpass","label":"UID + Password","fields":[["uid","UID","123456789"],["password","Password","YOUR_PASSWORD"]]},{"value":"access","label":"Access Token","fields":[["access","Access token","YOUR_ACCESS_TOKEN"]]},{"value":"jwt","label":"JWT Token","fields":[["jwt","JWT","YOUR_JWT"]]}],"commonFields":[["bio","Bio text","Hello from SHAPPNO"]],"fields":[["bio","Bio text","Hello from SHAPPNO"],["uid","UID","123456789"],["password","Password","YOUR_PASSWORD"]],"method":"GET"} ,{"name":"20+ LIKE API","path":"/like","desc":"Send 20+ likes","fields":[["uid","Target UID","123456789"],["server_name","Server","BD"],["key","API Key","LIKE_API_KEY"]]},\n{"name":"220 LIKE API","path":"/like2","desc":"Send 220 likes","fields":[["uid","Target UID","123456789"],["server_name","Server","BD"],["key","API Key","LIKE_API_KEY"]]},{"name":"VISIT API","path":"/visit","desc":"Send 15000+ profile visits ","fields":[["uid","Target UID","123456789"],["server_name","Server","BD"]]}];\nconst palette=[\'#63eaff\',\'#a98bff\',\'#60f2b0\',\'#ff9fcf\',\'#ffc46b\',\'#7eafff\',\'#ff7e9c\',\'#74e3cb\'];\nconst grid=document.getElementById(\'apiGrid\');\ndocument.getElementById(\'apiCount\').textContent=APIS.length;\nfunction escapeHtml(s){return String(s).replace(/[&<>"\']/g,c=>({\'&\':\'&amp;\',\'<\':\'&lt;\',\'>\':\'&gt;\',\'"\':\'&quot;\',"\'":\'&#39;\'}[c]));}\nfunction addLog(){}\nfunction fieldMarkup(fields){return (fields||[]).map(([key,label,example])=>`<div class="field"><label>${escapeHtml(label)}</label><input data-key="${escapeHtml(key)}" placeholder="${escapeHtml(example)}" ${[\'password\',\'pass\',\'jwt\',\'token\',\'access\'].includes(key)?\'type="password"\':\'\'}></div>`).join(\'\');}\nfunction renderFields(api,mode){const selected=(api.authModes||[]).find(x=>x.value===mode)||(api.authModes||[])[0];return fieldMarkup(api.commonFields)+(selected?fieldMarkup(selected.fields):fieldMarkup(api.fields));}\nfunction render(){const q=document.getElementById(\'search\').value.toLowerCase();const filtered=APIS.filter(a=>(a.name+\' \'+a.path+\' \'+a.desc).toLowerCase().includes(q));document.getElementById(\'visibleCount\').textContent=`${filtered.length} / ${APIS.length} APIs`;grid.innerHTML=filtered.map((a)=>{const idx=APIS.indexOf(a),accent=palette[idx%palette.length],mode=(a.authModes||[])[0]?.value||\'\';return `<article class="api-card" style="--accent:${accent}" data-path="${a.path}"><div class="card-head"><div><div class="api-name">${escapeHtml(a.name)}</div><span class="path">${escapeHtml(a.path)}</span></div><span class="method">${a.method||\'GET\'}</span></div><p class="desc">${escapeHtml(a.desc)}</p>${a.authModes?`<div class="field auth-mode"><label>AUTHENTICATION METHOD</label><select data-auth-select="${idx}">${a.authModes.map(x=>`<option value="${escapeHtml(x.value)}">${escapeHtml(x.label)}</option>`).join(\'\')}</select></div>`:\'\'}<div class="fields">${renderFields(a,mode)}</div><div class="actions"><button class="btn example" data-copy-url="${idx}">COPY URL</button><button class="btn call" data-call="${idx}">CALL API ↗</button></div><div class="result" id="result-${idx}"><div class="result-head"><span>API RESPONSE</span><button class="copy" data-copy="${idx}">COPY RESPONSE</button></div><pre></pre></div></article>`}).join(\'\');}\n\nasync function callApi(idx,button){const api=APIS[idx],card=button.closest(\'.api-card\'),params=new URLSearchParams();card.querySelectorAll(\'input\').forEach(input=>{if(input.value.trim())params.set(input.dataset.key,input.value.trim());});if(!params.toString()){addLog(api.name,false,\'Fill the required parameters first.\');return;}button.disabled=true;button.textContent=\'CALLING...\';const result=document.getElementById(`result-${idx}`);result.classList.add(\'show\');const pre=result.querySelector(\'pre\');pre.textContent=\'Connecting to API...\';try{const response=await fetch(api.path+\'?\'+params.toString(),{method:api.method||\'GET\',headers:{\'Accept\':\'application/json, text/plain, */*\'}});const type=response.headers.get(\'content-type\')||\'\';if(type.includes(\'image/\')){const blob=await response.blob(),url=URL.createObjectURL(blob);pre.innerHTML=\'\';const img=document.createElement(\'img\');img.src=url;pre.appendChild(img);addLog(api.name,response.ok,`${response.status} · image response`);result.dataset.response=\'Image response\';}else{const body=await response.text();let pretty=body;try{pretty=JSON.stringify(JSON.parse(body),null,2)}catch{}pre.textContent=pretty;result.dataset.response=pretty;if(response.ok)addLog(api.name,true,`${response.status} · ${api.path}`);else addLog(api.name,false,`${response.status} · ${pretty}`);}}catch(err){pre.textContent=String(err);result.dataset.response=String(err);addLog(api.name,false,String(err));}finally{button.disabled=false;button.textContent=\'CALL API ↗\';}}\ngrid.addEventListener(\'change\',e=>{const select=e.target.closest(\'[data-auth-select]\');if(!select)return;const idx=Number(select.dataset.authSelect),api=APIS[idx],card=select.closest(\'.api-card\');if(card&&api)card.querySelector(\'.fields\').innerHTML=renderFields(api,select.value);});\ngrid.addEventListener(\'click\',e=>{const urlBtn=e.target.closest(\'[data-copy-url]\');if(urlBtn){const idx=+urlBtn.dataset.copyUrl,card=urlBtn.closest(\'.api-card\'),params=new URLSearchParams();card.querySelectorAll(\'input\').forEach(input=>{if(input.value.trim())params.set(input.dataset.key,input.value.trim());});const fullUrl=location.origin+APIS[idx].path+(params.toString()?\'?\'+params.toString():\'\');if(navigator.clipboard&&navigator.clipboard.writeText){navigator.clipboard.writeText(fullUrl).then(()=>{urlBtn.textContent=\'COPIED ✓\';setTimeout(()=>urlBtn.textContent=\'COPY URL\',1200)}).catch(()=>window.prompt(\'Copy API URL\',fullUrl));}else{window.prompt(\'Copy API URL\',fullUrl);}return;}const call=e.target.closest(\'[data-call]\');if(call){callApi(+call.dataset.call,call);return;}const cp=e.target.closest(\'[data-copy]\');if(cp){const r=document.getElementById(`result-${cp.dataset.copy}`);const t=r.dataset.response||r.querySelector(\'pre\').innerText;navigator.clipboard?.writeText(t);cp.textContent=\'COPIED\';setTimeout(()=>cp.textContent=\'COPY RESPONSE\',1000);}});\n\nconst ALL_URLS_TEXT="SHAPPNO APIS\\n\\n1. ACCESS TOKEN\\n   http://127.0.0.1:5000/access?uid=YOUR_UID&password=YOUR_PASSWORD\\n\\n2. JWT  TOKEN\\n   http://127.0.0.1:5000/token?uid=YOUR_UID&password=YOUR_PASSWORD\\n\\n3. INFO\\n   http://127.0.0.1:5000/info?uid=YOUR_UID\\n\\n4. PROFILE ITEM\\n   http://127.0.0.1:5000/profile-item?uid=MY_UID&password=MY_PASS\\n   http://127.0.0.1:5000/profile-item?access=MY_ACCESS_TOKEN\\n   http://127.0.0.1:5000/profile-item?jwt=MY_JWT_TOKEN\\n\\n5. LEVEL INFO\\n   http://127.0.0.1:5000/level?uid=YOUR_UID\\n\\n5. REGION INFO\\n   http://127.0.0.1:5000/region?uid=YOUR_UID\\n\\n6. LEADER INFO\\n   http://127.0.0.1:5000/leader?uid=YOUR_UID\\n\\n7. WISHLIST INFO (PICTURE)\\n   http://127.0.0.1:5000/wishlist?uid=YOUR_UID\\n\\n8. OUTFIT INFO\\n   http://127.0.0.1:5000/outfit?uid=YOUR_UID\\n\\n9. ADD FRIEND\\n   http://127.0.0.1:5000/add_friend?uid=YOUR_UID&password=YOUR_PASSWORD&friend_uid=TARGET_UID\\n\\nhttp://127.0.0.1:5000/add_friend?uid=YOUR_UID&password=YOUR_PASSWORD&friend_uid=TARGET_UID&server_name=REGION\\n\\n10. REMOVE FRIEND\\n    http://127.0.0.1:5000/rv_friend?uid=YOUR_UID&password=YOUR_PASSWORD&friend_uid=TARGET_UID\\n\\n11. FRIEND RQ SEND SPAM\\n    http://127.0.0.1:5000/shappno-send?uid=YOUR_UID&region=REGION\\n\\n12. SHAPPNO BANNER (PICTURE)\\n    http://127.0.0.1:5000/banner?uid=YOUR_UID\\n\\n13. DUO INFO\\n    http://127.0.0.1:5000/duo-ck?uid=YOUR_UID\\n\\n14. REQUEST CLAN (GUILD RQ)\\n    http://127.0.0.1:5000/request_clan?uid=YOUR_UID&pass=YOUR_PASS&clan_id=CLAN_ID\\n\\nhttp://127.0.0.1:5000/request_clan?uid=YOUR_UID&pass=YOUR_PASSWORD&clan_id=CLAN_ID&region=REGION\\n\\n16. QUIT CLAN (GUILD LEAVE)\\n    http://127.0.0.1:5000/quit_clan?uid=YOUR_UID&pass=YOUR_PASS&clan_id=CLAN_ID\\n\\n17. GUEST (NAME CHANGE)\\n    http://127.0.0.1:5000/guest?uid=YOUR_UID&password=YOUR_PASS&name=NEW_NAME\\n\\nhttp://127.0.0.1:5000/guest?uid=YOUR_UID&password=YOUR_PASSWORD&name=YOUR_NAME&region=REGION\\n\\n18. JWT ( NMAE CHANGE)\\n    http://127.0.0.1:5000/jwt-to-change?jwt=YOUR_JWT&name=YOUR_NAME\\n\\n19. EMOTE EQUIPMENT (FF EMOTE EQ)\\n  http://127.0.0.1:5000/emote-eq?uid=YOUR_UID&password=YOUR_PASS&emote_enquip=1\\n\\nhttp://127.0.0.1:5000/emote-eq?uid=YOUR_UID&password=YOUR_PASSWORD&emote_enquip=1&region=YOUR_REGION\\n\\n19. DECODE JWT\\n    http://127.0.0.1:5000/decode?token=YOUR_JWT_TOKEN\\n\\n21. BIO UPLOAD\\n    http://127.0.0.1:5000/bio_upload?uid=YOUR_UID&pass=YOUR_PASS&bio=Hello-fck\\n\\nhttp://127.0.0.1:5000/bio_upload?jwt=YOUR_JWT&bio=Hello-fck\\n\\nhttp://127.0.0.1:5000/bio_upload?access=YOUR_ACCESS_TOKEN&bio=Hello-fck\\n\\n22. 20 LIKE API \\n    http://127.0.0.1:5000/like?uid=TARGET_UID&server_name=BD&key=YOUR_LIKE_KEY\\n\\n23. 220 LIKE API\\n    http://127.0.0.1:5000/like2?uid=TARGET_UID&server_name=BD&key=YOUR_LIKE_KEY\\n\\n24. VISIT API\\n    http://127.0.0.1:5000/visit?uid=TARGET_UID&server_name=BD&target=15000";\nconst copyAllButton=document.getElementById(\'copyAllUrls\');\ncopyAllButton.addEventListener(\'click\',async()=>{\n  try{\n    if(navigator.clipboard&&window.isSecureContext){await navigator.clipboard.writeText(ALL_URLS_TEXT);}\n    else{\n      const area=document.createElement(\'textarea\');area.value=ALL_URLS_TEXT;\n      area.setAttribute(\'readonly\',\'\');area.style.position=\'fixed\';area.style.opacity=\'0\';\n      document.body.appendChild(area);area.select();\n      const copied=document.execCommand(\'copy\');area.remove();\n      if(!copied)throw new Error(\'Clipboard copy is not available\');\n    }\n    copyAllButton.textContent=\'COPIED ✓\';\n    setTimeout(()=>copyAllButton.textContent=\'ALL URLS COPY\',1400);\n  }catch(err){\n    const area=document.createElement(\'textarea\');area.value=ALL_URLS_TEXT;\n    area.style.position=\'fixed\';area.style.opacity=\'0\';document.body.appendChild(area);\n    area.select();document.execCommand(\'copy\');area.remove();\n    copyAllButton.textContent=\'COPIED ✓\';\n    setTimeout(()=>copyAllButton.textContent=\'ALL URLS COPY\',1400);\n  }\n});\n\ndocument.getElementById(\'search\').addEventListener(\'input\',render);\nrender();(()=>{const splash=document.getElementById(\'splash\');if(!splash)return;const word=splash.querySelector(\'.splash-word\'),modes=[\'mode-flip\',\'mode-glitch\',\'mode-pop\',\'mode-wave\'];let n=0;const cycle=()=>{if(!word)return;word.classList.remove(...modes);void word.offsetWidth;word.classList.add(modes[n++%modes.length]);};cycle();const motion=setInterval(()=>{if(splash.classList.contains(\'hide\')){clearInterval(motion);return;}cycle();},720);setTimeout(()=>{splash.classList.add(\'hide\');clearInterval(motion);},2900);})();\n</script></body></html>'
@app.route("/")
def shappno_home():
    return Response(DASHBOARD_HTML, mimetype="text/html; charset=utf-8")


# ============================================================
# ADMIN PANEL ROUTES / UI (kept at the bottom)
# ============================================================
ADMIN_PANEL_HTML = '''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>SHAPPNO Admin</title><style>
*{box-sizing:border-box}body{margin:0;min-height:100vh;background:radial-gradient(circle at 10% 0,#233b69,transparent 38%),radial-gradient(circle at 90% 10%,#173e54,transparent 34%),#070b17;color:#f4f7ff;font:15px system-ui}.wrap{max-width:980px;margin:auto;padding:26px}.panel{background:#111b32;border:1px solid #314568;border-radius:20px;padding:22px;margin:16px 0;box-shadow:0 15px 45px #0005}h1{margin:8px 0 22px;letter-spacing:.4px}.muted{color:#aab9d5}.key-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:14px;margin:14px 0}.key-grid label{display:block;color:#b8c8e8;font-size:12px;font-weight:700}.key-grid input{display:block;width:100%;margin-top:7px;padding:13px 14px;border-radius:12px;border:1px solid #3a527b;background:#091326;color:#f5f8ff;outline:none}.key-grid input:focus{border-color:#63eaff;box-shadow:0 0 0 3px #63eaff20}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:12px}.stat{background:#0b1326;border:1px solid #283b5e;border-radius:14px;padding:16px}.num{font-size:30px;font-weight:800;color:#72e7ff}input{width:100%;padding:13px;border-radius:10px;border:1px solid #3b5075;background:#080f20;color:white;margin:8px 0 12px}button{border:0;border-radius:10px;padding:12px 17px;margin:5px 5px 5px 0;font-weight:800;background:linear-gradient(100deg,#63eaff,#a88bff);color:#071020;cursor:pointer}.danger{background:#ff6684;color:#250712}.good{background:#62efb1;color:#061a12}.row{display:flex;gap:10px;flex-wrap:wrap;align-items:center}.hidden{display:none}pre{white-space:pre-wrap;word-break:break-word;color:#cbd8f2}</style></head><body><main class="wrap"><h1>SHAPPNO <span style="color:#70eaff">ADMIN</span></h1><p class="muted">Secure control center</p>
<section id="login" class="panel"><h2>Admin Login</h2><input id="password" type="password" placeholder="Admin password"><button onclick="login()">LOGIN</button><p id="loginMsg" class="muted"></p></section>
<div id="dashboard" class="hidden"><section class="panel"><h2>Service Control</h2><p id="lockState" class="muted">Loading...</p><div class="row"><button class="good" onclick="setLock(false)">TURN ON</button><button class="danger" onclick="setLock(true)">TURN OFF / LOCK WEBSITE</button></div></section>
<section class="panel"><h2>API Statistics</h2><div class="grid"><div class="stat"><div class="num" id="calls">0</div><div class="muted">Total API calls</div></div><div class="stat"><div class="num" id="likeCalls">0</div><div class="muted">Like endpoint calls</div></div><div class="stat"><div class="num" id="likes">0</div><div class="muted">Likes given (reported)</div></div></div><h3>Endpoint calls</h3><pre id="endpoints"></pre></section>
<section class="panel"><h2>Like API Keys</h2><div class="key-grid">
<label>Like API 1 Key<input id="key1" type="text" autocomplete="off"></label>
<label>Like API 2 Key<input id="key2" type="text" autocomplete="off"></label>
<label>Like API 3 Key<input id="key3" type="text" autocomplete="off"></label>
<label>Like API 4 Key<input id="key4" type="text" autocomplete="off"></label>
</div><button onclick="saveKeys()">SAVE API KEYS</button><p class="muted">Changes apply immediately to /like, /like2, /like3 and /like4.</p></section>
<section class="panel"><h2>Runtime Data</h2><p class="muted">Deletes generated files inside the runtime data folder. Original account credentials, Proto files, app.py and admin settings are preserved.</p><button class="danger" onclick="clearData()">ALL DATA DELETE</button></section><button onclick="logout()">LOG OUT</button><p id="msg" class="muted"></p></div></main>
<script>
async function api(path,data){const r=await fetch(path,{method:data?'POST':'GET',headers:data?{'Content-Type':'application/json'}:{},body:data?JSON.stringify(data):undefined});const j=await r.json();if(!r.ok)throw Error(j.message||j.error||'Request failed');return j}
async function login(){try{await api('/admin-shappno/login',{password:document.getElementById('password').value});document.getElementById('login').classList.add('hidden');document.getElementById('dashboard').classList.remove('hidden');await refresh();setInterval(refresh,5000)}catch(e){document.getElementById('loginMsg').textContent=e.message}}
async function refresh(){try{const s=await api('/admin-shappno/stats');document.getElementById('lockState').textContent=s.locked?'WEBSITE LOCKED':'WEBSITE ONLINE';document.getElementById('calls').textContent=s.api_calls;document.getElementById('likeCalls').textContent=s.like_calls;document.getElementById('likes').textContent=s.likes_given;document.getElementById('endpoints').textContent=JSON.stringify(s.endpoint_calls,null,2);document.getElementById('key1').value=s.like_key_1;document.getElementById('key2').value=s.like_key_2;document.getElementById('key3').value=s.like_key_3;document.getElementById('key4').value=s.like_key_4}catch(e){document.getElementById('msg').textContent=e.message}}
async function setLock(v){try{await api('/admin-shappno/lock',{locked:v});await refresh()}catch(e){alert(e.message)}}
async function saveKeys(){try{await api('/admin-shappno/keys',{key1:document.getElementById('key1').value,key2:document.getElementById('key2').value,key3:document.getElementById('key3').value,key4:document.getElementById('key4').value});document.getElementById('msg').textContent='Keys updated.'}catch(e){alert(e.message)}}
async function clearData(){if(!confirm('Delete all generated runtime data now?'))return;try{const x=await api('/admin-shappno/clear-data',{});document.getElementById('msg').textContent=x.message;await refresh()}catch(e){alert(e.message)}}
async function logout(){await api('/admin-shappno/logout',{});location.reload()}
</script></body></html>'''

@app.route("/admin-shappno", methods=["GET"])
def admin_panel():
    return Response(ADMIN_PANEL_HTML, mimetype="text/html; charset=utf-8")

@app.route("/admin-shappno/login", methods=["POST"])
def admin_login():
    payload = request.get_json(silent=True) or {}
    if str(payload.get("password", "")) != ADMIN_PASSWORD:
        return jsonify({"status": "error", "message": "Invalid admin password"}), 401
    from flask import session
    session["shappno_admin"] = True
    return jsonify({"status": "success"})

def _require_admin():
    from flask import session
    return bool(session.get("shappno_admin"))

@app.route("/admin-shappno/stats", methods=["GET"])
def admin_stats():
    if not _require_admin(): return jsonify({"message": "Unauthorized"}), 401
    with _ADMIN_LOCK:
        return jsonify({k: _ADMIN_STATE[k] for k in ("locked", "api_calls", "like_calls", "likes_given", "endpoint_calls", "like_key_1", "like_key_2", "like_key_3", "like_key_4")})

@app.route("/admin-shappno/lock", methods=["POST"])
def admin_lock():
    if not _require_admin(): return jsonify({"message": "Unauthorized"}), 401
    payload = request.get_json(silent=True) or {}
    with _ADMIN_LOCK:
        _ADMIN_STATE["locked"] = bool(payload.get("locked"))
        _save_admin_state()
    return jsonify({"status": "success", "locked": _ADMIN_STATE["locked"]})

@app.route("/admin-shappno/keys", methods=["POST"])
def admin_keys():
    if not _require_admin(): return jsonify({"message": "Unauthorized"}), 401
    payload = request.get_json(silent=True) or {}
    keys = {
        1: str(payload.get("key1", "")).strip(),
        2: str(payload.get("key2", "")).strip(),
        3: str(payload.get("key3", _ADMIN_STATE.get("like_key_3", LIKE_API_KEY_3))).strip(),
        4: str(payload.get("key4", _ADMIN_STATE.get("like_key_4", LIKE_API_KEY_4))).strip(),
    }
    if not all(keys.values()):
        return jsonify({"message": "All four Like API keys are required"}), 400
    with _ADMIN_LOCK:
        for number, value in keys.items():
            _ADMIN_STATE[f"like_key_{number}"] = value
            setattr(like_visit, f"KEY_LIKE{number}", value)
        _save_admin_state()
    return jsonify({"status": "success"})

@app.route("/admin-shappno/clear-data", methods=["POST"])
def admin_clear_data():
    if not _require_admin(): return jsonify({"message": "Unauthorized"}), 401
    data_dir = getattr(like_visit, "STORAGE_DIR", os.path.join(os.path.dirname(__file__), "data"))
    os.makedirs(data_dir, exist_ok=True)
    removed = 0
    for name in os.listdir(data_dir):
        path = os.path.join(data_dir, name)
        try:
            if os.path.isfile(path) or os.path.islink(path): os.remove(path)
            elif os.path.isdir(path): shutil.rmtree(path)
            removed += 1
        except OSError:
            app.logger.exception("Could not remove runtime data: %s", path)
    # Reset in-memory engine caches as well as generated files.
    with _API_TOKEN_RESPONSE_LOCK:
        _API_TOKEN_RESPONSE_CACHE.clear()
    for attr in ("TOKEN_CACHE", "VISIT_TOKEN_CACHE", "FAILED_TOKENS", "PLAYER_CACHE", "LIKE_CACHE"):
        value = getattr(like_visit, attr, None)
        if hasattr(value, "clear"):
            try: value.clear()
            except Exception: pass
    with _ADMIN_LOCK:
        _ADMIN_STATE["api_calls"] = 0
        _ADMIN_STATE["like_calls"] = 0
        _ADMIN_STATE["likes_given"] = 0
        _ADMIN_STATE["endpoint_calls"] = {}
        _save_admin_state()
    return jsonify({"status": "success", "message": f"Runtime data cleared ({removed} entries). Original project/account files were kept."})

@app.route("/admin-shappno/logout", methods=["POST"])
def admin_logout():
    if not _require_admin(): return jsonify({"message": "Unauthorized"}), 401
    from flask import session
    session.pop("shappno_admin", None)
    return jsonify({"status": "success"})



async def startup():
    asyncio.create_task(refresh_tokens_periodically())





# ==================== NEW OUTFIT + BANNER SYSTEM ====================
banner_bp = Blueprint('banner_api', __name__)


def _require_pillow():
    if Image is None or ImageDraw is None or ImageFont is None:
        raise RuntimeError("Pillow is required for Outfit and Banner image endpoints.")
ASSET_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "SHAPPNO")

CANVAS_W = 1866
CANVAS_H = 400
AVATAR_W = 400
TEXT_X = 485

@lru_cache(maxsize=1)
def _discover_font_paths():
    bundled = os.path.join(ASSET_DIR, "NotoSans-Combined.ttf")
    paths = [bundled] if os.path.isfile(bundled) else []
    for path in (
        "/system/fonts/NotoSans-Regular.ttf",
        "/system/fonts/NotoSansSymbols-Regular-Subsetted.ttf",
        "/system/fonts/NotoSansSymbols2-Regular.ttf",
        "/system/fonts/NotoSansCJK-Regular.ttc",
        "/data/data/com.termux/files/usr/share/fonts/TTF/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ):
        if os.path.isfile(path) and path not in paths:
            paths.append(path)
    return tuple(paths)

@lru_cache(maxsize=512)
def _load_font_from_path(path, size):
    return ImageFont.truetype(path, size=size)

@lru_cache(maxsize=4096)
def _font_file_has_char(path, ch):
    if not path or len(ch) != 1:
        return True
    cp = ord(ch)
                                                                        
    if unicodedata.combining(ch):
        return True
    try:
        from fontTools.ttLib import TTFont
        font = TTFont(path, fontNumber=0, lazy=True)
        for table in font["cmap"].tables:
            if cp in table.cmap:
                try:
                    font.close()
                except Exception:
                    pass
                return True
        try:
            font.close()
        except Exception:
            pass
    except Exception:
                                                                                
                                                                            
        try:
            probe = ImageFont.truetype(path, size=32)
            actual = probe.getmask(ch)
            missing = probe.getmask(chr(0x10FFFF))
            return actual.size != missing.size or bytes(actual) != bytes(missing)
        except Exception:
            return False
    return False

def _font_candidates(size):
    if ImageFont is None:
        return []
    fonts = []
    for path in _discover_font_paths():
        try:
            fonts.append(_load_font_from_path(path, size))
        except Exception:
            pass
    if not fonts:
        fonts.append(ImageFont.load_default())
    return fonts

def _banner_load_font(size):
    fonts = _font_candidates(size)
    return fonts[0] if fonts else None

def _clean(value, default=""):
    if value is None:
        return default
    value = str(value)
    value = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f\u200b\ufeff]", "", value)
    value = value.strip()
    return value if value else default

def _to_int(value, default=None):
    try:
        if value in (None, ""):
            return default
        return int(value)
    except Exception:
        return default

def _first(*vals):
    for v in vals:
        if v not in (None, "", {}, [], 0, "0"):
            return v
    return None

def _dig(obj, *path):
    cur = obj
    for key in path:
        if not isinstance(cur, dict):
            return None
        cur = cur.get(key)
    return cur

def _normalize_png_id(icon_id):
    if icon_id in (None, "", 0, "0", "none", "null"):
        return None
    icon_id = str(icon_id).strip()
    icon_id = icon_id.split("?")[0].split("#")[0].strip("/")
    if icon_id.lower().endswith(".png"):
        icon_id = icon_id[:-4]
    return icon_id or None

def _icon_url(icon_id):
    icon_id = _normalize_png_id(icon_id)
    if not icon_id:
        return None
    api = PNG_API
    if "{id}" in api:
        return api.format(id=icon_id)
    if "(id)" in api:
        return api.replace("(id)", icon_id)
    sep = "&" if "?" in api else "?"
    return f"{api}{sep}pngid={icon_id}"

def _fetch_image(icon_id, kind="icon"):
    icon_id = _normalize_png_id(icon_id)
    if not icon_id:
        return None

    urls = []
    base_url = _icon_url(icon_id)
    if base_url:
        urls.append(base_url)
        if not base_url.lower().endswith(".png") and "pngid=" in base_url:
            urls.append(base_url.replace(f"pngid={icon_id}", f"pngid={icon_id}.png"))

    headers = {
        "User-Agent": "Mozilla/5.0 BannerRenderer/1.0",
        "Accept": "image/png,image/*;q=0.9,*/*;q=0.1",
        "Cache-Control": "no-cache",
    }

    for url in urls:
        try:
            r = requests.get(url, timeout=15, headers=headers)
            ctype = (r.headers.get("content-type") or "").lower()
            if r.status_code != 200 or not r.content:
                continue
                                                                                                       
            if ("image" not in ctype) and not r.content[:8].startswith(b"\x89PNG"):
                continue
            img = Image.open(io.BytesIO(r.content))
            img.load()
            return img.convert("RGBA")
        except Exception as e:
            try:
                current_app.logger.warning("PNG fetch failed kind=%s id=%s url=%s error=%s", kind, icon_id, url, e)
            except Exception:
                pass
    return None


def _visible_bbox(img):
    try:
        return img.split()[-1].getbbox()
    except Exception:
        return None

def _detect_inner_white_border_crop(img):
    if img is None:
        return None
    img = img.convert("RGBA")
    bbox = _visible_bbox(img)
    if bbox:
        img = img.crop(bbox)
    w, h = img.size
    pix = img.load()
    xs, ys = [], []
    for y in range(h):
        for x in range(w):
            r, g, b, a = pix[x, y]
            if a > 80 and r > 205 and g > 205 and b > 205 and max(r, g, b) - min(r, g, b) < 50:
                xs.append(x); ys.append(y)
    if len(xs) > max(80, (w*h)//300):
        left, right = min(xs), max(xs)
        top, bottom = min(ys), max(ys)
        pad = max(2, int(min(w,h)*0.012))
        left, top = max(0, left-pad), max(0, top-pad)
        right, bottom = min(w, right+pad), min(h, bottom+pad)
        cw, ch = right-left, bottom-top
        if cw > w*0.42 and ch > h*0.42:
            return img.crop((left, top, right, bottom))
    side = min(w,h)
    left, top = max(0,(w-side)//2), max(0,(h-side)//2)
    return img.crop((left, top, left+side, top+side))

def _fit_headpic_icon(img, size=(400,400)):
    bg = Image.new("RGBA", size, (20,20,20,255))
    if img is None:
        return bg
    img = _detect_inner_white_border_crop(img)
    if img is None:
        return bg
    w, h = img.size
    scale = min(size[0]/max(1,w), size[1]/max(1,h))
    nw, nh = max(1,int(w*scale)), max(1,int(h*scale))
    img = img.resize((nw,nh), Image.LANCZOS)
    bg.alpha_composite(img, ((size[0]-nw)//2, (size[1]-nh)//2))
    return bg



def _font_has_char(font, ch):
    try:
        path = getattr(font, "path", None)
        if path and not _font_file_has_char(path, ch):
            return False
        mask = font.getmask(ch)
        return bool(mask and mask.getbbox()) or unicodedata.combining(ch)
    except Exception:
        return False

def _choose_font_for_char(ch, fonts, default_font):
                                                             
    if ch.isspace() or unicodedata.combining(ch):
        return default_font
    for f in fonts:
        if _font_has_char(f, ch):
            return f
    return default_font

def _iter_text_units(text):
    buf = ""
    for ch in str(text):
        if not buf:
            buf = ch
        elif unicodedata.combining(ch) or ch in "\ufe0f\ufe0e":
            buf += ch
        else:
            yield buf
            buf = ch
    if buf:
        yield buf

def _font_for_single_char(ch, fonts, default_font):
    if ch.isspace():
        return default_font
    for candidate in fonts:
        if _font_has_char(candidate, ch):
            return candidate
    return default_font


def _draw_text(draw, xy, text, font, stroke_width=4):
    if not text or font is None:
        return
    text = str(text)
    fonts = _font_candidates(getattr(font, "size", 60)) or [font]
    x, y = xy
    for unit in _iter_text_units(text):
        base = unit[0]
        chosen = _font_for_single_char(base, fonts, font)
        draw.text((int(x), y), base, font=chosen, fill="white",
                  stroke_width=stroke_width, stroke_fill="black")
        try:
            base_width = draw.textlength(base, font=chosen)
        except Exception:
            box = draw.textbbox((0, 0), base, font=chosen)
            base_width = max(0, box[2] - box[0])

                                                                            
                                                                                
                                                         
        for mark in unit[1:]:
            mark_font = None
            for candidate in fonts:
                path = getattr(candidate, "path", None)
                if path and _font_file_has_char(path, mark):
                    mark_font = candidate
                    break
            if mark_font is None:
                continue
            try:
                mb = draw.textbbox((0, 0), mark, font=mark_font, stroke_width=stroke_width)
                mw = max(1, mb[2] - mb[0])
                mh = max(1, mb[3] - mb[1])
                mark_x = x + (base_width - mw) / 2
                mark_y = y - max(1, mh // 3)
                draw.text((int(mark_x), int(mark_y)), mark, font=mark_font,
                          fill="white", stroke_width=stroke_width, stroke_fill="black")
            except Exception:
                pass
        x += base_width


def _text_width(draw, text, font, stroke_width=4):
    if not text or font is None:
        return 0
    fonts = _font_candidates(getattr(font, "size", 60)) or [font]
    total = 0
    for unit in _iter_text_units(str(text)):
        chosen = _font_for_single_char(unit[0], fonts, font)
        try:
            total += draw.textlength(unit[0], font=chosen)
        except Exception:
            box = draw.textbbox((0, 0), unit[0], font=chosen, stroke_width=stroke_width)
            total += max(0, box[2] - box[0])
    return total


def _fit_font(draw, text, max_width, start, minimum):
    text = _clean(text)
    for size in range(start, minimum - 1, -3):
        font = _banner_load_font(size)
        try:
            if _text_width(draw, text, font, stroke_width=4) <= max_width:
                return font
        except Exception:
            return font
    return _banner_load_font(minimum)

def _fit_full_icon(img, size=(400, 400), pad=0):
    bg = Image.new("RGBA", size, (20, 20, 20, 255))
    if img is None:
        return bg
    img = img.convert("RGBA")
    try:
        alpha = img.split()[-1]
        bbox = alpha.getbbox()
        if bbox:
            img = img.crop(bbox)
    except Exception:
        pass
    max_w, max_h = size[0] - pad * 2, size[1] - pad * 2
    w, h = img.size
    scale = min(max_w / max(1, w), max_h / max(1, h))
    nw, nh = max(1, int(w * scale)), max(1, int(h * scale))
    img = img.resize((nw, nh), Image.LANCZOS)
    bg.alpha_composite(img, ((size[0] - nw) // 2, (size[1] - nh) // 2))
    return bg

def _crop_square(img, size=(400, 400)):
    return _fit_full_icon(img, size=size, pad=0)

def _prepare_pin_icon(img, size=(82, 82)):
    if img is None:
        return None
    img = img.convert("RGBA")
    try:
        w, h = img.size
        pix = img.load()
        cut = h
        for y in range(h - 1, max(0, h - int(h * 0.55)), -1):
            samples = pink = darkbase = 0
            for x in range(0, w, max(1, w // 90)):
                r, g, b, a = pix[x, y]
                if a > 30:
                    samples += 1
                    if r > 105 and b > 105 and g < 110:
                        pink += 1
                    if b > r + 20 and b > g + 20 and r > 35:
                        darkbase += 1
            if samples and ((pink / samples > 0.28) or (darkbase / samples > 0.36)):
                cut = y
            elif cut != h:
                break
        if cut < h:
            img = img.crop((0, 0, w, max(1, cut)))
    except Exception:
        pass
    return _fit_full_icon(img, size=size, pad=1)

def _crop_banner(img, size=(1466, 400)):
    if img is None:
        return Image.new("RGBA", size, (40, 40, 40, 255))
    w, h = img.size
    tw, th = size
    scale = max(tw / max(1, w), th / max(1, h))
    nw, nh = int(w * scale), int(h * scale)
    img = img.resize((nw, nh), Image.LANCZOS)
    left = max(0, (nw - tw) // 2)
    top = max(0, (nh - th) // 2)
    return img.crop((left, top, left + tw, top + th))

def _decode_jwt_uid(jwt_token):
    try:
        parts = jwt_token.split(".")
        if len(parts) < 2:
            return None
        payload = parts[1] + "=" * (-len(parts[1]) % 4)
        data = json.loads(base64.urlsafe_b64decode(payload.encode()).decode())
        return str(data.get("account_id") or data.get("external_uid") or data.get("uid") or "")
    except Exception:
        return None

def resolve_uid_from_request():
    uid = request.args.get("uid") or request.args.get("account_id") or request.args.get("accountId")
    if uid:
        return str(uid).strip()

    jwt_token = request.args.get("jwt") or request.args.get("token")
    if jwt_token:
        uid = _decode_jwt_uid(jwt_token)
        if uid:
            return uid

    return None



def _normalize_info_response(raw):
    data = raw if isinstance(raw, dict) else {}
    basic = data.get("basicInfo") or data.get("basic_info") or data.get("basicinfo") or {}
    clan = data.get("clanBasicInfo") or data.get("clan_basic_info") or data.get("clanbasicinfo") or {}
    captain = data.get("captainBasicInfo") or data.get("captain_basic_info") or {}

    bannerid = _first(
        basic.get("bannerId"), basic.get("banner_id"), basic.get("bannerid"),
        captain.get("bannerId") if not basic else None
    )
    headpicid = _first(
        basic.get("headPic"), basic.get("head_pic"), basic.get("headpic"),
        basic.get("avatarId"), basic.get("avatar_id")
    )
    pinid = _first(basic.get("pinId"), basic.get("pin_id"), basic.get("pinid"))
    level = _first(basic.get("level"), data.get("level"))
    name = _first(basic.get("nickname"), basic.get("playerName"), basic.get("name"), data.get("nickname"))
    guild = _first(
        clan.get("clanName"), clan.get("clan_name"), clan.get("guildName"),
        clan.get("name"), basic.get("clanName"), data.get("clanName"), ""
    )
    player_uid = _first(
        basic.get("accountId"), basic.get("account_id"), basic.get("uid"),
        data.get("accountId"), data.get("account_id"), data.get("uid"), request.args.get("uid")
    )

    return {
        "data": data,
        "basic": basic,
        "clan": clan,
        "profile": {
            "uid": str(player_uid or ""),
            "server": str(_first(basic.get("region"), request.args.get("server"), request.args.get("region"), "BD")).upper(),
            "bannerid": bannerid,
            "headpicid": headpicid,
            "pinid": pinid,
            "level": level,
            "playernickname": _clean(name, "Unknown"),
            "guildname": _clean(guild, ""),
            }
    }

def fetch_profile_by_uid(uid):
    """Use this Flask app's own Info pipeline; avoid slow self-HTTP requests."""
    region_hint = request.args.get("server") or request.args.get("region")
    try:
        region, data = asyncio.run(_try_regions(str(uid), region_hint))
    except Exception as exc:
        raise RuntimeError(f"Player info request failed: {exc}")
    if not isinstance(data, dict) or not data:
        raise RuntimeError("Player info returned no player data")
    data = add_equipped_items(data)
    extracted = _normalize_info_response(data)
    extracted["data"] = data
    extracted["profile"]["uid"] = str(uid)
    extracted["profile"]["server"] = str(
        (data.get("basicInfo") or {}).get("region") or region or "BD"
    ).upper()
    return extracted


def render_profile_banner(profile):
    headpicid = profile.get("headpicid")
    bannerid = profile.get("bannerid")
    pinid = profile.get("pinid")
    level = _clean(profile.get("level"), "0")
    uid = _clean(profile.get("uid") or profile.get("accountId") or profile.get("account_id"), "Unknown")
    guildname = _clean(profile.get("guildname"), "No Guild")

    _require_pillow()
    avatar = _fit_headpic_icon(_fetch_image(headpicid, "headpic"), (400, 400))
    banner = _crop_banner(_fetch_image(bannerid, "banner"), (1466, 400))


    canvas = Image.new("RGBA", (1866, 400), (0,0,0,255))
    canvas.alpha_composite(avatar, (0, 0))
    canvas.alpha_composite(banner, (400, 0))

    shade = Image.new("RGBA", (1466, 400), (0, 0, 0, 75))
    canvas.alpha_composite(shade, (400, 0))
    draw = ImageDraw.Draw(canvas)

    pin = _prepare_pin_icon(_fetch_image(pinid, "pin"), (82, 82))
    if pin:
        canvas.alpha_composite(pin, (-10, 322))


                                                               
                                                                        
    player_name = _clean(profile.get("playernickname"), "Unknown")
    guild_text = _clean(profile.get("guildname"), "")
    name_font = _fit_font(draw, player_name, 1280, 112, 46)
    guild_font = _fit_font(draw, guild_text, 1280, 100, 42)
    level_text = f"lvl:{level}"
    level_font = _fit_font(draw, level_text, 320, 48, 28)

    _draw_text(draw, (485, 62), player_name, name_font, stroke_width=4)
    if guild_text and guild_text != "No Guild":
        _draw_text(draw, (485, 205), guild_text, guild_font, stroke_width=4)

    try:
        bbox = draw.textbbox((0, 0), level_text, font=level_font, stroke_width=3)
        tw, th = bbox[2]-bbox[0], bbox[3]-bbox[1]
        level_xy = (1866-tw-28, 400-th-24)
        draw.text(level_xy, level_text, font=level_font, fill="white",
                  stroke_width=2, stroke_fill="white")
        _draw_text(draw, level_xy, level_text, level_font, stroke_width=4)
    except Exception:
        pass

    out = io.BytesIO()
    canvas.save(out, "PNG")
    return out.getvalue()

def _host_url(path, **params):
    base = request.host_url.rstrip("/")
    query = urlencode({k:v for k,v in params.items() if v not in (None, "")})
    return f"{base}{path}" + (f"?{query}" if query else "")

def _profile_with_urls(profile):
    p = {k:v for k,v in profile.items() if v not in (None, "", {}, [])}
    p["icon_urls"] = {}
    for label, key in [("banner", "bannerid"), ("headpic", "headpicid"), ("pin", "pinid")]:
        url = _icon_url(p.get(key))
        if url:
            p["icon_urls"][label] = url
    return p



@banner_bp.route("/banner/all", methods=["GET"])
def banner_all():
    uid = resolve_uid_from_request()
    if not uid:
        return jsonify({"status":"error", "message":"Provide uid: /banner/all?uid=123"}), 400
    try:
        extracted = fetch_profile_by_uid(uid)
        profile = _profile_with_urls(extracted["profile"])
        profile["banner_image"] = _host_url("/onlybanner/all", uid=uid, server=profile.get("server"))
        return jsonify({
            "status": "success",
            "profile": profile,
            "endpoints": {
                "banner_png": profile["banner_image"],
                "outfit_png": _host_url("/outfit/all", uid=uid, server=profile.get("server"))
            }
        })
    except Exception as e:
        return jsonify({"status":"error", "message":str(e)}), 500

@banner_bp.route("/banner", methods=["GET"])
@banner_bp.route("/onlybanner/all", methods=["GET"])
def only_banner_all():
    uid = resolve_uid_from_request()
    if not uid:
        return jsonify({"status":"error", "message":"Provide uid: /banner/all?uid=123"}), 400
    try:
        extracted = fetch_profile_by_uid(uid)
        img = render_profile_banner(extracted["profile"])
        return Response(img, mimetype="image/png")
    except Exception as e:
        return jsonify({"status":"error", "message":str(e)}), 500




                         
                                             
                                                                            
                                                           
OUTFIT_BG_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "SHAPPNO", "outfit.png")
WEAPON_PNG_BASE = "https://cdn.jsdelivr.net/gh/bot1912545-netizen/ultimates_png@main/PNG/{id}.png"

def _fetch_outfit_png(png_id, avatar=False, weapon=False):
    png_id = _normalize_png_id(png_id)
    if not png_id:
        return None
    urls = [_icon_url(png_id)] if avatar else [WEAPON_PNG_BASE.format(id=png_id)]
    for url in urls:
        if not url:
            continue
        try:
            resp = requests.get(url, timeout=12, headers={"User-Agent":"Mozilla/5.0", "Accept":"image/png,image/*"})
            if resp.status_code == 200 and resp.content:
                im = Image.open(io.BytesIO(resp.content)).convert("RGBA")
                im.load()
                return im
        except Exception:
            pass
    return None

def _strip_showcase_color_bar(im):
    if im is None:
        return None
    im = im.convert("RGBA")
    w, h = im.size
    if w < 8 or h < 8:
        return im

    from collections import deque
    px = im.load()

                                                                             
                                                                              
    scan_start = max(0, int(h * 0.78))
    bar_rows = []
    for y in range(scan_start, h):
        colored = 0
        vivid_pink = 0
        opaque = 0
        for x in range(0, w, max(1, w // 120)):
            r, g, b, a = px[x, y]
            if a > 80:
                opaque += 1
                if max(r, g, b) - min(r, g, b) > 45 and max(r, g, b) > 95:
                    colored += 1
                if r > 100 and b > 100 and g < 125 and r > g * 1.25 and b > g * 1.15:
                    vivid_pink += 1
        if opaque and (vivid_pink / opaque >= 0.20 or colored / opaque >= 0.72):
            bar_rows.append(y)

                                                                            
                                                                             
    if bar_rows and bar_rows[-1] >= h - 2:
        run_start = bar_rows[-1]
        for y in range(bar_rows[-1] - 1, scan_start - 1, -1):
            if y in set(bar_rows):
                run_start = y
            else:
                break
        if h - run_start >= max(2, int(h * 0.012)):
            im = im.crop((0, 0, w, max(1, run_start)))
            w, h = im.size
            px = im.load()

                                                                          
                                                                              
                                                                             
    seen = bytearray(w * h)
    queue = deque()

    def is_tile_background(x, y):
        r, g, b, a = px[x, y]
        if a <= 8:
            return True
        dark = max(r, g, b) < 58
        purple = r > 35 and b > 38 and r > g * 1.18 and b > g * 1.12 and g < 105
        magenta = r > 90 and b > 90 and g < 115 and r > g * 1.25 and b > g * 1.15
        return dark or purple or magenta

    for x in range(w):
        queue.append((x, 0))
        queue.append((x, h - 1))
    for y in range(h):
        queue.append((0, y))
        queue.append((w - 1, y))

    while queue:
        x, y = queue.popleft()
        idx = y * w + x
        if seen[idx]:
            continue
        seen[idx] = 1
        if not is_tile_background(x, y):
            continue
        r, g, b, _a = px[x, y]
        px[x, y] = (r, g, b, 0)
        if x > 0 and not seen[idx - 1]: queue.append((x - 1, y))
        if x + 1 < w and not seen[idx + 1]: queue.append((x + 1, y))
        if y > 0 and not seen[idx - w]: queue.append((x, y - 1))
        if y + 1 < h and not seen[idx + w]: queue.append((x, y + 1))

    bbox = im.getchannel("A").getbbox()
    return im.crop(bbox) if bbox else im

def _contain_rgba(im, box_w, box_h, padding=0.08):
    if im is None:
        return None
    im = im.convert("RGBA")
    bbox = im.getchannel("A").getbbox()
    if bbox:
        im = im.crop(bbox)
    if im.width < 1 or im.height < 1:
        return None
    scale = min((box_w*(1-padding))/im.width, (box_h*(1-padding))/im.height)
    size = (max(1, int(im.width*scale)), max(1, int(im.height*scale)))
    return im.resize(size, Image.Resampling.LANCZOS)

def _paste_center(canvas, im, center, box, padding=0.08):
    fitted = _contain_rgba(im, box[0], box[1], padding)
    if fitted is not None:
        canvas.alpha_composite(fitted, (int(center[0]-fitted.width/2), int(center[1]-fitted.height/2)))

def _paste_hex_center(canvas, im, center, box, padding=0.04):
    fitted = _contain_rgba(im, box[0], box[1], padding)
    if fitted is None:
        return
    layer = Image.new("RGBA", box, (0, 0, 0, 0))
    layer.alpha_composite(fitted, ((box[0] - fitted.width) // 2,
                                   (box[1] - fitted.height) // 2))
    mask = Image.new("L", box, 0)
    md = ImageDraw.Draw(mask)
    bw, bh = box
                                                                             
    md.polygon([(bw * 0.25, 0), (bw * 0.75, 0), (bw, bh * 0.5),
                (bw * 0.75, bh), (bw * 0.25, bh), (0, bh * 0.5)], fill=255)
    layer.putalpha(Image.composite(layer.getchannel("A"), Image.new("L", box, 0), mask))
    canvas.alpha_composite(layer, (int(center[0] - bw / 2), int(center[1] - bh / 2)))


def _draw_outfit_hex(canvas, center, png_id, weapon=False, label=""):
    im = _fetch_outfit_png(png_id, weapon=weapon)
    if im is not None:
                                                                              
                                                                          
        im = _strip_showcase_color_bar(im)
        _paste_hex_center(canvas, im, center, (76, 86), padding=0.04)

@banner_bp.route("/outfit", methods=["GET"])
@banner_bp.route("/outfit/all", methods=["GET"])
def outfit_all():
    _require_pillow()
    uid = (request.args.get("uid") or "").strip()
    if not uid or not uid.isdigit() or int(uid) <= 0:
        return jsonify({"status": "error", "message": "Provide a valid numeric uid: /outfit/all?uid=123"}), 400

    try:
        extracted = fetch_profile_by_uid(uid)
        data = extracted.get("data") or {}
        basic = data.get("basicInfo") or data.get("basic_info") or data.get("basicinfo") or {}
        profile = data.get("profileInfo") or data.get("profile_info") or data.get("profileinfo") or {}
        if not os.path.isfile(OUTFIT_BG_PATH):
            return jsonify({"status": "error", "message": "Outfit background asset is missing"}), 500

                                                                             
                                                                               
        bg = Image.open(OUTFIT_BG_PATH).convert("RGBA")
        canvas = bg.copy()
        w, h = canvas.size

                                                                            
                                                                             
                              
        left_nodes = [(252, 105), (150, 229), (150, 393), (252, 532), (355, 608)]
        right_nodes = [(1026, 105), (1128, 229), (1128, 393), (1026, 532)]

                                                                         
        avatar_id = profile.get("avatarId", profile.get("avatar_id"))
        character = _fetch_outfit_png(avatar_id, avatar=True)
        if character is not None:
            _paste_center(canvas, character, (w // 2, int(h * 0.51)),
                          (470, int(h * 0.88)), padding=0.015)

                                                               
                                                    
                                                                      
        def _item_id(value):
            if isinstance(value, dict):
                for key in ("id", "itemId", "item_id", "clothesId", "clothes_id",
                            "skinId", "skin_id", "weaponSkinId", "weapon_skin_id",
                            "weaponSkinID", "petId", "pet_id", "bundleId", "bundle_id"):
                    candidate = value.get(key)
                    normalized = _normalize_png_id(candidate)
                    if normalized:
                        return normalized
                return None
            if isinstance(value, (list, tuple)):
                for candidate in value:
                    found = _item_id(candidate)
                    if found:
                        return found
                return None
            return _normalize_png_id(value)

        clothes_raw = profile.get("clothes") or []
                                                                           
                                                                      
        clothing_keys = ("head", "mask", "top", "bottom", "shoes")
        clothing_slots = [None] * 5
        if isinstance(clothes_raw, dict):
            clothes_dict = clothes_raw
            for slot_index, slot_name in enumerate(clothing_keys):
                value = clothes_dict.get(slot_name)
                if value is None:
                    value = clothes_dict.get(slot_name + "Id") or clothes_dict.get(slot_name + "_id")
                clothing_slots[slot_index] = _item_id(value)
            clothes_raw = [clothes_dict.get(name) for name in clothing_keys]
        elif isinstance(clothes_raw, (list, tuple)):
                                                                      
                                                                          
            for slot_index in range(min(5, len(clothes_raw))):
                clothing_slots[slot_index] = _item_id(clothes_raw[slot_index])
        else:
            clothes_raw = []

        clothes = [value for value in clothing_slots if value]
        for slot_index, png_id in enumerate(clothing_slots):
            if png_id:
                _draw_outfit_hex(canvas, left_nodes[slot_index], png_id, weapon=False)

                                                                       
                                             
        facepaint_id = None
        for key in ("facePaint", "facepaint", "facePaintId", "facepaintId",
                    "face_paint", "face_paint_id", "tattooId", "tattoo_id"):
            facepaint_id = _item_id(profile.get(key)) or _item_id(basic.get(key)) or _item_id(data.get(key))
            if facepaint_id:
                break
        if not facepaint_id and len(clothes_raw) > 5:
            facepaint_id = _item_id(clothes_raw[5])
        if facepaint_id and facepaint_id not in clothes[:5]:
            _draw_outfit_hex(canvas, right_nodes[0], facepaint_id, weapon=False)

                                                                             
        bundle_id = None
        for source in (profile, basic, data):
            for key in ("bundleId", "bundle_id", "bundleID", "bundle", "outfitId", "outfit_id"):
                bundle_id = _item_id(source.get(key))
                if bundle_id:
                    break
            if bundle_id:
                break
        if bundle_id and bundle_id not in clothes[:5] and bundle_id != facepaint_id:
            _draw_outfit_hex(canvas, right_nodes[1], bundle_id, weapon=False)

                                                                    
        pet_id = None
        pet_obj = (data.get("petInfo") or data.get("pet_info") or
                   data.get("petinfo") or profile.get("petInfo") or profile.get("pet_info") or {})
        pet_id = _item_id(pet_obj)
        if not pet_id:
            for source in (profile, basic, data):
                for key in ("petId", "pet_id", "selectedPetId", "selected_pet_id"):
                    pet_id = _item_id(source.get(key))
                    if pet_id:
                        break
                if pet_id:
                    break
        if pet_id and pet_id not in clothes[:5] and pet_id not in (facepaint_id, bundle_id):
            _draw_outfit_hex(canvas, right_nodes[2], pet_id, weapon=False)

                                                                        
                                                                             
                                                                                
        weapon_shows = None
        for source in (basic, profile, data):
            for key in ("weaponSkinShows", "weapon_skin_shows", "weaponSkinShow",
                        "weapon_skin_show", "weaponShows", "weapon_shows"):
                candidate = source.get(key)
                if candidate:
                    weapon_shows = candidate
                    break
            if weapon_shows:
                break

        gun_skin_id = _item_id(weapon_shows)
        if gun_skin_id and gun_skin_id not in clothes[:5] and gun_skin_id not in (facepaint_id, bundle_id, pet_id):
            _draw_outfit_hex(canvas, right_nodes[3], gun_skin_id, weapon=True)

        out = io.BytesIO()
        canvas.save(out, format="PNG", optimize=True)
        out.seek(0)
        return Response(out.getvalue(), mimetype="image/png")
    except Exception as e:
        current_app.logger.exception("Outfit renderer failed for uid=%s", uid)
        return jsonify({"status": "error", "message": str(e)}), 500



app.register_blueprint(banner_bp)

if __name__ == '__main__':
    try:
        asyncio.run(startup())
    except Exception:
        pass
    app.run(host='0.0.0.0', port=int(os.environ.get('PORT', 50385)), debug=False, threaded=True)
