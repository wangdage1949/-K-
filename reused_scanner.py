#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import hashlib
import json
import os
import random
import re
import sqlite3
import sys
import time
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Any

import requests

# =========================
# 配置区域
# =========================

INPUT_FILE = "zuixin.txt"
CHECKPOINT_FILE = "checkpoint.json"
FOUND_FILE = "find.txt"
SEEN_R_DB = "seen_r.sqlite"

HTTP_TIMEOUT = 20  # 秒
JITTER_MIN = 10
JITTER_MAX = 120

# ✅ 防止无限翻页：每个地址总分页（所有接口合计）超过 10 就结束该地址
MAX_PAGES_PER_ADDRESS = 10

# 统计打印
STATS_PRINT_EVERY_SEC = 30

# -------------------------
# TxID 列表接口（多接口）
# -------------------------

# Esplora（用于 txid 列表 & tx 详情）
ESPLORA_BASE_URLS = [
    "https://blockstream.info/api",
    "https://mempool.space/api",
]
# 某些 esplora 的 /address/.../txs/chain 兼容差异更大，保守用 blockstream
ESPLORA_CHAIN_BASE_URLS = [
    "https://blockstream.info/api",
]

# blockchain.info（address tx list: limit/offset）
BLOCKCHAIN_INFO_BASE = "https://blockchain.info"

# BlockCypher（address full: before=block_height keyset）
BLOCKCYPHER_BASE = "https://api.blockcypher.com"

# SoChain（transactions/BTC/{addr}/{page}）
SOCHAIN_BASE = "https://chain.so"

# =========================
# LOGO
# =========================

def print_logo():
    logo = r"""
###############################
#                             #
#     Reused R Scanner        #
#   (Multi-TxID Providers)    #
#   TxID-list First + Resume  #
#                             #
###############################
"""
    print(logo)

# =========================
# 地址抽取
# =========================

RE_BASE58 = re.compile(r'(?<![A-Za-z0-9])([13][a-km-zA-HJ-NP-Z1-9]{25,34})(?![A-Za-z0-9])')
RE_BECH32 = re.compile(r'(?<![A-Za-z0-9])(bc1[ac-hj-np-z02-9]{11,71})(?![A-Za-z0-9])', re.IGNORECASE)

def extract_addresses_from_file(path: str) -> List[str]:
    if not os.path.exists(path):
        print(f"[FATAL] input file not found: {path}")
        sys.exit(1)

    found: List[str] = []
    seen = set()
    with open(path, "r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            for m in RE_BASE58.findall(line):
                if m not in seen:
                    seen.add(m)
                    found.append(m)
            for m in RE_BECH32.findall(line):
                m = m.lower()
                if m not in seen:
                    seen.add(m)
                    found.append(m)
    return found

def addresses_hash(addrs: List[str]) -> str:
    h = hashlib.sha256()
    for a in addrs:
        h.update(a.encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()

# =========================
# DER 签名解析：提取 r
# =========================

def _try_parse_der_r(sig: bytes) -> Optional[str]:
    """
    输入可能是：DER_SIG + sighash(1byte) 或纯 DER_SIG
    返回 32-byte r 的 hex（64 chars），失败返回 None
    """
    if not sig or len(sig) < 8:
        return None
    if sig[0] != 0x30:
        return None

    total_len = sig[1]
    der_end = 2 + total_len

    # 尝试按 DER 长度截断
    if der_end <= len(sig) and der_end >= 8:
        der = sig[:der_end]
    else:
        # 兜底：去掉末尾 1 byte 再试（常见 sighash）
        if len(sig) > 1:
            sig2 = sig[:-1]
            if len(sig2) < 8 or sig2[0] != 0x30:
                return None
            total_len2 = sig2[1]
            der_end2 = 2 + total_len2
            if der_end2 <= len(sig2) and der_end2 >= 8:
                der = sig2[:der_end2]
            else:
                return None
        else:
            return None

    # DER: 30 LL 02 LR R... 02 LS S...
    if len(der) < 8 or der[0] != 0x30:
        return None
    idx = 2
    if idx >= len(der) or der[idx] != 0x02:
        return None
    idx += 1
    if idx >= len(der):
        return None
    lr = der[idx]
    idx += 1
    if idx + lr > len(der):
        return None

    r_bytes = der[idx:idx + lr]

    # 去掉 DER INTEGER 的前导 0x00
    while len(r_bytes) > 0 and r_bytes[0] == 0x00:
        r_bytes = r_bytes[1:]
    if len(r_bytes) == 0 or len(r_bytes) > 32:
        return None

    r_32 = r_bytes.rjust(32, b"\x00")
    return r_32.hex()

def _script_extract_pushdata(script_hex: str) -> List[bytes]:
    """
    解析脚本 pushdata，提取所有被 push 的数据块
    """
    out: List[bytes] = []
    if not script_hex:
        return out
    try:
        b = bytes.fromhex(script_hex)
    except ValueError:
        return out

    i = 0
    n = len(b)
    while i < n:
        op = b[i]
        i += 1
        if 1 <= op <= 75:
            ln = op
            if i + ln <= n:
                out.append(b[i:i+ln])
            i += ln
        elif op == 76:  # OP_PUSHDATA1
            if i >= n:
                break
            ln = b[i]
            i += 1
            if i + ln <= n:
                out.append(b[i:i+ln])
            i += ln
        elif op == 77:  # OP_PUSHDATA2
            if i + 1 >= n:
                break
            ln = int.from_bytes(b[i:i+2], "little")
            i += 2
            if i + ln <= n:
                out.append(b[i:i+ln])
            i += ln
        elif op == 78:  # OP_PUSHDATA4
            if i + 3 >= n:
                break
            ln = int.from_bytes(b[i:i+4], "little")
            i += 4
            if i + ln <= n:
                out.append(b[i:i+ln])
            i += ln
        else:
            continue
    return out

def extract_r_from_vin_esplora(vin: Dict[str, Any]) -> List[Tuple[str, str]]:
    """
    Esplora tx JSON:
      vin[].scriptsig (hex string)
      vin[].witness (list of hex strings)
    """
    out: List[Tuple[str, str]] = []

    scriptsig = vin.get("scriptsig", "") or ""
    pushes = _script_extract_pushdata(scriptsig)
    for k, item in enumerate(pushes):
        r = _try_parse_der_r(item)
        if r:
            out.append((r, f"scriptsig_push#{k}"))

    witness = vin.get("witness", []) or []
    for k, w in enumerate(witness):
        if not w:
            continue
        try:
            wb = bytes.fromhex(w)
        except ValueError:
            continue
        r = _try_parse_der_r(wb)
        if r:
            out.append((r, f"witness_item#{k}"))

    return out

# =========================
# checkpoint（自动识别输入变化 + 版本）
# =========================

CKPT_VERSION = 2
CKPT_MODE = "txid_agg_v1"

def load_checkpoint() -> Dict[str, Any]:
    if not os.path.exists(CHECKPOINT_FILE):
        return {}
    try:
        with open(CHECKPOINT_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}

def save_checkpoint(state: Dict[str, Any]):
    tmp = CHECKPOINT_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=2)
    os.replace(tmp, CHECKPOINT_FILE)

# =========================
# SQLite：去重 + 统计
# =========================

def init_db(db_path: str) -> sqlite3.Connection:
    conn = sqlite3.connect(db_path, timeout=30)
    conn.execute("PRAGMA journal_mode=WAL;")
    conn.execute("PRAGMA synchronous=NORMAL;")
    conn.execute("PRAGMA temp_store=MEMORY;")
    conn.execute("PRAGMA busy_timeout=8000;")

    conn.execute("""
        CREATE TABLE IF NOT EXISTS seen_r (
            r TEXT PRIMARY KEY,
            first_json TEXT NOT NULL,
            count INTEGER NOT NULL
        )
    """)
    # ✅ 对 (r, txid, vin) 做去重，避免“同一签名被重复观测”误报
    conn.execute("""
        CREATE TABLE IF NOT EXISTS seen_occ (
            r TEXT NOT NULL,
            txid TEXT NOT NULL,
            vin_index INTEGER NOT NULL,
            occ_json TEXT NOT NULL,
            PRIMARY KEY (r, txid, vin_index)
        )
    """)
    conn.commit()
    return conn

def occ_insert_if_new(conn: sqlite3.Connection, r_hex: str, txid: str, vin_index: int, occ: Dict[str, Any]) -> bool:
    try:
        conn.execute(
            "INSERT INTO seen_occ (r, txid, vin_index, occ_json) VALUES (?, ?, ?, ?)",
            (r_hex, txid, vin_index, json.dumps(occ, ensure_ascii=False))
        )
        return True
    except sqlite3.IntegrityError:
        return False

def seen_r_update_on_new_occ(conn: sqlite3.Connection, r_hex: str, occ: Dict[str, Any]) -> Tuple[bool, Optional[Dict[str, Any]], int]:
    cur = conn.cursor()
    cur.execute("SELECT first_json, count FROM seen_r WHERE r=?", (r_hex,))
    row = cur.fetchone()

    if row is None:
        conn.execute(
            "INSERT INTO seen_r (r, first_json, count) VALUES (?, ?, ?)",
            (r_hex, json.dumps(occ, ensure_ascii=False), 1)
        )
        return (False, None, 1)

    first_json, count = row
    new_count = int(count) + 1

    first_occ = None
    try:
        first_occ = json.loads(first_json)
    except Exception:
        first_occ = None

    if first_occ is None or not isinstance(first_occ, dict):
        conn.execute("UPDATE seen_r SET first_json=?, count=? WHERE r=?",
                     (json.dumps(occ, ensure_ascii=False), new_count, r_hex))
        return (True, occ, new_count)

    conn.execute("UPDATE seen_r SET count=? WHERE r=?", (new_count, r_hex))
    return (True, first_occ, new_count)

def append_find(reused_r: str, first_occ: Dict[str, Any], now_occ: Dict[str, Any], new_count: int):
    line = {
        "r": reused_r,
        "count": new_count,
        "first": first_occ,
        "now": now_occ,
        "ts": int(time.time()),
    }
    with open(FOUND_FILE, "a", encoding="utf-8") as f:
        f.write(json.dumps(line, ensure_ascii=False) + "\n")
        f.flush()
        os.fsync(f.fileno())

# =========================
# HTTP Client（限流抖动 + 轮换）
# =========================

@dataclass
class RotatingHttpClient:
    base_urls: List[str]
    name: str = "client"

    def __post_init__(self):
        self.base_i = 0
        self.sess = requests.Session()
        self.sess.headers.update({
            "User-Agent": f"reused-r-scanner/2.0 ({self.name}; txid-list-first; jitter)"
        })

    @property
    def base(self) -> str:
        return self.base_urls[self.base_i % len(self.base_urls)].rstrip("/")

    def rotate(self):
        if len(self.base_urls) > 1:
            self.base_i = (self.base_i + 1) % len(self.base_urls)

    def _sleep_jitter(self, reason: str, stats: Dict[str, int]):
        stats["backoffs"] += 1
        t = random.randint(JITTER_MIN, JITTER_MAX)
        print(f"[BACKOFF] {reason} -> sleep {t}s (jitter {JITTER_MIN}-{JITTER_MAX})")
        time.sleep(t)

    def get_json(self, url_or_path: str, stats: Dict[str, int]) -> Any:
        """
        支持：
          - 传入完整 URL: https://...
          - 传入 path: /address/... (会拼接 base)
        """
        if url_or_path.startswith("http://") or url_or_path.startswith("https://"):
            url = url_or_path
        else:
            path = url_or_path
            if not path.startswith("/"):
                path = "/" + path
            url = self.base + path

        while True:
            stats["requests"] += 1
            t0 = time.time()
            try:
                print(f"[HTTP] GET {url}")
                resp = self.sess.get(url, timeout=HTTP_TIMEOUT)
                dt = time.time() - t0
                print(f"[HTTP] <- {resp.status_code} in {dt:.2f}s  via={self.name}")

                if resp.status_code == 429:
                    self._sleep_jitter("HTTP 429 Too Many Requests", stats)
                    self.rotate()
                    if not (url_or_path.startswith("http://") or url_or_path.startswith("https://")):
                        url = self.base + (url_or_path if url_or_path.startswith("/") else "/" + url_or_path)
                    continue

                if 500 <= resp.status_code <= 599:
                    self._sleep_jitter(f"HTTP {resp.status_code} ServerError", stats)
                    self.rotate()
                    if not (url_or_path.startswith("http://") or url_or_path.startswith("https://")):
                        url = self.base + (url_or_path if url_or_path.startswith("/") else "/" + url_or_path)
                    continue

                if resp.status_code != 200:
                    # 非 200：认为该接口当前不可用，抖动后返回 None 让上层切换接口
                    self._sleep_jitter(f"HTTP {resp.status_code} {resp.text[:120]!r}", stats)
                    return None

                return resp.json()

            except requests.exceptions.Timeout:
                self._sleep_jitter("Timeout", stats)
                self.rotate()
                if not (url_or_path.startswith("http://") or url_or_path.startswith("https://")):
                    url = self.base + (url_or_path if url_or_path.startswith("/") else "/" + url_or_path)
            except requests.exceptions.RequestException as e:
                self._sleep_jitter(f"RequestException: {e}", stats)
                self.rotate()
                if not (url_or_path.startswith("http://") or url_or_path.startswith("https://")):
                    url = self.base + (url_or_path if url_or_path.startswith("/") else "/" + url_or_path)

# =========================
# TxID 列表 Source（每个接口不同分页）
# =========================

class TxidSourceBase:
    name: str = "base"
    def fetch_page(self, address: str, state: Dict[str, Any], stats: Dict[str, int]) -> Tuple[List[str], Dict[str, Any], bool, Optional[str]]:
        """
        返回：(txids, new_state, done, page_fingerprint)
        - done=True：该 source 认为已拉完
        - page_fingerprint：用于检测“重复页不前进”
        """
        raise NotImplementedError

class EsploraTxidSource(TxidSourceBase):
    """
    分页规则：txid cursor
      1) /address/{addr}/txs
      2) /address/{addr}/txs/chain/{last_txid}
    """
    name = "esplora"

    def __init__(self, client_main: RotatingHttpClient, client_chain: RotatingHttpClient):
        self.client_main = client_main
        self.client_chain = client_chain

    def fetch_page(self, address: str, state: Dict[str, Any], stats: Dict[str, int]):
        phase = state.get("phase", "first")   # first/chain
        cursor = state.get("cursor_txid", None)

        if phase == "first":
            data = self.client_main.get_json(f"/address/{address}/txs", stats)
        else:
            if not cursor:
                return [], state, True, None
            data = self.client_chain.get_json(f"/address/{address}/txs/chain/{cursor}", stats)

        if not isinstance(data, list):
            return [], state, False, None

        txids = []
        for tx in data:
            txid = tx.get("txid") or tx.get("hash")
            if txid:
                txids.append(txid)

        if len(txids) == 0:
            return [], state, True, None

        first_txid = txids[0]
        last_txid = txids[-1]
        fp = f"{self.name}:{phase}:{first_txid}:{last_txid}:{len(txids)}"

        new_state = dict(state)
        if phase == "first":
            new_state["phase"] = "chain"
        new_state["cursor_txid"] = last_txid

        # cursor 不动 -> 结束
        if phase == "chain" and cursor == last_txid:
            return txids, new_state, True, fp

        return txids, new_state, False, fp

class BlockchainInfoTxidSource(TxidSourceBase):
    """
    分页规则：offset/limit
      https://blockchain.info/rawaddr/{addr}?format=json&limit=50&offset=...
    注意：该接口对 bc1 兼容性可能差；失败会返回 None，上层会切换接口
    """
    name = "blockchain_info"

    def __init__(self, client: RotatingHttpClient, limit: int = 50):
        self.client = client
        self.limit = max(1, min(50, int(limit)))

    def fetch_page(self, address: str, state: Dict[str, Any], stats: Dict[str, int]):
        offset = int(state.get("offset", 0))
        url = f"{BLOCKCHAIN_INFO_BASE}/rawaddr/{address}?format=json&limit={self.limit}&offset={offset}"

        data = self.client.get_json(url, stats)
        if not isinstance(data, dict):
            return [], state, True, None

        txs = data.get("txs", []) or []
        n_tx = data.get("n_tx", None)

        txids = []
        for tx in txs:
            h = tx.get("hash")
            if h:
                txids.append(h)

        if len(txids) == 0:
            return [], state, True, None

        fp = f"{self.name}:off={offset}:first={txids[0]}:last={txids[-1]}:{len(txids)}"

        new_state = dict(state)
        new_state["offset"] = offset + len(txs)

        done = False
        if isinstance(n_tx, int) and new_state["offset"] >= n_tx:
            done = True

        return txids, new_state, done, fp

class BlockCypherTxidSource(TxidSourceBase):
    """
    分页规则：before=block_height（keyset）
      /v1/btc/main/addrs/{addr}/full?limit=50&before=HEIGHT
    """
    name = "blockcypher"

    def __init__(self, client: RotatingHttpClient, limit: int = 50):
        self.client = client
        self.limit = max(1, min(50, int(limit)))

    def fetch_page(self, address: str, state: Dict[str, Any], stats: Dict[str, int]):
        before = state.get("before_height", None)
        if before is None:
            url = f"{BLOCKCYPHER_BASE}/v1/btc/main/addrs/{address}/full?limit={self.limit}"
        else:
            url = f"{BLOCKCYPHER_BASE}/v1/btc/main/addrs/{address}/full?limit={self.limit}&before={int(before)}"

        data = self.client.get_json(url, stats)
        if not isinstance(data, dict):
            return [], state, True, None

        txs = data.get("txs", []) or []
        has_more = bool(data.get("hasMore", False))

        txids = []
        heights = []
        for tx in txs:
            h = tx.get("hash")
            if h:
                txids.append(h)
            bh = tx.get("block_height", None)
            if isinstance(bh, int) and bh > 0:
                heights.append(bh)

        if len(txids) == 0:
            return [], state, True, None

        # 指纹
        min_h = min(heights) if heights else None
        fp = f"{self.name}:before={before}:minh={min_h}:first={txids[0]}:last={txids[-1]}:{len(txids)}"

        new_state = dict(state)
        done = False

        # 用最小高度继续往更早翻页；如果拿不到高度，就没法安全翻页 -> 结束
        if min_h is None:
            done = True
        else:
            # “below before height” -> 直接 before=min_h 即可（重复块用 txid 去重兜底）
            new_state["before_height"] = int(min_h)
            if not has_more:
                done = True

        return txids, new_state, done, fp

class SoChainTxidSource(TxidSourceBase):
    """
    分页规则：page=1,2,3...
      /api/v3/transactions/BTC/{address}/{page}  (最多 10 条/页)
    """
    name = "sochain"

    def __init__(self, client: RotatingHttpClient):
        self.client = client

    def fetch_page(self, address: str, state: Dict[str, Any], stats: Dict[str, int]):
        page = int(state.get("page", 1))
        url = f"{SOCHAIN_BASE}/api/v3/transactions/BTC/{address}/{page}"
        data = self.client.get_json(url, stats)
        if not isinstance(data, dict):
            return [], state, True, None

        if data.get("status") != "success":
            return [], state, True, None

        txs = ((data.get("data") or {}).get("transactions")) or []
        txids = []
        for tx in txs:
            h = tx.get("hash")
            if h:
                txids.append(h)

        if len(txids) == 0:
            return [], state, True, None

        fp = f"{self.name}:page={page}:first={txids[0]}:last={txids[-1]}:{len(txids)}"

        new_state = dict(state)
        new_state["page"] = page + 1

        done = False
        # 该接口没直接 hasMore；当返回 <10 一般可视为结束
        if len(txids) < 10:
            done = True

        return txids, new_state, done, fp

# =========================
# Tx 详情（Esplora /tx/{txid}）
# =========================

def fetch_tx_esplora(tx_client: RotatingHttpClient, txid: str, stats: Dict[str, int]) -> Optional[Dict[str, Any]]:
    data = tx_client.get_json(f"/tx/{txid}", stats)
    if not isinstance(data, dict):
        return None
    return data

# =========================
# 主程序
# =========================

def main():
    print_logo()

    addrs = extract_addresses_from_file(INPUT_FILE)
    print(f"[INPUT] extracted addresses = {len(addrs)} from {INPUT_FILE}")
    if not addrs:
        print("[DONE] no address found in input file")
        return

    a_hash = addresses_hash(addrs)

    ckpt = load_checkpoint()

    # 输入变化 或 checkpoint 版本/模式不匹配 -> 重置
    if ckpt.get("addresses_hash") != a_hash or ckpt.get("ckpt_version") != CKPT_VERSION or ckpt.get("mode") != CKPT_MODE:
        if ckpt:
            print("[CKPT] input/format changed -> auto reset checkpoint")
        ckpt = {
            "ckpt_version": CKPT_VERSION,
            "mode": CKPT_MODE,
            "addresses_hash": a_hash,
        }

    addr_index = int(ckpt.get("addr_index", 0))
    pages_used = int(ckpt.get("pages_used_in_addr", 0))
    rr_index = int(ckpt.get("round_robin_index", 0))
    last_processed_txid = ckpt.get("last_processed_txid", None)

    # 每个 source 的分页状态
    source_states: Dict[str, Any] = ckpt.get("source_states", {}) or {}
    source_done: Dict[str, bool] = ckpt.get("source_done", {}) or {}
    source_fp: Dict[str, Any] = ckpt.get("source_last_fp", {}) or {}
    source_same_fp_hits: Dict[str, int] = ckpt.get("source_same_fp_hits", {}) or {}

    conn = init_db(SEEN_R_DB)

    # clients
    esplora_main = RotatingHttpClient(ESPLORA_BASE_URLS, name="esplora_main")
    esplora_chain = RotatingHttpClient(ESPLORA_CHAIN_BASE_URLS, name="esplora_chain")
    blockchain_info = RotatingHttpClient([BLOCKCHAIN_INFO_BASE], name="blockchain_info")
    blockcypher = RotatingHttpClient([BLOCKCYPHER_BASE], name="blockcypher")
    sochain = RotatingHttpClient([SOCHAIN_BASE], name="sochain")

    # sources
    sources: List[TxidSourceBase] = [
        EsploraTxidSource(esplora_main, esplora_chain),
        BlockchainInfoTxidSource(blockchain_info),
        BlockCypherTxidSource(blockcypher),
        SoChainTxidSource(sochain),
    ]

    # 用 esplora 拉 tx 详情（兼容 scriptsig/witness 解析）
    tx_detail_client = esplora_main

    stats = {
        "requests": 0,
        "backoffs": 0,
        "pages": 0,      # txid pages
        "tx": 0,
        "vin": 0,
        "sig_r": 0,
        "new_occ": 0,
        "alerts": 0,
        "tx_fetch_fail": 0,
        "tx_sources_used": 0,
    }

    start_ts = time.time()
    last_stats_ts = start_ts

    # addr 级别 txid 去重
    seen_txids_in_addr: set = set(ckpt.get("seen_txids_in_addr", []) or [])

    def save_ckpt():
        ckpt.update({
            "ckpt_version": CKPT_VERSION,
            "mode": CKPT_MODE,
            "addresses_hash": a_hash,
            "addr_index": addr_index,
            "pages_used_in_addr": pages_used,
            "round_robin_index": rr_index,
            "last_processed_txid": last_processed_txid,
            "source_states": source_states,
            "source_done": source_done,
            "source_last_fp": source_fp,
            "source_same_fp_hits": source_same_fp_hits,
            # ✅ 为了断点后不重复处理同一地址里 txid
            "seen_txids_in_addr": list(seen_txids_in_addr)[:20000],  # 防爆：最多存 2w 个
        })
        save_checkpoint(ckpt)

    save_ckpt()

    print(f"[RESUME] addr_index={addr_index} pages_used_in_addr={pages_used} last_processed_txid={last_processed_txid}")
    print(f"[PROVIDER] esplora_main={esplora_main.base} esplora_chain={esplora_chain.base}")

    while addr_index < len(addrs):
        address = addrs[addr_index]
        print("\n" + "=" * 110)
        print(f"[ADDR] ({addr_index+1}/{len(addrs)}) {address}")
        print(f"[STATE] pages_used_in_addr={pages_used}/{MAX_PAGES_PER_ADDRESS} last_processed_txid={last_processed_txid}")
        print("=" * 110)

        # 初始化 source 状态（如果没有）
        for s in sources:
            if s.name not in source_states:
                # 各 source 初始 state
                if s.name == "esplora":
                    source_states[s.name] = {"phase": "first", "cursor_txid": None}
                elif s.name == "blockchain_info":
                    source_states[s.name] = {"offset": 0}
                elif s.name == "blockcypher":
                    source_states[s.name] = {"before_height": None}
                elif s.name == "sochain":
                    source_states[s.name] = {"page": 1}
                else:
                    source_states[s.name] = {}
            if s.name not in source_done:
                source_done[s.name] = False
            if s.name not in source_same_fp_hits:
                source_same_fp_hits[s.name] = 0

        # 拉 txid pages（轮询 sources），总页数超过 10 就结束该地址
        while pages_used < MAX_PAGES_PER_ADDRESS:
            # 选择一个还没 done 的 source
            active_sources = [s for s in sources if not source_done.get(s.name, False)]
            if not active_sources:
                print("[ADDR] all txid sources exhausted -> done.")
                break

            s = active_sources[rr_index % len(active_sources)]
            rr_index += 1

            pages_used += 1
            stats["pages"] += 1
            stats["tx_sources_used"] += 1

            print(f"[TXID_PAGE] #{pages_used}/{MAX_PAGES_PER_ADDRESS} source={s.name}")

            txids, new_state, done, fp = s.fetch_page(address, source_states.get(s.name, {}), stats)
            source_states[s.name] = new_state

            # 重复页检测（每个 source 独立）
            if fp and fp == source_fp.get(s.name):
                source_same_fp_hits[s.name] = int(source_same_fp_hits.get(s.name, 0)) + 1
                print(f"[WARN] source={s.name} same page repeated x{source_same_fp_hits[s.name]} fp={fp}")
                if source_same_fp_hits[s.name] >= 2:
                    print(f"[ABORT] source={s.name} pagination not progressing -> mark done")
                    done = True
            else:
                source_same_fp_hits[s.name] = 0
                if fp:
                    source_fp[s.name] = fp

            if done:
                source_done[s.name] = True

            save_ckpt()

            if not txids:
                print(f"[TXID_PAGE] source={s.name} -> empty")
                continue

            # 过滤本地址内重复 txid
            new_txids = []
            for t in txids:
                if t not in seen_txids_in_addr:
                    seen_txids_in_addr.add(t)
                    new_txids.append(t)

            print(f"[TXID_PAGE] got={len(txids)} new={len(new_txids)} (addr_seen={len(seen_txids_in_addr)})")

            if not new_txids:
                continue

            # 断点续跑：如果 last_processed_txid 存在，则跳过直到碰到它，然后从下一条开始
            skipping = last_processed_txid is not None
            if skipping:
                print(f"[RESUME] will skip txids until passing last_processed_txid={last_processed_txid}")

            for txid in new_txids:
                if skipping:
                    if txid == last_processed_txid:
                        print(f"[RESUME] hit last_processed_txid={txid}, skip it and resume from next txid")
                        skipping = False
                    else:
                        print(f"[RESUME] skip txid={txid}")
                    continue

                # 拉 tx 详情（Esplora）
                tx = fetch_tx_esplora(tx_detail_client, txid, stats)
                if not tx:
                    stats["tx_fetch_fail"] += 1
                    print(f"[TX] {txid} | [FAIL] cannot fetch tx detail (esplora).")
                    # 失败也写断点，避免无限卡同一条
                    last_processed_txid = txid
                    save_ckpt()
                    continue

                stats["tx"] += 1
                vin_list = tx.get("vin", []) or []
                confirmed = (tx.get("status", {}) or {}).get("confirmed", None)

                print("-" * 110)
                print(f"[TX] {txid} | confirmed={confirmed} | vin={len(vin_list)}")

                for vin_i, vin in enumerate(vin_list):
                    stats["vin"] += 1
                    prev = f"{vin.get('txid')}:{vin.get('vout')}"
                    scriptsig_len = len(vin.get("scriptsig", "") or "")
                    witness_items = len(vin.get("witness", []) or [])
                    print(f"  [VIN#{vin_i}] prev={prev} scriptsig_len={scriptsig_len} witness_items={witness_items}")

                    r_list = extract_r_from_vin_esplora(vin)
                    if not r_list:
                        print("    [SIG] no parsable DER signature found in scriptsig/witness")
                        continue

                    for (r_hex, src) in r_list:
                        stats["sig_r"] += 1
                        occ = {
                            "address": address,
                            "txid": txid,
                            "vin_index": vin_i,
                            "source": src,
                        }
                        print(f"    [SIG] r={r_hex} source={src}")

                        is_new = occ_insert_if_new(conn, r_hex, txid, vin_i, occ)
                        if not is_new:
                            print("    [DUP] same (r,txid,vin) observed before -> ignored")
                            continue

                        stats["new_occ"] += 1
                        is_reused, first_occ, new_count = seen_r_update_on_new_occ(conn, r_hex, occ)
                        conn.commit()

                        if is_reused and first_occ:
                            if first_occ.get("txid") == occ.get("txid") and first_occ.get("vin_index") == occ.get("vin_index"):
                                print("    [DUP] same txid+vin (should be impossible after dedupe) -> ignored")
                            else:
                                stats["alerts"] += 1
                                print(f"    [ALERT] REUSED r FOUND! r={r_hex} count={new_count}")
                                print(f"            first={first_occ}")
                                print(f"            now  ={occ}")
                                append_find(r_hex, first_occ, occ, new_count)

                # 每 tx 保存断点
                last_processed_txid = txid
                save_ckpt()

                # 周期打印统计
                now = time.time()
                if now - last_stats_ts >= STATS_PRINT_EVERY_SEC:
                    done_addr = addr_index
                    elapsed = now - start_ts
                    addr_per_sec = (done_addr / elapsed) if elapsed > 0 else 0.0
                    remain = len(addrs) - done_addr
                    eta_sec = (remain / addr_per_sec) if addr_per_sec > 0 else None
                    print("\n" + "#" * 90)
                    print(f"[STATS] done_addr {done_addr:,}/{len(addrs):,} ({done_addr/len(addrs)*100:.3f}%)")
                    print(f"[STATS] pages_used_in_addr={pages_used}/{MAX_PAGES_PER_ADDRESS} pages={stats['pages']} tx={stats['tx']} vin={stats['vin']}")
                    print(f"[STATS] requests={stats['requests']} backoffs={stats['backoffs']} sig_r={stats['sig_r']} new_occ={stats['new_occ']} alerts={stats['alerts']}")
                    print(f"[STATS] tx_fetch_fail={stats['tx_fetch_fail']}")
                    if eta_sec is not None:
                        finish_ts = now + eta_sec
                        print(f"[STATS] ETA {eta_sec/3600:.2f} hours | finish ~ {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(finish_ts))}")
                    else:
                        print("[STATS] ETA unknown (speed too low)")
                    print("#" * 90 + "\n")
                    last_stats_ts = now

            # ✅ 本轮 new_txids 处理完，清掉“页内续跑点”
            last_processed_txid = None
            save_ckpt()

        # 超过分页上限 / sources 枯竭：结束该地址
        if pages_used >= MAX_PAGES_PER_ADDRESS:
            print(f"[LIMIT] pages_used_in_addr reached {MAX_PAGES_PER_ADDRESS}. stop this address.")

        # 推进到下一个地址：重置 addr 内状态
        addr_index += 1
        pages_used = 0
        rr_index = 0
        last_processed_txid = None
        source_states = {}
        source_done = {}
        source_fp = {}
        source_same_fp_hits = {}
        seen_txids_in_addr = set()

        save_ckpt()
        print(f"[NEXT] move to next address, addr_index={addr_index}")

    print("\n[DONE] all addresses finished.")
    conn.close()

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n[!] Ctrl+C received. checkpoint saved. you can resume later.")
        sys.exit(1)
