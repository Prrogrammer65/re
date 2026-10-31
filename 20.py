#!/usr/bin/env python3
"""
Bitcoin puzzle range scanner (low-memory version: works with millions of target addresses)

Files:
  adress.txt : Bitcoin target addresses (one per line, P2PKH addresses starting with 1)
  adress1.txt: Ethereum target addresses (one per line, 0x... hex; optional)
  adress2.txt: Bitcoin Cash targets (legacy 1... or CashAddr q...; optional)
  adress3.txt: Dash targets (X...; optional)
  adress4.txt: Dogecoin targets (D...; optional)
  adress6.txt: Litecoin targets, all 3 address types mixed freely (optional):
               legacy L..., nested-segwit M..., native segwit ltc1...
  adress7.txt: Tron targets (T...; optional)
  range.txt  : ranges, scanned in file order (starts from puzzle 71 by default)
               one entry per line:  71   or   400000:7FFFFF   (hex)
  range1.txt : optional. When range.txt is finished without a full match, the program
               switches to a RANDOM search inside the ranges of this file. It has no
               limit and keeps going until you stop it (Ctrl+C).
               (if several ranges are listed, each one is picked with equal probability)

Usage:
  python puzzle_scanner.py            -> no address output (default, fastest)
  python puzzle_scanner.py first      -> print only the two pages next to the center point
  python puzzle_scanner.py all        -> print every generated address (very slow)

Memory:
  The address files are NOT kept in RAM. On the first start (and whenever an address file
  changes) they are converted into compact files inside target_cache/ (sorted 20-byte hashes
  + a small Bloom filter). The workers memory-map these files, so all processes share the
  same pages and RAM usage stays small even with tens of millions of addresses.
  Invalid or unsupported lines (P2SH, bech32, wrong coin) are counted and skipped.

Note: generated addresses are never written to disk. Only these files are written:
  prefix_matches.txt : (only if PREFIX_MATCH = True) first PREFIX_LEN characters matched
  found.txt          : full address match (private key hex + address)
  online_hits.txt    : online hits: UTXO coins with balance > 0 or any history,
                       ETH with balance > 0, Tron with USDT balance > 0
  state.json         : progress counters only
  target_cache/      : the compact target files described above

How each range is scanned:
  1) Center point = exactly 49.9% of the range:  C = start + size * 499 // 1000
  2) Each page = 128 keys
  3) PAGES_PER_SIDE (default 1,500,000) pages upward from C and the same number
     downward from C, so the 49.9% point sits exactly in the middle of the window
  4) For every key, the Bitcoin addresses (compressed and uncompressed), the Ethereum
     address and (if the files exist) the BCH / Dash / Dogecoin / Litecoin / Tron
     addresses are checked against the target files
  5) Progress is saved every CHUNK_PAGES pages; if the program is interrupted
     it resumes from the last saved point

Matches:
  - Full address match -> private key hex + address saved to found.txt. The search does NOT
    stop by itself (STOP_ON_MATCH = False); it keeps going until you stop it with Ctrl+C.
  - Online check (separate thread): ONE slot per second, in the fixed order of ONLINE_SCHEDULE
    (BTC uncompressed, ETH, BCH, DASH, BTC compressed, DOGE, LTC, BTC bech32/bc1, TRX, BNB,
    MATIC, AVAX, FTM, ARB, OP, repeat). TRX checks both the native TRX balance and USDT
    (TRC20) in one request. The 6 EVM chains (BNB/MATIC/AVAX/FTM/ARB/OP) are balance-check
    only - same address as ETH, no target file, no sweep, each on its own public RPC (see
    EVM_EXTRA_CHAINS).
    BTC checks balance only (not transaction history). BTC has two APIs (API_URL then
    API_URL_BACKUP, both esplora: blockstream.info then mempool.space) and automatically
    switches to the backup if the first one is blocked. Both cover every BTC address type,
    including bech32 (bc1...).
    Each second a fresh random key of the window being scanned is checked for that slot.
    Every checked address is printed with its balance.

Sweep (SWEEP_ENABLED, SWEEP_ADDRESSES - put your OWN addresses there before relying on this):
  As soon as a key with a REAL balance > 0 turns up (full match with funds, or an online check
  that finds one), the scan pauses, SWEEP_RESERVE_PCT (1% by default) of the balance is left
  behind and 99% is swept to SWEEP_ADDRESSES[coin], starting at FEE_PREMIUM (1.30 = 30%) above
  the network's normal fee/gas price, and the program waits for a confirmation before resuming:
    - UTXO coins (BTC/BCH/DASH/DOGE/LTC): if still unconfirmed after SWEEP_BUMP_AFTER seconds,
      the fee is raised (x SWEEP_BUMP_FACTOR) and a replacement (RBF) is rebroadcast.
    - Ethereum: same idea with the gas price, resent at the same nonce.
    - Tron/USDT: no fee-bump mechanism exists on Tron; the program just waits.
  If someone else's transaction wins the race, this is logged and the scan resumes - there is
  nothing left to sweep. IMPORTANT: this moves real funds with real transactions. Test it with
  a tiny, disposable amount before trusting it with a real find, and read the fee/gas settings
  below before using it.

Install:  pip install coincurve pycryptodome
"""

import hashlib
import heapq
import json
import mmap
import multiprocessing as mp
import os
import random
import signal
import sys
import threading
import time
import urllib.error
import urllib.request
from bisect import bisect_right
from itertools import islice, zip_longest

from coincurve import PrivateKey, PublicKey
from Crypto.Hash import RIPEMD160, keccak

# ------------------------- Settings -------------------------
PAGE_SIZE = 128
PAGES_PER_SIDE = 1_500_000          # pages upward from the center and the same number downward
PCT_NUM, PCT_DEN = 499, 1000        # center point: exactly 49.9% of the range
MAX_STEPS_PER_RANGE = 1             # 1 = only this window; 0 = keep widening until the range edges
CONTINUOUS = True                   # automatically move on to the next range
CHUNK_PAGES = 20_000                # save progress after this many pages
PROGRESS_SECONDS = 30               # print a progress line every N seconds
PREFIX_LEN = 8                      # number of leading characters for a partial match
WORKERS = None                      # None = all CPU cores minus one (min 1; 1 = no Pool). Or set a number
STOP_ON_MATCH = False               # False = keep searching after a full match (stop with Ctrl+C)
SWEEP_RESERVE_PCT = 0.01            # fraction of a found balance left behind (0.01 = 1% stays, 99% is swept)
FEE_PREMIUM = 1.30                  # the sweep's STARTING fee/gas price = this x the normal network rate
DUST_LIMIT = 546                    # UTXO coins: a "leave some behind" output below this is invalid/wasteful
PREFIX_MATCH = False                # partial (8-char) BTC matches; needs RAM and gives only noise
PREFIX_MAX_TARGETS = 200_000        # prefix matching is disabled above this many BTC addresses

TARGET_CACHE_DIR = "target_cache"   # compact copies of the address files (built automatically)
BLOOM_BITS_PER_ITEM = 24            # Bloom filter size: 24 bits (3 bytes) per address
SORT_CHUNK = 400_000                # addresses sorted in RAM at once while building the cache

ONLINE_CHECK = True                 # online check
ONLINE_INTERVAL = 1                 # one slot every N seconds (round-robin over ONLINE_SCHEDULE)
BTC_EXTRA_DELAY = 0.5                # extra seconds added on top of ONLINE_INTERVAL before
                                     # EACH of the 3 BTC slots (uncompressed/compressed/bech32),
                                     # so BTC is checked a bit less often than the other coins
# BTC online check order: uncompressed first, compressed 3 coins later, bech32 (bc1) after
# the 6th coin (LTC) - see ONLINE_SCHEDULE. One slot is checked every ONLINE_INTERVAL seconds
# (+ BTC_EXTRA_DELAY for the 3 BTC slots).
ONLINE_SCHEDULE = ["BTC_UNCOMPRESSED", "ETH", "BCH", "DASH",
                   "BTC_COMPRESSED", "DOGE", "LTC",
                   "BTC_BECH32", "TRX", "BNB", "MATIC", "AVAX", "FTM", "ARB", "OP"]
# esplora API (same format for both): covers every BTC address type, legacy/P2SH/bech32 alike.
ESPLORA_BASES = ["https://blockstream.info/api/", "https://mempool.space/api/"]
API_URL = ESPLORA_BASES[0] + "address/"
API_URL_BACKUP = ESPLORA_BASES[1] + "address/"        # used automatically if API_URL is blocked
ONLINE_TIMEOUT = 10

ETH_ENABLED = True                  # also scan Ethereum addresses
ETH_ADDRESS_FILE = "adress1.txt"    # Ethereum target addresses (0x...), optional file
ETH_RPC_URL = "https://ethereum-rpc.publicnode.com"   # public JSON-RPC used for eth_getBalance
CHECK_BTC_UNCOMPRESSED = True       # False = skip the uncompressed hash (BTC, BCH, Dash, DOGE, LTC; faster)

# EVM-compatible chains: ONLINE BALANCE CHECK ONLY, by request - no offline target-address
# matching, no sweep. Every EVM chain uses the exact same address derivation as ETH (same
# secp256k1 pubkey -> keccak -> last 20 bytes), so none of them need a target file or any
# extra per-key work in the offline scan (scan_page already computes that hash for ETH) -
# each just gets its own random-sample slot in the online check, on its OWN public RPC (a
# different provider/node per chain, so none of them share a quota with each other or ETH),
# which costs nothing in scan speed. name -> (public RPC URL, native coin symbol for display).
EVM_EXTRA_ENABLED = True
EVM_EXTRA_CHAINS = {
    "BNB":   ("https://bsc-dataseed.binance.org/",     "BNB"),    # BNB Smart Chain
    "MATIC": ("https://polygon-rpc.com",                "MATIC"), # Polygon
    "AVAX":  ("https://api.avax.network/ext/bc/C/rpc",  "AVAX"),  # Avalanche C-Chain
    "FTM":   ("https://rpc.ftm.tools",                  "FTM"),   # Fantom
    "ARB":   ("https://arb1.arbitrum.io/rpc",           "ETH"),   # Arbitrum One (settles in ETH)
    "OP":    ("https://mainnet.optimism.io",            "ETH"),   # Optimism (settles in ETH)
}

EXTRA_COINS_ENABLED = True          # also scan BCH, Dash, Dogecoin, Litecoin and Tron
# Base58 P2PKH coins: (name, target file, address version byte, P2SH version bytes to skip)
P2PKH_COINS = [
    ("BTC",  "adress.txt",  0x00, {0x05}),
    ("BCH",  "adress2.txt", 0x00, {0x05}),
    ("DASH", "adress3.txt", 0x4C, {0x10}),
    ("DOGE", "adress4.txt", 0x1E, {0x16}),
    ("LTC",  "adress6.txt", 0x30, {0x32, 0x05}),
]
TRX_ADDRESS_FILE = "adress7.txt"

# Litecoin's 3 address types are all read from the SAME file, adress6.txt, mixed freely:
#   legacy      L...   (P2PKH,        matched like any other P2PKH_COINS entry above)
#   nested-segwit M... (P2SH-segwit,  separate hash -> its own "p3" domain below)
#   native segwit ltc1...(bech32,     same hash as the compressed P2PKH pubkey, so it
#                                     is folded into the normal LTC P2PKH matching)
LTC_ADDRESS_FILE = "adress6.txt"
LTC_SEGWIT_HRP = "ltc"

ONLINE_NEW_COINS = True             # online check also for BCH, Dash, DOGE, LTC and Tron (USDT only)
# Blockbook API v2 base URLs (same JSON format as the BTC one). Change a URL if it stops working.
BLOCKBOOK_URLS = {
    "BCH":  "https://bch1.trezor.io/api/v2/address/",
    "DASH": "https://dash1.trezor.io/api/v2/address/",
    "DOGE": "https://doge1.trezor.io/api/v2/address/",
    "LTC":  "https://ltc1.trezor.io/api/v2/address/",
}


def _bc_token_qs(first: bool = True) -> str:
    """'?token=...' / '&token=...' if BLOCKCYPHER_TOKEN is set, else '' (used by the BlockCypher
    SWEEP helpers further down - BlockCypher is no longer used for the online balance check)."""
    if not BLOCKCYPHER_TOKEN:
        return ""
    return ("?" if first else "&") + "token=" + BLOCKCYPHER_TOKEN


# BCH/DASH/DOGE/LTC each used to share ONE provider (first trezor alone, then BlockCypher
# alone) for the online balance check: one provider blocked = all 4 broken at once, and
# BlockCypher's free tier (100 req/hour, SHARED across every coin on it) couldn't keep up with
# even one of them being polled every ~10s, let alone three. Each coin now has its own,
# different provider, so a block on one never affects the others and none of them share a
# quota. Blockbook (trezor) is kept as each coin's own second-choice fallback, same as before.
def _fetch_blockchair_bch(addr: str) -> dict:
    url_addr = addr.split(":", 1)[-1] if ":" in addr else addr   # strip "bitcoincash:" - the
    data = fetch_address(url_addr,                               # API rejects it in the URL
                         "https://api.blockchair.com/bitcoin-cash/dashboards/address/")
    try:
        entry = next(iter((data.get("data") or {}).values()))
        a = entry.get("address") or {}
    except StopIteration:
        a = {}
    return {"balance": a.get("balance", 0), "txs": a.get("transaction_count", 0),
            "totalReceived": a.get("received", 0)}


def _fetch_dash_insight(addr: str) -> dict:
    url = "https://insight.dash.org/insight-api/addr/" + addr + "/balance"
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        sat = int(resp.read().decode("utf-8").strip())        # plain integer, already duffs
    return {"balance": sat, "txs": 0, "totalReceived": 0}


def _fetch_dogechain(addr: str) -> dict:
    url = "https://dogechain.info/api/v1/address/balance/" + addr
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0",
                                               "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    sat = int(round(float(data.get("balance", 0) or 0) * 1e8))   # DOGE (decimal) -> smallest unit
    return {"balance": sat, "txs": 0, "totalReceived": 0}


def _fetch_esplora_ltc(addr: str) -> dict:
    """litecoinspace.org: a community-run esplora instance for Litecoin (same software/API
    shape as blockstream.info/mempool.space, just for LTC) - independent of SoChain, which
    kept having problems. Reuses the same balance math already used for BTC."""
    data = fetch_address(addr, "https://litecoinspace.org/api/address/")
    sat = _esplora_balance_sat(data)
    return {"balance": sat, "txs": 0, "totalReceived": 0}


def _blockbook_fetcher(name: str):
    def f(addr: str) -> dict:
        return fetch_address(addr, BLOCKBOOK_URLS[name])      # already in the shape we need
    return f


OTHER_COIN_FETCHERS = {
    "BCH":  [_fetch_blockchair_bch, _blockbook_fetcher("BCH")],
    "DASH": [_fetch_dash_insight,   _blockbook_fetcher("DASH")],
    "DOGE": [_fetch_dogechain,      _blockbook_fetcher("DOGE")],
    "LTC":  [_fetch_esplora_ltc,    _blockbook_fetcher("LTC")],
}
TRON_API_URL = "https://api.trongrid.io/v1/accounts/"
TRON_USDT_CONTRACT = "TR7NHqjeKQxGTCi8q8ZY4pL8otSzgjLj6t"   # USDT (Tether) on Tron
TRON_API_BASE = "https://api.trongrid.io"
TRON_NATIVE_FEE_BUFFER = 1_100_000  # sun (~1.1 TRX) kept unspent as a bandwidth/fee buffer

# ---- Sweep: stop the scan and move the funds out as soon as a real balance is found ----
SWEEP_ENABLED = True                 # master switch for everything below
SWEEP_ADDRESSES = {                  # <-- PUT YOUR OWN ADDRESSES HERE before relying on this
    "BTC": "", "ETH": "", "BCH": "", "DASH": "", "DOGE": "", "LTC": "",
    "TRX": "",                       # also used for the USDT (TRC20) sweep
}
SWEEP_POLL_SECONDS = 15              # how often to check whether the sweep confirmed
SWEEP_BUMP_AFTER = 45                # seconds unconfirmed before the fee/gas price is raised
SWEEP_BUMP_FACTOR = 1.8              # fee/gas multiplier on every bump
SWEEP_MAX_BUMPS = 12                 # give up bumping after this many tries
SWEEP_CONFIRMATIONS = 1              # confirmations required (UTXO coins) before resuming
UTXO_FEE_RATE = 20                   # starting fee rate (satoshi-like units per vbyte)
ETH_GAS_LIMIT = 21_000
ETH_CHAIN_ID = 1                     # 1 = Ethereum mainnet
TRON_FEE_LIMIT = 30_000_000          # max TRX burned (in sun) for the USDT transfer call
# BTC balance checks use the esplora API (API_URL: blockstream.info); sweeping needs a
# UTXO-capable Blockbook API instead (esplora's broadcast format is different), so BTC keeps
# its own Blockbook base here, separate from API_URL.
UTXO_BROADCAST_URLS = dict(BLOCKBOOK_URLS)
UTXO_BROADCAST_URLS["BTC"] = "https://btc1.trezor.io/api/v2/address/"
SHOW_ONLINE_ERRORS = False          # print network/API errors of the online check
ONLINE_DISABLE_AFTER = 5            # switch an online API off after this many errors in a row
ONLINE_COOLDOWN_SECONDS = 120        # auto re-enable a switched-off coin after this long (BTC
                                     # rotates to its backup API instead; see _service_fail)
# BCH/DASH/DOGE/LTC each now have their own, independent provider (see OTHER_COIN_FETCHERS),
# so they no longer share one quota the way they did when all 3 went through BlockCypher.
# This floor just keeps things polite to those free public services - raise/lower per taste.
EXTRA_COIN_MIN_GAP = 8.0
BLOCKCYPHER_TOKEN = ""              # optional free token from blockcypher.com, used only for
                                     # the sweep (see SWEEP_BLOCKCYPHER_BASES further down)
SHOW_ONLINE_CHECKED = True          # print every online-checked address with its balance (nothing saved if 0)
SHOW_ONLINE_STATS = False           # print the "Online check so far" line after each range

RANGE_FILE = "range.txt"
RANGE_FILE_2 = "range1.txt"         # optional: random, unlimited search after range.txt is finished
STATE_FILE = "state.json"
FOUND_FILE = "found.txt"
PREFIX_FILE = "prefix_matches.txt"
ONLINE_FILE = "online_hits.txt"

SHOW_MODE = sys.argv[1].lower() if len(sys.argv) > 1 else "none"
# ------------------------------------------------------------

STATE_VERSION = 5
B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


# ---------- Address helpers ----------
def b58_to_int(s: str) -> int:
    n = 0
    for ch in s:
        n = n * 58 + B58.index(ch)
    return n


def b58_to_hash160(addr: str) -> bytes:
    raw = b58_to_int(addr).to_bytes(25, "big")
    if hashlib.sha256(hashlib.sha256(raw[:-4]).digest()).digest()[:4] != raw[-4:]:
        raise ValueError(f"Invalid address: {addr}")
    return raw[1:21]


def hash160(data: bytes) -> bytes:
    return RIPEMD160.new(hashlib.sha256(data).digest()).digest()


def h160_to_addr(h: bytes) -> str:
    payload = b"\x00" + h
    raw = payload + hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
    n = int.from_bytes(raw, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = B58[r] + out
    pad = len(raw) - len(raw.lstrip(b"\x00"))
    return "1" * pad + out


def key_addresses(k: int):
    """Compressed and uncompressed address of a private key"""
    pub = PublicKey.from_secret(k.to_bytes(32, "big"))
    return (h160_to_addr(hash160(pub.format(compressed=True))),
            h160_to_addr(hash160(pub.format(compressed=False))))


def eth_hash(pub_uncompressed: bytes) -> bytes:
    """20-byte Ethereum address from a 65-byte uncompressed public key"""
    return keccak.new(digest_bits=256, data=pub_uncompressed[1:]).digest()[-20:]


def key_eth_address(k: int) -> str:
    pub = PublicKey.from_secret(k.to_bytes(32, "big"))
    return "0x" + eth_hash(pub.format(compressed=False)).hex()


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def _b58_to_bytes(s: str) -> bytes:
    n = b58_to_int(s)
    raw = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return b"\x00" * (len(s) - len(s.lstrip("1"))) + raw


def b58_encode_bytes(raw: bytes) -> str:
    n = int.from_bytes(raw, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = B58[r] + out
    return "1" * (len(raw) - len(raw.lstrip(b"\x00"))) + out


def b58check_encode(version: int, payload: bytes) -> str:
    raw = bytes([version]) + payload
    return b58_encode_bytes(raw + sha256d(raw)[:4])


def b58check_decode(addr: str):
    """-> (version byte, payload); raises ValueError on a bad checksum"""
    raw = _b58_to_bytes(addr)
    if len(raw) < 5 or sha256d(raw[:-4])[:4] != raw[-4:]:
        raise ValueError("bad checksum")
    return raw[0], raw[1:-4]


_CASHADDR_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"


def _cashaddr_polymod(values) -> int:
    c = 1
    for d in values:
        c0 = c >> 35
        c = ((c & 0x07FFFFFFFF) << 5) ^ d
        if c0 & 0x01: c ^= 0x98F2BC8E61
        if c0 & 0x02: c ^= 0x79B76D99E2
        if c0 & 0x04: c ^= 0xF33E5FB3C4
        if c0 & 0x08: c ^= 0xAE2EABE2A8
        if c0 & 0x10: c ^= 0x1E4F43E470
    return c ^ 1


def cashaddr_decode(addr: str):
    """Bitcoin Cash CashAddr -> (type, hash); type 0 = P2PKH, 1 = P2SH"""
    addr = addr.lower()
    prefix, sep, payload = addr.partition(":")
    if not sep:
        prefix, payload = "bitcoincash", addr
    data = [_CASHADDR_CHARSET.index(ch) for ch in payload]
    if _cashaddr_polymod([ord(c) & 0x1F for c in prefix] + [0] + data) != 0:
        raise ValueError("bad checksum")
    acc = bits = 0
    out = bytearray()
    for v in data[:-8]:
        acc = (acc << 5) | v
        bits += 5
        while bits >= 8:
            bits -= 8
            out.append((acc >> bits) & 0xFF)
            acc &= (1 << bits) - 1
    if not out or (out[0] & 7) != 0 or len(out) != 21:
        raise ValueError("unsupported CashAddr size")
    return (out[0] >> 3) & 0x0F, bytes(out[1:])


def cashaddr_encode(h: bytes, prefix: str = "bitcoincash") -> str:
    """20-byte hash160 -> Bitcoin Cash CashAddr (P2PKH)"""
    acc = bits = 0
    five = []
    for byte in bytes([0]) + h:
        acc = (acc << 8) | byte
        bits += 8
        while bits >= 5:
            bits -= 5
            five.append((acc >> bits) & 31)
            acc &= (1 << bits) - 1
    if bits:
        five.append((acc << (5 - bits)) & 31)
    chk = _cashaddr_polymod([ord(c) & 0x1F for c in prefix] + [0] + five + [0] * 8)
    five += [(chk >> 5 * (7 - i)) & 31 for i in range(8)]
    return prefix + ":" + "".join(_CASHADDR_CHARSET[v] for v in five)


# ---------- Fast prefix filter ----------
def prefix_intervals(prefix: str):
    """
    Every hash160 whose address starts with `prefix` falls inside a few numeric intervals.
    The real address is only built (and the prefix re-checked) when a hash160 lands
    inside one of these intervals.
    """
    out = []
    for total_len in range(26, 36):
        pad = total_len - len(prefix)
        if pad < 0:
            continue
        lo = b58_to_int(prefix + "1" * pad) >> 32
        hi = b58_to_int(prefix + "z" * pad) >> 32
        if lo >= (1 << 160):
            continue
        out.append((lo, min(hi, (1 << 160) - 1)))
    return out


def merge_intervals(intervals):
    intervals.sort()
    merged = []
    for lo, hi in intervals:
        if merged and lo <= merged[-1][1] + 1:
            merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
        else:
            merged.append((lo, hi))
    return merged


# ---------- Reading input files ----------
def clean_lines(path: str):
    if not os.path.exists(path):
        sys.exit(f"File not found: {path}")
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if line:
                yield line


REC = 20                             # every target is stored as a 20-byte hash
CACHE_VERSION = 1


def iter_addresses(path: str):
    """Stream the first word of every non-empty, non-comment line (never builds a big list)."""
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            words = line.split("#", 1)[0].split()
            if words:
                yield words[0]


def bech32_decode_segwit(hrp_expected: str, addr: str):
    """BIP173 bech32 segwit address -> (witver, witness-program bytes). Raises ValueError."""
    a = addr.strip()
    if a.lower() != a and a.upper() != a:
        raise ValueError("mixed case")
    a = a.lower()
    hrp, sep, data_part = a.rpartition("1")
    if not sep or hrp != hrp_expected or len(data_part) < 6:
        raise ValueError("not a bech32 " + hrp_expected + " address")
    try:
        data = [BECH32_CHARSET.index(c) for c in data_part]
    except ValueError:
        raise ValueError("bad bech32 character")
    if _bech32_polymod([ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp] + data) != 1:
        raise ValueError("bad bech32 checksum")
    witver = data[0]
    prog = _convertbits(data[1:-6], 5, 8, pad=False)
    if not (2 <= len(prog) <= 40) or witver > 16:
        raise ValueError("bad witness program")
    return witver, bytes(prog)


def _ltc_p2pkh_decode(addr: str):
    """LTC legacy (L..., version 0x30) and native segwit (ltc1..., same hash as compressed
    pubkey) targets; P2SH-segwit (M..., version 0x32) is handled by _ltc_p2sh_decode instead."""
    a = addr.strip()
    if a.lower().startswith(LTC_SEGWIT_HRP + "1"):
        witver, prog = bech32_decode_segwit(LTC_SEGWIT_HRP, a)
        if witver != 0 or len(prog) != 20:
            raise ValueError("unsupported LTC segwit address")
        return prog
    ver, h = b58check_decode(a)
    if len(h) != 20:
        raise ValueError("bad length")
    if ver == 0x32:
        return None                      # P2SH-segwit: not this decoder's job
    if ver != 0x30:
        raise ValueError("address of another coin")
    return h


def _ltc_p2sh_decode(addr: str):
    """LTC nested-segwit (P2SH, M..., version 0x32) targets only."""
    a = addr.strip()
    if a.lower().startswith(LTC_SEGWIT_HRP + "1"):
        return None                      # native segwit: not this decoder's job
    ver, h = b58check_decode(a)
    if len(h) != 20:
        raise ValueError("bad length")
    if ver != 0x32:
        return None
    return h


def _p2pkh_decoder(name: str, version: int, p2sh_versions):
    def decode(addr: str):
        if name == "BCH" and addr[:1] not in "13":
            typ, h = cashaddr_decode(addr)
            return h if typ == 0 else None              # None = script address, skipped
        ver, h = b58check_decode(addr)
        if len(h) != 20:
            raise ValueError("bad length")
        if ver in p2sh_versions:
            return None
        if ver != version:
            raise ValueError("address of another coin")
        return h
    return decode


def _eth_decode(addr: str) -> bytes:
    h = addr[2:] if addr[:2].lower() == "0x" else addr
    raw = bytes.fromhex(h)
    if len(raw) != 20:
        raise ValueError("bad length")
    return raw


def _trx_decode(addr: str) -> bytes:
    ver, h = b58check_decode(addr)
    if ver != 0x41 or len(h) != 20:
        raise ValueError("not a Tron address")
    return h


def _read_records(path: str):
    with open(path, "rb") as f:
        while True:
            block = f.read(REC * 8192)
            if not block:
                return
            for i in range(0, len(block), REC):
                yield block[i:i + REC]


def _merge_unique(runs, out_path: str) -> int:
    n, last = 0, None
    tmp = out_path + ".tmp"
    with open(tmp, "wb") as out:
        buf = bytearray()
        for rec in heapq.merge(*[_read_records(p) for p in runs]):
            if rec != last:
                buf += rec
                last = rec
                n += 1
                if len(buf) >= (1 << 20):
                    out.write(buf)
                    buf.clear()
        out.write(buf)
    os.replace(tmp, out_path)
    for p in runs:
        os.remove(p)
    return n


def build_sorted_file(src: str, out_path: str, decode, tag: str):
    """External merge sort: addresses -> sorted unique 20-byte records, with little RAM."""
    st = {"total": 0, "skipped": 0, "invalid": 0, "examples": []}
    runs, buf = [], []
    tmpdir = os.path.join(TARGET_CACHE_DIR, "tmp")
    os.makedirs(tmpdir, exist_ok=True)

    def flush():
        buf.sort()
        path = os.path.join(tmpdir, f"{tag}_{len(runs)}.run")
        with open(path, "wb") as f:
            f.write(b"".join(buf))
        runs.append(path)
        buf.clear()

    for addr in iter_addresses(src):
        st["total"] += 1
        try:
            h = decode(addr)
        except Exception:
            st["invalid"] += 1
            if len(st["examples"]) < 3:
                st["examples"].append(addr[:60])
            continue
        if h is None:
            st["skipped"] += 1
            continue
        buf.append(h)
        if len(buf) >= SORT_CHUNK:
            flush()
            print(f"    {tag}: {st['total']:,} addresses read ...", flush=True)
    if buf:
        flush()
    st["unique"] = _merge_unique(runs, out_path) if runs else 0
    if not runs:
        open(out_path, "wb").close()
    return st


def build_bloom(paths, out_path: str) -> None:
    total = sum(os.path.getsize(p) // REC for p in paths)
    nbytes = max(128, (total * BLOOM_BITS_PER_ITEM + 7) // 8)
    m = nbytes * 8
    bits = bytearray(nbytes)
    for p in paths:
        for rec in _read_records(p):
            a = int.from_bytes(rec[:8], "big") % m
            bits[a >> 3] |= 1 << (a & 7)
            b = int.from_bytes(rec[8:16], "big") % m
            bits[b >> 3] |= 1 << (b & 7)
    tmp = out_path + ".tmp"
    with open(tmp, "wb") as f:
        f.write(bits)
    os.replace(tmp, out_path)


def _file_sig(path: str) -> str:
    st = os.stat(path)
    return f"{st.st_size}:{st.st_mtime_ns}"


def _load_meta() -> dict:
    try:
        with open(os.path.join(TARGET_CACHE_DIR, "meta.json"), encoding="utf-8") as f:
            meta = json.load(f)
        if meta.get("version") == CACHE_VERSION:
            return meta
    except (OSError, ValueError):
        pass
    return {"version": CACHE_VERSION, "coins": {}, "blooms": {}}


def _save_meta(meta: dict) -> None:
    with open(os.path.join(TARGET_CACHE_DIR, "meta.json"), "w", encoding="utf-8") as f:
        json.dump(meta, f)


def load_prefix_structures(path: str, version: int, p2sh):
    """Old prefix filter (RAM heavy): only used when PREFIX_MATCH = True and few addresses."""
    dec = _p2pkh_decoder("BTC", version, p2sh)
    prefix_map, count = {}, 0
    for addr in iter_addresses(path):
        try:
            if dec(addr) is None:
                continue
        except Exception:
            continue
        count += 1
        if count > PREFIX_MAX_TARGETS:
            print(f"Note: more than {PREFIX_MAX_TARGETS:,} BTC addresses - prefix matching disabled "
                  f"(it needs too much RAM).")
            return None
        prefix_map.setdefault(addr[:PREFIX_LEN], []).append(addr)
    intervals = []
    for p in prefix_map:
        intervals.extend(prefix_intervals(p))
    merged = merge_intervals(intervals)
    return prefix_map, [m[0] for m in merged], [m[1] for m in merged]


def load_targets():
    """Builds (or reuses) the compact target files and returns small descriptors for the workers."""
    os.makedirs(TARGET_CACHE_DIR, exist_ok=True)
    meta = _load_meta()

    coins = []          # (domain, name, version, source file, decoder)
    for name, path, version, p2sh in P2PKH_COINS:
        if name == "BTC" or EXTRA_COINS_ENABLED:
            dec = _ltc_p2pkh_decode if name == "LTC" else _p2pkh_decoder(name, version, p2sh)
            coins.append(("p2", name, version, path, dec))
    if ETH_ENABLED:
        coins.append(("ke", "ETH", None, ETH_ADDRESS_FILE, _eth_decode))
    if EXTRA_COINS_ENABLED:
        coins.append(("ke", "TRX", 0x41, TRX_ADDRESS_FILE, _trx_decode))
        # Litecoin's 3rd address type, nested-segwit (M..., P2SH): a different hash than the
        # legacy/native-segwit addresses above, so it gets its own domain ("p3").
        coins.append(("p3", "LTC_SH", 0x32, LTC_ADDRESS_FILE, _ltc_p2sh_decode))

    built, missing = {}, []
    for domain, name, version, src, dec in coins:
        if not os.path.exists(src):
            missing.append(src)
            continue
        out = os.path.join(TARGET_CACHE_DIR, f"{name}.bin")
        sig = _file_sig(src)
        info = meta["coins"].get(name)
        if not (info and info.get("sig") == sig and info.get("src") == src and os.path.exists(out)):
            print(f"Building the target cache for {name} from {src} (only needed once) ...",
                  flush=True)
            info = build_sorted_file(src, out, dec, name)
            info.update(sig=sig, src=src)
            meta["coins"][name] = info
            _save_meta(meta)
        built[name] = (domain, version, out, info)

    targets = {"p2": None, "ke": None, "p3": None, "prefix": None}
    for domain in ("p2", "ke", "p3"):
        members = [(name, v, path, info["unique"]) for name, (d, v, path, info) in built.items()
                   if d == domain and info["unique"] > 0]
        if not members:
            continue
        bloom = os.path.join(TARGET_CACHE_DIR, f"{domain}.bloom")
        key = "|".join(f"{n}:{built[n][3]['sig']}" for n, _v, _p, _c in members) \
              + f"|{BLOOM_BITS_PER_ITEM}"
        if meta["blooms"].get(domain) != key or not os.path.exists(bloom):
            print(f"Building the Bloom filter ({domain}) ...", flush=True)
            build_bloom([p for _n, _v, p, _c in members], bloom)
            meta["blooms"][domain] = key
            _save_meta(meta)
        targets[domain] = {"bloom": bloom, "coins": members}

    if all(targets[d] is None for d in ("p2", "ke")):
        sys.exit("No usable target addresses found (checked: "
                 + ", ".join(c[3] for c in coins) + ").")

    counts = [f"{n} {info['unique']:,}" for n, (_d, _v, _p, info) in built.items()]
    print("Targets loaded: " + " | ".join(counts))
    for n, (_d, _v, _p, info) in built.items():
        if info["skipped"] or info["invalid"]:
            ex = (" (e.g. " + ", ".join(info["examples"]) + ")") if info["examples"] else ""
            print(f"  Note {n}: {info['skipped']:,} script/other-type and {info['invalid']:,} "
                  f"invalid or unsupported lines skipped{ex}")
    if missing:
        print("Note: not found, skipped: " + ", ".join(missing))

    if PREFIX_MATCH and "BTC" in built:
        _n, path, version, p2sh = P2PKH_COINS[0]
        targets["prefix"] = load_prefix_structures(path, version, p2sh)
    return targets


def parse_range(line: str):
    sep = ":" if ":" in line else ("-" if "-" in line else None)
    if sep is None:
        n = int(line)
        return 1 << (n - 1), (1 << n) - 1
    a, b = line.split(sep, 1)
    start, end = int(a.strip(), 16), int(b.strip(), 16)
    return (start, end) if start <= end else (end, start)


def _read_ranges(path: str, tag: str = ""):
    out = []
    for line in clean_lines(path):
        start, end = parse_range(line)
        if start < 1 or end >= SECP256K1_N:
            sys.exit(f"Invalid range in {path}: {line}")
        out.append((tag + line, start, end))
    return out


def load_ranges(verbose: bool = True):
    """Ranges of range.txt (scanned in order, window by window)"""
    if not os.path.exists(RANGE_FILE):
        if verbose:
            print(f"Note: {RANGE_FILE} not found.")
        return []
    ranges = _read_ranges(RANGE_FILE)
    if verbose:
        print(f"Ranges loaded: {len(ranges)} from {RANGE_FILE}")
    return ranges


def load_random_ranges(verbose: bool = True):
    """Ranges of range1.txt (searched randomly, without limit)"""
    if not os.path.exists(RANGE_FILE_2):
        return []
    rranges = _read_ranges(RANGE_FILE_2, "range1.txt: ")
    if verbose and rranges:
        print(f"Random-search ranges loaded: {len(rranges)} from {RANGE_FILE_2}")
    return rranges


# ---------- Progress ----------
def load_state():
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE) as f:
            s = json.load(f)
        if s.get("v") == STATE_VERSION:
            return s.get("range_index", 0), s.get("step", 0), s.get("done", 0)
    return 0, 0, 0


def save_state(idx: int, step: int, done: int) -> None:
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w") as f:
        json.dump({"v": STATE_VERSION, "range_index": idx, "step": step, "done": done}, f)
    os.replace(tmp, STATE_FILE)


# ---------- Pages (streamed, no huge lists) ----------
def center_point(start: int, end: int) -> int:
    """Exactly 49.9% of the range (integer arithmetic)"""
    return start + (end - start + 1) * PCT_NUM // PCT_DEN


def step_layout(start: int, end: int, step: int):
    """Number of pages above and below the center for one step, plus the start index"""
    C = center_point(start, end)
    i0 = step * PAGES_PER_SIDE
    i_max = (step + 1) * PAGES_PER_SIDE - 1
    up_count = max(0, min(i_max, (end - C) // PAGE_SIZE) - i0 + 1)
    down_count = max(0, min(i_max, (C - 1 - start) // PAGE_SIZE) - i0 + 1)
    return C, i0, up_count, down_count


def up_pages(start, end, C, i0, count):
    for i in range(i0, i0 + count):
        first = C + i * PAGE_SIZE
        yield (first, min(first + PAGE_SIZE - 1, end))


def down_pages(start, end, C, i0, count):
    for i in range(i0, i0 + count):
        last = C - i * PAGE_SIZE - 1
        yield (max(last - PAGE_SIZE + 1, start), last)


def interleaved_pages(start, end, C, i0, up_count, down_count):
    """Pages alternate: up, down, up, down ..."""
    for pair in zip_longest(up_pages(start, end, C, i0, up_count),
                            down_pages(start, end, C, i0, down_count)):
        for p in pair:
            if p is not None:
                yield p


def next_state_after(ranges, idx, step):
    start, end = ranges[idx][1], ranges[idx][2]
    _, _, u2, d2 = step_layout(start, end, step + 1)
    finished = (MAX_STEPS_PER_RANGE and step + 1 >= MAX_STEPS_PER_RANGE) or (u2 + d2 == 0)
    return (idx + 1, 0) if finished else (idx, step + 1)


def worker_count() -> int:
    """WORKERS if set, otherwise all CPU cores minus one (so the computer stays usable)."""
    if WORKERS:
        return WORKERS
    return max(1, (os.cpu_count() or 1) - 1)


def fmt_duration(sec: float) -> str:
    years = sec / 31557600
    if sec < 60:
        return f"{sec:.0f} sec"
    if sec < 3600:
        return f"{sec / 60:.0f} min"
    if sec < 86400:
        return f"{sec / 3600:.1f} hours"
    if years < 1:
        return f"{sec / 86400:.1f} days"
    return f"{years:.3g} years"


# ---------- Workers ----------
_P2 = _KE = _PFX = _P3 = None
_SHOW_ALL = False


def _open_mm(path: str):
    with open(path, "rb") as f:
        return mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)


def _open_domain(d):
    if not d:
        return None
    bloom = _open_mm(d["bloom"])
    return (bloom, len(bloom) * 8,
            [(name, version, _open_mm(path), n) for name, version, path, n in d["coins"]])


def _init_worker(targets, show_all):
    global _P2, _KE, _PFX, _P3, _SHOW_ALL
    if mp.current_process().name != "MainProcess":
        signal.signal(signal.SIGINT, signal.SIG_IGN)     # only the main process handles Ctrl+C
    _SHOW_ALL = show_all
    _P2 = _open_domain(targets.get("p2"))
    _KE = _open_domain(targets.get("ke"))
    _P3 = _open_domain(targets.get("p3"))
    _PFX = targets.get("prefix")


def _bloom_has(mm, m: int, h: bytes) -> bool:
    a = int.from_bytes(h[:8], "big") % m
    if not (mm[a >> 3] >> (a & 7)) & 1:
        return False
    b = int.from_bytes(h[8:16], "big") % m
    return (mm[b >> 3] >> (b & 7)) & 1 == 1


def _bin_has(mm, n: int, h: bytes) -> bool:
    lo, hi = 0, n
    while lo < hi:
        mid = (lo + hi) >> 1
        if mm[mid * REC:(mid + 1) * REC] < h:
            lo = mid + 1
        else:
            hi = mid
    return lo < n and mm[lo * REC:(lo + 1) * REC] == h


def coin_address(name: str, version, h: bytes) -> str:
    """Rebuild the address text from the 20-byte hash (nothing but hashes is stored)."""
    if name == "ETH":
        return "0x" + h.hex()
    if name == "BCH":
        return f"{cashaddr_encode(h)} (legacy {b58check_encode(0, h)})"
    return b58check_encode(version, h)


def ltc_p2sh_hash(compressed_pubkey_hash160: bytes) -> bytes:
    """LTC nested-segwit (M...) hash: hash160 of the P2WPKH witness script 0x00 0x14 <hash160>."""
    return hash160(b"\x00\x14" + compressed_pubkey_hash160)


def scan_page(item):
    label, first, last = item
    hits = []
    p2, ke, pfx, p3 = _P2, _KE, _PFX, _P3
    want_unc = CHECK_BTC_UNCOMPRESSED or _SHOW_ALL
    want_he = ke is not None or _SHOW_ALL
    need_pu = want_unc or want_he
    for k in range(first, last + 1):
        pub = PublicKey.from_secret(k.to_bytes(32, "big"))
        pc = pub.format(compressed=True)
        pu = pub.format(compressed=False) if need_pu else None
        hc = hash160(pc)
        hu = hash160(pu) if want_unc else None
        he = eth_hash(pu) if want_he else None

        if _SHOW_ALL:
            print(f"{k:x} {h160_to_addr(hc)} {h160_to_addr(hu)} 0x{he.hex()}", flush=True)

        matched = False
        if ke is not None and _bloom_has(ke[0], ke[1], he):
            for name, version, mm, n in ke[2]:
                if _bin_has(mm, n, he):
                    hits.append(("EXACT", label, k, coin_address(name, version, he), "", name))
                    matched = True

        if p2 is not None:
            for atype, h in (("compressed", hc), ("uncompressed", hu)):
                if h is not None and _bloom_has(p2[0], p2[1], h):
                    for name, version, mm, n in p2[2]:
                        if _bin_has(mm, n, h):
                            hits.append(("EXACT", label, k, coin_address(name, version, h),
                                         "", f"{name} {atype}"))
                            matched = True

        if p3 is not None:                                 # LTC nested-segwit (M..., P2SH)
            hsh = ltc_p2sh_hash(hc)
            if _bloom_has(p3[0], p3[1], hsh):
                for name, version, mm, n in p3[2]:
                    if _bin_has(mm, n, hsh):
                        hits.append(("EXACT", label, k, coin_address(name, version, hsh),
                                     "", f"{name} P2SH-segwit"))
                        matched = True

        if pfx is not None and not matched:                 # optional BTC prefix filter
            prefix_map, starts, ends = pfx
            for atype, h in (("compressed", hc), ("uncompressed", hu)):
                if h is None:
                    continue
                hv = int.from_bytes(h, "big")
                i = bisect_right(starts, hv) - 1
                if i >= 0 and hv <= ends[i]:
                    addr = h160_to_addr(h)
                    targets = prefix_map.get(addr[:PREFIX_LEN])
                    if targets:
                        hits.append(("PREFIX", label, k, addr, ",".join(targets), atype))
    return hits


# ---------- Online check ----------
ONLINE_STATS = {"checked": 0, "errors": 0, "hits": 0}


def fetch_address(addr: str, base: str = None):
    req = urllib.request.Request(
        (base or API_URL) + addr,
        headers={"User-Agent": "Mozilla/5.0", "Accept": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _int(x) -> int:
    try:
        return int(x)
    except (TypeError, ValueError):
        return 0


def eth_balance_wei(addr: str) -> int:
    return int(eth_rpc_call("eth_getBalance", [addr, "latest"]), 16)


BTC_APIS = [API_URL, API_URL_BACKUP]
ONLINE_STATE = {name: {"on": True, "fail": 0, "api_idx": 0, "disabled_until": 0.0,
                       "last_check": 0.0}
                for name in ("btc", "eth", "bch", "dash", "doge", "ltc", "trx",
                             "bnb", "matic", "avax", "ftm", "arb", "op")}
EXTRA_COIN_KEYS = {"bch", "dash", "doge", "ltc"}


def _service_ok(name: str) -> None:
    ONLINE_STATE[name]["fail"] = 0


def _api_count(name: str) -> int:
    """How many APIs a service can rotate through (BTC: 2 esplora; BCH/DASH/DOGE/LTC: 2 each
    via OTHER_COIN_FETCHERS; ETH/TRX: 1)."""
    if name == "btc":
        return len(BTC_APIS)
    coin = name.upper()
    return len(OTHER_COIN_FETCHERS[coin]) if coin in OTHER_COIN_FETCHERS else 1


def _service_fail(name: str, addr: str, e: Exception) -> None:
    """Count an error; rotate to a backup API (every coin now has one, not just BTC), or put
    the service on a cooldown (instead of switching it off for good) once every API has
    failed / looks blocked."""
    ONLINE_STATS["errors"] += 1
    st = ONLINE_STATE[name]
    st["fail"] += 1
    if SHOW_ONLINE_ERRORS:
        print(f"  [online] error checking {addr}: {e}", flush=True)
    blocked = isinstance(e, urllib.error.HTTPError) and e.code in (403, 429)
    if not (st["on"] and (blocked or st["fail"] >= ONLINE_DISABLE_AFTER)):
        return
    why = "blocked / rate limited" if blocked else f"{st['fail']} errors in a row"
    if st["api_idx"] + 1 < _api_count(name):
        st["api_idx"] += 1
        st["fail"] = 0
        print(f"  [online] {name.upper()} API #{st['api_idx']} ({why}) - switching to its "
              f"backup API.", flush=True)
        return
    st["on"] = False
    st["fail"] = 0
    st["api_idx"] = 0                     # retry from the primary API next time
    st["disabled_until"] = time.time() + ONLINE_COOLDOWN_SECONDS
    print(f"  [online] {name.upper()} online check paused for {ONLINE_COOLDOWN_SECONDS}s "
          f"({why}, every API tried); will retry automatically. Scanning continues.", flush=True)


def _online_hit(msg: str, has_funds: bool = True) -> None:
    ONLINE_STATS["hits"] += 1
    print("Online balance found:" if has_funds else "Online history found:", msg, flush=True)
    with open(ONLINE_FILE, "a", encoding="utf-8") as f:
        f.write(msg + "\n")


def tron_account_info(addr: str) -> dict:
    """Raw TronGrid account object: native TRX balance (in SUN) AND trc20 token balances
    (USDT included) in ONE request - no need for a second call to get both."""
    req = urllib.request.Request(
        TRON_API_URL + addr,
        headers={"User-Agent": "Mozilla/5.0", "Accept": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    accounts = data.get("data") or []
    return accounts[0] if accounts else {}            # {}: address was never activated


def _tron_usdt_from_info(info: dict) -> int:
    for token in info.get("trc20") or []:
        if TRON_USDT_CONTRACT in token:
            return _int(token[TRON_USDT_CONTRACT])
    return 0


def tron_usdt_balance(addr: str) -> int:
    """USDT (TRC20) balance of a Tron address in the smallest unit (6 decimals)"""
    return _tron_usdt_from_info(tron_account_info(addr))


def _state_key(item: str) -> str:
    return "btc" if item.startswith("BTC") else item.lower()


def _coin_enabled(item: str) -> bool:
    if item.startswith("BTC"):
        return True
    if item == "ETH":
        return ETH_ENABLED
    if item in EVM_EXTRA_CHAINS:
        return EVM_EXTRA_ENABLED
    return ONLINE_NEW_COINS and EXTRA_COINS_ENABLED


def _coin_on(item: str) -> bool:
    st = ONLINE_STATE[_state_key(item)]
    if not st["on"] and st["disabled_until"] and time.time() >= st["disabled_until"]:
        st["on"] = True                   # cooldown elapsed: automatically retry
        st["disabled_until"] = 0.0
        print(f"  [online] {_state_key(item).upper()} online check resuming after cooldown.",
              flush=True)
    return _coin_enabled(item) and st["on"]


def _utxo_report(name: str, kind: str, addr: str, info: dict, k: int, label: str) -> None:
    bal = _int(info.get("balance"))
    txs = _int(info.get("txs")) + _int(info.get("unconfirmedTxs"))
    received = _int(info.get("totalReceived"))
    if bal > 0 or txs > 0 or received > 0:              # balance OR any history -> save
        _online_hit(f"range [{label}] | key {k:064x} | {name} {kind} | address {addr} | "
                    f"balance {bal} (smallest unit) | txs {txs} | total received {received}",
                    has_funds=bal > 0)
        if bal > 0:
            sweep_and_wait(name, k, label)
    elif SHOW_ONLINE_CHECKED:
        print(f"  [online] {name} {kind} {addr} | balance: 0 | txs: 0", flush=True)


def _btc_api() -> str:
    return BTC_APIS[ONLINE_STATE["btc"]["api_idx"]]


def _esplora_balance_sat(info: dict) -> int:
    """blockstream.info / mempool.space use esplora's format, NOT the old Blockbook one:
    there is no top-level "balance" field - it has to be computed from chain_stats /
    mempool_stats (funded minus spent, confirmed + unconfirmed). Works the same for every
    BTC address type (legacy 1..., P2SH 3..., bech32 bc1...)."""
    cs = info.get("chain_stats") or {}
    ms = info.get("mempool_stats") or {}
    return (_int(cs.get("funded_txo_sum")) - _int(cs.get("spent_txo_sum"))
            + _int(ms.get("funded_txo_sum")) - _int(ms.get("spent_txo_sum")))


def _online_btc_kind(kind: str, addr: str, k: int, label: str) -> None:
    """BTC: balance only (no txs/totalReceived history check), via whichever BTC API is live."""
    if not ONLINE_STATE["btc"]["on"]:
        return
    try:
        info = fetch_address(addr, _btc_api())
    except Exception as e:
        _service_fail("btc", addr, e)
        return
    _service_ok("btc")
    ONLINE_STATS["checked"] += 1
    bal = _esplora_balance_sat(info)
    if bal > 0:
        _online_hit(f"range [{label}] | key {k:064x} | BTC {kind} | address {addr} | "
                    f"balance {bal} sat")
        sweep_and_wait("BTC", k, label)
    elif SHOW_ONLINE_CHECKED:
        print(f"  [online] BTC {kind} {addr} | balance: 0", flush=True)


def _online_btc_uncompressed(k: int, label: str) -> None:
    _comp, uncomp = key_addresses(k)
    _online_btc_kind("uncompressed", uncomp, k, label)


def _online_btc_compressed(k: int, label: str) -> None:
    comp, _uncomp = key_addresses(k)
    _online_btc_kind("compressed", comp, k, label)


def _online_btc_bech32(k: int, label: str) -> None:
    pub = PublicKey.from_secret(k.to_bytes(32, "big"))
    addr = segwit_addr_encode("bc", 0, hash160(pub.format(compressed=True)))
    _online_btc_kind("bech32 (bc1)", addr, k, label)


def _online_blockbook(name: str, k: int, label: str) -> None:
    version = next(v for n, _p, v, _s in P2PKH_COINS if n == name)
    pub = PublicKey.from_secret(k.to_bytes(32, "big"))
    key = name.lower()
    for kind, data in (("compressed", pub.format(compressed=True)),
                       ("uncompressed", pub.format(compressed=False))):
        if not ONLINE_STATE[key]["on"]:
            return
        h = hash160(data)
        addr = cashaddr_encode(h) if name == "BCH" else b58check_encode(version, h)
        fetch = OTHER_COIN_FETCHERS[name][ONLINE_STATE[key]["api_idx"]]
        try:
            info = fetch(addr)
        except Exception as e:
            _service_fail(key, addr, e)
            continue
        _service_ok(key)
        ONLINE_STATS["checked"] += 1
        _utxo_report(name, kind, addr, info, k, label)


def _online_eth(k: int, label: str) -> None:
    addr = key_eth_address(k)
    try:
        wei = eth_balance_wei(addr)                     # one request per address
    except Exception as e:
        _service_fail("eth", addr, e)
        return
    _service_ok("eth")
    ONLINE_STATS["checked"] += 1
    if wei > 0:                                         # balance > 0 -> save
        _online_hit(f"range [{label}] | key {k:064x} | ETH | address {addr} | "
                    f"balance {wei / 10**18:.8f} ETH")
        sweep_and_wait("ETH", k, label)
    elif SHOW_ONLINE_CHECKED:
        print(f"  [online] ETH {addr} | balance: 0", flush=True)


def evm_rpc_call(url: str, method: str, params: list):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    req = urllib.request.Request(
        url, data=body,
        headers={"User-Agent": "Mozilla/5.0", "Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    if "result" not in data:
        raise RuntimeError(str(data.get("error")))
    return data["result"]


def _online_evm_extra(chain: str, k: int, label: str) -> None:
    """Online balance check only, by request - no target file, no sweep. Same address as ETH
    on every one of these chains (all EVM-compatible), each on its own, separate public RPC -
    see EVM_EXTRA_CHAINS."""
    rpc_url, unit = EVM_EXTRA_CHAINS[chain]
    addr = key_eth_address(k)
    key = chain.lower()
    try:
        wei = int(evm_rpc_call(rpc_url, "eth_getBalance", [addr, "latest"]), 16)
    except Exception as e:
        _service_fail(key, addr, e)
        return
    _service_ok(key)
    ONLINE_STATS["checked"] += 1
    if wei > 0:
        _online_hit(f"range [{label}] | key {k:064x} | {chain} | address {addr} | "
                    f"balance {wei / 10**18:.8f} {unit}")
    elif SHOW_ONLINE_CHECKED:
        print(f"  [online] {chain} {addr} | balance: 0", flush=True)


def _online_trx(k: int, label: str) -> None:
    """Checks BOTH the native TRX balance AND the USDT (TRC20) balance - one request covers
    both, since TronGrid's account endpoint returns the whole account object."""
    pub = PublicKey.from_secret(k.to_bytes(32, "big"))
    addr = b58check_encode(0x41, eth_hash(pub.format(compressed=False)))
    try:
        info = tron_account_info(addr)
    except Exception as e:
        _service_fail("trx", addr, e)
        return
    _service_ok("trx")
    ONLINE_STATS["checked"] += 1
    trx_sun = _int(info.get("balance"))
    usdt = _tron_usdt_from_info(info)
    if trx_sun > 0 or usdt > 0:
        parts = []
        if trx_sun > 0:
            parts.append(f"TRX balance {trx_sun / 10**6:.6f}")
        if usdt > 0:
            parts.append(f"USDT balance {usdt / 10**6:.6f}")
        _online_hit(f"range [{label}] | key {k:064x} | TRON | address {addr} | "
                    + " | ".join(parts))
        if trx_sun > 0:
            sweep_and_wait("TRX", k, label)
        if usdt > 0:
            sweep_and_wait("USDT", k, label)
    elif SHOW_ONLINE_CHECKED:
        print(f"  [online] TRON {addr} | TRX: 0 | USDT: 0", flush=True)


def online_check_coin(item: str, k: int, label: str) -> None:
    if item == "BTC_UNCOMPRESSED":
        _online_btc_uncompressed(k, label)
    elif item == "BTC_COMPRESSED":
        _online_btc_compressed(k, label)
    elif item == "BTC_BECH32":
        _online_btc_bech32(k, label)
    elif item == "ETH":
        _online_eth(k, label)
    elif item == "TRX":
        _online_trx(k, label)
    elif item in EVM_EXTRA_CHAINS:
        _online_evm_extra(item, k, label)
    else:
        _online_blockbook(item, k, label)


def online_sampler(progress, stop_event):
    """One slot every ONLINE_INTERVAL seconds, in the fixed order of ONLINE_SCHEDULE (+
    BTC_EXTRA_DELAY extra seconds before each of the 3 BTC slots). A coin that gets rate
    limited is paused for ONLINE_COOLDOWN_SECONDS and then retried automatically - it is
    never silently dropped for the rest of the run."""
    order = [c for c in ONLINE_SCHEDULE if _coin_enabled(c)]
    if not order:
        return
    i = 0
    next_t = time.time()
    while True:
        coin = order[i % len(order)]
        i += 1
        wait = ONLINE_INTERVAL + (BTC_EXTRA_DELAY if coin.startswith("BTC") else 0.0)
        next_t += wait
        if stop_event.wait(max(0.0, next_t - time.time())):
            break
        if not _coin_on(coin):                           # paused / cooling down: skip this slot
            continue
        skey = _state_key(coin)
        if skey in EXTRA_COIN_KEYS:
            now = time.time()
            if now - ONLINE_STATE[skey]["last_check"] < EXTRA_COIN_MIN_GAP:
                continue                                  # too soon - stay under the shared
                                                           # BlockCypher hourly budget
            ONLINE_STATE[skey]["last_check"] = now
        if SCAN_PAUSED.is_set():                          # a sweep is already in progress: wait
            continue
        item = progress.get("item")
        if item is None:
            continue
        label, first, last = item
        try:
            online_check_coin(coin, random.randint(first, last), label)
        except Exception:
            ONLINE_STATS["errors"] += 1


# ---------- Running ----------
def show_page(title, first, last):
    print(f"--- {title} ({last - first + 1} keys) ---")
    print("key(hex)  compressed_address  uncompressed_address  ethereum_address")
    for k in range(first, last + 1):
        comp, uncomp = key_addresses(k)
        eth = key_eth_address(k) if ETH_ENABLED else "-"
        print(f"{k:x} {comp} {uncomp} {eth}")


# ---------- Sweep: move funds out as soon as a real balance is found ----------
def varint(n: int) -> bytes:
    if n < 0xfd:
        return bytes([n])
    if n <= 0xffff:
        return b"\xfd" + n.to_bytes(2, "little")
    if n <= 0xffffffff:
        return b"\xfe" + n.to_bytes(4, "little")
    return b"\xff" + n.to_bytes(8, "little")


def ecdsa_sign_der(secret_int: int, digest32: bytes) -> bytes:
    """DER-encoded ECDSA signature of a precomputed 32-byte digest (low-S, via libsecp256k1)."""
    return PrivateKey(secret_int.to_bytes(32, "big")).sign(digest32, hasher=None)


def ecdsa_sign_recoverable(secret_int: int, digest32: bytes) -> bytes:
    """65-byte r||s||recid recoverable signature of a precomputed 32-byte digest."""
    return PrivateKey(secret_int.to_bytes(32, "big")).sign_recoverable(digest32, hasher=None)


# ----- UTXO coins (BTC, BCH, DASH, DOGE, LTC): raw P2PKH transaction, sign, broadcast -----
def _p2pkh_script(h160: bytes) -> bytes:
    return b"\x76\xa9\x14" + h160 + b"\x88\xac"


def _ser_outpoint(txid_hex: str, vout: int) -> bytes:
    return bytes.fromhex(txid_hex)[::-1] + vout.to_bytes(4, "little")


def _ser_tx(version: int, inputs, outputs, locktime: int) -> bytes:
    """inputs: [(outpoint(36B), script, sequence)]   outputs: [(value, script)]"""
    out = version.to_bytes(4, "little") + varint(len(inputs))
    for op, script, seq in inputs:
        out += op + varint(len(script)) + script + seq.to_bytes(4, "little")
    out += varint(len(outputs))
    for value, script in outputs:
        out += value.to_bytes(8, "little") + varint(len(script)) + script
    out += locktime.to_bytes(4, "little")
    return out


def legacy_sighash(inputs, outputs, locktime: int, idx: int, script_code: bytes,
                    hashtype: int, version: int) -> bytes:
    """Pre-BIP143 sighash (BTC, DASH, DOGE, LTC): scriptSig of every other input is emptied."""
    sig_inputs = [(op, script_code if i == idx else b"", seq)
                  for i, (op, _s, seq) in enumerate(inputs)]
    preimage = _ser_tx(version, sig_inputs, outputs, locktime) + hashtype.to_bytes(4, "little")
    return sha256d(preimage)


def bip143_sighash(inputs, outputs, locktime: int, idx: int, script_code: bytes,
                    value: int, hashtype: int, version: int) -> bytes:
    """BIP143-style digest (used by Bitcoin Cash with SIGHASH_FORKID)."""
    hash_prevouts = sha256d(b"".join(op for op, _s, _q in inputs))
    hash_sequence = sha256d(b"".join(seq.to_bytes(4, "little") for _o, _s, seq in inputs))
    hash_outputs = sha256d(b"".join(v.to_bytes(8, "little") + varint(len(sc)) + sc
                                    for v, sc in outputs))
    op, _s, seq = inputs[idx]
    preimage = (version.to_bytes(4, "little") + hash_prevouts + hash_sequence + op +
                varint(len(script_code)) + script_code + value.to_bytes(8, "little") +
                seq.to_bytes(4, "little") + hash_outputs + locktime.to_bytes(4, "little") +
                hashtype.to_bytes(4, "little"))
    return sha256d(preimage)


BECH32_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"


def _bech32_polymod(values) -> int:
    gen = [0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3]
    chk = 1
    for v in values:
        b = chk >> 25
        chk = ((chk & 0x1FFFFFF) << 5) ^ v
        for i in range(5):
            if (b >> i) & 1:
                chk ^= gen[i]
    return chk


def _bech32_create_checksum(hrp: str, data) -> list:
    values = [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp] + data
    polymod = _bech32_polymod(values + [0, 0, 0, 0, 0, 0]) ^ 1
    return [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]


def _convertbits(data, frombits: int, tobits: int, pad: bool = True) -> list:
    acc = bits = 0
    ret = []
    maxv = (1 << tobits) - 1
    for value in data:
        acc = (acc << frombits) | value
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad and bits:
        ret.append((acc << (tobits - bits)) & maxv)
    return ret


def segwit_addr_encode(hrp: str, witver: int, witprog: bytes) -> str:
    """BIP173 bech32 P2WPKH/P2WSH address (e.g. 'bc1q...') from a witness program."""
    data = [witver] + _convertbits(list(witprog), 8, 5)
    combined = data + _bech32_create_checksum(hrp, data)
    return hrp + "1" + "".join(BECH32_CHARSET[d] for d in combined)


def _dest_h160(name: str, addr: str) -> bytes:
    if name == "BCH" and addr[:1] not in "13":
        typ, h = cashaddr_decode(addr)
        if typ != 0:
            raise ValueError("the BCH destination must be a P2PKH address")
        return h
    _ver, h = b58check_decode(addr)
    return h


def build_utxo_tx(name: str, secret_int: int, source_h160: bytes, utxos, dest_addr: str,
                   fee_rate: int, reserve_pct: float = 0.0, locktime: int = 0):
    """utxos: [{'txid', 'vout', 'value'}]. reserve_pct of the total is kept behind as a change
    output back to the source address (skipped if that would be dust). Returns (raw_hex, txid)."""
    seq = 0xFFFFFFFD                                    # signals RBF (opt-in replace-by-fee)
    inputs = [(_ser_outpoint(u["txid"], u["vout"]), b"", seq) for u in utxos]
    total_in = sum(u["value"] for u in utxos)
    reserve = int(total_in * reserve_pct)
    if reserve < DUST_LIMIT:
        reserve = 0
    spendable = total_in - reserve
    n_out = 2 if reserve else 1
    est_size = len(utxos) * 148 + n_out * 34 + 10         # ~bytes for a single P2PKH sweep tx
    fee = max(int(est_size * fee_rate), len(utxos) * 200)
    send_value = spendable - fee
    if send_value <= 0:
        raise ValueError(f"fee ({fee}) is bigger than the spendable balance ({spendable}) - "
                         f"nothing to sweep")
    outputs = [(send_value, _p2pkh_script(_dest_h160(name, dest_addr)))]
    if reserve:
        outputs.append((reserve, _p2pkh_script(source_h160)))      # left behind, back to source

    version = 2 if name == "BCH" else 1
    script_code = _p2pkh_script(source_h160)
    pub = PublicKey.from_secret(secret_int.to_bytes(32, "big")).format(compressed=True)
    scripts = []
    for i in range(len(inputs)):
        if name == "BCH":
            digest = bip143_sighash(inputs, outputs, locktime, i, script_code,
                                    utxos[i]["value"], hashtype=0x41, version=version)
            sig = ecdsa_sign_der(secret_int, digest) + bytes([0x41])
        else:
            digest = legacy_sighash(inputs, outputs, locktime, i, script_code,
                                    hashtype=0x01, version=version)
            sig = ecdsa_sign_der(secret_int, digest) + bytes([0x01])
        scripts.append(bytes([len(sig)]) + sig + bytes([len(pub)]) + pub)
    final_inputs = [(op, scripts[i], sq) for i, (op, _s, sq) in enumerate(inputs)]
    raw = _ser_tx(version, final_inputs, outputs, locktime)
    return raw.hex(), sha256d(raw)[::-1].hex()


def fetch_utxos(addr: str, base: str):
    url = base.replace("/address/", "/utxo/") + addr
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return [{"txid": u["txid"], "vout": int(u["vout"]), "value": int(u["value"])} for u in data]


def broadcast_utxo_tx(base: str, raw_hex: str) -> str:
    url = base.replace("/address/", "/sendtx/") + raw_hex
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    if "result" not in data:
        raise RuntimeError(str(data.get("error") or data))
    return data["result"]


def _utxo_confirmations(name: str, txid: str):
    """None = not found (may have been replaced); int = confirmations (0 = pending)."""
    try:
        url = UTXO_BROADCAST_URLS[name].replace("/address/", "/tx/") + txid
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        return int(data.get("confirmations", 0))
    except Exception:
        return None


# ----- esplora backend (blockstream.info / mempool.space): used for the BTC sweep, so the
# sweep uses the same, currently-working API as the balance check instead of only the
# separate Blockbook (trezor) endpoint. -----
def fetch_utxos_esplora(addr: str, base: str):
    req = urllib.request.Request(base + f"address/{addr}/utxo",
                                 headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return [{"txid": u["txid"], "vout": int(u["vout"]), "value": int(u["value"])} for u in data]


def broadcast_tx_esplora(base: str, raw_hex: str) -> str:
    req = urllib.request.Request(base + "tx", data=raw_hex.encode("ascii"),
                                 headers={"User-Agent": "Mozilla/5.0",
                                          "Content-Type": "text/plain"})
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        return resp.read().decode("utf-8").strip()      # esplora returns the raw txid, not JSON


def _utxo_confirmations_esplora(base: str, txid: str):
    try:
        req = urllib.request.Request(base + f"tx/{txid}/status",
                                     headers={"User-Agent": "Mozilla/5.0",
                                              "Accept": "application/json"})
        with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
            st = json.loads(resp.read().decode("utf-8"))
        if not st.get("confirmed"):
            return 0
        req2 = urllib.request.Request(base + "blocks/tip/height",
                                      headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req2, timeout=ONLINE_TIMEOUT) as resp2:
            tip = int(resp2.read().decode("utf-8").strip())
        return max(1, tip - int(st["block_height"]) + 1)
    except Exception:
        return None


# BlockCypher is kept ONLY for the sweep (it conveniently combines UTXO fetch + raw-tx
# broadcast + confirmations in one coherent format); it is no longer used for the frequent
# online balance check (see OTHER_COIN_FETCHERS above). A real sweep only happens once a
# balance is actually found, so its low request rate never comes close to any free-tier cap.
SWEEP_BLOCKCYPHER_BASES = {
    "LTC":  "https://api.blockcypher.com/v1/ltc/main/addrs/",
    "DASH": "https://api.blockcypher.com/v1/dash/main/addrs/",
    "DOGE": "https://api.blockcypher.com/v1/doge/main/addrs/",
}


def fetch_utxos_blockcypher(addr: str, base: str):
    url = base + addr + "?unspentOnly=true&limit=2000" + _bc_token_qs(first=False)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    refs = (data.get("txrefs") or []) + (data.get("unconfirmed_txrefs") or [])
    return [{"txid": r["tx_hash"], "vout": int(r["tx_output_n"]), "value": int(r["value"])}
            for r in refs]


def broadcast_tx_blockcypher(base: str, raw_hex: str) -> str:
    body = json.dumps({"tx": raw_hex}).encode("utf-8")
    url = base.rsplit("addrs/", 1)[0] + "txs/push" + _bc_token_qs()
    req = urllib.request.Request(url, data=body,
                                 headers={"User-Agent": "Mozilla/5.0",
                                          "Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return data["tx"]["hash"]


def _utxo_confirmations_blockcypher(base: str, txid: str):
    try:
        url = base.rsplit("addrs/", 1)[0] + "txs/" + txid + _bc_token_qs()
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        return int(data.get("confirmations", 0))
    except Exception:
        return None


def _sweep_backends(name: str):
    """Ordered (fetch_fn, broadcast_fn, confirm_fn, base) candidates to try, per coin - same
    idea as the online balance check: an independent primary API first, the old Blockbook
    (trezor) endpoint kept as the fallback if that API can't be reached.
      BTC          -> esplora (blockstream.info / mempool.space), then Blockbook
      LTC/DASH/DOGE -> BlockCypher, then Blockbook
      BCH          -> Blockbook only (Blockchair's raw-tx broadcast format isn't wired up
                      here yet, so it stays balance-check-only for now)"""
    if name == "BTC":
        idx = ONLINE_STATE["btc"]["api_idx"] % len(ESPLORA_BASES)
        bases = [ESPLORA_BASES[idx]] + [b for j, b in enumerate(ESPLORA_BASES) if j != idx]
        out = [(fetch_utxos_esplora, broadcast_tx_esplora,
                lambda txid, b=b: _utxo_confirmations_esplora(b, txid), b) for b in bases]
        out.append((fetch_utxos, broadcast_utxo_tx,
                    lambda txid: _utxo_confirmations("BTC", txid), UTXO_BROADCAST_URLS["BTC"]))
        return out
    if name in ("LTC", "DASH", "DOGE"):
        bc_base = SWEEP_BLOCKCYPHER_BASES[name]
        bb_base = UTXO_BROADCAST_URLS[name]
        return [(fetch_utxos_blockcypher, broadcast_tx_blockcypher,
                 lambda txid, b=bc_base: _utxo_confirmations_blockcypher(b, txid), bc_base),
                (fetch_utxos, broadcast_utxo_tx,
                 lambda txid: _utxo_confirmations(name, txid), bb_base)]
    base = UTXO_BROADCAST_URLS[name]
    return [(fetch_utxos, broadcast_utxo_tx,
             lambda txid: _utxo_confirmations(name, txid), base)]


def _sweep_utxo(name: str, secret_int: int, dest: str) -> None:
    pub = PublicKey.from_secret(secret_int.to_bytes(32, "big"))
    version = next(v for n, _p, v, _s in P2PKH_COINS if n == name)
    chosen = None
    for fetch_fn, broadcast_fn, confirm_fn, base in _sweep_backends(name):
        for data_ in (pub.format(compressed=True), pub.format(compressed=False)):
            h160 = hash160(data_)
            addr = cashaddr_encode(h160) if name == "BCH" else b58check_encode(version, h160)
            try:
                utxos = fetch_fn(addr, base)
            except Exception as e:
                print(f"  [sweep] {name}: could not read the UTXOs of {addr} via {base}: {e}",
                      flush=True)
                utxos = []
            if utxos:
                chosen = (h160, addr, utxos, broadcast_fn, confirm_fn, base)
                break
        if chosen:
            break
    if not chosen:
        print(f"  [sweep] {name}: no spendable balance found - nothing to sweep.", flush=True)
        return
    h160, addr, utxos, broadcast_fn, confirm_fn, base = chosen

    fee_rate = int(UTXO_FEE_RATE * FEE_PREMIUM)
    sent = None
    for attempt in range(SWEEP_MAX_BUMPS + 1):
        try:
            raw_hex, txid = build_utxo_tx(name, secret_int, h160, utxos, dest, fee_rate,
                                          reserve_pct=SWEEP_RESERVE_PCT)
            sent = broadcast_fn(base, raw_hex)
        except Exception as e:
            print(f"  [sweep] {name}: broadcast failed ({e}); will retry with a higher fee.",
                  flush=True)
            fee_rate = int(fee_rate * SWEEP_BUMP_FACTOR) + 1
            time.sleep(SWEEP_POLL_SECONDS)
            continue
        print(f"  [sweep] {name}: broadcast {sent} from {addr} via {base} "
              f"(fee rate {fee_rate}, attempt #{attempt + 1})", flush=True)

        found_once, lost = False, False
        deadline = time.time() + SWEEP_BUMP_AFTER
        while time.time() < deadline:
            time.sleep(min(SWEEP_POLL_SECONDS, max(1, deadline - time.time())))
            conf = confirm_fn(sent)
            if conf is not None:
                found_once = True
                if conf >= SWEEP_CONFIRMATIONS:
                    print(f"  [sweep] {name}: confirmed ({conf} confirmation(s)).", flush=True)
                    return
            elif found_once:
                lost = True
                break
        if lost:
            print(f"  [sweep] {name}: transaction {sent} disappeared - likely replaced by a "
                  f"higher-fee transaction. Giving up on this coin.", flush=True)
            return
        fee_rate = int(fee_rate * SWEEP_BUMP_FACTOR) + 1
        print(f"  [sweep] {name}: still unconfirmed, raising the fee and resending ...", flush=True)
    print(f"  [sweep] {name}: gave up after {SWEEP_MAX_BUMPS} fee bumps "
          f"(last transaction: {sent}). Check it manually.", flush=True)


# ----- Ethereum: legacy signed transaction (RLP + EIP-155), broadcast via JSON-RPC -----
def _rlp_len(n: int, offset: int) -> bytes:
    if n < 56:
        return bytes([offset + n])
    nb = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([offset + 55 + len(nb)]) + nb


def rlp_encode(item):
    if isinstance(item, int):
        item = item.to_bytes((item.bit_length() + 7) // 8, "big") if item else b""
    if isinstance(item, bytes):
        if len(item) == 1 and item[0] < 0x80:
            return item
        return _rlp_len(len(item), 0x80) + item
    payload = b"".join(rlp_encode(x) for x in item)
    return _rlp_len(len(payload), 0xC0) + payload


def eth_rpc_call(method: str, params: list):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    req = urllib.request.Request(
        ETH_RPC_URL, data=body,
        headers={"User-Agent": "Mozilla/5.0", "Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    if "result" not in data:
        raise RuntimeError(str(data.get("error")))
    return data["result"]


def eth_tx_hash_and_raw(secret_int: int, nonce: int, gas_price: int, gas_limit: int,
                        to_h160: bytes, value: int, chain_id: int):
    unsigned = [nonce, gas_price, gas_limit, to_h160, value, b"", chain_id, 0, 0]
    digest = keccak.new(digest_bits=256, data=rlp_encode(unsigned)).digest()
    sig = ecdsa_sign_recoverable(secret_int, digest)
    r, s, rec = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:64], "big"), sig[64]
    v = chain_id * 2 + 35 + rec
    raw = rlp_encode([nonce, gas_price, gas_limit, to_h160, value, b"", v, r, s])
    return raw.hex(), "0x" + keccak.new(digest_bits=256, data=raw).digest().hex()


def _sweep_eth(secret_int: int, dest: str) -> None:
    pub = PublicKey.from_secret(secret_int.to_bytes(32, "big"))
    from_addr = "0x" + eth_hash(pub.format(compressed=False)).hex()
    try:
        nonce = int(eth_rpc_call("eth_getTransactionCount", [from_addr, "pending"]), 16)
        gas_price = int(int(eth_rpc_call("eth_gasPrice", []), 16) * FEE_PREMIUM)
    except Exception as e:
        print(f"  [sweep] ETH: could not reach the RPC: {e}", flush=True)
        return
    to_h160 = bytes.fromhex(dest[2:] if dest[:2].lower() == "0x" else dest)

    sent = None
    for attempt in range(SWEEP_MAX_BUMPS + 1):
        try:
            balance = int(eth_rpc_call("eth_getBalance", [from_addr, "latest"]), 16)
        except Exception as e:
            print(f"  [sweep] ETH: could not read the balance: {e}", flush=True)
            time.sleep(SWEEP_POLL_SECONDS)
            continue
        reserve = int(balance * SWEEP_RESERVE_PCT)
        value = balance - reserve - gas_price * ETH_GAS_LIMIT
        if value <= 0:
            print("  [sweep] ETH: balance too small to cover gas - nothing (more) to sweep.",
                  flush=True)
            return
        raw_hex, _txid = eth_tx_hash_and_raw(secret_int, nonce, gas_price, ETH_GAS_LIMIT,
                                             to_h160, value, ETH_CHAIN_ID)
        try:
            sent = eth_rpc_call("eth_sendRawTransaction", ["0x" + raw_hex])
        except Exception as e:
            print(f"  [sweep] ETH: broadcast failed ({e}); will retry with a higher gas price.",
                  flush=True)
            gas_price = int(gas_price * SWEEP_BUMP_FACTOR)
            time.sleep(SWEEP_POLL_SECONDS)
            continue
        print(f"  [sweep] ETH: broadcast {sent} (nonce {nonce}, "
              f"gas price {gas_price / 1e9:.1f} gwei, attempt #{attempt + 1})", flush=True)

        deadline = time.time() + SWEEP_BUMP_AFTER
        while time.time() < deadline:
            time.sleep(min(SWEEP_POLL_SECONDS, max(1, deadline - time.time())))
            try:
                receipt = eth_rpc_call("eth_getTransactionReceipt", [sent])
            except Exception:
                receipt = None
            if receipt:
                ok = int(receipt.get("status", "0x0"), 16) == 1
                print(f"  [sweep] ETH: {'confirmed' if ok else 'confirmed but FAILED on-chain'}.",
                      flush=True)
                return
            try:
                current_nonce = int(eth_rpc_call("eth_getTransactionCount", [from_addr, "latest"]), 16)
            except Exception:
                current_nonce = nonce
            if current_nonce > nonce:
                print(f"  [sweep] ETH: lost the race - another transaction used nonce {nonce} first.",
                      flush=True)
                return
        gas_price = int(gas_price * SWEEP_BUMP_FACTOR)
        print("  [sweep] ETH: still unconfirmed, raising the gas price and resending ...", flush=True)
    print(f"  [sweep] ETH: gave up after {SWEEP_MAX_BUMPS} bumps "
          f"(last transaction: {sent}). Check it manually.", flush=True)


# ----- Tron: native TRX and USDT (TRC20), via the TronGrid REST API -----
def tron_addr_hex(addr_b58: str) -> str:
    ver, h = b58check_decode(addr_b58)
    return (bytes([ver]) + h).hex()


def tron_sign(secret_int: int, tx_id_hex: str) -> str:
    return ecdsa_sign_recoverable(secret_int, bytes.fromhex(tx_id_hex)).hex()


def tron_rpc_post(path: str, payload: dict):
    body = json.dumps(payload).encode()
    req = urllib.request.Request(
        TRON_API_BASE + path, data=body,
        headers={"User-Agent": "Mozilla/5.0", "Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=ONLINE_TIMEOUT) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _sweep_tron(coin: str, secret_int: int, dest: str) -> None:
    pub = PublicKey.from_secret(secret_int.to_bytes(32, "big"))
    owner_h160 = eth_hash(pub.format(compressed=False))
    owner_hex = (b"\x41" + owner_h160).hex()
    owner_b58 = b58check_encode(0x41, owner_h160)
    dest_hex = tron_addr_hex(dest)
    try:
        if coin == "USDT":
            usdt = tron_usdt_balance(owner_b58)
            if usdt <= 0:
                print("  [sweep] USDT: balance already 0 - nothing to sweep.", flush=True)
                return
            amount = usdt - int(usdt * SWEEP_RESERVE_PCT)
            if amount <= 0:
                print("  [sweep] USDT: balance too small - nothing to sweep.", flush=True)
                return
            param = dest_hex[2:].rjust(64, "0") + f"{amount:064x}"
            resp = tron_rpc_post("/wallet/triggersmartcontract", {
                "owner_address": owner_hex, "contract_address": tron_addr_hex(TRON_USDT_CONTRACT),
                "function_selector": "transfer(address,uint256)", "parameter": param,
                "fee_limit": TRON_FEE_LIMIT, "call_value": 0, "visible": False,
            })
            tx = resp.get("transaction")
            if not tx:
                print(f"  [sweep] USDT: could not build the transaction: {resp}", flush=True)
                print("  [sweep] USDT: note - a zero-TRX account cannot pay the fee for a token "
                      "transfer; it needs a small amount of TRX sent in from elsewhere first.",
                      flush=True)
                return
        else:
            acct = tron_rpc_post("/wallet/getaccount", {"address": owner_hex, "visible": False})
            balance = acct.get("balance", 0)
            amount = balance - int(balance * SWEEP_RESERVE_PCT) - TRON_NATIVE_FEE_BUFFER
            if amount <= 0:
                print("  [sweep] TRX: balance too small - nothing to sweep.", flush=True)
                return
            tx = tron_rpc_post("/wallet/createtransaction", {
                "owner_address": owner_hex, "to_address": dest_hex,
                "amount": amount, "visible": False,
            })
            if "txID" not in tx:
                print(f"  [sweep] TRX: could not build the transaction: {tx}", flush=True)
                return
        tx["signature"] = [tron_sign(secret_int, tx["txID"])]
        bresp = tron_rpc_post("/wallet/broadcasttransaction", tx)
        if not bresp.get("result"):
            print(f"  [sweep] {coin}: broadcast rejected: {bresp.get('message', bresp)}", flush=True)
            return
    except Exception as e:
        print(f"  [sweep] {coin}: failed ({e})", flush=True)
        return

    txid = tx["txID"]
    print(f"  [sweep] {coin}: broadcast {txid}", flush=True)
    deadline = time.time() + SWEEP_BUMP_AFTER * 2     # Tron confirms in a few seconds normally
    while time.time() < deadline:
        time.sleep(min(SWEEP_POLL_SECONDS, max(1, deadline - time.time())))
        try:
            info = tron_rpc_post("/wallet/gettransactioninfobyid", {"value": txid})
        except Exception:
            info = {}
        if info.get("blockNumber"):
            print(f"  [sweep] {coin}: confirmed.", flush=True)
            return
    print(f"  [sweep] {coin}: still not confirmed. Tron has no fee-bump mechanism for this - "
          f"check {txid} manually.", flush=True)


# ----- orchestration: pause the scan, sweep, resume -----
SCAN_PAUSED = threading.Event()
_SWEEP_LOCK = threading.Lock()


def sweep_and_wait(coin: str, secret_int: int, label: str) -> None:
    """Pauses the scan, sweeps `coin` to SWEEP_ADDRESSES[coin], waits for it to resolve, resumes."""
    if not SWEEP_ENABLED:
        return
    dest_key = "TRX" if coin == "USDT" else coin
    dest = SWEEP_ADDRESSES.get(dest_key, "")
    if not dest:
        print(f"  [sweep] no SWEEP_ADDRESSES[\"{dest_key}\"] configured - leaving the funds "
              f"where they are.", flush=True)
        return
    if not _SWEEP_LOCK.acquire(blocking=False):
        print(f"  [sweep] a sweep is already in progress - {coin} will be picked up again "
              f"on a later pass.", flush=True)
        return
    SCAN_PAUSED.set()
    try:
        print(f"\n*** Balance found on {coin} (key {secret_int:064x}, range [{label}]). "
              f"Pausing the scan and sweeping to {dest} ... ***", flush=True)
        if coin in ("BCH", "DASH", "DOGE", "LTC", "BTC"):
            _sweep_utxo(coin, secret_int, dest)
        elif coin == "ETH":
            _sweep_eth(secret_int, dest)
        elif coin in ("TRX", "USDT"):
            _sweep_tron(coin, secret_int, dest)
        else:
            print(f"  [sweep] sweeping is not implemented for {coin}.", flush=True)
    except Exception as e:
        print(f"  [sweep] FAILED: {e}. Leaving the funds; you may need to sweep manually.",
              flush=True)
    finally:
        SCAN_PAUSED.clear()
        _SWEEP_LOCK.release()
        print("*** Resuming the scan. ***\n", flush=True)


def run_step(targets, ranges, idx, step, done0, launch_stats):
    """One step (window) of one range, with progress saving. Returns ('stop'|'ok', next_state)"""
    label, start, end = ranges[idx]
    C, i0, up_count, down_count = step_layout(start, end, step)
    total = up_count + down_count
    nxt_idx, nxt_step = next_state_after(ranges, idx, step)

    if total == 0 or done0 >= total:
        save_state(nxt_idx, nxt_step, 0)
        return "ok", (nxt_idx, nxt_step, 0)

    low = max(start, C - (i0 + down_count) * PAGE_SIZE)
    high = min(end, C + (i0 + up_count) * PAGE_SIZE - 1)
    print(f"\n=== Range [{label}] | step {step + 1} ===")
    print(f"Center point (49.9%): {C:x}")
    print(f"Window: {low:x} to {high:x}")
    print(f"{down_count:,} pages below + {up_count:,} pages above = {total:,} pages "
          f"({total * PAGE_SIZE:,} keys)"
          + (f" | resuming from page {done0:,}" if done0 else ""))

    if SHOW_MODE == "first" and done0 == 0:
        if down_count:
            show_page("First page below the center point", *next(down_pages(start, end, C, i0, 1)))
        if up_count:
            show_page("First page above the center point", *next(up_pages(start, end, C, i0, 1)))

    workers = worker_count()
    initargs = (targets, SHOW_MODE == "all")
    pool = None
    if workers == 1:
        _init_worker(*initargs)                     # single core: no Pool
    else:
        pool = mp.Pool(workers, initializer=_init_worker, initargs=initargs)

    progress = {"item": None}
    stop_event = threading.Event()
    if ONLINE_CHECK:
        threading.Thread(target=online_sampler, args=(progress, stop_event),
                         daemon=True).start()

    pages = islice(interleaved_pages(start, end, C, i0, up_count, down_count),
                   done0, None)
    done = done0
    stopped = False
    last_print = time.time()

    try:
        while not stopped:
            while SCAN_PAUSED.is_set():                 # an online-thread sweep is in progress
                time.sleep(1)
            chunk = [(label, a, b) for a, b in islice(pages, CHUNK_PAGES)]
            if not chunk:
                break
            progress["item"] = chunk[0]
            results = (pool.imap_unordered(scan_page, chunk, chunksize=16)
                       if pool else map(scan_page, chunk))

            for j, hits in enumerate(results):
                progress["item"] = chunk[min(j, len(chunk) - 1)]
                if process_hits(hits):
                    stopped = True
                if stopped:
                    break

                launch_stats["pages"] += 1
                now = time.time()
                if now - last_print >= PROGRESS_SECONDS:
                    last_print = now
                    rate = launch_stats["pages"] * PAGE_SIZE / (now - launch_stats["t0"])
                    left = (total - (done + j + 1)) * PAGE_SIZE
                    print(f"  {done + j + 1:,}/{total:,} pages "
                          f"({(done + j + 1) / total * 100:.1f}%) | {rate:,.0f} keys/sec | "
                          f"remaining for this range: {fmt_duration(left / rate)}", flush=True)

            if stopped:
                break
            done += len(chunk)
            save_state(idx, step, done)             # save progress after every chunk
    finally:
        stop_event.set()
        if pool is not None:
            pool.terminate()

    if stopped:
        print("Search stopped (full match).")
        return "stop", (idx, step, done)

    save_state(nxt_idx, nxt_step, 0)
    rate = launch_stats["pages"] * PAGE_SIZE / (time.time() - launch_stats["t0"])
    print(f"Finished range [{label}] | average {rate:,.0f} keys/sec.")
    if ONLINE_CHECK and SHOW_ONLINE_STATS:
        print(f"Online check so far: {ONLINE_STATS['checked']} addresses checked, "
              f"{ONLINE_STATS['errors']} errors, {ONLINE_STATS['hits']} with balance")
    remaining = len(ranges) - nxt_idx
    if remaining > 0 and MAX_STEPS_PER_RANGE:
        eta = remaining * MAX_STEPS_PER_RANGE * total * PAGE_SIZE / rate
        print(f"Ranges remaining: {remaining} | estimated time to finish all: {fmt_duration(eta)}")
    return "ok", (nxt_idx, nxt_step, 0)


_SEEN_MATCHES = set()


def process_hits(hits) -> bool:
    """Print and save the hits of one page. Returns True only if the search should stop."""
    stop = False
    for kind, lb, k, addr, tgt, atype in hits:
        if kind == "EXACT":
            if (k, atype) in _SEEN_MATCHES:             # same key found again (random search)
                continue
            _SEEN_MATCHES.add((k, atype))
            msg = (f"FULL MATCH! range [{lb}] | address ({atype}): {addr} | "
                   f"private key (hex): {k:064x}")
            print(msg, flush=True)
            with open(FOUND_FILE, "a", encoding="utf-8") as f:
                f.write(msg + "\n")
            sweep_and_wait(atype.split()[0], k, lb)
            if STOP_ON_MATCH:
                stop = True
        else:
            msg = (f"range [{lb}] | key {k:064x} | address ({atype}) {addr} | "
                   f"target {tgt}")
            print("Prefix match:", msg, flush=True)
            with open(PREFIX_FILE, "a", encoding="utf-8") as f:
                f.write(msg + "\n")
    return stop


def random_pages(rranges):
    """Endless stream of random pages; every range of range1.txt is equally likely"""
    rng = random.SystemRandom()
    while True:
        label, start, end = rranges[rng.randrange(len(rranges))]
        if end - start + 1 <= PAGE_SIZE:
            yield label, start, end
        else:
            a = rng.randint(start, end - PAGE_SIZE + 1)
            yield label, a, a + PAGE_SIZE - 1


def run_random(targets, rranges):
    """Random search in range1.txt: no limit, until a full match or Ctrl+C. Returns 'stop'|'ok'"""
    print("\n=== Random search (range1.txt) - no limit, press Ctrl+C to stop ===")
    for lb, a, b in rranges:
        print(f"  [{lb}]: {a:x} to {b:x}")

    workers = worker_count()
    initargs = (targets, SHOW_MODE == "all")
    pool = None
    if workers == 1:
        _init_worker(*initargs)
    else:
        pool = mp.Pool(workers, initializer=_init_worker, initargs=initargs)

    progress = {"item": None}
    stop_event = threading.Event()
    if ONLINE_CHECK:
        threading.Thread(target=online_sampler, args=(progress, stop_event),
                         daemon=True).start()

    pages = random_pages(rranges)
    keys = 0
    t0 = last_print = time.time()
    stopped = False
    try:
        while not stopped:
            while SCAN_PAUSED.is_set():                 # an online-thread sweep is in progress
                time.sleep(1)
            chunk = list(islice(pages, CHUNK_PAGES))
            progress["item"] = chunk[0]
            results = (pool.imap_unordered(scan_page, chunk, chunksize=16)
                       if pool else map(scan_page, chunk))
            for j, hits in enumerate(results):
                progress["item"] = chunk[min(j, len(chunk) - 1)]
                if process_hits(hits):
                    stopped = True
                    break
                keys += PAGE_SIZE
                now = time.time()
                if now - last_print >= PROGRESS_SECONDS:
                    last_print = now
                    print(f"  random search: {keys:,} keys scanned | "
                          f"{keys / (now - t0):,.0f} keys/sec | "
                          f"running for {fmt_duration(now - t0)}", flush=True)
    finally:
        stop_event.set()
        if pool is not None:
            pool.terminate()

    if stopped:
        print("Search stopped (full match).")
        return "stop"
    return "ok"


def main():
    if SHOW_MODE not in ("first", "all", "none"):
        sys.exit("Display mode must be first, all or none.")

    targets = load_targets()
    ranges = load_ranges()
    if not ranges and not os.path.exists(RANGE_FILE_2):
        sys.exit(f"Neither {RANGE_FILE} nor {RANGE_FILE_2} found.")
    load_random_ranges(verbose=False)
    idx, step, done = load_state()
    idx = min(idx, len(ranges))

    launch_stats = {"pages": 0, "t0": time.time()}
    stopped = False
    try:
        while idx < len(ranges):
            status, (idx, step, done) = run_step(targets, ranges, idx, step, done, launch_stats)
            if status == "stop":
                stopped = True
                break
            if not CONTINUOUS:
                break

        if not stopped and idx >= len(ranges):
            rranges = load_random_ranges(verbose=False)     # range1.txt may have been added meanwhile
            if rranges:
                print(f"\n{RANGE_FILE} is finished without a full match - "
                      f"switching to the random search in {RANGE_FILE_2}.")
                run_random(targets, rranges)
            else:
                print(f"All ranges are finished (no full match). Create {RANGE_FILE_2} for an "
                      f"unlimited random search, or delete state.json to start over.")
        elif not stopped:
            print(f"Next run will continue from range [{ranges[idx][0]}].")
    except KeyboardInterrupt:
        print(f"\nStopped by the user. The progress of {RANGE_FILE} is saved in state.json.")


if __name__ == "__main__":
    main()
