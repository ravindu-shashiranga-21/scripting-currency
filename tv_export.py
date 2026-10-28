#!/usr/bin/env python3
"""
Re-run TradingView's built-in indicators and strategies on market candles and
export every indicator and every strategy to its own CSV file.

Data: Binance (crypto pairs like ADAUSDT) and Yahoo Finance (stocks AAPL,
RELIANCE.NS; indices ^GSPC, ^NSEI; forex EURUSD=X; futures GC=F; crypto BTC-USD).
A bare symbol tries Binance first, then Yahoo; force one with BINANCE:/YAHOO:.

Pure standard library -- no pandas / pip needed.

Usage (defaults match the chart: ADAUSDT, 1h, Jan 1 2026 -> now, 100K capital):
    python tv_export.py
    python tv_export.py --symbol AAPL --interval 4h --start 2025-06-01 --end 2026-10-01
    python tv_export.py --symbols "BTCUSDT,AAPL,^GSPC,EURUSD=X,GC=F"
    python tv_export.py --watchlist watchlist.txt
    python tv_export.py --pct 100 --commission 0.1 --utc-offset 5.5

Output:
    out/<SYMBOL>_<TF>/indicators/<Indicator>.csv     one file per indicator
    out/<SYMBOL>_<TF>/strategies/<Strategy>.csv      list of trades per strategy
    out/<SYMBOL>_<TF>/strategies_summary.csv         key stats of all strategies
    out/<SYMBOL>_<TF>/candles.csv                    raw OHLCV
    out/all_symbols_summary_<TF>.csv                 every strategy x every symbol

Strategy engine follows Pine defaults: signals on bar close, market orders fill
at next bar open, stop orders fill when touched (intrabar path O-H-L-C or
O-L-H-C, whichever extreme is nearer the open), pyramiding = 0 (an opposite
entry reverses the position). Margin calls are not simulated.
"""
import argparse
import csv
import json
import math
import os
import shutil
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone

API = "https://api.binance.com/api/v3"
YAHOO = "https://query1.finance.yahoo.com/v8/finance/chart/"
YAHOO_NATIVE = {"1m": "1m", "5m": "5m", "15m": "15m", "30m": "30m", "1h": "60m", "1d": "1d",
                "1w": "1wk", "1M": "1mo"}
YAHOO_RESAMPLE = {"3m": "1m", "2h": "60m", "4h": "60m", "6h": "60m", "8h": "60m", "12h": "60m", "3d": "1d"}
YAHOO_STEP_MS = {"1m": 60_000, "5m": 300_000, "15m": 900_000, "30m": 1_800_000, "60m": 3_600_000,
                 "1d": 86_400_000, "1wk": 604_800_000, "1mo": 2_592_000_000}
YAHOO_MAX_DAYS = {"1m": 7, "5m": 59, "15m": 59, "30m": 59, "60m": 729}  # Yahoo intraday history limits
INTERVAL_MS = {
    "1m": 60_000, "3m": 180_000, "5m": 300_000, "15m": 900_000, "30m": 1_800_000,
    "1h": 3_600_000, "2h": 7_200_000, "4h": 14_400_000, "6h": 21_600_000,
    "8h": 28_800_000, "12h": 43_200_000, "1d": 86_400_000, "3d": 259_200_000,
    "1w": 604_800_000, "1M": 2_592_000_000,  # 1M ~ 30 days, only used for paging/warm-up maths
}
# the timeframes in TradingView's interval menu
TV_INTERVALS = ["1m", "3m", "5m", "15m", "30m", "1h", "2h", "4h", "8h", "12h", "1d", "3d", "1w", "1M"]
WARMUP_BARS = 500
MIN_WARMUP = 100
MIN_FREE_DISK_MB = 500


# ----------------------------------------------------------------------------- data

def http_json(url):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def fetch_klines(symbol, interval, start_ms, end_ms):
    step = INTERVAL_MS[interval]
    now = int(time.time() * 1000)
    rows, cur = [], start_ms
    while cur < end_ms:
        batch = http_json(f"{API}/klines?symbol={symbol}&interval={interval}"
                          f"&startTime={cur}&endTime={end_ms}&limit=1000")
        if not batch:
            break
        rows += [r for r in batch if r[6] < now]  # closed candles only
        cur = batch[-1][0] + 1  # +1ms, not +step: months have different lengths
        if len(batch) < 1000:
            break
    d = {k: [] for k in ("t", "o", "h", "l", "c", "v")}
    for r in rows:
        d["t"].append(r[0])
        for k, idx in (("o", 1), ("h", 2), ("l", 3), ("c", 4), ("v", 5)):
            d[k].append(float(r[idx]))
    return d


def tick_size(symbol):
    try:
        info = http_json(f"{API}/exchangeInfo?symbol={symbol}")
        for f in info["symbols"][0]["filters"]:
            if f["filterType"] == "PRICE_FILTER":
                return float(f["tickSize"])
    except Exception:
        pass
    return 0.0001


def empty_series():
    return {k: [] for k in ("t", "o", "h", "l", "c", "v")}


def resample(d, step, now):
    out = empty_series()
    for i, t in enumerate(d["t"]):
        b = t // step * step
        if not out["t"] or out["t"][-1] != b:
            for k in ("o", "h", "l", "c", "v"):
                out[k].append(d[k][i])
            out["t"].append(b)
        else:
            out["h"][-1] = max(out["h"][-1], d["h"][i])
            out["l"][-1] = min(out["l"][-1], d["l"][i])
            out["c"][-1] = d["c"][i]
            out["v"][-1] += d["v"][i]
    if out["t"] and out["t"][-1] + step > now:  # drop the still-forming bucket
        for k in out:
            out[k].pop()
    return out


def fetch_yahoo(symbol, interval, start_ms, end_ms):
    """Stocks, ETFs, indices, forex, futures, crypto (e.g. AAPL, ^GSPC, EURUSD=X, GC=F, BTC-USD)."""
    yi = YAHOO_NATIVE.get(interval) or YAHOO_RESAMPLE[interval]
    now = int(time.time() * 1000)
    if yi in YAHOO_MAX_DAYS:
        start_ms = max(start_ms, now - YAHOO_MAX_DAYS[yi] * 86_400_000)
    url = (f"{YAHOO}{urllib.parse.quote(symbol)}?interval={yi}"
           f"&period1={start_ms // 1000}&period2={end_ms // 1000}&includePrePost=false")
    res = http_json(url)["chart"]["result"][0]
    q = res["indicators"]["quote"][0]
    base_step = YAHOO_STEP_MS[yi]
    d = empty_series()
    for k, ts in enumerate(res.get("timestamp") or []):
        bar = [q["open"][k], q["high"][k], q["low"][k], q["close"][k]]
        if None in bar or ts * 1000 + base_step > now:
            continue
        d["t"].append(ts * 1000)
        for key, x in zip(("o", "h", "l", "c"), bar):
            d[key].append(float(x))
        d["v"].append(float(q["volume"][k] or 0))
    if interval in YAHOO_RESAMPLE:
        d = resample(d, INTERVAL_MS[interval], now)
    return d, 10 ** -res["meta"].get("priceHint", 2)


# TradingView symbols with no direct Yahoo ticker
TV_ALIASES = {
    "SP:SPX": "^GSPC", "TVC:SPX": "^GSPC", "SP:SPY": "SPY", "TVC:NDX": "^NDX", "NASDAQ:NDX": "^NDX",
    "TVC:DJI": "^DJI", "DJ:DJI": "^DJI", "TVC:VIX": "^VIX", "CBOE:VIX": "^VIX", "TVC:DXY": "DX-Y.NYB",
    "NSE:NIFTY": "^NSEI", "NSE:BANKNIFTY": "^NSEBANK", "BSE:SENSEX": "^BSESN", "NSE:CNXIT": "^CNXIT",
    "TVC:GOLD": "GC=F", "OANDA:XAUUSD": "GC=F", "FX_IDC:XAUUSD": "GC=F", "TVC:SILVER": "SI=F",
    "OANDA:XAGUSD": "SI=F", "TVC:USOIL": "CL=F", "TVC:UKOIL": "BZ=F", "NYMEX:CL1!": "CL=F",
    "COMEX:GC1!": "GC=F", "COMEX:SI1!": "SI=F", "NYMEX:NG1!": "NG=F", "CME_MINI:ES1!": "ES=F",
    "CME_MINI:NQ1!": "NQ=F", "TVC:US10Y": "^TNX", "CRYPTOCAP:BTC": "BTC-USD",
}
# exchange prefix -> Yahoo ticker suffix
TV_EXCHANGE_SUFFIX = {
    "NSE": ".NS", "BSE": ".BO", "LSE": ".L", "TSX": ".TO", "TSXV": ".V", "XETR": ".DE", "FWB": ".F",
    "EURONEXT": ".PA", "HKEX": ".HK", "TSE": ".T", "ASX": ".AX", "SIX": ".SW", "BME": ".MC",
    "MIL": ".MI", "KRX": ".KS", "SGX": ".SI", "BMFBOVESPA": ".SA", "TWSE": ".TW", "SSE": ".SS", "SZSE": ".SZ",
}
US_EXCHANGES = {"NASDAQ", "NYSE", "AMEX", "NYSEARCA", "ARCA", "CBOE", "BATS", "OTC", "AMEX_DL"}
FOREX_EXCHANGES = {"FX", "FX_IDC", "OANDA", "FOREXCOM", "PEPPERSTONE", "FXCM", "SAXO", "ICMARKETS", "CAPITALCOM"}
CRYPTO_QUOTES = ("USDT", "USDC", "FDUSD", "BUSD", "BTC", "ETH", "BNB", "USD", "EUR", "INR")


def resolve_symbol(symbol):
    """Turn a TradingView-style 'EXCHANGE:TICKER' into (source, ticker); source '' = try Binance, then Yahoo."""
    s = symbol.strip().upper() if ":" in symbol else symbol.strip()
    if s in TV_ALIASES:
        return "YAHOO", TV_ALIASES[s]
    src, _, sym = s.rpartition(":")
    if src in ("", "BINANCE", "YAHOO"):
        return src, sym
    if src in TV_EXCHANGE_SUFFIX:
        return "YAHOO", sym.replace(".", "-") + TV_EXCHANGE_SUFFIX[src]
    if src in US_EXCHANGES:
        return "YAHOO", sym.replace(".", "-")
    if src in FOREX_EXCHANGES and len(sym) == 6:
        return "YAHOO", sym + "=X"
    for q in CRYPTO_QUOTES:  # other crypto exchanges (COINBASE, BYBIT, OKX, KRAKEN, ...)
        if sym.endswith(q) and len(sym) > len(q):
            if q in ("USDT", "USDC", "FDUSD", "BUSD"):
                return "", sym  # e.g. BYBIT:SOLUSDT -> Binance SOLUSDT, else Yahoo
            return "YAHOO", f"{sym[:-len(q)]}-{q}"  # COINBASE:BTCEUR -> BTC-EUR
    return "YAHOO", sym


def load_symbol(symbol, interval, start_ms, end_ms, max_bars):
    """'BINANCE:ADAUSDT' / 'YAHOO:AAPL' / any TradingView 'EXCHANGE:TICKER'; bare symbols try Binance then Yahoo."""
    src, sym = resolve_symbol(symbol)
    step = INTERVAL_MS[interval]
    if src in ("", "BINANCE"):
        try:
            first = max(start_ms, end_ms - max_bars * step) - WARMUP_BARS * step
            d = fetch_klines(sym, interval, first, end_ms)
            if d["t"]:
                return "Binance", sym, d, tick_size(sym)
        except urllib.error.HTTPError:
            if src == "BINANCE":
                raise
    # markets that close (nights/weekends) need more calendar time for the same number of bars
    first = max(start_ms, end_ms - max_bars * step * 4) - WARMUP_BARS * step * 4
    try:
        d, tick = fetch_yahoo(sym, interval, max(first, 0), end_ms)
    except urllib.error.HTTPError:
        if src == "" and sym.endswith(("USDT", "USDC", "USD")):  # e.g. COINBASE:BTCUSD -> BTC-USD
            base = sym[:-4] if sym.endswith(("USDT", "USDC")) else sym[:-3]
            sym = f"{base}-USD"
            d, tick = fetch_yahoo(sym, interval, max(first, 0), end_ms)
        else:
            raise
    return "Yahoo", sym, d, tick


# ----------------------------------------------------------------------------- series helpers
# Series are plain lists; None means Pine's `na`.

def ok(*xs):
    return all(x is not None for x in xs)


def lift(f, *series):
    out = []
    for xs in zip(*series):
        if ok(*xs):
            try:
                out.append(f(*xs))
            except (ZeroDivisionError, ValueError):
                out.append(None)
        else:
            out.append(None)
    return out


def const(x, n):
    return [x] * n


def shift(s, n=1):
    return [None] * n + s[:len(s) - n] if n > 0 else s[:]


def window(s, n, f):
    out = [None] * len(s)
    for i in range(n - 1, len(s)):
        w = s[i - n + 1:i + 1]
        if None not in w:
            try:
                out[i] = f(w)
            except (ZeroDivisionError, ValueError):
                pass
    return out


def sma(s, n):
    return window(s, n, lambda w: sum(w) / n)


def wma(s, n):
    den = n * (n + 1) / 2
    return window(s, n, lambda w: sum(x * (k + 1) for k, x in enumerate(w)) / den)


def stdev(s, n):  # biased, like ta.stdev
    def f(w):
        m = sum(w) / n
        return math.sqrt(max(sum((x - m) ** 2 for x in w) / n, 0.0))
    return window(s, n, f)


def dev(s, n):  # mean absolute deviation, like ta.dev
    def f(w):
        m = sum(w) / n
        return sum(abs(x - m) for x in w) / n
    return window(s, n, f)


def rsum(s, n):
    return window(s, n, sum)


def highest(s, n):
    return window(s, n, max)


def lowest(s, n):
    return window(s, n, min)


def _ewm(s, n, alpha):
    seed = sma(s, n)
    out, prev = [None] * len(s), None
    for i, x in enumerate(s):
        if x is None:
            continue
        prev = seed[i] if prev is None else alpha * x + (1 - alpha) * prev
        out[i] = prev
    return out


def ema(s, n):
    return _ewm(s, n, 2 / (n + 1))


def rma(s, n):
    return _ewm(s, n, 1 / n)


def change(s, n=1):
    return lift(lambda a, b: a - b, s, shift(s, n))


def cum(s):
    out, tot = [], 0.0
    for x in s:
        tot += x or 0.0
        out.append(tot)
    return out


def crossover(a, b):
    return [i > 0 and ok(a[i], b[i], a[i - 1], b[i - 1]) and a[i] > b[i] and a[i - 1] <= b[i - 1]
            for i in range(len(a))]


def crossunder(a, b):
    return [i > 0 and ok(a[i], b[i], a[i - 1], b[i - 1]) and a[i] < b[i] and a[i - 1] >= b[i - 1]
            for i in range(len(a))]


def true_range(h, l, c, handle_na=True):
    out = []
    for i in range(len(c)):
        if i == 0:
            out.append(h[0] - l[0] if handle_na else None)
        else:
            out.append(max(h[i] - l[i], abs(h[i] - c[i - 1]), abs(l[i] - c[i - 1])))
    return out


def atr(h, l, c, n):
    return rma(true_range(h, l, c), n)


def rsi(s, n):
    up = rma(lift(lambda a, b: max(a - b, 0.0), s, shift(s)), n)
    dn = rma(lift(lambda a, b: max(b - a, 0.0), s, shift(s)), n)

    def f(u, d):
        if d == 0:
            return 100.0
        if u == 0:
            return 0.0
        return 100 - 100 / (1 + u / d)
    return lift(f, up, dn)


def stoch(src, h, l, n):
    hh, ll = highest(h, n), lowest(l, n)
    return lift(lambda x, a, b: 100 * (x - b) / (a - b), src, hh, ll)


def linreg(s, n, offset=0):
    xs = list(range(n))
    mx = sum(xs) / n
    sxx = sum((x - mx) ** 2 for x in xs)

    def f(w):
        my = sum(w) / n
        slope = sum((x - mx) * (y - my) for x, y in zip(xs, w)) / sxx
        return my - slope * mx + slope * (n - 1 - offset)
    return window(s, n, f)


def alma(s, n, offset=0.85, sigma=6):
    m = offset * (n - 1)
    sd = n / sigma
    wts = [math.exp(-((k - m) ** 2) / (2 * sd * sd)) for k in range(n)]
    norm = sum(wts)
    return window(s, n, lambda w: sum(x * wt for x, wt in zip(w, wts)) / norm)


def hma(s, n):
    a = wma(s, n // 2)
    b = wma(s, n)
    return wma(lift(lambda x, y: 2 * x - y, a, b), int(math.floor(math.sqrt(n))))


def bars_since_extreme(s, n, use_max):
    """ta.highestbars/lowestbars (returns offset <= 0)."""
    out = [None] * len(s)
    for i in range(n - 1, len(s)):
        w = s[i - n + 1:i + 1]
        if None in w:
            continue
        ext = max(w) if use_max else min(w)
        k = len(w) - 1 - w[::-1].index(ext)
        out[i] = k - (n - 1)
    return out


def pivot(s, left, right, is_high):
    out = [None] * len(s)
    for i in range(left + right, len(s)):
        p = i - right
        v = s[p]
        others = s[p - left:p] + s[p + 1:i + 1]
        if all((v > x) if is_high else (v < x) for x in others):
            out[i] = v
    return out


def supertrend(h, l, c, factor, period):
    a = atr(h, l, c, period)
    n = len(c)
    st, direction = [None] * n, [None] * n
    ub_prev = lb_prev = 0.0
    for i in range(n):
        if a[i] is None:
            continue
        src = (h[i] + l[i]) / 2
        ub, lb = src + factor * a[i], src - factor * a[i]
        pc = c[i - 1] if i > 0 else c[i]
        lb = lb if (lb > lb_prev or pc < lb_prev) else lb_prev
        ub = ub if (ub < ub_prev or pc > ub_prev) else ub_prev
        if i == 0 or a[i - 1] is None:
            d = 1
        elif st[i - 1] == ub_prev:
            d = -1 if c[i] > ub else 1
        else:
            d = 1 if c[i] < lb else -1
        st[i] = lb if d == -1 else ub
        direction[i] = d
        ub_prev, lb_prev = ub, lb
    return st, direction


def psar(h, l, c, start=0.02, inc=0.02, mx=0.2):
    """ta.sar; also returns trend flag and the next-bar SAR used by the strategy."""
    n = len(c)
    res, below, nxt = [None] * n, [None] * n, [None] * n
    result = max_min = acc = 0.0
    is_below = False
    for i in range(1, n):
        first = False
        if i == 1:
            if c[1] >= c[0]:
                is_below, max_min, result = True, h[1], l[0]
            else:
                is_below, max_min, result = False, l[1], h[0]
            first, acc = True, start
        result = result + acc * (max_min - result)
        if is_below:
            if result > l[i]:
                first, is_below = True, False
                result = max(h[i], max_min)
                max_min, acc = l[i], start
        else:
            if result < h[i]:
                first, is_below = True, True
                result = min(l[i], max_min)
                max_min, acc = h[i], start
        if not first:
            if is_below and h[i] > max_min:
                max_min, acc = h[i], min(acc + inc, mx)
            elif not is_below and l[i] < max_min:
                max_min, acc = l[i], min(acc + inc, mx)
        if is_below:
            result = min(result, l[i - 1], l[i - 2] if i > 1 else l[i - 1])
        else:
            result = max(result, h[i - 1], h[i - 2] if i > 1 else h[i - 1])
        res[i], below[i] = result, is_below
        nb = result + acc * (max_min - result)
        nxt[i] = min(nb, l[i], l[i - 1]) if is_below else max(nb, h[i], h[i - 1])
    return res, below, nxt


# ----------------------------------------------------------------------------- indicators

def build_indicators(d):
    t, o, h, l, c, v = d["t"], d["o"], d["h"], d["l"], d["c"], d["v"]
    n = len(c)
    hl2 = lift(lambda a, b: (a + b) / 2, h, l)
    hlc3 = lift(lambda a, b, x: (a + b + x) / 3, h, l, c)
    tr = true_range(h, l, c)
    I = {}

    I["SMA 9"] = {"SMA": sma(c, 9)}
    I["EMA 9"] = {"EMA": ema(c, 9)}
    I["WMA 9"] = {"WMA": wma(c, 9)}
    I["VWMA 20"] = {"VWMA": lift(lambda a, b: a / b, sma(lift(lambda x, y: x * y, c, v), 20), sma(v, 20))}
    I["Hull MA 9"] = {"HMA": hma(c, 9)}
    I["ALMA 9"] = {"ALMA": alma(c, 9, 0.85, 6)}
    e1 = ema(c, 9)
    e2 = ema(e1, 9)
    e3 = ema(e2, 9)
    I["Double EMA 9"] = {"DEMA": lift(lambda a, b: 2 * a - b, e1, e2)}
    I["Triple EMA 9"] = {"TEMA": lift(lambda a, b, x: 3 * (a - b) + x, e1, e2, e3)}
    I["Smoothed MA 7"] = {"SMMA": rma(c, 7)}
    I["Least Squares MA 25"] = {"LSMA": linreg(c, 25)}
    I["Linear Regression 100"] = {"LinReg": linreg(c, 100)}

    r = rsi(c, 14)
    I["RSI 14"] = {"RSI": r, "RSI_MA_14": sma(r, 14)}

    fast, slow = ema(c, 12), ema(c, 26)
    macd = lift(lambda a, b: a - b, fast, slow)
    sig = ema(macd, 9)
    I["MACD 12 26 9"] = {"MACD": macd, "Signal": sig, "Histogram": lift(lambda a, b: a - b, macd, sig)}

    k = sma(stoch(c, h, l, 14), 1)
    I["Stochastic 14 1 3"] = {"K": k, "D": sma(k, 3)}

    srk = sma(stoch(r, r, r, 14), 3)
    I["Stochastic RSI 3 3 14 14"] = {"K": srk, "D": sma(srk, 3)}

    basis, sd = sma(c, 20), stdev(c, 20)
    bbu = lift(lambda b, s: b + 2 * s, basis, sd)
    bbl = lift(lambda b, s: b - 2 * s, basis, sd)
    I["Bollinger Bands 20 2"] = {"Basis": basis, "Upper": bbu, "Lower": bbl}
    I["Bollinger Bands %B 20 2"] = {"%B": lift(lambda x, u, lo: (x - lo) / (u - lo), c, bbu, bbl)}
    I["Bollinger BandWidth 20 2"] = {"BBW": lift(lambda u, lo, b: (u - lo) / b * 100, bbu, bbl, basis)}

    kma, katr = ema(c, 20), atr(h, l, c, 10)
    I["Keltner Channels 20 2"] = {"Basis": kma,
                                  "Upper": lift(lambda m, a: m + 2 * a, kma, katr),
                                  "Lower": lift(lambda m, a: m - 2 * a, kma, katr)}
    dh, dl = highest(h, 20), lowest(l, 20)
    I["Donchian Channels 20"] = {"Upper": dh, "Lower": dl, "Basis": lift(lambda a, b: (a + b) / 2, dh, dl)}
    I["Envelope 20 10%"] = {"Basis": basis,
                            "Upper": lift(lambda b: b * 1.1, basis),
                            "Lower": lift(lambda b: b * 0.9, basis)}

    I["ATR 14"] = {"ATR": atr(h, l, c, 14)}

    up = change(h)
    down = lift(lambda x: -x, change(l))
    pdm = lift(lambda u, dn: u if (u > dn and u > 0) else 0.0, up, down)
    mdm = lift(lambda u, dn: dn if (dn > u and dn > 0) else 0.0, up, down)
    trur = rma(tr, 14)
    plus = lift(lambda a, b: 100 * a / b, rma(pdm, 14), trur)
    minus = lift(lambda a, b: 100 * a / b, rma(mdm, 14), trur)
    adx = rma(lift(lambda p, m: abs(p - m) / ((p + m) or 1), plus, minus), 14)
    I["DMI ADX 14 14"] = {"+DI": plus, "-DI": minus, "ADX": lift(lambda x: 100 * x, adx)}

    I["CCI 20"] = {"CCI": lift(lambda x, m, dv: (x - m) / (0.015 * dv), hlc3, sma(hlc3, 20), dev(hlc3, 20))}
    hh14, ll14 = highest(h, 14), lowest(l, 14)
    I["Williams %R 14"] = {"%R": lift(lambda x, a, b: 100 * (x - a) / (a - b), c, hh14, ll14)}
    I["Momentum 10"] = {"MOM": change(c, 10)}
    I["Rate Of Change 9"] = {"ROC": lift(lambda a, b: 100 * (a - b) / b, c, shift(c, 9))}

    sign_chg = lift(lambda x: (x > 0) - (x < 0), change(c))
    I["On Balance Volume"] = {"OBV": cum(lift(lambda s, x: s * x, sign_chg, v))}
    I["Net Volume"] = {"NetVolume": lift(lambda s, x: s * x, sign_chg, v)}
    I["Price Volume Trend"] = {"PVT": cum(lift(lambda ch, p, x: ch / p * x, change(c), shift(c), v))}
    I["Volume"] = {"Volume": v, "Volume_MA_20": sma(v, 20)}

    ch3 = change(hlc3)
    mf_up = rsum(lift(lambda x, ch, p: 0.0 if ch <= 0 else x * p, v, ch3, hlc3), 14)
    mf_dn = rsum(lift(lambda x, ch, p: 0.0 if ch >= 0 else x * p, v, ch3, hlc3), 14)
    I["Money Flow Index 14"] = {"MFI": lift(lambda a, b: 100 - 100 / (1 + a / b), mf_up, mf_dn)}

    ad = [0.0 if (c[i] == h[i] and c[i] == l[i]) or h[i] == l[i]
          else ((2 * c[i] - l[i] - h[i]) / (h[i] - l[i])) * v[i] for i in range(n)]
    I["Chaikin Money Flow 20"] = {"CMF": lift(lambda a, b: a / b, rsum(ad, 20), rsum(v, 20))}
    adl = cum(ad)
    I["Accumulation Distribution"] = {"ADL": adl}
    I["Chaikin Oscillator 3 10"] = {"ChaikinOsc": lift(lambda a, b: a - b, ema(adl, 3), ema(adl, 10))}

    a_up = lift(lambda x: 100 * (x + 14) / 14, bars_since_extreme(h, 15, True))
    a_dn = lift(lambda x: 100 * (x + 14) / 14, bars_since_extreme(l, 15, False))
    I["Aroon 14"] = {"Up": a_up, "Down": a_dn}
    I["Aroon Oscillator 14"] = {"AroonOsc": lift(lambda a, b: a - b, a_up, a_dn)}

    I["Parabolic SAR"] = {"SAR": psar(h, l, c)[0]}
    st, std = supertrend(h, l, c, 3, 10)
    I["Supertrend 10 3"] = {"Supertrend": st, "Direction(-1=up)": std}

    def donch(p):
        return lift(lambda a, b: (a + b) / 2, lowest(l, p), highest(h, p))
    conv, base = donch(9), donch(26)
    span_a = shift(lift(lambda a, b: (a + b) / 2, conv, base), 25)
    span_b = shift(donch(52), 25)
    lagging = c[25:] + [None] * 25
    I["Ichimoku 9 26 52 26"] = {"Conversion": conv, "Base": base, "LeadingSpanA": span_a,
                                "LeadingSpanB": span_b, "LaggingSpan": lagging}

    vw, pv_sum, v_sum, day = [], 0.0, 0.0, None
    for i in range(n):
        dday = t[i] // 86_400_000
        if dday != day:
            day, pv_sum, v_sum = dday, 0.0, 0.0
        pv_sum += hlc3[i] * v[i]
        v_sum += v[i]
        vw.append(pv_sum / v_sum if v_sum else None)
    I["VWAP Session (UTC day)"] = {"VWAP": vw}

    I["Awesome Oscillator"] = {"AO": lift(lambda a, b: a - b, sma(hl2, 5), sma(hl2, 34))}
    I["Choppiness Index 14"] = {"CHOP": lift(lambda s, a, b: 100 * math.log10(s / (a - b)) / math.log10(14),
                                             rsum(tr, 14), hh14, ll14)}
    lc = [math.log(x) for x in c]
    I["TRIX 18"] = {"TRIX": lift(lambda x: 10000 * x, change(ema(ema(ema(lc, 18), 18), 18)))}

    pc = shift(c)
    bp = lift(lambda x, lo, p: x - min(lo, p), c, l, pc)
    tr_uo = lift(lambda hi, lo, p: max(hi, p) - min(lo, p), h, l, pc)

    def uo_avg(p):
        return lift(lambda a, b: a / b, rsum(bp, p), rsum(tr_uo, p))
    I["Ultimate Oscillator 7 14 28"] = {"UO": lift(lambda a, b, x: 100 * (4 * a + 2 * b + x) / 7,
                                                   uo_avg(7), uo_avg(14), uo_avg(28))}

    m = change(c)
    s1 = rsum(lift(lambda x: x if x >= 0 else 0.0, m), 9)
    s2 = rsum(lift(lambda x: 0.0 if x >= 0 else -x, m), 9)
    I["Chande Momentum Oscillator 9"] = {"CMO": lift(lambda a, b: 100 * (a - b) / (a + b), s1, s2)}
    I["Detrended Price Oscillator 21"] = {"DPO": lift(lambda x, mm: x - mm, c, shift(sma(c, 21), 11))}
    I["Elder Force Index 13"] = {"EFI": ema(lift(lambda ch, x: ch * x, change(c), v), 13)}
    I["Ease Of Movement 14"] = {"EOM": sma(lift(lambda ch, hi, lo, x: 10000 * ch * (hi - lo) / x,
                                                change(hl2), h, l, v), 14)}
    I["Price Oscillator 10 21"] = {"PPO": lift(lambda a, b: (a - b) / b * 100, sma(c, 10), sma(c, 21))}
    I["Historical Volatility 10"] = {"HV": lift(lambda x: 100 * x * math.sqrt(365),
                                                stdev(lift(lambda a, b: math.log(a / b), c, pc), 10))}

    def roc(p):
        return lift(lambda a, b: 100 * (a - b) / b, c, shift(c, p))
    I["Coppock Curve"] = {"Coppock": wma(lift(lambda a, b: a + b, roc(14), roc(11)), 10)}

    pchg = change(c)
    num = ema(ema(pchg, 25), 13)
    den = ema(ema(lift(abs, pchg), 25), 13)
    tsi = lift(lambda a, b: 100 * a / b, num, den)
    I["True Strength Index 25 13"] = {"TSI": tsi, "Signal": ema(tsi, 13)}

    span = lift(lambda a, b: a - b, h, l)
    e9 = ema(span, 9)
    I["Mass Index 10"] = {"MassIndex": rsum(lift(lambda a, b: a / b, e9, ema(e9, 9)), 10)}

    vmp = rsum(lift(lambda hi, lo: abs(hi - lo), h, shift(l)), 14)
    vmm = rsum(lift(lambda lo, hi: abs(lo - hi), l, shift(h)), 14)
    str_ = rsum(tr, 14)
    I["Vortex Indicator 14"] = {"VI+": lift(lambda a, b: a / b, vmp, str_),
                                "VI-": lift(lambda a, b: a / b, vmm, str_)}
    e13 = ema(c, 13)
    I["Bull Bear Power 13"] = {"BBPower": lift(lambda hi, lo, e: (hi - e) + (lo - e), h, l, e13)}
    I["Balance of Power"] = {"BOP": lift(lambda cl, op, hi, lo: (cl - op) / (hi - lo), c, o, h, l)}

    def swma(s):
        return lift(lambda a, b, x, y: a / 6 + b * 2 / 6 + x * 2 / 6 + y / 6,
                    shift(s, 3), shift(s, 2), shift(s, 1), s)
    rvi = lift(lambda a, b: a / b, rsum(swma(lift(lambda a, b: a - b, c, o)), 10),
               rsum(swma(lift(lambda a, b: a - b, h, l)), 10))
    I["Relative Vigor Index 10"] = {"RVGI": rvi, "Signal": swma(rvi)}

    fh, fl = highest(hl2, 9), lowest(hl2, 9)
    fish, trig, val, f1 = [None] * n, [None] * n, 0.0, 0.0
    for i in range(n):
        if fh[i] is None or fh[i] == fl[i]:
            continue
        val = 0.66 * ((hl2[i] - fl[i]) / (fh[i] - fl[i]) - 0.5) + 0.67 * val
        val = 0.999 if val > 0.99 else (-0.999 if val < -0.99 else val)
        prev = f1
        f1 = 0.5 * math.log((1 + val) / (1 - val)) + 0.5 * f1
        fish[i], trig[i] = f1, prev
    I["Fisher Transform 9"] = {"Fisher": fish, "Trigger": trig}

    kst = lift(lambda a, b, x, y: a + 2 * b + 3 * x + 4 * y,
               sma(roc(10), 10), sma(roc(15), 10), sma(roc(20), 10), sma(roc(30), 15))
    I["Know Sure Thing"] = {"KST": kst, "Signal": sma(kst, 9)}
    return I


# ----------------------------------------------------------------------------- strategy engine

class Engine:
    def __init__(self, d, capital, pct, qty, commission, start_i, end_i):
        self.d = d
        self.capital, self.pct, self.fixed_qty, self.comm = capital, pct, qty, commission / 100
        self.start_i, self.end_i = start_i, end_i
        self.active = False
        self.orders = {}           # id -> (direction, stop or None)
        self.pos = 0               # +1 long, -1 short, 0 flat
        self.qty = 0.0
        self.realized = 0.0
        self.trade = None
        self.trades = []
        self.equity_curve = []

    # --- Pine-like API used by strategies
    def entry(self, oid, direction, stop=None):
        if self.active:
            self.orders.pop(oid, None)  # re-issuing an id moves it to the back, like modifying
            self.orders[oid] = (direction, stop)

    def cancel(self, oid):
        if self.active:
            self.orders.pop(oid, None)

    # --- internals
    def _equity(self):
        return self.capital + self.realized

    def _open(self, direction, price, oid, i):
        eq = self._equity()
        qty = self.fixed_qty if self.fixed_qty else eq * self.pct / 100 / price
        if qty <= 0:
            return
        self.pos, self.qty = direction, qty
        self.trade = {"dir": direction, "entry_sig": oid, "entry_i": i, "entry_px": price, "qty": qty,
                      "entry_comm": qty * price * self.comm, "hi": price, "lo": price}

    def _close(self, price, oid, i):
        tr = self.trade
        exit_comm = tr["qty"] * price * self.comm
        profit = tr["dir"] * tr["qty"] * (price - tr["entry_px"]) - tr["entry_comm"] - exit_comm
        self.realized += profit
        tr.update(exit_sig=oid, exit_i=i, exit_px=price, profit=profit, status="Closed")
        self.trades.append(tr)
        self.pos, self.qty, self.trade = 0, 0.0, None

    def _fill(self, direction, price, oid, i):
        if self.pos == -direction:
            self._close(price, oid, i)
        self._open(direction, price, oid, i)

    def _process_bar(self, i):
        o, h, l, c = self.d["o"][i], self.d["h"][i], self.d["l"][i], self.d["c"][i]
        path = [o, h, l, c] if (h - o) <= (o - l) else [o, l, h, c]

        def hit(direction, stop):
            if stop is None:
                return -1.0, o
            if direction > 0:
                if o >= stop:
                    return 0.0, o
                for k in range(3):
                    a, b = path[k], path[k + 1]
                    if a < stop <= b:
                        return k + (stop - a) / (b - a), stop
            else:
                if o <= stop:
                    return 0.0, o
                for k in range(3):
                    a, b = path[k], path[k + 1]
                    if a > stop >= b:
                        return k + (a - stop) / (a - b), stop
            return None

        events = []
        for seq, (oid, (direction, stop)) in enumerate(list(self.orders.items())):
            if stop is None:
                self.orders.pop(oid)  # market orders live for one bar
            r = hit(direction, stop)
            if r is not None:
                events.append((r[0], seq, oid, direction, r[1], stop is None))
        for _, _, oid, direction, price, is_market in sorted(events):
            if self.pos == direction:
                continue  # pyramiding = 0: stays pending (stop) / dropped (market)
            if not is_market and oid not in self.orders:
                continue
            self.orders.pop(oid, None)
            self._fill(direction, price, oid, i)

        if self.trade:
            self.trade["hi"] = max(self.trade["hi"], h)
            self.trade["lo"] = min(self.trade["lo"], l)

    def run(self, strategy):
        n = len(self.d["c"])
        for i in range(min(n, self.end_i + 1)):
            if i > self.start_i:
                self._process_bar(i)
            self.active = i >= self.start_i
            strategy(i, self)
            if self.active:
                open_pnl = 0.0
                if self.trade:
                    open_pnl = self.trade["dir"] * self.trade["qty"] * (self.d["c"][i] - self.trade["entry_px"])
                self.equity_curve.append(self._equity() + open_pnl)
        if self.trade:
            tr = self.trade
            px = self.d["c"][self.end_i]
            tr.update(exit_sig="Open", exit_i=self.end_i, exit_px=px, status="Open",
                      profit=tr["dir"] * tr["qty"] * (px - tr["entry_px"]) - tr["entry_comm"])
            self.trades.append(tr)


# ----------------------------------------------------------------------------- built-in strategies

def build_strategies(d, mintick):
    o, h, l, c = d["o"], d["h"], d["l"], d["c"]
    n = len(c)
    S = {}

    def strategy(name):
        def deco(f):
            S[name] = f
            return f
        return deco

    @strategy("BarUpDn Strategy")
    def _(i, E):
        if i < 1:
            return
        if c[i] > o[i] and o[i] > c[i - 1]:
            E.entry("BarUp", 1)
        if c[i] < o[i] and o[i] < c[i - 1]:
            E.entry("BarDn", -1)

    bb_basis, bb_sd = sma(c, 20), stdev(c, 20)
    bb_up = lift(lambda b, s: b + 2 * s, bb_basis, bb_sd)
    bb_lo = lift(lambda b, s: b - 2 * s, bb_basis, bb_sd)
    bb_long, bb_short = crossover(c, bb_lo), crossunder(c, bb_up)

    @strategy("Bollinger Bands Strategy")
    def _(i, E):
        if bb_long[i]:
            E.entry("BBandLE", 1, stop=bb_lo[i])
        else:
            E.cancel("BBandLE")
        if bb_short[i]:
            E.entry("BBandSE", -1, stop=bb_up[i])
        else:
            E.cancel("BBandSE")

    cb_hh, cb_ll = highest(h, 5), lowest(l, 5)

    @strategy("Channel Breakout Strategy")
    def _(i, E):
        if i >= 5 and ok(cb_hh[i], cb_ll[i]):
            E.entry("ChBrkLE", 1, stop=cb_hh[i] + mintick)
            E.entry("ChBrkSE", -1, stop=cb_ll[i] - mintick)

    ups, dns = [0] * n, [0] * n
    for i in range(1, n):
        ups[i] = ups[i - 1] + 1 if c[i] > c[i - 1] else 0
        dns[i] = dns[i - 1] + 1 if c[i] < c[i - 1] else 0

    @strategy("Consecutive Up-Down Strategy")
    def _(i, E):
        if ups[i] >= 3:
            E.entry("ConsUpLE", 1)
        if dns[i] >= 3:
            E.entry("ConsDnSE", -1)

    @strategy("InSide Bar Strategy")
    def _(i, E):
        if i >= 1 and h[i] < h[i - 1] and l[i] > l[i - 1]:
            if c[i] > o[i]:
                E.entry("InsBarLE", 1)
            if c[i] < o[i]:
                E.entry("InsBarSE", -1)

    kc_ma, kc_atr = ema(c, 20), atr(h, l, c, 10)
    kc_up = lift(lambda m, a: m + 2 * a, kc_ma, kc_atr)
    kc_lo = lift(lambda m, a: m - 2 * a, kc_ma, kc_atr)
    kc_cu, kc_cl = crossover(c, kc_up), crossunder(c, kc_lo)
    kst = {"b": 0.0, "s": 0.0, "cb": False, "cs": False}

    @strategy("Keltner Channels Strategy")
    def _(i, E):
        if kc_ma[i] is None:
            return
        if kc_cu[i]:
            kst["b"], kst["cb"] = h[i] + mintick, True
        if kc_cl[i]:
            kst["s"], kst["cs"] = l[i] - mintick, True
        if kst["cb"] and (c[i] < kc_ma[i] or h[i] >= kst["b"]):
            E.cancel("KltChLE")
        if kc_cu[i]:
            E.entry("KltChLE", 1, stop=kst["b"])
        if kst["cs"] and (c[i] > kc_ma[i] or l[i] <= kst["s"]):
            E.cancel("KltChSE")
        if kc_cl[i]:
            E.entry("KltChSE", -1, stop=kst["s"])

    macd = lift(lambda a, b: a - b, ema(c, 12), ema(c, 26))
    delta = lift(lambda a, b: a - b, macd, ema(macd, 9))
    zero = const(0.0, n)
    m_up, m_dn = crossover(delta, zero), crossunder(delta, zero)

    @strategy("MACD Strategy")
    def _(i, E):
        if m_up[i]:
            E.entry("MacdLE", 1)
        if m_dn[i]:
            E.entry("MacdSE", -1)

    mom0 = change(c, 12)
    mom1 = change(mom0, 1)

    @strategy("Momentum Strategy")
    def _(i, E):
        if ok(mom0[i], mom1[i]) and mom0[i] > 0 and mom1[i] > 0:
            E.entry("MomLE", 1, stop=h[i] + mintick)
        else:
            E.cancel("MomLE")
        if ok(mom0[i], mom1[i]) and mom0[i] < 0 and mom1[i] < 0:
            E.entry("MomSE", -1, stop=l[i] - mintick)
        else:
            E.cancel("MomSE")

    ma9 = sma(c, 9)
    bcount, scount = [0] * n, [0] * n
    for i in range(n):
        p_b = bcount[i - 1] if i else 0
        p_s = scount[i - 1] if i else 0
        bcount[i] = p_b + 1 if ma9[i] is not None and c[i] > ma9[i] else 0
        scount[i] = p_s + 1 if ma9[i] is not None and c[i] < ma9[i] else 0

    @strategy("MovingAvg Cross")
    def _(i, E):
        if bcount[i] == 1:
            E.entry("MACrossLE", 1)
        if scount[i] == 1:
            E.entry("MACrossSE", -1)

    ma_f, ma_s = sma(c, 9), sma(c, 18)
    ma2_up, ma2_dn = crossover(ma_f, ma_s), crossunder(ma_f, ma_s)

    @strategy("MovingAvg2Line Cross")
    def _(i, E):
        if ma2_up[i]:
            E.entry("MA2CrossLE", 1)
        if ma2_dn[i]:
            E.entry("MA2CrossSE", -1)

    @strategy("OutSide Bar Strategy")
    def _(i, E):
        if i >= 1 and h[i] > h[i - 1] and l[i] < l[i - 1]:
            if c[i] > o[i]:
                E.entry("OutBarLE", 1)
            if c[i] < o[i]:
                E.entry("OutBarSE", -1)

    _, sar_below, sar_next = psar(h, l, c)

    @strategy("Parabolic SAR Strategy")
    def _(i, E):
        if sar_next[i] is None:
            return
        if sar_below[i]:
            E.entry("ParSE", -1, stop=sar_next[i])
            E.cancel("ParLE")
        else:
            E.entry("ParLE", 1, stop=sar_next[i])
            E.cancel("ParSE")

    ph, pl = pivot(h, 4, 2, True), pivot(l, 4, 2, False)

    @strategy("Pivot Extension Strategy")
    def _(i, E):
        if pl[i] is not None:
            E.entry("PivExtLE", 1)
        if ph[i] is not None:
            E.entry("PivExtSE", -1)

    pst = {"hp": 0.0, "le": False, "lp": 0.0, "se": False}

    @strategy("Pivot Reversal Strategy")
    def _(i, E):
        if ph[i] is not None:
            pst["hp"], pst["le"] = ph[i], True
        elif pst["le"] and h[i] > pst["hp"]:
            pst["le"] = False
        if pst["le"]:
            E.entry("PivRevLE", 1, stop=pst["hp"] + mintick)
        if pl[i] is not None:
            pst["lp"], pst["se"] = pl[i], True
        elif pst["se"] and l[i] < pst["lp"]:
            pst["se"] = False
        if pst["se"]:
            E.entry("PivRevSE", -1, stop=pst["lp"] - mintick)

    pc_hh, pc_ll = highest(h, 20), lowest(l, 20)

    @strategy("Price Channel Strategy")
    def _(i, E):
        if i >= 20 and ok(pc_hh[i], pc_ll[i]):
            E.entry("PChLE", 1, stop=pc_hh[i])
            E.entry("PChSE", -1, stop=pc_ll[i])

    r14 = rsi(c, 14)
    r_co, r_cu = crossover(r14, const(30.0, n)), crossunder(r14, const(70.0, n))

    @strategy("RSI Strategy")
    def _(i, E):
        if r_co[i]:
            E.entry("RsiLE", 1)
        if r_cu[i]:
            E.entry("RsiSE", -1)

    sk = sma(stoch(c, h, l, 14), 3)
    sd_ = sma(sk, 3)
    s_co, s_cu = crossover(sk, sd_), crossunder(sk, sd_)

    @strategy("Stochastic Slow Strategy")
    def _(i, E):
        if not ok(sk[i], sd_[i]):
            return
        if s_co[i] and sk[i] < 20:
            E.entry("StochLE", 1)
        if s_cu[i] and sk[i] > 80:
            E.entry("StochSE", -1)

    _, st_dir = supertrend(h, l, c, 3, 10)
    st_chg = change(st_dir)

    @strategy("SuperTrend Strategy")
    def _(i, E):
        if st_chg[i] is not None and st_chg[i] < 0:
            E.entry("My Long Entry Id", 1)
        if st_chg[i] is not None and st_chg[i] > 0:
            E.entry("My Short Entry Id", -1)

    vatrs = lift(lambda x: x * 0.75, sma(true_range(h, l, c, handle_na=False), 5))

    @strategy("Volty Expan Close Strategy")
    def _(i, E):
        if i >= 5 and vatrs[i] is not None:
            E.entry("VltClsLE", 1, stop=c[i] + vatrs[i])
            E.entry("VltClsSE", -1, stop=c[i] - vatrs[i])

    return S


# ----------------------------------------------------------------------------- output

def fmt_time(ms, offset_h):
    dt = datetime.fromtimestamp(ms / 1000, tz=timezone.utc) + timedelta(hours=offset_h)
    return dt.strftime("%Y-%m-%d %H:%M")


def r6(x):
    return "" if x is None else round(x, 8)


def safe_name(name):
    return "".join(ch if ch.isalnum() or ch in " -_." else "_" for ch in name).strip()


def summarize(name, E, d, start_i, end_i):
    trades = E.trades
    closed = [t for t in trades if t["status"] == "Closed"]
    wins = [t["profit"] for t in closed if t["profit"] > 0]
    losses = [t["profit"] for t in closed if t["profit"] <= 0]
    open_pnl = sum(t["profit"] for t in trades if t["status"] == "Open")
    net = sum(t["profit"] for t in closed)
    peak, mdd = -math.inf, 0.0
    for eq in E.equity_curve:
        peak = max(peak, eq)
        mdd = max(mdd, peak - eq)
    gl = abs(sum(losses))
    bh = (d["c"][end_i] / d["o"][start_i] - 1) * 100
    return {
        "Strategy": name,
        "Net Profit": round(net, 2),
        "Net Profit %": round(net / E.capital * 100, 2),
        "Open PnL": round(open_pnl, 2),
        "Gross Profit": round(sum(wins), 2),
        "Gross Loss": round(-gl, 2),
        "Profit Factor": round(sum(wins) / gl, 3) if gl else "",
        "Max Drawdown": round(mdd, 2),
        "Total Closed Trades": len(closed),
        "Winning Trades": len(wins),
        "Losing Trades": len(losses),
        "Percent Profitable": round(len(wins) / len(closed) * 100, 2) if closed else "",
        "Avg Trade": round(net / len(closed), 2) if closed else "",
        "Largest Win": round(max(wins), 2) if wins else "",
        "Largest Loss": round(min(losses), 2) if losses else "",
        "Final Equity": round(E.capital + net + open_pnl, 2),
        "Buy & Hold %": round(bh, 2),
    }


def read_watchlist(path):
    """One symbol per line, or a TradingView watchlist export
    ('###CRYPTO,BINANCE:BTCUSDT,###STOCKS,NASDAQ:AAPL,...')."""
    syms = []
    with open(path, encoding="utf-8-sig") as f:
        for line in f:
            s = line.strip()
            if s.startswith("#") and not s.startswith("###"):
                continue  # comment line
            for tok in s.split(","):
                tok = tok.strip()
                if tok and not tok.startswith("#") and tok not in syms:
                    syms.append(tok)
    return syms


def run_symbol(symbol, a, start_ms, end_ms):
    print(f"\n=== {symbol} {a.interval} ===")
    source, sym, d, mintick = load_symbol(symbol, a.interval, start_ms, end_ms, a.max_bars)
    if not d["t"]:
        raise RuntimeError("no candles returned - check symbol/interval/dates")
    start_i = next((i for i, t in enumerate(d["t"]) if t >= start_ms), None)
    if start_i is None:
        raise RuntimeError("no candles inside the requested date range")
    end_i = len(d["t"]) - 1
    start_i = max(start_i, end_i - a.max_bars + 1)
    if start_i < MIN_WARMUP and len(d["t"]) > 2 * MIN_WARMUP:
        start_i = MIN_WARMUP  # history starts late (e.g. Yahoo 1m = last 7 days): keep a warm-up
    print(f"  {source}: {len(d['t'])} candles ({start_i} warm-up), backtest "
          f"{fmt_time(d['t'][start_i], a.utc_offset)} -> {fmt_time(d['t'][end_i], a.utc_offset)}, tick {mintick:g}")

    root = os.path.join(a.out, f"{safe_name(sym)}_{a.interval}")
    ind_dir, st_dir = os.path.join(root, "indicators"), os.path.join(root, "strategies")
    os.makedirs(ind_dir, exist_ok=True)
    os.makedirs(st_dir, exist_ok=True)

    times = [fmt_time(t, a.utc_offset) for t in d["t"]]
    rng = range(start_i, end_i + 1)

    with open(os.path.join(root, "candles.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["time", "open", "high", "low", "close", "volume"])
        for i in rng:
            w.writerow([times[i], d["o"][i], d["h"][i], d["l"][i], d["c"][i], d["v"][i]])

    indicators = build_indicators(d)
    for name, cols in indicators.items():
        with open(os.path.join(ind_dir, safe_name(name) + ".csv"), "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["time", "open", "high", "low", "close", "volume"] + list(cols))
            for i in rng:
                w.writerow([times[i], d["o"][i], d["h"][i], d["l"][i], d["c"][i], d["v"][i]]
                           + [r6(s[i]) for s in cols.values()])
    print(f"  wrote {len(indicators)} indicator CSVs -> {ind_dir}")

    summary = []
    for name, strat in build_strategies(d, mintick).items():
        E = Engine(d, a.capital, a.pct, a.qty, a.commission, start_i, end_i)
        E.run(strat)
        cum_p = 0.0
        with open(os.path.join(st_dir, safe_name(name) + ".csv"), "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["Trade #", "Type", "Entry Signal", "Entry Time", "Entry Price", "Exit Signal",
                        "Exit Time", "Exit Price", "Qty", "Profit", "Profit %", "Cum Profit",
                        "Run-up", "Drawdown", "Bars", "Status"])
            for k, t in enumerate(E.trades, 1):
                cum_p += t["profit"]
                notional = t["qty"] * t["entry_px"]
                if t["dir"] > 0:
                    runup, dd = (t["hi"] - t["entry_px"]) * t["qty"], (t["entry_px"] - t["lo"]) * t["qty"]
                else:
                    runup, dd = (t["entry_px"] - t["lo"]) * t["qty"], (t["hi"] - t["entry_px"]) * t["qty"]
                w.writerow([k, "Long" if t["dir"] > 0 else "Short", t["entry_sig"], times[t["entry_i"]],
                            r6(t["entry_px"]), t["exit_sig"], times[t["exit_i"]], r6(t["exit_px"]),
                            round(t["qty"], 4), round(t["profit"], 2),
                            round(t["profit"] / notional * 100, 2), round(cum_p, 2),
                            round(runup, 2), round(-dd, 2), t["exit_i"] - t["entry_i"], t["status"]])
        summary.append(summarize(name, E, d, start_i, end_i))
        s = summary[-1]
        print(f"  {name:32s} net {s['Net Profit']:>12,.2f}  trades {s['Total Closed Trades']:>4}  "
              f"win% {s['Percent Profitable']}")

    with open(os.path.join(root, "strategies_summary.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(summary[0]))
        w.writeheader()
        w.writerows(summary)
    print(f"  wrote {len(summary)} strategy CSVs -> {st_dir}")
    return [{"Symbol": sym, "Interval": a.interval, "Source": source,
             "Backtest From": times[start_i], "Bars": end_i - start_i + 1, **s} for s in summary]


def write_rows(path, rows):
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--symbol", default="ADAUSDT", help="single symbol (ignored if --symbols/--watchlist)")
    ap.add_argument("--symbols", help="comma-separated symbols, e.g. BTCUSDT,AAPL,^GSPC,EURUSD=X")
    ap.add_argument("--watchlist", help="text file with one symbol per line (# comments allowed)")
    ap.add_argument("--interval", default="1h", choices=list(INTERVAL_MS))
    ap.add_argument("--intervals", help='comma-separated timeframes, or "all" for '
                                        + ",".join(TV_INTERVALS) + " (overrides --interval)")
    ap.add_argument("--max-bars", type=int, default=10000,
                    help="backtest at most the most recent N bars per run (default 10000)")
    ap.add_argument("--start", default="2026-01-01", help="backtest start date (UTC, YYYY-MM-DD)")
    ap.add_argument("--end", default=None, help="backtest end date (UTC, YYYY-MM-DD, default: now)")
    ap.add_argument("--capital", type=float, default=100_000)
    ap.add_argument("--pct", type=float, default=100, help="order size, %% of equity (default 100)")
    ap.add_argument("--qty", type=float, default=0, help="fixed order qty in units (overrides --pct)")
    ap.add_argument("--commission", type=float, default=0, help="commission %% per side")
    ap.add_argument("--utc-offset", type=float, default=0, help="hours added to timestamps in CSVs")
    ap.add_argument("--out", default="out")
    a = ap.parse_args()

    start_ms = int(datetime.strptime(a.start, "%Y-%m-%d").replace(tzinfo=timezone.utc).timestamp() * 1000)
    end_ms = (int(datetime.strptime(a.end, "%Y-%m-%d").replace(tzinfo=timezone.utc).timestamp() * 1000)
              if a.end else int(time.time() * 1000))

    if a.watchlist:
        symbols = read_watchlist(a.watchlist)
    elif a.symbols:
        symbols = [s.strip() for s in a.symbols.split(",") if s.strip()]
    else:
        symbols = [a.symbol]

    if a.intervals:
        intervals = TV_INTERVALS if a.intervals.lower() == "all" else [s.strip() for s in a.intervals.split(",")]
        bad = [iv for iv in intervals if iv not in INTERVAL_MS]
        if bad:
            raise SystemExit(f"unknown interval(s): {bad}; choose from {list(INTERVAL_MS)}")
    else:
        intervals = [a.interval]

    os.makedirs(a.out, exist_ok=True)
    every_row, failed, total = [], [], 0
    for interval in intervals:
        a.interval = interval
        tf_rows = []
        for symbol in symbols:
            total += 1
            free_mb = shutil.disk_usage(os.path.abspath(a.out)).free / 2**20
            if free_mb < MIN_FREE_DISK_MB:
                print(f"\nSTOPPED: only {free_mb:.0f} MB disk left. Free some space or lower --max-bars.")
                failed.append(f"{symbol}@{interval}")
                continue
            try:
                tf_rows += run_symbol(symbol, a, start_ms, end_ms)
            except Exception as e:
                print(f"  FAILED {symbol} {interval}: {e}")
                failed.append(f"{symbol}@{interval}")
        if tf_rows:
            path = os.path.join(a.out, f"all_symbols_summary_{interval}.csv")
            write_rows(path, tf_rows)
            print(f"\nSummary for {interval} ({len(tf_rows)} rows) -> {path}")
        every_row += tf_rows

    if len(intervals) > 1 and every_row:
        path = os.path.join(a.out, "all_symbols_all_timeframes_summary.csv")
        write_rows(path, every_row)
        print(f"Master summary ({len(every_row)} rows) -> {path}")
    print(f"Done: {total - len(failed)}/{total} symbol-timeframe runs OK"
          + (f", failed: {', '.join(failed)}" if failed else ""))


if __name__ == "__main__":
    main()
