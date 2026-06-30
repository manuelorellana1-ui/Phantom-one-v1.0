"""
phantom_backtest_v22_vs_v30.py — Backtest comparativo
Wino and Company · Jun 30, 2026

Compara:
  v2.2: Kijun TP → RSI(2) exit → ATR×3.0 SL (100% close)
  v3.0: Leg 1 (50%) Kijun/RSI(2) → Leg 2 (50%) Span B/RSI(14) div → ATR×3.0 SL

Uso:
  python phantom_backtest_v22_vs_v30.py

Datos: BingX public klines API (no requiere API key)
"""

import requests
import time
from typing import List, Dict, Optional
from dataclasses import dataclass, field
from datetime import datetime, timezone

# ══════════════════════════════════════════════════════════════════════════════
# CONFIG (idéntica a producción)
# ══════════════════════════════════════════════════════════════════════════════
PAIRS = ["BTC-USDT", "SOL-USDT", "ETH-USDT"]
KLINE_INTERVAL = "1h"
KLINE_LIMIT = 1000  # ~41 días de datos 1H

RSI_PERIOD = 2
RSI_OVERSOLD = 10
RSI_OVERBOUGHT = 90
RSI_EXIT_LONG = 60
RSI_EXIT_SHORT = 40
ZSCORE_THRESHOLD = 1.5
ZSCORE_PERIOD = 20
EMA_TREND_PERIOD = 50
ADX_PERIOD = 14
ADX_THRESHOLD = 40

KIJUN_PERIOD = 26
TENKAN_PERIOD = 9
KIJUN_GATE_ATR_MULT = 6.0
TK_CROSS_LOOKBACK = 5
ALERT_TIMEOUT_BARS = 48  # 48 bars = 48 hours en 1H

SENKOU_B_PERIOD = 52
KUMO_DISPLACEMENT = 26
LEG1_PCT = 0.50
RSI14_DIV_LOOKBACK = 20

ATR_SL_MULT = 3.0
LEVERAGE = 7
RISK_PCT = 0.15
MIN_CONFIDENCE = 30
TAKER_FEE = 0.0005

INITIAL_CAPITAL = 100.0  # backtesting con $100

# ══════════════════════════════════════════════════════════════════════════════
# INDICADORES (copiados textual de phantom.py — golden rule)
# ══════════════════════════════════════════════════════════════════════════════

def calc_rsi(closes: List[float], period: int = RSI_PERIOD) -> float:
    if len(closes) < period + 1:
        return 50.0
    deltas = [closes[i] - closes[i-1] for i in range(1, len(closes))]
    recent = deltas[-period:]
    gains = [max(d, 0) for d in recent]
    losses = [max(-d, 0) for d in recent]
    avg_gain = sum(gains) / period
    avg_loss = sum(losses) / period
    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    return 100 - (100 / (1 + rs))

def calc_ema(values: List[float], period: int) -> List[float]:
    if len(values) < period:
        return []
    k = 2 / (period + 1)
    ema = [sum(values[:period]) / period]
    for v in values[period:]:
        ema.append(v * k + ema[-1] * (1 - k))
    return ema

def calc_zscore(closes: List[float], period: int = ZSCORE_PERIOD) -> float:
    if len(closes) < period:
        return 0.0
    window = closes[-period:]
    mean = sum(window) / len(window)
    std = (sum((x - mean)**2 for x in window) / len(window)) ** 0.5
    if std == 0:
        return 0.0
    return (closes[-1] - mean) / std

def calc_atr(klines: List[dict], period: int = 14) -> float:
    if len(klines) < period + 1:
        return 0.0
    trs = []
    for i in range(1, len(klines)):
        h, l, pc = klines[i]["high"], klines[i]["low"], klines[i-1]["close"]
        trs.append(max(h - l, abs(h - pc), abs(l - pc)))
    return sum(trs[-period:]) / period

def calc_adx(klines: List[dict], period: int = ADX_PERIOD) -> float:
    if len(klines) < period * 2 + 1:
        return 0.0
    plus_dm, minus_dm, tr_list = [], [], []
    for i in range(1, len(klines)):
        h, l = klines[i]["high"], klines[i]["low"]
        ph, pl, pc = klines[i-1]["high"], klines[i-1]["low"], klines[i-1]["close"]
        up_move, down_move = h - ph, pl - l
        plus_dm.append(up_move if up_move > down_move and up_move > 0 else 0)
        minus_dm.append(down_move if down_move > up_move and down_move > 0 else 0)
        tr_list.append(max(h - l, abs(h - pc), abs(l - pc)))
    if len(tr_list) < period:
        return 0.0
    atr_s = sum(tr_list[:period])
    plus_s = sum(plus_dm[:period])
    minus_s = sum(minus_dm[:period])
    dx_list = []
    for i in range(period, len(tr_list)):
        atr_s = atr_s - (atr_s / period) + tr_list[i]
        plus_s = plus_s - (plus_s / period) + plus_dm[i]
        minus_s = minus_s - (minus_s / period) + minus_dm[i]
        if atr_s == 0:
            continue
        plus_di = 100 * plus_s / atr_s
        minus_di = 100 * minus_s / atr_s
        di_sum = plus_di + minus_di
        if di_sum == 0:
            continue
        dx_list.append(100 * abs(plus_di - minus_di) / di_sum)
    if len(dx_list) < period:
        return 0.0
    adx = sum(dx_list[:period]) / period
    for dx in dx_list[period:]:
        adx = (adx * (period - 1) + dx) / period
    return adx

def calc_kijun(klines: List[dict], period: int = KIJUN_PERIOD) -> float:
    if len(klines) < period:
        return 0.0
    recent = klines[-period:]
    return (max(k["high"] for k in recent) + min(k["low"] for k in recent)) / 2

def calc_tenkan(klines: List[dict], period: int = TENKAN_PERIOD) -> float:
    if len(klines) < period:
        return 0.0
    recent = klines[-period:]
    return (max(k["high"] for k in recent) + min(k["low"] for k in recent)) / 2

def calc_senkou_span_b(klines: List[dict], period: int = SENKOU_B_PERIOD) -> float:
    if len(klines) < period:
        return 0.0
    recent = klines[-period:]
    return (max(k["high"] for k in recent) + min(k["low"] for k in recent)) / 2

def calc_leading_span_b(klines: List[dict]) -> float:
    if len(klines) < SENKOU_B_PERIOD + KUMO_DISPLACEMENT:
        return 0.0
    past_klines = klines[:-KUMO_DISPLACEMENT]
    return calc_senkou_span_b(past_klines)

def calc_rsi14(closes: List[float]) -> float:
    period = 14
    if len(closes) < period + 1:
        return 50.0
    deltas = [closes[i] - closes[i-1] for i in range(1, len(closes))]
    avg_gain = sum(max(d, 0) for d in deltas[:period]) / period
    avg_loss = sum(abs(min(d, 0)) for d in deltas[:period]) / period
    for d in deltas[period:]:
        avg_gain = (avg_gain * (period - 1) + max(d, 0)) / period
        avg_loss = (avg_loss * (period - 1) + abs(min(d, 0))) / period
    if avg_loss == 0:
        return 100.0
    return 100 - (100 / (1 + avg_gain / avg_loss))

def detect_rsi14_divergence(closes: List[float], action: str) -> bool:
    lookback = RSI14_DIV_LOOKBACK
    if len(closes) < lookback + 14:
        return False
    rsi_vals = []
    for i in range(lookback):
        idx = len(closes) - lookback + i
        rsi_vals.append(calc_rsi14(closes[:idx + 1]))
    if len(rsi_vals) < 10:
        return False
    half = len(rsi_vals) // 2
    price_recent = closes[-half:]
    price_prior = closes[-(2 * half):-half]
    rsi_recent = rsi_vals[-half:]
    rsi_prior = rsi_vals[-2 * half:-half]
    if action == "BUY":
        return (max(price_recent) > max(price_prior) and
                max(rsi_recent) < max(rsi_prior) and
                max(rsi_recent) > 55)
    else:
        return (min(price_recent) < min(price_prior) and
                min(rsi_recent) > min(rsi_prior) and
                min(rsi_recent) < 45)


# ══════════════════════════════════════════════════════════════════════════════
# DATA FETCHING — BingX public API (no key needed)
# ══════════════════════════════════════════════════════════════════════════════

import random
import math

def generate_synthetic_klines(symbol: str, limit: int = 1000) -> List[dict]:
    """
    Generate realistic crypto klines with regime switching.
    Includes lateral (MR-friendly), trending, crash, and recovery phases.
    """
    random.seed(hash(symbol) % 2**32)
    base_prices = {"BTC-USDT": 65000.0, "SOL-USDT": 145.0, "ETH-USDT": 3400.0}
    price = base_prices.get(symbol, 1000.0)
    klines = []

    regime_schedule = []
    bars_left = limit
    while bars_left > 0:
        regime = random.choice(["lateral", "lateral", "trend_up", "trend_down", "crash", "recovery"])
        duration = min(random.randint(30, 120), bars_left)
        regime_schedule.append((regime, duration))
        bars_left -= duration

    bar_idx = 0
    for regime, duration in regime_schedule:
        for j in range(duration):
            params = {
                "lateral":    (random.gauss(0, 0.001),    random.uniform(0.005, 0.015)),
                "trend_up":   (random.gauss(0.002, 0.001), random.uniform(0.008, 0.02)),
                "trend_down": (random.gauss(-0.002, 0.001), random.uniform(0.008, 0.02)),
                "crash":      (random.gauss(-0.008, 0.003), random.uniform(0.015, 0.035)),
                "recovery":   (random.gauss(0.005, 0.002), random.uniform(0.01, 0.025)),
            }
            drift, vol = params.get(regime, (0, 0.01))
            ret = drift + random.gauss(0, vol)
            open_p = price
            close_p = open_p * (1 + ret)
            wick_up = abs(random.gauss(0, vol * 0.7))
            wick_dn = abs(random.gauss(0, vol * 0.7))
            high_p = max(open_p, close_p) * (1 + wick_up)
            low_p = min(open_p, close_p) * (1 - wick_dn)
            klines.append({
                "open": round(open_p, 2), "high": round(high_p, 2),
                "low": round(low_p, 2), "close": round(close_p, 2),
                "volume": round(random.uniform(100, 5000), 2), "time": bar_idx,
            })
            price = close_p
            bar_idx += 1
    print(f"  ✅ {symbol}: {len(klines)} synthetic klines generated")
    return klines


def fetch_klines(symbol: str, interval: str = KLINE_INTERVAL, limit: int = KLINE_LIMIT) -> List[dict]:
    """Fetch historical klines from BingX public API. Falls back to synthetic if blocked."""
    url = "https://open-api.bingx.com/openApi/swap/v3/quote/klines"
    params = {"symbol": symbol, "interval": interval, "limit": str(limit)}
    try:
        r = requests.get(url, params=params, timeout=15)
        data = r.json()
        if data.get("code") != 0:
            print(f"  ⚠️ {symbol}: API error, falling back to synthetic data")
            return generate_synthetic_klines(symbol, limit)
        raw = data.get("data", [])
        klines = []
        for k in raw:
            if isinstance(k, dict):
                klines.append({
                    "open": float(k.get("open", 0)),
                    "high": float(k.get("high", 0)),
                    "low": float(k.get("low", 0)),
                    "close": float(k.get("close", 0)),
                    "volume": float(k.get("volume", 0)),
                    "time": int(k.get("time", 0)),
                })
        print(f"  ✅ {symbol}: {len(klines)} klines fetched (LIVE)")
        return klines
    except Exception as e:
        print(f"  ⚠️ {symbol}: BingX blocked, using synthetic data")
        return generate_synthetic_klines(symbol, limit)


# ══════════════════════════════════════════════════════════════════════════════
# ENTRY DETECTION (shared for both versions)
# ══════════════════════════════════════════════════════════════════════════════

@dataclass
class Alert:
    action: str
    bar_idx: int
    price: float
    confidence: int

@dataclass
class Trade:
    action: str
    symbol: str
    entry_price: float
    entry_bar: int
    sl: float
    atr: float
    kijun_at_entry: float
    confidence: int


def detect_alert(klines: List[dict], bar_idx: int) -> Optional[Alert]:
    """Phase 1: detect mean-reversion extension. Identical for v2.2 and v3.0."""
    window = klines[:bar_idx + 1]
    if len(window) < max(200, EMA_TREND_PERIOD + 10):
        return None

    closes = [k["close"] for k in window]
    price = closes[-1]

    rsi = calc_rsi(closes, RSI_PERIOD)
    zscore = calc_zscore(closes, ZSCORE_PERIOD)
    adx = calc_adx(window, ADX_PERIOD)
    atr = calc_atr(window, 14)
    ema_vals = calc_ema(closes, EMA_TREND_PERIOD)
    kijun = calc_kijun(window)

    if not ema_vals:
        return None

    # ADX gate
    if adx >= ADX_THRESHOLD:
        return None

    # Signal
    action = None
    if rsi < RSI_OVERSOLD and zscore < -ZSCORE_THRESHOLD:
        action = "BUY"
    elif rsi > RSI_OVERBOUGHT and zscore > ZSCORE_THRESHOLD:
        action = "SELL"
    if not action:
        return None

    # Kijun gate (dynamic)
    if kijun > 0 and atr > 0:
        kijun_gate_pct = (atr * KIJUN_GATE_ATR_MULT) / price
        if action == "BUY":
            kijun_dist = (kijun - price) / kijun
            if kijun_dist > kijun_gate_pct:
                return None
        elif action == "SELL":
            kijun_dist = (price - kijun) / kijun
            if kijun_dist > kijun_gate_pct:
                return None

    # Confidence (simplified — same formula as production)
    ema_now = ema_vals[-1]
    with_trend = (action == "BUY" and price > ema_now) or (action == "SELL" and price < ema_now)
    if action == "BUY":
        rsi_score = max(0, min(30, (10 - rsi) / 10 * 30))
    else:
        rsi_score = max(0, min(30, (rsi - 90) / 10 * 30))
    z_score_pts = max(0, min(25, (abs(zscore) - 1.5) / 1.5 * 25))
    adx_score = max(0, min(20, (25 - adx) / 10 * 20))
    trend_score = 15 if with_trend else 5
    confidence = round(max(0, min(100, rsi_score + z_score_pts + adx_score + trend_score)))

    if confidence < MIN_CONFIDENCE:
        return None

    return Alert(action=action, bar_idx=bar_idx, price=price, confidence=confidence)


def check_tk_cross(klines: List[dict], bar_idx: int, action: str) -> bool:
    """Phase 2: check TK Cross confirmation with lookback."""
    window = klines[:bar_idx + 1]
    if len(window) < KIJUN_PERIOD + TK_CROSS_LOOKBACK + 1:
        return False

    for lb in range(1, TK_CROSS_LOOKBACK + 1):
        slice_curr = window[:-(lb - 1)] if lb > 1 else window
        slice_prev = window[:-lb]

        if len(slice_curr) < KIJUN_PERIOD or len(slice_prev) < KIJUN_PERIOD:
            continue

        t_now = calc_tenkan(slice_curr)
        k_now = calc_kijun(slice_curr)
        t_prev = calc_tenkan(slice_prev)
        k_prev = calc_kijun(slice_prev)

        if t_now <= 0 or k_now <= 0 or t_prev <= 0 or k_prev <= 0:
            continue

        if action == "BUY" and t_prev <= k_prev and t_now > k_now:
            return True
        elif action == "SELL" and t_prev >= k_prev and t_now < k_now:
            return True

    return False


def recheck_kijun_gate(klines: List[dict], bar_idx: int, action: str) -> bool:
    """Re-check Kijun gate at confirmation time. Returns True if BLOCKED."""
    window = klines[:bar_idx + 1]
    price = window[-1]["close"]
    kijun = calc_kijun(window)
    atr = calc_atr(window)
    if kijun <= 0 or atr <= 0:
        return False
    kijun_gate_pct = (atr * KIJUN_GATE_ATR_MULT) / price
    if action == "BUY":
        return (kijun - price) / kijun > kijun_gate_pct
    else:
        return (price - kijun) / kijun > kijun_gate_pct


# ══════════════════════════════════════════════════════════════════════════════
# TRADE SIMULATION
# ══════════════════════════════════════════════════════════════════════════════

@dataclass
class TradeResult:
    symbol: str
    action: str
    entry_price: float
    entry_bar: int
    exit_price: float
    exit_bar: int
    exit_reason: str
    pnl_usd: float
    pnl_pct: float
    margin: float
    bars_held: int
    # v3.0 extras
    leg1_exit_price: float = 0.0
    leg1_exit_bar: int = 0
    leg1_reason: str = ""
    leg1_pnl: float = 0.0
    leg2_exit_price: float = 0.0
    leg2_exit_bar: int = 0
    leg2_reason: str = ""
    leg2_pnl: float = 0.0


def simulate_v22(trade: Trade, klines: List[dict]) -> Optional[TradeResult]:
    """v2.2 exit: Kijun TP → RSI(2) exit → ATR×3.0 SL. 100% close."""
    entry = trade.entry_price
    sl = trade.sl
    margin = INITIAL_CAPITAL * RISK_PCT  # simplified, doesn't compound in backtest
    notional = margin * LEVERAGE
    qty = notional / entry

    for i in range(trade.entry_bar + 1, len(klines)):
        window = klines[:i + 1]
        closes = [k["close"] for k in window]
        price = closes[-1]
        bar_low = klines[i]["low"]
        bar_high = klines[i]["high"]

        # SL check (intra-bar)
        if trade.action == "BUY" and bar_low <= sl:
            exit_p = sl
            raw_pnl = (exit_p - entry) * qty
            fee = (entry * qty + exit_p * qty) * TAKER_FEE
            pnl = raw_pnl - fee
            return TradeResult(
                symbol=trade.symbol, action=trade.action, entry_price=entry,
                entry_bar=trade.entry_bar, exit_price=exit_p, exit_bar=i,
                exit_reason="SL", pnl_usd=pnl, pnl_pct=pnl/margin*100,
                margin=margin, bars_held=i - trade.entry_bar
            )
        if trade.action == "SELL" and bar_high >= sl:
            exit_p = sl
            raw_pnl = (entry - exit_p) * qty
            fee = (entry * qty + exit_p * qty) * TAKER_FEE
            pnl = raw_pnl - fee
            return TradeResult(
                symbol=trade.symbol, action=trade.action, entry_price=entry,
                entry_bar=trade.entry_bar, exit_price=exit_p, exit_bar=i,
                exit_reason="SL", pnl_usd=pnl, pnl_pct=pnl/margin*100,
                margin=margin, bars_held=i - trade.entry_bar
            )

        # Kijun TP
        kijun = calc_kijun(window)
        if kijun > 0:
            if trade.action == "BUY" and price >= kijun and kijun > entry:
                exit_p = price
                raw_pnl = (exit_p - entry) * qty
                fee = (entry * qty + exit_p * qty) * TAKER_FEE
                pnl = raw_pnl - fee
                return TradeResult(
                    symbol=trade.symbol, action=trade.action, entry_price=entry,
                    entry_bar=trade.entry_bar, exit_price=exit_p, exit_bar=i,
                    exit_reason="KIJUN_TP", pnl_usd=pnl, pnl_pct=pnl/margin*100,
                    margin=margin, bars_held=i - trade.entry_bar
                )
            if trade.action == "SELL" and price <= kijun and kijun < entry:
                exit_p = price
                raw_pnl = (entry - exit_p) * qty
                fee = (entry * qty + exit_p * qty) * TAKER_FEE
                pnl = raw_pnl - fee
                return TradeResult(
                    symbol=trade.symbol, action=trade.action, entry_price=entry,
                    entry_bar=trade.entry_bar, exit_price=exit_p, exit_bar=i,
                    exit_reason="KIJUN_TP", pnl_usd=pnl, pnl_pct=pnl/margin*100,
                    margin=margin, bars_held=i - trade.entry_bar
                )

        # RSI exit
        rsi = calc_rsi(closes, RSI_PERIOD)
        if trade.action == "BUY" and rsi > RSI_EXIT_LONG:
            exit_p = price
            raw_pnl = (exit_p - entry) * qty
            fee = (entry * qty + exit_p * qty) * TAKER_FEE
            pnl = raw_pnl - fee
            return TradeResult(
                symbol=trade.symbol, action=trade.action, entry_price=entry,
                entry_bar=trade.entry_bar, exit_price=exit_p, exit_bar=i,
                exit_reason="RSI_EXIT", pnl_usd=pnl, pnl_pct=pnl/margin*100,
                margin=margin, bars_held=i - trade.entry_bar
            )
        if trade.action == "SELL" and rsi < RSI_EXIT_SHORT:
            exit_p = price
            raw_pnl = (entry - exit_p) * qty
            fee = (entry * qty + exit_p * qty) * TAKER_FEE
            pnl = raw_pnl - fee
            return TradeResult(
                symbol=trade.symbol, action=trade.action, entry_price=entry,
                entry_bar=trade.entry_bar, exit_price=exit_p, exit_bar=i,
                exit_reason="RSI_EXIT", pnl_usd=pnl, pnl_pct=pnl/margin*100,
                margin=margin, bars_held=i - trade.entry_bar
            )

    return None  # trade still open at end of data


def simulate_v30(trade: Trade, klines: List[dict]) -> Optional[TradeResult]:
    """
    v3.0 exit: Two-leg system.
    Leg 1 (50%): Kijun TP → RSI(2) exit
    Leg 2 (50%): Leading Span B TP → RSI(14) divergence
    SL: ATR×3.0 (original, never changes) — closes ALL remaining
    """
    entry = trade.entry_price
    sl = trade.sl  # original_sl, never changes
    margin = INITIAL_CAPITAL * RISK_PCT
    notional = margin * LEVERAGE
    qty = notional / entry
    leg1_qty = qty * LEG1_PCT
    leg2_qty = qty - leg1_qty

    leg1_closed = False
    leg1_exit_price = 0.0
    leg1_exit_bar = 0
    leg1_reason = ""
    leg1_pnl = 0.0

    for i in range(trade.entry_bar + 1, len(klines)):
        window = klines[:i + 1]
        closes = [k["close"] for k in window]
        price = closes[-1]
        bar_low = klines[i]["low"]
        bar_high = klines[i]["high"]

        # ── SL check (closes ALL remaining) ──
        sl_hit = False
        if trade.action == "BUY" and bar_low <= sl:
            sl_hit = True
            exit_p = sl
        elif trade.action == "SELL" and bar_high >= sl:
            sl_hit = True
            exit_p = sl

        if sl_hit:
            remaining_qty = leg2_qty if leg1_closed else qty
            if trade.action == "BUY":
                raw_pnl = (exit_p - entry) * remaining_qty
            else:
                raw_pnl = (entry - exit_p) * remaining_qty
            fee = (entry * remaining_qty + exit_p * remaining_qty) * TAKER_FEE
            sl_pnl = raw_pnl - fee
            total_pnl = leg1_pnl + sl_pnl

            return TradeResult(
                symbol=trade.symbol, action=trade.action, entry_price=entry,
                entry_bar=trade.entry_bar, exit_price=exit_p, exit_bar=i,
                exit_reason="SL" if not leg1_closed else "LEG2_SL",
                pnl_usd=total_pnl, pnl_pct=total_pnl/margin*100,
                margin=margin, bars_held=i - trade.entry_bar,
                leg1_exit_price=leg1_exit_price, leg1_exit_bar=leg1_exit_bar,
                leg1_reason=leg1_reason, leg1_pnl=leg1_pnl,
                leg2_exit_price=exit_p, leg2_exit_bar=i,
                leg2_reason="SL", leg2_pnl=sl_pnl,
            )

        # ════════════════════════════════════════
        # LEG 1: Kijun TP → RSI(2) exit
        # ════════════════════════════════════════
        if not leg1_closed:
            leg1_exit = False
            leg1_r = ""

            kijun = calc_kijun(window)
            if kijun > 0:
                if trade.action == "BUY" and price >= kijun and kijun > entry:
                    leg1_exit = True
                    leg1_r = "KIJUN_TP"
                elif trade.action == "SELL" and price <= kijun and kijun < entry:
                    leg1_exit = True
                    leg1_r = "KIJUN_TP"

            if not leg1_exit:
                rsi = calc_rsi(closes, RSI_PERIOD)
                if trade.action == "BUY" and rsi > RSI_EXIT_LONG:
                    leg1_exit = True
                    leg1_r = "RSI_EXIT"
                elif trade.action == "SELL" and rsi < RSI_EXIT_SHORT:
                    leg1_exit = True
                    leg1_r = "RSI_EXIT"

            if leg1_exit:
                leg1_closed = True
                leg1_exit_price = price
                leg1_exit_bar = i
                leg1_reason = leg1_r
                if trade.action == "BUY":
                    raw = (price - entry) * leg1_qty
                else:
                    raw = (entry - price) * leg1_qty
                fee = (entry * leg1_qty + price * leg1_qty) * TAKER_FEE
                leg1_pnl = raw - fee
                continue

        # ════════════════════════════════════════
        # LEG 2: Span B TP → RSI(14) divergence
        # ════════════════════════════════════════
        if leg1_closed:
            # Leading Span B TP
            leading_b = calc_leading_span_b(window)
            if leading_b > 0:
                if trade.action == "BUY" and price >= leading_b and leading_b > entry:
                    if trade.action == "BUY":
                        raw = (price - entry) * leg2_qty
                    else:
                        raw = (entry - price) * leg2_qty
                    fee = (entry * leg2_qty + price * leg2_qty) * TAKER_FEE
                    leg2_pnl = raw - fee
                    total_pnl = leg1_pnl + leg2_pnl
                    return TradeResult(
                        symbol=trade.symbol, action=trade.action, entry_price=entry,
                        entry_bar=trade.entry_bar, exit_price=price, exit_bar=i,
                        exit_reason="LEG2_SPAN_B_TP", pnl_usd=total_pnl,
                        pnl_pct=total_pnl/margin*100, margin=margin,
                        bars_held=i - trade.entry_bar,
                        leg1_exit_price=leg1_exit_price, leg1_exit_bar=leg1_exit_bar,
                        leg1_reason=leg1_reason, leg1_pnl=leg1_pnl,
                        leg2_exit_price=price, leg2_exit_bar=i,
                        leg2_reason="SPAN_B_TP", leg2_pnl=leg2_pnl,
                    )
                elif trade.action == "SELL" and price <= leading_b and leading_b < entry:
                    raw = (entry - price) * leg2_qty
                    fee = (entry * leg2_qty + price * leg2_qty) * TAKER_FEE
                    leg2_pnl = raw - fee
                    total_pnl = leg1_pnl + leg2_pnl
                    return TradeResult(
                        symbol=trade.symbol, action=trade.action, entry_price=entry,
                        entry_bar=trade.entry_bar, exit_price=price, exit_bar=i,
                        exit_reason="LEG2_SPAN_B_TP", pnl_usd=total_pnl,
                        pnl_pct=total_pnl/margin*100, margin=margin,
                        bars_held=i - trade.entry_bar,
                        leg1_exit_price=leg1_exit_price, leg1_exit_bar=leg1_exit_bar,
                        leg1_reason=leg1_reason, leg1_pnl=leg1_pnl,
                        leg2_exit_price=price, leg2_exit_bar=i,
                        leg2_reason="SPAN_B_TP", leg2_pnl=leg2_pnl,
                    )

            # RSI(14) divergence
            if len(closes) > RSI14_DIV_LOOKBACK + 14:
                if detect_rsi14_divergence(closes, trade.action):
                    if trade.action == "BUY":
                        raw = (price - entry) * leg2_qty
                    else:
                        raw = (entry - price) * leg2_qty
                    fee = (entry * leg2_qty + price * leg2_qty) * TAKER_FEE
                    leg2_pnl = raw - fee
                    total_pnl = leg1_pnl + leg2_pnl
                    return TradeResult(
                        symbol=trade.symbol, action=trade.action, entry_price=entry,
                        entry_bar=trade.entry_bar, exit_price=price, exit_bar=i,
                        exit_reason="LEG2_RSI14_DIV", pnl_usd=total_pnl,
                        pnl_pct=total_pnl/margin*100, margin=margin,
                        bars_held=i - trade.entry_bar,
                        leg1_exit_price=leg1_exit_price, leg1_exit_bar=leg1_exit_bar,
                        leg1_reason=leg1_reason, leg1_pnl=leg1_pnl,
                        leg2_exit_price=price, leg2_exit_bar=i,
                        leg2_reason="RSI14_DIV", leg2_pnl=leg2_pnl,
                    )

    return None  # trade still open


# ══════════════════════════════════════════════════════════════════════════════
# BACKTEST ENGINE
# ══════════════════════════════════════════════════════════════════════════════

def run_backtest(symbol: str, klines: List[dict]) -> dict:
    """Run backtest for both v2.2 and v3.0 on same entries."""
    print(f"\n{'═' * 60}")
    print(f"  BACKTEST: {symbol} | {len(klines)} bars")
    print(f"{'═' * 60}")

    warmup = 200  # need enough bars for indicators
    entries: List[Trade] = []
    pending_alert: Optional[Alert] = None

    # ── Find all entries (shared between both versions) ──
    for i in range(warmup, len(klines)):
        # Check pending alert for TK Cross confirmation
        if pending_alert:
            elapsed = i - pending_alert.bar_idx
            if elapsed > ALERT_TIMEOUT_BARS:
                pending_alert = None
            elif check_tk_cross(klines, i, pending_alert.action):
                # Re-check Kijun gate at confirmation
                if not recheck_kijun_gate(klines, i, pending_alert.action):
                    window = klines[:i + 1]
                    price = window[-1]["close"]
                    atr = calc_atr(window)
                    kijun = calc_kijun(window)
                    if pending_alert.action == "BUY":
                        sl = price - atr * ATR_SL_MULT
                    else:
                        sl = price + atr * ATR_SL_MULT
                    entries.append(Trade(
                        action=pending_alert.action, symbol=symbol,
                        entry_price=price, entry_bar=i, sl=sl,
                        atr=atr, kijun_at_entry=kijun,
                        confidence=pending_alert.confidence
                    ))
                pending_alert = None
            continue

        # Check for new alert
        alert = detect_alert(klines, i)
        if alert:
            pending_alert = alert

    print(f"  Entries found: {len(entries)}")
    if not entries:
        return {"symbol": symbol, "entries": 0}

    # ── Simulate both versions ──
    v22_results: List[TradeResult] = []
    v30_results: List[TradeResult] = []

    for trade in entries:
        r22 = simulate_v22(trade, klines)
        r30 = simulate_v30(trade, klines)
        if r22:
            v22_results.append(r22)
        if r30:
            v30_results.append(r30)

    # ── Print trade-by-trade comparison ──
    print(f"\n  {'─' * 56}")
    print(f"  {'TRADE-BY-TRADE COMPARISON':^56}")
    print(f"  {'─' * 56}")
    print(f"  {'#':>3} {'Action':>5} {'Entry':>10} {'v2.2 PnL%':>10} {'v2.2 Exit':>10} {'v3.0 PnL%':>10} {'v3.0 Exit':>12}")
    print(f"  {'─' * 56}")

    for idx, trade in enumerate(entries):
        r22 = v22_results[idx] if idx < len(v22_results) else None
        r30 = v30_results[idx] if idx < len(v30_results) else None

        v22_pnl_str = f"{r22.pnl_pct:+.2f}%" if r22 else "OPEN"
        v22_exit_str = r22.exit_reason if r22 else "—"
        v30_pnl_str = f"{r30.pnl_pct:+.2f}%" if r30 else "OPEN"
        v30_exit_str = r30.exit_reason[:12] if r30 else "—"

        print(f"  {idx+1:>3} {trade.action:>5} ${trade.entry_price:>9,.2f} {v22_pnl_str:>10} {v22_exit_str:>10} {v30_pnl_str:>10} {v30_exit_str:>12}")

        # v3.0 leg detail
        if r30 and r30.leg1_reason:
            print(f"      └─ L1: {r30.leg1_reason} pnl=${r30.leg1_pnl:+.4f} | L2: {r30.leg2_reason} pnl=${r30.leg2_pnl:+.4f}")

    # ── Summary stats ──
    def calc_stats(results: List[TradeResult], label: str) -> dict:
        if not results:
            return {}
        wins = [r for r in results if r.pnl_usd > 0]
        losses = [r for r in results if r.pnl_usd <= 0]
        total_pnl = sum(r.pnl_usd for r in results)
        gross_profit = sum(r.pnl_usd for r in wins) if wins else 0
        gross_loss = abs(sum(r.pnl_usd for r in losses)) if losses else 0.001
        pf = gross_profit / gross_loss if gross_loss > 0 else float('inf')
        avg_win = sum(r.pnl_pct for r in wins) / len(wins) if wins else 0
        avg_loss = sum(r.pnl_pct for r in losses) / len(losses) if losses else 0
        avg_bars = sum(r.bars_held for r in results) / len(results)

        stats = {
            "label": label,
            "trades": len(results),
            "wins": len(wins),
            "wr": len(wins) / len(results) * 100,
            "total_pnl": total_pnl,
            "profit_factor": pf,
            "avg_win_pct": avg_win,
            "avg_loss_pct": avg_loss,
            "avg_bars": avg_bars,
            "max_win": max(r.pnl_pct for r in results),
            "max_loss": min(r.pnl_pct for r in results),
        }
        return stats

    s22 = calc_stats(v22_results, "v2.2")
    s30 = calc_stats(v30_results, "v3.0")

    if s22 and s30:
        print(f"\n  {'═' * 56}")
        print(f"  {'SUMMARY':^56}")
        print(f"  {'═' * 56}")
        print(f"  {'Metric':<20} {'v2.2':>15} {'v3.0':>15}")
        print(f"  {'─' * 56}")
        print(f"  {'Trades':<20} {s22['trades']:>15} {s30['trades']:>15}")
        print(f"  {'Win Rate':<20} {s22['wr']:>14.1f}% {s30['wr']:>14.1f}%")
        print(f"  {'Profit Factor':<20} {s22['profit_factor']:>15.2f} {s30['profit_factor']:>15.2f}")
        print(f"  {'Total PnL ($)':<20} {s22['total_pnl']:>+15.4f} {s30['total_pnl']:>+15.4f}")
        print(f"  {'Avg Win %':<20} {s22['avg_win_pct']:>+14.2f}% {s30['avg_win_pct']:>+14.2f}%")
        print(f"  {'Avg Loss %':<20} {s22['avg_loss_pct']:>+14.2f}% {s30['avg_loss_pct']:>+14.2f}%")
        print(f"  {'Avg Bars Held':<20} {s22['avg_bars']:>15.1f} {s30['avg_bars']:>15.1f}")
        print(f"  {'Max Win %':<20} {s22['max_win']:>+14.2f}% {s30['max_win']:>+14.2f}%")
        print(f"  {'Max Loss %':<20} {s22['max_loss']:>+14.2f}% {s30['max_loss']:>+14.2f}%")
        print(f"  {'═' * 56}")

        # ── v3.0 exit breakdown ──
        if v30_results:
            reasons = {}
            for r in v30_results:
                reasons[r.exit_reason] = reasons.get(r.exit_reason, 0) + 1
            print(f"\n  v3.0 Exit Breakdown:")
            for reason, count in sorted(reasons.items()):
                subset = [r for r in v30_results if r.exit_reason == reason]
                avg_pnl = sum(r.pnl_pct for r in subset) / len(subset)
                print(f"    {reason:<20} {count:>3} trades  avg pnl={avg_pnl:+.2f}%")

    return {"symbol": symbol, "entries": len(entries), "v22": s22, "v30": s30}


# ══════════════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════════════

def main():
    print("=" * 60)
    print("  PHANTOM BACKTEST — v2.2 vs v3.0")
    print(f"  Data: BingX {KLINE_INTERVAL} klines × {KLINE_LIMIT}")
    print(f"  Capital: ${INITIAL_CAPITAL} | Lev: {LEVERAGE}x | Risk: {RISK_PCT*100}%")
    print("=" * 60)

    print("\n📡 Fetching data...")
    all_results = []

    for symbol in PAIRS:
        klines = fetch_klines(symbol)
        if len(klines) < 300:
            print(f"  ⚠️ {symbol}: insufficient data ({len(klines)} bars), skipping")
            continue
        time.sleep(0.5)
        result = run_backtest(symbol, klines)
        all_results.append(result)

    # ── AGGREGATE ──
    print(f"\n{'═' * 60}")
    print(f"  AGGREGATE RESULTS (all pairs)")
    print(f"{'═' * 60}")

    total_entries = sum(r["entries"] for r in all_results)
    if total_entries == 0:
        print("  ⚠️ No trades found across any pair.")
        print("  This is expected if the 1000-bar window has no mean-reversion signals.")
        print("  Consider: market has been trending (ADX>40) or RSI(2) never hit <10/>90.")
        return

    # Aggregate v22
    all_v22 = [r["v22"] for r in all_results if r.get("v22")]
    all_v30 = [r["v30"] for r in all_results if r.get("v30")]

    if all_v22 and all_v30:
        def agg(stats_list):
            total_trades = sum(s["trades"] for s in stats_list)
            total_wins = sum(s["wins"] for s in stats_list)
            total_pnl = sum(s["total_pnl"] for s in stats_list)
            return {
                "trades": total_trades,
                "wr": total_wins / total_trades * 100 if total_trades > 0 else 0,
                "total_pnl": total_pnl,
            }

        a22 = agg(all_v22)
        a30 = agg(all_v30)

        print(f"  {'Metric':<20} {'v2.2':>15} {'v3.0':>15}")
        print(f"  {'─' * 56}")
        print(f"  {'Total Trades':<20} {a22['trades']:>15} {a30['trades']:>15}")
        print(f"  {'Win Rate':<20} {a22['wr']:>14.1f}% {a30['wr']:>14.1f}%")
        print(f"  {'Total PnL ($)':<20} {a22['total_pnl']:>+15.4f} {a30['total_pnl']:>+15.4f}")
        delta = a30['total_pnl'] - a22['total_pnl']
        print(f"  {'─' * 56}")
        print(f"  v3.0 vs v2.2 delta: ${delta:+.4f}")
        if delta > 0:
            print(f"  ✅ v3.0 outperforms v2.2 by ${delta:.4f}")
        elif delta < 0:
            print(f"  ❌ v2.2 outperforms v3.0 by ${abs(delta):.4f}")
        else:
            print(f"  ➡️ Equal performance")

    print(f"\n{'═' * 60}")
    print(f"  BACKTEST COMPLETE")
    print(f"{'═' * 60}")


if __name__ == "__main__":
    main()
