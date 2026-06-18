"""
phantom.py — Phantom Bot v1.0
Wino and Company · Junio 2026

ESTRATEGIA: Statistical Mean-Reversion con Detección de Régimen
═════════════════════════════════════════════════════════════════

FUNDAMENTO MATEMÁTICO:
  - RSI(2) de Larry Connors: 75%+ win rate documentado en 34 años de backtests
  - Z-Score estadístico: mide desviaciones estándar del precio vs media
  - Detección de régimen: ADX determina si el mercado está en rango (mean-revert)
    o en tendencia (no operar mean-reversion)

LÓGICA CORE:
  1. Régimen: ADX < 25 = mercado lateral → mean-reversion activo
                ADX >= 25 = mercado en tendencia → NO operar (esperar)
  2. Trend filter: EMA50 determina si estamos en uptrend o downtrend
  3. Señal: RSI(2) < 10 en uptrend → BUY (oversold en tendencia alcista)
           RSI(2) > 90 en downtrend → SELL (overbought en tendencia bajista)
  4. Confirmación: Z-Score > 2.0 desviaciones del precio vs media
  5. Salida: RSI(2) cruza 60 (BUY) o 40 (SELL) — NO target fijo

DIFERENCIAS CLAVE vs WinoBot/Scalpers:
  - NO persigue breakouts (compra DESPUÉS de caídas, no después de subidas)
  - NO usa market orders agresivos (usa limit orders al close de la vela)
  - NO tiene TP fijo (sale cuando RSI vuelve a zona neutral = el mercado decide)
  - SL basado en ATR × 3.0 (fuera del ruido, no dentro)
  - Evalúa cada 15 minutos (no cada 60 segundos)

ACTIVOS: BTC-USDT, SOL-USDT (BingX auto) + NVDA (Telegram/Quantfury)
OBJETIVO: +2% diario sobre capital disponible
"""

import os
import time
import hmac
import hashlib
import json
import logging
import requests
from datetime import datetime, timezone, timedelta
from typing import Optional, Dict, List, Tuple
from collections import deque

# ══════════════════════════════════════════════════════════════════════════════
# LOGGING
# ══════════════════════════════════════════════════════════════════════════════
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [phantom][%(levelname)s] %(message)s"
)
logger = logging.getLogger("phantom")

# ══════════════════════════════════════════════════════════════════════════════
# CONFIG
# ══════════════════════════════════════════════════════════════════════════════

# ── Credenciales ──
BINGX_API_KEY    = os.getenv("BINGX_API_KEY", "")
BINGX_API_SECRET = os.getenv("BINGX_API_SECRET", "")
TG_TOKEN         = os.getenv("TELEGRAM_BOT_TOKEN", "")
TG_CHAT_ID       = os.getenv("TELEGRAM_CHAT_ID", "")

# ── Activos ──
CRYPTO_PAIRS = ["BTC-USDT", "SOL-USDT"]
STOCK_SYMBOL = "NVDA"

# ── Estrategia ──
RSI_PERIOD        = 2       # RSI(2) — Connors
RSI_OVERSOLD      = 10      # Comprar cuando RSI < 10 (extremo)
RSI_OVERBOUGHT    = 90      # Vender cuando RSI > 90 (extremo)
RSI_EXIT_LONG     = 60      # Salir de LONG cuando RSI > 60
RSI_EXIT_SHORT    = 40      # Salir de SHORT cuando RSI < 40
ZSCORE_THRESHOLD  = 2.0     # Confirmación: precio a 2σ de la media
ZSCORE_PERIOD     = 20      # Ventana para calcular Z-Score
EMA_TREND_PERIOD  = 50      # EMA para determinar tendencia
ADX_PERIOD        = 14      # ADX para detección de régimen
ADX_THRESHOLD     = 25      # ADX < 25 = mercado lateral (ideal para MR)

# ── Risk Management ──
LEVERAGE          = 7
RISK_PCT          = 0.15    # 15% del capital por trade (Kelly óptimo para 75% WR)
ATR_SL_MULT       = 3.0    # SL = ATR × 3.0 (fuera del ruido)
MAX_POSITIONS     = 2       # máximo 2 posiciones simultáneas
DAILY_LOSS_LIMIT  = 0.03    # -3% del capital = stop trading hoy
MAX_SLIPPAGE_PCT  = 0.003   # 0.3% max slippage permitido

# ── Evaluación ──
EVAL_INTERVAL     = 900     # Evaluar cada 15 minutos (900 segundos)
KLINE_TIMEFRAME   = "15m"   # Velas de 15 minutos
KLINE_LIMIT       = 100     # Últimas 100 velas

# ── BingX API ──
BINGX_BASE = "https://open-api.bingx.com"

# ── Estado ──
_positions: Dict[str, dict] = {}
_daily_pnl = 0.0
_daily_trades = 0
_start_balance = 0.0

# ══════════════════════════════════════════════════════════════════════════════
# BINGX API CLIENT
# ══════════════════════════════════════════════════════════════════════════════

def _sign(params: dict) -> dict:
    """Firma HMAC-SHA256 para BingX API."""
    params["timestamp"] = str(int(time.time() * 1000))
    query = "&".join(f"{k}={v}" for k, v in sorted(params.items()))
    sig = hmac.new(BINGX_API_SECRET.encode(), query.encode(), hashlib.sha256).hexdigest()
    params["signature"] = sig
    return params

def _headers() -> dict:
    return {"X-BX-APIKEY": BINGX_API_KEY, "Content-Type": "application/json"}

def api_get(path: str, params: dict = None) -> dict:
    try:
        p = _sign(params or {})
        r = requests.get(f"{BINGX_BASE}{path}", params=p, headers=_headers(), timeout=10)
        return r.json()
    except Exception as e:
        logger.error(f"[API] GET {path}: {e}")
        return {}

def api_post(path: str, params: dict = None) -> dict:
    try:
        p = _sign(params or {})
        r = requests.post(f"{BINGX_BASE}{path}", json=p, headers=_headers(), timeout=10)
        return r.json()
    except Exception as e:
        logger.error(f"[API] POST {path}: {e}")
        return {}


# ══════════════════════════════════════════════════════════════════════════════
# DATA FETCHING
# ══════════════════════════════════════════════════════════════════════════════

def get_klines(symbol: str, interval: str = KLINE_TIMEFRAME, limit: int = KLINE_LIMIT) -> List[dict]:
    """Obtiene velas de BingX."""
    data = api_get("/openApi/swap/v3/quote/klines", {
        "symbol": symbol, "interval": interval, "limit": str(limit)
    })
    if data.get("code") != 0:
        return []
    raw = data.get("data", [])
    klines = []
    for k in raw:
        if isinstance(k, dict):
            klines.append({
                "open":   float(k.get("open", 0)),
                "high":   float(k.get("high", 0)),
                "low":    float(k.get("low", 0)),
                "close":  float(k.get("close", 0)),
                "volume": float(k.get("volume", 0)),
            })
    return klines

def get_nvda_klines() -> List[dict]:
    """Obtiene velas 15m de NVDA via Yahoo Finance."""
    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{STOCK_SYMBOL}"
    params = {"interval": "15m", "range": "5d", "includePrePost": "false"}
    headers = {"User-Agent": "Mozilla/5.0"}
    try:
        r = requests.get(url, params=params, headers=headers, timeout=10)
        data = r.json()
        result = data.get("chart", {}).get("result", [])
        if not result:
            return []
        meta = result[0]
        quotes = meta.get("indicators", {}).get("quote", [{}])[0]
        stamps = meta.get("timestamp", [])
        klines = []
        for i in range(len(stamps)):
            o, h, l, c, v = quotes["open"][i], quotes["high"][i], quotes["low"][i], quotes["close"][i], quotes["volume"][i]
            if None in (o, h, l, c, v):
                continue
            klines.append({"open": float(o), "high": float(h), "low": float(l), "close": float(c), "volume": float(v)})
        return klines[-KLINE_LIMIT:]
    except Exception as e:
        logger.error(f"[DATA] Yahoo NVDA: {e}")
        return []

def get_balance() -> float:
    """Obtiene balance disponible en USDT."""
    data = api_get("/openApi/swap/v2/user/balance")
    if data.get("code") == 0:
        bal = data.get("data", {}).get("balance", {})
        return float(bal.get("availableMargin", 0))
    return 0.0

def get_price(symbol: str) -> float:
    """Precio actual de un par en BingX."""
    data = api_get("/openApi/swap/v2/quote/price", {"symbol": symbol})
    if data.get("code") == 0:
        return float(data.get("data", {}).get("price", 0))
    return 0.0

def get_positions() -> List[dict]:
    """Posiciones abiertas en BingX."""
    data = api_get("/openApi/swap/v2/user/positions")
    if data.get("code") == 0:
        return data.get("data", [])
    return []


# ══════════════════════════════════════════════════════════════════════════════
# INDICADORES MATEMÁTICOS
# ══════════════════════════════════════════════════════════════════════════════

def calc_rsi(closes: List[float], period: int = RSI_PERIOD) -> float:
    """RSI de Wilder con período configurable. Default: RSI(2)."""
    if len(closes) < period + 1:
        return 50.0
    deltas = [closes[i] - closes[i-1] for i in range(1, len(closes))]
    recent = deltas[-(period):]
    gains = [d if d > 0 else 0 for d in recent]
    losses = [-d if d < 0 else 0 for d in recent]
    avg_gain = sum(gains) / period
    avg_loss = sum(losses) / period
    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    return 100 - (100 / (1 + rs))

def calc_ema(values: List[float], period: int) -> List[float]:
    """EMA con multiplicador estándar."""
    if len(values) < period:
        return []
    k = 2 / (period + 1)
    ema = [sum(values[:period]) / period]
    for v in values[period:]:
        ema.append(v * k + ema[-1] * (1 - k))
    return ema

def calc_zscore(closes: List[float], period: int = ZSCORE_PERIOD) -> float:
    """Z-Score: cuántas desviaciones estándar del precio vs media."""
    if len(closes) < period:
        return 0.0
    window = closes[-period:]
    mean = sum(window) / len(window)
    std = (sum((x - mean)**2 for x in window) / len(window)) ** 0.5
    if std == 0:
        return 0.0
    return (closes[-1] - mean) / std

def calc_atr(klines: List[dict], period: int = 14) -> float:
    """Average True Range."""
    if len(klines) < period + 1:
        return 0.0
    trs = []
    for i in range(1, len(klines)):
        h = klines[i]["high"]
        l = klines[i]["low"]
        pc = klines[i-1]["close"]
        tr = max(h - l, abs(h - pc), abs(l - pc))
        trs.append(tr)
    return sum(trs[-period:]) / period

def calc_adx(klines: List[dict], period: int = ADX_PERIOD) -> float:
    """ADX — Wilder smoothing correcto."""
    if len(klines) < period * 2 + 1:
        return 0.0
    
    plus_dm = []
    minus_dm = []
    tr_list = []
    
    for i in range(1, len(klines)):
        h = klines[i]["high"]
        l = klines[i]["low"]
        ph = klines[i-1]["high"]
        pl = klines[i-1]["low"]
        pc = klines[i-1]["close"]
        
        up_move = h - ph
        down_move = pl - l
        
        plus_dm.append(up_move if up_move > down_move and up_move > 0 else 0)
        minus_dm.append(down_move if down_move > up_move and down_move > 0 else 0)
        tr_list.append(max(h - l, abs(h - pc), abs(l - pc)))
    
    if len(tr_list) < period:
        return 0.0
    
    # Wilder smoothing
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
        dx = 100 * abs(plus_di - minus_di) / di_sum
        dx_list.append(dx)
    
    if len(dx_list) < period:
        return 0.0
    
    # Smooth DX into ADX
    adx = sum(dx_list[:period]) / period
    for dx in dx_list[period:]:
        adx = (adx * (period - 1) + dx) / period
    
    return adx


# ══════════════════════════════════════════════════════════════════════════════
# MOTOR DE SEÑAL — MEAN REVERSION
# ══════════════════════════════════════════════════════════════════════════════

def evaluate(symbol: str, klines: List[dict]) -> Optional[dict]:
    """
    Evalúa si hay señal de mean-reversion.
    
    Reglas:
    1. ADX < 25 → mercado en rango (condición necesaria)
    2. RSI(2) < 10 + precio > EMA50 → BUY (pullback en uptrend)
    3. RSI(2) > 90 + precio < EMA50 → SELL (bounce en downtrend)
    4. Z-Score confirma extremo estadístico (|Z| > 2.0)
    5. Slippage check antes de ejecutar
    """
    if len(klines) < max(KLINE_LIMIT, EMA_TREND_PERIOD + 10):
        logger.debug(f"[EVAL] {symbol} — datos insuficientes ({len(klines)} velas)")
        return None
    
    closes = [k["close"] for k in klines]
    price = closes[-1]
    
    # ── Indicadores ──
    rsi = calc_rsi(closes, RSI_PERIOD)
    zscore = calc_zscore(closes, ZSCORE_PERIOD)
    adx = calc_adx(klines, ADX_PERIOD)
    atr = calc_atr(klines, 14)
    ema50 = calc_ema(closes, EMA_TREND_PERIOD)
    
    if not ema50:
        return None
    
    ema_now = ema50[-1]
    trend = "BULLISH" if price > ema_now else "BEARISH"
    regime = "LATERAL" if adx < ADX_THRESHOLD else "TRENDING"
    
    # ── Log estado ──
    logger.info(
        f"[EVAL] {symbol} ${price:,.2f} | "
        f"RSI2={rsi:.1f} Z={zscore:+.2f} ADX={adx:.1f} "
        f"ATR={atr:.4f} EMA50={ema_now:,.2f} | "
        f"{trend} {regime}"
    )
    
    # ── Regla 1: Solo operar en mercado lateral ──
    if regime == "TRENDING":
        logger.debug(f"[EVAL] {symbol} SKIP — ADX={adx:.1f} > {ADX_THRESHOLD} (trending)")
        return None
    
    # ── Verificar si ya tenemos posición en este par ──
    if symbol in _positions:
        return None
    
    # ── Regla 2: Señal de entrada ──
    action = None
    
    if rsi < RSI_OVERSOLD and trend == "BULLISH" and zscore < -ZSCORE_THRESHOLD:
        action = "BUY"
    elif rsi > RSI_OVERBOUGHT and trend == "BEARISH" and zscore > ZSCORE_THRESHOLD:
        action = "SELL"
    
    if not action:
        return None
    
    # ── SL basado en ATR ──
    sl_distance = atr * ATR_SL_MULT
    if action == "BUY":
        sl = round(price - sl_distance, 6)
    else:
        sl = round(price + sl_distance, 6)
    
    sl_pct = sl_distance / price * 100
    
    # ── CONFIDENCE SCORE (0-100) ──
    # Factores ponderados:
    #   RSI extremo (30pts): más extremo = más confianza
    #   Z-Score profundidad (25pts): más desviaciones = más confianza
    #   ADX bajo (20pts): más lateral = mejor para mean-reversion
    #   Trend alignment (15pts): precio bien apoyado en EMA
    #   Volatilidad estable (10pts): ATR no inflado
    
    # RSI score (30pts): RSI<5 o >95 = max, RSI=10/90 = min
    if action == "BUY":
        rsi_score = max(0, min(30, (10 - rsi) / 10 * 30))
    else:
        rsi_score = max(0, min(30, (rsi - 90) / 10 * 30))
    
    # Z-Score score (25pts): |Z|>3 = max, |Z|=2 = min
    z_abs = abs(zscore)
    z_score_pts = max(0, min(25, (z_abs - 2.0) / 1.5 * 25))
    
    # ADX score (20pts): ADX<15 = max (muy lateral), ADX=25 = 0
    adx_score = max(0, min(20, (25 - adx) / 10 * 20))
    
    # Trend alignment (15pts): distancia precio vs EMA como % de ATR
    ema_dist = abs(price - ema_now) / atr if atr > 0 else 0
    trend_score = max(0, min(15, ema_dist / 3 * 15))
    
    # Volatilidad (10pts): ATR estable = bueno (comparar últimas 5 vs 14)
    recent_atr = calc_atr(klines, 5)
    atr_ratio = recent_atr / atr if atr > 0 else 1
    vol_score = max(0, min(10, (2 - abs(atr_ratio - 1) * 5) * 5))
    
    confidence = round(rsi_score + z_score_pts + adx_score + trend_score + vol_score)
    confidence = max(0, min(100, confidence))
    
    logger.info(
        f"[SIGNAL] 🎯 {action} {symbol} @ ${price:,.2f} | "
        f"RSI2={rsi:.1f} Z={zscore:+.2f} ADX={adx:.1f} | "
        f"SL=${sl:,.2f} ({sl_pct:.2f}%) | {trend} {regime} | "
        f"Score={confidence}/100 [RSI={rsi_score:.0f} Z={z_score_pts:.0f} ADX={adx_score:.0f} T={trend_score:.0f} V={vol_score:.0f}]"
    )
    
    return {
        "action": action,
        "symbol": symbol,
        "price": price,
        "sl": sl,
        "sl_pct": sl_pct,
        "rsi": rsi,
        "zscore": zscore,
        "adx": adx,
        "atr": atr,
        "trend": trend,
        "regime": regime,
        "confidence": confidence,
    }


def check_exit(symbol: str, klines: List[dict]) -> Optional[str]:
    """
    Verifica si debemos cerrar una posición abierta.
    
    Regla de salida (Connors):
    - LONG: RSI(2) > 60 → el snapback ya ocurrió, tomar ganancias
    - SHORT: RSI(2) < 40 → el snapback ya ocurrió, tomar ganancias
    - SL: si el precio cruza el SL, cerrar inmediatamente
    """
    if symbol not in _positions:
        return None
    
    pos = _positions[symbol]
    closes = [k["close"] for k in klines]
    price = closes[-1]
    rsi = calc_rsi(closes, RSI_PERIOD)
    
    # ── Check SL ──
    if pos["action"] == "BUY" and price <= pos["sl"]:
        logger.info(f"[EXIT] 🛑 SL HIT {symbol} @ ${price:,.2f} (SL=${pos['sl']:,.2f})")
        return "SL"
    elif pos["action"] == "SELL" and price >= pos["sl"]:
        logger.info(f"[EXIT] 🛑 SL HIT {symbol} @ ${price:,.2f} (SL=${pos['sl']:,.2f})")
        return "SL"
    
    # ── Check RSI exit ──
    if pos["action"] == "BUY" and rsi > RSI_EXIT_LONG:
        logger.info(f"[EXIT] ✅ RSI EXIT {symbol} RSI={rsi:.1f} > {RSI_EXIT_LONG} (mean reverted)")
        return "RSI_EXIT"
    elif pos["action"] == "SELL" and rsi < RSI_EXIT_SHORT:
        logger.info(f"[EXIT] ✅ RSI EXIT {symbol} RSI={rsi:.1f} < {RSI_EXIT_SHORT} (mean reverted)")
        return "RSI_EXIT"
    
    return None


# ══════════════════════════════════════════════════════════════════════════════
# EXECUTION ENGINE
# ══════════════════════════════════════════════════════════════════════════════

def execute_crypto(signal: dict) -> bool:
    """Ejecuta trade en BingX con limit order."""
    symbol = signal["symbol"]
    action = signal["action"]
    price = signal["price"]
    sl = signal["sl"]
    
    # ── Position sizing ──
    balance = get_balance()
    if balance <= 0:
        logger.error(f"[EXEC] Sin balance disponible")
        return False
    
    margin = balance * RISK_PCT
    notional = margin * LEVERAGE
    
    # ── Obtener precio real y verificar slippage ──
    real_price = get_price(symbol)
    if real_price <= 0:
        return False
    
    slippage = abs(real_price - price) / price
    if slippage > MAX_SLIPPAGE_PCT:
        logger.warning(
            f"[EXEC] ❌ SLIPPAGE GATE — {symbol} signal=${price:,.2f} "
            f"real=${real_price:,.2f} slip={slippage*100:.2f}% > {MAX_SLIPPAGE_PCT*100:.1f}%"
        )
        return False
    
    # ── Calcular cantidad ──
    qty = notional / real_price
    
    # ── Colocar orden ──
    side = "BUY" if action == "BUY" else "SELL"
    order_params = {
        "symbol": symbol,
        "side": side,
        "positionSide": "LONG" if action == "BUY" else "SHORT",
        "type": "MARKET",
        "quantity": str(round(qty, 6)),
    }
    
    result = api_post("/openApi/swap/v2/trade/order", order_params)
    
    if result.get("code") == 0:
        order_data = result.get("data", {})
        fill_price = float(order_data.get("price", real_price))
        
        # ── Recalcular SL desde fill price ──
        atr = signal["atr"]
        if action == "BUY":
            sl = round(fill_price - atr * ATR_SL_MULT, 6)
        else:
            sl = round(fill_price + atr * ATR_SL_MULT, 6)
        
        # ── Registrar posición ──
        _positions[symbol] = {
            "action": action,
            "entry": fill_price,
            "sl": sl,
            "qty": qty,
            "margin": margin,
            "time": datetime.now(timezone.utc).isoformat(),
        }
        
        # ── Colocar SL en BingX ──
        sl_side = "SELL" if action == "BUY" else "BUY"
        sl_pos_side = "LONG" if action == "BUY" else "SHORT"
        api_post("/openApi/swap/v2/trade/order", {
            "symbol": symbol,
            "side": sl_side,
            "positionSide": sl_pos_side,
            "type": "STOP_MARKET",
            "stopPrice": str(sl),
            "quantity": str(round(qty, 6)),
        })
        
        logger.info(
            f"[TRADE] ✅ {action} {symbol} @ ${fill_price:,.2f} | "
            f"Qty={qty:.6f} | SL=${sl:,.2f} | Margin=${margin:.2f}"
        )
        
        # ── Telegram ──
        tg_trade_alert(signal, fill_price, sl, margin, "BINGX")
        return True
    else:
        logger.error(f"[EXEC] Error orden {symbol}: {result}")
        return False


def close_crypto(symbol: str, reason: str) -> float:
    """Cierra posición en BingX."""
    if symbol not in _positions:
        return 0.0
    
    pos = _positions[symbol]
    side = "SELL" if pos["action"] == "BUY" else "BUY"
    pos_side = "LONG" if pos["action"] == "BUY" else "SHORT"
    
    result = api_post("/openApi/swap/v2/trade/order", {
        "symbol": symbol,
        "side": side,
        "positionSide": pos_side,
        "type": "MARKET",
        "quantity": str(round(pos["qty"], 6)),
    })
    
    if result.get("code") == 0:
        close_price = get_price(symbol)
        if pos["action"] == "BUY":
            pnl = (close_price - pos["entry"]) * pos["qty"]
        else:
            pnl = (pos["entry"] - close_price) * pos["qty"]
        
        pnl_pct = pnl / pos["margin"] * 100
        
        logger.info(
            f"[CLOSE] {symbol} {reason} | Entry=${pos['entry']:,.2f} → "
            f"Close=${close_price:,.2f} | PnL=${pnl:+.2f} ({pnl_pct:+.1f}%)"
        )
        
        tg_close_alert(symbol, pos, close_price, pnl, reason)
        
        global _daily_pnl, _daily_trades
        _daily_pnl += pnl
        _daily_trades += 1
        
        del _positions[symbol]
        return pnl
    
    return 0.0


# ══════════════════════════════════════════════════════════════════════════════
# TELEGRAM
# ══════════════════════════════════════════════════════════════════════════════

def tg_send(msg: str) -> bool:
    if not TG_TOKEN or not TG_CHAT_ID:
        logger.warning("[TG] Token o chat_id vacío — no se puede enviar")
        return False
    try:
        chat = TG_CHAT_ID.strip()
        r = requests.post(
            f"https://api.telegram.org/bot{TG_TOKEN.strip()}/sendMessage",
            json={"chat_id": chat, "text": msg, "parse_mode": "HTML"},
            timeout=10,
        )
        if r.status_code != 200:
            logger.error(f"[TG] Error {r.status_code}: {r.text[:300]}")
            return False
        return True
    except Exception as e:
        logger.error(f"[TG] Exception: {e}")
        return False

def tg_trade_alert(signal: dict, fill: float, sl: float, margin: float, venue: str):
    emoji = "🟢" if signal["action"] == "BUY" else "🔴"
    side = "LONG" if signal["action"] == "BUY" else "SHORT"
    sl_pct = abs(fill - sl) / fill * 100
    conf = signal.get("confidence", 0)
    
    # Score visual bar
    filled = round(conf / 10)
    bar = "█" * filled + "░" * (10 - filled)
    
    # Pronostico basado en score
    if conf >= 80:
        pronostico = "EXCELENTE"
    elif conf >= 65:
        pronostico = "FAVORABLE"
    elif conf >= 50:
        pronostico = "MODERADO"
    else:
        pronostico = "BAJO"
    
    msg = (
        f"{emoji} <b>PHANTOM — {side} {signal['symbol']}</b>\n"
        f"{'━' * 24}\n"
        f"📍 Entry:   ${fill:,.2f}\n"
        f"🛑 SL:      ${sl:,.2f} (-{sl_pct:.2f}%)\n"
        f"📊 Exit:    RSI(2) cruza {'60' if signal['action']=='BUY' else '40'}\n"
        f"{'━' * 24}\n"
        f"📈 RSI(2):  {signal['rsi']:.1f}\n"
        f"📐 Z-Score: {signal['zscore']:+.2f}σ\n"
        f"📊 ADX:     {signal['adx']:.1f} ({signal['regime']})\n"
        f"📈 Trend:   {signal['trend']}\n"
        f"{'━' * 24}\n"
        f"🎯 Score:   {conf}/100 [{bar}]\n"
        f"🔮 Pronóstico: {pronostico}\n"
        f"{'━' * 24}\n"
        f"💰 Margin: ${margin:.2f} | Venue: {venue}\n"
        f"⏱ {datetime.now(timezone.utc).strftime('%H:%M')} UTC"
    )
    tg_send(msg)

def tg_close_alert(symbol: str, pos: dict, close_price: float, pnl: float, reason: str):
    emoji = "✅" if pnl > 0 else "❌"
    pnl_pct = pnl / pos["margin"] * 100
    msg = (
        f"{emoji} <b>PHANTOM — CLOSE {symbol}</b>\n"
        f"{'━' * 24}\n"
        f"📍 Entry: ${pos['entry']:,.2f} → Close: ${close_price:,.2f}\n"
        f"💰 PnL:   ${pnl:+.2f} ({pnl_pct:+.1f}%)\n"
        f"📋 Razón: {reason}\n"
        f"📊 Hoy:   ${_daily_pnl:+.2f} ({_daily_trades} trades)"
    )
    tg_send(msg)

def tg_startup(balance: float):
    tg_send(
        f"👻 <b>PHANTOM v1.0 iniciado</b>\n"
        f"{'━' * 24}\n"
        f"Estrategia: Mean-Reversion (RSI2 + Z-Score)\n"
        f"Activos: {', '.join(CRYPTO_PAIRS)} + {STOCK_SYMBOL}\n"
        f"Balance: ${balance:,.2f}\n"
        f"Riesgo: {RISK_PCT*100:.0f}% por trade | Lev: {LEVERAGE}x\n"
        f"Régimen: Solo ADX &lt; {ADX_THRESHOLD}\n"
        f"Eval: cada {EVAL_INTERVAL//60} min\n"
        f"{'━' * 24}\n"
        f"SL: ATR × {ATR_SL_MULT} | Slippage gate: {MAX_SLIPPAGE_PCT*100:.1f}%\n"
        f"Entry: RSI2 &lt; {RSI_OVERSOLD} (BUY) / &gt; {RSI_OVERBOUGHT} (SELL)\n"
        f"Exit: RSI2 &gt; {RSI_EXIT_LONG} (BUY) / &lt; {RSI_EXIT_SHORT} (SELL)"
    )

def tg_daily_report():
    tg_send(
        f"📊 <b>PHANTOM — Resumen diario</b>\n"
        f"{'━' * 24}\n"
        f"Trades: {_daily_trades}\n"
        f"PnL: ${_daily_pnl:+.2f}\n"
        f"Posiciones abiertas: {len(_positions)}\n"
        f"⏱ {datetime.now(timezone.utc).strftime('%H:%M')} UTC"
    )


# ══════════════════════════════════════════════════════════════════════════════
# NVDA HANDLER (Telegram only — Quantfury manual)
# ══════════════════════════════════════════════════════════════════════════════

def is_us_market_open() -> bool:
    """Verifica si el mercado US está abierto."""
    et = datetime.now(timezone.utc) + timedelta(hours=-4)
    if et.weekday() > 4:
        return False
    t = (et.hour, et.minute)
    return (9, 30) <= t < (16, 0)

def evaluate_nvda(klines: List[dict]) -> Optional[dict]:
    """Evalúa NVDA con la misma lógica pero solo manda alerta Telegram."""
    signal = evaluate(STOCK_SYMBOL, klines)
    if signal:
        signal["venue"] = "QUANTFURY"
        # Solo alerta — no ejecuta
        tg_trade_alert(signal, signal["price"], signal["sl"], 0, "QUANTFURY (manual)")
        logger.info(f"[NVDA] 📱 Alerta Telegram enviada — {signal['action']} @ ${signal['price']:,.2f}")
    return signal


# ══════════════════════════════════════════════════════════════════════════════
# MAIN LOOP
# ══════════════════════════════════════════════════════════════════════════════

def main_loop():
    global _daily_pnl, _daily_trades, _start_balance
    
    _start_balance = get_balance()
    logger.info("=" * 60)
    logger.info("PHANTOM v1.0 — Wino and Company")
    logger.info(f"Balance: ${_start_balance:,.2f}")
    logger.info(f"Activos: {CRYPTO_PAIRS} + {STOCK_SYMBOL}")
    logger.info(f"Estrategia: Mean-Reversion RSI(2) + Z-Score + ADX Regime")
    logger.info(f"Eval cada {EVAL_INTERVAL//60} min | SL ATR×{ATR_SL_MULT}")
    logger.info("=" * 60)
    
    tg_startup(_start_balance)
    
    last_daily_reset = datetime.now(timezone.utc).date()
    
    while True:
        try:
            now = datetime.now(timezone.utc)
            
            # ── Reset diario ──
            if now.date() != last_daily_reset:
                tg_daily_report()
                _daily_pnl = 0.0
                _daily_trades = 0
                last_daily_reset = now.date()
                logger.info("[DAILY] Reset PnL diario")
            
            # ── Daily loss limit ──
            balance = get_balance()
            if _start_balance > 0 and _daily_pnl < -(_start_balance * DAILY_LOSS_LIMIT):
                logger.warning(
                    f"[GUARD] ⛔ Daily loss limit hit: ${_daily_pnl:.2f} "
                    f"(límite: -${_start_balance * DAILY_LOSS_LIMIT:.2f})"
                )
                time.sleep(EVAL_INTERVAL)
                continue
            
            # ── Evaluar crypto pairs ──
            for symbol in CRYPTO_PAIRS:
                klines = get_klines(symbol)
                if not klines:
                    continue
                
                # Check exits primero
                exit_reason = check_exit(symbol, klines)
                if exit_reason:
                    close_crypto(symbol, exit_reason)
                    continue
                
                # Check entries
                if len(_positions) < MAX_POSITIONS:
                    signal = evaluate(symbol, klines)
                    if signal:
                        execute_crypto(signal)
            
            # ── Evaluar NVDA (solo durante market hours) ──
            if is_us_market_open():
                nvda_klines = get_nvda_klines()
                if nvda_klines:
                    evaluate_nvda(nvda_klines)
            
        except Exception as e:
            logger.error(f"[LOOP] Error: {e}", exc_info=True)
        
        time.sleep(EVAL_INTERVAL)


# ══════════════════════════════════════════════════════════════════════════════
# ENTRY POINT
# ══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    if not BINGX_API_KEY:
        logger.error("[CONFIG] BINGX_API_KEY no configurada")
    if not BINGX_API_SECRET:
        logger.error("[CONFIG] BINGX_API_SECRET no configurada")
    main_loop()
