"""
phantom.py — Phantom Bot v1.3
Wino and Company · Junio 2026

ESTRATEGIA: Statistical Mean-Reversion con Detección de Régimen
═════════════════════════════════════════════════════════════════

v1.3 CHANGELOG (21-Jun-2026):
  - Fix: mark price inyectado en last candle para indicadores live (no stale)
  - Fix: RSI(2) docstring corregido — es Cutler's SMA (Pine Script ajustado para match)
  - Fix: SQLite persistence para posiciones (sobrevive redeploys)
  - Fix: cancel SL orders huérfanas al cerrar por RSI exit
  - Fix: min confidence gate (score < 30 = no ejecutar)
  - Fix: PnL descuenta taker fees (0.05% × 2)
  - Fix: is_us_market_open usa zoneinfo (EDT/EST correcto todo el año)
  - Fix: mark price fetch 1 vez por símbolo por ciclo (no 2x)
  - Fix: get_klines usa signed=False (endpoint público)
  - Fix: docstring execute_crypto corregido (MARKET, no limit)
  - Add: NEAR MISS logging (2/3 condiciones cumplidas)
  - Add: fill_price=0 fallback consulta posición real
  - Clean: imports no usados removidos (json, deque, Tuple)

v1.2 CHANGELOG (18-Jun-2026):
  - Trend filter: GATE → BIAS (ya no bloquea entradas counter-trend)
  - Counter-trend entries ejecutan con confianza reducida (-15pts)
  - With-trend entries mantienen bonus completo (+15pts)
  - Fix: catch-22 donde RSI extremo forzaba price past EMA50

v1.1 CHANGELOG (18-Jun-2026):
  - Timeframe: 15m → 1H (reduce ruido, EMA50=50h sticky, Z-Score=20h robusto)
  - Z-Score threshold: 2.0σ → 1.5σ (compensa menor volatilidad intra-candle 1H)
  - Kline limit: 100 → 200 (más data para cálculos en 1H)
  - Activos: +ETH-USDT (mayor superficie de señales)

LÓGICA CORE:
  1. Régimen: ADX < 40 = mercado lateral/semi-trending → mean-reversion activo
                ADX >= 40 = tendencia fuerte → NO operar (esperar)
  2. Señal: RSI(2) < 10 + Z-Score < -1.5σ → BUY (oversold extremo)
           RSI(2) > 90 + Z-Score > +1.5σ → SELL (overbought extremo)
  3. Trend EMA50: modifica confidence score, NO bloquea entrada
     - With-trend: +15pts confianza
     - Counter-trend: -15pts confianza (penalidad, no bloqueo)
  4. Salida: RSI(2) cruza 60 (BUY) o 40 (SELL) — NO target fijo
  5. Min confidence: score >= 30 para ejecutar

ACTIVOS: BTC-USDT, SOL-USDT, ETH-USDT (BingX auto) + NVDA (Telegram/Quantfury)
OBJETIVO: +1-2% diario sobre capital disponible
"""

import os
import time
import hmac
import hashlib
import sqlite3
import logging
import requests
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
from typing import Optional, Dict, List

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
CRYPTO_PAIRS = ["BTC-USDT", "SOL-USDT", "ETH-USDT"]
STOCK_SYMBOL = "NVDA"

# ── Estrategia ──
RSI_PERIOD        = 2       # RSI(2) — Connors
RSI_OVERSOLD      = 10      # Comprar cuando RSI < 10 (extremo)
RSI_OVERBOUGHT    = 90      # Vender cuando RSI > 90 (extremo)
RSI_EXIT_LONG     = 60      # Salir de LONG cuando RSI > 60
RSI_EXIT_SHORT    = 40      # Salir de SHORT cuando RSI < 40
ZSCORE_THRESHOLD  = 1.5     # Confirmación: precio a 1.5σ de la media (v1.1: bajado de 2.0)
ZSCORE_PERIOD     = 20      # Ventana para calcular Z-Score
EMA_TREND_PERIOD  = 50      # EMA para determinar tendencia
ADX_PERIOD        = 14      # ADX para detección de régimen
ADX_THRESHOLD     = 40      # ADX < 40 = lateral + semi-trending (v1.2: era 30)

# ── Risk Management ──
LEVERAGE          = 7
RISK_PCT          = 0.15    # 15% del capital por trade (Kelly óptimo para 75% WR)
ATR_SL_MULT       = 3.0    # SL = ATR × 3.0 (fuera del ruido)
MAX_POSITIONS     = 2       # máximo 2 posiciones simultáneas
DAILY_LOSS_LIMIT  = 0.03    # -3% del capital = stop trading hoy
MAX_SLIPPAGE_PCT  = 0.20    # 20% max (v1.2: 1H kline close vs mark price puede diferir hasta ~15%)
MIN_CONFIDENCE    = 30      # Score mínimo para ejecutar (v1.3: gate real, no decorativo)
TAKER_FEE         = 0.0005  # 0.05% taker fee BingX
# ── Evaluación ──
EVAL_INTERVAL     = 900     # Evaluar cada 15 minutos (captura candle 1H formándose)
KLINE_TIMEFRAME   = "1h"    # Velas de 1 hora (v1.1: era 15m)
KLINE_LIMIT       = 200     # Últimas 200 velas (v1.1: era 100)

# ── BingX API ──
BINGX_BASE = "https://open-api.bingx.com"

# ── SQLite DB ──
DB_PATH = os.getenv("PHANTOM_DB", "/tmp/phantom_positions.db")

# ── Estado (runtime) ──
_positions: Dict[str, dict] = {}
_daily_pnl = 0.0
_daily_trades = 0
_start_balance = 0.0


# ══════════════════════════════════════════════════════════════════════════════
# SQLITE PERSISTENCE — posiciones sobreviven redeploys
# ══════════════════════════════════════════════════════════════════════════════

def init_db():
    """Crea tabla de posiciones si no existe."""
    conn = sqlite3.connect(DB_PATH)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS positions (
            symbol     TEXT PRIMARY KEY,
            action     TEXT NOT NULL,
            entry      REAL NOT NULL,
            sl         REAL NOT NULL,
            qty        REAL NOT NULL,
            margin     REAL NOT NULL,
            opened_at  TEXT NOT NULL
        )
    """)
    conn.commit()
    conn.close()
    logger.info(f"[DB] SQLite initialized: {DB_PATH}")


def db_save_position(symbol: str, pos: dict):
    """Guarda posición en SQLite."""
    conn = sqlite3.connect(DB_PATH)
    conn.execute(
        "INSERT OR REPLACE INTO positions (symbol, action, entry, sl, qty, margin, opened_at) "
        "VALUES (?, ?, ?, ?, ?, ?, ?)",
        (symbol, pos["action"], pos["entry"], pos["sl"], pos["qty"], pos["margin"], pos["time"])
    )
    conn.commit()
    conn.close()


def db_load_positions() -> Dict[str, dict]:
    """Carga posiciones guardadas al iniciar."""
    conn = sqlite3.connect(DB_PATH)
    rows = conn.execute("SELECT symbol, action, entry, sl, qty, margin, opened_at FROM positions").fetchall()
    conn.close()
    positions = {}
    for row in rows:
        positions[row[0]] = {
            "action": row[1], "entry": row[2], "sl": row[3],
            "qty": row[4], "margin": row[5], "time": row[6],
        }
    return positions


def db_delete_position(symbol: str):
    """Elimina posición de SQLite."""
    conn = sqlite3.connect(DB_PATH)
    conn.execute("DELETE FROM positions WHERE symbol = ?", (symbol,))
    conn.commit()
    conn.close()

# ══════════════════════════════════════════════════════════════════════════════
# BINGX API CLIENT
# ══════════════════════════════════════════════════════════════════════════════

def _sign(params: dict) -> str:
    """Firma HMAC-SHA256 — idéntica a WinoBot (NO ordena params)."""
    query = "&".join(f"{k}={v}" for k, v in params.items())
    return hmac.new(
        BINGX_API_SECRET.encode("utf-8"),
        query.encode("utf-8"),
        hashlib.sha256
    ).hexdigest()

def _headers() -> dict:
    return {
        "X-BX-APIKEY": BINGX_API_KEY,
        "Content-Type": "application/x-www-form-urlencoded",
    }

def api_get(path: str, params: dict = None, signed: bool = True) -> dict:
    try:
        p = params or {}
        if signed:
            p["timestamp"] = int(time.time() * 1000)
            p["signature"] = _sign(p)
        r = requests.get(f"{BINGX_BASE}{path}", params=p, headers=_headers(), timeout=10)
        return r.json()
    except Exception as e:
        logger.error(f"[API] GET {path}: {e}")
        return {}

def api_post(path: str, params: dict = None) -> dict:
    try:
        p = params or {}
        p["timestamp"] = int(time.time() * 1000)
        p["signature"] = _sign(p)
        r = requests.post(f"{BINGX_BASE}{path}", params=p, headers=_headers(), timeout=10)
        return r.json()
    except Exception as e:
        logger.error(f"[API] POST {path}: {e}")
        return {}


# ══════════════════════════════════════════════════════════════════════════════
# TRADE SETUP — leverage, margin mode, step size
# ══════════════════════════════════════════════════════════════════════════════

_step_size_cache: Dict[str, float] = {}


def get_step_size(symbol: str) -> float:
    """Obtiene el tamaño mínimo de cantidad para un símbolo."""
    if symbol in _step_size_cache:
        return _step_size_cache[symbol]

    data = api_get("/openApi/swap/v2/quote/contracts", {})
    if data.get("code") != 0:
        return 0.001

    contracts = data.get("data", [])
    if isinstance(contracts, list):
        for c in contracts:
            sym = c.get("symbol", "")
            step = float(c.get("tradeMinQuantity", 0.001))
            _step_size_cache[sym] = step
            if sym == symbol:
                logger.info(f"[STEPSIZE] {symbol} = {step}")
                return step

    return 0.001


def round_qty(symbol: str, qty_raw: float) -> float:
    """Redondea cantidad al step size válido para BingX."""
    step = get_step_size(symbol)
    qty = int(qty_raw / step) * step
    return round(qty, 8)


def set_leverage_all(pairs: list, leverage: int):
    """Configura leverage y margin mode para todos los pares."""
    for symbol in pairs:
        # Margin mode ISOLATED
        try:
            api_post("/openApi/swap/v2/trade/marginType",
                     {"symbol": symbol, "marginType": "ISOLATED"})
            logger.info(f"[SETUP] {symbol} margin=ISOLATED")
        except Exception as e:
            logger.warning(f"[SETUP] {symbol} margin error: {e}")

        # Leverage LONG + SHORT
        try:
            api_post("/openApi/swap/v2/trade/leverage",
                     {"symbol": symbol, "side": "LONG", "leverage": leverage})
            api_post("/openApi/swap/v2/trade/leverage",
                     {"symbol": symbol, "side": "SHORT", "leverage": leverage})
            logger.info(f"[SETUP] {symbol} leverage={leverage}x OK")
        except Exception as e:
            logger.warning(f"[SETUP] {symbol} leverage error: {e}")

        time.sleep(0.3)  # rate limit


# ══════════════════════════════════════════════════════════════════════════════
# DATA FETCHING
# ══════════════════════════════════════════════════════════════════════════════

def get_klines(symbol: str, interval: str = KLINE_TIMEFRAME, limit: int = KLINE_LIMIT) -> List[dict]:
    """Obtiene velas de BingX."""
    data = api_get("/openApi/swap/v3/quote/klines", {
        "symbol": symbol, "interval": interval, "limit": str(limit)
    }, signed=False)
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
    """Obtiene velas 1h de NVDA via Yahoo Finance."""
    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{STOCK_SYMBOL}"
    params = {"interval": "1h", "range": "10d", "includePrePost": "false"}
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
    """RSI Cutler's (SMA) con período configurable. Default: RSI(2)."""
    if len(closes) < period + 1:
        return 50.0
    deltas = [closes[i] - closes[i-1] for i in range(1, len(closes))]
    recent = deltas[-(period):]
    gains = [max(d, 0) for d in recent]
    losses = [max(-d, 0) for d in recent]
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

def evaluate(symbol: str, klines: List[dict], mark_price: float = 0) -> Optional[dict]:
    """
    Evalúa si hay señal de mean-reversion.
    
    Reglas (v1.3):
    1. ADX < 40 → mercado en rango o semi-trending (condición necesaria)
    2. RSI(2) < 10 + Z < -1.5σ → BUY (oversold extremo)
    3. RSI(2) > 90 + Z > +1.5σ → SELL (overbought extremo)
    4. Trend EMA50: ajusta confidence (+15 with-trend, -15 counter-trend)
    5. Confidence >= MIN_CONFIDENCE para ejecutar
    """
    if len(klines) < max(KLINE_LIMIT, EMA_TREND_PERIOD + 10):
        logger.debug(f"[EVAL] {symbol} — datos insuficientes ({len(klines)} velas)")
        return None
    
    # ── Inyectar mark price actual como close del candle formándose ──
    # Sin esto, los indicadores son stale hasta que cierre la vela 1H
    if mark_price > 0:
        klines = list(klines)  # copia para no mutar original
        klines[-1] = {**klines[-1], "close": mark_price}
    
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
    
    # ── Regla 2: Señal de entrada (v1.2: trend = bias, no gate) ──
    action = None
    
    if rsi < RSI_OVERSOLD and zscore < -ZSCORE_THRESHOLD:
        action = "BUY"
    elif rsi > RSI_OVERBOUGHT and zscore > ZSCORE_THRESHOLD:
        action = "SELL"
    
    # Determinar si es with-trend o counter-trend
    with_trend = False
    if action == "BUY" and trend == "BULLISH":
        with_trend = True
    elif action == "SELL" and trend == "BEARISH":
        with_trend = True
    
    if not action:
        # ── NEAR MISS: 2 de 3 condiciones cumplidas ──
        rsi_ok = rsi < RSI_OVERSOLD or rsi > RSI_OVERBOUGHT
        z_ok = abs(zscore) > ZSCORE_THRESHOLD
        adx_ok = adx < ADX_THRESHOLD
        conditions_met = sum([rsi_ok, z_ok, adx_ok])
        if conditions_met >= 2:
            logger.info(
                f"[NEAR MISS] {symbol} {conditions_met}/3 | "
                f"RSI={'✅' if rsi_ok else '❌'}{rsi:.1f} "
                f"Z={'✅' if z_ok else '❌'}{zscore:+.2f} "
                f"ADX={'✅' if adx_ok else '❌'}{adx:.1f}"
            )
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
    
    # Z-Score score (25pts): |Z|>3 = max, |Z|=1.5 = min
    z_abs = abs(zscore)
    z_score_pts = max(0, min(25, (z_abs - 1.5) / 1.5 * 25))
    
    # ADX score (20pts): ADX<15 = max (muy lateral), ADX=25 = 0
    adx_score = max(0, min(20, (25 - adx) / 10 * 20))
    
    # Trend alignment (15pts): v1.2 BIAS — with-trend = +15, counter-trend = -15
    trend_score = 15 if with_trend else -15
    trend_label = "WITH" if with_trend else "COUNTER"
    
    # Volatilidad (10pts): ATR estable = bueno (comparar últimas 5 vs 14)
    recent_atr = calc_atr(klines, 5)
    atr_ratio = recent_atr / atr if atr > 0 else 1
    vol_score = max(0, min(10, (2 - abs(atr_ratio - 1) * 5) * 5))
    
    confidence = round(rsi_score + z_score_pts + adx_score + trend_score + vol_score)
    confidence = max(0, min(100, confidence))
    
    # ── MIN CONFIDENCE GATE (v1.3: score es un gate real, no decorativo) ──
    if confidence < MIN_CONFIDENCE:
        logger.info(
            f"[EVAL] {symbol} SKIP — Score={confidence} < {MIN_CONFIDENCE} | "
            f"{action} RSI={rsi:.1f} Z={zscore:+.2f} [{trend_label}-TREND]"
        )
        return None
    
    logger.info(
        f"[SIGNAL] 🎯 {action} {symbol} @ ${price:,.2f} | "
        f"RSI2={rsi:.1f} Z={zscore:+.2f} ADX={adx:.1f} | "
        f"SL=${sl:,.2f} ({sl_pct:.2f}%) | {trend} {regime} [{trend_label}-TREND] | "
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
        "trend_label": trend_label,
        "regime": regime,
        "confidence": confidence,
    }


def check_exit(symbol: str, klines: List[dict], mark_price: float = 0) -> Optional[str]:
    """
    Verifica si debemos cerrar una posición abierta.
    v1.3: mark price inyectado desde el loop (1 fetch por símbolo).
    """
    if symbol not in _positions:
        return None
    
    pos = _positions[symbol]
    
    # ── Inyectar mark price para RSI fresco ──
    real_price = mark_price
    if real_price > 0:
        klines = list(klines)  # copia para no mutar original
        klines[-1] = {**klines[-1], "close": real_price}
    
    closes = [k["close"] for k in klines]
    rsi = calc_rsi(closes, RSI_PERIOD)
    
    if real_price <= 0:
        real_price = closes[-1]  # fallback
    
    # ── Check SL con precio real ──
    if pos["action"] == "BUY" and real_price <= pos["sl"]:
        logger.info(f"[EXIT] 🛑 SL HIT {symbol} @ ${real_price:,.2f} (SL=${pos['sl']:,.2f})")
        return "SL"
    elif pos["action"] == "SELL" and real_price >= pos["sl"]:
        logger.info(f"[EXIT] 🛑 SL HIT {symbol} @ ${real_price:,.2f} (SL=${pos['sl']:,.2f})")
        return "SL"
    
    # ── Check RSI exit (usa kline data, correcto) ──
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
    """Ejecuta trade en BingX con MARKET order."""
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
    
    # ── Calcular cantidad con step size ──
    qty_raw = notional / real_price
    qty = round_qty(symbol, qty_raw)
    
    if qty <= 0:
        logger.error(f"[EXEC] {symbol} qty=0 después de step size (notional=${notional:.2f} price=${real_price:.2f})")
        return False
    
    # ── Colocar orden ──
    side = "BUY" if action == "BUY" else "SELL"
    order_params = {
        "symbol": symbol,
        "side": side,
        "positionSide": "LONG" if action == "BUY" else "SHORT",
        "type": "MARKET",
        "quantity": str(qty),
    }
    
    result = api_post("/openApi/swap/v2/trade/order", order_params)
    
    if result.get("code") == 0:
        order_data = result.get("data", {})
        fill_price = float(order_data.get("price", 0))
        
        # ── fill_price=0 fallback: BingX market orders son asíncronas ──
        if fill_price <= 0:
            time.sleep(1)
            fill_price = get_price(symbol)
        if fill_price <= 0:
            fill_price = real_price  # último recurso
        
        # ── Recalcular SL desde fill price ──
        atr = signal["atr"]
        if action == "BUY":
            sl = round(fill_price - atr * ATR_SL_MULT, 6)
        else:
            sl = round(fill_price + atr * ATR_SL_MULT, 6)
        
        # ── Registrar posición (RAM + SQLite) ──
        _positions[symbol] = {
            "action": action,
            "entry": fill_price,
            "sl": sl,
            "qty": qty,
            "margin": margin,
            "time": datetime.now(timezone.utc).isoformat(),
        }
        db_save_position(symbol, _positions[symbol])
        
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
    """Cierra posición en BingX y cancela órdenes huérfanas."""
    if symbol not in _positions:
        return 0.0
    
    pos = _positions[symbol]
    side = "SELL" if pos["action"] == "BUY" else "BUY"
    pos_side = "LONG" if pos["action"] == "BUY" else "SHORT"
    
    # ── Cancelar SL orders huérfanas ANTES de cerrar ──
    try:
        api_post("/openApi/swap/v2/trade/cancelAllOpenOrders", {"symbol": symbol})
        logger.info(f"[CLOSE] {symbol} — órdenes pendientes canceladas")
    except Exception as e:
        logger.warning(f"[CLOSE] {symbol} — cancel orders error: {e}")
    
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
            raw_pnl = (close_price - pos["entry"]) * pos["qty"]
        else:
            raw_pnl = (pos["entry"] - close_price) * pos["qty"]
        
        # ── Descontar taker fees (open + close) ──
        fee = (pos["entry"] * pos["qty"] + close_price * pos["qty"]) * TAKER_FEE
        pnl = raw_pnl - fee
        
        pnl_pct = pnl / pos["margin"] * 100
        
        logger.info(
            f"[CLOSE] {symbol} {reason} | Entry=${pos['entry']:,.2f} → "
            f"Close=${close_price:,.2f} | PnL=${pnl:+.2f} ({pnl_pct:+.1f}%) fee=${fee:.4f}"
        )
        
        tg_close_alert(symbol, pos, close_price, pnl, reason)
        
        global _daily_pnl, _daily_trades
        _daily_pnl += pnl
        _daily_trades += 1
        
        del _positions[symbol]
        db_delete_position(symbol)
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
    atr = signal.get("atr", 0)
    
    # ── TP estimado (ATR × 1.5 desde fill) ──
    if signal["action"] == "BUY":
        tp_est = fill + atr * 1.5
    else:
        tp_est = fill - atr * 1.5
    tp_pct = abs(tp_est - fill) / fill * 100
    
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
        f"🎯 TP est:  ${tp_est:,.2f} (+{tp_pct:.2f}%)\n"
        f"🛑 SL:      ${sl:,.2f} (-{sl_pct:.2f}%)\n"
        f"📊 Exit:    RSI(2) cruza {'60' if signal['action']=='BUY' else '40'}\n"
        f"{'━' * 24}\n"
        f"📈 RSI(2):  {signal['rsi']:.1f}\n"
        f"📐 Z-Score: {signal['zscore']:+.2f}σ\n"
        f"📊 ADX:     {signal['adx']:.1f} ({signal['regime']})\n"
        f"📈 Trend:   {signal['trend']} [{signal.get('trend_label', 'N/A')}-TREND]\n"
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
        f"👻 <b>PHANTOM v1.3 iniciado</b>\n"
        f"{'━' * 24}\n"
        f"Estrategia: Mean-Reversion (RSI2 + Z-Score)\n"
        f"Trend: BIAS (no bloquea counter-trend)\n"
        f"Timeframe: {KLINE_TIMEFRAME} | Eval: {EVAL_INTERVAL//60}min\n"
        f"Activos: {', '.join(CRYPTO_PAIRS)} + {STOCK_SYMBOL}\n"
        f"Balance: ${balance:,.2f}\n"
        f"Riesgo: {RISK_PCT*100:.0f}% por trade | Lev: {LEVERAGE}x\n"
        f"{'━' * 24}\n"
        f"RSI2: &lt;{RSI_OVERSOLD} / &gt;{RSI_OVERBOUGHT} (Cutler's SMA)\n"
        f"Z-Score: ±{ZSCORE_THRESHOLD}σ\n"
        f"ADX: &lt;{ADX_THRESHOLD} (lateral)\n"
        f"SL: ATR × {ATR_SL_MULT}\n"
        f"Min Score: {MIN_CONFIDENCE}/100\n"
        f"Exit: RSI2 &gt;{RSI_EXIT_LONG} / &lt;{RSI_EXIT_SHORT}\n"
        f"Persistence: SQLite ✅"
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
    """Verifica si el mercado US está abierto (EDT/EST automático)."""
    et = datetime.now(ZoneInfo("America/New_York"))
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
    global _daily_pnl, _daily_trades, _start_balance, _positions
    
    # ── SQLite init + cargar posiciones sobrevivientes ──
    init_db()
    _positions = db_load_positions()
    if _positions:
        logger.info(f"[DB] Posiciones recuperadas: {list(_positions.keys())}")
        for sym, pos in _positions.items():
            logger.info(f"  → {sym} {pos['action']} entry=${pos['entry']:,.2f} sl=${pos['sl']:,.2f} qty={pos['qty']}")
    
    _start_balance = get_balance()
    logger.info("=" * 60)
    logger.info("PHANTOM v1.3 — Wino and Company")
    logger.info(f"Balance: ${_start_balance:,.2f}")
    logger.info(f"Activos: {CRYPTO_PAIRS} + {STOCK_SYMBOL}")
    logger.info(f"Estrategia: Mean-Reversion RSI(2) + Z-Score + ADX Regime")
    logger.info(f"Timeframe: {KLINE_TIMEFRAME} | Eval cada {EVAL_INTERVAL//60} min | SL ATR×{ATR_SL_MULT}")
    logger.info(f"Thresholds: RSI<{RSI_OVERSOLD}/{RSI_OVERBOUGHT}> | Z>{ZSCORE_THRESHOLD}σ | ADX<{ADX_THRESHOLD}")
    logger.info(f"Min Confidence: {MIN_CONFIDENCE} | Persistence: SQLite")
    logger.info("=" * 60)
    
    tg_startup(_start_balance)
    
    # ── Setup leverage y margin mode para todos los pares ──
    logger.info("[SETUP] Configurando leverage y margin mode...")
    set_leverage_all(CRYPTO_PAIRS, LEVERAGE)
    logger.info("[SETUP] ✅ Completado")
    
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
                
                # ── Un solo fetch de mark price por símbolo ──
                mark = get_price(symbol)
                
                # Check exits primero
                exit_reason = check_exit(symbol, klines, mark)
                if exit_reason:
                    close_crypto(symbol, exit_reason)
                    continue
                
                # Check entries
                if len(_positions) < MAX_POSITIONS:
                    signal = evaluate(symbol, klines, mark)
                    if signal:
                        execute_crypto(signal)
                
                time.sleep(0.3)  # rate limit entre símbolos
            
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
