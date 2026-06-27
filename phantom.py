"""
phantom.py — Phantom Bot v2.1
Wino and Company · Junio 2026

ESTRATEGIA: Statistical Mean-Reversion con Confirmación Estructural
═════════════════════════════════════════════════════════════════════

v2.1 CHANGELOG (27-Jun-2026) — Phase 2 enablement:
  EVIDENCIA: v2.0 ALLOW_COUNTER_TREND=False bloqueó 100% de señales
  (mean-reversion genera señales counter-trend por definición).
  0 trades ejecutados durante freeze period.

  CAMBIOS:
  - Counter-trend hard block ELIMINADO de Phase 1 y Phase 2
  - TK Cross en Phase 2 actúa como filtro natural: si Tenkan cruza Kijun
    en dirección del trade, la reversión ya comenzó → señal válida
  - Counter-trend penalizado en confidence (-10 pts) pero no bloqueado
  - Kijun gate preservado (protección contra catching falling knives)
  - Todos los demás parámetros sin cambios (freeze activo)

v2.0 CHANGELOG (24-Jun-2026) — Full redesign post performance audit:
  EVIDENCIA: 7/7 trades = counter-trend LONGs en bear market, 0% WR.
  Sesgo estructural: RSI(2)+Z-Score solo se alinean para BUY en downtrend.
  Resultado: Phantom era una máquina de catch-the-falling-knife (Judas Swings).

  CAMBIOS ARQUITECTÓNICOS:
  - NEW: ALLOW_COUNTER_TREND = False (elimina counter-trend, 7/7 perdedores)
  - NEW: Two-phase entry system:
    · Phase 1 (Detection): RSI(2)+Z-Score detectan extensión → ALERT state
    · Phase 2 (Confirmation): Tenkan cruza Kijun → entrada confirmada
  - NEW: Kijun-sen gate — no LONG si precio > 3% debajo de Kijun-sen
  - NEW: Kijun-sen dynamic TP — target en Kijun (equilibrio natural del precio)
  - NEW: calc_kijun(period=26), calc_tenkan(period=9)
  - NEW: Alert persistence en SQLite (sobrevive redeploys Railway)
  - RSI exit conservado como fallback (RSI > 60 LONG / RSI < 40 SHORT)
  - SL sin cambios: ATR × 3.0

  FLUJO v2.0:
  1. evaluate() detecta extensión → guarda ALERT (no ejecuta)
  2. check_confirmation() verifica TK Cross cada 15 min
  3. Si TK Cross confirma Y trend sigue with-trend Y Kijun gate pasa → ejecuta
  4. Alert timeout: 48 horas sin confirmación → alert descartada
  5. Exit: Kijun TP (primario) → RSI exit (fallback) → SL (protección)

  v1.x CHANGELOG preservado en git history.

ACTIVOS: BTC-USDT, SOL-USDT, ETH-USDT (BingX auto) + NVDA (Telegram/Quantfury)
OBJETIVO: % de ganancia positiva sobre capital por día (sin WR target)
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

# ── v2.0: Counter-trend + Ichimoku ──
ALLOW_COUNTER_TREND    = False   # v2.0: bloqueado (7/7 counter-trend = losses)
KIJUN_PERIOD           = 26      # Kijun-sen: (HH+LL)/2 de 26 períodos
TENKAN_PERIOD          = 9       # Tenkan-sen: (HH+LL)/2 de 9 períodos
KIJUN_GATE_PCT         = 0.03    # No LONG si precio > 3% debajo de Kijun
ALERT_TIMEOUT_SECONDS  = 48 * 3600  # 48 horas para confirmación TK Cross

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
_alerts: Dict[str, dict] = {}  # v2.0: Phase 1 alerts awaiting TK Cross confirmation
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
    conn.execute("""
        CREATE TABLE IF NOT EXISTS alerts (
            symbol     TEXT PRIMARY KEY,
            action     TEXT NOT NULL,
            price      REAL NOT NULL,
            confidence INTEGER NOT NULL,
            created_at TEXT NOT NULL
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


# ── v2.0: Alert persistence ──

def db_save_alert(symbol: str, alert: dict):
    """Guarda alert Phase 1 en SQLite (sobrevive redeploys)."""
    conn = sqlite3.connect(DB_PATH)
    conn.execute(
        "INSERT OR REPLACE INTO alerts (symbol, action, price, confidence, created_at) "
        "VALUES (?, ?, ?, ?, ?)",
        (symbol, alert["action"], alert["price"], alert["confidence"],
         alert["created_at"])
    )
    conn.commit()
    conn.close()


def db_load_alerts() -> Dict[str, dict]:
    """Carga alerts pendientes al iniciar."""
    conn = sqlite3.connect(DB_PATH)
    try:
        rows = conn.execute(
            "SELECT symbol, action, price, confidence, created_at FROM alerts"
        ).fetchall()
    except sqlite3.OperationalError:
        rows = []
    conn.close()
    alerts = {}
    for row in rows:
        alerts[row[0]] = {
            "action": row[1], "price": row[2], "confidence": row[3],
            "created_at": row[4],
        }
    return alerts


def db_delete_alert(symbol: str):
    """Elimina alert de SQLite."""
    conn = sqlite3.connect(DB_PATH)
    conn.execute("DELETE FROM alerts WHERE symbol = ?", (symbol,))
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

def position_exists_on_exchange(symbol: str) -> bool:
    """Verifica si el símbolo tiene posición real abierta en BingX."""
    try:
        for pos in get_positions():
            if pos.get("symbol") == symbol and abs(float(pos.get("positionAmt", 0))) > 0:
                return True
    except Exception as e:
        logger.error(f"[SYNC] Error verificando posición {symbol}: {e}")
        return True  # en caso de error, asumir que existe (no borrar)
    return False


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


# ── v2.0: Ichimoku Components ──

def calc_kijun(klines: List[dict], period: int = KIJUN_PERIOD) -> float:
    """
    Kijun-sen (Base Line): midpoint of highest high + lowest low over period.
    Representa el equilibrio natural del precio. Mean-reversion target.
    Math: (max(high[n]) + min(low[n])) / 2, n = period
    """
    if len(klines) < period:
        return 0.0
    recent = klines[-period:]
    hh = max(k["high"] for k in recent)
    ll = min(k["low"] for k in recent)
    return (hh + ll) / 2


def calc_tenkan(klines: List[dict], period: int = TENKAN_PERIOD) -> float:
    """
    Tenkan-sen (Conversion Line): midpoint over 9 periods.
    Reacciona más rápido que Kijun. TK Cross = señal de momentum.
    Math: (max(high[n]) + min(low[n])) / 2, n = period
    """
    if len(klines) < period:
        return 0.0
    recent = klines[-period:]
    hh = max(k["high"] for k in recent)
    ll = min(k["low"] for k in recent)
    return (hh + ll) / 2


# ══════════════════════════════════════════════════════════════════════════════
# MOTOR DE SEÑAL — MEAN REVERSION v2.0
# ══════════════════════════════════════════════════════════════════════════════

def evaluate(symbol: str, klines: List[dict], mark_price: float = 0) -> Optional[dict]:
    """
    v2.0 Phase 1: Detecta extensión y genera ALERT (NO ejecuta directamente).
    
    Reglas:
    1. ADX < 40 → mercado en rango o semi-trending
    2. RSI(2) < 10 + Z < -1.5σ → BUY alert
       RSI(2) > 90 + Z > +1.5σ → SELL alert
    3. ALLOW_COUNTER_TREND = False → solo with-trend
    4. Kijun gate: no LONG si precio > 3% debajo de Kijun-sen
    5. Min confidence >= 30
    
    Returns: alert dict para guardar en _alerts, o None
    """
    if len(klines) < max(KLINE_LIMIT, EMA_TREND_PERIOD + 10):
        logger.debug(f"[EVAL] {symbol} — datos insuficientes ({len(klines)} velas)")
        return None
    
    # ── Inyectar mark price actual como close del candle formándose ──
    if mark_price > 0:
        klines = list(klines)
        klines[-1] = {**klines[-1], "close": mark_price}
    
    closes = [k["close"] for k in klines]
    price = closes[-1]
    
    # ── Indicadores ──
    rsi = calc_rsi(closes, RSI_PERIOD)
    zscore = calc_zscore(closes, ZSCORE_PERIOD)
    adx = calc_adx(klines, ADX_PERIOD)
    atr = calc_atr(klines, 14)
    ema50 = calc_ema(closes, EMA_TREND_PERIOD)
    kijun = calc_kijun(klines)
    tenkan = calc_tenkan(klines)
    
    if not ema50:
        return None
    
    ema_now = ema50[-1]
    trend = "BULLISH" if price > ema_now else "BEARISH"
    regime = "LATERAL" if adx < ADX_THRESHOLD else "TRENDING"
    
    # ── Log estado (v2.0: incluye Kijun/Tenkan) ──
    logger.info(
        f"[EVAL] {symbol} ${price:,.2f} | "
        f"RSI2={rsi:.1f} Z={zscore:+.2f} ADX={adx:.1f} "
        f"ATR={atr:.4f} EMA50={ema_now:,.2f} | "
        f"Kijun={kijun:,.2f} Tenkan={tenkan:,.2f} | "
        f"{trend} {regime} | "
        f"RSI={'✅' if rsi < RSI_OVERSOLD or rsi > RSI_OVERBOUGHT else '❌'} "
        f"Z={'✅' if abs(zscore) > ZSCORE_THRESHOLD else '❌'} "
        f"ADX={'✅' if adx < ADX_THRESHOLD else '❌'}"
    )
    
    # ── Regla 1: Solo operar en mercado lateral ──
    if regime == "TRENDING":
        return None
    
    # ── Verificar si ya tenemos posición o alert en este par ──
    if symbol in _positions or symbol in _alerts:
        return None
    
    # ── Regla 2: Señal de entrada ──
    action = None
    if rsi < RSI_OVERSOLD and zscore < -ZSCORE_THRESHOLD:
        action = "BUY"
    elif rsi > RSI_OVERBOUGHT and zscore > ZSCORE_THRESHOLD:
        action = "SELL"
    
    if not action:
        # ── NEAR MISS logging ──
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
    
    # ── v2.1: Counter-trend = allowed (TK Cross in Phase 2 is the filter) ──
    with_trend = (action == "BUY" and trend == "BULLISH") or \
                 (action == "SELL" and trend == "BEARISH")
    trend_label = "WITH-TREND" if with_trend else "COUNTER-TREND"
    
    if not with_trend:
        logger.info(
            f"[EVAL] {symbol} ⚠️ {action} is COUNTER-TREND ({trend}) — "
            f"allowed, TK Cross must confirm reversal in Phase 2"
        )
    
    # ── v2.0: Kijun gate ──
    if kijun > 0:
        if action == "BUY":
            kijun_dist = (kijun - price) / kijun
            if kijun_dist > KIJUN_GATE_PCT:
                logger.info(
                    f"[EVAL] {symbol} BLOCKED — KIJUN GATE | "
                    f"Price ${price:,.2f} is {kijun_dist:.1%} below Kijun ${kijun:,.2f} "
                    f"(max {KIJUN_GATE_PCT:.0%})"
                )
                return None
        elif action == "SELL":
            kijun_dist = (price - kijun) / kijun
            if kijun_dist > KIJUN_GATE_PCT:
                logger.info(
                    f"[EVAL] {symbol} BLOCKED — KIJUN GATE | "
                    f"Price ${price:,.2f} is {kijun_dist:.1%} above Kijun ${kijun:,.2f} "
                    f"(max {KIJUN_GATE_PCT:.0%})"
                )
                return None
    
    # ── Confidence score ──
    if action == "BUY":
        rsi_score = max(0, min(30, (10 - rsi) / 10 * 30))
    else:
        rsi_score = max(0, min(30, (rsi - 90) / 10 * 30))
    z_score_pts = max(0, min(25, (abs(zscore) - 1.5) / 1.5 * 25))
    adx_score = max(0, min(20, (25 - adx) / 10 * 20))
    trend_score = 15 if with_trend else 5  # v2.1: counter-trend penalizado pero permitido
    recent_atr = calc_atr(klines, 5)
    atr_ratio = recent_atr / atr if atr > 0 else 1
    vol_score = max(0, min(10, (2 - abs(atr_ratio - 1) * 5) * 5))
    
    confidence = round(max(0, min(100, rsi_score + z_score_pts + adx_score + trend_score + vol_score)))
    
    if confidence < MIN_CONFIDENCE:
        logger.info(
            f"[EVAL] {symbol} SKIP — Score={confidence} < {MIN_CONFIDENCE} | "
            f"{action} RSI={rsi:.1f} Z={zscore:+.2f}"
        )
        return None
    
    # ── v2.0: Genera ALERT (no ejecuta) ──
    now_iso = datetime.now(timezone.utc).isoformat()
    
    logger.info(
        f"[ALERT] 🔔 Phase 1 — {action} {symbol} @ ${price:,.2f} | "
        f"RSI2={rsi:.1f} Z={zscore:+.2f} ADX={adx:.1f} | "
        f"Kijun=${kijun:,.2f} Tenkan=${tenkan:,.2f} | "
        f"{trend} {regime} [{trend_label}] | "
        f"Score={confidence}/100 | Awaiting TK Cross confirmation..."
    )
    
    return {
        "action": action,
        "symbol": symbol,
        "price": price,
        "confidence": confidence,
        "trend": trend,
        "regime": regime,
        "rsi": rsi,
        "zscore": zscore,
        "adx": adx,
        "created_at": now_iso,
    }


def check_confirmation(symbol: str, klines: List[dict], mark_price: float = 0) -> Optional[dict]:
    """
    v2.0 Phase 2: Verifica si TK Cross confirma la alerta pendiente.
    
    Confirmación = Tenkan cruza Kijun en la dirección del trade:
      - BUY alert: Tenkan cruza ARRIBA de Kijun (momentum alcista)
      - SELL alert: Tenkan cruza ABAJO de Kijun (momentum bajista)
    
    Validaciones adicionales en confirmación:
      1. Re-check trend (puede haber flipiado desde la alerta)
      2. Re-check Kijun gate (Kijun se mueve)
      3. Timeout: 48 horas desde la alerta
    
    Returns: signal dict listo para execute_crypto(), o None
    """
    global _alerts
    
    alert = _alerts.get(symbol)
    if not alert:
        return None
    
    # ── Timeout check ──
    created = datetime.fromisoformat(alert["created_at"])
    elapsed = (datetime.now(timezone.utc) - created).total_seconds()
    if elapsed > ALERT_TIMEOUT_SECONDS:
        logger.info(
            f"[ALERT] ⏰ TIMEOUT {symbol} — {alert['action']} alert expired "
            f"after {elapsed/3600:.1f}h (limit {ALERT_TIMEOUT_SECONDS/3600:.0f}h)"
        )
        del _alerts[symbol]
        db_delete_alert(symbol)
        return None
    
    # ── Inyectar mark price ──
    if mark_price > 0:
        klines = list(klines)
        klines[-1] = {**klines[-1], "close": mark_price}
    
    closes = [k["close"] for k in klines]
    price = closes[-1]
    
    # ── Calcular Tenkan y Kijun actuales ──
    tenkan = calc_tenkan(klines)
    kijun = calc_kijun(klines)
    
    if tenkan <= 0 or kijun <= 0:
        return None
    
    # ── Calcular Tenkan y Kijun del bar anterior ──
    prev_klines = klines[:-1]
    if len(prev_klines) < KIJUN_PERIOD:
        return None
    prev_tenkan = calc_tenkan(prev_klines)
    prev_kijun = calc_kijun(prev_klines)
    
    if prev_tenkan <= 0 or prev_kijun <= 0:
        return None
    
    # ── TK Cross detection ──
    action = alert["action"]
    confirmed = False
    
    if action == "BUY" and prev_tenkan <= prev_kijun and tenkan > kijun:
        confirmed = True
        logger.info(
            f"[CONFIRM] ✅ TK Cross BULLISH {symbol} | "
            f"Tenkan={tenkan:,.2f} crossed above Kijun={kijun:,.2f}"
        )
    elif action == "SELL" and prev_tenkan >= prev_kijun and tenkan < kijun:
        confirmed = True
        logger.info(
            f"[CONFIRM] ✅ TK Cross BEARISH {symbol} | "
            f"Tenkan={tenkan:,.2f} crossed below Kijun={kijun:,.2f}"
        )
    
    if not confirmed:
        return None
    
    # ── Re-check trend at confirmation time ──
    ema_vals = calc_ema(closes, EMA_TREND_PERIOD)
    if not ema_vals:
        return None
    
    ema_now = ema_vals[-1]
    trend = "BULLISH" if price > ema_now else "BEARISH"
    with_trend = (action == "BUY" and trend == "BULLISH") or \
                 (action == "SELL" and trend == "BEARISH")
    
    # ── v2.1: Log trend status but allow counter-trend (TK Cross IS the confirmation) ──
    if not with_trend:
        logger.info(
            f"[CONFIRM] ⚠️ {symbol} — {action} is counter-trend ({trend}) "
            f"but TK Cross confirmed reversal — proceeding"
        )
    
    # ── Re-check Kijun gate at confirmation time ──
    if action == "BUY" and kijun > 0:
        kijun_dist = (kijun - price) / kijun
        if kijun_dist > KIJUN_GATE_PCT:
            logger.info(
                f"[CONFIRM] ❌ ABORT {symbol} — KIJUN GATE failed at confirmation | "
                f"Price ${price:,.2f} is {kijun_dist:.1%} below Kijun ${kijun:,.2f}"
            )
            del _alerts[symbol]
            db_delete_alert(symbol)
            return None
    elif action == "SELL" and kijun > 0:
        kijun_dist = (price - kijun) / kijun
        if kijun_dist > KIJUN_GATE_PCT:
            logger.info(
                f"[CONFIRM] ❌ ABORT {symbol} — KIJUN GATE failed at confirmation | "
                f"Price ${price:,.2f} is {kijun_dist:.1%} above Kijun ${kijun:,.2f}"
            )
            del _alerts[symbol]
            db_delete_alert(symbol)
            return None
    
    # ── Build execution signal ──
    atr = calc_atr(klines)
    adx = calc_adx(klines)
    sl_distance = atr * ATR_SL_MULT
    sl = round(price - sl_distance, 6) if action == "BUY" else round(price + sl_distance, 6)
    sl_pct = sl_distance / price * 100
    regime = "LATERAL" if adx < ADX_THRESHOLD else "TRENDING"
    
    trend_label = "WITH-TREND" if with_trend else "COUNTER-TREND"
    
    logger.info(
        f"[SIGNAL] 🎯 {action} {symbol} @ ${price:,.2f} | "
        f"TK Cross confirmed | Kijun TP=${kijun:,.2f} | "
        f"SL=${sl:,.2f} ({sl_pct:.2f}%) | {trend} {regime} [{trend_label}] | "
        f"Score={alert['confidence']}/100"
    )
    
    # Cleanup alert
    del _alerts[symbol]
    db_delete_alert(symbol)
    
    return {
        "action": action,
        "symbol": symbol,
        "price": price,
        "sl": sl,
        "sl_pct": sl_pct,
        "rsi": calc_rsi(closes),
        "zscore": calc_zscore(closes),
        "adx": adx,
        "atr": atr,
        "trend": trend,
        "trend_label": trend_label,
        "regime": regime,
        "confidence": alert["confidence"],
        "kijun_tp": kijun,
    }


def check_exit(symbol: str, klines: List[dict], mark_price: float = 0) -> Optional[str]:
    """
    Verifica si debemos cerrar una posición abierta.
    v2.0: Kijun TP (primario) → RSI exit (fallback) → SL (protección).
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
    sl_hit = False
    if pos["action"] == "BUY" and real_price <= pos["sl"]:
        sl_hit = True
    elif pos["action"] == "SELL" and real_price >= pos["sl"]:
        sl_hit = True
    
    if sl_hit:
        # Verificar si BingX ya cerró por STOP_MARKET server-side
        if not position_exists_on_exchange(symbol):
            logger.info(f"[SYNC] {symbol} — posición cerrada por BingX (SL server-side). Limpiando local.")
            tg_send(f"🔄 <b>SYNC</b> {symbol}\nPosición cerrada por BingX (SL server-side)")
            del _positions[symbol]
            db_delete_position(symbol)
            return None
        logger.info(f"[EXIT] 🛑 SL HIT {symbol} @ ${real_price:,.2f} (SL=${pos['sl']:,.2f})")
        return "SL"
    
    # ── v2.0: Check Kijun TP (primary exit — dynamic target) ──
    kijun = calc_kijun(klines)
    if kijun > 0:
        if pos["action"] == "BUY" and real_price >= kijun and kijun > pos["entry"]:
            logger.info(
                f"[EXIT] 🎯 KIJUN TP {symbol} @ ${real_price:,.2f} | "
                f"Kijun=${kijun:,.2f} | Entry=${pos['entry']:,.2f} | "
                f"PnL={(real_price - pos['entry'])/pos['entry']*100:+.2f}%"
            )
            return "KIJUN_TP"
        elif pos["action"] == "SELL" and real_price <= kijun and kijun < pos["entry"]:
            logger.info(
                f"[EXIT] 🎯 KIJUN TP {symbol} @ ${real_price:,.2f} | "
                f"Kijun=${kijun:,.2f} | Entry=${pos['entry']:,.2f} | "
                f"PnL={(pos['entry'] - real_price)/pos['entry']*100:+.2f}%"
            )
            return "KIJUN_TP"
    
    # ── Check RSI exit (fallback — v2.0: secondary to Kijun TP) ──
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
    
    # ── Si close falla, verificar si BingX ya cerró la posición ──
    if not position_exists_on_exchange(symbol):
        logger.warning(f"[SYNC] {symbol} — close falló pero posición no existe en BingX. Limpiando local.")
        del _positions[symbol]
        db_delete_position(symbol)
    
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
        f"📊 Exit:    Kijun TP → RSI(2) {'60' if signal['action']=='BUY' else '40'} → SL\n"
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
        f"👻 <b>PHANTOM v2.1 iniciado</b>\n"
        f"{'━' * 24}\n"
        f"Estrategia: Mean-Reversion (RSI2 + Z-Score)\n"
        f"Trend: Counter-trend allowed (TK Cross filters)\n"
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
    global _daily_pnl, _daily_trades, _start_balance, _positions, _alerts
    
    # ── SQLite init + cargar estado sobreviviente ──
    init_db()
    _positions = db_load_positions()
    _alerts = db_load_alerts()
    
    if _positions:
        logger.info(f"[DB] Posiciones recuperadas: {list(_positions.keys())}")
        for sym, pos in _positions.items():
            logger.info(f"  → {sym} {pos['action']} entry=${pos['entry']:,.2f} sl=${pos['sl']:,.2f} qty={pos['qty']}")
    if _alerts:
        logger.info(f"[DB] Alerts recuperadas: {list(_alerts.keys())}")
        for sym, alt in _alerts.items():
            logger.info(f"  → {sym} {alt['action']} detected @ ${alt['price']:,.2f} | awaiting TK Cross")
    
    _start_balance = get_balance()
    logger.info("=" * 60)
    logger.info("PHANTOM v2.1 — Wino and Company")
    logger.info(f"Balance: ${_start_balance:,.2f}")
    logger.info(f"Activos: {CRYPTO_PAIRS} + {STOCK_SYMBOL}")
    logger.info(f"Estrategia: Mean-Reversion + TK Cross Confirmation")
    logger.info(f"Timeframe: {KLINE_TIMEFRAME} | Eval cada {EVAL_INTERVAL//60} min | SL ATR×{ATR_SL_MULT}")
    logger.info(f"Thresholds: RSI<{RSI_OVERSOLD}/{RSI_OVERBOUGHT}> | Z>{ZSCORE_THRESHOLD}σ | ADX<{ADX_THRESHOLD}")
    logger.info(f"Counter-trend: ALLOWED (TK Cross filters)")
    logger.info(f"Kijun gate: {KIJUN_GATE_PCT:.0%} max distance | TK Cross timeout: {ALERT_TIMEOUT_SECONDS//3600}h")
    logger.info(f"Exit priority: Kijun TP → RSI exit → SL")
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
                
                # ── 1. Check exits primero ──
                exit_reason = check_exit(symbol, klines, mark)
                if exit_reason:
                    close_crypto(symbol, exit_reason)
                    continue
                
                # ── 2. Check confirmation of pending alerts (Phase 2) ──
                if symbol in _alerts and len(_positions) < MAX_POSITIONS:
                    confirmed_signal = check_confirmation(symbol, klines, mark)
                    if confirmed_signal:
                        execute_crypto(confirmed_signal)
                        continue
                
                # ── 3. Check for new detections (Phase 1) ──
                if symbol not in _positions and symbol not in _alerts:
                    if len(_positions) < MAX_POSITIONS:
                        alert = evaluate(symbol, klines, mark)
                        if alert:
                            _alerts[symbol] = alert
                            db_save_alert(symbol, alert)
                            tg_send(
                                f"🔔 <b>ALERT Phase 1</b>\n"
                                f"{alert['action']} {symbol} @ ${alert['price']:,.2f}\n"
                                f"RSI={alert['rsi']:.1f} Z={alert['zscore']:+.2f}\n"
                                f"Score={alert['confidence']}/100\n"
                                f"⏳ Awaiting TK Cross confirmation..."
                            )
                
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
