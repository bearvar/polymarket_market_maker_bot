import os
import json
import asyncio
import logging
import signal
import time
import queue
import math
from logging.handlers import QueueHandler, QueueListener
from functools import partial
from decimal import Decimal, ROUND_DOWN, ROUND_CEILING, getcontext
from datetime import datetime, timedelta, timezone

from web3 import Web3

from py_builder_relayer_client.client import RelayClient
from py_builder_relayer_client.models import SafeTransaction 

try:
    from zoneinfo import ZoneInfo
except ImportError:
    print("CRITICAL: Python 3.9+ and 'zoneinfo' required.")
    exit(1)

try:
    import uvloop
    asyncio.set_event_loop_policy(uvloop.EventLoopPolicy())
except ImportError:
    pass

import aiohttp
from dotenv import load_dotenv

from py_clob_client.client import ClobClient
from py_clob_client.clob_types import OrderArgs, OrderType, PostOrdersArgs, BalanceAllowanceParams, AssetType, CreateOrderOptions, MarketOrderArgs, OpenOrderParams
from py_clob_client.order_builder.constants import BUY, SELL
from py_builder_signing_sdk.config import BuilderConfig, BuilderApiKeyCreds

# --- CONFIGURATION ---
getcontext().prec = 10
load_dotenv()

# --- CONSTANTS ---
HOST = "https://clob.polymarket.com"
WS_HOST = "wss://ws-subscriptions-clob.polymarket.com/ws/market"
CHAIN_ID = 137
GAMMA_HOST = "https://gamma-api.polymarket.com"
DATA_API_HOST = "https://data-api.polymarket.com"
RELAYER_HOST = "https://relayer-v2.polymarket.com"

# CTF & USDC Constants for Merging
CTF_EXCHANGE = "0x4D97DCd97eC945f40cF65F87097ACe5EA0476045"
USDC_ADDRESS = "0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174"

# --- STRATEGY SETTINGS ---
LADDER_LEVELS = 3
LADDER_STEP = Decimal("0.02")
TARGET_COMBINED_BID = Decimal("0.99")

# --- RISK MANAGEMENT ---
MIN_PRICE_THRESHOLD = Decimal("0.15") # цена одной из ставок ниже, прекращаем торговлю (только набираем хедж если нужно)
SIZE_SAFETY_BUFFER = Decimal("0.05")

SKEW_GUARD_THRESHOLD = Decimal("10")
EXPOSURE_THRESHOLD = Decimal("20")
PANIC_THRESHOLD = Decimal("30")
MAX_TOLERABLE_SUM = Decimal("1.025")    
KNIFE_CATCH_DISCOUNT = Decimal("0.04")  

# Cash Reserve
MIN_CASH_RESERVE = Decimal("50.0") # в долларах
DEPOSIT_LIMIT = Decimal(os.getenv("DEPOSIT_LIMIT", "0.15")) 

# --- MERGE SETTINGS ---
MERGE_THRESHOLD_AMOUNT = Decimal("10.0")

# --- TIME MANAGEMENT SETTINGS ---
STOP_TRADING_MINUTES_15M = 4  
STOP_TRADING_MINUTES_1H = 15

TARGET_ASSET = "SOL" 

# Карта имен для слагов (Hourly / 15m)
ASSET_SLUG_MAP = {
    "BTC": {"hourly": "bitcoin",  "15m": "btc"},
    "ETH": {"hourly": "ethereum", "15m": "eth"},
    "XRP": {"hourly": "xrp",      "15m": "xrp"},
    "SOL": {"hourly": "solana",   "15m": "sol"}
}

# --- ASYNC LOGGING SETUP ---
log_queue = queue.Queue()
queue_handler = QueueHandler(log_queue)

logger = logging.getLogger("Gabagool")
logger.setLevel(logging.DEBUG) 
logger.addHandler(queue_handler)

formatter = logging.Formatter('%(asctime)s - [Gabagool] - %(levelname)s - %(message)s')

file_handler = logging.FileHandler("bot_v8.log")
file_handler.setFormatter(formatter)
stream_handler = logging.StreamHandler()
stream_handler.setFormatter(formatter)

log_listener = QueueListener(log_queue, file_handler, stream_handler)

for lib in ["httpx", "hpack", "httpcore", "telegram", "aiohttp", "web3", "urllib3", "websockets"]:
    logging.getLogger(lib).setLevel(logging.WARNING)

# ------------------------------------------------------------------------------
# CLASS: RATE LIMITER
# ------------------------------------------------------------------------------
class RateLimiter:
    def __init__(self, rate_limit):
        self.rate = rate_limit
        self.tokens = rate_limit
        self.last_update = time.monotonic()
        self.lock = asyncio.Lock()

    async def acquire(self):
        async with self.lock:
            now = time.monotonic()
            elapsed = now - self.last_update
            self.last_update = now
            self.tokens += elapsed * self.rate
            if self.tokens > self.rate: self.tokens = self.rate
            
            if self.tokens >= 1:
                self.tokens -= 1
                return
            
            wait_time = (1 - self.tokens) / self.rate
            if wait_time > 0:
                await asyncio.sleep(wait_time)
                self.tokens = 0

# ------------------------------------------------------------------------------
# CLASS: MARKET STATE
# ------------------------------------------------------------------------------
class MarketState:
    def __init__(self):
        self.books = {}
        self.my_orders = {} 
        self.market_ready = False
    
    def init_market(self, t_yes, t_no):
        self.books[t_yes] = {'bids': {}, 'asks': {}}
        self.books[t_no] = {'bids': {}, 'asks': {}}
        self.my_orders[t_yes] = {}
        self.my_orders[t_no] = {}
        self.market_ready = True
        logger.debug("📘 MarketState initialized")

    def update_book(self, token_id, side, price_str, size_str):
        if token_id not in self.books: return
        price = Decimal(price_str)
        size = Decimal(size_str)
        book_side = 'bids' if side.upper() == 'BUY' else 'asks'
        if size == 0:
            self.books[token_id][book_side].pop(price, None)
        else:
            self.books[token_id][book_side][price] = size

    def get_market_levels(self, token_id):
        if token_id not in self.books: return Decimal("0"), Decimal("1")
        bids = sorted(self.books[token_id]['bids'].keys(), reverse=True)
        asks = sorted(self.books[token_id]['asks'].keys())
        bb = bids[0] if bids else Decimal("0")
        ba = asks[0] if asks else Decimal("1")
        return bb, ba

    def get_locked_funds(self):
        total_locked = Decimal("0")
        for token_id in self.my_orders:
            for order_id, info in self.my_orders[token_id].items():
                p = info['price']
                s = info['size']
                total_locked += (p * s)
        return total_locked

# ------------------------------------------------------------------------------
# BOT CLASS
# ------------------------------------------------------------------------------
class GabagoolV8:
    def __init__(self):
        self.builder_config = self._init_builder_config()
        self.client = self._init_clob_client()
        self.relayer = self._init_relayer_client()
        
        self.state = MarketState()
        self.stop_event = asyncio.Event()
        self.current_market = None
        
        self.pos_yes = Decimal("0")
        self.pos_no = Decimal("0")
        self.avg_price_yes = Decimal("0")
        self.avg_price_no = Decimal("0")
        
        self.usdc_balance = Decimal("0")
        self.portfolio_value = Decimal("0")
        self.deposit_usage = Decimal("0")
        
        self.last_buy_price = {} 
        
        self.last_hedge_ts = 0
        self.last_opp_log_ts = 0 
        
        self.last_usdc = None
        self.last_pos_yes = None
        self.last_pos_no = None
        self.last_log_ts = 0
        
        self.spend_accumulator = Decimal("0")
        self.pos_lock = asyncio.Lock()
        
        self.orders_lock = asyncio.Lock()
        
        self.zombie_candidates = {} 
        
        self.last_ws_update_ts = 0.0
        
        self.market_slug = ""
        self.creds = None
        self.logic_event = asyncio.Event()
        
        self.tx_limiter = RateLimiter(50) 
        self.data_limiter = RateLimiter(10)
        
        self.market_type_env = os.getenv("MARKET_TYPE", "1h").lower()
        self.proxy_address = os.getenv("POLY_PROXY_ADDRESS")
        self.session = None
        
        self.shutdown_task = None

    def _init_builder_config(self):
        b_key = os.getenv("POLY_BUILDER_API_KEY")
        b_secret = os.getenv("POLY_BUILDER_SECRET")
        b_pass = os.getenv("POLY_BUILDER_PASSPHRASE")
        
        if b_key:
            return BuilderConfig(
                local_builder_creds=BuilderApiKeyCreds(
                    key=b_key, secret=b_secret, passphrase=b_pass
                )
            )
        return None

    def _init_clob_client(self):
        pk = os.getenv("PRIVATE_KEY")
        funder = os.getenv("POLY_PROXY_ADDRESS") 
        return ClobClient(
            HOST, key=pk, chain_id=CHAIN_ID, signature_type=2, funder=funder, builder_config=self.builder_config
        )

    def _init_relayer_client(self):
        if not self.builder_config:
            logger.warning("⚠️ Builder config missing. Merging will NOT work.")
            return None
            
        pk = os.getenv("PRIVATE_KEY")
        try:
            return RelayClient(
                RELAYER_HOST, 
                CHAIN_ID, 
                pk, 
                self.builder_config
            )
        except Exception as e:
            logger.error(f"❌ Failed to init Relayer: {e}")
            return None

    async def _run_sync(self, func, *args, **kwargs):
        loop = asyncio.get_running_loop()
        try:
            res = await loop.run_in_executor(None, partial(func, *args, **kwargs))
            return res
        except Exception as e:
            raise e

    def _update_avg_price(self, token_id, new_size, new_price):
        """Пересчитывает среднюю цену входа"""
        is_yes = (token_id == self.current_market['token_yes'])
        
        current_pos = self.pos_yes if is_yes else self.pos_no
        current_avg = self.avg_price_yes if is_yes else self.avg_price_no
        
        if current_pos <= 0:
            new_avg = new_price
        else:
            total_cost = (current_pos * current_avg) + (new_size * new_price)
            total_qty = current_pos + new_size
            new_avg = total_cost / total_qty
            
        if is_yes:
            self.avg_price_yes = new_avg
        else:
            self.avg_price_no = new_avg

    async def merge_worker(self):
        """
        Умный Merge Worker.
        FIX V8.13: Исправлена обработка результата.
        Метод .wait() возвращает словарь, а не объект.
        Добавлена универсальная проверка хеша (dict keys или attribute).
        """
        logger.info("twisted_rightwards_arrows Smart Merge Worker Started")
        
        if not self.relayer:
            logger.error("⛔ Relayer not initialized. Merge worker stopped.")
            return

        # "Обманка" для Relayer API (int для JSON, object.value для Python)
        class PseudoEnum(int):
            @property
            def value(self):
                return self

        ctf_abi = [{
            "name": "mergePositions",
            "type": "function",
            "inputs": [
                {"name": "collateralToken", "type": "address"},
                {"name": "parentCollectionId", "type": "bytes32"},
                {"name": "conditionId", "type": "bytes32"},
                {"name": "partition", "type": "uint256[]"},
                {"name": "amount", "type": "uint256"}
            ],
            "outputs": []
        }]

        while not self.stop_event.is_set():
            await asyncio.sleep(30) 

            if not self.current_market or not self.state.market_ready:
                continue

            try:
                async with self.pos_lock:
                    pos_yes = self.pos_yes
                    pos_no = self.pos_no
                    usage = self.deposit_usage 
                
                common_shares = min(pos_yes, pos_no).quantize(Decimal("1"), rounding=ROUND_DOWN)
                
                if common_shares < MERGE_THRESHOLD_AMOUNT:
                    continue

                net_exposure = abs(pos_yes - pos_no)
                if net_exposure > EXPOSURE_THRESHOLD:
                    logger.info(f"⏳ Merge hold: Stabilizing... Net exposure {net_exposure:.1f} > {EXPOSURE_THRESHOLD}")
                    continue

                logger.info(f"🔋 MERGE TRIGGERED: Found {common_shares} sets. Usage was {usage:.1%}. Executing...")

                partition = [1, 2] 
                amount_wei = int(common_shares * 1000000) 
                condition_id_bytes = self.current_market['condition_id']
                
                # Инициализация Web3 (оффлайн)
                w3 = Web3()
                contract = w3.eth.contract(address=CTF_EXCHANGE, abi=ctf_abi)
                
                # Кодируем данные
                data_payload = contract.encode_abi(
                    "mergePositions",
                    args=[
                        USDC_ADDRESS,
                        "0x" + "0"*64, 
                        condition_id_bytes,
                        partition,
                        amount_wei
                    ]
                )

                # Создаем транзакцию
                transaction = SafeTransaction(
                    to=CTF_EXCHANGE,
                    data=data_payload,
                    value="0",              
                    operation=PseudoEnum(0) 
                )

                def execute_relay():
                    tx_resp = self.relayer.execute([transaction], "Smart Merge V8.13")
                    return tx_resp.wait()

                result = await self._run_sync(execute_relay)

                # --- FIX: Безопасное извлечение хеша ---
                tx_hash = None
                if isinstance(result, dict):
                    # Пробуем разные варианты ключей (snake_case или camelCase)
                    tx_hash = result.get('transactionHash') or result.get('transaction_hash')
                elif hasattr(result, 'transaction_hash'):
                    tx_hash = result.transaction_hash
                elif hasattr(result, 'transactionHash'):
                    tx_hash = result.transactionHash
                # ---------------------------------------

                if tx_hash:
                    # Конвертируем HexBytes в строку, если нужно
                    if not isinstance(tx_hash, str):
                        tx_hash = tx_hash.hex()

                    logger.info(f"✅ MERGE COMPLETE! Freed {common_shares} USDC. Tx: {tx_hash}")
                    
                    async with self.pos_lock:
                        self.pos_yes -= common_shares
                        self.pos_no -= common_shares
                        self.usdc_balance += common_shares
                        self.portfolio_value -= common_shares 
                    
                    logger.info(f"📉 Reloading... New Pos: {self.pos_yes}/{self.pos_no}, Balance increased.")
                else:
                    logger.warning(f"⚠️ Merge transaction finished but no hash found. Result: {result}")

            except Exception as e:
                error_details = str(e)
                if hasattr(e, 'response') and e.response:
                    try:
                        error_details += f" Body: {e.response.text}"
                    except: pass
                logger.error(f"❌ Smart Merge Error: {error_details}")

    async def graceful_shutdown(self):
        self.stop_event.set() 
        logger.warning("\n\n🚨 EMERGENCY SHUTDOWN SEQUENCE STARTED...")
        
        if not self.current_market:
            logger.info("👋 No active market to dump. Exiting.")
            return

        logger.info("🗑️ (1/3) Cancelling ALL open orders...")
        try:
            await self._run_sync(
                self.client.cancel_market_orders, 
                market=self.current_market['condition_id']
            )
            async with self.orders_lock:
                self.state.my_orders.clear()
        except Exception as e:
            logger.error(f"Cancel failed: {e}")

        logger.info("💸 (2/3) Starting MARKET DUMP LOOP (Max 5 attempts)...")
        t1, t2 = self.current_market['token_yes'], self.current_market['token_no']
        
        async def dump_token_market(token_id, size):
            if size < Decimal("1.0"): return 
            try:
                args = MarketOrderArgs(
                    token_id=token_id,
                    amount=float(size), # Shares
                    side=SELL
                )
                signed = await self._run_sync(self.client.create_market_order, args)
                resp = await self._run_sync(self.client.post_order, signed, OrderType.FAK)
                logger.info(f"✅ DUMPED {size} shares of {token_id[:10]}... Resp: {resp.get('orderID')}")
            except Exception as e:
                logger.error(f"❌ DUMP FAILED for {token_id}: {e}")

        for i in range(5):
            try:
                res = await asyncio.gather(
                    self._run_sync(self.client.get_balance_allowance, BalanceAllowanceParams(asset_type=AssetType.CONDITIONAL, token_id=t1)),
                    self._run_sync(self.client.get_balance_allowance, BalanceAllowanceParams(asset_type=AssetType.CONDITIONAL, token_id=t2))
                )
                curr_yes = Decimal(res[0]['balance']) / Decimal("1000000")
                curr_no = Decimal(res[1]['balance']) / Decimal("1000000")
                
                logger.info(f"🔄 Attempt {i+1}: Holding YES={curr_yes:.1f}, NO={curr_no:.1f}")
                
                if curr_yes < 1 and curr_no < 1:
                    logger.info("✨ Positions successfully cleared.")
                    break
                
                tasks = []
                if curr_yes >= 1: tasks.append(dump_token_market(t1, curr_yes))
                if curr_no >= 1: tasks.append(dump_token_market(t2, curr_no))
                
                if tasks:
                    await asyncio.gather(*tasks)
                
                await asyncio.sleep(2)
                
            except Exception as e:
                logger.error(f"Dump loop error: {e}")
                await asyncio.sleep(1)

        logger.info("💀 SHUTDOWN COMPLETE. Safe to exit.")

    async def ws_loop(self):
        logger.info("🎬 Entering WS Loop...")
        while not self.stop_event.is_set():
            if not self.current_market or not self.creds or not self.session:
                await asyncio.sleep(1)
                continue
            
            current_cond_id = self.current_market['condition_id']
            
            try:
                user_auth = {
                    "apiKey": self.creds.api_key,
                    "secret": self.creds.api_secret,
                    "passphrase": self.creds.api_passphrase
                }
                
                async with self.session.ws_connect(WS_HOST) as ws:
                    logger.info("🔌 WS Connected")
                    await ws.send_json({
                        "assets_ids": [self.current_market['token_yes'], self.current_market['token_no']], 
                        "type": "market"
                    })
                    await ws.send_json({
                        "type": "user",
                        "auth": user_auth,
                        "markets": [self.current_market['condition_id']]
                    })
                    
                    async for msg in ws:
                        if self.stop_event.is_set(): break
                        
                        if self.current_market['condition_id'] != current_cond_id:
                            logger.info("🔄 Market switched! Restarting WS for new tokens...")
                            break 
                        
                        if msg.type == aiohttp.WSMsgType.TEXT:
                            if not msg.data: continue 
                            try:
                                raw_data = json.loads(msg.data)
                            except json.JSONDecodeError: continue

                            if isinstance(raw_data, list):
                                items = raw_data
                            elif isinstance(raw_data, dict):
                                items = [raw_data]
                            else:
                                continue

                            for data in items:
                                if not isinstance(data, dict): continue
                                
                                event_type = data.get("event_type")

                                if event_type == "book":
                                    asset_id = data.get('asset_id')
                                    if asset_id and asset_id in self.state.books:
                                        self.state.books[asset_id] = {'bids': {}, 'asks': {}}

                                    for b in data.get('bids', []): 
                                        self.state.update_book(data['asset_id'], 'BUY', b['price'], b['size'])
                                    for a in data.get('asks', []): 
                                        self.state.update_book(data['asset_id'], 'SELL', a['price'], a['size'])
                                    self._trigger_logic()

                                elif event_type == "price_change":
                                    changes = data.get("price_changes", []) or data.get("changes", [])
                                    for ch in changes:
                                        aid = ch.get('asset_id', data.get('asset_id'))
                                        self.state.update_book(aid, ch['side'], ch['price'], ch['size'])
                                    self._trigger_logic()
                                
                                elif event_type == "trade" and data.get("status") == "MATCHED":
                                    await self.process_ws_trade(data)
                        
                                elif event_type == "order":
                                    status = data.get("status")
                                    if status in ["CANCELED", "KILLED", "FILLED"]:
                                        oid = data.get("id") or data.get("orderID")
                                        asset_id = data.get("asset_id")
                                        
                                        if oid and asset_id:
                                            async with self.orders_lock:
                                                if asset_id in self.state.my_orders:
                                                    if oid in self.state.my_orders[asset_id]:
                                                        del self.state.my_orders[asset_id][oid]
                                                        logger.info(f"⚡ WS Fast Remove: Order {oid} is {status}")
                        
                        elif msg.type == aiohttp.WSMsgType.PING:
                            await ws.pong()
            
            except Exception as e: 
                if not self.stop_event.is_set():
                    logger.error(f"❌ WS Exception: {e}")
                    await asyncio.sleep(2)

    async def process_ws_trade(self, data):
        try:
            maker_orders = data.get("maker_orders", [])
            for mo in maker_orders:
                filled_size = Decimal(mo.get("matched_amount", "0"))
                asset_id = mo.get("asset_id")
                price = Decimal(mo.get("price", "0"))
                cost = filled_size * price
                
                order_side = mo.get("side", "").upper()
                if order_side == "BUY":
                    self.last_buy_price[asset_id] = price
                    self._update_avg_price(asset_id, filled_size, price)

                async with self.pos_lock:
                    if asset_id == self.current_market['token_yes']:
                        self.pos_yes += filled_size
                        self.usdc_balance -= cost
                    elif asset_id == self.current_market['token_no']:
                        self.pos_no += filled_size
                        self.usdc_balance -= cost
                    
                    self.last_ws_update_ts = time.time()
                    logger.info(f"⚡ FAST UPDATE: Filled {filled_size} {asset_id[:5]}... Price {price}, New Bal: {self.usdc_balance:.2f}")

        except Exception as e:
            logger.error(f"WS Trade Parse Error: {e}")

    def _trigger_logic(self):
        if self.state.market_ready:
            self.logic_event.set()

    async def logic_worker(self):
        logger.info("👷 Logic Worker Started")
        while not self.stop_event.is_set():
            try:
                await asyncio.wait_for(self.logic_event.wait(), timeout=10.0)
                self.logic_event.clear()
                if not self.stop_event.is_set():
                    await self.trading_iteration()
            except asyncio.TimeoutError:
                if self.state.market_ready and not self.stop_event.is_set():
                    await self.trading_iteration()

    async def trading_iteration(self):
        try:
            # 1. Получаем текущее состояние и настройки времени
            stop_buffer = STOP_TRADING_MINUTES_1H if self.market_type_env == '1h' else STOP_TRADING_MINUTES_15M
            time_left = self.current_market['expiry_ts'] - time.time()
            is_stop_time = time_left < (stop_buffer * 60)
            
            now = time.time()
            verbose = (now - self.last_log_ts) > 10 

            # 2. Получаем текущую позицию
            async with self.pos_lock:
                current_net = self.pos_yes - self.pos_no
                
            # 3. Taker Hedge (Экстренный сброс) - работает всегда первым
            hedge_triggered = await self.execute_taker_hedge(verbose)
            if hedge_triggered:
                if verbose: 
                    logger.info("⚠️ Hedge active. Skipping maker orders update.")
                    self.last_log_ts = now 
                return

            # 4. Инициализация флагов (по умолчанию торгуем все)
            allow_buy_yes = True
            allow_buy_no = True

            # --- ЛОГИКА ОСТАНОВКИ ПО ВРЕМЕНИ ---
            if is_stop_time:
                if abs(current_net) < Decimal("1.0"):
                    if verbose:
                        self.last_log_ts = now
                        logger.info(f"⏳ Market ending in {time_left/60:.1f}m. Position Clean. Stopping.")
                    async with self.orders_lock:
                        if self.state.my_orders:
                            await self.tx_limiter.acquire()
                            await self._run_sync(
                                self.client.cancel_market_orders, 
                                market=self.current_market['condition_id']
                            )
                            self.state.my_orders.clear()
                    return
                else:
                    # Close-Only Mode (Time)
                    if verbose:
                        self.last_log_ts = now
                        logger.info(f"🛡️ Time Close-Only: Net={current_net:.1f}. Placing LIMIT HEDGE orders only.")
                    
                    if current_net > 0:
                        allow_buy_yes = False 
                        allow_buy_no = True   
                    else:
                        allow_buy_yes = True
                        allow_buy_no = False

            # Получаем цены стакана
            t_yes = self.current_market['token_yes']
            t_no = self.current_market['token_no']
            y_bid, y_ask = self.state.get_market_levels(t_yes)
            n_bid, n_ask = self.state.get_market_levels(t_no)

            # --- ЛОГИКА НИЗКОЙ ЦЕНЫ (FIX) ---
            # Проверяем цены только если мы еще не в режиме Stop-Time (там свои правила)
            if not is_stop_time:
                is_price_low = (y_bid <= MIN_PRICE_THRESHOLD and y_bid > 0) or \
                               (n_bid <= MIN_PRICE_THRESHOLD and n_bid > 0)

                if is_price_low:
                    # Сценарий А: Позиции нет -> Полный стоп (безопасно)
                    if abs(current_net) < Decimal("1.0"):
                        if verbose:
                            self.last_log_ts = now
                            logger.warning(f"📉 Price too low (<= {MIN_PRICE_THRESHOLD}). No Position. Halting.")
                        async with self.orders_lock:
                            if self.state.my_orders:
                                await self.tx_limiter.acquire()
                                await self._run_sync(self.client.cancel_market_orders, market=self.current_market['condition_id'])
                                self.state.my_orders.clear()
                        return
                    
                    # Сценарий Б: Позиция ЕСТЬ -> Игнорируем низкую цену, включаем Close-Only
                    else:
                        if verbose:
                            self.last_log_ts = now
                            logger.warning(f"📉 Price Low but Net Exposure {current_net:.1f}. FORCING HEDGE MODE.")
                        
                        # Принудительно выставляем флаги на закрытие
                        if current_net > 0:
                            # У нас лонг YES, надо покупать NO (даже если цена странная)
                            allow_buy_yes = False
                            allow_buy_no = True
                        else:
                            # У нас лонг NO, надо покупать YES
                            allow_buy_yes = True
                            allow_buy_no = False

            if (y_bid == 0 and y_ask == 1) or (n_bid == 0 and n_ask == 1):
                return

            # Расчет размера
            ref_price_y = y_bid if y_bid > Decimal("0") else Decimal("0.5")
            ref_price_n = n_bid if n_bid > Decimal("0") else Decimal("0.5")
            raw_min_price = min(ref_price_y, ref_price_n)
            
            calc_price = raw_min_price - SIZE_SAFETY_BUFFER
            if calc_price < Decimal("0.01"): calc_price = Decimal("0.01")
            
            raw_shares = Decimal("1.3") / calc_price
            current_size = Decimal(math.ceil(raw_shares))
            if current_size < Decimal("5"): current_size = Decimal("5")
            
            if verbose:
                self.last_log_ts = now
                mode_str = "NORMAL"
                if not allow_buy_yes: mode_str = "HEDGE-NO-ONLY"
                if not allow_buy_no: mode_str = "HEDGE-YES-ONLY"
                logger.info(f"👀 Snap ({mode_str}): Y[{y_bid}/{y_ask}] N[{n_bid}/{n_ask}] | Pos: {self.pos_yes:.0f}/{self.pos_no:.0f}")

            # 5. Расчет лестниц
            lad_y = []
            lad_n = []

            if allow_buy_yes:
                lad_y = self.calculate_ladder(t_yes, True, n_bid, verbose)
            
            if allow_buy_no:
                lad_n = self.calculate_ladder(t_no, False, y_bid, verbose)

            # 6. SPREAD COLLISION CHECK
            if lad_y and lad_n:
                top_y = lad_y[0]
                top_n = lad_n[0]
                combined = top_y + top_n
                
                if combined > TARGET_COMBINED_BID:
                    diff = combined - TARGET_COMBINED_BID
                    async with self.pos_lock:
                        p_y = self.pos_yes
                        p_n = self.pos_no

                    reduce_yes = False
                    if p_y > p_n: reduce_yes = True
                    elif p_n > p_y: reduce_yes = False
                    else: reduce_yes = (top_y > top_n)
                    
                    if reduce_yes:
                        lad_y = [p - diff for p in lad_y if (p - diff) > 0]
                    else:
                        lad_n = [p - diff for p in lad_n if (p - diff) > 0]

            # 7. Проверка средств
            can_trade, fail_reason = await self.check_combined_risk_and_funds(lad_y, lad_n, current_size)

            if not can_trade:
                if verbose: 
                    self.last_log_ts = now
                    logger.warning(f"🛑 TRADING HALTED: {fail_reason}. Cancelling existing orders.")
                async with self.orders_lock:
                    if self.state.my_orders:
                        await self.tx_limiter.acquire()
                        await self._run_sync(
                            self.client.cancel_market_orders, 
                            market=self.current_market['condition_id']
                        )
                        self.state.my_orders.clear()
                return

            # 8. Отправка ордеров
            await asyncio.gather(
                self.manage_orders(t_yes, lad_y, True, current_size),
                self.manage_orders(t_no, lad_n, False, current_size)
            )

        except Exception as e:
            logger.exception(f"🔥 Logic Iteration Crashed: {e}")

    async def check_combined_risk_and_funds(self, lad_y, lad_n, size_per_order):
        async with self.pos_lock:
            async with self.orders_lock:
                current_locked = self.state.get_locked_funds()
            
            cost_y = sum([p * size_per_order for p in lad_y])
            cost_n = sum([p * size_per_order for p in lad_n])
            total_new_cost = cost_y + cost_n
            
            available_for_maker = self.usdc_balance + current_locked - MIN_CASH_RESERVE
            
            if available_for_maker < total_new_cost:
                return False, f"Insufficient funds. Need {total_new_cost:.2f}, Avail {available_for_maker:.2f}"
            
            total_equity = self.usdc_balance + self.portfolio_value
            if total_equity > 0:
                proj_exposure = self.portfolio_value + total_new_cost
                proj_usage = proj_exposure / total_equity
                if proj_usage > DEPOSIT_LIMIT:
                    return False, f"Deposit Limit Exceeded: {proj_usage:.1%} > {DEPOSIT_LIMIT:.1%}"

            return True, "OK"

    async def update_money_stats(self):
        if not self.session: return
        request_start_time = time.time()
        
        try:
            await self.data_limiter.acquire()
            collateral_resp = await self._run_sync(
                self.client.get_balance_allowance, 
                BalanceAllowanceParams(asset_type=AssetType.COLLATERAL)
            )
            usdc = Decimal(collateral_resp['balance']) / Decimal("1000000")

            async with self.session.get(f"{DATA_API_HOST}/value", params={"user": self.proxy_address}) as resp:
                data = await resp.json()
                p_value = Decimal(str(data[0].get('value', 0))) if (data and isinstance(data, list)) else Decimal("0")

            async with self.pos_lock:
                if self.last_ws_update_ts > request_start_time:
                    return 

                self.usdc_balance = usdc
                self.portfolio_value = p_value
                self.spend_accumulator = Decimal("0")
                total_equity = self.usdc_balance + self.portfolio_value
                self.deposit_usage = (self.portfolio_value / total_equity) if total_equity > 0 else Decimal("0")
            
            if self.last_usdc is None or abs(self.usdc_balance - self.last_usdc) > Decimal("0.001"):
                logger.info(f"💰 Balance API Sync: USDC={self.usdc_balance:.2f} | Portf={self.portfolio_value:.2f}")
                self.last_usdc = self.usdc_balance

        except Exception as e:
            logger.debug(f"Money sync warning: {e}")

    async def background_balance_sync(self):
        logger.info("🔄 Background Balance Sync Started")
        while not self.stop_event.is_set():
            await self.update_money_stats()

            if self.current_market:
                request_start_time = time.time()
                
                if (time.time() - self.last_hedge_ts) < 20.0:
                    logger.debug("🛡️ Skipping Pos Sync (Trusting local state after hedge)")
                    await asyncio.sleep(2)
                    continue
                
                try:
                    t1, t2 = self.current_market['token_yes'], self.current_market['token_no']
                    res = await asyncio.gather(
                        self._run_sync(self.client.get_balance_allowance, BalanceAllowanceParams(asset_type=AssetType.CONDITIONAL, token_id=t1)),
                        self._run_sync(self.client.get_balance_allowance, BalanceAllowanceParams(asset_type=AssetType.CONDITIONAL, token_id=t2))
                    )
                    
                    async with self.pos_lock:
                        if self.last_ws_update_ts > request_start_time:
                            logger.warning("⚔️ Race Condition in Pos Sync! WS is newer. Skipping REST update.")
                        else:
                            self.pos_yes = Decimal(res[0]['balance']) / Decimal("1000000")
                            self.pos_no = Decimal(res[1]['balance']) / Decimal("1000000")
                    
                    changed = False
                    if self.last_pos_yes is None or self.last_pos_yes != self.pos_yes: changed = True
                    if self.last_pos_no is None or self.last_pos_no != self.pos_no: changed = True
                    
                    if changed:
                        logger.info(f"📊 Positions API Sync: YES={self.pos_yes:.1f} | NO={self.pos_no:.1f} | Net={self.pos_yes - self.pos_no:.1f}")
                        self.last_pos_yes = self.pos_yes
                        self.last_pos_no = self.pos_no
                        
                except Exception as e:
                    logger.error(f"Pos Sync Err: {e}")
            
            await asyncio.sleep(5)

    async def reconcile_orders(self):
        if not self.current_market or not self.state.market_ready: return
        try:
            await self.data_limiter.acquire()
            
            params = OpenOrderParams(market=self.current_market['condition_id'])
            open_orders = await self._run_sync(self.client.get_orders, params=params)
            
            real_order_ids = set()
            for o in open_orders:
                oid = o.get('id') or o.get('orderID')
                if oid: real_order_ids.add(oid)

            local_removed_count = 0
            token_ids = [self.current_market['token_yes'], self.current_market['token_no']]
            
            now = time.time()

            async with self.orders_lock:
                for token_id in token_ids:
                    if token_id not in self.state.my_orders:
                        continue
                        
                    current_local_ids = list(self.state.my_orders[token_id].keys())
                    
                    for oid in current_local_ids:
                        if oid not in real_order_ids:
                            order_info = self.state.my_orders[token_id][oid]
                            created_at = order_info.get('created_at', 0)
                            
                            if (now - created_at) > 15.0:
                                del self.state.my_orders[token_id][oid]
                                local_removed_count += 1
                
                if local_removed_count > 0:
                    logger.debug(f"🧹 Reconciler clean-up: {local_removed_count} stale orders.")

                local_known_ids = set()
                for token_id in self.state.my_orders:
                    local_known_ids.update(self.state.my_orders[token_id].keys())
            
            unknown_on_exchange = []
            for o in open_orders:
                oid = o.get('id') or o.get('orderID')
                asset_id = o.get('asset_id')
                if oid and asset_id in token_ids:
                    if oid not in local_known_ids:
                        unknown_on_exchange.append(oid)

            zombies_to_cancel = []
            for oid in unknown_on_exchange:
                if oid not in self.zombie_candidates:
                    self.zombie_candidates[oid] = now
                elif (now - self.zombie_candidates[oid]) > 10: 
                    zombies_to_cancel.append(oid)

            current_unknown_set = set(unknown_on_exchange)
            for oid in list(self.zombie_candidates.keys()):
                if oid not in current_unknown_set:
                    del self.zombie_candidates[oid]

            if zombies_to_cancel:
                logger.warning(f"🧟 Zombie Guard: Killing {len(zombies_to_cancel)} unknown orders.")
                await self.tx_limiter.acquire()
                await self._run_sync(self.client.cancel_orders, zombies_to_cancel)

        except Exception as e:
            logger.error(f"Reconcile Error: {e}")

    async def reconcile_worker(self):
        logger.info("👮 Reconcile Worker Started")
        while not self.stop_event.is_set():
            await asyncio.sleep(5) 
            await self.reconcile_orders()

    async def execute_taker_hedge(self, verbose=False):
        async with self.pos_lock:
            net = self.pos_yes - self.pos_no
            avail_usdc = self.usdc_balance
            usage = self.deposit_usage
            
            async with self.orders_lock:
                locked_funds = self.state.get_locked_funds()
        
        if net == 0: return False

        if net > 0: 
            token_buy = self.current_market['token_no']
            opp_token = self.current_market['token_yes'] 
        else: 
            token_buy = self.current_market['token_yes']
            opp_token = self.current_market['token_no']
            
        _, ba_hedge = self.state.get_market_levels(token_buy)
        bb_hold, _ = self.state.get_market_levels(opp_token)

        async with self.orders_lock:
            existing_hedge_orders = self.state.my_orders.get(token_buy, {})
        
        if existing_hedge_orders:
            stale_orders = []
            for oid, info in existing_hedge_orders.items():
                oprice = info['price']
                if oprice < (ba_hedge - Decimal("0.03")):
                    stale_orders.append(oid)
            
            if stale_orders:
                logger.warning(f"🧹 Clearing {len(stale_orders)} stale orders blocking hedge... (Price {list(existing_hedge_orders.values())[0]['price']} vs Market {ba_hedge})")
                try:
                    await self.tx_limiter.acquire()
                    await self._run_sync(self.client.cancel_orders, stale_orders)
                    
                    async with self.orders_lock:
                        for oid in stale_orders:
                            if oid in self.state.my_orders.get(token_buy, {}):
                                del self.state.my_orders[token_buy][oid]
                except Exception as e:
                    logger.error(f"Failed to clear stale hedge blockers: {e}")
                return True

            if verbose:
                logger.info(f"⏳ Hedge active: Found {len(existing_hedge_orders)} pending orders. Waiting...")
            return True
        
        last_entry_price = self.last_buy_price.get(opp_token)
        force_profit_hedge = False
        
        if last_entry_price:
            lock_cost = last_entry_price + ba_hedge
            # Проверяем, есть ли гарантированная прибыль
            if lock_cost < Decimal("0.98"):
                if (time.time() - self.last_opp_log_ts) > 2.0: # FIX: Анти-спам таймер (не чаще раз в 2 сек)
                    logger.info(f"💎 OPPORTUNITY: Entry({last_entry_price}) + Hedge({ba_hedge}) = {lock_cost}. FORCING HEDGE!")
                    self.last_opp_log_ts = time.time()
                
                force_profit_hedge = True

        # --- FIX: BYPASS THRESHOLD IF DEPOSIT FULL ---
        is_deposit_critical = usage > (DEPOSIT_LIMIT * Decimal("0.85")) # Если заполнено >85%, хеджируем принудительно
        
        if not force_profit_hedge and not is_deposit_critical and abs(net) < EXPOSURE_THRESHOLD: 
            return False
        # ---------------------------------------------

        sum_price = ba_hedge + bb_hold
        is_panic = abs(net) > PANIC_THRESHOLD
        
        spread_is_safe = sum_price <= MAX_TOLERABLE_SUM
        
        if is_panic or force_profit_hedge or is_deposit_critical:
            if verbose and is_panic: logger.warning("🔥 PANIC MODE: Ignoring spread checks!")
            spread_is_safe = True 
            exec_price = ba_hedge + Decimal("0.05") 
        else:
            exec_price = ba_hedge + Decimal("0.02") 

        if exec_price > Decimal("0.99"): exec_price = Decimal("0.99")
        
        est_cost = abs(net) * exec_price

        if spread_is_safe:
            funds_needed_diff = est_cost - avail_usdc
            
            if funds_needed_diff > 0:
                if (avail_usdc + locked_funds) >= est_cost:
                    logger.warning("🚨 EMERGENCY: CANCELLING ORDERS TO FUND HEDGE!")
                    try:
                        await self.tx_limiter.acquire()
                        await self._run_sync(
                            self.client.cancel_market_orders,
                            market=self.current_market['condition_id']
                        )
                        async with self.orders_lock:
                            self.state.my_orders.clear()
                        await asyncio.sleep(0.5) 
                        return True 
                    except Exception as e:
                        logger.error(f"Emergency cancel failed: {e}")
                        await asyncio.sleep(1)
                        return True
                else:
                    logger.error(f"❌ CRITICAL: Insufficient funds. Need {est_cost}, Have {avail_usdc + locked_funds}")
                    return True

            try:
                size_exec = abs(net).quantize(Decimal("1"), rounding=ROUND_DOWN)
                if size_exec < 1: return False

                args = OrderArgs(price=float(exec_price), size=float(size_exec), side=BUY, token_id=token_buy)
                options = CreateOrderOptions(neg_risk=self.current_market['neg_risk'], tick_size="0.01")
                
                logger.info(f"🚀 EXECUTING HEDGE: Buy {size_exec} {token_buy[:10]} @ {exec_price}")
                
                signed = await self._run_sync(self.client.create_order, args, options)
                
                await self.tx_limiter.acquire()
                resp = await self._run_sync(self.client.post_order, signed, OrderType.GTC)
                
                async with self.pos_lock:
                    self.last_hedge_ts = time.time()
                    self._update_avg_price(token_buy, size_exec, exec_price)
                    
                    cost_spent = size_exec * exec_price
                    self.usdc_balance -= cost_spent
                    
                    if token_buy == self.current_market['token_yes']:
                        self.pos_yes += size_exec
                    else:
                        self.pos_no += size_exec
                    
                    self.last_ws_update_ts = time.time()
                    
                    if resp.get('success'):
                        oid = resp.get('orderID') or resp.get('id')
                        if oid:
                            self.last_buy_price[token_buy] = exec_price
                            async with self.orders_lock:
                                self.state.my_orders.setdefault(token_buy, {})[oid] = {
                                    'price': exec_price, 
                                    'size': size_exec,
                                    'created_at': time.time()
                                }
                
                await asyncio.sleep(0.5) 
                return True
            except Exception as e:
                err_msg = str(e)
                if "not enough balance" in err_msg:
                    logger.error(f"📉 Hedge failed: Not enough balance.")
                    await asyncio.sleep(1)
                else:
                    logger.error(f"Taker err: {e}")
                    await asyncio.sleep(1)
                return True
        
        return False

    def calculate_ladder(self, token_id, is_yes, opp_best_bid, verbose=False):
        """
        UPDATED V9.1: Fix NameError (now -> time.time())
        """
        side_str = "YES" if is_yes else "NO"
        bb_me, ba_me = self.state.get_market_levels(token_id)

        p_yes, p_no = self.pos_yes, self.pos_no
        net = p_yes - p_no
        
        i_am_heavy = (is_yes and net > EXPOSURE_THRESHOLD) or (not is_yes and net < -EXPOSURE_THRESHOLD)

        if i_am_heavy and abs(net) > SKEW_GUARD_THRESHOLD:
            if verbose: logger.info(f"🛑 {side_str}: Skew Guard Active (Net={net:.1f}). STOP BUYING.")
            return []

        # 1. Базовая логика
        ideal = bb_me + Decimal("0.01")
        
        # 2. Не встаем выше аска
        if ideal >= ba_me: 
            ideal = bb_me 
            if ideal >= ba_me:
                ideal = ba_me - Decimal("0.01")

        # 3. 🔥 Ограничение по сумме бидов (TARGET_COMBINED_BID)
        if opp_best_bid > 0:
            max_allowed = TARGET_COMBINED_BID - opp_best_bid
            if ideal > max_allowed:
                # FIX: Заменили 'now' на 'time.time()'
                if verbose and (time.time() - self.last_log_ts) > 10: 
                     logger.info(f"📉 {side_str} Capped by Spread: {ideal} -> {max_allowed} (OppBid: {opp_best_bid})")
                ideal = max_allowed

        # Если у нас перекос позиции
        if i_am_heavy:
            ideal = bb_me - KNIFE_CATCH_DISCOUNT
            if ideal < Decimal("0.02"): ideal = Decimal("0.01")

        ideal = ideal.quantize(Decimal("0.01"), rounding=ROUND_DOWN)
        
        if ideal < Decimal("0.01") or ideal > Decimal("0.99"): return []
        if ideal >= ba_me: return [] 

        if is_yes:
            if net > Decimal("1"): 
                last_p = self.last_buy_price.get(token_id)
                if last_p is not None and ideal >= (last_p - Decimal("0.01")): 
                    return []
        else:
            if net < Decimal("-1"):
                last_p = self.last_buy_price.get(token_id)
                if last_p is not None and ideal >= last_p:
                    return []

        ladder = []
        for i in range(LADDER_LEVELS):
            p = ideal - (Decimal(i) * LADDER_STEP)
            if p >= Decimal("0.01"): ladder.append(p)
        return ladder

    async def manage_orders(self, token_id, target_prices, is_yes, target_size):
        async with self.orders_lock:
            current_orders = self.state.my_orders.get(token_id, {})
            
            all_sizes_correct = True
            for info in current_orders.values():
                if info['size'] != target_size:
                    all_sizes_correct = False
                    break

            has_enough_orders = len(current_orders) >= LADDER_LEVELS
            is_price_fresh = False
            
            if current_orders and target_prices:
                my_best_price = max([Decimal(info['price']) for info in current_orders.values()])
                target_best_price = max(target_prices)
                diff = abs(my_best_price - target_best_price)
                if diff < Decimal("0.015"):
                    is_price_fresh = True
            
            if has_enough_orders and is_price_fresh and all_sizes_correct:
                return

            side_str = "YES" if is_yes else "NO"
            
            curr_map = {}
            to_cancel = []

            for oid, info in current_orders.items():
                p = info['price']
                s = info['size']
                if s != target_size:
                    to_cancel.append(oid)
                else:
                    curr_map.setdefault(p, []).append(oid)
            
            to_create = [] 
            size_float = float(target_size)
            
            target_counts = {p: 0 for p in target_prices}
            for p in target_prices: target_counts[p] += 1
            
            for p in list(target_counts.keys()):
                if p in curr_map and curr_map[p]:
                    curr_map[p].pop(0) 
                    target_counts[p] -= 1
                    if target_counts[p] == 0: del target_counts[p]
            
            for p_list in curr_map.values(): to_cancel.extend(p_list)
            
            for p, count in target_counts.items():
                for _ in range(count): to_create.append(p)
            
            if to_cancel:
                valid_cancel = [oid for oid in to_cancel if oid]
                for oid in to_cancel:
                    if oid in self.state.my_orders[token_id]: 
                        del self.state.my_orders[token_id][oid]
                
                if valid_cancel:
                    try:
                        await self.tx_limiter.acquire()
                        await self._run_sync(self.client.cancel_orders, valid_cancel)
                    except Exception as e:
                        logger.error(f"Cancel err: {e}")

        if to_create:
            options = CreateOrderOptions(neg_risk=self.current_market['neg_risk'], tick_size="0.01")
            batch = []
            prices = []
            
            for p in to_create:
                try:
                    args = OrderArgs(price=float(p), size=size_float, side=BUY, token_id=token_id)
                    signed = await self._run_sync(self.client.create_order, args, options)
                    batch.append(PostOrdersArgs(order=signed, orderType=OrderType.GTC))
                    prices.append(p)
                except: pass

            if batch:
                try:
                    await self.tx_limiter.acquire()
                    resps = await self._run_sync(self.client.post_orders, batch)
                    
                    async with self.orders_lock:
                        success_count = 0
                        total_cost_placed = Decimal("0")
                        for i, r in enumerate(resps):
                            if r.get('success'):
                                oid = r.get('orderID') or r.get('id') or r.get('order_id')
                                
                                if not oid:
                                    logger.error(f"❌ CRITICAL: Order placed but NO ID returned! Raw response: {r}")
                                    continue
                                
                                logger.info(f"✅ Order PLACED {side_str}: ID={oid} Price={prices[i]} Size={target_size}")
                                
                                self.state.my_orders.setdefault(token_id, {})[oid] = {
                                    'price': prices[i],
                                    'size': target_size,
                                    'created_at': time.time()
                                }
                                success_count += 1
                                total_cost_placed += (prices[i] * target_size)
                            else:
                                logger.error(f"❌ Post Fail {side_str}: {r.get('errorMsg')} (Code: {r.get('code')})")
                    
                    if success_count > 0:
                        async with self.pos_lock:
                            self.spend_accumulator += total_cost_placed
                except Exception as e:
                    logger.error(f"Post err: {e}")

    def _get_next_hour_market_slug(self):
        utc_now = datetime.now(timezone.utc)
        et_tz = ZoneInfo("US/Eastern")
        et_now = utc_now.astimezone(et_tz)
        
        current_hour_start = et_now.replace(minute=0, second=0, microsecond=0)
        current_expiry = current_hour_start + timedelta(hours=1)
        time_until_expiry = (current_expiry - et_now).total_seconds()
        
        if time_until_expiry < 120:
            target_start = current_hour_start + timedelta(hours=1)
            target_expiry = current_expiry + timedelta(hours=1)
            log_note = "NEXT (Close to expiry)"
        else:
            target_start = current_hour_start
            target_expiry = current_expiry
            log_note = "CURRENT"
            
        month_str = target_start.strftime("%B").lower()
        day_str = str(int(target_start.strftime("%d")))
        hour_12 = int(target_start.strftime("%I")) 
        am_pm = target_start.strftime("%p").lower() 
        
        # 🔥 БЕРЕМ НАЗВАНИЕ ИЗ НАСТРОЕК (bitcoin, ethereum, etc.)
        asset_name = ASSET_SLUG_MAP[TARGET_ASSET]["hourly"]
        
        slug = f"{asset_name}-up-or-down-{month_str}-{day_str}-{hour_12}{am_pm}-et"
        
        logger.info(f"🕒 TIME DEBUG [{TARGET_ASSET}]: UTC={utc_now.strftime('%H:%M')} | ET={et_now.strftime('%H:%M')} | Selection={log_note} | SLUG={slug}")
        return slug, target_expiry.timestamp()

    async def find_market(self):
        target_slug = ""
        expiry_ts = 0
        
        if self.market_type_env == "1h":
            try:
                target_slug, expiry_ts = self._get_next_hour_market_slug()
            except Exception as e:
                logger.error(f"Slug gen error: {e}")
                await asyncio.sleep(5)
                return
        else:
            # Логика для 15m рынков с учетом актива
            now_ts = time.time()
            curr_start = (int(now_ts) // 900) * 900
            time_left = (curr_start + 900) - now_ts
            expiry_ts = curr_start + 900 if time_left < 120 else curr_start + 900
            
            # 🔥 БЕРЕМ КОРОТКИЙ ПРЕФИКС (btc, eth, sol)
            asset_prefix = ASSET_SLUG_MAP[TARGET_ASSET]["15m"]
            
            target_slug = f"{asset_prefix}-updown-15m-{expiry_ts}" 
            
            if time_left < 120:
                expiry_ts = expiry_ts + 900
                target_slug = f"{asset_prefix}-updown-15m-{expiry_ts}"

        if self.market_slug == target_slug and self.current_market: return

        logger.info(f"🔎 Looking for market: {target_slug}")
        try:
            if not self.session: return
            async with self.session.get(f"{GAMMA_HOST}/events", params={"slug": target_slug}) as resp:
                data = await resp.json()
                
                if not data: 
                    logger.warning(f"Market {target_slug} not found yet. Retrying...")
                    await asyncio.sleep(2)
                    return
                
                market = data[0]['markets'][0]
        
            clob_ids = json.loads(market['clobTokenIds'])
            outcomes = json.loads(market['outcomes'])
            
            t_yes = clob_ids[0] if outcomes[0].upper() in ["UP", "YES"] else clob_ids[1]
            t_no = clob_ids[1] if outcomes[0].upper() in ["UP", "YES"] else clob_ids[0]

            logger.info(f"📝 Market Details: NegRisk={market.get('negRisk')}")

            if self.market_slug != target_slug:
                if self.current_market:
                    logger.info("Switching markets, cancelling old orders...")
                    try:
                        await self._run_sync(self.client.cancel_market_orders, market=self.current_market['condition_id'])
                    except: pass
                
                async with self.orders_lock:
                    self.state.my_orders.clear()
                
                self.state.init_market(t_yes, t_no)
                self.last_buy_price = {}
                self.zombie_candidates = {}
                
                async with self.pos_lock:
                    self.pos_yes = Decimal("0")
                    self.pos_no = Decimal("0")
                    self.last_pos_yes = None
                    self.last_pos_no = None

            self.market_slug = target_slug
            self.current_market = {
                "token_yes": t_yes, "token_no": t_no,
                "condition_id": market['conditionId'],
                "neg_risk": market.get('negRisk', False),
                "slug": target_slug,
                "expiry_ts": expiry_ts 
            }
            logger.info(f"✅ Market Found & Init: {target_slug} | Expire: {datetime.fromtimestamp(expiry_ts)}")
            
            self.logic_event.set()
            await self.update_money_stats()
            
        except Exception as e:
            logger.error(f"Find market error: {e}")
            await asyncio.sleep(2)

    async def market_discovery_worker(self):
        """Регулярно проверяет наличие нового рынка (смена часа)"""
        logger.info("🔭 Market Discovery Worker Started")
        while not self.stop_event.is_set():
            try:
                await self.find_market()
            except Exception as e:
                logger.error(f"Discovery error: {e}")
            
            await asyncio.sleep(10)

    async def main_loop(self):
        log_listener.start()
        self.session = aiohttp.ClientSession()

        logger.info(f"🚀 V8.13 [Mode: {self.market_type_env.upper()}]")
        try:
            self.creds = await self._run_sync(self.client.create_or_derive_api_creds)
            self.client.set_api_creds(self.creds)
            logger.info("🔑 API Creds Set")
        except Exception as e:
            logger.error(f"Auth fail: {e}")
            log_listener.stop()
            await self.session.close()
            return

        while not self.current_market:
            await self.find_market()
            await asyncio.sleep(1)

        tasks = [
            asyncio.create_task(self.background_balance_sync()),
            asyncio.create_task(self.reconcile_worker()), 
            asyncio.create_task(self.ws_loop()),
            asyncio.create_task(self.logic_worker()),
            # asyncio.create_task(self.merge_worker()),
            asyncio.create_task(self.market_discovery_worker())
        ]
        
        logger.info("⚡ ALL SYSTEMS GO. Waiting for data...")

        try:
            await self.stop_event.wait()
            
            if self.shutdown_task:
                logger.info("⏳ Main Loop: Waiting for shutdown sequence to finish...")
                await self.shutdown_task

        finally:
            logger.info("🛑 Shutting down...")
            for t in tasks: t.cancel()
            await self.session.close()
            log_listener.stop()

async def main():
    bot = GabagoolV8()
    loop = asyncio.get_running_loop()

    def signal_handler():
        logger.warning("⌨️ Keyboard Interrupt received! Launching graceful shutdown...")
        bot.shutdown_task = asyncio.create_task(bot.graceful_shutdown())

    for sig in (signal.SIGINT, signal.SIGTERM):
        loop.add_signal_handler(sig, signal_handler)

    await bot.main_loop()

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass