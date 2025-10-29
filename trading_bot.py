# -*- coding: utf-8 -*-
import threading
import queue
import time
from datetime import datetime, timedelta, UTC
from decimal import Decimal, getcontext
import logging
import numpy as np
import os
import json
from concurrent.futures import ThreadPoolExecutor, as_completed
import requests
import warnings

# --- НАСТРОЙКА ЛОГИРОВАНИЯ (для этого модуля) ---
logger = logging.getLogger(__name__)

# --- НАСТРОЙКА ТОЧНОСТИ ВЫЧИСЛЕНИЙ ---
getcontext().prec = 18

# --- ПРОВЕРКА И ИМПОРТ БИБЛИОТЕК ---
try:
    from binance.client import Client
    from binance.exceptions import BinanceAPIException, BinanceRequestException
    import pandas as pd
    import pandas_ta as ta
except ImportError:
    logger.critical("КРИТИЧЕСКАЯ ОШИБКА: trading_bot.py не смог импортировать 'binance', 'pandas' или 'pandas_ta'. Убедитесь, что main.py был запущен и библиотеки установлены.")
    pass 

# --- Файл для сохранения состояния бота ---
STATE_FILE = "bot_state_multi_strategy.json"


# --- ОСНОВНОЙ КЛАСС ЛОГИКИ БОТА (v1.1 Scalping 2025 - 6 стратегий) ---
class TradingBot(threading.Thread):
    
    def __init__(self, api_key, api_secret, event_queue, risk_per_trade, rr_ratio, symbol, active_strategies_config, backtest_client=None):
        super().__init__()
        self.daemon = True
        self.api_key, self.api_secret, self.event_queue = api_key, api_secret, event_queue
        try:
            self.base_risk_per_trade = Decimal(str(risk_per_trade)) / 100
            # *** ИЗМЕНЕНИЕ (v1.0 Scalp): Минимальный RR для скальпинга (может быть 1.0) ***
            self.base_rr_ratio = Decimal(str(rr_ratio)) # (Например, 1.0 или 1.2)
        except (ValueError, TypeError):
            self.log("Ошибка: риск и R/R должны быть числами. Используются значения по умолчанию.")
            self.base_risk_per_trade = Decimal('0.01')
            self.base_rr_ratio = Decimal('1.0')

        self.symbol = symbol.upper()
        self.stop_event = threading.Event()
        self.binance_client = backtest_client
        self.is_backtest = backtest_client is not None
        if self.is_backtest:
            backtest_client.log_callback = self.log

        self.active_strategies = active_strategies_config
        self.log(f"Активные стратегии: {[stype for stype, active in self.active_strategies.items() if active]}")

        self.is_connected = False
        self.reconnect_attempts = 0
        
        # --- Состояние позиции ---
        self.position_side = None
        self.entry_price, self.quantity = Decimal('0.0'), Decimal('0.0')
        self.stop_loss_price = Decimal('0.0')
        self.entry_commission_cost = Decimal('0.0')
        self.is_profit_locked = False
        self.is_trailing_active = False
        self.initial_stop_loss_price = Decimal('0.0')
        self.is_tp1_hit = False
        self.take_profit_price_1 = Decimal('0.0')
        self.final_take_profit_price = Decimal('0.0')
        self.initial_quantity = Decimal('0.0')
        self.entry_time = None
        self.sl_confirmation_counter = 0
        
        self.current_trade_strategy_type = "UNKNOWN"

        # --- Общая статистика ---
        self.total_pnl_usdt, self.total_fees_paid_usdt = Decimal('0.0'), Decimal('0.0')
        self.win_trades, self.loss_trades = 0, 0
        self.trade_counter = 0 
        self.current_trade_id = None
        self.current_trade_pnl = Decimal('0.0')

        # *** НАЧАЛО ИЗМЕНЕНИЯ (v1.1): Добавлены новые стратегии ***
        self.strategy_types = [
            "SCALP_LIQUIDITY_SWEEP_3M", "SCALP_RSI_VOLUME_5M", "SCALP_BREAKOUT_CONFIRM_1M",
            "SCALP_PRICE_ACTION_1M",
            "SCALP_MOMENTUM_BREAK_3M",
            "SCALP_BOLLINGER_TOUCH_5M",
            "UNKNOWN"
        ]
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***
        
        self.pnl_by_strategy = {stype: Decimal('0.0') for stype in self.strategy_types}
        self.wins_by_strategy = {stype: 0 for stype in self.strategy_types}
        self.losses_by_strategy = {stype: 0 for stype in self.strategy_types}

        # --- Параметры символа ---
        self.base_asset, self.quote_asset = "", "USDT"
        self.step_size, self.qty_precision, self.price_precision = Decimal('0.0001'), 4, 2
        self.commission_rate, self.min_notional = Decimal('0.001'), Decimal('10.0')

        # --- Параметры индикаторов (SCALPING) ---
        self.ema_scalp_fast_len = 5
        self.ema_scalp_slow_len = 10
        self.ema_trend_len = 200
        self.atr_period = 14 
        self.atr_multiplier_trail = Decimal('2.0') # Трейлинг по умолчанию
        self.adx_len = 14
        self.vol_sma_len = 20
        # MACD/StochRSI параметры используются по умолчанию в pandas_ta
        
        # *** НАЧАЛО ИЗМЕНЕНИЯ (v1.1): Параметры для новых индикаторов ***
        self.bb_len = 20
        self.bb_std = 2.0
        self.rsi_period = 14 # (Уже используется, но подтверждено)
        self.stoch_period = 14
        self.stoch_k = 3
        self.stoch_d = 3
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***
        
        self.last_heartbeat_log_time = time.time()
        self.last_hour_checked = None # Используем для 1-минутных проверок

    def _save_state(self):
        # (Эта функция без изменений)
        if self.is_backtest: return
        pnl_by_strategy_str = {k: str(v) for k, v in self.pnl_by_strategy.items()}
        state = {
            'symbol': self.symbol, 'position_side': self.position_side, 'entry_price': str(self.entry_price),
            'quantity': str(self.quantity), 'initial_quantity': str(self.initial_quantity),
            'stop_loss_price': str(self.stop_loss_price), 'initial_stop_loss_price': str(self.initial_stop_loss_price),
            'take_profit_price_1': str(self.take_profit_price_1), 'final_take_profit_price': str(self.final_take_profit_price),
            'entry_commission_cost': str(self.entry_commission_cost),
            'is_profit_locked': self.is_profit_locked, 'is_trailing_active': self.is_trailing_active, 'is_tp1_hit': self.is_tp1_hit,
            'entry_time': self.entry_time.isoformat() if self.entry_time else None,
            'sl_confirmation_counter': self.sl_confirmation_counter,
            'current_trade_strategy_type': self.current_trade_strategy_type,
            'total_pnl_usdt': str(self.total_pnl_usdt), 'total_fees_paid_usdt': str(self.total_fees_paid_usdt),
            'win_trades': self.win_trades, 'loss_trades': self.loss_trades,
            'trade_counter': self.trade_counter, 'current_trade_id': self.current_trade_id,
            'pnl_by_strategy': pnl_by_strategy_str,
            'wins_by_strategy': self.wins_by_strategy,
            'losses_by_strategy': self.losses_by_strategy,
        }
        try:
            with open(STATE_FILE, 'w') as f: json.dump(state, f, indent=4)
        except Exception as e: self.log(f"КРИТИЧЕСКАЯ ОШИБКА: Не удалось сохранить состояние бота: {e}")

    def _load_state(self):
        # (Эта функция без изменений, но инициализирует новые типы стратегий)
        if self.is_backtest or not os.path.exists(STATE_FILE): return
        try:
            with open(STATE_FILE, 'r') as f: state = json.load(f)
            if state.get('symbol') != self.symbol: self.log(f"Найден файл состояния для другой пары ({state.get('symbol')}). Игнорируется."); return
            
            self.position_side = state.get('position_side')
            self.entry_price = Decimal(state.get('entry_price', '0.0'))
            self.quantity = Decimal(state.get('quantity', '0.0'))
            self.initial_quantity = Decimal(state.get('initial_quantity', '0.0'))
            self.stop_loss_price = Decimal(state.get('stop_loss_price', '0.0'))
            self.initial_stop_loss_price = Decimal(state.get('initial_stop_loss_price', '0.0'))
            self.take_profit_price_1 = Decimal(state.get('take_profit_price_1', '0.0'))
            self.final_take_profit_price = Decimal(state.get('final_take_profit_price', '0.0'))
            self.entry_commission_cost = Decimal(state.get('entry_commission_cost', '0.0'))
            self.is_profit_locked = state.get('is_profit_locked', False)
            self.is_trailing_active = state.get('is_trailing_active', False)
            self.is_tp1_hit = state.get('is_tp1_hit', False)
            self.sl_confirmation_counter = state.get('sl_confirmation_counter', 0)
            self.current_trade_strategy_type = state.get('current_trade_strategy_type', "UNKNOWN")
            entry_time_str = state.get('entry_time')
            if entry_time_str:
                try: 
                    # (Рекомендация по анализу: добавляем .replace(tzinfo=UTC))
                    self.entry_time = datetime.fromisoformat(entry_time_str).replace(tzinfo=UTC)
                except ValueError: 
                    self.entry_time = None; self.log("Предупреждение: неверный формат даты в файле состояния.")
            else: self.entry_time = None
            self.total_pnl_usdt = Decimal(state.get('total_pnl_usdt', '0.0'))
            self.total_fees_paid_usdt = Decimal(state.get('total_fees_paid_usdt', '0.0'))
            self.win_trades = state.get('win_trades', 0)
            self.loss_trades = state.get('loss_trades', 0)
            self.trade_counter = state.get('trade_counter', 0)
            self.current_trade_id = state.get('current_trade_id', None)
            
            # (Обновлено для новых стратегий v1.1)
            pnl_by_strategy_str = state.get('pnl_by_strategy', {})
            self.pnl_by_strategy = {stype: Decimal(pnl_by_strategy_str.get(stype, '0.0')) for stype in self.strategy_types}
            self.wins_by_strategy = state.get('wins_by_strategy', {stype: 0 for stype in self.strategy_types})
            self.losses_by_strategy = state.get('losses_by_strategy', {stype: 0 for stype in self.strategy_types})
            for stype in self.strategy_types:
                if stype not in self.pnl_by_strategy: self.pnl_by_strategy[stype] = Decimal('0.0')
                if stype not in self.wins_by_strategy: self.wins_by_strategy[stype] = 0
                if stype not in self.losses_by_strategy: self.losses_by_strategy[stype] = 0
                
            self.log("Состояние бота успешно загружено.")
            if self.position_side: self.log(f"Загружена активная позиция: {self.position_side} {self.quantity} {self.base_asset}")
        except Exception as e: self.log(f"ОШИБКА: Не удалось загрузить состояние бота: {e}")

    def run(self):
        # *** ИЗМЕНЕНИЕ (v1.1 Scalp) ***
        bot_name = "Scalping Bot v1.1 (2025 Filters - 6 Strategies)"
        mode = "БЭКТЕСТ (1M)" if self.is_backtest else "РЕАЛЬНАЯ ТОРГОВЛЯ" 
        self.log(f"Запуск бота '{bot_name}' в режиме '{mode}' для символа {self.symbol}...")
        
        if not self._initialize_apis(): self._stop_bot_on_error("Не удалось инициализировать API."); return
        self._load_state()
        if not self._get_symbol_info(): self._stop_bot_on_error("Не удалось получить информацию о символе."); return
            
        loop_condition = self.binance_client.has_more_data if self.is_backtest else lambda: not self.stop_event.is_set()
        tick_counter = 0 
        
        while loop_condition():
            try:
                current_time_dt = self._get_current_time()
                # (Логика Scalp: проверяем на каждой 1М свече)
                current_minute = current_time_dt.replace(second=0, microsecond=0)
                should_check_logic = (self.last_hour_checked is None or current_minute > self.last_hour_checked)

                if not self.is_connected and not self.is_backtest: self._handle_disconnection(); continue

                current_1m_candle = None; current_high = None; current_low = None
                if self.is_backtest:
                    current_1m_candle = self.binance_client.get_current_candle()
                    if current_1m_candle is None: break 
                    current_high = Decimal(str(current_1m_candle['high']))
                    current_low = Decimal(str(current_1m_candle['low']))

                # (Получаем 1m, 3m, 5m, 15m, 1d)
                market_data = self._get_market_data()
                if not market_data: self._wait_or_continue(); continue
                
                current_price = market_data['current_price']
                if not self.is_backtest:
                    current_high = current_price; current_low = current_price
                
                # *** ИСПРАВЛЕНИЕ (v1.1): Удалена избыточная проверка (tick_counter % 1 == 0) ***
                # Обновляем GUI каждую минуту в бэктесте (т.е. каждый тик) или в реальном времени.
                self._update_dashboard_data(market_data, current_price)
                
                if should_check_logic:
                    self.last_hour_checked = current_minute
                    # (Лог Scalp: каждую минуту)
                    if tick_counter > 0: # Не логируем первый тик
                        log_msg = f"--- Новая 1M свеча ({current_time_dt.strftime('%H:%M')}). Обновление STF данных... ---"
                        if self.is_backtest: self.log(log_msg)
                        if not self.is_backtest: self.log(log_msg)
                
                if self.position_side:
                    self._check_and_manage_exit_conditions(market_data, current_price, current_high, current_low, current_1m_candle) 
                else:
                    if market_data['usdt_balance'] < self.min_notional:
                        if self.is_backtest: self.log("Баланс USDT исчерпан. Бэктест остановлен."); break
                        self.log(f"Торговля приостановлена. Недостаточно средств."); self._wait_or_continue(300); continue
                    
                    # (Проверяем логику каждую минуту)
                    if should_check_logic:
                        best_signal = self._get_algorithmic_decision(market_data, current_price)
                        
                        if best_signal:
                            self._calculate_and_open_position(best_signal, market_data)
                        else: 
                            # self.log("Анализ завершен: Нет сигналов.") # Слишком много спама для 1M
                            pass
                    
                current_time_seconds = time.time()
                if not self.is_backtest and current_time_seconds - self.last_heartbeat_log_time > 60: # Частый Heartbeat для скальпинга
                    self._log_heartbeat(market_data, current_price)
                    self.last_heartbeat_log_time = current_time_seconds
                elif self.is_backtest and tick_counter % 60 == 0 and tick_counter > 0: # Heartbeat каждый час в бэктесте
                    self._log_heartbeat(market_data, current_price)
            
            except (BinanceRequestException, requests.exceptions.RequestException) as e: 
                self.log(f"Сетевая ошибка: {e}. Активация режима переподключения."); self.is_connected = False
                time.sleep(2 ** min(self.reconnect_attempts, 5)); self.reconnect_attempts += 1
            except BinanceAPIException as e: 
                self.log(f"Ошибка API Binance: {e}. Код: {e.code}, Сообщение: {e.message}"); self._sleep_interruptible(60)
            except Exception as e:
                self.log(f"НЕОЖИДАННАЯ ОШИБКА в главном цикле: {e}. Попытка продолжить через 60 секунд."); logger.exception("Детали:"); self._sleep_interruptible(60)
            
            self._wait_or_continue(); tick_counter += 1
            
        self._finalize_run()

    def _log_heartbeat(self, market_data, current_price):
        # (Эта функция без изменений)
        try:
            balance_usdt = market_data['usdt_balance']
            current_price_str = f"{current_price:.{self.price_precision}f}"
            
            if self.position_side:
                pos_qty = f"{self.quantity:.{self.qty_precision}f}"
                entry_p = f"{self.entry_price:.{self.price_precision}f}"
                pnl = (current_price - self.entry_price) * self.quantity
                status_msg = f"СТАТУС: Позиция {pos_qty} {self.base_asset} | Вход: {entry_p} | PnL: ${pnl:+.2f} | SL: {self.stop_loss_price:.{self.price_precision}f}"
            else:
                status_msg = "СТАТУС: Ожидание сигнала..."
            
            self.log(f"{status_msg} (Bal: ${balance_usdt:.2f} | Cur: ${current_price_str})")
        
        except Exception as e:
            self.log(f"Ошибка в логе Heartbeat: {e}")

    # ---
    # --- ЛОГИКА ПРИНЯТИЯ РЕШЕНИЙ (v1.1 Scalp - 6 стратегий) ---
    # ---
    def _get_algorithmic_decision(self, market_data, current_price):
        
        # (Фильтр 1D Тренда оставлен, т.к. одна из стратегий его использует)
        ind_1d = market_data.get('indicators_1d')
        is_1d_bull_trend = False
        
        # (Проверка на пустой DF из анализа)
        if ind_1d is None or ind_1d.empty or len(ind_1d) < self.ema_trend_len:
            reason = f"Ожидание данных для 1D ({len(ind_1d) if ind_1d is not None else 0}/{self.ema_trend_len})"
            self._log_daily_status(reason); return None
        try:
            price_1d = Decimal(str(ind_1d.iloc[-1]['close']))
            ema200_1d = Decimal(str(ind_1d.iloc[-1][f'EMA_{self.ema_trend_len}']))
            is_1d_bull_trend = price_1d > ema200_1d
        except (ValueError, KeyError, IndexError):
            self.log("Предупреждение: Недопустимые данные в индикаторах 1D. Пропуск."); return None

        self._log_daily_status(f"1D Тренд: {'' if is_1d_bull_trend else 'НЕ '}Бычий. Поиск Scalp-сигналов...")

        # (Удален _get_key_levels)

        # *** НАЧАЛО ИЗМЕНЕНИЯ (v1.1): Добавлены новые стратегии ***
        signals = {
            "SCALP_LIQUIDITY_SWEEP_3M": None, 
            "SCALP_RSI_VOLUME_5M": None, 
            "SCALP_BREAKOUT_CONFIRM_1M": None,
            "SCALP_PRICE_ACTION_1M": None,
            "SCALP_MOMENTUM_BREAK_3M": None,
            "SCALP_BOLLINGER_TOUCH_5M": None
        }
        
        # (Существующие стратегии)
        if self.active_strategies.get("SCALP_LIQUIDITY_SWEEP_3M", False):
            signals["SCALP_LIQUIDITY_SWEEP_3M"] = self._find_entry_scalp_sweep_3m(market_data, current_price)
        if self.active_strategies.get("SCALP_RSI_VOLUME_5M", False):
            signals["SCALP_RSI_VOLUME_5M"] = self._find_entry_scalp_rsi_vol_5m(market_data, current_price)
        if self.active_strategies.get("SCALP_BREAKOUT_CONFIRM_1M", False):
            signals["SCALP_BREAKOUT_CONFIRM_1M"] = self._find_entry_scalp_breakout_1m(market_data, current_price)
            
        # (Новые стратегии v1.1)
        if self.active_strategies.get("SCALP_PRICE_ACTION_1M", False):
            signals["SCALP_PRICE_ACTION_1M"] = self._find_entry_scalp_price_action_1m(market_data, current_price)
        if self.active_strategies.get("SCALP_MOMENTUM_BREAK_3M", False):
            signals["SCALP_MOMENTUM_BREAK_3M"] = self._find_entry_scalp_momentum_break_3m(market_data, current_price)
        if self.active_strategies.get("SCALP_BOLLINGER_TOUCH_5M", False):
            signals["SCALP_BOLLINGER_TOUCH_5M"] = self._find_entry_scalp_bollinger_touch_5m(market_data, current_price)
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***
        
        # --- УРОВЕНЬ 3: Скальпинг-Сигналы ---
        # (Все стратегии имеют одинаковый приоритет (Tier 3), выбираем лучший R/R)
        
        # *** НАЧАЛО ИЗМЕНЕНИЯ (v1.1): Обновленный список Tier 3 ***
        tier_3_signals = [
            signals["SCALP_LIQUIDITY_SWEEP_3M"], signals["SCALP_RSI_VOLUME_5M"], signals["SCALP_BREAKOUT_CONFIRM_1M"],
            signals["SCALP_PRICE_ACTION_1M"], signals["SCALP_MOMENTUM_BREAK_3M"], signals["SCALP_BOLLINGER_TOUCH_5M"]
        ]
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***
        
        # (Проверяем R/R >= self.base_rr_ratio, который теперь 1.0 или 1.2)
        valid_tier_3 = [s for s in tier_3_signals if s and s.get('rr_ratio', Decimal('0')) >= self.base_rr_ratio]
        
        if valid_tier_3:
            # Выбираем сигнал с наилучшим R/R
            best_signal = max(valid_tier_3, key=lambda x: x['rr_ratio'])
            self.log(f"    -> ✅ ВЫБОР (TIER 3 - Scalp): {best_signal['type']} (R/R: {best_signal['rr_ratio']:.2f}:1)")
            return best_signal
        
        return None

    # ---
    # --- (УДАЛЕНЫ СТАРЫЕ СТРАТЕГИИ И _get_key_levels) ---
    # ---

    # ---
    # --- СУЩЕСТВУЮЩИЕ СТРАТЕГИИ (v1.0 Scalp) ---
    # ---

    def _find_entry_scalp_sweep_3m(self, market_data, current_price):
        ind_3m = market_data.get('indicators_3m')
        ind_15m = market_data.get('indicators_15m')
        # (Проверка на пустой DF из анализа)
        if ind_3m is None or ind_3m.empty or ind_15m is None or ind_15m.empty or len(ind_3m) < 21 or len(ind_15m) < self.ema_trend_len:
            return None
        
        # 1. Глобальный фильтр (15m TF)
        try:
            price_15m = Decimal(str(ind_15m.iloc[-1]['close']))
            ema200_15m = Decimal(str(ind_15m.iloc[-1][f'EMA_{self.ema_trend_len}']))
            if price_15m <= ema200_15m:
                # self.log("    -> ОТКЛОНЕНО (SWEEP 3M): Цена ниже EMA 200 на 15M.")
                return None
        except (ValueError, KeyError, IndexError): return None
        
        # 2. Анализ 3M
        try:
            recent_data = ind_3m.iloc[-20:] # Данные за 20 свечей (1 час)
            last_candle = ind_3m.iloc[-1]
            
            # (Sweep Detection)
            lookback_low = Decimal(str(ind_3m.iloc[-6:-1]['low'].min())) # Low за 5 предыдущих свечей
            current_low = Decimal(str(last_candle['low']))
            current_close = Decimal(str(last_candle['close']))
            current_open = Decimal(str(last_candle['open']))
            
            is_sweep = (current_low < lookback_low) and (current_close > current_open)
            if not is_sweep: return None

            # (Momentum Confirmation)
            ema_5 = Decimal(str(last_candle[f'EMA_{self.ema_scalp_fast_len}']))
            ema_10 = Decimal(str(last_candle[f'EMA_{self.ema_scalp_slow_len}']))
            macd_hist = Decimal(str(last_candle['MACDh_12_26_9']))
            prev_macd_hist = Decimal(str(ind_3m.iloc[-2]['MACDh_12_26_9']))
            
            is_momentum_ok = (ema_5 > ema_10) or (macd_hist > 0 and macd_hist > prev_macd_hist)
            if not is_momentum_ok:
                # self.log("    -> ОТКЛОНЕНО (SWEEP 3M): Sweep есть, но Momentum-фильтр (EMA 5>10 или MACD Hist > 0) не пройден.")
                return None

            # (Volume Filter)
            norm_vol = Decimal(str(last_candle['norm_volume']))
            avg_norm_vol = Decimal(str(last_candle[f'NORM_VOL_SMA_{self.vol_sma_len}']))
            if norm_vol <= (avg_norm_vol * Decimal('1.3')):
                # self.log(f"    -> ОТКЛОНЕНО (SWEEP 3M): Низкий Norm. Volume ({norm_vol:.2f} <= {avg_norm_vol*Decimal('1.3'):.2f})")
                return None

            # (Volatility Filter)
            atr_14 = Decimal(str(last_candle[f'ATRr_{self.atr_period}']))
            avg_atr_14 = Decimal(str(recent_data[f'ATRr_{self.atr_period}'].mean()))
            if atr_14 <= avg_atr_14:
                # self.log("    -> ОТКЛОНЕНО (SWEEP 3M): Низкая волатильность (ATR <= Avg ATR).")
                return None

        except (ValueError, KeyError, IndexError): 
            return None

        entry_price = current_price
        
        # (SL: Entry - (ATR * 0.8))
        sl_mult = Decimal('0.8')
        stop_loss_price = self._round_price(entry_price - (atr_14 * sl_mult))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # (TP: R/R 1.2)
        rr_mult = Decimal('1.2')
        reward_per_coin = risk_per_coin * rr_mult
        target_tp = self._round_price(entry_price + reward_per_coin)
        rr_ratio = reward_per_coin / risk_per_coin

        if rr_ratio < Decimal('1.2'): return None # (Требование R/R >= 1.2)

        self.log(f"    -> Кандидат (SCALP_LIQUIDITY_SWEEP_3M): LONG на 3M (sweep + momentum + volume). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "SCALP_LIQUIDITY_SWEEP_3M", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}


    def _find_entry_scalp_rsi_vol_5m(self, market_data, current_price):
        ind_5m = market_data.get('indicators_5m')
        # (Проверка на пустой DF из анализа)
        if ind_5m is None or ind_5m.empty or len(ind_5m) < (self.vol_sma_len + 2):
            return None
        
        try:
            last_candle = ind_5m.iloc[-1]
            prev_candle = ind_5m.iloc[-2]

            # (Oversold Signal)
            rsi = Decimal(str(last_candle['RSI_14']))
            prev_rsi = Decimal(str(prev_candle['RSI_14']))
            
            is_oversold_exit = (prev_rsi < 30) and (rsi > 30)
            if not is_oversold_exit: return None

            # (Volume Breakout)
            norm_vol = Decimal(str(last_candle['norm_volume']))
            avg_norm_vol = Decimal(str(last_candle[f'NORM_VOL_SMA_{self.vol_sma_len}']))
            
            if norm_vol <= (avg_norm_vol * Decimal('1.5')):
                # self.log(f"    -> ОТКЛОНЕНО (RSI 5M): Низкий Norm. Volume ({norm_vol:.2f} <= {avg_norm_vol*Decimal('1.5'):.2f})")
                return None
            
            # (Stochastic Filter)
            stoch_k = Decimal(str(last_candle['STOCHRSIk_14_14_3_3']))
            prev_stoch_k = Decimal(str(prev_candle['STOCHRSIk_14_14_3_3']))
            
            is_stoch_exit = (prev_stoch_k < 20) and (stoch_k > 20)
            if not is_stoch_exit:
                # self.log("    -> ОТКЛОНЕНО (RSI 5M): StochRSI не выходит из зоны < 20.")
                return None

            # (Micro-trend Filter)
            ema_10 = Decimal(str(last_candle[f'EMA_{self.ema_scalp_slow_len}']))
            if current_price < ema_10:
                # self.log("    -> ОТКЛОНЕНО (RSI 5M): Цена ниже EMA 10 (микро-даунтренд).")
                return None
                
            atr_14 = Decimal(str(last_candle[f'ATRr_{self.atr_period}']))

        except (ValueError, KeyError, IndexError):
            return None

        entry_price = current_price
        
        # (SL: Entry - (ATR * 1.0))
        sl_mult = Decimal('1.0')
        stop_loss_price = self._round_price(entry_price - (atr_14 * sl_mult))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # (TP: R/R 1.5)
        rr_mult = Decimal('1.5')
        reward_per_coin = risk_per_coin * rr_mult
        target_tp = self._round_price(entry_price + reward_per_coin)
        rr_ratio = reward_per_coin / risk_per_coin
        
        if rr_ratio < Decimal('1.5'): return None # (Требование R/R >= 1.5)

        self.log(f"    -> Кандидат (SCALP_RSI_VOLUME_5M): LONG на 5M (RSI oversold + volume breakout). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "SCALP_RSI_VOLUME_5M", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}


    def _find_entry_scalp_breakout_1m(self, market_data, current_price):
        ind_1m = market_data.get('indicators_1m')
        # (Проверка на пустой DF из анализа)
        if ind_1m is None or ind_1m.empty or len(ind_1m) < (self.vol_sma_len + 11):
            return None
            
        try:
            last_candle = ind_1m.iloc[-1]
            
            # (Breakout Level)
            resistance = Decimal(str(ind_1m.iloc[-11:-1]['high'].max())) # Max high за 10 предыдущих свечей
            current_close = Decimal(str(last_candle['close']))
            
            if current_close <= resistance:
                return None
                
            # (MACD Filter)
            macd_hist = Decimal(str(last_candle['MACDh_12_26_9']))
            prev_macd_hist = Decimal(str(ind_1m.iloc[-2]['MACDh_12_26_9']))
            
            if not (macd_hist > 0 and macd_hist > prev_macd_hist):
                # self.log("    -> ОТКЛОНЕНО (BREAKOUT 1M): MACD фильтр не пройден (Hist <= 0 или падает).")
                return None
                
            # (Volume Confirmation)
            norm_vol = Decimal(str(last_candle['norm_volume']))
            avg_norm_vol = Decimal(str(last_candle[f'NORM_VOL_SMA_{self.vol_sma_len}']))
            
            if norm_vol <= (avg_norm_vol * Decimal('1.2')):
                # self.log(f"    -> ОТКЛОНЕНО (BREAKOUT 1M): Низкий Norm. Volume ({norm_vol:.2f} <= {avg_norm_vol*Decimal('1.2'):.2f})")
                return None
            
            # (Overbought Filter)
            rsi = Decimal(str(last_candle['RSI_14']))
            if rsi >= 70:
                # self.log("    -> ОТКЛОНЕНО (BREAKOUT 1M): RSI >= 70 (перекупленность).")
                return None
                
            # (Volatility Filter)
            atr_14 = Decimal(str(last_candle[f'ATRr_{self.atr_period}']))
            avg_atr_14 = Decimal(str(ind_1m.iloc[-11:-1][f'ATRr_{self.atr_period}'].mean()))
            if atr_14 <= avg_atr_14:
                # self.log("    -> ОТКЛОНЕНО (BREAKOUT 1M): Низкая волатильность (ATR <= Avg ATR).")
                return None

        except (ValueError, KeyError, IndexError):
            return None

        entry_price = current_price
        
        # (SL: Entry - (ATR * 0.5))
        sl_mult = Decimal('0.5')
        stop_loss_price = self._round_price(entry_price - (atr_14 * sl_mult))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # (TP: R/R 1.0)
        rr_mult = Decimal('1.0')
        reward_per_coin = risk_per_coin * rr_mult
        target_tp = self._round_price(entry_price + reward_per_coin)
        rr_ratio = reward_per_coin / risk_per_coin
        
        if rr_ratio < Decimal('1.0'): return None # (Требование R/R >= 1.0)

        self.log(f"    -> Кандидат (SCALP_BREAKOUT_CONFIRM_1M): LONG на 1M (breakout + MACD + volume). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "SCALP_BREAKOUT_CONFIRM_1M", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}

    # ---
    # --- *** НАЧАЛО: НОВЫЕ СТРАТЕГИИ v1.1 *** ---
    # ---

    def _find_entry_scalp_price_action_1m(self, market_data, current_price):
        ind_1m = market_data.get('indicators_1m')
        # (Проверка на пустой DF из анализа)
        if ind_1m is None or ind_1m.empty or len(ind_1m) < (self.vol_sma_len + 5): # (Нужен запас для rolling_low)
            return None
            
        try:
            last_candle = ind_1m.iloc[-1]
            
            # 1. Price Action Signal
            is_bull_engulf = last_candle.get('bull_engulf', False)
            is_pin_bar = last_candle.get('pin_bar', False)
            
            if not (is_bull_engulf or is_pin_bar):
                return None
                
            # 2. Volume Filter
            norm_vol = Decimal(str(last_candle['norm_volume']))
            avg_norm_vol = Decimal(str(last_candle[f'NORM_VOL_SMA_{self.vol_sma_len}']))
            
            if norm_vol <= (avg_norm_vol * Decimal('1.4')):
                # self.log(f"    -> ОТКЛОНЕНО (PA 1M): Низкий Norm. Volume ({norm_vol:.2f} <= {avg_norm_vol*Decimal('1.4'):.2f})")
                return None

            # 3. RSI Confirmation
            rsi = Decimal(str(last_candle['RSI_14']))
            if rsi >= 35:
                # self.log(f"    -> ОТКЛОНЕНО (PA 1M): RSI не в зоне oversold ({rsi:.1f} >= 35)")
                return None
                
            # 4. Micro-trend Filter
            ema_10 = Decimal(str(last_candle[f'EMA_{self.ema_scalp_slow_len}']))
            if current_price < ema_10:
                # self.log("    -> ОТКЛОНЕНО (PA 1M): Цена ниже EMA 10 (микро-даунтренд).")
                return None
                
            # 5. Volatility Filter
            atr_14 = Decimal(str(last_candle[f'ATRr_{self.atr_period}']))
            avg_atr_14 = Decimal(str(ind_1m.iloc[-11:-1][f'ATRr_{self.atr_period}'].mean()))
            if atr_14 <= avg_atr_14:
                # self.log("    -> ОТКЛОНЕНО (PA 1M): Низкая волатильность (ATR <= Avg ATR).")
                return None

        except (ValueError, KeyError, IndexError):
            return None

        entry_price = current_price
        
        # SL: (ATR * 0.6)
        sl_mult = Decimal('0.6')
        stop_loss_price = self._round_price(entry_price - (atr_14 * sl_mult))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # TP: R/R 1.0 (Как указано в инструкции: TP1 = 0.5 R/R, Trailing)
        rr_mult = Decimal('1.0')
        reward_per_coin = risk_per_coin * rr_mult
        target_tp = self._round_price(entry_price + reward_per_coin)
        rr_ratio = reward_per_coin / risk_per_coin
        
        if rr_ratio < Decimal('1.0'): return None # (Требование R/R >= 1.0)

        log_msg = f"Engulfing" if is_bull_engulf else f"Pin Bar"
        self.log(f"    -> Кандидат (SCALP_PRICE_ACTION_1M): LONG на 1M ({log_msg} + volume + RSI). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "SCALP_PRICE_ACTION_1M", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}

    def _find_entry_scalp_momentum_break_3m(self, market_data, current_price):
        ind_3m = market_data.get('indicators_3m')
        # (Проверка на пустой DF из анализа)
        if ind_3m is None or ind_3m.empty or len(ind_3m) < (self.vol_sma_len + 10):
            return None
            
        try:
            last_candle = ind_3m.iloc[-1]
            atr_14 = Decimal(str(last_candle[f'ATRr_{self.atr_period}']))
            
            # 1. Breakout Signal
            resistance = Decimal(str(ind_3m.iloc[-6:-1]['close'].max())) # Max close за 5 предыдущих свечей
            breakout_level = resistance + (atr_14 * Decimal('0.5'))
            current_close = Decimal(str(last_candle['close']))
            
            if current_close <= breakout_level:
                return None
                
            # 2. MACD Confirmation
            macd_hist = Decimal(str(last_candle['MACDh_12_26_9']))
            prev_macd_hist = Decimal(str(ind_3m.iloc[-2]['MACDh_12_26_9']))
            
            if not (macd_hist > 0 and macd_hist > prev_macd_hist):
                # self.log("    -> ОТКЛОНЕНО (MOMENTUM 3M): MACD фильтр не пройден (Hist <= 0 или падает).")
                return None
                
            # 3. Volume & ADX Filter
            norm_vol = Decimal(str(last_candle['norm_volume']))
            avg_norm_vol = Decimal(str(last_candle[f'NORM_VOL_SMA_{self.vol_sma_len}']))
            adx = Decimal(str(last_candle[f'ADX_{self.adx_len}']))
            
            if norm_vol <= (avg_norm_vol * Decimal('1.3')) or adx <= 20:
                # self.log(f"    -> ОТКЛОНЕНО (MOMENTUM 3M): Фильтр Volume ({norm_vol:.1f} <= {avg_norm_vol*Decimal('1.3'):.1f}) или ADX ({adx:.1f} <= 20) не пройден.")
                return None
            
            # 4. Overbought Filter
            rsi = Decimal(str(last_candle['RSI_14']))
            if rsi >= 65:
                # self.log("    -> ОТКЛОНЕНО (MOMENTUM 3M): RSI >= 65 (перекупленность).")
                return None
                
            # 5. Volatility Filter
            avg_atr_14 = Decimal(str(ind_3m.iloc[-11:-1][f'ATRr_{self.atr_period}'].mean()))
            if atr_14 <= avg_atr_14:
                # self.log("    -> ОТКЛОНЕНО (MOMENTUM 3M): Низкая волатильность (ATR <= Avg ATR).")
                return None

        except (ValueError, KeyError, IndexError):
            return None

        entry_price = current_price
        
        # SL: (ATR * 0.7)
        sl_mult = Decimal('0.7')
        stop_loss_price = self._round_price(entry_price - (atr_14 * sl_mult))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # TP: R/R 1.2
        rr_mult = Decimal('1.2')
        reward_per_coin = risk_per_coin * rr_mult
        target_tp = self._round_price(entry_price + reward_per_coin)
        rr_ratio = reward_per_coin / risk_per_coin
        
        if rr_ratio < Decimal('1.2'): return None # (Требование R/R >= 1.2)

        self.log(f"    -> Кандидат (SCALP_MOMENTUM_BREAK_3M): LONG на 3M (breakout + MACD + volume/ADX). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "SCALP_MOMENTUM_BREAK_3M", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}

    def _find_entry_scalp_bollinger_touch_5m(self, market_data, current_price):
        ind_5m = market_data.get('indicators_5m')
        # (Проверка на пустой DF из анализа)
        if ind_5m is None or ind_5m.empty or len(ind_5m) < (self.vol_sma_len + 5):
            return None
            
        try:
            last_candle = ind_5m.iloc[-1]
            prev_candle = ind_5m.iloc[-2]

            # 1. Band Touch Signal
            bb_low = Decimal(str(last_candle[f'BBL_{self.bb_len}_{self.bb_std}']))
            current_low = Decimal(str(last_candle['low']))
            
            if current_low > bb_low:
                return None
                
            # 2. Reversal Confirmation (RSI + Stoch)
            rsi = Decimal(str(last_candle['RSI_14']))
            prev_rsi = Decimal(str(prev_candle['RSI_14']))
            stoch_k = Decimal(str(last_candle[f'STOCHk_{self.stoch_period}_{self.stoch_k}_{self.stoch_d}']))
            stoch_d = Decimal(str(last_candle[f'STOCHd_{self.stoch_period}_{self.stoch_k}_{self.stoch_d}']))
            
            is_rsi_exit = (prev_rsi < 30) and (rsi > 30)
            is_stoch_exit = (stoch_k > stoch_d) and (stoch_k > 20) # Crossover + выход из <20
            
            if not (is_rsi_exit and is_stoch_exit):
                # self.log(f"    -> ОТКЛОНЕНО (BB 5M): Reversal фильтр не пройден (RSI Exit: {is_rsi_exit}, Stoch Exit: {is_stoch_exit})")
                return None

            # 3. Volume Filter
            norm_vol = Decimal(str(last_candle['norm_volume']))
            avg_norm_vol = Decimal(str(last_candle[f'NORM_VOL_SMA_{self.vol_sma_len}']))
            
            if norm_vol <= (avg_norm_vol * Decimal('1.5')):
                # self.log(f"    -> ОТКЛОНЕНО (BB 5M): Низкий Norm. Volume ({norm_vol:.2f} <= {avg_norm_vol*Decimal('1.5'):.2f})")
                return None
            
            # 4. Candle Filter
            if Decimal(str(last_candle['close'])) <= Decimal(str(last_candle['open'])):
                # self.log(f"    -> ОТКЛОНЕНО (BB 5M): Свеча разворота не бычья (Close <= Open)")
                return None
                
            # 5. Trend Filter (ADX < 25 - боковик)
            adx = Decimal(str(last_candle[f'ADX_{self.adx_len}']))
            if adx >= 25:
                # self.log(f"    -> ОТКЛОНЕНО (BB 5M): ADX >= 25 (не боковик, а тренд)")
                return None
                
            atr_14 = Decimal(str(last_candle[f'ATRr_{self.atr_period}']))

        except (ValueError, KeyError, IndexError):
            return None

        entry_price = current_price
        
        # SL: (ATR * 0.8)
        sl_mult = Decimal('0.8')
        stop_loss_price = self._round_price(entry_price - (atr_14 * sl_mult))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # TP: R/R 1.5
        rr_mult = Decimal('1.5')
        reward_per_coin = risk_per_coin * rr_mult
        target_tp = self._round_price(entry_price + reward_per_coin)
        rr_ratio = reward_per_coin / risk_per_coin
        
        if rr_ratio < Decimal('1.5'): return None # (Требование R/R >= 1.5)

        self.log(f"    -> Кандидат (SCALP_BOLLINGER_TOUCH_5M): LONG на 5M (band touch + reversal + volume). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "SCALP_BOLLINGER_TOUCH_5M", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}

    # ---
    # --- *** КОНЕЦ: НОВЫЕ СТРАТЕГИИ v1.1 *** ---
    # ---

    # ---
    # --- ЛОГИКА ОТКРЫТИЯ ПОЗИЦИИ (Изменена v1.0 Scalp) ---
    # ---
    def _calculate_and_open_position(self, best_signal, market_data):
        entry_price = best_signal['entry_price']
        stop_loss_price = best_signal['stop_loss_price']
        self.final_take_profit_price = best_signal['final_take_profit_price']
        rr_ratio = best_signal['rr_ratio']
        self.current_trade_strategy_type = best_signal['type']
        risk_per_coin = entry_price - stop_loss_price
        
        # *** ИЗМЕНЕНИЕ (v1.0 Scalp): TP1 = 50% до Final TP ***
        reward_per_coin = self.final_take_profit_price - entry_price
        if reward_per_coin > 0:
             self.take_profit_price_1 = self._round_price(entry_price + (reward_per_coin * Decimal('0.5')))
        else:
             self.take_profit_price_1 = self.final_take_profit_price
        
        self.log(f"     -> Расчет для {self.current_trade_strategy_type}. R/R: {rr_ratio:.1f}:1")
        # ---

        usdt_balance = market_data['usdt_balance']
        
        # *** ИЗМЕНЕНИЕ (v1.1 Scalp): Риск 0.5x для ВСЕХ скальп-стратегий ***
        risk_per_trade = self.base_risk_per_trade
        # (Проверяем, что это скальпинг-стратегия)
        if "SCALP_" in self.current_trade_strategy_type:
            risk_per_trade = self.base_risk_per_trade * Decimal('0.5')
            self.log(f"     -> Scalping-стратегия, риск уменьшен до {risk_per_trade * 100:.2f}%")
        # ---
        
        risk_capital = usdt_balance * risk_per_trade
        if risk_per_coin <= 0: 
            self.log(f"ИНФО: Вход {self.current_trade_strategy_type} пропущен. Расчетный риск на монету <= 0."); return
        quantity = self._round_quantity(risk_capital / risk_per_coin)
        if quantity <= 0:
            self.log(f"ИНФО: Вход {self.current_trade_strategy_type} пропущен. Рассчитанное количество <= 0 (риск слишком мал)."); return
        
        position_cost = quantity * entry_price
        if position_cost * (Decimal('1') + self.commission_rate) > usdt_balance:
            original_risk_perc = risk_per_trade * 100
            self.log(f"ИНФО: Недостаточно средств для риска {original_risk_perc:.2f}%. Автокорректировка размера позиции.")
            max_affordable_quantity = (usdt_balance / (entry_price * (Decimal('1') + self.commission_rate))) * Decimal('0.998')
            quantity = self._round_quantity(max_affordable_quantity)
            position_cost = quantity * entry_price
            new_risk_capital = quantity * risk_per_coin
            new_risk_perc = (new_risk_capital / usdt_balance) * 100 if usdt_balance > 0 else Decimal('0')
            self.log(f"     -> Размер позиции скорректирован. Новый риск: {new_risk_perc:.2f}%")
            
        if position_cost < self.min_notional:
            self.log(f"ИНФО: Вход пропущен. Размер позиции (${position_cost:.2f}) меньше минимально допустимого (${self.min_notional:.2f})."); return

        self.trade_counter += 1
        self.current_trade_id = f"{self.symbol[:3]}-{self.trade_counter}"
        self.current_trade_pnl = Decimal('0.0')

        try:
            self.log(f"ИСПОЛНЕНИЕ ОРДЕРА (BUY, {self.current_trade_strategy_type}): {quantity} {self.base_asset} по рыночной цене...")
            if self.is_backtest:
                trigger_price = entry_price
                order_result = self.binance_client.create_order(
                    symbol=self.symbol, side=Client.SIDE_BUY, type=Client.ORDER_TYPE_MARKET,
                    quantity=float(quantity), trigger_price=trigger_price
                )
            else:
                order_result = self.binance_client.create_order(
                    symbol=self.symbol, side=Client.SIDE_BUY, type=Client.ORDER_TYPE_MARKET,
                    quantity=float(quantity)
                )
            
            self._process_filled_order(order_result, "SWING OPEN")
            self.position_side, self.stop_loss_price = 'LONG', stop_loss_price
            self.entry_time = self._get_current_time()
            self.initial_quantity = self.quantity
            self.initial_stop_loss_price = stop_loss_price
            self.is_profit_locked, self.is_trailing_active, self.is_tp1_hit = False, False, False
            self._save_state()
            final_risk_amount = risk_per_coin * self.quantity
            self.log(f"✅✅✅ ПОЗИЦИЯ ОТКРЫТА: {self.quantity} {self.base_asset} @ ${self.entry_price:.{self.price_precision}f}. ✅✅✅")
            self.log(f"    - ID СДЕЛКИ: {self.current_trade_id}, Тип: {self.current_trade_strategy_type}")
            self.log(f"    - СТОП-ЛОСС: ${self.stop_loss_price:.{self.price_precision}f} (Риск: ${final_risk_amount:.2f})")
            
            # (Все скальп-стратегии используют TP1 + Final TP)
            self.log(f"    - TP1 (50%): ${self.take_profit_price_1:.{self.price_precision}f}, Финальный TP: ${self.final_take_profit_price:.{self.price_precision}f} (RR: {rr_ratio:.1f}:1)")

        except BinanceAPIException as e:
            if e.code == -2010: self.log(f"ОШИБКА ОТКРЫТИЯ: Недостаточно средств на балансе. {e.message}")
            else: self.log(f"ОШИБКА API при открытии позиции: {e}")
            self._reset_position_state()
        except Exception as e: 
            self.log(f"КРИТИЧЕСКАЯ ОШИБКА при открытии позиции: {e}"); self._reset_position_state()

    # ---
    # --- ЛОГИКА УПРАВЛЕНИЯ ВЫХОДОМ (v1.1 Scalp - Добавлен Timeout) ---
    # ---
    def _check_and_manage_exit_conditions(self, market_data, current_price, current_high, current_low, current_1m_candle):
        if not self.position_side: return
        current_open = current_price
        if self.is_backtest and current_1m_candle is not None:
            current_open = Decimal(str(current_1m_candle['open']))
        
        # 1. Проверка СТОП-ЛОССА
        if current_low <= self.stop_loss_price:
            self.sl_confirmation_counter += 1
            # (Для скальпинга v1.0, 1 минута = 1 подтверждение. 2 мин = выход)
            sl_confirm_needed = 2 
            self.log(f"⚠️ ПРЕДУПРЕЖДЕНИЕ SL: Цена ({current_low:.{self.price_precision}f}) <= Стоп-лосс ({self.stop_loss_price:.{self.price_precision}f}). Подтверждение {self.sl_confirmation_counter}/{sl_confirm_needed}...")
            self._save_state()
            if self.sl_confirmation_counter >= sl_confirm_needed:
                reason = "TRAIL STOP" if self.is_trailing_active else "STOP LOSS"
                self.log(f"✅ ВЫХОД: {reason} ПОДТВЕРЖДЕН ({sl_confirm_needed} мин). Минимальная цена 1М свечи (${current_low:.{self.price_precision}f}) достигла/пробила стоп-уровень (${self.stop_loss_price:.{self.price_precision}f}).")
                exec_price = min(current_open, self.stop_loss_price)
                self.log(f"    -> Цена исполнения (SL): ${exec_price:.{self.price_precision}f}")
                self._close_position(reason=f"{reason} ({sl_confirm_needed}-min confirm)", is_partial=False, execution_price=exec_price)
                return
        else:
            if self.sl_confirmation_counter > 0:
                self.log(f"ИНФО: Условие SL больше не выполняется. Cброс счетчика подтверждения ({self.sl_confirmation_counter} -> 0).")
                self.sl_confirmation_counter = 0; self._save_state()
        
        # (Удален выход по ADX для Momentum)
        
        # 2. Управление по Времени (SCALP TIMEOUT)
        if self.entry_time:
            trade_duration_minutes = (self._get_current_time() - self.entry_time).total_seconds() / 60
            max_duration_minutes = None
            
            # (Существующие таймауты v1.0)
            if self.current_trade_strategy_type == "SCALP_BREAKOUT_CONFIRM_1M": 
                max_duration_minutes = 5 # (3-5 мин)
            elif self.current_trade_strategy_type == "SCALP_LIQUIDITY_SWEEP_3M": 
                max_duration_minutes = 12 # (9-12 мин)
            elif self.current_trade_strategy_type == "SCALP_RSI_VOLUME_5M": 
                max_duration_minutes = 20 # (15-20 мин)
                
            # *** НАЧАЛО ИЗМЕНЕНИЯ (v1.1): Таймауты для новых стратегий ***
            elif self.current_trade_strategy_type == "SCALP_PRICE_ACTION_1M": 
                max_duration_minutes = 6 # (3-6 мин)
            elif self.current_trade_strategy_type == "SCALP_MOMENTUM_BREAK_3M": 
                max_duration_minutes = 15 # (9-15 мин)
            elif self.current_trade_strategy_type == "SCALP_BOLLINGER_TOUCH_5M": 
                max_duration_minutes = 25 # (15-25 мин)
            # *** КОНЕЦ ИЗМЕНЕНИЯ ***

            if max_duration_minutes and trade_duration_minutes >= max_duration_minutes:
                self.log(f"!!! УПРАВЛЕНИЕ ПО ВРЕМЕНИ (TIMEOUT): Сделка {self.current_trade_strategy_type} >{max_duration_minutes} мин. Принудительное закрытие.")
                self._close_position(reason=f"TIMEOUT ({max_duration_minutes}m)", is_partial=False, execution_price=current_open)
                return
        
        # 3. Проверка ТЕЙК-ПРОФИТОВ
        if not self.is_tp1_hit and current_high >= self.final_take_profit_price:
             self.log(f"ВЫХОД: Сработал Финальный ТЕЙК-ПРОФИТ (до TP1) по цене ${self.final_take_profit_price:.{self.price_precision}f} (High: {current_high})")
             exec_price = max(current_open, self.final_take_profit_price)
             self.log(f"    -> Цена исполнения (TP Final): ${exec_price:.{self.price_precision}f}")
             self._close_position(reason="FINAL TP", is_partial=False, execution_price=exec_price); return
        
        if self.is_tp1_hit and current_high >= self.final_take_profit_price:
            self.log(f"ВЫХОД: Сработал Финальный ТЕЙК-ПРОФИТ (после TP1) по цене ${self.final_take_profit_price:.{self.price_precision}f} (High: {current_high})")
            exec_price = max(current_open, self.final_take_profit_price)
            self.log(f"    -> Цена исполнения (TP Final): ${exec_price:.{self.price_precision}f}")
            self._close_position(reason="FINAL TP", is_partial=False, execution_price=exec_price); return
        
        if not self.is_tp1_hit and current_high >= self.take_profit_price_1:
            # (Все скальп-стратегии используют TP1)
            self.log(f"ФИКСАЦИЯ: Сработал Тейк-Профит 1 по цене ${self.take_profit_price_1:.{self.price_precision}f} (High: {current_high})")
            exec_price = max(current_open, self.take_profit_price_1)
            self.log(f"    -> Цена исполнения (TP1): ${exec_price:.{self.price_precision}f}")
            self._close_position(reason="TP1", is_partial=True, partial_ratio=0.5, execution_price=exec_price)
            self.is_tp1_hit = True; 
            
            # (Трейлинг для скальпинга: SL в БУ + активация ATR)
            self.stop_loss_price = self.entry_price; 
            self.is_trailing_active = True
            
            self.log(f"УПРАВЛЕНИЕ: Позиция обезопасена. Стоп в безубытке, ТРЕЙЛИНГ ПО ATR АКТИВИРОВАН.")
            self._save_state(); return
        
        # 4. Логика Трейлинг-Стопа
        if self.is_trailing_active:
            # (Для скальпинга нет 'profit lock' на 2R, только ATR трейлинг)
            
            # (Используем 15M ATR для более стабильного трейлинга)
            ind_15m = market_data.get('indicators_15m')
            if ind_15m is not None and not ind_15m.empty:
                try:
                    atr_15m = Decimal(str(ind_15m.iloc[-1][f'ATRr_{self.atr_period}']))
                    # (Для скальпинга используем более агрессивный трейлинг, 1.5 * ATR)
                    trail_mult = Decimal('1.5') 
                    new_sl = self._round_price(current_price - (atr_15m * trail_mult)) 
                    if new_sl > self.stop_loss_price:
                        self.stop_loss_price = new_sl; self._save_state()
                        self.log(f"УПРАВЛЕНИЕ: Трейлинг-стоп (15m ATR) подтянут до ${self.stop_loss_price:.{self.price_precision}f}")
                except (ValueError, KeyError):
                    pass # Ошибка ATR
        
        if not self.is_backtest:
            log_type = "ТРЕЙЛИНГ" if self.is_trailing_active else "УПРАВЛЕНИЕ"
            log_tp = self.final_take_profit_price if self.is_tp1_hit else f"TP1: {self.take_profit_price_1:.{self.price_precision}f}"
            pass


    # ---
    # --- ЛОГИКА ЗАКРЫТИЯ И ОБРАБОТКИ (Без изменений) ---
    # ---
    def _close_position(self, reason="", is_partial=False, partial_ratio=0.5, execution_price=None):
        if not self.position_side: return
        qty_to_sell = (self.quantity * Decimal(str(partial_ratio))) if is_partial else self.quantity
        if qty_to_sell <= 0: return
        try:
            qty_to_sell = self._round_quantity(qty_to_sell)
            
            if not self.is_backtest:
                actual_balance_dict = self.binance_client.get_asset_balance(asset=self.base_asset)
                actual_balance = Decimal(actual_balance_dict['free'])
                if is_partial: 
                    qty_to_sell = self._round_quantity(actual_balance * Decimal(str(partial_ratio)))
                else: 
                    qty_to_sell = self._round_quantity(actual_balance)
                if qty_to_sell <= 0:
                    self.log(f"Доступное количество {self.base_asset} <= 0. Позиция считается закрытой.")
                    self._reset_position_state(); self._save_state(); return
            
            if self.is_backtest and not is_partial and qty_to_sell > self.quantity:
                qty_to_sell = self.quantity
                
            log_prefix = "ЧАСТИЧНОЕ ЗАКРЫТИЕ" if is_partial else "ПОЛНОЕ ЗАКРЫТИЕ"
            self.log(f"ЗАПУСК {log_prefix}. Причина: {reason}.")
            
            if self.is_backtest:
                order = self.binance_client.create_order(
                    symbol=self.symbol, side=Client.SIDE_SELL, type=Client.ORDER_TYPE_MARKET,
                    quantity=float(qty_to_sell), trigger_price=execution_price
                )
            else:
                order = self.binance_client.create_order(
                    symbol=self.symbol, side=Client.SIDE_SELL, type=Client.ORDER_TYPE_MARKET,
                    quantity=float(qty_to_sell)
                )

            self._process_filled_order(order, f"CLOSE {self.position_side}", is_partial)
            
            if is_partial: 
                self.quantity -= qty_to_sell
            else: 
                self._reset_position_state()
                
            self._save_state()
            
        except Exception as e: 
            self.log(f"ОШИБКА при {'частичном' if is_partial else 'полном'} закрытии: {e}")
            if not is_partial: self._reset_position_state(); self._save_state()
    
    def _process_filled_order(self, order, order_type_str, is_partial=False):
        if not order or not order.get('fills'): self.log("Ордер не содержит информации об исполнении."); return
        fills = order['fills']; total_qty = sum(Decimal(f['qty']) for f in fills); total_cost = sum(Decimal(f['qty']) * Decimal(f['price']) for f in fills); total_comm = sum(Decimal(f['commission']) for f in fills)
        avg_price = total_cost / total_qty if total_qty > 0 else Decimal('0'); comm_usdt = self._convert_commission_to_usdt(total_comm, fills[0]['commissionAsset'])
        if 'CLOSE' not in order_type_str:
            self.entry_price, self.quantity, self.entry_commission_cost = avg_price, total_qty, comm_usdt
            self.total_fees_paid_usdt += comm_usdt
            trade_info = {'trade_id': self.current_trade_id, 'strategy': self.current_trade_strategy_type, 'side': 'LONG', 'entry_time': self._get_current_time().strftime('%y-%m-%d %H:%M'), 'entry_price': f"{avg_price:.{self.price_precision}f}", 'quantity': f"{total_qty:.{self.qty_precision}f}",}
            self._add_trade_to_history_gui(trade_info)
        else:
            pnl_gross = (avg_price - self.entry_price) * total_qty
            commission_to_attribute = self.entry_commission_cost * (total_qty / self.initial_quantity) if self.initial_quantity > 0 else 0
            net_pnl = pnl_gross - commission_to_attribute - comm_usdt
            self.total_pnl_usdt += net_pnl; self.total_fees_paid_usdt += comm_usdt; self.current_trade_pnl += net_pnl
            log_prefix = "ЧАСТЬ СДЕЛКИ" if is_partial else "СДЕЛКА"
            self.log(f"🏁 {log_prefix} {self.current_trade_id} ЗАКРЫТА. PnL (чистый): ${net_pnl:.2f}")
            stype = self.current_trade_strategy_type
            if not is_partial:
                self.pnl_by_strategy[stype] += self.current_trade_pnl
                if self.current_trade_pnl > 0: self.win_trades += 1; self.wins_by_strategy[stype] += 1
                else: self.loss_trades += 1; self.losses_by_strategy[stype] += 1
                self.log(f"ИТОГ СДЕЛКИ ({stype}): PnL: ${self.current_trade_pnl:.2f}, Комиссии: ${comm_usdt + commission_to_attribute:.2f}")
            remaining_qty_val = self.quantity - total_qty
            if not is_partial:
                remaining_qty_val = Decimal('0.0')
            trade_update_info = {
                'trade_id': self.current_trade_id,
                'strategy': stype,
                'exit_time': self._get_current_time().strftime('%y-%m-%d %H:%M'),
                'exit_price': f"{avg_price:.{self.price_precision}f}",
                'pnl': f"{net_pnl:.2f}",
                'is_partial': is_partial,
                'remaining_quantity': f"{remaining_qty_val:.{self.qty_precision}f}"
            }
            self._update_trade_in_history_gui(trade_update_info)
    
    def _reset_position_state(self):
        # (Эта функция без изменений)
        self.position_side = None; self.entry_price, self.quantity, self.initial_quantity = Decimal('0.0'), Decimal('0.0'), Decimal('0.0'); self.stop_loss_price, self.take_profit_price_1, self.final_take_profit_price, self.entry_commission_cost = Decimal('0.0'), Decimal('0.0'), Decimal('0.0'), Decimal('0.0')
        self.is_profit_locked, self.is_trailing_active, self.is_tp1_hit = False, False, False; self.sl_confirmation_counter = 0; self.initial_stop_loss_price = Decimal('0.0')
        self.current_trade_id = None; self.current_trade_pnl = Decimal('0.0'); self.entry_time = None; self.current_trade_strategy_type = "UNKNOWN"
        
    def _handle_disconnection(self):
        # (Эта функция без изменений)
        self.log("Потеряно соединение с Binance. Попытка восстановления..."); self._update_status_gui("Переподключение...")
        while not self.stop_event.is_set():
            try:
                self.binance_client.ping(); self.is_connected = True; self.reconnect_attempts = 0
                self.log("✅ Соединение с Binance восстановлено!"); self._update_status_gui("В работе..."); break
            except (BinanceRequestException, requests.exceptions.RequestException):
                self.reconnect_attempts += 1; delay = min(600, 10 * (2 ** (self.reconnect_attempts - 1)))
                self.log(f"Попытка переподключения #{self.reconnect_attempts} не удалась. Следующая попытка через {delay} секунд."); self._sleep_interruptible(delay)

    def _initialize_apis(self):
        # (Эта функция без изменений)
        if self.is_backtest: self.log("✅ API симулятор для бэктеста инициализирован."); self.is_connected = True; return True
        try:
            self.binance_client = Client(self.api_key, self.api_secret, {"timeout": 30}); self.binance_client.ping()
            self.log("✅ Успешное подключение к Binance API."); self.is_connected = True; return True
        except Exception as e: self.log(f"❌ ОШИБКА подключения к Binance: {e}"); self.is_connected = False; return True

    def _get_symbol_info(self):
        # (Эта функция без изменений)
        try:
            info = self.binance_client.get_symbol_info(self.symbol)
            self.base_asset, self.quote_asset = info['baseAsset'], info['quoteAsset']
            if self.is_backtest: self.binance_client.base_asset, self.binance_client.quote_asset = self.base_asset, self.base_asset
            for f in info['filters']:
                if f['filterType'] == 'LOT_SIZE': self.step_size, self.qty_precision = Decimal(f['stepSize']), abs(Decimal(f['stepSize']).as_tuple().exponent)
                if f['filterType'] == 'PRICE_FILTER': self.price_precision = abs(Decimal(f['tickSize']).as_tuple().exponent)
                if f['filterType'] == 'NOTIONAL': self.min_notional = Decimal(f['minNotional'])
            fees_data = self.binance_client.get_trade_fee(symbol=self.symbol)
            self.commission_rate = Decimal(fees_data[0]['makerCommission'])
            if self.is_backtest: self.binance_client.commission_rate = self.commission_rate
            return True
        except Exception as e: self.log(f"Не удалось получить правила торгов для {self.symbol}. Ошибка: {e}"); return False

    def _get_market_data(self):
        # (v1.0 Scalp: 1m, 3m, 5m, 15m, 1d)
        try:
            # (Добавляем недостающие константы, если они не импортированы)
            if not hasattr(Client, 'KLINE_INTERVAL_3MINUTE'): Client.KLINE_INTERVAL_3MINUTE = '3m'
            if not hasattr(Client, 'KLINE_INTERVAL_5MINUTE'): Client.KLINE_INTERVAL_5MINUTE = '5m'
            if not hasattr(Client, 'KLINE_INTERVAL_15MINUTE'): Client.KLINE_INTERVAL_15MINUTE = '15m'
                
            kline_calls = {
                Client.KLINE_INTERVAL_1MINUTE: 300,
                Client.KLINE_INTERVAL_3MINUTE: 200,
                Client.KLINE_INTERVAL_5MINUTE: 150,
                Client.KLINE_INTERVAL_15MINUTE: 205,
                Client.KLINE_INTERVAL_1DAY: 250
            }
            
            with ThreadPoolExecutor(max_workers=6) as executor:
                future_map = {}
                for interval, limit in kline_calls.items(): 
                    future_map[executor.submit(self.binance_client.get_klines, symbol=self.symbol, interval=interval, limit=limit)] = {'type': 'klines', 'interval': interval}
                
                future_map[executor.submit(self.binance_client.get_asset_balance, asset=self.quote_asset)] = {'type': 'usdt_balance'}
                future_map[executor.submit(self.binance_client.get_asset_balance, asset=self.base_asset)] = {'type': 'base_balance'}
                future_map[executor.submit(self.binance_client.get_symbol_ticker, symbol=self.symbol)] = {'type': 'ticker'}
                
                results, klines_results = {}, {}
                for future in as_completed(future_map):
                    task_info, task_type = future_map[future], future_map[future]['type']
                    try:
                        result_data = future.result()
                        if task_type == 'klines': klines_results[task_info['interval']] = result_data
                        else: results[task_type] = result_data
                    except Exception as e: self.log(f"Ошибка в подзадаче {task_type} ({task_info.get('interval', 'N/A')}): {e}"); return None
            
            return {
                "indicators_1m": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_1MINUTE), "1m"),
                "indicators_3m": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_3MINUTE), "3m"),
                "indicators_5m": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_5MINUTE), "5m"),
                "indicators_15m": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_15MINUTE), "15m"),
                "indicators_1d": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_1DAY), "1d"),
                "usdt_balance": Decimal(results.get("usdt_balance", {}).get('free', '0')), 
                "base_balance": Decimal(results.get("base_balance", {}).get('free', '0')),
                "current_price": Decimal(results.get("ticker", {}).get('price', '0'))
            }
        except Exception as e: self.log(f"Ошибка получения данных: {e}"); return None

    def _calculate_indicators(self, klines, interval='N/A'):
        # (ИЗМЕНЕНО v1.1 Scalp: Добавлены EMA 5, 10, BB, Stoch, Price Action)
        
        # (Проверка на пустой список)
        if not klines: 
             return pd.DataFrame()
        
        df = pd.DataFrame(klines, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume', 'close_time', 'qav', 'trades', 'tbav', 'tqav', 'ig'])
        for col in ['open', 'high', 'low', 'close', 'volume']: df[col] = pd.to_numeric(df[col])
        
        # *** НАЧАЛО: ИСПРАВЛЕНИЕ (АНАЛИЗ) ***
        # Добавляем проверку на NaN и достаточную длину
        df = df.dropna(subset=['open', 'high', 'low', 'close'])
        if len(df) < 50:
            self.log(f"Предупреждение: Недостаточно данных для {interval} ({len(df)} свечей). Пропуск индикаторов.")
            return pd.DataFrame()
        # *** КОНЕЦ: ИСПРАВЛЕНИЕ (АНАЛИЗ) ***
        
        
        # (Новые EMA для скальпинга)
        df.ta.ema(length=self.ema_scalp_fast_len, append=True) # 5
        df.ta.ema(length=self.ema_scalp_slow_len, append=True) # 10
        df.ta.ema(length=self.ema_trend_len, append=True)      # 200
        
        df.ta.rsi(length=self.rsi_period, append=True); df.ta.atr(length=self.atr_period, append=True); df.ta.stochrsi(append=True)
        df.ta.adx(length=self.adx_len, append=True)
        
        # (BBANDS НУЖНЫ)
        
        df[f'VOL_SMA_{self.vol_sma_len}'] = ta.sma(df['volume'], length=self.vol_sma_len)
        
        # (Нормализованный объем)
        atr_col = f'ATRr_{self.atr_period}'
        
        # *** ИСПРАВЛЕНИЕ (v1.1): Замена fillna(method='ffill') на .ffill() ***
        safe_atr = df[atr_col].replace(0, np.nan).ffill().fillna(1)
        
        safe_atr[safe_atr == 0] = 1 
        df['norm_volume'] = df['volume'] / safe_atr
        df[f'NORM_VOL_SMA_{self.vol_sma_len}'] = ta.sma(df['norm_volume'], length=self.vol_sma_len)
        
        # (MACD)
        df.ta.macd(append=True) 

        # *** НАЧАЛО ИЗМЕНЕНИЯ (v1.1): Новые индикаторы ***
        
        # (Bollinger Bands)
        df.ta.bbands(length=self.bb_len, std=self.bb_std, append=True)
        
        # (Standard Stochastic)
        df.ta.stoch(length=self.stoch_period, k=self.stoch_k, d=self.stoch_d, append=True)
        
        # (Price Action Patterns - manual calculation)
        try:
            # Bullish Engulfing (Current open < prev close, Current close > prev open, Current close > prev high)
            df['bull_engulf'] = (df['open'] < df['close'].shift(1)) & \
                                 (df['close'] > df['open'].shift(1)) & \
                                 (df['close'] > df['high'].shift(1))
            
            # Pin Bar (Low < 3-bar low, Close > 70% of candle range from bottom)
            # (Используем rolling(4) для 3 предыдущих + текущая, затем shift(1) для 3 предыдущих)
            rolling_low = df['low'].rolling(window=4, min_periods=4).min().shift(1)
            candle_range = df['high'] - df['low']
            
            # *** ИСПРАВЛЕНИЕ (v1.1): Замена Decimal('0.7') на float 0.7 ***
            candle_body_threshold = df['open'] + (candle_range * 0.7)
            
            df['pin_bar'] = (df['low'] < rolling_low) & \
                            (df['close'] > candle_body_threshold) & \
                            (candle_range > 0)
        except Exception as e:
            # self.log(f"Предупреждение: не удалось рассчитать PA паттерны: {e}")
            df['bull_engulf'] = False
            df['pin_bar'] = False
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***
            
        return df
    
    def _log_daily_status(self, reason):
        # (Эта функция без изменений)
        self._update_status_gui(f"{reason}")

    def stop(self): self.log("Получен сигнал на остановку..."); self.stop_event.set()
    def _sleep_interruptible(self, seconds):
        # (Эта функция без изменений)
        if self.is_backtest: return
        sleep_interval, end_time = 0.1, time.time() + seconds
        while time.time() < end_time:
            if self.stop_event.is_set(): break
            remaining_time = end_time - time.time()
            time.sleep(min(sleep_interval, remaining_time))
            
    def _wait_or_continue(self, seconds=None):
        # (Эта функция без изменений)
        if self.is_backtest: self.binance_client._advance_tick(); return
        if seconds is not None: self._sleep_interruptible(seconds)
        else:
            try:
                current_time = self._get_current_time(); buffer_seconds = 0.5; seconds_past_minute = current_time.second + (current_time.microsecond / 1_000_000)
                seconds_to_sleep = (60.0 - seconds_past_minute) + buffer_seconds
                if seconds_to_sleep < 0 or seconds_to_sleep > 65: self.log(f"ПРЕДУПРЕЖДЕНИЕ: Ошибка расчета синхронизации (расчет: {seconds_to_sleep}с). Сплю 60с."); seconds_to_sleep = 60.0
                self._sleep_interruptible(seconds_to_sleep)
            except Exception as e: self.log(f"Ошибка синхронизации времени: {e}. Сплю 60 секунд (fallback)."); self._sleep_interruptible(60)
            
    def _round_price(self, price): return price.quantize(Decimal('1e-' + str(self.price_precision)))
    def _round_quantity(self, qty): return (qty // self.step_size) * self.step_size
    def _convert_commission_to_usdt(self, commission, asset):
        # (Эта функция без изменений)
        if asset == self.quote_asset or commission <= 0: return commission if asset == self.quote_asset else Decimal('0')
        try: return commission * Decimal(self.binance_client.get_symbol_ticker(symbol=f"{asset}{self.quote_asset}")['price'])
        except: return Decimal('0')
    
    def log(self, message): 
        # (Эта функция без изменений)
        mode = "BACKTEST" if self.is_backtest else "LIVE"
        current_time_dt = self._get_current_time()
        
        if self.is_backtest:
            current_time_str = current_time_dt.strftime('%Y-%m-%d %H:%M')
        else:
            current_time_str = current_time_dt.strftime('%Y-%m-%d %H:%M:%S')
        
        detailed_message = f"[{mode} {current_time_str}] {message}"
        
        logger.info(detailed_message)
        self.event_queue.put({'type': 'log', 'data': detailed_message})

    def _update_dashboard_data(self, market_data, current_price):
        # (Изменено v1.0 Scalp: Удалены индикаторы 4H)
        pv = market_data['usdt_balance'] + (market_data['base_balance'] * current_price); wr = (self.win_trades/(self.win_trades+self.loss_trades)*100) if (self.win_trades+self.loss_trades)>0 else 0
        unrealized_pnl = "N/A"
        if self.position_side == 'LONG': pnl = (current_price - self.entry_price) * self.quantity; unrealized_pnl = f"{pnl:+.2f}"
        data = {'usdt_balance':f"{market_data['usdt_balance']:.2f}", 'base_balance':f"{market_data['base_balance']:.{self.qty_precision}f}", 'portfolio_value':f"{pv:.2f}", 'unrealized_pnl': unrealized_pnl, 'total_pnl':f"{self.total_pnl_usdt:.2f}", 'total_fees':f"{self.total_fees_paid_usdt:.4f}", 'win_rate':f"{wr:.1f}% ({self.win_trades}/{self.loss_trades})"}
        
        # (Блок индикаторов 4H удален, т.к. market_data['indicators_4h'] больше не существует)
        
        self.event_queue.put({'type': 'dashboard_update', 'data': data})
        
        # (Обновление статистики по новым стратегиям v1.1)
        stats_data = {}
        for stype in self.strategy_types:
            if stype == "UNKNOWN": continue
            wins = self.wins_by_strategy.get(stype, 0); losses = self.losses_by_strategy.get(stype, 0); total = wins + losses
            wr = (wins / total * 100) if total > 0 else 0; pnl = self.pnl_by_strategy.get(stype, Decimal('0.0'))
            stats_data[stype] = {'pnl': f"{pnl:+.2f}", 'wr': f"{wr:.1f}% ({wins}/{losses})"}
        self.event_queue.put({'type': 'strategy_stats_update', 'data': stats_data})
    
    # --- Функции обратной связи с GUI (без изменений) ---
    def _add_trade_to_history_gui(self, trade_info): self.event_queue.put({'type': 'new_trade', 'data': trade_info})
    def _update_trade_in_history_gui(self, trade_info): self.event_queue.put({'type': 'update_trade', 'data': trade_info})
    def _update_gui_status(self, is_running): self.event_queue.put({'type': 'status_update', 'data': {'is_running': is_running}})
    def _update_status_gui(self, status_text): self.event_queue.put({'type': 'status_text_update', 'data': status_text})
    def _stop_bot_on_error(self, message): self.log(f"Критическая ошибка: {message}. Бот остановлен."); self._update_gui_status(is_running=False)
    
    def _get_current_time(self):
        # (Эта функция без изменений)
        if self.is_backtest:
            current_tick = min(self.binance_client.current_tick, self.binance_client.total_ticks - 1)
            return datetime.fromtimestamp(self.binance_client.main_data_iterator.iloc[current_tick]['timestamp'] / 1000, tz=UTC)
        else:
            if self.binance_client is None: return datetime.now(UTC)
            return datetime.fromtimestamp(self.binance_client.get_server_time()['serverTime'] / 1000, tz=UTC)
    
    def _finalize_run(self):
        # (Эта функция без изменений, self.strategy_types обновлен v1.1)
        self._save_state()
        if not self.stop_event.is_set():
            self.log("\n" + "="*50)
            if self.is_backtest: 
                final_balance = self.binance_client.balances[self.quote_asset]
                if self.position_side:
                    self.log("ВНИМАНИЕ: Бэктест завершен с открытой позицией. Принудительное закрытие по последней цене...")
                    last_price = Decimal(str(self.binance_client.main_data_iterator.iloc[-1]['close']))
                    final_balance += self.quantity * last_price * (Decimal('1') - self.commission_rate)
                    self.log(f"Стоимость позиции ${self.quantity * last_price:.2f} добавлена к итоговому балансу.")
                self.log(f"🏁🏁🏁 БЭКТЕСТ ЗАВЕРШЕН 🏁🏁🏁\nИтоговый баланс: ${final_balance:.2f} USDT")
            else: self.log("🏁 Бот остановлен.")
            wr = (self.win_trades/(self.win_trades+self.loss_trades)*100) if (self.win_trades+self.loss_trades)>0 else 0
            self.log(f"Итоговый PnL: ${self.total_pnl_usdt:.2f}\nВсего комиссий: ${self.total_fees_paid_usdt:.2f}")
            self.log(f"Win Rate: {wr:.2f}% (Всего сделок: {self.win_trades + self.loss_trades}, W: {self.win_trades}, L: {self.loss_trades})")
            self.log("\n--- ИТОГИ ПО СТРАТЕГИЯМ ---")
            for stype in self.strategy_types:
                if stype == "UNKNOWN" and self.wins_by_strategy.get(stype, 0) == 0 and self.losses_by_strategy.get(stype, 0) == 0: continue
                wins = self.wins_by_strategy.get(stype, 0); losses = self.losses_by_strategy.get(stype, 0); total = wins + losses
                if total == 0: continue
                wr = (wins / total * 100) if total > 0 else 0; pnl = self.pnl_by_strategy.get(stype, Decimal('0.0'))
                self.log(f"  - {stype}:"); self.log(f"    PnL: ${pnl:+.2f} | WR: {wr:.1f}% ({wins} W / {losses} L)")
            self.log("="*50)
        self._update_gui_status(is_running=False)