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


# --- ОСНОВНОЙ КЛАСС ЛОГИКИ БОТА (v9.10 2025 Filters) ---
class TradingBot(threading.Thread):
    
    def __init__(self, api_key, api_secret, event_queue, risk_per_trade, rr_ratio, symbol, active_strategies_config, backtest_client=None):
        super().__init__()
        self.daemon = True
        self.api_key, self.api_secret, self.event_queue = api_key, api_secret, event_queue
        try:
            self.base_risk_per_trade = Decimal(str(risk_per_trade)) / 100
            # *** ИЗМЕНЕНИЕ (v9.9): Минимальный RR повышен до 2.0 по рекомендации 2025 ***
            self.base_rr_ratio = Decimal('2.0') # (Было 1.3)
        except (ValueError, TypeError):
            self.log("Ошибка: риск и R/R должны быть числами. Используются значения по умолчанию.")
            self.base_risk_per_trade = Decimal('0.01')
            self.base_rr_ratio = Decimal('2.0')

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

        # --- Статистика по стратегиям ---
        self.strategy_types = [
            "RSI_DIVERGENCE", "PRICE_ACTION", "EMA_CROSS", 
            "MEAN_REVERSION", "BREAKOUT_4H", "MOMENTUM_1H", "UNKNOWN"
        ]
        self.pnl_by_strategy = {stype: Decimal('0.0') for stype in self.strategy_types}
        self.wins_by_strategy = {stype: 0 for stype in self.strategy_types}
        self.losses_by_strategy = {stype: 0 for stype in self.strategy_types}

        # --- Параметры символа ---
        self.base_asset, self.quote_asset = "", "USDT"
        self.step_size, self.qty_precision, self.price_precision = Decimal('0.0001'), 4, 2
        self.commission_rate, self.min_notional = Decimal('0.001'), Decimal('10.0')

        # --- Параметры индикаторов ---
        self.ema_superfast_len, self.ema_fast_len, self.ema_slow_len, self.ema_trend_len = 9, 21, 50, 200
        self.atr_period = 14 
        # *** ИЗМЕНЕНИЕ (v9.9): Множитель SL для Mean Reversion увеличен до 2.0 (по предложению) ***
        self.atr_multiplier_sl = Decimal('2.0') # Множитель для Mean Reversion (Был 1.5 в v9.7)
        self.atr_multiplier_trail = Decimal('2.0')
        self.bb_len, self.bb_std = 20, 2.0
        self.kc_len, self.kc_scalar = 20, 2.0
        self.adx_len = 14
        self.vol_sma_len = 20
        
        self.last_heartbeat_log_time = time.time()
        self.last_hour_checked = None

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
        # (Эта функция без изменений)
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
                try: self.entry_time = datetime.fromisoformat(entry_time_str)
                except ValueError: self.entry_time = None; self.log("Предупреждение: неверный формат даты в файле состояния.")
            else: self.entry_time = None
            self.total_pnl_usdt = Decimal(state.get('total_pnl_usdt', '0.0'))
            self.total_fees_paid_usdt = Decimal(state.get('total_fees_paid_usdt', '0.0'))
            self.win_trades = state.get('win_trades', 0)
            self.loss_trades = state.get('loss_trades', 0)
            self.trade_counter = state.get('trade_counter', 0)
            self.current_trade_id = state.get('current_trade_id', None)
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
        # *** ИЗМЕНЕНИЕ (v9.10): Обновлена версия ***
        bot_name = "Multi-Strategy Trader v9.10 (2025 Filters)"
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
                current_hour = current_time_dt.replace(minute=0, second=0, microsecond=0)
                should_check_logic = (self.last_hour_checked is None or current_hour > self.last_hour_checked)

                if not self.is_connected and not self.is_backtest: self._handle_disconnection(); continue

                current_1m_candle = None; current_high = None; current_low = None
                if self.is_backtest:
                    current_1m_candle = self.binance_client.get_current_candle()
                    if current_1m_candle is None: break 
                    current_high = Decimal(str(current_1m_candle['high']))
                    current_low = Decimal(str(current_1m_candle['low']))

                market_data = self._get_market_data()
                if not market_data: self._wait_or_continue(); continue
                
                current_price = market_data['current_price']
                if not self.is_backtest:
                    current_high = current_price; current_low = current_price
                
                if not self.is_backtest or (tick_counter % 5 == 0):
                    self._update_dashboard_data(market_data, current_price)
                
                if should_check_logic:
                    self.last_hour_checked = current_hour
                    log_msg = f"--- Новая 1H свеча ({current_time_dt.strftime('%Y-%m-%d %H:%M')}). Обновление HTF данных... ---"
                    if self.is_backtest and tick_counter > 0: self.log(log_msg)
                    if not self.is_backtest: self.log(log_msg)
                
                if self.position_side:
                    self._check_and_manage_exit_conditions(market_data, current_price, current_high, current_low, current_1m_candle) 
                else:
                    if market_data['usdt_balance'] < self.min_notional:
                        if self.is_backtest: self.log("Баланс USDT исчерпан. Бэктест остановлен."); break
                        self.log(f"Торговля приостановлена. Недостаточно средств."); self._wait_or_continue(300); continue
                    
                    best_signal = self._get_algorithmic_decision(market_data, current_price)
                    
                    if best_signal:
                        self._calculate_and_open_position(best_signal, market_data)
                    elif should_check_logic: 
                        self.log("Анализ завершен: Нет сигналов, соответствующих Tier-системе (или R/R < 2.0).")
                    
                current_time_seconds = time.time()
                if not self.is_backtest and current_time_seconds - self.last_heartbeat_log_time > 300: 
                    self._log_heartbeat(market_data, current_price)
                    self.last_heartbeat_log_time = current_time_seconds
                elif self.is_backtest and tick_counter % 240 == 0 and tick_counter > 0: 
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
    # --- ЛОГИКА ПРИНЯТИЯ РЕШЕНИЙ (v9.9 - R:R >= 2.0) ---
    # ---
    def _get_algorithmic_decision(self, market_data, current_price):
        
        ind_1d = market_data.get('indicators_1d')
        is_1d_bull_trend = False
        if ind_1d is None or len(ind_1d) < self.ema_trend_len:
            reason = f"Ожидание данных для 1D ({len(ind_1d) if ind_1d is not None else 0}/{self.ema_trend_len})"
            self._log_daily_status(reason); return None
        try:
            price_1d = Decimal(str(ind_1d.iloc[-1]['close']))
            ema200_1d = Decimal(str(ind_1d.iloc[-1][f'EMA_{self.ema_trend_len}']))
            is_1d_bull_trend = price_1d > ema200_1d
        except ValueError:
            self.log("Предупреждение: Недопустимые данные в индикаторах 1D. Пропуск."); return None

        self._log_daily_status(f"1D Тренд: {'' if is_1d_bull_trend else 'НЕ '}Бычий. Поиск сигналов...")

        key_levels = self._get_key_levels(market_data['indicators_4h'])

        signals = {
            "RSI_DIVERGENCE": None, "MEAN_REVERSION": None, "PRICE_ACTION": None,
            "EMA_CROSS": None, "BREAKOUT_4H": None, "MOMENTUM_1H": None
        }
        
        if self.active_strategies.get("RSI_DIVERGENCE", False):
            signals["RSI_DIVERGENCE"] = self._find_entry_rsi_divergence_4h(market_data, current_price)
        if self.active_strategies.get("MEAN_REVERSION", False):
            signals["MEAN_REVERSION"] = self._find_entry_mean_reversion_4h(market_data, current_price)
        if self.active_strategies.get("PRICE_ACTION", False):
            signals["PRICE_ACTION"] = self._find_entry_price_action_1h(market_data, current_price, key_levels)
        if self.active_strategies.get("EMA_CROSS", False):
            signals["EMA_CROSS"] = self._find_entry_ema_pullback_4h(market_data, current_price, key_levels, is_1d_bull_trend)
        
        if self.active_strategies.get("BREAKOUT_4H", False):
            signals["BREAKOUT_4H"] = self._find_entry_breakout_retest_4h(market_data, current_price, key_levels, is_1d_bull_trend)
        if self.active_strategies.get("MOMENTUM_1H", False):
            signals["MOMENTUM_1H"] = self._find_entry_momentum_pullback_1h(market_data, current_price, key_levels, is_1d_bull_trend)
        
        # --- УРОВЕНЬ 1: Сигналы Разворота (Высший приоритет) ---
        # *** ИЗМЕНЕНИЕ (v9.9): Проверка R/R >= self.base_rr_ratio (который теперь 2.0) ***
        tier_1_signals = [signals["RSI_DIVERGENCE"], signals["MEAN_REVERSION"]]
        valid_tier_1 = [s for s in tier_1_signals if s and s.get('rr_ratio', Decimal('0')) >= self.base_rr_ratio]
        
        if valid_tier_1:
            best_signal = max(valid_tier_1, key=lambda x: x['rr_ratio'])
            self.log(f"    -> ✅ ВЫБОР (TIER 1 - Разворот): {best_signal['type']} (R/R: {best_signal['rr_ratio']:.2f}:1)")
            return best_signal

        # --- УРОВЕНЬ 2: Сигналы Подтверждения (Средний приоритет) ---
        tier_2_signal = signals["PRICE_ACTION"]
        if tier_2_signal and tier_2_signal.get('rr_ratio', Decimal('0')) >= self.base_rr_ratio:
            best_signal = tier_2_signal
            self.log(f"    -> ✅ ВЫБОР (TIER 2 - PA Подтверждение): {best_signal['type']} (R/R: {best_signal['rr_ratio']:.2f}:1)")
            return best_signal

        # --- УРОВЕНЬ 3: Сигналы "По Тренду" (Низший приоритет) ---
        tier_3_signals = [signals["EMA_CROSS"], signals["BREAKOUT_4H"], signals["MOMENTUM_1H"]]
        valid_tier_3 = [s for s in tier_3_signals if s and s.get('rr_ratio', Decimal('0')) >= self.base_rr_ratio]
        
        if valid_tier_3:
            best_signal = max(valid_tier_3, key=lambda x: x['rr_ratio'])
            self.log(f"    -> ✅ ВЫБОР (TIER 3 - По тренду): {best_signal['type']} (R/R: {best_signal['rr_ratio']:.2f}:1)")
            return best_signal
        
        return None

    
    def _get_key_levels(self, ind_4h):
        # (без изменений)
        levels = {'supports': [], 'resistances': []}
        if ind_4h is None or len(ind_4h) < 60: return levels
        recent_data = ind_4h.iloc[-60:]
        supports = recent_data[(recent_data['low'] < recent_data['low'].shift(1)) & (recent_data['low'] < recent_data['low'].shift(-1))]
        resistances = recent_data[(recent_data['high'] > recent_data['high'].shift(1)) & (recent_data['high'] > recent_data['high'].shift(-1))]
        levels['supports'] = sorted([Decimal(str(s_val)) for s_val in supports['low'].values], reverse=True)
        levels['resistances'] = sorted([Decimal(str(r_val)) for r_val in resistances['high'].values])
        return levels

    # ---
    # --- СТРАТЕГИИ (v9.10 - 2025 Filters) ---
    # ---

    def _find_entry_ema_pullback_4h(self, market_data, current_price, key_levels, is_1d_bull_trend):
        # (ИЗМЕНЕНО v9.10: Используем Vol/ATR)
        if not is_1d_bull_trend:
            return None
        ind_4h = market_data.get('indicators_4h')
        ind_1h = market_data.get('indicators_1h')
        if ind_4h is None or ind_1h is None or len(ind_4h) < self.ema_slow_len or len(ind_1h) < (self.vol_sma_len + 1): return None
        last_4h = ind_4h.iloc[-1]
        try:
            ema9_4h = Decimal(str(last_4h[f'EMA_{self.ema_superfast_len}']))
            ema21_4h = Decimal(str(last_4h[f'EMA_{self.ema_fast_len}']))
            ema50_4h = Decimal(str(last_4h[f'EMA_{self.ema_slow_len}']))
            atr_4h = Decimal(str(last_4h[f'ATRr_{self.atr_period}']))
            adx_4h = Decimal(str(last_4h[f'ADX_{self.adx_len}']))
            if adx_4h < 25: 
                self.log("    -> ОТКЛОНЕНО (EMA Cross): ADX < 25, тренд 4H слишком слабый."); return None
        except (ValueError, KeyError): return None
        if not (ema9_4h > ema21_4h and ema21_4h > ema50_4h): return None
        is_in_zone = (ema50_4h * Decimal('0.998')) < current_price < (ema9_4h * Decimal('1.002'))
        if not is_in_zone: return None
        signal_1h, prev_1h = ind_1h.iloc[-1], ind_1h.iloc[-2]
        is_hammer, is_engulfing = self._is_bullish_hammer(signal_1h), self._is_bullish_engulfing(prev_1h, signal_1h)
        if not (is_hammer or is_engulfing): return None
        
        # *** НАЧАЛО ИЗМЕНЕНИЯ (v9.10 Filters: Vol/ATR) ***
        try:
            # Используем нормализованный объем (по предложению 2025)
            signal_norm_vol_1h = Decimal(str(signal_1h['norm_volume']))
            avg_norm_vol_1h = Decimal(str(prev_1h[f'NORM_VOL_SMA_{self.vol_sma_len}'])) # Среднее с *предыдущей* свечи
            
            rsi_1h = Decimal(str(signal_1h['RSI_14']))
            if signal_norm_vol_1h <= avg_norm_vol_1h: 
                self.log("    -> ОТКЛОНЕНО (EMA Cross): Низкий нормализованный объем (Vol/ATR) на 1H PA свече."); return None
            if rsi_1h < 50:
                self.log("    -> ОТКЛОНЕНО (EMA Cross): RSI < 50 на 1H PA свече."); return None
        except (ValueError, KeyError): return None
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***

        entry_price = current_price
        
        # (v9.9 Smart SL): Множитель 1.5 (по предложению)
        stop_loss_price = self._round_price(ema50_4h - (atr_4h * Decimal('1.5'))) # Ставим SL на 1.5 ATR ниже EMA 50
        
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        target_tp = self._get_next_resistance(key_levels, entry_price)
        if not target_tp: return None
        reward_per_coin = target_tp - entry_price
        if reward_per_coin <= 0: return None
        rr_ratio = reward_per_coin / risk_per_coin
        self.log(f"    -> Кандидат (EMA Pullback): 1H паттерн (Vol/ATR+, RSI>50) на 4H EMA (ADX>25). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "EMA_CROSS", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}

    def _find_entry_rsi_divergence_4h(self, market_data, current_price):
        # (ИЗМЕНЕНО v9.9: Добавлен ADX < 25, MACD Hist > 0, ATR SL 1.5)
        ind_4h = market_data.get('indicators_4h')
        if ind_4h is None or len(ind_4h) < 40: return None
        lookback_period = 30
        recent_data = ind_4h.iloc[-lookback_period:]
        rsi_lows = recent_data[(recent_data['RSI_14'] < recent_data['RSI_14'].shift(1)) & (recent_data['RSI_14'] < recent_data['RSI_14'].shift(-1))]
        if len(rsi_lows) < 2: return None
        last_rsi_low_val, prev_rsi_low_val = rsi_lows.iloc[-1]['RSI_14'], rsi_lows.iloc[-2]['RSI_14']
        last_rsi_low_idx, prev_rsi_low_idx = rsi_lows.index[-1], rsi_lows.index[-2]
        if not (prev_rsi_low_val < 45): return None
        if not (last_rsi_low_val > prev_rsi_low_val): return None # Regular Bullish Div
        price_at_last_rsi_low, price_at_prev_rsi_low = recent_data.loc[last_rsi_low_idx]['low'], recent_data.loc[prev_rsi_low_idx]['low']
        if not (price_at_last_rsi_low < price_at_prev_rsi_low): return None
        is_recent_divergence = (ind_4h.index[-1] - last_rsi_low_idx) <= 5
        if not is_recent_divergence: return None
        
        # *** НАЧАЛО ИЗМЕНЕНИЯ (v9.9 Filters) ***
        try:
            last_4h = ind_4h.iloc[-1]
            adx_4h = Decimal(str(last_4h[f'ADX_{self.adx_len}']))
            macd_hist_4h = Decimal(str(last_4h['MACDh_12_26_9']))
            if adx_4h > 25: 
                self.log("    -> ОТКЛОНЕНО (RSI Div): ADX > 25, не похоже на разворот."); return None
            if macd_hist_4h < 0: 
                self.log("    -> ОТКЛОНЕНО (RSI Div): MACD Histogram < 0, нет подтверждения."); return None
        except (ValueError, KeyError): return None
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***

        entry_price = current_price
        stop_loss_ref_candle = recent_data.loc[last_rsi_low_idx]
        
        try:
            atr_4h = Decimal(str(stop_loss_ref_candle[f'ATRr_{self.atr_period}']))
            divergence_low = Decimal(str(stop_loss_ref_candle['low']))
        except (KeyError, ValueError): return None
        
        # *** НАЧАЛО ИЗМЕНЕНИЯ (v9.9 Smart SL): Множитель 1.5 (по предложению) ***
        stop_loss_price = self._round_price(divergence_low - (atr_4h * Decimal('1.5'))) # Ставим SL на 1.5 ATR ниже минимума дивергенции
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***
        
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        target_tp = self._round_price(Decimal(str(recent_data.loc[prev_rsi_low_idx]['high'])))
        reward_per_coin = target_tp - entry_price
        if reward_per_coin <= 0: return None
        rr_ratio = reward_per_coin / risk_per_coin
        self.log(f"    -> Кандидат (RSI Divergence): 4H дивергенция (ADX<25, MACD+). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "RSI_DIVERGENCE", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}

    def _find_entry_price_action_1h(self, market_data, current_price, key_levels):
       # (ИЗМЕНЕНО v9.10: Используем Vol/ATR)
       ind_1h = market_data.get('indicators_1h')
       if ind_1h is None or len(ind_1h) < (self.vol_sma_len + 1): return None
       signal_candle, prev_candle = ind_1h.iloc[-1], ind_1h.iloc[-2]
       is_hammer, is_engulfing = self._is_bullish_hammer(signal_candle), self._is_bullish_engulfing(prev_candle, signal_candle)
       if not (is_hammer or is_engulfing): return None
       
       # *** НАЧАЛО ИЗМЕНЕНИЯ (v9.10 Filters: Vol/ATR) ***
       try:
           rsi_1h = Decimal(str(signal_candle['RSI_14']))
           
           # Используем нормализованный объем (по предложению 2025)
           avg_norm_volume = Decimal(str(prev_candle[f'NORM_VOL_SMA_{self.vol_sma_len}'])) # Среднее с *предыдущей* свечи
           signal_norm_volume = Decimal(str(signal_candle['norm_volume']))
           
           atr_1h = Decimal(str(signal_candle[f'ATRr_{self.atr_period}']))
           signal_low = Decimal(str(signal_candle['low']))
           atr_perc = (atr_1h / current_price) * 100 if current_price > 0 else Decimal('0')
           
           adx_1h = Decimal(str(signal_candle[f'ADX_{self.adx_len}']))
           if adx_1h > 20: 
               self.log("    -> ОТКЛОНЕНО (PA 1H): ADX > 20, рынок в тренде, а не в 'range'."); return None
       except (ValueError, KeyError): return None
       # *** КОНЕЦ ИЗМЕНЕНИЯ ***
       
       if rsi_1h <= 40 or rsi_1h >= 70: return None
       is_near_support = any(abs(current_price - support) / support < Decimal('0.02') for support in key_levels['supports'])
       if not is_near_support: return None
       
       # *** ИЗМЕНЕНИЕ (v9.10): Проверка нормализованного объема ***
       if signal_norm_volume <= avg_norm_volume: 
           self.log("    -> ОТКЛОНЕНО (PA 1H): Низкий нормализованный объем (Vol/ATR) на сигнальной свече."); return None
       if atr_perc > 3: return None
       
       entry_price = current_price
       
       # (v9.7 Smart SL) - Без изменений (1.0 ATR)
       stop_loss_price = self._round_price(signal_low - (atr_1h * Decimal('1.0')))
       
       risk_per_coin = entry_price - stop_loss_price
       if risk_per_coin <= 0: return None
       target_tp = self._get_next_resistance(key_levels, entry_price)
       if not target_tp: return None
       reward_per_coin = target_tp - entry_price
       if reward_per_coin <= 0: return None
       rr_ratio = reward_per_coin / risk_per_coin
       pattern_type = "hammer" if is_hammer else "engulfing"
       self.log(f"    -> Кандидат (Price Action 1H): Паттерн {pattern_type} (ADX<20, Vol/ATR+), у поддержки. SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
       return {"type": "PRICE_ACTION", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}

    def _find_entry_mean_reversion_4h(self, market_data, current_price):
        # (ИЗМЕНЕНО v9.10: Добавлены MACD+ и DI+ > DI- фильтры)
        ind_4h = market_data.get('indicators_4h')
        if ind_4h is None or len(ind_4h) < (self.bb_len + 1): return None
        last_4h = ind_4h.iloc[-1]
        try:
            adx = Decimal(str(last_4h[f'ADX_{self.adx_len}']))
            rsi = Decimal(str(last_4h['RSI_14']))
            low_price = Decimal(str(last_4h['low']))
            lower_bb = Decimal(str(last_4h[f'BBL_{self.bb_len}_{self.bb_std}_{self.bb_std}']))
            middle_bb = Decimal(str(last_4h[f'BBM_{self.bb_len}_{self.bb_std}_{self.bb_std}']))
            atr_4h = Decimal(str(last_4h[f'ATRr_{self.atr_period}']))
            # *** НАЧАЛО ИЗМЕНЕНИЯ (v9.10): Доп. фильтры (по предложению 2025) ***
            di_plus = Decimal(str(last_4h[f'DMP_{self.adx_len}']))
            di_minus = Decimal(str(last_4h[f'DMN_{self.adx_len}']))
            macd_hist = Decimal(str(last_4h['MACDh_12_26_9']))
            # *** КОНЕЦ ИЗМЕНЕНИЯ ***
        except (ValueError, KeyError): return None
        
        # (v9.9 Filter): ADX < 20
        if adx >= 20: 
            self.log(f"    -> ОТКЛОНЕНО (Mean Rev): ADX ({adx:.1f}) >= 20, рынок в тренде."); return None
        
        # *** НАЧАЛО ИЗМЕНЕНИЯ (v9.10): Доп. фильтры (по предложению 2025) ***
        if macd_hist < 0:
            self.log(f"    -> ОТКЛОНЕНО (Mean Rev): MACD Hist ({macd_hist:.2f}) < 0, нет бычьего подтверждения."); return None
        if di_plus <= di_minus:
            self.log(f"    -> ОТКЛОНЕНО (Mean Rev): DI+ ({di_plus:.1f}) <= DI- ({di_minus:.1f}), нет бычьего направления."); return None
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***

        # (v9.9 Filter): RSI < 30
        if rsi >= 30: 
            self.log(f"    -> ОТКЛОНЕНО (Mean Rev): RSI ({rsi:.1f}) >= 30, не в зоне 'oversold'."); return None

        is_pierced = low_price < (lower_bb * Decimal('0.995'))
        is_at_band = (current_price >= lower_bb) and (low_price < lower_bb)
        if not (is_pierced or is_at_band): return None
        entry_price = current_price
        
        # (v9.9 Smart SL): Множитель 2.0 (через self.atr_multiplier_sl)
        stop_loss_price = self._round_price(low_price - (atr_4h * self.atr_multiplier_sl)) # Используем self.atr_multiplier_sl = 2.0
        
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        target_tp = self._round_price(middle_bb)
        reward_per_coin = target_tp - entry_price
        if reward_per_coin <= 0: return None
        rr_ratio = reward_per_coin / risk_per_coin
        # *** ИЗМЕНЕНИЕ (v9.10): Обновлен лог ***
        self.log(f"    -> Кандидат (Mean Reversion): Возврат в BB (ADX<20, RSI<30, MACD+, DI+). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "MEAN_REVERSION", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}

    def _find_entry_breakout_retest_4h(self, market_data, current_price, key_levels, is_1d_bull_trend):
        # (ИЗМЕНЕНО v9.10: Используем Vol/ATR)
        if not is_1d_bull_trend: return None
        ind_4h = market_data.get('indicators_4h')
        ind_1h = market_data.get('indicators_1h')
        if ind_4h is None or ind_1h is None or len(ind_4h) < 30 or len(ind_1h) < (self.vol_sma_len + 1): return None
        
        prev_4h = ind_4h.iloc[-2]
        signal_1h, prev_1h = ind_1h.iloc[-1], ind_1h.iloc[-2]
        
        try:
            prev_close = Decimal(str(prev_4h['close']))
            prev_upper_kc = Decimal(str(prev_4h[f'KCUe_{self.kc_len}_{self.kc_scalar}']))
            signal_1h_low = Decimal(str(signal_1h['low']))
            atr_1h = Decimal(str(signal_1h[f'ATRr_{self.atr_period}']))
        except (ValueError, KeyError, IndexError): return None
        
        is_breakout_candle = (prev_close > prev_upper_kc)
        if not is_breakout_candle: return None
        
        retest_level = prev_upper_kc
        is_in_retest_zone = (retest_level * Decimal('0.995') < current_price < retest_level * Decimal('1.015'))
        if not is_in_retest_zone: return None
        
        is_hammer, is_engulfing = self._is_bullish_hammer(signal_1h), self._is_bullish_engulfing(prev_1h, signal_1h)
        if not (is_hammer or is_engulfing): return None
        
        # *** НАЧАЛО ИЗМЕНЕНИЯ (v9.10 Filters: Vol/ATR) ***
        try:
            # Используем нормализованный объем (по предложению 2025)
            signal_norm_vol_1h = Decimal(str(signal_1h['norm_volume']))
            avg_norm_vol_1h = Decimal(str(prev_1h[f'NORM_VOL_SMA_{self.vol_sma_len}'])) # Среднее с *предыдущей* свечи
            
            if signal_norm_vol_1h <= avg_norm_vol_1h: 
                self.log("    -> ОТКЛОНЕНО (Breakout): Низкий нормализованный объем (Vol/ATR) на 1H PA свече ретеста."); return None
        except (ValueError, KeyError): return None
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***

        entry_price = current_price
        
        # (v9.7 Smart SL) - Без изменений (1.0 ATR)
        stop_loss_price = self._round_price(signal_1h_low - (atr_1h * Decimal('1.0')))
        
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        target_tp = self._get_next_resistance(key_levels, entry_price)
        if not target_tp: return None 
            
        reward_per_coin = target_tp - entry_price
        if reward_per_coin <= 0: return None 
            
        rr_ratio = reward_per_coin / risk_per_coin
        
        max_rr_cap = Decimal('3.0') 
        if rr_ratio > max_rr_cap:
            self.log(f"    -> (Breakout) R/R ({rr_ratio:.2f}) превышает лимит {max_rr_cap}. Цель скорректирована.")
            rr_ratio = max_rr_cap
            reward_per_coin = risk_per_coin * rr_ratio
            target_tp = self._round_price(entry_price + reward_per_coin)
        
        self.log(f"    -> Кандидат (Breakout & Retest): 1H паттерн (Vol/ATR+) на 4H KC ретесте. SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "BREAKOUT_4H", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}

    def _find_entry_momentum_pullback_1h(self, market_data, current_price, key_levels, is_1d_bull_trend):
        # (ИЗМЕНЕНО v9.10: ADX > 35)
        if not is_1d_bull_trend: return None
        ind_1h = market_data.get('indicators_1h')
        ind_4h = market_data.get('indicators_4h')
        if ind_1h is None or ind_4h is None or len(ind_1h) < 30 or len(ind_4h) < self.ema_slow_len:
            return None
        last_4h = ind_4h.iloc[-1]
        last_1h = ind_1h.iloc[-1]; prev_1h = ind_1h.iloc[-2]
        try:
            price_4h = Decimal(str(last_4h['close']))
            ema_50_4h = Decimal(str(last_4h[f'EMA_{self.ema_slow_len}']))
            if price_4h <= ema_50_4h: return None
            ema_9_1h = Decimal(str(last_1h[f'EMA_{self.ema_superfast_len}']))
            ema_21_1h = Decimal(str(last_1h[f'EMA_{self.ema_fast_len}']))
            atr_1h = Decimal(str(last_1h[f'ATRr_{self.atr_period}'])) 
            if ema_9_1h <= ema_21_1h: return None
            
            # *** НАЧАЛО ИЗМЕНЕНИЯ (v9.10 Filters: ADX > 35) ***
            adx_1h = Decimal(str(last_1h[f'ADX_{self.adx_len}']))
            rsi_1h = Decimal(str(last_1h['RSI_14']))
            # (v9.10): ADX > 35 (по предложению 2025)
            if adx_1h < 35: 
                self.log(f"    -> ОТКЛОНЕНО (Momentum): ADX ({adx_1h:.1f}) < 35, импульс не подтвержден."); return None
            if rsi_1h < 50: 
                self.log(f"    -> ОТКЛОНЕНО (Momentum): RSI ({rsi_1h:.1f}) < 50, нет бычьего моментума."); return None
            # *** КОНЕЦ ИЗМЕНЕНИЯ ***

            if current_price > (ema_21_1h * Decimal('1.003')): return None
            stoch_k_1h = Decimal(str(last_1h['STOCHRSIk_14_14_3_3']))
            stoch_d_1h = Decimal(str(last_1h['STOCHRSId_14_14_3_3']))
            stoch_k_prev_1h = Decimal(str(prev_1h['STOCHRSIk_14_14_3_3']))
            is_oversold_cross = (stoch_k_1h < 30) and (stoch_k_prev_1h <= stoch_d_1h) and (stoch_k_1h > stoch_d_1h)
            if not is_oversold_cross: return None
        except (ValueError, KeyError): return None
        
        entry_price = current_price
        
        # (v9.7 Smart SL) - Без изменений (1.0 ATR)
        stop_loss_price = self._round_price(ema_21_1h - (atr_1h * Decimal('1.0'))) 
        
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None

        target_tp = self._get_next_resistance(key_levels, entry_price)
        if not target_tp: 
            return None 

        reward_per_coin = target_tp - entry_price
        if reward_per_coin <= 0: return None 
            
        rr_ratio = reward_per_coin / risk_per_coin
        
        max_rr_cap = Decimal('3.0') 
        if rr_ratio > max_rr_cap:
            self.log(f"    -> (Momentum) R/R ({rr_ratio:.2f}) превышает лимит {max_rr_cap}. Цель скорректирована.")
            rr_ratio = max_rr_cap
            reward_per_coin = risk_per_coin * rr_ratio
            target_tp = self._round_price(entry_price + reward_per_coin)
        
        self.log(f"    -> Кандидат (Momentum Pullback): StochRSI откат (ADX>35, RSI>50). SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {"type": "MOMENTUM_1H", "entry_price": entry_price, "stop_loss_price": stop_loss_price, "final_take_profit_price": target_tp, "rr_ratio": rr_ratio}
    
    # --- ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ---
    def _is_bullish_pin_bar(self, c):
        c_open, c_close, c_high, c_low = Decimal(str(c['open'])), Decimal(str(c['close'])), Decimal(str(c['high'])), Decimal(str(c['low']))
        body, rng = abs(c_close - c_open), c_high - c_low
        if body == 0 or rng == 0: return False
        return (min(c_open, c_close) - c_low) > body * 2 and body < rng * Decimal('0.33')

    def _is_bullish_hammer(self, c):
       c_open, c_close, c_high, c_low = Decimal(str(c['open'])), Decimal(str(c['close'])), Decimal(str(c['high'])), Decimal(str(c['low']))
       body, rng = abs(c_close - c_open), c_high - c_low
       if body == 0 or rng == 0: return False
       lower_shadow = min(c_open, c_close) - c_low
       upper_shadow = c_high - max(c_open, c_close)
       return (lower_shadow > body * Decimal('2')) and (upper_shadow < body) and (c_close > c_open) and (body < rng * Decimal('0.33'))

    def _is_bullish_engulfing(self, prev_c, c):
        prev_open, prev_close = Decimal(str(prev_c['open'])), Decimal(str(prev_c['close']))
        c_open, c_close = Decimal(str(c['open'])), Decimal(str(c['close']))
        return (c_close > prev_open) and (c_open < prev_close) and (c_close > c_open) and (prev_close < prev_open)

    def _get_next_resistance(self, key_levels, entry_price):
        if not key_levels['resistances']: return None
        for res in key_levels['resistances']:
            if res > entry_price:
                return self._round_price(res)
        return None

    # ---
    # --- ЛОГИКА ОТКРЫТИЯ ПОЗИЦИИ (Без изменений) ---
    # ---
    def _calculate_and_open_position(self, best_signal, market_data):
        entry_price = best_signal['entry_price']
        stop_loss_price = best_signal['stop_loss_price']
        self.final_take_profit_price = best_signal['final_take_profit_price']
        rr_ratio = best_signal['rr_ratio']
        self.current_trade_strategy_type = best_signal['type']
        risk_per_coin = entry_price - stop_loss_price
        
        if self.current_trade_strategy_type in ['MEAN_REVERSION', 'MOMENTUM_1H', 'BREAKOUT_4H']:
            self.take_profit_price_1 = self.final_take_profit_price 
            self.log(f"     -> Расчет для {self.current_trade_strategy_type}. R/R: {rr_ratio:.1f}:1 (Только Финал ТП)")
        else:
            self.take_profit_price_1 = self._round_price(entry_price + (risk_per_coin * Decimal('1.0')))
            self.log(f"     -> Расчет для {self.current_trade_strategy_type}. R/R: {rr_ratio:.1f}:1")

        usdt_balance = market_data['usdt_balance']
        try:
            ind_4h = market_data.get('indicators_4h')
            current_atr_perc = (Decimal(str(ind_4h.iloc[-1]['ATRr_14'])) / entry_price) * 100
        except (IndexError, ValueError):
            self.log("Пропуск открытия: Недопустимые данные 4H ATR."); return
            
        risk_per_trade = self.base_risk_per_trade
        if current_atr_perc > 3:
            risk_per_trade = self.base_risk_per_trade * Decimal('0.5')
            self.log(f"     -> Высокая волатильность (>3% ATR), риск уменьшен до {risk_per_trade * 100:.2f}%")
        
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
            
            if self.current_trade_strategy_type in ['MEAN_REVERSION', 'MOMENTUM_1H', 'BREAKOUT_4H']:
                 self.log(f"    - TP (Финал): ${self.final_take_profit_price:.{self.price_precision}f} (RR: {rr_ratio:.1f}:1)")
            else:
                 self.log(f"    - TP1 (50%): ${self.take_profit_price_1:.{self.price_precision}f}, Финальный TP: ${self.final_take_profit_price:.{self.price_precision}f} (RR: {rr_ratio:.1f}:1)")

        except BinanceAPIException as e:
            if e.code == -2010: self.log(f"ОШИБКА ОТКРЫТИЯ: Недостаточно средств на балансе. {e.message}")
            else: self.log(f"ОШИБКА API при открытии позиции: {e}")
            self._reset_position_state()
        except Exception as e: 
            self.log(f"КРИТИЧЕСКАЯ ОШИБКА при открытии позиции: {e}"); self._reset_position_state()

    # ---
    # --- ЛОГИКА УПРАВЛЕНИЯ ВЫХОДОМ (v9.9 - Добавлен выход по ADX для Momentum) ---
    # ---
    def _check_and_manage_exit_conditions(self, market_data, current_price, current_high, current_low, current_1m_candle):
        if not self.position_side: return
        current_open = current_price
        if self.is_backtest and current_1m_candle is not None:
            current_open = Decimal(str(current_1m_candle['open']))
        
        # 1. Проверка СТОП-ЛОССА
        if current_low <= self.stop_loss_price:
            self.sl_confirmation_counter += 1
            self.log(f"⚠️ ПРЕДУПРЕЖДЕНИЕ SL: Цена ({current_low:.{self.price_precision}f}) <= Стоп-лосс ({self.stop_loss_price:.{self.price_precision}f}). Подтверждение {self.sl_confirmation_counter}/3...")
            self._save_state()
            if self.sl_confirmation_counter >= 3:
                reason = "TRAIL STOP" if self.is_trailing_active else "STOP LOSS"
                self.log(f"✅ ВЫХОД: {reason} ПОДТВЕРЖДЕН (3 мин). Минимальная цена 1М свечи (${current_low:.{self.price_precision}f}) достигла/пробила стоп-уровень (${self.stop_loss_price:.{self.price_precision}f}).")
                exec_price = min(current_open, self.stop_loss_price)
                self.log(f"    -> Цена исполнения (SL): ${exec_price:.{self.price_precision}f}")
                self._close_position(reason=f"{reason} (3-min confirm)", is_partial=False, execution_price=exec_price)
                return
        else:
            if self.sl_confirmation_counter > 0:
                self.log(f"ИНФО: Условие SL больше не выполняется. Cброс счетчика подтверждения ({self.sl_confirmation_counter} -> 0).")
                self.sl_confirmation_counter = 0; self._save_state()
        
        # (v9.9): Выход по угасанию Momentum (ADX < 25)
        if self.current_trade_strategy_type == "MOMENTUM_1H":
            try:
                ind_1h = market_data.get('indicators_1h')
                if ind_1h is not None and not ind_1h.empty:
                    adx_1h = Decimal(str(ind_1h.iloc[-1][f'ADX_{self.adx_len}']))
                    if adx_1h < 25:
                        self.log(f"ВЫХОД (Momentum): 1H ADX ({adx_1h:.1f}) упал < 25. Импульс иссяк.")
                        self._close_position(reason="MOMENTUM EXIT (ADX<25)", is_partial=False, execution_price=current_open)
                        return
            except (ValueError, KeyError, IndexError):
                pass # Игнорируем ошибку индикатора, пусть SL/TP отработают
        
        # 2. Управление по Времени
        if self.entry_time and not self.is_tp1_hit:
            trade_duration = (self._get_current_time() - self.entry_time).total_seconds() / 86400
            max_duration_days = 5
            if trade_duration >= max_duration_days and current_price > self.entry_price:
                self.log(f"!!! УПРАВЛЕНИЕ ПО ВРЕМЕНИ: Сделка в плюсе >{max_duration_days} дней. Активация режима TP1.")
                self._close_position(reason=f"TIME Mgmt ({max_duration_days}d)", is_partial=True, partial_ratio=0.5, execution_price=current_open)
                self.is_tp1_hit = True; self.stop_loss_price = self.entry_price; self.is_trailing_active = True
                self.log(f"УПРАВЛЕНИЕ: Позиция обезопасена. Стоп в безубытке, ТРЕЙЛИНГ ПО ATR АКТИВИРОВАН.")
                self._save_state(); return
        
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
            if self.current_trade_strategy_type in ['MEAN_REVERSION', 'MOMENTUM_1H', 'BREAKOUT_4H']: return 
            self.log(f"ФИКСАЦИЯ: Сработал Тейк-Профит 1 по цене ${self.take_profit_price_1:.{self.price_precision}f} (High: {current_high})")
            exec_price = max(current_open, self.take_profit_price_1)
            self.log(f"    -> Цена исполнения (TP1): ${exec_price:.{self.price_precision}f}")
            self._close_position(reason="TP1", is_partial=True, partial_ratio=0.5, execution_price=exec_price)
            self.is_tp1_hit = True; self.stop_loss_price = self.entry_price; self.is_trailing_active = True
            self.log(f"УПРАВЛЕНИЕ: Позиция обезопасена. Стоп в безубытке, ТРЕЙЛИНГ ПО ATR АКТИВИРОВАН.")
            self._save_state(); return
        
        # 4. Логика Трейлинг-Стопа
        if self.is_trailing_active:
            profit_lock_target = self.entry_price + (self.entry_price - self.initial_stop_loss_price) * 2
            if not self.is_profit_locked and current_high >= profit_lock_target:
                new_stop_price = self.entry_price + (self.entry_price - self.initial_stop_loss_price)
                if new_stop_price > self.stop_loss_price:
                    self.stop_loss_price = self._round_price(new_stop_price)
                    self.is_profit_locked = True; self._save_state()
                    self.log(f"УПРАВЛЕНИЕ: ЗАМОК НА ПРИБЫЛЬ. Цена достигла 2R. Стоп-лосс поднят до 1R: ${self.stop_loss_price:.{self.price_precision}f}")
            
            ind_4h = market_data.get('indicators_4h')
            if ind_4h is not None and not ind_4h.empty:
                atr_4h = Decimal(str(ind_4h.iloc[-1][f'ATRr_{self.atr_period}']))
                new_sl = self._round_price(current_price - (atr_4h * self.atr_multiplier_trail)) 
                if new_sl > self.stop_loss_price:
                    self.stop_loss_price = new_sl; self._save_state()
                    self.log(f"УПРАВЛЕНИЕ: Трейлинг-стоп подтянут по ATR до ${self.stop_loss_price:.{self.price_precision}f}")
        
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
            if self.is_backtest: self.binance_client.base_asset, self.binance_client.quote_asset = self.base_asset, self.quote_asset
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
        # (v9.1 - Без BTC)
        try:
            kline_calls = { Client.KLINE_INTERVAL_1HOUR: 205, Client.KLINE_INTERVAL_4HOUR: 205, Client.KLINE_INTERVAL_1DAY: 250 }
            with ThreadPoolExecutor(max_workers=5) as executor:
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
                    except Exception as e: self.log(f"Ошибка в подзадаче {task_type}: {e}"); return None
            return {
                "indicators_1h": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_1HOUR)),
                "indicators_4h": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_4HOUR)), 
                "indicators_1d": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_1DAY)),
                "usdt_balance": Decimal(results.get("usdt_balance", {}).get('free', '0')), 
                "base_balance": Decimal(results.get("base_balance", {}).get('free', '0')),
                "current_price": Decimal(results.get("ticker", {}).get('price', '0'))
            }
        except Exception as e: self.log(f"Ошибка получения данных: {e}"); return None

    def _calculate_indicators(self, klines):
        # (ИЗМЕНЕНО v9.10: Добавлен MACD, Нормализованный Объем)
        if not klines or len(klines) < 50: return pd.DataFrame()
        df = pd.DataFrame(klines, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume', 'close_time', 'qav', 'trades', 'tbav', 'tqav', 'ig'])
        for col in ['open', 'high', 'low', 'close', 'volume']: df[col] = pd.to_numeric(df[col])
        df.ta.ema(length=self.ema_superfast_len, append=True); df.ta.ema(length=self.ema_fast_len, append=True); df.ta.ema(length=self.ema_slow_len, append=True); df.ta.ema(length=self.ema_trend_len, append=True)
        df.ta.rsi(length=14, append=True); df.ta.atr(length=self.atr_period, append=True); df.ta.stochrsi(append=True)
        df.ta.adx(length=self.adx_len, append=True)
        df.ta.bbands(length=self.bb_len, std=self.bb_std, append=True); df.ta.kc(length=self.kc_len, scalar=self.kc_scalar, append=True)
        
        df[f'VOL_SMA_{self.vol_sma_len}'] = ta.sma(df['volume'], length=self.vol_sma_len)
        
        # *** НАЧАЛО ИЗМЕНЕНИЯ (v9.10): Нормализованный объем (по предложению 2025) ***
        atr_col = f'ATRr_{self.atr_period}'
        # Заполняем NaN и 0, чтобы избежать ошибок деления
        safe_atr = df[atr_col].replace(0, np.nan).fillna(method='ffill').fillna(1) 
        safe_atr[safe_atr == 0] = 1 # Убедимся, что 0 нет
        df['norm_volume'] = df['volume'] / safe_atr
        df[f'NORM_VOL_SMA_{self.vol_sma_len}'] = ta.sma(df['norm_volume'], length=self.vol_sma_len)
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***
        
        # (v9.9 Filters)
        df.ta.macd(append=True) # Расчет MACD
        
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
        # (Эта функция без изменений)
        pv = market_data['usdt_balance'] + (market_data['base_balance'] * current_price); wr = (self.win_trades/(self.win_trades+self.loss_trades)*100) if (self.win_trades+self.loss_trades)>0 else 0
        unrealized_pnl = "N/A"
        if self.position_side == 'LONG': pnl = (current_price - self.entry_price) * self.quantity; unrealized_pnl = f"{pnl:+.2f}"
        data = {'usdt_balance':f"{market_data['usdt_balance']:.2f}", 'base_balance':f"{market_data['base_balance']:.{self.qty_precision}f}", 'portfolio_value':f"{pv:.2f}", 'unrealized_pnl': unrealized_pnl, 'total_pnl':f"{self.total_pnl_usdt:.2f}", 'total_fees':f"{self.total_fees_paid_usdt:.4f}", 'win_rate':f"{wr:.1f}% ({self.win_trades}/{self.loss_trades})"}
        ind_4h = market_data.get('indicators_4h')
        if ind_4h is not None and not ind_4h.empty:
            last_4h = ind_4h.iloc[-1]
            data['ema_9_4h'] = f"{Decimal(str(last_4h[f'EMA_{self.ema_superfast_len}'])):.2f}"; data['ema_21_4h'] = f"{Decimal(str(last_4h[f'EMA_{self.ema_fast_len}'])):.2f}"; data['ema_50_4h'] = f"{Decimal(str(last_4h[f'EMA_{self.ema_slow_len}'])):.2f}"
            data['ema_200_4h'] = f"{Decimal(str(last_4h[f'EMA_{self.ema_trend_len}'])):.2f}"; data['rsi_14_4h'] = f"{Decimal(str(last_4h['RSI_14'])):.2f}"; data['atr_14_4h'] = f"{Decimal(str(last_4h[f'ATRr_{self.atr_period}'])):.2f}"
        self.event_queue.put({'type': 'dashboard_update', 'data': data})
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
        # (Эта функция без изменений)
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