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


# --- ОСНОВНОЙ КЛАСС ЛОГИКИ БОТА (v8.7 Smart Prioritization) ---
class TradingBot(threading.Thread):
    
    def __init__(self, api_key, api_secret, event_queue, risk_per_trade, rr_ratio, symbol, active_strategies_config, backtest_client=None):
        super().__init__()
        self.daemon = True
        self.api_key, self.api_secret, self.event_queue = api_key, api_secret, event_queue
        try:
            self.base_risk_per_trade = Decimal(str(risk_per_trade)) / 100
            # --- ИЗМЕНЕНО: Базовый R/R теперь - это МИНИМАЛЬНО допустимый R/R ---
            self.base_rr_ratio = Decimal(str(rr_ratio)) 
        except (ValueError, TypeError):
            self.log("Ошибка: риск и R/R должны быть числами. Используются значения по умолчанию.")
            self.base_risk_per_trade = Decimal('0.01')
            self.base_rr_ratio = Decimal('1.3')

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
        self.atr_multiplier_sl = Decimal('1.5') # Множитель ATR для SL по умолчанию
        self.atr_multiplier_trail = Decimal('2.0')
        self.bb_len, self.bb_std = 20, 2.0
        self.kc_len, self.kc_scalar = 20, 2.0
        self.adx_len = 14
        self.vol_sma_len = 20
        
        self.last_log_time = time.time()
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
        bot_name = "Multi-Strategy Trader v8.7 (Smart Prioritization)" # --- ИЗМЕНЕНО ---
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

                if self.is_backtest and not self.position_side and not should_check_logic:
                    self._wait_or_continue(); tick_counter += 1; continue

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
                
                if not self.is_backtest or tick_counter % 65 == 0:
                    self._update_dashboard_data(market_data, current_price)
                
                if should_check_logic:
                    self.last_hour_checked = current_hour
                    if not self.is_backtest:
                         self.log(f"--- Новая 1H свеча ({current_time_dt.strftime('%Y-%m-%d %H:%M')}). Запуск анализа... ---")
                
                if self.position_side:
                    # --- ИЗМЕНЕНО: Передаем 'market_data' для управления SL по RSI ---
                    self._check_and_manage_exit_conditions(market_data, current_price, current_high, current_low, current_1m_candle) 
                else:
                    if should_check_logic: 
                        if self.is_backtest and tick_counter > 0: 
                             self.log(f"--- Новая 1H свеча ({current_time_dt.strftime('%Y-%m-%d %H:%M')}). Запуск анализа... ---")
                        
                        if market_data['usdt_balance'] < self.min_notional:
                            if self.is_backtest: self.log("Баланс USDT исчерпан. Бэктест остановлен."); break
                            self.log(f"Торговля приостановлена. Недостаточно средств."); self._wait_or_continue(300); continue
                        
                        # --- ИЗМЕНЕНО: Вызов _get_algorithmic_decision (сама функция тоже изменена) ---
                        # --- ИЗМЕНЕНО: Теперь передаем current_price для более точных расчетов R:R ---
                        best_signal = self._get_algorithmic_decision(market_data, current_price)
                        
                        if best_signal:
                            # --- ИЗМЕНЕНО: _calculate_and_open_position теперь принимает 'best_signal' ---
                            self._calculate_and_open_position(best_signal, market_data)
                        else:
                            if self.is_backtest or not self.is_backtest: 
                                self.log("Анализ завершен: Нет сигналов, соответствующих мин. R/R.")
                    
                if not self.is_backtest and time.time() - self.last_log_time > 300:
                    self._log_detailed_status(market_data); self.last_log_time = time.time()
            
            except (BinanceRequestException, requests.exceptions.RequestException) as e: 
                self.log(f"Сетевая ошибка: {e}. Активация режима переподключения."); self.is_connected = False
                time.sleep(2 ** min(self.reconnect_attempts, 5)); self.reconnect_attempts += 1
            except BinanceAPIException as e: 
                self.log(f"Ошибка API Binance: {e}. Код: {e.code}, Сообщение: {e.message}"); self._sleep_interruptible(60)
            except Exception as e:
                self.log(f"НЕОЖИДАННАЯ ОШИБКА в главном цикле: {e}. Попытка продолжить через 60 секунд."); logger.exception("Детали:"); self._sleep_interruptible(60)
            
            self._wait_or_continue(); tick_counter += 1
            
        self._finalize_run()

    def _log_detailed_status(self, market_data):
        # (Эта функция без изменений)
        status_msg = "Детальная проверка статуса:\n"
        ind_1d = market_data.get('indicators_1d')
        if ind_1d is not None and not ind_1d.empty:
            last_1d = ind_1d.iloc[-1]
            price_1d = Decimal(str(last_1d['close']))
            ema200_1d = Decimal(str(last_1d[f'EMA_{self.ema_trend_len}']))
            status_msg += f"  - 1D Цена: {price_1d}, EMA200: {ema200_1d} (Бычий: {price_1d > ema200_1d})\n"
        ind_4h = market_data.get('indicators_4h')
        if ind_4h is not None and not ind_4h.empty:
            last_4h = ind_4h.iloc[-1]
            rsi_4h = Decimal(str(last_4h['RSI_14']))
            status_msg += f"  - 4H RSI: {rsi_4h} (Перекупленность: {rsi_4h > 70}, Перепроданность: {rsi_4h < 30})\n"
        if self.position_side:
            status_msg += f"  - Активная позиция: {self.position_side}, Вход: {self.entry_price}, Текущая: {market_data['current_price']}\n"
        else:
            status_msg += "  - Нет открытой позиции. Ожидание сигналов.\n"
        self.log(status_msg)

    # ---
    # --- ИЗМЕНЕНО: ГЛАВНАЯ ЛОГИКА ПРИНЯТИЯ РЕШЕНИЙ ---
    # ---
    def _get_algorithmic_decision(self, market_data, current_price):
        # --- 1. Глобальный фильтр (1D) (без изменений) ---
        ind_1d = market_data.get('indicators_1d')
        if ind_1d is None or len(ind_1d) < self.ema_trend_len:
            reason = f"Ожидание данных для 1D ({len(ind_1d) if ind_1d is not None else 0}/{self.ema_trend_len})"
            self._log_daily_status(reason); return None
        try:
            price_1d = Decimal(str(ind_1d.iloc[-1]['close']))
            ema200_1d = Decimal(str(ind_1d.iloc[-1][f'EMA_{self.ema_trend_len}']))
        except ValueError:
            self.log("Предупреждение: Недопустимые данные в индикаторах 1D. Пропуск."); return None
        if price_1d < ema200_1d:
            reason = "Рынок медвежий (Цена < 1D EMA200). Покупки запрещены."
            self._log_daily_status(reason); return None
        ind_1d_btc = market_data.get('indicators_1d_btc')
        if ind_1d_btc is None or len(ind_1d_btc) < self.ema_trend_len:
            reason = "Ожидание данных для BTCUSDT 1D"
            self._log_daily_status(reason); return None
        try:
            btc_price_1d = Decimal(str(ind_1d_btc.iloc[-1]['close']))
            btc_ema200_1d = Decimal(str(ind_1d_btc.iloc[-1][f'EMA_{self.ema_trend_len}']))
        except ValueError:
            self.log("Предупреждение: Недопустимые данные в индикаторах BTC 1D. Пропуск."); return None
        if btc_price_1d < btc_ema200_1d:
            reason = "BTC в медвежьем тренде (Цена < 1D EMA200). Покупки запрещены."
            self._log_daily_status(reason); return None
        corr_period = 30
        if len(ind_1d) >= corr_period and len(ind_1d_btc) >= corr_period:
            try:
                symbol_closes = np.array(ind_1d['close'].tail(corr_period).astype(float))
                btc_closes = np.array(ind_1d_btc['close'].tail(corr_period).astype(float))
                if np.isnan(symbol_closes).any() or np.isnan(btc_closes).any():
                    self.log("Предупреждение: NaN в данных корреляции. Пропуск проверки.")
                else:
                    correlation = np.corrcoef(symbol_closes, btc_closes)[0, 1]
                    btc_change = (btc_price_1d - Decimal(str(ind_1d.iloc[-2]['close']))) / Decimal(str(ind_1d.iloc[-2]['close']))
                    if correlation > 0.8 and btc_change < 0:
                        reason = f"Корреляция с BTC > 0.8 ({correlation:.2f}) и BTC падает ({btc_change:.2%}). Покупки запрещены."
                        self._log_daily_status(reason); return None
            except Exception as e:
                 self.log(f"Ошибка проверки корреляции: {e}")
        
        self._log_daily_status("Рынок бычий (Цена > 1D EMA200). Поиск сигналов...")

        # --- 2. НОВАЯ ЛОГИКА: Сбор и Приоритезация Сигналов ---
        all_potential_signals = []
        key_levels = self._get_key_levels(market_data['indicators_4h'])

        # --- Стратегия 1: Mean Reversion ---
        if self.active_strategies.get("MEAN_REVERSION", False):
            signal = self._find_entry_mean_reversion_4h(market_data, current_price)
            if signal: all_potential_signals.append(signal)

        # --- Стратегия 2: Breakout & Retest ---
        if self.active_strategies.get("BREAKOUT_4H", False):
            signal = self._find_entry_breakout_retest_4h(market_data, current_price)
            if signal: all_potential_signals.append(signal)

        # --- Стратегия 3: Momentum Pullback ---
        if self.active_strategies.get("MOMENTUM_1H", False):
            signal = self._find_entry_momentum_pullback_1h(market_data, current_price)
            if signal: all_potential_signals.append(signal)

        # --- Стратегия 4: Swing (RSI Дивергенция) ---
        if self.active_strategies.get("RSI_DIVERGENCE", False):
            signal = self._find_entry_rsi_divergence_4h(market_data, current_price)
            if signal: all_potential_signals.append(signal)

        # --- Стратегия 5: Swing (Price Action) ---
        if self.active_strategies.get("PRICE_ACTION", False):
            signal = self._find_entry_price_action_1h(market_data, current_price, key_levels)
            if signal: all_potential_signals.append(signal)
        
        # --- Стратегия 6: Swing (EMA Pullback) ---
        if self.active_strategies.get("EMA_CROSS", False):
            signal = self._find_entry_ema_pullback_4h(market_data, current_price, key_levels)
            if signal: all_potential_signals.append(signal)

        # --- 3. ВЫБОР ЛУЧШЕГО СИГНАЛА ---
        if not all_potential_signals:
            return None # Нет сигналов

        # Сортируем все найденные сигналы по R:R (от лучшего к худшему)
        sorted_signals = sorted(all_potential_signals, key=lambda x: x.get('rr_ratio', Decimal('0.0')), reverse=True)
        
        # Логируем все найденные сигналы для отладки
        for s in sorted_signals:
             self.log(f"    -> КАНДИДАТ: {s['type']} (Расчетный R/R: {s['rr_ratio']:.2f}:1)")

        best_signal = sorted_signals[0]
        
        # Выбираем лучший, только если он соответствует нашему МИНИМАЛЬНОМУ R/R
        if best_signal['rr_ratio'] >= self.base_rr_ratio:
            self.log(f"    -> ✅ ВЫБОР ЛУЧШЕГО СИГНАЛА: {best_signal['type']} (R/R: {best_signal['rr_ratio']:.2f}:1)")
            return best_signal
        else:
            self.log(f"    -> СИГНАЛЫ ОТКЛОНЕНЫ: Лучший R/R ({best_signal['rr_ratio']:.2f}:1) < минимального ({self.base_rr_ratio}:1)")
            return None
    
    def _get_key_levels(self, ind_4h):
        # (без изменений)
        levels = {'supports': [], 'resistances': []}
        if ind_4h is None or len(ind_4h) < 60: return levels
        recent_data = ind_4h.iloc[-60:]
        supports = recent_data[(recent_data['low'] < recent_data['low'].shift(1)) & (recent_data['low'] < recent_data['low'].shift(-1))]
        resistances = recent_data[(recent_data['high'] > recent_data['high'].shift(1)) & (recent_data['high'] > recent_data['high'].shift(-1))]
        levels['supports'] = sorted([Decimal(str(s_val)) for s_val in supports['low'].values], reverse=True) # Сортируем (от ближнего к дальнему)
        levels['resistances'] = sorted([Decimal(str(r_val)) for r_val in resistances['high'].values]) # Сортируем (от ближнего к дальнему)
        return levels

    # ---
    # --- ИЗМЕНЕННЫЕ СТРАТЕГИИ ---
    # ---

    # --- СТРАТЕГИЯ 6 (ИЗМЕНЕНО): EMA Pullback (Откат к EMA) ---
    def _find_entry_ema_pullback_4h(self, market_data, current_price, key_levels):
        ind_4h = market_data.get('indicators_4h')
        ind_1h = market_data.get('indicators_1h')
        if ind_4h is None or ind_1h is None or len(ind_4h) < self.ema_slow_len or len(ind_1h) < 2:
            return None
        
        last_4h = ind_4h.iloc[-1]
        try:
            ema9_4h = Decimal(str(last_4h[f'EMA_{self.ema_superfast_len}']))
            ema21_4h = Decimal(str(last_4h[f'EMA_{self.ema_fast_len}']))
            ema50_4h = Decimal(str(last_4h[f'EMA_{self.ema_slow_len}']))
            atr_4h = Decimal(str(last_4h[f'ATRr_{self.atr_period}']))
        except (ValueError, KeyError):
            return None
            
        # 1. Тренд должен быть бычьим и устоявшимся
        if not (ema9_4h > ema21_4h and ema21_4h > ema50_4h):
            self.log("Пропуск EMA Pullback: 4H EMAs не в бычьем порядке (9 > 21 > 50)."); return None

        # 2. Цена должна быть в зоне отката (между EMA 9 и EMA 50)
        if not (ema50_4h < current_price < ema9_4h):
             self.log(f"Пропуск EMA Pullback: Цена ({current_price}) не в зоне отката (между {ema9_4h:.2f} и {ema50_4h:.2f})."); return None

        # 3. Ищем 1H бычий паттерн для входа
        signal_1h, prev_1h = ind_1h.iloc[-1], ind_1h.iloc[-2]
        is_hammer, is_engulfing = self._is_bullish_hammer(signal_1h), self._is_bullish_engulfing(prev_1h, signal_1h)
        if not (is_hammer or is_engulfing):
            self.log("Пропуск EMA Pullback: Нет 1H паттерна (Hammer/Engulfing) на 4H уровне."); return None
            
        # 4. Расчет R:R
        entry_price = current_price
        # SL: Чуть ниже 4H EMA 50 (самая сильная поддержка)
        stop_loss_price = self._round_price(ema50_4h - (atr_4h * Decimal('0.5'))) 
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # TP: Ближайший 4H уровень сопротивления
        target_tp = self._get_next_resistance(key_levels, entry_price)
        if not target_tp: 
             self.log("Пропуск EMA Pullback: Не найден уровень сопротивления для TP."); return None
             
        reward_per_coin = target_tp - entry_price
        if reward_per_coin <= 0: return None
        
        rr_ratio = reward_per_coin / risk_per_coin
        
        self.log(f"    -> Кандидат (EMA Pullback): 1H паттерн на 4H EMA. SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {
            "type": "EMA_CROSS", # Оставляем старый тип для статистики
            "entry_price": entry_price,
            "stop_loss_price": stop_loss_price,
            "final_take_profit_price": target_tp,
            "rr_ratio": rr_ratio
        }

    # --- СТРАТЕГИЯ 4 (ИЗМЕНЕНО): RSI Divergence (с 1H подтверждением) ---
    def _find_entry_rsi_divergence_4h(self, market_data, current_price):
        ind_4h = market_data.get('indicators_4h')
        ind_1h = market_data.get('indicators_1h')
        if ind_4h is None or ind_1h is None or len(ind_4h) < 40 or len(ind_1h) < 2:
            return None
        
        lookback_period = 30
        recent_data = ind_4h.iloc[-lookback_period:]
        rsi_lows = recent_data[(recent_data['RSI_14'] < recent_data['RSI_14'].shift(1)) & (recent_data['RSI_14'] < recent_data['RSI_14'].shift(-1))]
        if len(rsi_lows) < 2: return None
            
        last_rsi_low_val, prev_rsi_low_val = rsi_lows.iloc[-1]['RSI_14'], rsi_lows.iloc[-2]['RSI_14']
        last_rsi_low_idx, prev_rsi_low_idx = rsi_lows.index[-1], rsi_lows.index[-2]

        # 1. Первый минимум RSI < 40
        if not (prev_rsi_low_val < 40): return None
        # 2. Второй минимум RSI > первого (RSI растет)
        if not (last_rsi_low_val > prev_rsi_low_val): return None
        # 3. Цена на втором минимуме < цены на первом (Цена падает)
        price_at_last_rsi_low, price_at_prev_rsi_low = recent_data.loc[last_rsi_low_idx]['low'], recent_data.loc[prev_rsi_low_idx]['low']
        if not (price_at_last_rsi_low < price_at_prev_rsi_low): return None
            
        # 4. Ищем 1H паттерн (раннее подтверждение)
        signal_1h, prev_1h = ind_1h.iloc[-1], ind_1h.iloc[-2]
        is_hammer, is_engulfing = self._is_bullish_hammer(signal_1h), self._is_bullish_engulfing(prev_1h, signal_1h)
        
        # Дивергенция должна была случиться недавно (на последних 3-х 4H свечах)
        is_recent_divergence = (ind_4h.index[-1] - last_rsi_low_idx) <= 3
        
        if not ((is_hammer or is_engulfing) and is_recent_divergence):
             self.log(f"Пропуск RSI Div: Дивергенция найдена, но нет 1H паттерна (Hammer/Engulfing) для входа."); return None
            
        # 5. Расчет R:R
        entry_price = current_price
        # SL: Под абсолютным минимумом дивергенции + ATR
        stop_loss_ref_candle = recent_data.loc[last_rsi_low_idx]
        atr_4h = Decimal(str(stop_loss_ref_candle[f'ATRr_{self.atr_period}']))
        stop_loss_price = self._round_price(Decimal(str(stop_loss_ref_candle['low'])) - (atr_4h * Decimal('0.5')))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None

        # TP: Уровень High первого минимума дивергенции
        target_tp = self._round_price(Decimal(str(recent_data.loc[prev_rsi_low_idx]['high'])))
        reward_per_coin = target_tp - entry_price
        if reward_per_coin <= 0: return None
        
        rr_ratio = reward_per_coin / risk_per_coin

        self.log(f"    -> Кандидат (RSI Divergence): 4H дивергенция + 1H PA. SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {
            "type": "RSI_DIVERGENCE",
            "entry_price": entry_price,
            "stop_loss_price": stop_loss_price,
            "final_take_profit_price": target_tp,
            "rr_ratio": rr_ratio
        }

    # --- СТРАТЕГИЯ 5 (ИЗМЕНЕНО): Price Action (PA 1H) ---
    def _find_entry_price_action_1h(self, market_data, current_price, key_levels):
       ind_1h = market_data.get('indicators_1h')
       if ind_1h is None or len(ind_1h) < 20: return None
       
       signal_candle, prev_candle = ind_1h.iloc[-1], ind_1h.iloc[-2]
       
       # 1. Ищем бычий паттерн
       is_hammer, is_engulfing = self._is_bullish_hammer(signal_candle), self._is_bullish_engulfing(prev_candle, signal_candle)
       is_pin_bar = self._is_bullish_pin_bar(signal_candle)
       if not (is_hammer or is_engulfing or is_pin_bar): return None
           
       try:
           rsi_1h = Decimal(str(signal_candle['RSI_14']))
           avg_volume = ind_1h['volume'].tail(10).mean()
           signal_volume = Decimal(str(signal_candle['volume']))
           atr_1h = Decimal(str(signal_candle[f'ATRr_{self.atr_period}']))
       except (ValueError, KeyError):
            self.log("Пропуск Price Action: Ошибка данных RSI/Volume/ATR."); return None
            
       # 2. ИЗМЕНЕННЫЙ ФИЛЬТР: RSI должен быть < 40 (зона перепроданности)
       if rsi_1h >= 40: 
           self.log(f"Пропуск Price Action: RSI ({rsi_1h:.1f}) не в зоне < 40."); return None
           
       # 3. Цена у 4H поддержки
       is_near_support = any(abs(current_price - support) / support < Decimal('0.015') for support in key_levels['supports'])
       if not is_near_support: 
           self.log("Пропуск Price Action: Цена не у 4H поддержки."); return None
           
       # 4. Объем выше среднего
       if signal_volume <= Decimal(str(avg_volume)): 
           self.log("Пропуск Price Action: Объем не выше среднего."); return None
           
       # 5. Расчет R:R
       entry_price = current_price
       stop_loss_price = self._round_price(Decimal(str(signal_candle['low'])) - (atr_1h * Decimal('0.2')))
       risk_per_coin = entry_price - stop_loss_price
       if risk_per_coin <= 0: return None
       
       # TP: Ближайший 4H уровень сопротивления
       target_tp = self._get_next_resistance(key_levels, entry_price)
       if not target_tp: 
            self.log("Пропуск Price Action: Не найден уровень сопротивления для TP."); return None
            
       reward_per_coin = target_tp - entry_price
       if reward_per_coin <= 0: return None
       
       rr_ratio = reward_per_coin / risk_per_coin
       pattern_type = "hammer" if is_hammer else ("engulfing" if is_engulfing else "pin_bar")
       
       self.log(f"    -> Кандидат (Price Action 1H): Паттерн {pattern_type}, RSI < 40, у поддержки. SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
       return {
            "type": "PRICE_ACTION",
            "entry_price": entry_price,
            "stop_loss_price": stop_loss_price,
            "final_take_profit_price": target_tp,
            "rr_ratio": rr_ratio
       }

    # --- СТРАТЕГИЯ 1 (ИЗМЕНЕНО): Mean Reversion (BB 4H) ---
    def _find_entry_mean_reversion_4h(self, market_data, current_price):
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
        except (ValueError, KeyError):
            self.log("Пропуск Mean Reversion: Ошибка данных ADX/BB/RSI."); return None
            
        # 1. Ищем флэт (ADX < 25)
        if adx >= 25:
            self.log(f"Пропуск Mean Reversion: ADX ({adx:.1f}) >= 25 (сильный тренд)."); return None
            
        # 2. ИЗМЕНЕНО: Ищем реальную перепроданность (RSI < 30)
        if rsi >= 30:
            self.log(f"Пропуск Mean Reversion: RSI ({rsi:.1f}) >= 30."); return None

        # 3. ИЗМЕНЕНО: Цена должна *значительно* пробить BB или вернуться к ней
        is_pierced = low_price < (lower_bb * Decimal('0.995')) # Сильный пробой
        is_at_band = (current_price >= lower_bb) and (low_price < lower_bb) # Возврат
        
        if not (is_pierced or is_at_band):
             self.log(f"Пропуск Mean Reversion: Нет пробоя или возврата в BB."); return None

        # 4. Расчет R:R
        entry_price = current_price
        # SL: на 1.5 ATR ниже минимума
        stop_loss_price = self._round_price(low_price - (atr_4h * self.atr_multiplier_sl))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # TP: Средняя линия BB
        target_tp = self._round_price(middle_bb)
        reward_per_coin = target_tp - entry_price
        if reward_per_coin <= 0: return None
        
        rr_ratio = reward_per_coin / risk_per_coin

        self.log(f"    -> Кандидат (Mean Reversion): Возврат в BB. SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {
            "type": "MEAN_REVERSION",
            "entry_price": entry_price,
            "stop_loss_price": stop_loss_price,
            "final_take_profit_price": target_tp,
            "rr_ratio": rr_ratio
        }

    # --- СТРАТЕГИЯ 2 (ИЗМЕНЕНО): Breakout & Retest (KC 4H) ---
    def _find_entry_breakout_retest_4h(self, market_data, current_price):
        ind_4h = market_data.get('indicators_4h')
        ind_1h = market_data.get('indicators_1h')
        if ind_4h is None or ind_1h is None or len(ind_4h) < 30 or len(ind_1h) < 2:
            return None
        
        # Нам нужны 2 последние 4H свечи
        prev_4h, last_4h = ind_4h.iloc[-2], ind_4h.iloc[-1]
        
        try:
            # Данные для Breakout
            prev_close = Decimal(str(prev_4h['close']))
            prev_upper_kc = Decimal(str(prev_4h[f'KCUe_{self.kc_len}_{self.kc_scalar}']))
            prev_adx = Decimal(str(prev_4h[f'ADX_{self.adx_len}']))
            
            # Данные для Retest
            last_low = Decimal(str(last_4h['low']))
            last_atr = Decimal(str(last_4h[f'ATRr_{self.atr_period}']))
            
        except (ValueError, KeyError):
            self.log(f"Пропуск Breakout/Retest: Ошибка данных KC/ADX."); return None
            
        # 1. Ищем свечу "Breakout" (предыдущая свеча)
        is_breakout_candle = (prev_close > prev_upper_kc) and (prev_adx > 20)
        if not is_breakout_candle:
            self.log("Пропуск B/R: Нет 4H свечи пробоя (Close > KC) на прошлой свече."); return None
            
        # 2. Ищем "Retest" (текущая цена или 1H свеча)
        # Уровень ретеста = Верхняя KC *прошлой* свечи
        retest_level = prev_upper_kc
        
        # Цена должна быть сейчас в зоне ретеста
        if not (retest_level * Decimal('0.995') < current_price < retest_level * Decimal('1.01')):
            self.log(f"Пропуск B/R: Цена {current_price} не в зоне ретеста {retest_level:.2f}"); return None
            
        # 3. Ищем 1H бычий паттерн на этом уровне
        signal_1h, prev_1h = ind_1h.iloc[-1], ind_1h.iloc[-2]
        is_hammer, is_engulfing = self._is_bullish_hammer(signal_1h), self._is_bullish_engulfing(prev_1h, signal_1h)
        if not (is_hammer or is_engulfing):
            self.log("Пропуск B/R: Нет 1H паттерна (Hammer/Engulfing) на уровне ретеста."); return None
            
        # 4. Расчет R:R
        entry_price = current_price
        # SL: Под минимум последней 4H свечи (которая делала ретест)
        stop_loss_price = self._round_price(last_low - (last_atr * Decimal('0.2')))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # TP: 3R (пробойные стратегии обычно имеют высокий R:R)
        reward_per_coin = risk_per_coin * Decimal('3.0')
        target_tp = self._round_price(entry_price + reward_per_coin)
        rr_ratio = Decimal('3.0')
            
        self.log(f"    -> Кандидат (Breakout & Retest): 1H паттерн на 4H KC ретесте. SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {
            "type": "BREAKOUT_4H",
            "entry_price": entry_price,
            "stop_loss_price": stop_loss_price,
            "final_take_profit_price": target_tp,
            "rr_ratio": rr_ratio
        }

    # --- СТРАТЕГИЯ 3 (ИЗМЕНЕНО): Momentum Pullback (1H) ---
    def _find_entry_momentum_pullback_1h(self, market_data, current_price):
        ind_1h = market_data.get('indicators_1h')
        ind_4h = market_data.get('indicators_4h')
        if ind_1h is None or ind_4h is None or len(ind_1h) < 30 or len(ind_4h) < self.ema_slow_len:
            return None
        
        last_4h = ind_4h.iloc[-1]
        last_1h = ind_1h.iloc[-1]; prev_1h = ind_1h.iloc[-2]
        
        try:
            # 1. 4H Фильтр: Глобальный тренд вверх
            price_4h = Decimal(str(last_4h['close']))
            ema_50_4h = Decimal(str(last_4h[f'EMA_{self.ema_slow_len}']))
            if price_4h <= ema_50_4h:
                self.log(f"Пропуск Momentum Pullback: 4H цена ({price_4h}) <= 4H EMA50 ({ema_50_4h})."); return None

            # 2. 1H Фильтр: Локальный тренд вверх
            ema_9_1h = Decimal(str(last_1h[f'EMA_{self.ema_superfast_len}']))
            ema_21_1h = Decimal(str(last_1h[f'EMA_{self.ema_fast_len}']))
            if ema_9_1h <= ema_21_1h:
                self.log(f"Пропуск Momentum Pullback: 1H EMA9 ({ema_9_1h}) <= 1H EMA21 ({ema_21_1h})."); return None
                
            # 3. ИЗМЕНЕННЫЙ СИГНАЛ: Ищем 1H откат (StochRSI в перепроданности)
            stoch_k_1h = Decimal(str(last_1h['STOCHRSIk_14_14_3_3']))
            stoch_d_1h = Decimal(str(last_1h['STOCHRSId_14_14_3_3']))
            stoch_k_prev_1h = Decimal(str(prev_1h['STOCHRSIk_14_14_3_3']))
            
            # StochK должен быть < 30 (зона отката) и пересекать StochD снизу вверх
            is_oversold_cross = (stoch_k_1h < 30) and (stoch_k_prev_1h <= stoch_d_1h) and (stoch_k_1h > stoch_d_1h)
            
            if not is_oversold_cross:
                self.log("Пропуск Momentum Pullback: Нет StochRSI пересечения в зоне < 30."); return None

        except (ValueError, KeyError):
            self.log("Пропуск Momentum Pullback: Ошибка данных EMA/StochRSI."); return None
            
        # 4. Расчет R:R
        entry_price = current_price
        # SL: Под 1H EMA 21 (динамическая поддержка)
        stop_loss_price = self._round_price(ema_21_1h * Decimal('0.998'))
        risk_per_coin = entry_price - stop_loss_price
        if risk_per_coin <= 0: return None
        
        # TP: 2R (стандарт для моментум-стратегий)
        reward_per_coin = risk_per_coin * Decimal('2.0')
        target_tp = self._round_price(entry_price + reward_per_coin)
        rr_ratio = Decimal('2.0')
        
        self.log(f"    -> Кандидат (Momentum Pullback): StochRSI откат в 1H/4H аптренде. SL={stop_loss_price:.2f}, TP={target_tp:.2f}, R:R={rr_ratio:.2f}")
        return {
            "type": "MOMENTUM_1H",
            "entry_price": entry_price,
            "stop_loss_price": stop_loss_price,
            "final_take_profit_price": target_tp,
            "rr_ratio": rr_ratio
        }
    
    # --- ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ PA ---
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

    # --- ВСПОМОГАТЕЛЬНАЯ ФУНКЦИЯ ДЛЯ TP ---
    def _get_next_resistance(self, key_levels, entry_price):
        if not key_levels['resistances']: return None
        # Ищем первый уровень сопротивления, который ВЫШЕ цены входа
        for res in key_levels['resistances']:
            if res > entry_price:
                return self._round_price(res)
        return None # Не найдено

    # --- ЛОГИКА УПРАВЛЕНИЯ ВЫХОДОМ (RSI Divergence) ---
    def _find_exit_rsi_divergence_4h(self, market_data):
        ind_4h = market_data.get('indicators_4h')
        if ind_4h is None or len(ind_4h) < 40 or not self.position_side == 'LONG':
            return None
        lookback_period = 40
        recent_data = ind_4h.iloc[-lookback_period:]
        rsi_highs = recent_data[(recent_data['RSI_14'] > recent_data['RSI_14'].shift(1)) & (recent_data['RSI_14'] > recent_data['RSI_14'].shift(-1))]
        if len(rsi_highs) < 2: return None
        last_rsi_high, prev_rsi_high = rsi_highs.iloc[-1], rsi_highs.iloc[-2]
        if not (last_rsi_high['RSI_14'] < prev_rsi_high['RSI_14']): return None
        price_at_last_rsi_high, price_at_prev_rsi_high = last_rsi_high['high'], prev_rsi_high['high']
        if not (price_at_last_rsi_high > price_at_prev_rsi_high): return None
        new_stop_price = self._round_price(Decimal(str(last_rsi_high['low'])))
        if new_stop_price > self.stop_loss_price: return new_stop_price
        return None
        
    # ---
    # --- ИЗМЕНЕНО: ГЛАВНЫЙ МОДУЛЬ РАСЧЕТА И ОТКРЫТИЯ ПОЗИЦИИ ---
    # ---
    def _calculate_and_open_position(self, best_signal, market_data):
        
        # --- 1. Получаем все данные из pre-calculated сигнала ---
        entry_price = best_signal['entry_price']
        stop_loss_price = best_signal['stop_loss_price']
        self.final_take_profit_price = best_signal['final_take_profit_price']
        rr_ratio = best_signal['rr_ratio']
        self.current_trade_strategy_type = best_signal['type']
        
        risk_per_coin = entry_price - stop_loss_price
        
        # --- 2. Рассчитываем TP1 (кроме Mean Reversion) ---
        if self.current_trade_strategy_type == 'MEAN_REVERSION':
            self.take_profit_price_1 = self.final_take_profit_price
            self.log(f"     -> Расчет для Mean Reversion. R/R: {rr_ratio:.1f}:1")
        else:
            # TP1 ставится на 1R
            self.take_profit_price_1 = self._round_price(entry_price + (risk_per_coin * Decimal('1.0')))
            self.log(f"     -> Расчет для {self.current_trade_strategy_type}. R/R: {rr_ratio:.1f}:1")

        # --- 3. ОБЩАЯ ЛОГИКА РАСЧЕТА РАЗМЕРА ПОЗИЦИИ ---
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

        # --- 4. ИСПОЛНЕНИЕ ОРДЕРА ---
        self.trade_counter += 1
        self.current_trade_id = f"{self.symbol[:3]}-{self.trade_counter}"
        self.current_trade_pnl = Decimal('0.0')

        try:
            self.log(f"ИСПОЛНЕНИЕ ОРДЕРА (BUY, {self.current_trade_strategy_type}): {quantity} {self.base_asset} по рыночной цене...")

            # --- ИЗМЕНЕНИЕ: Разделяем логику Live и Backtest ---
            if self.is_backtest:
                # В бэктесте мы передаем 'entry_price', чтобы симулировать исполнение по этой цене
                trigger_price = entry_price
                order_result = self.binance_client.create_order(
                    symbol=self.symbol,
                    side=Client.SIDE_BUY,
                    type=Client.ORDER_TYPE_MARKET,
                    quantity=float(quantity),
                    trigger_price=trigger_price
                )
            else:
                # В РЕАЛЬНОЙ ТОРГОВЛЕ 'trigger_price' НЕ используется для MARKET ордеров
                order_result = self.binance_client.create_order(
                    symbol=self.symbol,
                    side=Client.SIDE_BUY,
                    type=Client.ORDER_TYPE_MARKET,
                    quantity=float(quantity)
                )
            # --- КОНЕЦ ИЗМЕНЕНИЯ ---
            
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
            if self.current_trade_strategy_type == 'MEAN_REVERSION':
                 self.log(f"    - TP (Оба): ${self.final_take_profit_price:.{self.price_precision}f} (Middle BB)")
            else:
                 self.log(f"    - TP1 (50%): ${self.take_profit_price_1:.{self.price_precision}f}, Финальный TP: ${self.final_take_profit_price:.{self.price_precision}f} (RR: {rr_ratio:.1f}:1)")
        except BinanceAPIException as e:
            if e.code == -2010: self.log(f"ОШИБКА ОТКРЫТИЯ: Недостаточно средств на балансе. {e.message}")
            else: self.log(f"ОШИБКА API при открытии позиции: {e}")
            self._reset_position_state()
        except Exception as e: 
            self.log(f"КРИТИЧЕСКАЯ ОШИБКА при открытии позиции: {e}"); self._reset_position_state()

    def _check_and_manage_exit_conditions(self, market_data, current_price, current_high, current_low, current_1m_candle):
        # (Эта функция без изменений)
        if not self.position_side: return
        current_open = current_price
        if self.is_backtest and current_1m_candle is not None:
            current_open = Decimal(str(current_1m_candle['open']))
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
        if self.entry_time and not self.is_tp1_hit:
            trade_duration = (self._get_current_time() - self.entry_time).total_seconds() / 86400
            max_duration_days = 5
            if trade_duration >= max_duration_days and current_price > self.entry_price:
                self.log(f"!!! УПРАВЛЕНИЕ ПО ВРЕМЕНИ: Сделка в плюсе >{max_duration_days} дней. Активация режима TP1.")
                self._close_position(reason=f"TIME Mgmt ({max_duration_days}d)", is_partial=True, partial_ratio=0.5, execution_price=current_open)
                self.is_tp1_hit = True; self.stop_loss_price = self.entry_price; self.is_trailing_active = True
                self.log(f"УПРАВЛЕНИЕ: Позиция обезопасена. Стоп в безубытке, ТРЕЙЛИНГ ПО ATR АКТИВИРОВАН.")
                self._save_state(); return
        new_stop_from_divergence = self._find_exit_rsi_divergence_4h(market_data)
        if new_stop_from_divergence:
            self.log(f"!!! УПРАВЛЕНИЕ (RSI DIVERGENCE EXIT): Обнаружена медвежья дивергенция на 4H.")
            self.log(f"     -> Стоп-лосс агрессивно поднят до ${new_stop_from_divergence:.{self.price_precision}f} для защиты прибыли.")
            self.stop_loss_price = new_stop_from_divergence
            if not self.is_trailing_active:
                self.is_trailing_active = True
                self.log("     -> Режим трейлинга активирован из-за сигнала дивергенции.")
            self._save_state()
            if current_low <= self.stop_loss_price:
                self.log(f"ВЫХОД: Сработал немедленно стоп-лосс после ужесточения по сигналу RSI дивергенции.")
                self._close_position(reason="RSI DIV STOP", is_partial=False, execution_price=min(current_open, self.stop_loss_price))
                return
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
            if self.current_trade_strategy_type == 'MEAN_REVERSION': return
            self.log(f"ФИКСАЦИЯ: Сработал Тейк-Профит 1 по цене ${self.take_profit_price_1:.{self.price_precision}f} (High: {current_high})")
            exec_price = max(current_open, self.take_profit_price_1)
            self.log(f"    -> Цена исполнения (TP1): ${exec_price:.{self.price_precision}f}")
            self._close_position(reason="TP1", is_partial=True, partial_ratio=0.5, execution_price=exec_price)
            self.is_tp1_hit = True; self.stop_loss_price = self.entry_price; self.is_trailing_active = True
            self.log(f"УПРАВЛЕНИЕ: Позиция обезопасена. Стоп в безубытке, ТРЕЙЛИНГ ПО ATR АКТИВИРОВАН.")
            self._save_state(); return
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
        ind_4h = market_data.get('indicators_4h')
        if ind_4h is not None and not ind_4h.empty:
            rsi_4h = Decimal(str(ind_4h.iloc[-1]['RSI_14']))
            if rsi_4h > 70:
                new_sl = self._round_price(Decimal(str(ind_4h.iloc[-1]['low'])))
                if new_sl > self.stop_loss_price:
                    self.stop_loss_price = new_sl
                    self.log(f"!!! УПРАВЛЕНИЕ (RSI OVERBOUGHT): RSI > 70 на 4H. Стоп-лосс ужесточен до ${new_sl:.{self.price_precision}f}.")
                    self._save_state()
                    if current_low <= self.stop_loss_price:
                        self.log(f"ВЫХОД: Сработал стоп-лосс после ужесточения по RSI overbought.")
                        self._close_position(reason="RSI OVERBOUGHT STOP", is_partial=False, execution_price=min(current_open, self.stop_loss_price))
                        return
        if not self.is_backtest:
            log_type = "ТРЕЙЛИНГ" if self.is_trailing_active else "УПРАВЛЕНИЕ"
            log_tp = self.final_take_profit_price if self.is_tp1_hit else f"TP1: {self.take_profit_price_1:.{self.price_precision}f}"
            self.log(f"{log_type}: Цена={current_price:.{self.price_precision}f}, SL={self.stop_loss_price:.{self.price_precision}f}, TP={log_tp}")

    def _close_position(self, reason="", is_partial=False, partial_ratio=0.5, execution_price=None):
        if not self.position_side: return
        qty_to_sell = (self.quantity * Decimal(str(partial_ratio))) if is_partial else self.quantity
        if qty_to_sell <= 0: return
        try:
            qty_to_sell = self._round_quantity(qty_to_sell)
            
            # Проверка реального баланса для live-торговли
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
            
            # Корректировка для бэктеста, если расчетное кол-во > имеющегося
            if self.is_backtest and not is_partial and qty_to_sell > self.quantity:
                qty_to_sell = self.quantity
                
            log_prefix = "ЧАСТИЧНОЕ ЗАКРЫТИЕ" if is_partial else "ПОЛНОЕ ЗАКРЫТИЕ"
            self.log(f"ЗАПУСК {log_prefix}. Причина: {reason}.")
            
            # --- ИЗМЕНЕНИЕ: Убираем дублирование и разделяем логику ---
            if self.is_backtest:
                # В бэктесте мы передаем execution_price в mock-обработчик
                order = self.binance_client.create_order(
                    symbol=self.symbol, side=Client.SIDE_SELL, type=Client.ORDER_TYPE_MARKET,
                    quantity=float(qty_to_sell), trigger_price=execution_price
                )
            else:
                # В РЕАЛЬНОЙ ТОРГОВЛЕ 'trigger_price' НЕ используется
                order = self.binance_client.create_order(
                    symbol=self.symbol,
                    side=Client.SIDE_SELL,
                    type=Client.ORDER_TYPE_MARKET,
                    quantity=float(qty_to_sell)
                )
            # --- КОНЕЦ ИЗМЕНЕНИЯ ---

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

            # --- ИЗМЕНЕНИЕ: Отправляем оставшееся кол-во в GUI ---
            # self.quantity здесь - это кол-во ДО продажи
            # total_qty - это кол-во, которое было продано
            remaining_qty_val = self.quantity - total_qty
            if not is_partial:
                remaining_qty_val = Decimal('0.0') # Если закрытие полное
            
            trade_update_info = {
                'trade_id': self.current_trade_id,
                'strategy': stype,
                'exit_time': self._get_current_time().strftime('%y-%m-%d %H:%M'),
                'exit_price': f"{avg_price:.{self.price_precision}f}",
                'pnl': f"{net_pnl:.2f}",
                'is_partial': is_partial,
                'remaining_quantity': f"{remaining_qty_val:.{self.qty_precision}f}" # <-- НОВЫЙ ПАРАМЕТР
            }
            self._update_trade_in_history_gui(trade_update_info)
            # --- КОНЕЦ ИЗМЕНЕНИЯ ---
    
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
        # (Эта функция без изменений)
        try:
            kline_calls = { Client.KLINE_INTERVAL_1HOUR: 205, Client.KLINE_INTERVAL_4HOUR: 205, Client.KLINE_INTERVAL_1DAY: 250 }
            btc_symbol = 'BTCUSDT'
            with ThreadPoolExecutor(max_workers=5) as executor:
                future_map = {}
                for interval, limit in kline_calls.items(): 
                    future_map[executor.submit(self.binance_client.get_klines, symbol=self.symbol, interval=interval, limit=limit)] = {'type': 'klines', 'interval': interval}
                    if interval == Client.KLINE_INTERVAL_1DAY:
                        future_map[executor.submit(self.binance_client.get_klines, symbol=btc_symbol, interval=interval, limit=limit)] = {'type': 'klines_btc', 'interval': interval}
                future_map[executor.submit(self.binance_client.get_asset_balance, asset=self.quote_asset)] = {'type': 'usdt_balance'}
                future_map[executor.submit(self.binance_client.get_asset_balance, asset=self.base_asset)] = {'type': 'base_balance'}
                future_map[executor.submit(self.binance_client.get_symbol_ticker, symbol=self.symbol)] = {'type': 'ticker'}
                results, klines_results = {}, {}
                for future in as_completed(future_map):
                    task_info, task_type = future_map[future], future_map[future]['type']
                    try:
                        result_data = future.result()
                        if task_type == 'klines': klines_results[task_info['interval']] = result_data
                        elif task_type == 'klines_btc': klines_results[f"{task_info['interval']}_btc"] = result_data
                        else: results[task_type] = result_data
                    except Exception as e: self.log(f"Ошибка в подзадаче {task_type}: {e}"); return None
            return {
                "indicators_1h": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_1HOUR)),
                "indicators_4h": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_4HOUR)), 
                "indicators_1d": self._calculate_indicators(klines_results.get(Client.KLINE_INTERVAL_1DAY)),
                "indicators_1d_btc": self._calculate_indicators(klines_results.get(f"{Client.KLINE_INTERVAL_1DAY}_btc")),
                "usdt_balance": Decimal(results.get("usdt_balance", {}).get('free', '0')), 
                "base_balance": Decimal(results.get("base_balance", {}).get('free', '0')),
                "current_price": Decimal(results.get("ticker", {}).get('price', '0'))
            }
        except Exception as e: self.log(f"Ошибка получения данных: {e}"); return None

    def _calculate_indicators(self, klines):
        # (Эта функция без изменений)
        if not klines or len(klines) < 50: return pd.DataFrame()
        df = pd.DataFrame(klines, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume', 'close_time', 'qav', 'trades', 'tbav', 'tqav', 'ig'])
        for col in ['open', 'high', 'low', 'close', 'volume']: df[col] = pd.to_numeric(df[col])
        df.ta.ema(length=self.ema_superfast_len, append=True); df.ta.ema(length=self.ema_fast_len, append=True); df.ta.ema(length=self.ema_slow_len, append=True); df.ta.ema(length=self.ema_trend_len, append=True)
        df.ta.rsi(length=14, append=True); df.ta.atr(length=self.atr_period, append=True); df.ta.stochrsi(append=True)
        
        # --- ИЗМЕНЕНИЕ ---
        # Убеждаемся, что adx() добавляет DMP и DMN для стратегии Breakout
        df.ta.adx(length=self.adx_len, append=True)
        
        df.ta.bbands(length=self.bb_len, std=self.bb_std, append=True); df.ta.kc(length=self.kc_len, scalar=self.kc_scalar, append=True)
        df[f'VOL_SMA_{self.vol_sma_len}'] = ta.sma(df['volume'], length=self.vol_sma_len)
        return df
    
    def _log_daily_status(self, reason):
        # (Эта функция без изменений)
        if self.is_backtest: 
             current_time = self._get_current_time()
             self.log(f"--- Анализ на {current_time.strftime('%Y-%m-%d %H:%M')} ---"); self.log(f"СТАТУС: {reason}")
             self._update_status_gui(f"Статус: {reason}")

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
        detailed_message = f"[{mode}] {message}"
        if self.is_backtest:
             current_time_dt = self._get_current_time()
             current_time_str = current_time_dt.strftime('%Y-%m-%d %H:%M')
             logger.info(f"[{current_time_str}] {message}")
             self.event_queue.put({'type': 'log', 'data': f"[{current_time_str}] {message}"}); return
        if self.binance_client is not None:
            try:
                balance_usdt = self.balances.get(self.quote_asset, Decimal('0.0')) if self.is_backtest else Decimal(self.binance_client.get_asset_balance(asset=self.quote_asset)['free'])
                current_price_val = Decimal(self.binance_client.get_symbol_ticker(symbol=self.symbol)['price']); current_price = f"{current_price_val:.{self.price_precision}f}"
                current_time = self._get_current_time(); pos_qty = f"{self.quantity:.{self.qty_precision}f}" if self.position_side else "N/A"; entry_p = f"{self.entry_price:.{self.price_precision}f}" if self.position_side else "N/A"
                detailed_message = f"[{mode} {current_time.strftime('%H:%M:%S')}] {message} (Bal: {balance_usdt:.2f} | Pos: {pos_qty} | Entry: {entry_p} | Cur: {current_price})"
            except Exception as e: detailed_message += f" (Ошибка в деталях лога: {e})"
        logger.info(detailed_message); self.event_queue.put({'type': 'log', 'data': detailed_message})
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
