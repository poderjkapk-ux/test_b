# -*- coding: utf-8 -*-
import time
from datetime import datetime, timedelta, UTC
from decimal import Decimal, getcontext
import logging
import numpy as np
import os
import json
import random # <-- Добавлено для симуляции slippage

# --- НАСТРОЙКА ЛОГИРОВАНИЯ (для этого модуля) ---
logger = logging.getLogger(__name__)

# --- НАСТРОЙКА ТОЧНОСТИ ВЫЧИСЛЕНИЙ ---
getcontext().prec = 18

# --- ПРОВЕРКА И ИМПОРТ БИБЛИОТЕК ---
try:
    from binance.exceptions import BinanceAPIException
    import pandas as pd
except ImportError:
    logger.critical("КРИТИЧЕСКАЯ ОШИБКА: mock_binance_client.py не смог импортировать 'binance' или 'pandas'. Убедитесь, что main.py был запущен и библиотеки установлены.")
    pass 


# --- СИМУЛЯTOR API BINANCE (v1.0 Scalp + Slippage) ---
class MockBinanceClient:
    KLINE_INTERVAL_1MINUTE = '1m'
    # *** НАЧАЛО ИЗМЕНЕНИЯ (v1.0 Scalp) ***
    KLINE_INTERVAL_3MINUTE = '3m'
    KLINE_INTERVAL_5MINUTE = '5m'
    KLINE_INTERVAL_15MINUTE = '15m'
    # *** КОНЕЦ ИЗМЕНЕНИЯ ***
    KLINE_INTERVAL_1HOUR = '1h'
    KLINE_INTERVAL_4HOUR = '4h'
    KLINE_INTERVAL_1DAY = '1d'
    SIDE_BUY = 'BUY'
    SIDE_SELL = 'SELL'
    ORDER_TYPE_MARKET = 'MARKET'

    def __init__(self, iterator_df, all_1m_data, initial_usdt_balance, symbol, base_asset, quote_asset, commission_rate):
        self.log_callback = lambda msg: print(f"MOCK: {msg}")
        if iterator_df.empty or all_1m_data.empty: raise ValueError("Передан пустой DataFrame с историческими данными.")
        
        self.main_data_iterator = iterator_df
        self.all_1m_data = all_1m_data
        
        self.log_callback(f"✅ Исторические данные готовы. Свечей для итерации (1м): {len(self.main_data_iterator)}")
        self.log_callback(f"✅ Всего 1М свечей для расчетов HTF: {len(self.all_1m_data)}")
        
        self.symbol, self.base_asset, self.quote_asset = symbol, base_asset, quote_asset
        self.commission_rate = commission_rate
        self.balances = {self.quote_asset: Decimal(initial_usdt_balance), self.base_asset: Decimal('0.0')}
        
        self.current_tick = 0
        self.total_ticks = len(self.main_data_iterator)
        
        # *** НАЧАЛО ИЗМЕНЕНИЯ (v1.0 Scalp) ***
        self.pd_interval_map = {
            self.KLINE_INTERVAL_1MINUTE: 'T',
            self.KLINE_INTERVAL_3MINUTE: '3T',
            self.KLINE_INTERVAL_5MINUTE: '5T',
            self.KLINE_INTERVAL_15MINUTE: '15T',
            self.KLINE_INTERVAL_1HOUR: 'H',
            self.KLINE_INTERVAL_4HOUR: '4H',
            self.KLINE_INTERVAL_1DAY: 'D'
        }
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***

    def has_more_data(self): return self.current_tick < self.total_ticks
    def _advance_tick(self): self.current_tick += 1
    def ping(self): return {}
    def get_server_time(self): return {'serverTime': int(self.main_data_iterator.iloc[self.current_tick]['timestamp'])}

    def get_symbol_info(self, symbol):
        return {'symbol': self.symbol, 'baseAsset': self.base_asset, 'quoteAsset': self.quote_asset, 'filters': [{'filterType': 'PRICE_FILTER', 'tickSize': '0.01'}, {'filterType': 'LOT_SIZE', 'stepSize': '0.0001'}, {'filterType': 'NOTIONAL', 'minNotional': '10.0'}]}
    def get_trade_fee(self, symbol): return [{'symbol': symbol, 'makerCommission': str(self.commission_rate), 'takerCommission': str(self.commission_rate)}]
    def get_asset_balance(self, asset): return {'asset': asset, 'free': str(self.balances.get(asset, Decimal('0.0')))}

    def get_klines(self, symbol, interval, limit):
        current_timestamp = self.main_data_iterator.iloc[self.current_tick]['timestamp']
        available_1m_data = self.all_1m_data[self.all_1m_data['timestamp'] < current_timestamp]
        
        if available_1m_data.empty:
            logger.warning(f"Пустой срез свечей (нет доступных 1M данных) для {interval} в {current_timestamp}.")
            return []

        df_slice = None
        
        if interval == self.KLINE_INTERVAL_1MINUTE:
            df_slice = available_1m_data.iloc[-limit:]
        else:
            pd_interval = self.pd_interval_map.get(interval)
            if not pd_interval:
                raise ValueError(f"Неподдерживаемый интервал {interval}")
            try:
                df_resampled = available_1m_data.set_index('datetime').resample(pd_interval).agg(
                    {'open': 'first', 'high': 'max', 'low': 'min', 'close': 'last', 'volume': 'sum'}
                ).dropna()
                if df_resampled.empty:
                     # (Это ожидаемо в начале, если данных 1м < 3м/5м/15м)
                     # logger.warning(f"Пустой срез свечей после resampling для {interval} в {current_timestamp}.")
                     return []
                df_resampled['timestamp'] = df_resampled.index.astype(np.int64) // 1_000_000
                df_slice = df_resampled.iloc[-limit:]
            except Exception as e:
                logger.error(f"Ошибка при resampling для {interval} в {current_timestamp}: {e}")
                return []

        if df_slice is None or df_slice.empty:
            # logger.warning(f"Пустой срез свечей возвращен для {interval} в {current_timestamp} (после resampling).")
            return []
        
        klines = [[int(row.timestamp), str(row.open), str(row.high), str(row.low), str(row.close), str(row.volume), 0,0,0,0,0,0] for _, row in df_slice.iterrows()]
        return klines

    def get_symbol_ticker(self, symbol): 
        price = self.main_data_iterator.iloc[self.current_tick]['open']
        return {'symbol': symbol, 'price': str(price)}

    def get_current_candle(self):
        if not self.has_more_data():
            return None
        try:
            return self.main_data_iterator.iloc[self.current_tick]
        except IndexError:
            return None

    def create_order(self, symbol, side, type, quantity, trigger_price=None):
        if type != self.ORDER_TYPE_MARKET: raise NotImplementedError("В режиме бэктеста поддерживаются только рыночные ордера.")
        
        current_candle = self.main_data_iterator.iloc[self.current_tick]
        
        if trigger_price:
            execution_price = Decimal(str(trigger_price))
            candle_low = Decimal(str(current_candle['low']))
            candle_high = Decimal(str(current_candle['high']))
            if execution_price < candle_low: execution_price = candle_low
            if execution_price > candle_high: execution_price = candle_high
        else:
            execution_price = Decimal(str(current_candle['open']))

        quantity = Decimal(str(quantity))

        # *** НАЧАЛО ИЗМЕНЕНИЯ (v1.0 Slippage) ***
        # (Симуляция проскальзывания 0.01% - 0.05%)
        slippage_rate = Decimal(str(random.uniform(0.0001, 0.0005)))
        if side == self.SIDE_BUY:
            # (Покупаем дороже)
            execution_price = execution_price * (Decimal('1') + slippage_rate)
        elif side == self.SIDE_SELL:
            # (Продаем дешевле)
            execution_price = execution_price * (Decimal('1') - slippage_rate)
        # *** КОНЕЦ ИЗМЕНЕНИЯ ***

        notional = execution_price * quantity
        commission = notional * self.commission_rate
        commission_asset = self.quote_asset

        if side == self.SIDE_BUY:
            required_usdt = notional + commission
            if self.balances[self.quote_asset] < required_usdt: 
                error_msg = '{"code": -2010, "msg": "Account has insufficient balance for requested action."}'
                raise BinanceAPIException(self._MockResponse(text=error_msg), 400)
            self.balances[self.quote_asset] -= required_usdt
            self.balances[self.base_asset] += quantity
        elif side == self.SIDE_SELL:
            if self.balances[self.base_asset] < quantity: 
                if quantity > self.balances[self.base_asset] and abs(quantity - self.balances[self.base_asset]) / quantity < Decimal('0.01'):
                    self.log_callback(f"Корректировка кол-ва продажи: {quantity} -> {self.balances[self.base_asset]}")
                    quantity = self.balances[self.base_asset]
                else:
                    error_msg = '{"code": -2010, "msg": "Account has insufficient balance for requested action."}'
                    raise BinanceAPIException(self._MockResponse(text=error_msg), 400)
            
            self.balances[self.quote_asset] += (notional - commission)
            self.balances[self.base_asset] -= quantity
            
        return {'symbol': symbol, 'orderId': int(time.time()), 'status': 'FILLED', 'fills': [{'price': str(execution_price), 'qty': str(quantity), 'commission': str(commission), 'commissionAsset': commission_asset}]}
    
    class _MockResponse:
        def __init__(self, text=''): self.request = None; self.text = text