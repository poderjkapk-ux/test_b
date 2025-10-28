# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import scrolledtext, messagebox, ttk, filedialog
import threading
import queue
import time
from datetime import datetime, timedelta, UTC
from decimal import Decimal, getcontext
import logging
import os
from concurrent.futures import ThreadPoolExecutor, as_completed
from dateutil.relativedelta import relativedelta
import requests
import warnings

warnings.filterwarnings("ignore", message="pkg_resources is deprecated")

# --- НАСТРОЙКА ЛОГИРОВАНИЯ ---
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s', filename='trading_bot_multi_strategy_v2.log', filemode='a')
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
    missing_libs_message = "Необходимые библиотеки не установлены. Пожалуйста, выполните команду: pip install python-binance pandas pandas-ta numpy python-dateutil requests"
    print(missing_libs_message)
    root_temp = tk.Tk()
    root_temp.withdraw()
    messagebox.showerror("Критическая ошибка", missing_libs_message)
    root_temp.destroy()
    exit()

# --- Импорт кастомных классов из других файлов ---
from trading_bot import TradingBot
from mock_binance_client import MockBinanceClient


# --- КЛАСС ГРАФИЧЕСКОГО ИНТЕРФЕЙСА ---
class App:
    def __init__(self, root):
        self.root = root
        self.root.title("Multi-Strategy Trader v8.6 (Configurable)")
        self.root.geometry("1440x900") # Ширина x Высота
        self.root.bind("<Configure>", self._resize_columns)
        self.event_queue = queue.Queue()
        self.bot_thread = None
        self.backtest_file_path = ""
        self.trade_view_items = {}
        self.total_pnl_history = {}
        
        # *** НОВОЕ: Словарь для хранения Checkbutton-ов и их переменных ***
        self.strategy_vars = {}
        self.strategy_checkboxes = {}
        
        self._create_widgets()
        self.process_event_queue()
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

    def _create_widgets(self):
        # *** ИЗМЕНЕНО: Полностью переработанная компоновка GUI ***
        style = ttk.Style(); style.theme_use('clam')
        style.configure("TLabel", padding=3, foreground="#333333", background="#f8f9fa")
        style.configure("TButton", padding=3, background="#007bff", foreground="white")
        style.configure("Accent.TButton", foreground="white", background="#28a745")
        style.configure("Treeview", background="#ffffff", foreground="#000000", fieldbackground="#ffffff", font=("Arial", 9))
        style.configure("Treeview.Heading", font=('Arial', 9, 'bold'), background="#e9ecef")
        style.map("TButton", background=[('active', '#0056b3')])
        style.map("Accent.TButton", background=[('active', '#218838')])

        # --- 1. Главный контейнер (Панель логов/сделок СЛЕВА, Панель управления СПРАВА) ---
        main_paned_window = tk.PanedWindow(self.root, orient="horizontal", sashrelief="raised", bg="#f8f9fa"); 
        main_paned_window.pack(fill="both", expand=True, padx=5, pady=5)

        # --- 2. ЛЕВАЯ ПАНЕЛЬ (Логи и Сделки) ---
        left_frame = ttk.Frame(main_paned_window, width=900); 
        main_paned_window.add(left_frame, stretch="always")
        
        left_paned = tk.PanedWindow(left_frame, orient="vertical", sashrelief="raised", bg="#f8f9fa"); 
        left_paned.pack(fill="both", expand=True)
        
        log_frame = ttk.LabelFrame(left_paned, text="Лог работы бота"); 
        left_paned.add(log_frame, stretch="always")
        self.log_text = scrolledtext.ScrolledText(log_frame, wrap=tk.WORD, state="disabled", bg="#2c3e50", fg="#ecf0f1", font=("Consolas", 8)); 
        self.log_text.pack(fill="both", expand=True, padx=3, pady=3)
        
        trades_frame = ttk.LabelFrame(left_paned, text="История сделок"); 
        left_paned.add(trades_frame, stretch="never")
        cols = ("ID", "Стратегия", "Сторона", "Время входа", "Цена входа", "Кол-во", "Время выхода", "Цена выхода", "PnL ($)")
        self.trades_tree = ttk.Treeview(trades_frame, columns=cols, show="headings", height=10)
        for col in cols:
            self.trades_tree.heading(col, text=col)
            self.trades_tree.column(col, anchor="center")
        self.trades_tree.pack(fill="both", expand=True, padx=3, pady=3)

        # --- 3. ПРАВАЯ ПАНЕЛЬ (Управление, Настройки, Статистика) ---
        right_frame = ttk.Frame(main_paned_window, width=400); 
        main_paned_window.add(right_frame, stretch="never")
        
        # Контейнер для прокрутки правой панели, если окно станет слишком низким
        right_canvas = tk.Canvas(right_frame, bg="#f8f9fa", highlightthickness=0)
        scrollbar = ttk.Scrollbar(right_frame, orient="vertical", command=right_canvas.yview)
        scrollable_frame = ttk.Frame(right_canvas)
        
        scrollable_frame.bind("<Configure>", lambda e: right_canvas.configure(scrollregion=right_canvas.bbox("all")))
        right_canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        right_canvas.configure(yscrollcommand=scrollbar.set)
        
        right_canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # --- Наполнение правой панели ---
        controls_frame = ttk.Frame(scrollable_frame); controls_frame.pack(fill="x", pady=(0, 5))
        self.start_button = ttk.Button(controls_frame, text="Старт (Live)", command=self.start_bot, style="Accent.TButton"); self.start_button.pack(side="left", padx=3, fill='x', expand=True)
        self.stop_button = ttk.Button(controls_frame, text="Стоп", command=self.stop_bot, state="disabled"); self.stop_button.pack(side="left", padx=3, fill='x', expand=True)
        
        api_frame = ttk.LabelFrame(scrollable_frame, text="API Ключи Binance"); api_frame.pack(fill="x", padx=3, pady=3, ipady=3)
        tk.Label(api_frame, text="API Key:").pack(anchor="w", padx=3)
        self.binance_key_entry = tk.Entry(api_frame, width=50); self.binance_key_entry.pack(fill="x", expand=True, padx=3, pady=1)
        tk.Label(api_frame, text="API Secret:").pack(anchor="w", padx=3)
        self.binance_secret_entry = tk.Entry(api_frame, width=50, show="*"); self.binance_secret_entry.pack(fill="x", expand=True, padx=3, pady=1)
        
        settings_frame = ttk.LabelFrame(scrollable_frame, text="Настройки торговли"); settings_frame.pack(fill="x", padx=3, pady=5, ipady=3); settings_frame.columnconfigure(1, weight=1)
        tk.Label(settings_frame, text="Торговая пара:").grid(row=0, column=0, sticky="w", padx=3, pady=3)
        self.symbol_var = tk.StringVar(value="ETHUSDT"); ttk.Entry(settings_frame, textvariable=self.symbol_var, width=12).grid(row=0, column=1, sticky="w", padx=3, pady=3)
        tk.Label(settings_frame, text="Риск на сделку (%):").grid(row=2, column=0, sticky="w", padx=3, pady=3)
        self.risk_per_trade_var = tk.StringVar(value="1"); ttk.Entry(settings_frame, textvariable=self.risk_per_trade_var, width=8).grid(row=2, column=1, sticky="w", padx=3, pady=3)
        tk.Label(settings_frame, text="Базовый R/R:").grid(row=3, column=0, sticky="w", padx=3, pady=3)
        self.rr_ratio_var = tk.StringVar(value="1.3"); ttk.Entry(settings_frame, textvariable=self.rr_ratio_var, width=8).grid(row=3, column=1, sticky="w", padx=3, pady=3)

        # --- НОВЫЙ ФРЕЙМ: Конфигурация стратегий ---
        strategy_config_frame = ttk.LabelFrame(scrollable_frame, text="Активные стратегии"); 
        strategy_config_frame.pack(fill="x", padx=3, pady=5, ipady=3)
        
        self.strategy_display_names = {
            "RSI_DIVERGENCE": "Swing (RSI Div)", "PRICE_ACTION": "Swing (PA 1H)", "EMA_CROSS": "Swing (EMA Cross)",
            "MEAN_REVERSION": "Mean Rev (BB 4H)", "BREAKOUT_4H": "Breakout (KC 4H)", "MOMENTUM_1H": "Momentum (1H)"
        }
        
        for stype, name in self.strategy_display_names.items():
            var = tk.BooleanVar(value=True) # По умолчанию все включены
            chk = ttk.Checkbutton(strategy_config_frame, text=name, variable=var)
            chk.pack(anchor="w", padx=5)
            self.strategy_vars[stype] = var
            self.strategy_checkboxes[stype] = chk
        # --- КОНЕЦ НОВОГО ФРЕЙМА ---

        backtest_frame = ttk.LabelFrame(scrollable_frame, text="Бэктестинг"); backtest_frame.pack(fill="x", padx=3, pady=5, ipady=3); backtest_frame.columnconfigure(1, weight=1)
        tk.Label(backtest_frame, text="Стартовый баланс (USDT):").grid(row=0, column=0, sticky="w", padx=3, pady=3)
        self.initial_balance_var = tk.StringVar(value="1000"); ttk.Entry(backtest_frame, textvariable=self.initial_balance_var, width=12).grid(row=0, column=1, sticky="w", padx=3, pady=3)
        self.backtest_source_var = tk.BooleanVar(value=True); ttk.Checkbutton(backtest_frame, text="Загрузить онлайн", variable=self.backtest_source_var, command=self._toggle_backtest_source).grid(row=1, column=0, columnspan=2, sticky="w", padx=3, pady=3)
        self.online_frame = ttk.Frame(backtest_frame); self.online_frame.grid(row=2, column=0, columnspan=2, sticky='ew')
        tk.Label(self.online_frame, text="Дата начала (ГГГГ-ММ-ДД):").pack(side='left', padx=3)
        self.start_date_var = tk.StringVar(value="2023-01-01"); ttk.Entry(self.online_frame, textvariable=self.start_date_var, width=12).pack(side='left', padx=3)
        self.local_file_frame = ttk.Frame(backtest_frame); ttk.Button(self.local_file_frame, text="Выбрать файл (.csv)", command=self.select_backtest_file).pack(fill='x', expand=True, padx=3)
        self.backtest_file_label = ttk.Label(self.local_file_frame, text="Файл не выбран", anchor="w", foreground="grey"); self.backtest_file_label.pack(fill='x', expand=True, padx=3, pady=1)
        self.start_backtest_button = ttk.Button(backtest_frame, text="Старт Бэктест", command=self.start_backtest); self.start_backtest_button.grid(row=4, column=0, columnspan=2, sticky="ew", padx=3, pady=5)
        self._toggle_backtest_source()
        
        dashboard_frame = ttk.LabelFrame(scrollable_frame, text="Панель активов"); dashboard_frame.pack(fill="x", padx=3, pady=5, ipady=3); dashboard_frame.columnconfigure(1, weight=1)
        self.dashboard_labels = {}
        dash_items = [("Баланс USDT:", "usdt_balance"), ("Баланс Актива:", "base_balance"), ("Портфель:", "portfolio_value"), ("Нереализ. PnL:", "unrealized_pnl"), ("Чистый PnL:", "total_pnl"), ("Комиссии:", "total_fees"), ("Win Rate:", "win_rate")]
        for i, (text, key) in enumerate(dash_items):
            ttk.Label(dashboard_frame, text=text).grid(row=i, column=0, sticky="w", padx=3, pady=2)
            self.dashboard_labels[key] = ttk.Label(dashboard_frame, text="N/A", font=("Arial", 9, "bold"), anchor="e"); self.dashboard_labels[key].grid(row=i, column=1, sticky="ew", padx=3, pady=2)
        
        indicators_frame = ttk.LabelFrame(scrollable_frame, text="Рыночные Показатели (4H)"); indicators_frame.pack(fill="x", padx=3, pady=5, ipady=3); indicators_frame.columnconfigure(1, weight=1)
        ind_items = [("EMA 9:", "ema_9_4h"), ("EMA 21:", "ema_21_4h"), ("EMA 50:", "ema_50_4h"), ("EMA 200:", "ema_200_4h"), ("RSI 14:", "rsi_14_4h"), ("ATR 14:", "atr_14_4h")]
        for i, (text, key) in enumerate(ind_items):
            ttk.Label(indicators_frame, text=text).grid(row=i, column=0, sticky="w", padx=3, pady=2)
            self.dashboard_labels[key] = ttk.Label(indicators_frame, text="N/A", font=("Arial", 9, "bold"), anchor="e"); self.dashboard_labels[key].grid(row=i, column=1, sticky="ew", padx=3, pady=2)
        
        self.strategy_stats_frame = ttk.LabelFrame(scrollable_frame, text="Статистика по Стратегиям"); self.strategy_stats_frame.pack(fill="x", padx=3, pady=5, ipady=3)
        self.strategy_stats_frame.columnconfigure(1, weight=1); self.strategy_stats_frame.columnconfigure(2, weight=1)
        self.strategy_labels = {}
        ttk.Label(self.strategy_stats_frame, text="Стратегия", font=("Arial", 9, "bold")).grid(row=0, column=0, sticky="w", padx=3, pady=2)
        ttk.Label(self.strategy_stats_frame, text="PnL ($)", font=("Arial", 9, "bold"), anchor="e").grid(row=0, column=1, sticky="ew", padx=3, pady=2)
        ttk.Label(self.strategy_stats_frame, text="W/R (W/L)", font=("Arial", 9, "bold"), anchor="e").grid(row=0, column=2, sticky="ew", padx=3, pady=2)
        i = 1
        for stype, name in self.strategy_display_names.items():
            ttk.Label(self.strategy_stats_frame, text=f"{name}:").grid(row=i, column=0, sticky="w", padx=3, pady=1)
            lbl_pnl = ttk.Label(self.strategy_stats_frame, text="N/A", font=("Arial", 8), anchor="e"); lbl_pnl.grid(row=i, column=1, sticky="ew", padx=3, pady=1)
            lbl_wr = ttk.Label(self.strategy_stats_frame, text="N/A", font=("Arial", 8), anchor="e"); lbl_wr.grid(row=i, column=2, sticky="ew", padx=3, pady=1)
            self.strategy_labels[stype] = {'pnl': lbl_pnl, 'wr': lbl_wr}
            i += 1
        
        # --- 4. Статус бар ---
        self.status_bar = ttk.Label(self.root, text="Статус: Ожидание запуска...", anchor='w', relief='sunken', padding=3, background="#e9ecef"); 
        self.status_bar.pack(side='bottom', fill='x')

    def _resize_columns(self, event):
        # (Эта функция без изменений)
        if hasattr(self, 'trades_tree'):
            width = self.trades_tree.winfo_width()
            if width > 1:
                col_widths = [int(width * 0.08), int(width * 0.12), int(width * 0.08), int(width * 0.12), int(width * 0.10), int(width * 0.10), int(width * 0.12), int(width * 0.10), int(width * 0.08)]
                total_w = sum(col_widths); 
                if total_w < width: col_widths[-1] += (width - total_w)
                for i, col in enumerate(self.trades_tree["columns"]):
                    self.trades_tree.column(col, width=col_widths[i], anchor='c')

    def _toggle_backtest_source(self):
        # (Эта функция без изменений)
        if self.backtest_source_var.get(): self.online_frame.grid(row=2, column=0, columnspan=2, sticky='ew'); self.local_file_frame.grid_remove()
        else: self.online_frame.grid_remove(); self.local_file_frame.grid(row=2, column=0, columnspan=2, sticky='ew')
    
    def select_backtest_file(self):
        # (Эта функция без изменений)
        path = filedialog.askopenfilename(title="Выберите CSV файл с минутными данными", filetypes=[("CSV Files", "*.csv")])
        if path: self.backtest_file_path = path; self.backtest_file_label.config(text=os.path.basename(path), foreground="black")
    
    def _validate_common_settings(self):
        # (Эта функция без изменений)
        try:
            if not 0 < float(self.risk_per_trade_var.get()) <= 10: raise ValueError
            if not 0 < float(self.rr_ratio_var.get()): raise ValueError
            datetime.strptime(self.start_date_var.get(), '%Y-%m-%d')
        except ValueError: messagebox.showerror("Ошибка", "Риск должен быть числом (0-10), R:R > 0, дата в формате YYYY-MM-DD."); return False
        if not self.symbol_var.get().strip(): messagebox.showerror("Ошибка", "Пожалуйста, введите торговую пару."); return False
        return True
    
    def _clear_previous_run(self):
        # (Эта функция без изменений)
        self.log_text.config(state="normal"); self.log_text.delete('1.0', tk.END); self.log_text.config(state="disabled")
        for item in self.trades_tree.get_children(): self.trades_tree.delete(item)
        self.trade_view_items.clear(); self.total_pnl_history.clear()
        for label in self.dashboard_labels.values(): label.config(text="N/A")
        for stype in self.strategy_labels:
            self.strategy_labels[stype]['pnl'].config(text="N/A")
            self.strategy_labels[stype]['wr'].config(text="N/A")
        self.status_bar.config(text="Статус: Очистка...")
    
    # *** ИЗМЕНЕНО: Сбор данных с галочек перед стартом ***
    def _get_active_strategies_config(self):
        config = {stype: var.get() for stype, var in self.strategy_vars.items()}
        if not any(config.values()):
            messagebox.showwarning("Нет стратегий", "Вы не выбрали ни одной стратегии. Бот не будет открывать сделки.")
        return config

    def start_bot(self):
        if not all(k.strip() for k in [self.binance_key_entry.get(), self.binance_secret_entry.get()]): messagebox.showerror("Ошибка", "Пожалуйста, введите API ключи Binance."); return
        if not self._validate_common_settings(): return
        if not messagebox.askokcancel("ПОДТВЕРЖДЕНИЕ", "Вы уверены, что хотите запустить бота в режиме РЕАЛЬНОЙ ТОРГОВЛИ?"): return
        
        self._clear_previous_run(); self._set_controls_running(True)
        active_strategies = self._get_active_strategies_config() # НОВОЕ
        
        bot_args = {
            "api_key": self.binance_key_entry.get(), "api_secret": self.binance_secret_entry.get(), 
            "event_queue": self.event_queue, "risk_per_trade": self.risk_per_trade_var.get(), 
            "rr_ratio": self.rr_ratio_var.get(), "symbol": self.symbol_var.get(),
            "active_strategies_config": active_strategies # НОВОЕ
        }
        self.bot_thread = TradingBot(**bot_args); self.bot_thread.start()
    
    def start_backtest(self):
        if not self._validate_common_settings(): return
        try:
            if float(self.initial_balance_var.get()) <= 0: raise ValueError
        except ValueError: messagebox.showerror("Ошибка", "Начальный баланс должен быть положительным числом."); return
        
        self._clear_previous_run(); self._set_controls_running(True)
        self.active_strategies_config = self._get_active_strategies_config() # НОВОЕ
        
        threading.Thread(target=self._run_backtest_flow, args=(float(self.initial_balance_var.get()),), daemon=True).start()
        
    def _run_backtest_flow(self, initial_balance):
        # *** ИЗМЕНЕНО: Передача active_strategies_config в mock-бота ***
        try:
            df_1m = self._get_backtest_data()
            if df_1m is None or df_1m.empty: 
                self.event_queue.put({'type': 'status_update', 'data': {'is_running': False}}); return
            
            self.event_queue.put({'type': 'log', 'data': "Данные 1М загружены. Бэктест будет использовать 'lookahead-free' симулятор."})
            user_start_date = datetime.strptime(self.start_date_var.get(), '%Y-%m-%d').replace(tzinfo=UTC)
            df_1m_test_iterator = df_1m[df_1m['datetime'] >= user_start_date].reset_index(drop=True)

            if df_1m_test_iterator.empty:
                self.event_queue.put({'type': 'log', 'data': f"КРИТИЧЕСКАЯ ОШИБКА: Не найдено 1-минутных данных для начала теста с {self.start_date_var.get()}."})
                self.event_queue.put({'type': 'status_update', 'data': {'is_running': False}}); return

            symbol_str = self.symbol_var.get().upper()
            mock_client = MockBinanceClient(
                iterator_df=df_1m_test_iterator, all_1m_data=df_1m, initial_usdt_balance=initial_balance, 
                symbol=symbol_str, base_asset=symbol_str.replace("USDT", ""), 
                quote_asset="USDT", commission_rate=Decimal('0.001')
            )
            
            bot_args = {
                "api_key": "mock", "api_secret": "mock", "event_queue": self.event_queue, 
                "risk_per_trade": self.risk_per_trade_var.get(), "rr_ratio": self.rr_ratio_var.get(), 
                "symbol": symbol_str, "backtest_client": mock_client,
                "active_strategies_config": self.active_strategies_config # НОВОЕ
            }
            self.bot_thread = TradingBot(**bot_args); self.bot_thread.start(); self.bot_thread.join()
        except Exception as e:
            self.event_queue.put({'type': 'log', 'data': f"КРИТИЧЕСКАЯ ОШИБКА БЭКТЕСТА: {e}"}); logger.exception("Детали:"); self.event_queue.put({'type': 'status_update', 'data': {'is_running': False}})

    def _get_backtest_data(self):
        # (Эта функция без изменений)
        if self.backtest_source_var.get():
            try: return self._fetch_historical_data(self.symbol_var.get(), self.start_date_var.get())
            except ValueError: messagebox.showerror("Ошибка", "Неверный формат даты."); return None
        else:
            if not self.backtest_file_path: messagebox.showerror("Ошибка", "Выберите файл."); return None
            try:
                self.event_queue.put({'type': 'log', 'data': f"Загрузка из {os.path.basename(self.backtest_file_path)}..."})
                df = pd.read_csv(self.backtest_file_path)
                req_cols = ['timestamp', 'open', 'high', 'low', 'close', 'volume']
                if not all(col in df.columns for col in req_cols): raise ValueError(f"CSV должен содержать: {', '.join(req_cols)}")
                df['datetime'] = pd.to_datetime(df['timestamp'], unit='ms', utc=True); df.sort_values('timestamp', inplace=True)
                return df
            except Exception as e: messagebox.showerror("Ошибка файла", f"Не удалось обработать CSV: {e}"); return None

    def _fetch_historical_data(self, symbol, start_date_str):
        # (Эта функция без изменений)
        self.event_queue.put({'type': 'log', 'data': f"Загрузка минутных данных для {symbol} с {start_date_str}..."})
        try:
            user_start_date = datetime.strptime(start_date_str, '%Y-%m-%d').replace(tzinfo=UTC); warmup_days = 250
            self.event_queue.put({'type': 'log', 'data': f"INFO: Загружаю данные за {warmup_days} дней до даты старта для 'разогрева' индикаторов..."})
            data_load_start_date = user_start_date - timedelta(days=warmup_days); end_date = datetime.now(UTC); date_ranges = []; current_start = data_load_start_date
            while current_start < end_date:
                current_end = current_start + relativedelta(months=1)
                date_ranges.append((current_start, min(current_end, end_date))); current_start = current_end
            self.event_queue.put({'type': 'log', 'data': f"Разбиваю задачу на {len(date_ranges)} потоков..."}); all_klines = []
            def _fetch_chunk(start_dt, end_dt, index):
                client = Client(requests_params={"timeout": 30}); start_ts, end_ts = int(start_dt.timestamp()*1000), int(end_dt.timestamp()*1000); chunk_klines = []; retries = 0
                while start_ts < end_ts and retries < 3:
                    klines = client.get_historical_klines(symbol, Client.KLINE_INTERVAL_1MINUTE, start_ts, limit=1000)
                    if not klines: retries += 1; time.sleep(1); continue
                    chunk_klines.extend(klines); start_ts = klines[-1][0] + 1 if klines else end_ts
                self.event_queue.put({'type': 'log', 'data': f"  - Поток {index}/{len(date_ranges)} завершен, загружено {len(chunk_klines)} свечей."}); return chunk_klines
            with ThreadPoolExecutor(max_workers=10) as executor:
                futures = {executor.submit(_fetch_chunk, s, e, i+1): (s, e) for i, (s, e) in enumerate(date_ranges)}
                for future in as_completed(futures):
                    try: all_klines.extend(future.result())
                    except Exception as exc: self.event_queue.put({'type': 'log', 'data': f"Ошибка в потоке: {exc}"})
            self.event_queue.put({'type': 'log', 'data': f"✅ Загрузка завершена. Всего {len(all_klines)} свечей. Обработка..."})
            df = pd.DataFrame(all_klines, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume', 'ct', 'qav', 'nt', 'tbbav', 'tbqav', 'ig'])
            df.drop_duplicates(subset=['timestamp'], inplace=True); df.sort_values('timestamp', inplace=True, ignore_index=True)
            for col in ['open', 'high', 'low', 'close', 'volume']: df[col] = pd.to_numeric(df[col], errors='coerce')
            df.dropna(inplace=True); df['datetime'] = pd.to_datetime(df['timestamp'], unit='ms', utc=True); return df
        except Exception as e: messagebox.showerror("Ошибка загрузки", f"Не удалось загрузить данные с Binance: {e}"); return None

    def stop_bot(self):
        # (Эта функция без изменений)
        if self.bot_thread and self.bot_thread.is_alive(): self.bot_thread.stop()
        self._set_controls_running(False)
    
    def _set_controls_running(self, is_running):
        # *** ИЗМЕНЕНО: Добавлена блокировка галочек ***
        state = "disabled" if is_running else "normal"
        self.start_button.config(state=state); self.start_backtest_button.config(state=state)
        self.stop_button.config(state="normal" if is_running else "disabled")
        
        # Блокируем галочки стратегий
        for chk in self.strategy_checkboxes.values():
            chk.config(state=state)
            
        self.status_bar.config(text="Статус: В работе..." if is_running else "Статус: Остановлен.")
    
    def process_event_queue(self):
        # (Эта функция без изменений)
        try:
            while True:
                event = self.event_queue.get_nowait()
                event_type, event_data = event['type'], event['data']
                if event_type == 'log':
                    log_msg = event['data']
                    if not (self.bot_thread and self.bot_thread.is_backtest): log_msg = f"[{datetime.now().strftime('%H:%M:%S')}] {event['data']}"
                    self.log_text.config(state="normal"); self.log_text.insert(tk.END, f"{log_msg}\n"); self.log_text.config(state="disabled"); self.log_text.see(tk.END)
                elif event_type == 'dashboard_update':
                    for key, value in event_data.items():
                        if key in self.dashboard_labels: self.dashboard_labels[key].config(text=value)
                elif event_type == 'new_trade':
                    trade_id = event_data['trade_id']; self.total_pnl_history[trade_id] = Decimal('0.0')
                    values = (trade_id, event_data['strategy'], event_data['side'], event_data['entry_time'], event_data['entry_price'], event_data['quantity'], '...', '...', '...')
                    item_id = self.trades_tree.insert("", 0, values=values); self.trade_view_items[trade_id] = item_id
                elif event_type == 'update_trade':
                    trade_id = event_data['trade_id']; item_id = self.trade_view_items.get(trade_id)
                    if item_id:
                        self.total_pnl_history[trade_id] += Decimal(event_data['pnl']); total_pnl_for_trade = self.total_pnl_history[trade_id]
                        pnl_text = f"{total_pnl_for_trade:+.2f}"; 
                        if event_data['is_partial']: pnl_text += " (TP1)"
                        current_values = self.trades_tree.item(item_id)['values']
                        updated_values = (current_values[0], current_values[1], current_values[2], current_values[3], current_values[4], current_values[5], event_data['exit_time'], event_data['exit_price'], pnl_text)
                        self.trades_tree.item(item_id, values=updated_values)
                elif event_type == 'strategy_stats_update':
                    for stype, data in event_data.items():
                        if stype in self.strategy_labels:
                            self.strategy_labels[stype]['pnl'].config(text=data['pnl'])
                            self.strategy_labels[stype]['wr'].config(text=data['wr'])
                elif event_type == 'status_update': 
                    self._set_controls_running(event_data['is_running'])
                elif event_type == 'status_text_update': 
                    self.status_bar.config(text=f"Статус: {event_data}")
        except queue.Empty:
            pass
        finally:
            self.root.after(50, self.process_event_queue)
            
    def on_closing(self):
        # (Эта функция без изменений)
        if messagebox.askokcancel("Выход", "Вы уверены, что хотите закрыть бота?"): self.stop_bot(); self.root.destroy()

if __name__ == "__main__":
    root = tk.Tk()
    app = App(root)
    root.mainloop()