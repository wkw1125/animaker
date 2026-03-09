#!/usr/bin/env python3
"""Animaker 动画魅客 GUI 界面"""

import io
import json
import math
import os
import random
import subprocess
import sys
import threading
import time
import zipfile
from collections import deque
from datetime import datetime
from pathlib import Path
from urllib.parse import unquote

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

import numpy as np

try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    _DND_AVAILABLE = True
except ImportError:
    _DND_AVAILABLE = False
from PIL import Image, ImageTk, ImageDraw, ImageChops
from skimage.metrics import structural_similarity

# 支持的图片格式（与 image_compare 一致）
IMAGE_EXTENSIONS = {".png", ".jpg", ".jpeg", ".bmp", ".tiff", ".tif", ".webp"}

# 上次选择目录的配置存储路径
CONFIG_DIR = Path.home() / ".config" / "evideo-image-utils"
LAST_DIR_FILE = CONFIG_DIR / "animaker_last_dir"


def get_default_initial_dir() -> Path:
    """获取文件夹选择器的默认初始目录：优先上次选择，否则为「下载」文件夹。"""
    if LAST_DIR_FILE.exists():
        try:
            path = Path(LAST_DIR_FILE.read_text(encoding="utf-8").strip())
            if path.is_dir():
                return path
        except Exception:
            pass
    return Path.home() / "Downloads"


def save_last_dir(path: Path) -> None:
    """记住上次选择的文件夹路径。"""
    try:
        CONFIG_DIR.mkdir(parents=True, exist_ok=True)
        LAST_DIR_FILE.write_text(str(path), encoding="utf-8")
    except Exception:
        pass


# 动画默认 16 fps，循环播放
DEFAULT_PREVIEW_FPS = 16


class AnimakerApp:
    """Animaker 动画魅客应用主类"""

    def __init__(self):
        self.root = (TkinterDnD.Tk() if _DND_AVAILABLE else tk.Tk())  # type: ignore[assignment]
        self.root.title("Animaker - 动画魅客")
        self.root.geometry("1200x800")
        self.root.minsize(600, 400)
        if _DND_AVAILABLE:
            self.root.drop_target_register(DND_FILES)
            self.root.dnd_bind("<<Drop>>", self._on_drop)

        # 当前打开的文件夹与图片列表
        self.folder_path: Path | None = None
        self.image_files: list[Path] = []
        self._preview_photo: ImageTk.PhotoImage | None = None
        # 每个图片的原始尺寸缓存（width, height），与 image_files 对齐
        self._image_sizes: list[tuple[int, int]] = []
        # 每个图片的文件大小（字节），与 image_files 对齐
        self._file_sizes: list[int] = []
        # 动画预览：选中帧索引列表、当前下标、after id（用于取消）
        self._animation_indices: list[int] = []
        self._animation_index: int = 0
        self._animation_after_id: str | None = None
        self._selected_indices: list[int] = []
        # 动画控制
        self._fps_var = tk.IntVar(value=DEFAULT_PREVIEW_FPS)
        self._fps_label_var = tk.StringVar(value=f"帧率：{self._fps_var.get()}")
        self._preview_fps_var = tk.StringVar(value="预览帧率：—")
        # 实际帧率：每帧间隔历史（秒），用于计算并显示实际 fps
        self._last_tick_time: float | None = None
        self._frame_interval_history: deque[float] = deque(maxlen=10)
        self._is_playing = tk.BooleanVar(value=True)  # 默认播放
        self._play_mode_var = tk.StringVar(value="loop")  # once / loop，默认 loop
        self._bg_var = tk.StringVar(value="透明")
        self._bg_image_path: Path | None = None  # 背景为「图片」时用户选择的路径
        self._bg_image_cache: tuple[int, int, Image.Image] | None = None  # (w, h, image) 避免每帧重载
        self._color_mode_var = tk.StringVar(value="原图")  # 原图 / 灰度 / 黑白
        self._zoom_mode_var = tk.StringVar(value="fit")  # fit / x1 / x2
        self._ruler_var = tk.BooleanVar(value=False)  # 轮廓开关
        # 当前帧信息显示：当前帧：n/m name wxh
        self._frame_info_var = tk.StringVar(value="")
        # 首尾帧 tab 信息与预览
        self._headtail_info_var = tk.StringVar(value="")
        self._headtail_mode_var = tk.StringVar(value="差异")  # 差异 / 叠加
        self._headtail_photo: ImageTk.PhotoImage | None = None
        # 单击行为：普通选择=仅选当前项，单击追加=追加/取消选中
        self._click_mode_var = tk.StringVar(value="单击追加")
        # 导出时重命名帧：按 {name}_001 格式，默认勾选
        self._export_rename_var = tk.BooleanVar(value=True)
        # 导出GIF：zip 中增加 {name}.gif，默认不勾选
        self._export_gif_var = tk.BooleanVar(value=True)
        # Phaser 动画导出：本次运行内记住上次的参数
        self._phaser_anim_enabled_last: bool = True
        self._phaser_atlas_last: str = ""
        # 默认帧名格式：{name}/{frame}.{ext}
        self._phaser_frame_fmt_last: str = "{name}/{frame}.{ext}"
        # 导出时重命名帧的序位补0位数，默认3（001、002…）
        self._export_rename_digits_last: int = 3
        # 导出窗口「名称」默认值：上次导出使用的名称；打开新文件夹后改为该文件夹名
        self._export_name_last: str = ""
        # 导出保存目录：本次运行内记住上次选择的目录，未选过则用下载目录
        self._export_save_dir: Path | None = None
        # 合并JSON导出：本次运行内记住上次保存目录，未选过则用下载目录
        self._merge_export_dir: Path | None = None
        # 打开文件夹时是否自动计算智能首尾帧，默认勾选
        self._smart_headtail_open_calc_var = tk.BooleanVar(value=False)
        # 本次运行内上次计算首尾帧使用的参数，供下次计算（含打开文件夹自动计算）作为默认
        self._last_smart_headtail_params: dict | None = None
        # 区间选择：从第 a 帧起每 b 帧共选 c 帧
        self._range_start_var = tk.StringVar(value="1")
        self._range_step_var = tk.StringVar(value="1")
        self._range_count_var = tk.StringVar(value="30")

        self._build_ui()

    def _build_ui(self) -> None:
        # 菜单栏：「文件」-> 打开帧序列、导出
        # 使用 accelerator 在菜单右侧显示快捷键提示，标签文本不包含快捷键信息。
        if sys.platform == "darwin":
            # macOS：使用 Command- 前缀，符合 Tk 在 macOS 上的习惯写法
            open_accel = "Command-O"
            export_accel = "Command-S"
        else:
            open_accel = "Ctrl+O"
            export_accel = "Ctrl+S"

        menubar = tk.Menu(self.root)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(
            label="打开帧序列",
            command=self._on_open_folder,
            accelerator=open_accel,
        )
        file_menu.add_command(
            label="导出",
            command=self._on_export,
            accelerator=export_accel,
        )
        menubar.add_cascade(label="文件", menu=file_menu)
        tools_menu = tk.Menu(menubar, tearoff=0)
        if sys.platform == "darwin":
            merge_accel = "Command-J"
        else:
            merge_accel = "Ctrl+J"
        tools_menu.add_command(
            label="合并JSON",
            command=self._show_merge_anims_dialog,
            accelerator=merge_accel,
        )
        menubar.add_cascade(label="工具", menu=tools_menu)
        about_menu = tk.Menu(menubar, tearoff=0)
        about_menu.add_command(
            label="关于 Animaker",
            command=self._show_about,
        )
        menubar.add_cascade(label="关于", menu=about_menu)
        self.root.config(menu=menubar)
        # 快捷键：macOS 用 Command，其它平台用 Control
        if sys.platform == "darwin":
            self.root.bind("<Command-o>", lambda e: self._on_open_folder())
            self.root.bind("<Command-s>", lambda e: self._on_export())
            self.root.bind("<Command-j>", lambda e: self._show_merge_anims_dialog())
        else:
            self.root.bind("<Control-o>", lambda e: self._on_open_folder())
            self.root.bind("<Control-s>", lambda e: self._on_export())
            self.root.bind("<Control-j>", lambda e: self._show_merge_anims_dialog())
        self.root.bind("<Right>", lambda e: self._on_next_frame())
        self.root.bind("<Left>", lambda e: self._on_prev_frame())
        self.root.bind("<space>", lambda e: self._toggle_play())

        # 顶部栏 50px
        top_bar = tk.Frame(self.root, height=50, bg="#f0f0f0", relief="ridge", bd=1)
        top_bar.pack(side="top", fill="x")
        top_bar.pack_propagate(False)

        btn_open = tk.Button(
            top_bar,
            text="打开帧序列文件夹",
            command=self._on_open_folder,
            font=("", 12),
            padx=16,
            pady=8,
        )
        btn_open.pack(side="left", padx=(20, 12), pady=8)

        ttk.Separator(top_bar, orient="vertical").pack(side="left", fill="y", padx=12, pady=6)

        tk.Checkbutton(
            top_bar,
            text="打开时计算",
            variable=self._smart_headtail_open_calc_var,
            bg="#f0f0f0",
            activebackground="#f0f0f0",
            selectcolor="#f0f0f0",
        ).pack(side="left", padx=(0, 8), pady=8)

        self._btn_smart_headtail = tk.Button(
            top_bar,
            text="智能首尾帧",
            command=self._on_smart_headtail,
            font=("", 12),
            padx=16,
            pady=8,
        )
        self._btn_smart_headtail.pack(side="left", padx=(12, 4), pady=8)

        self._smart_headtail_combo = ttk.Combobox(
            top_bar,
            values=[],
            state="readonly",
            width=18,
        )
        self._smart_headtail_combo.set("未计算")
        self._smart_headtail_combo.pack(side="left", padx=(0, 2), pady=8)
        self._smart_headtail_combo.bind(
            "<<ComboboxSelected>>",
            lambda e: self._on_smart_headtail_combo_select(),
        )

        self._btn_smart_headtail_next = tk.Button(
            top_bar,
            text="⬇",
            command=self._on_smart_headtail_next,
            font=("", 12),
            width=2,
            padx=2,
            pady=4,
        )
        self._btn_smart_headtail_next.pack(side="left", padx=(0, 8), pady=8)

        self._update_smart_headtail_ui_state()

        # 中间弹性空间，使右侧控件右对齐
        tk.Frame(top_bar).pack(side="left", fill="x", expand=True)

        self._btn_export = tk.Button(
            top_bar,
            text="导出",
            command=self._on_export,
            font=("", 12),
            padx=16,
            pady=8,
        )
        self._btn_export.pack(side="right", padx=8, pady=8)
        self._btn_export.config(state="disabled")

        # 底部栏：高度随内容自适应（不使用单独背景色）
        bottom_bar = tk.Frame(self.root, relief="ridge", bd=1)
        bottom_bar.pack(side="bottom", fill="x")

        self._status_var = tk.StringVar(value="未打开文件夹")
        status_label = tk.Label(
            bottom_bar,
            textvariable=self._status_var,
            font=("", 10),
            anchor="w",
        )
        status_label.pack(side="left", fill="x", expand=True, padx=10, pady=8)

        # 操作区：左右可调节（PanedWindow 直接 pack，无多余父容器）
        paned = ttk.PanedWindow(self.root, orient="horizontal")
        paned.pack(side="top", fill="both", expand=True)

        # 左侧：帧列表 + 底部按钮/复选框
        left_frame = tk.Frame(paned)
        list_container = tk.Frame(left_frame)
        list_container.pack(fill="both", expand=True)
        scrollbar = ttk.Scrollbar(list_container)
        scrollbar.pack(side="right", fill="y")
        self._listbox = tk.Listbox(
            list_container,
            yscrollcommand=scrollbar.set,
            font=("", 11),
            selectmode="extended",
            exportselection=False,
        )
        self._listbox.pack(side="left", fill="both", expand=True)
        scrollbar.config(command=self._listbox.yview)
        self._listbox.bind("<<ListboxSelect>>", self._on_list_select)
        self._listbox.bind("<Button-1>", self._on_listbox_click)
        # 上滚 / 下滚：选中序号全部 -1 / +1，不超出范围
        roll_row = tk.Frame(left_frame)
        roll_row.pack(side="bottom", fill="x", padx=4, pady=(0, 2))
        self._btn_roll_up = tk.Button(roll_row, text="上滚", command=self._select_roll_up)
        self._btn_roll_up.pack(side="left", padx=2)
        self._btn_roll_down = tk.Button(roll_row, text="下滚", command=self._select_roll_down)
        self._btn_roll_down.pack(side="left", padx=2)
        self._btn_roll_up.config(state="disabled")
        self._btn_roll_down.config(state="disabled")

        # 区间选择：从第 a 帧起每 b 帧共选 c 帧
        range_row = tk.Frame(left_frame)
        range_row.pack(side="bottom", fill="x", padx=4, pady=(0, 4))
        tk.Label(range_row, text="第").pack(side="left")
        tk.Entry(range_row, textvariable=self._range_start_var, width=3).pack(side="left", padx=(2, 2))
        tk.Label(range_row, text="帧起每").pack(side="left")
        tk.Entry(range_row, textvariable=self._range_step_var, width=3).pack(side="left", padx=(2, 2))
        tk.Label(range_row, text="帧，共选").pack(side="left")
        tk.Entry(range_row, textvariable=self._range_count_var, width=3).pack(side="left", padx=(2, 2))
        tk.Label(range_row, text="帧").pack(side="left")
        tk.Button(range_row, text="选择", command=self._select_by_range).pack(side="left", padx=(6, 2))

        # 快速选择：奇数 / 偶数 / 随机（随机右侧为数量，默认 30），先 pack 使在更下方
        quick_row = tk.Frame(left_frame)
        quick_row.pack(side="bottom", fill="x", padx=4, pady=(0, 4))
        tk.Button(quick_row, text="奇数", command=self._select_odd).pack(side="left", padx=2)
        tk.Button(quick_row, text="偶数", command=self._select_even).pack(side="left", padx=2)
        tk.Button(quick_row, text="随机", command=self._select_random).pack(side="left", padx=2)
        self._random_count_var = tk.StringVar(value="30")
        tk.Entry(quick_row, textvariable=self._random_count_var, width=5).pack(side="left", padx=2)

        # 帧列表底部：左对齐 3 按钮，右对齐单击行为下拉框
        list_footer = tk.Frame(left_frame)
        list_footer.pack(side="bottom", fill="x", padx=4, pady=4)
        tk.Button(list_footer, text="全选", command=self._select_all).pack(side="left", padx=2)
        tk.Button(list_footer, text="反选", command=self._invert_selection).pack(side="left", padx=2)
        tk.Button(list_footer, text="清除", command=self._select_none).pack(side="left", padx=2)
        self._click_mode_combo = ttk.Combobox(
            list_footer,
            textvariable=self._click_mode_var,
            values=["普通选择", "单击追加"],
            state="readonly",
            width=8,
        )
        self._click_mode_combo.pack(side="right", padx=2)
        self._click_mode_combo.set("单击追加")
        self._click_mode_combo.bind("<<ComboboxSelected>>", lambda e: self._defocus_combobox())

        paned.add(left_frame, weight=1)

        # 右侧：Tab 容器（动画预览 / 首尾帧）
        self._right_notebook = ttk.Notebook(paned)
        paned.add(self._right_notebook, weight=2)
        self._preview_tab_index = 0  # 「动画预览」为第 0 个 tab

        # Tab「动画预览」：帧预览容器
        preview_tab = tk.Frame(self._right_notebook)
        self._right_notebook.add(preview_tab, text="动画预览")
        preview_tab.rowconfigure(0, weight=0)
        preview_tab.rowconfigure(1, weight=1)
        preview_tab.rowconfigure(2, weight=0)
        preview_tab.columnconfigure(0, weight=1)

        # 顶部：左侧当前帧信息，右侧预览帧率
        top_row = tk.Frame(preview_tab)
        top_row.grid(row=0, column=0, sticky="ew", padx=4, pady=(4, 2))
        top_row.columnconfigure(0, weight=1)
        tk.Label(
            top_row,
            textvariable=self._frame_info_var,
            anchor="w",
            font=("", 10),
        ).grid(row=0, column=0, sticky="w")
        tk.Label(
            top_row,
            textvariable=self._preview_fps_var,
            anchor="e",
            font=("", 10),
        ).grid(row=0, column=1, sticky="e")

        self._preview_label = tk.Label(
            preview_tab,
            text="点击打开帧序列文件夹",
            bg="#ddd",
            font=("", 12),
        )
        self._preview_label.grid(row=1, column=0, sticky="nsew")
        self._preview_label.bind("<Configure>", self._on_preview_resize)
        self._preview_label.bind("<Button-1>", self._on_preview_click)

        # 帧动画下方控制区
        controls = tk.Frame(preview_tab)
        controls.grid(row=2, column=0, sticky="ew", padx=8, pady=8)

        # 目标帧率滑块 1~60
        tk.Label(controls, textvariable=self._fps_label_var).pack(side="left", padx=(0, 4))
        self._fps_scale = tk.Scale(
            controls,
            from_=1,
            to=60,
            orient="horizontal",
            showvalue=False,
            variable=self._fps_var,
            command=self._on_fps_change,
            length=180,
        )
        self._fps_scale.pack(side="left", padx=4)

        # 暂停/播放（默认播放，所以按钮初始为“暂停”）
        self._play_button = tk.Button(controls, text="⏸", command=self._toggle_play, width=2)
        self._play_button.pack(side="left", padx=4)

        self._btn_next_frame = tk.Button(controls, text=">", command=self._on_next_frame, width=2)
        self._btn_next_frame.pack(side="left", padx=2)
        self._update_next_frame_button_state()

        # 播放模式：循环 / 单次（下拉框，默认循环）
        self._play_mode_combo = ttk.Combobox(
            controls,
            values=["循环", "单次"],
            state="readonly",
            width=6,
        )
        self._play_mode_combo.set("循环")
        self._play_mode_combo.pack(side="left", padx=4)
        self._play_mode_combo.bind(
            "<<ComboboxSelected>>",
            lambda e: (self._on_play_mode_combo_change(), self._defocus_combobox()),
        )

        # 色彩下拉框：原图/灰度/黑白（在背景左侧）
        self._color_combo = ttk.Combobox(
            controls,
            textvariable=self._color_mode_var,
            values=["原图", "灰度", "黑白"],
            state="readonly",
            width=6,
        )
        self._color_combo.pack(side="left", padx=4)
        self._color_combo.set("原图")
        self._color_combo.bind("<<ComboboxSelected>>", lambda e: (self._on_color_mode_change(e), self._defocus_combobox()))

        # 背景下拉框：透明/黑/白/粉/图片
        self._bg_combo = ttk.Combobox(
            controls,
            textvariable=self._bg_var,
            values=["透明", "黑", "白", "粉", "图片"],
            state="readonly",
            width=6,
        )
        self._bg_combo.pack(side="left", padx=4)
        self._bg_combo.bind("<<ComboboxSelected>>", lambda e: (self._on_bg_change(e), self._defocus_combobox()))

        # 预览缩放模式：适应 / x0.1 / x0.3 / x0.5 / x1 / x2（放在背景右侧）
        self._zoom_combo = ttk.Combobox(
            controls,
            values=["适应", "x0.1", "x0.3", "x0.5", "x1", "x2"],
            state="readonly",
            width=6,
        )
        self._zoom_combo.pack(side="left", padx=4)
        self._zoom_combo.set("适应")
        self._zoom_combo.bind("<<ComboboxSelected>>", lambda e: (self._on_zoom_change(e), self._defocus_combobox()))

        # 轮廓：为帧绘制红色边框和中心十字线
        self._ruler_check = tk.Checkbutton(
            controls,
            text="轮廓",
            variable=self._ruler_var,
            command=self._on_ruler_toggle,
        )
        self._ruler_check.pack(side="left", padx=4)

        # Tab「首尾帧」：三段式布局（信息/预览/底部），不复制动画预览功能
        head_tail_tab = tk.Frame(self._right_notebook)
        self._right_notebook.add(head_tail_tab, text="首尾帧")
        head_tail_tab.rowconfigure(0, weight=0)
        head_tail_tab.rowconfigure(1, weight=1)
        head_tail_tab.rowconfigure(2, weight=0)
        head_tail_tab.columnconfigure(0, weight=1)

        head_info = tk.Label(
            head_tail_tab,
            textvariable=self._headtail_info_var,
            anchor="w",
            font=("", 10),
        )
        head_info.grid(row=0, column=0, sticky="ew", padx=4, pady=(4, 2))

        self._headtail_preview_label = tk.Label(
            head_tail_tab,
            text="请选择帧",
            bg="#ddd",
            font=("", 12),
        )
        self._headtail_preview_label.grid(row=1, column=0, sticky="nsew")
        self._headtail_preview_label.bind("<Configure>", self._on_headtail_resize)

        head_controls = tk.Frame(head_tail_tab)
        head_controls.grid(row=2, column=0, sticky="ew", padx=8, pady=8)
        self._headtail_mode_combo = ttk.Combobox(
            head_controls,
            textvariable=self._headtail_mode_var,
            values=["差值", "叠加"],
            state="readonly",
            width=6,
        )
        self._headtail_mode_combo.pack(side="left", padx=4)
        self._headtail_mode_combo.set("差值")
        self._headtail_mode_combo.bind("<<ComboboxSelected>>", lambda e: (self._on_headtail_mode_change(e), self._defocus_combobox()))

        self._right_notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)

    def _show_about(self) -> None:
        """显示关于信息，包括作者与 GitHub 地址。"""
        message = (
            "Animaker 动画魅客\n\n"
            "作者：wkw\n"
            "GitHub：https://github.com/wkw1125/animaker"
        )
        messagebox.showinfo("关于 Animaker", message, parent=self.root)

    def _on_tab_changed(self, _event: tk.Event) -> None:
        """切换到「动画预览」时，若正在播放则继续调度。"""
        if self._is_preview_tab_active() and self._is_playing.get() and self._animation_indices:
            self._schedule_next_tick()
        # 切换到首尾帧时，确保内容刷新
        if not self._is_preview_tab_active():
            self._update_headtail_view()

    def _on_drop(self, event) -> None:
        """拖拽放入：若为文件夹则等同于打开帧序列文件夹。"""
        if not _DND_AVAILABLE or not event.data:
            return
        try:
            for raw in self.root.tk.splitlist(event.data):
                s = str(raw).strip()
                if s.startswith("file://"):
                    s = unquote(s[7:].lstrip("/"))
                p = Path(s)
                if p.is_dir():
                    self._load_folder(p)
                    return
        except Exception:
            pass

    def _open_path_with_system(self, path: Path | str) -> None:
        """用系统默认程序打开文件或目录（绝对路径，避免选「是」后打不开）。"""
        p = Path(path).resolve()
        if not p.exists():
            return
        try:
            if sys.platform == "win32":
                os.startfile(str(p))
            elif sys.platform == "darwin":
                subprocess.run(["/usr/bin/open", str(p)], check=False)
            else:
                subprocess.run(["xdg-open", str(p)], check=False)
        except Exception:
            pass

    def _load_folder(self, path: Path) -> None:
        """加载指定文件夹为帧序列（与「打开帧序列文件夹」相同逻辑）。"""
        save_last_dir(path)
        self.folder_path = path
        # 打开新文件夹后，导出窗口「名称」默认改为该文件夹名
        self._export_name_last = path.name
        files: list[Path] = sorted(
            [f for f in path.iterdir() if f.is_file() and f.suffix.lower() in IMAGE_EXTENSIONS],
            key=lambda p: p.name,
        )
        self.image_files = files
        self._image_sizes = []
        self._file_sizes = []
        for f in self.image_files:
            try:
                size_bytes = f.stat().st_size
            except OSError:
                size_bytes = 0
            self._file_sizes.append(size_bytes)
            try:
                with Image.open(f) as im:
                    self._image_sizes.append((int(im.width), int(im.height)))
            except Exception:
                self._image_sizes.append((0, 0))
        self._update_status_bar(len(self.image_files), 0)
        self._listbox.delete(0, tk.END)
        for f in self.image_files:
            self._listbox.insert(tk.END, f.name)
        self._smart_headtail_combo["values"] = []
        self._smart_headtail_combo.set("未计算")
        self._bg_image_cache = None
        self._update_smart_headtail_ui_state()
        self._stop_animation()
        self._preview_label.config(image="", text="请从左侧列表选择帧（可多选）")
        self._preview_photo = None
        if self.image_files:
            self._listbox.selection_set(0, tk.END)
            self._sync_selection_to_preview()
        self._update_export_button_state()
        if (
            self._smart_headtail_open_calc_var.get()
            and len(self.image_files) >= self._SMART_HEADTAIL_MIN_GAP + 1
        ):
            self._run_smart_headtail_async(
                self._get_default_smart_headtail_params(),
                show_progress_dialog=True,
                show_result_messagebox=True,
            )

    def _on_open_folder(self) -> None:
        initial_dir = get_default_initial_dir()
        folder = filedialog.askdirectory(
            title="选择帧序列文件夹",
            initialdir=initial_dir,
        )
        self.root.focus_force()
        if not folder:
            return
        path = Path(folder)
        if not path.is_dir():
            return
        self._load_folder(path)

    # 智能首尾帧默认参数
    _SMART_HEADTAIL_ALPHA_THRESHOLD = 40
    _SMART_HEADTAIL_MIN_GAP = 15
    _SMART_HEADTAIL_COMPARE_SIZE = 256
    _SMART_HEADTAIL_TOP_K = 5
    _SMART_HEADTAIL_USE_PERIOD_PRIOR = True
    _SMART_HEADTAIL_EXPECTED_PERIOD = 24

    def _get_default_smart_headtail_params(self) -> dict:
        """返回智能首尾帧的默认参数字典：本次运行内若已计算过则用上次参数，否则用类默认值。"""
        if self._last_smart_headtail_params is not None:
            return dict(self._last_smart_headtail_params)
        return {
            "alpha_threshold": self._SMART_HEADTAIL_ALPHA_THRESHOLD,
            "min_gap": self._SMART_HEADTAIL_MIN_GAP,
            "compare_size": self._SMART_HEADTAIL_COMPARE_SIZE,
            "top_k": self._SMART_HEADTAIL_TOP_K,
            "use_period_prior": self._SMART_HEADTAIL_USE_PERIOD_PRIOR,
            "expected_period": self._SMART_HEADTAIL_EXPECTED_PERIOD,
        }

    def _compute_smart_headtail(self, params: dict | None = None) -> list[tuple[int, int, float]]:
        """在序列中找最相似的两帧：取 SSIM 最高的 top_k 对，按周期先验排序；返回 [(i, j, ssim), ...]。params 未传或缺少键时用类默认值。"""
        p = params or {}
        n = len(self.image_files)
        min_gap = p.get("min_gap", self._SMART_HEADTAIL_MIN_GAP)
        size = p.get("compare_size", self._SMART_HEADTAIL_COMPARE_SIZE)
        alpha_th = p.get("alpha_threshold", self._SMART_HEADTAIL_ALPHA_THRESHOLD)
        top_k = p.get("top_k", self._SMART_HEADTAIL_TOP_K)
        use_period = p.get("use_period_prior", self._SMART_HEADTAIL_USE_PERIOD_PRIOR)
        expected_period = p.get("expected_period", self._SMART_HEADTAIL_EXPECTED_PERIOD)
        if n < min_gap + 1:
            return []
        # 加载每帧：RGBA → 缩放到 size×size，灰度 + mask(alpha>th)
        grays: list[np.ndarray] = []
        masks: list[np.ndarray] = []
        for i in range(n):
            try:
                with Image.open(self.image_files[i]) as im:
                    im = im.convert("RGBA")
                    if im.size != (size, size):
                        im = im.resize((size, size), Image.Resampling.LANCZOS)
                    arr = np.array(im)
                    alpha = arr[:, :, 3]
                    rgb = arr[:, :, :3]
                    gray = np.array(
                        Image.fromarray(rgb).convert("L"),
                        dtype=np.float64,
                    )
                    mask = alpha > alpha_th
                    grays.append(gray)
                    masks.append(mask)
            except Exception:
                grays.append(np.zeros((size, size), dtype=np.float64))
                masks.append(np.ones((size, size), dtype=bool))
        # 每帧前景 bbox（无前景则用全图）
        def bbox_from_mask(m: np.ndarray) -> tuple[int, int, int, int]:
            xs, ys = np.where(m)
            if xs.size == 0 or ys.size == 0:
                return (0, 0, size, size)
            return (int(ys.min()), int(xs.min()), int(ys.max()) + 1, int(xs.max()) + 1)

        # 收集 (ssim, i, j)，按 SSIM 降序取前 top_k
        candidates: list[tuple[float, int, int]] = []
        for i in range(n):
            for j in range(i + min_gap, n):
                if j >= len(grays):
                    continue
                b1 = bbox_from_mask(masks[i])
                b2 = bbox_from_mask(masks[j])
                x1 = max(b1[0], b2[0])
                y1 = max(b1[1], b2[1])
                x2 = min(b1[2], b2[2])
                y2 = min(b1[3], b2[3])
                if x1 >= x2 or y1 >= y2:
                    patch1 = grays[i]
                    patch2 = grays[j]
                else:
                    patch1 = grays[i][y1:y2, x1:x2]
                    patch2 = grays[j][y1:y2, x1:x2]
                if patch1.size == 0:
                    continue
                s = structural_similarity(patch1, patch2, data_range=255)
                candidates.append((s, i, j))
        if not candidates:
            return []
        candidates.sort(key=lambda x: -x[0])
        top = candidates[:top_k]
        if use_period and expected_period is not None:
            top.sort(key=lambda x: abs((x[2] - x[1]) - expected_period))
        return [(i, j, s) for s, i, j in top]

    def _update_smart_headtail_ui_state(self) -> None:
        """未打开帧序列时禁用计算按钮、结果下拉框、切换按钮；打开后启用。"""
        enabled = bool(self.image_files)
        self._btn_smart_headtail.config(state="normal" if enabled else "disabled")
        self._smart_headtail_combo.config(state="readonly" if enabled else "disabled")
        self._btn_smart_headtail_next.config(state="normal" if enabled else "disabled")

    def _on_smart_headtail(self) -> None:
        """智能首尾帧：弹出参数窗口，确认后计算；取消则不计算。"""
        if not self.image_files:
            messagebox.showinfo("智能首尾帧", "请先打开帧序列文件夹。")
            return
        n = len(self.image_files)
        min_gap = self._SMART_HEADTAIL_MIN_GAP
        if n < min_gap + 1:
            messagebox.showinfo(
                "智能首尾帧",
                f"帧数不足（需至少 {min_gap + 1} 帧），无法计算。",
            )
            return
        self._show_smart_headtail_param_dialog()

    def _show_smart_headtail_param_dialog(self) -> None:
        """弹出智能首尾帧参数窗口，确定后使用填入参数进行计算。"""
        defaults = self._get_default_smart_headtail_params()
        dlg = tk.Toplevel(self.root)
        dlg.title("智能首尾帧 - 参数")
        dlg.resizable(False, False)
        dlg.transient(self.root)
        dlg.grab_set()
        row = 0

        def add_row(label: str, var: tk.StringVar | tk.BooleanVar, hint: str = "") -> None:
            nonlocal row
            frm = tk.Frame(dlg)
            frm.grid(row=row, column=0, sticky="ew", padx=12, pady=4)
            tk.Label(frm, text=label, width=14, anchor="w").pack(side="left")
            if isinstance(var, tk.BooleanVar):
                tk.Checkbutton(frm, variable=var).pack(side="left")
            else:
                tk.Entry(frm, textvariable=var, width=10).pack(side="left")
            if hint:
                tk.Label(frm, text=hint, fg="gray").pack(side="left", padx=4)
            row += 1

        v_alpha = tk.StringVar(value=str(defaults["alpha_threshold"]))
        v_min_gap = tk.StringVar(value=str(defaults["min_gap"]))
        v_compare_size = tk.StringVar(value=str(defaults["compare_size"]))
        v_top_k = tk.StringVar(value=str(defaults["top_k"]))
        v_use_period = tk.BooleanVar(value=defaults["use_period_prior"])
        v_expected = tk.StringVar(
            value=(str(defaults["expected_period"]) if defaults["expected_period"] is not None else "")
        )

        add_row("前景 Alpha 阈值", v_alpha, "(> 此值计入前景)")
        add_row("最小帧间距", v_min_gap, "(j-i ≥ 此值)")
        add_row("比较尺寸", v_compare_size, "(边长像素)")
        add_row("候选组数 top_k", v_top_k, "")
        add_row("周期先验", v_use_period, "(优先接近期望周期)")
        add_row("期望周期(帧)", v_expected, "(空=不使用)")

        def on_ok() -> None:
            try:
                alpha_th = int(v_alpha.get().strip())
                min_gap = int(v_min_gap.get().strip())
                compare_size = int(v_compare_size.get().strip())
                top_k = int(v_top_k.get().strip())
            except ValueError:
                messagebox.showerror("智能首尾帧", "请填写有效的整数（Alpha 阈值、最小帧间距、比较尺寸、top_k）。", parent=dlg)
                return
            expected_str = v_expected.get().strip()
            expected_period: int | None = int(expected_str) if expected_str else None
            if alpha_th < 0 or min_gap < 1 or compare_size < 8 or top_k < 1:
                messagebox.showerror("智能首尾帧", "Alpha 阈值≥0，最小帧间距≥1，比较尺寸≥8，top_k≥1。", parent=dlg)
                return
            try:
                dlg.grab_release()
                dlg.destroy()
            except Exception:
                pass
            params = {
                "alpha_threshold": alpha_th,
                "min_gap": min_gap,
                "compare_size": compare_size,
                "top_k": top_k,
                "use_period_prior": v_use_period.get(),
                "expected_period": expected_period,
            }
            self._run_smart_headtail_async(params, show_progress_dialog=True, show_result_messagebox=True)

        def on_cancel() -> None:
            try:
                dlg.grab_release()
                dlg.destroy()
            except Exception:
                pass

        btn_frm = tk.Frame(dlg)
        btn_frm.grid(row=row, column=0, pady=12)
        tk.Button(btn_frm, text="确定", command=on_ok, width=8).pack(side="left", padx=4)
        tk.Button(btn_frm, text="取消", command=on_cancel, width=8).pack(side="left", padx=4)

    def _run_smart_headtail_async(
        self,
        params: dict,
        *,
        show_progress_dialog: bool = True,
        show_result_messagebox: bool = True,
    ) -> None:
        """使用给定参数在后台运行智能首尾帧计算；完成后更新下拉框与选中区间。本次参数在本次运行内作为下次默认。"""
        self._last_smart_headtail_params = dict(params)
        progress_dlg: tk.Toplevel | None = None
        if show_progress_dialog:
            progress_dlg = tk.Toplevel(self.root)
            progress_dlg.title("智能首尾帧")
            progress_dlg.resizable(False, False)
            tk.Label(progress_dlg, text="计算中，请稍候…", font=("", 12), padx=24, pady=16).pack()
            progress_dlg.transient(self.root)

        def run() -> None:
            results = self._compute_smart_headtail(params)
            self.root.after(0, lambda: _on_done(progress_dlg, results, show_result_messagebox))

        def _on_done(
            dialog: tk.Toplevel | None,
            results: list[tuple[int, int, float]],
            show_msg: bool,
        ) -> None:
            if dialog:
                try:
                    dialog.destroy()
                except Exception:
                    pass
            if not results:
                if show_msg:
                    messagebox.showerror("智能首尾帧", "计算未得到有效结果。")
                return
            display_values = [
                f"{n}-[{i+1},{j+1}]({j-i+1}) ssim={ssim:.2f}"
                for n, (i, j, ssim) in enumerate(results, 1)
            ]
            self._smart_headtail_combo["values"] = display_values
            self._smart_headtail_combo.set(display_values[0])
            idx_i, idx_j, ssim_val = results[0]
            self._listbox.selection_clear(0, tk.END)
            for idx in range(idx_i, idx_j + 1):
                self._listbox.selection_set(idx)
            self._sync_selection_to_preview()
            self._update_export_button_state()
            if show_msg:
                msg = (
                    f"已找到 {len(results)} 组候选首尾帧\n\n"
                    f"当前选中：第 {idx_i + 1}～{idx_j + 1} 帧，共 {idx_j - idx_i + 1} 帧，SSIM={ssim_val:.4f}\n\n"
                    f"可在顶部下拉框中切换其他候选组"
                )
                messagebox.showinfo("智能首尾帧", msg)
        threading.Thread(target=run, daemon=True).start()

    def _on_smart_headtail_next(self) -> None:
        """首尾帧结果「下一组」：下拉框切换为下一项并选中对应帧序列（末项后回到第一项）。"""
        vals = self._smart_headtail_combo["values"]
        if not vals:
            return
        cur = self._smart_headtail_combo.get().strip()
        try:
            idx = list(vals).index(cur)
        except ValueError:
            idx = -1
        next_idx = (idx + 1) % len(vals)
        self._smart_headtail_combo.set(vals[next_idx])
        self._on_smart_headtail_combo_select()

    def _on_smart_headtail_combo_select(self) -> None:
        """切换智能首尾帧下拉框时，选中对应的帧序列。"""
        val = self._smart_headtail_combo.get().strip()
        if not val or val == "未计算":
            return
        # 解析格式：n-[i,j](count) ssim=0.99，提取 [i,j] 部分
        start = val.find("[")
        end = val.find("]")
        if start == -1 or end == -1 or start >= end:
            return
        try:
            ij = val[start + 1 : end].split(",")
            if len(ij) != 2:
                return
            i1, j1 = int(ij[0].strip()), int(ij[1].strip())
            i, j = i1 - 1, j1 - 1
        except ValueError:
            return
        n = len(self.image_files)
        if i < 0 or j < i or j >= n:
            return
        self._listbox.selection_clear(0, tk.END)
        for idx in range(i, j + 1):
            self._listbox.selection_set(idx)
        self._sync_selection_to_preview()
        self._update_export_button_state()
        self._defocus_combobox()

    def _update_export_button_state(self) -> None:
        has_folder = self.folder_path is not None and len(self.image_files) > 0
        sel = self._listbox.curselection()
        self._btn_export.config(state="normal" if (has_folder and len(sel) > 0) else "disabled")

    def _defocus_combobox(self) -> None:
        """选择后使下拉框不保留焦点，焦点回到帧列表。"""
        self._listbox.focus_set()

    def _on_preview_click(self, _event: tk.Event) -> None:
        """在未加载序列帧时，点击预览区域等同于点击打开按钮。"""
        if not self.image_files:
            self._on_open_folder()

    def _update_status_bar(self, total: int, selected: int) -> None:
        if self.folder_path is None:
            self._status_var.set("未打开文件夹")
            return
        fps = max(1, int(self._fps_var.get()))
        duration = 0.0
        if selected > 0:
            duration = selected / fps
        # 选中帧合计文件大小（KB/MB）
        total_bytes = 0
        sel = self._listbox.curselection()
        for i in sel:
            if i < len(self._file_sizes):
                total_bytes += self._file_sizes[i]
        if total_bytes >= 1024 * 1024:
            size_str = f"{total_bytes / (1024 * 1024):.2f} MB"
        else:
            size_str = f"{total_bytes / 1024:.2f} KB"
        self._status_var.set(
            f"文件夹：{self.folder_path}  |  已选：{selected}/{total}, {size_str}  |  帧率：{fps}  |  时长：{duration:.1f}秒"
        )
        self._update_export_button_state()
        self._update_roll_button_state()

    def _update_roll_button_state(self) -> None:
        n = self._listbox.size()
        sel = tuple(self._listbox.curselection())
        if not sel or n == 0:
            self._btn_roll_up.config(state="disabled")
            self._btn_roll_down.config(state="disabled")
            return
        self._btn_roll_up.config(state="normal" if min(sel) > 0 else "disabled")
        self._btn_roll_down.config(state="normal" if max(sel) < n - 1 else "disabled")

    def _rgba_to_p_with_transparency(self, im: Image.Image) -> Image.Image:
        """将 RGBA 转为 P 模式并保留透明（GIF 单色透明）；透明固定为调色板索引 0，不引入可见衬色。"""
        if im.mode != "RGBA":
            im = im.convert("RGBA")
        w, h = im.size
        rgb = im.convert("RGB")
        alpha = im.split()[3]
        # 透明区用罕见衬色，量化后该索引视为透明并映射到 0，避免品红等进入画面
        sentinel = (1, 2, 3)
        composite = Image.new("RGB", (w, h), sentinel)
        opaque_mask = alpha.point(lambda a: 255 if a >= 128 else 0, "L")
        composite.paste(rgb, mask=opaque_mask)
        p = composite.quantize(colors=255, method=Image.Quantize.MEDIANCUT)
        palette = p.getpalette()
        if palette is None:
            palette = [0] * 768
        # 找衬色在调色板中的索引
        best_i = 0
        best_d = 3 * 256 * 256
        for i in range(min(255, len(palette) // 3)):
            dr = palette[i * 3] - sentinel[0]
            dg = palette[i * 3 + 1] - sentinel[1]
            db = palette[i * 3 + 2] - sentinel[2]
            d = dr * dr + dg * dg + db * db
            if d < best_d:
                best_d = d
                best_i = i
        # 调色板：索引 0 = 透明占位，1..255 = 原 255 色
        new_palette = [0, 0, 0] + palette[: 255 * 3]
        out = Image.new("P", (w, h), 0)
        out.putpalette(new_palette)
        # 透明（alpha<128 或量化到衬色）-> 0；其余 -> 1+原索引
        q_arr = list(p.getdata())
        a_arr = list(alpha.getdata())
        out_data = []
        for i, q in enumerate(q_arr):
            if a_arr[i] < 128 or q == best_i:
                out_data.append(0)
            else:
                out_data.append(1 + q)
        out.putdata(out_data)
        out.info["transparency"] = 0
        return out

    def _build_gif_from_frames(
        self, sel: list[int], fps: int, max_size: int = 512
    ) -> bytes | None:
        """用选中帧按指定 fps 生成 GIF（支持透明）；最长边大于 max_size 时先缩小。返回 GIF 字节或 None。

        GIF 时长/帧率：每帧在文件里存一个「延迟」值，单位是百分之一秒(centisecond)。
        帧率 = 100/延迟_cs，总时长(秒) = 帧数 × 延迟_cs/100。
        Pillow 的 duration 参数单位是毫秒；写入时做 int(duration/10) 得到 centiseconds，故传 10×centiseconds。
        为免截断导致偏快，这里用 ceil(100/fps) 得到 centiseconds，再 ×10 传 Pillow，并对每帧显式传列表保证每帧同延。
        """
        if not sel or fps < 1:
            return None
        duration_cs = max(1, math.ceil(100 / fps))
        duration_ms = 10 * duration_cs
        frames_rgba: list[Image.Image] = []
        try:
            for i in sel:
                if i >= len(self.image_files):
                    continue
                with Image.open(self.image_files[i]) as im:
                    im = im.convert("RGBA")
                    w, h = im.size
                    if max(w, h) > max_size:
                        im = im.copy()
                        im.thumbnail((max_size, max_size), Image.Resampling.LANCZOS)
                    frames_rgba.append(im)
            if not frames_rgba:
                return None
            frames_p = [self._rgba_to_p_with_transparency(im) for im in frames_rgba]
            n_frames = len(frames_p)
            trans_idx = frames_p[0].info.get("transparency", 0)
            buf = io.BytesIO()
            frames_p[0].save(
                buf,
                format="GIF",
                save_all=True,
                append_images=frames_p[1:],
                duration=[duration_ms] * n_frames,
                loop=0,
                transparency=trans_idx,
                disposal=2,
            )
            return buf.getvalue()
        except Exception:
            return None

    def _on_export(self) -> None:
        """导出入口：校验状态后弹出导出参数窗口。"""
        if self.folder_path is None or not self.image_files:
            messagebox.showinfo("导出", "请先打开帧序列文件夹，并选择要导出的帧。")
            self.root.focus_force()
            return
        sel = sorted(int(i) for i in self._listbox.curselection())
        if not sel:
            messagebox.showinfo("导出", "请先选择要导出的帧。")
            self.root.focus_force()
            return
        self._show_export_dialog(sel)

    def _show_export_dialog(self, sel: list[int]) -> None:
        """导出参数窗口：左侧参数、右侧 JSON 预览，底部取消/导出按钮。"""
        if not sel or self.folder_path is None:
            return

        # 默认名称：上次导出时的名称；若尚未导出或刚打开新文件夹则为当前文件夹名
        default_name = self._export_name_last or (
            self.folder_path.name if self.folder_path is not None else "export"
        )
        name_var = tk.StringVar(value=default_name)

        # Phaser 动画参数：本次运行内记住上次的配置
        phaser_enabled_default = getattr(self, "_phaser_anim_enabled_last", True)
        atlas_default = getattr(self, "_phaser_atlas_last", "")
        frame_fmt_default = getattr(self, "_phaser_frame_fmt_last", "{name}/{frame}.{ext}")

        base_fps = max(1, int(self._fps_var.get()))
        # 播放模式：循环 -> repeat=-1，一次 -> repeat=0
        play_mode = (self._play_mode_var.get() or "loop").strip()
        repeat_default = -1 if play_mode == "loop" else 0

        phaser_enable_var = tk.BooleanVar(value=phaser_enabled_default)
        phaser_fps_var = tk.StringVar(value=str(base_fps))
        phaser_repeat_var = tk.StringVar(value=str(repeat_default))
        phaser_atlas_var = tk.StringVar(value=atlas_default)
        phaser_frame_fmt_var = tk.StringVar(value=frame_fmt_default)

        dlg = tk.Toplevel(self.root)
        dlg.title("导出")
        dlg.resizable(True, True)
        dlg.transient(self.root)
        dlg.grab_set()

        # 打开时默认聚焦名称输入框并全选；Enter=导出，Esc=取消
        def _focus_name_and_select() -> None:
            name_entry.focus_set()
            name_entry.select_range(0, tk.END)
            name_entry.icursor(tk.END)
        dlg.after(0, _focus_name_and_select)

        # 第一行：左参数、右预览
        top_frame = tk.Frame(dlg)
        top_frame.pack(side="top", fill="both", expand=True, padx=10, pady=10)

        params_frame = tk.Frame(top_frame)
        params_frame.pack(side="left", fill="both", expand=True, padx=(0, 8))

        preview_frame = tk.Frame(top_frame)
        preview_frame.pack(side="right", fill="both", expand=True)

        # 参数：名称 + 导出选项
        tk.Label(params_frame, text="名称").grid(row=0, column=0, sticky="w")
        name_entry = tk.Entry(params_frame, textvariable=name_var, width=24)
        name_entry.grid(row=0, column=1, sticky="ew", padx=(4, 0))
        params_frame.columnconfigure(1, weight=1)

        rename_cb = tk.Checkbutton(
            params_frame,
            text="用名称重命名帧",
            variable=self._export_rename_var,
        )
        rename_cb.grid(row=1, column=0, columnspan=2, sticky="w", pady=(6, 0))

        rename_digits_default = getattr(self, "_export_rename_digits_last", 3)
        rename_digits_var = tk.StringVar(value=str(rename_digits_default))
        tk.Label(params_frame, text="帧序位数").grid(row=2, column=0, sticky="w", pady=(4, 0))
        rename_digits_entry = tk.Entry(params_frame, textvariable=rename_digits_var, width=6)
        rename_digits_entry.grid(row=2, column=1, sticky="w", padx=(4, 0), pady=(4, 0))

        def _update_rename_digits_state() -> None:
            rename_digits_entry.configure(state="normal" if self._export_rename_var.get() else "disabled")

        def _on_rename_toggle() -> None:
            _update_rename_digits_state()
            refresh_preview()

        rename_cb.configure(command=_on_rename_toggle)

        # 动画参数分隔线
        sep = ttk.Separator(params_frame, orient="horizontal")
        sep.grid(row=4, column=0, columnspan=2, sticky="ew", pady=(8, 8))

        # Phaser 动画参数（在勾选 Phaser 动画定义后可编辑）
        def _update_phaser_controls_state() -> None:
            state = "normal" if phaser_enable_var.get() else "disabled"
            fps_entry.configure(state=state)
            repeat_entry.configure(state=state)
            atlas_entry.configure(state=state)
            frame_fmt_entry.configure(state=state)

        def _on_phaser_toggle() -> None:
            self._phaser_anim_enabled_last = phaser_enable_var.get()
            _update_phaser_controls_state()
            refresh_preview()

        phaser_cb = tk.Checkbutton(
            params_frame,
            text="Phaser 动画定义",
            variable=phaser_enable_var,
            command=_on_phaser_toggle,
        )
        phaser_cb.grid(row=5, column=0, columnspan=2, sticky="w")

        tk.Label(params_frame, text="帧率").grid(row=6, column=0, sticky="w", pady=(6, 0))
        fps_entry = tk.Entry(params_frame, textvariable=phaser_fps_var, width=10)
        fps_entry.grid(row=6, column=1, sticky="w", padx=(4, 0), pady=(6, 0))

        tk.Label(params_frame, text="重复").grid(row=7, column=0, sticky="w", pady=(4, 0))
        repeat_entry = tk.Entry(params_frame, textvariable=phaser_repeat_var, width=10)
        repeat_entry.grid(row=7, column=1, sticky="w", padx=(4, 0), pady=(4, 0))

        tk.Label(params_frame, text="图集名称").grid(row=8, column=0, sticky="w", pady=(6, 0))
        atlas_entry = tk.Entry(params_frame, textvariable=phaser_atlas_var, width=24)
        atlas_entry.grid(row=8, column=1, sticky="ew", padx=(4, 0), pady=(6, 0))

        tk.Label(params_frame, text="帧名格式").grid(row=9, column=0, sticky="w", pady=(4, 0))
        frame_fmt_entry = tk.Entry(params_frame, textvariable=phaser_frame_fmt_var, width=24)
        frame_fmt_entry.grid(row=9, column=1, sticky="ew", padx=(4, 0), pady=(4, 0))

        # 分割线 + 导出GIF 移到下方（不再单独提供“保留后缀”选项，由帧名格式决定）
        sep2 = ttk.Separator(params_frame, orient="horizontal")
        sep2.grid(row=10, column=0, columnspan=2, sticky="ew", pady=(8, 8))
        gif_cb = tk.Checkbutton(
            params_frame,
            text="导出GIF",
            variable=self._export_gif_var,
        )
        gif_cb.grid(row=11, column=0, columnspan=2, sticky="w", pady=(0, 4))

        # 初始根据是否启用 Phaser 动画、用名称重命名帧 设置控件状态
        _update_phaser_controls_state()
        _update_rename_digits_state()

        # 预览区：标题行（左「动画数据预览」、右「复制」）+ 只读多行文本框
        preview_title_row = tk.Frame(preview_frame)
        preview_title_row.pack(fill="x")
        tk.Label(preview_title_row, text="动画数据预览").pack(side="left")
        tk.Frame(preview_title_row).pack(side="left", fill="x", expand=True)

        def _copy_preview() -> None:
            try:
                content = preview_text.get("1.0", tk.END)
                self.root.clipboard_clear()
                self.root.clipboard_append(content)
            except Exception:
                pass

        tk.Button(preview_title_row, text="复制", width=6, command=_copy_preview).pack(side="right", padx=(4, 0))
        preview_text = tk.Text(
            preview_frame,
            width=60,
            height=18,
            font=("Courier", 9),
            wrap="none",
        )
        preview_text.pack(side="top", fill="both", expand=True)
        preview_text.configure(state="disabled")

        src_dir = str(self.folder_path)
        src_frames = [self.image_files[i].name for i in sel if i < len(self.image_files)]

        def _get_rename_digits() -> int:
            try:
                d = int((rename_digits_var.get() or "").strip() or "3")
                return max(1, min(9, d))
            except ValueError:
                return 3

        def _build_frames_list(name_val: str) -> list[str]:
            if self._export_rename_var.get():
                digits = _get_rename_digits()
                return [
                    f"{name_val}_{k:0{digits}d}{Path(self.image_files[i]).suffix}"
                    for k, i in enumerate(sel, 1)
                    if i < len(self.image_files)
                ]
            return list(src_frames)

        def _build_anim_block(name_val: str, frames: list[str]) -> dict | None:
            if not phaser_enable_var.get():
                return None
            # 帧率与重复：容错解析
            try:
                fps_val = int((phaser_fps_var.get() or "").strip() or str(base_fps))
            except ValueError:
                fps_val = base_fps
            try:
                repeat_val = int((phaser_repeat_var.get() or "").strip() or str(repeat_default))
            except ValueError:
                repeat_val = repeat_default
            atlas = (phaser_atlas_var.get() or "").strip()
            # 帧名格式：支持 {name} / {frame} / {ext}
            frame_tpl = (phaser_frame_fmt_var.get() or "{name}/{frame}.{ext}").strip()

            frames_anim: list[dict] = []
            for arcname in frames:
                # 使用 zip 中的文件名（不含目录）拆分为 {frame} 与 {ext}
                base = arcname.split("/")[-1]
                if "." in base:
                    frame_base, ext = base.rsplit(".", 1)
                else:
                    frame_base, ext = base, ""
                frame_str = (
                    frame_tpl.replace("{name}", name_val)
                    .replace("{frame}", frame_base)
                    .replace("{ext}", ext)
                )
                frames_anim.append(
                    {
                        "key": atlas,
                        "frame": frame_str,
                    }
                )
            return {
                "key": name_val,
                "frameRate": fps_val,
                "repeat": repeat_val,
                "frames": frames_anim,
            }

        def refresh_preview() -> None:
            name_val = (name_var.get() or "").strip() or default_name
            frames = _build_frames_list(name_val)
            frames_json: dict = {
                "name": name_val,
                "frames": frames,
            }
            anim_block = _build_anim_block(name_val, frames)
            if anim_block is not None:
                frames_json["anim"] = anim_block
            # meta 放在最后，包含创建时间
            frames_json["meta"] = {
                "create_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            }
            text = json.dumps(frames_json, indent=2, ensure_ascii=False)
            preview_text.configure(state="normal")
            # 保持滚动位置
            yview = preview_text.yview()
            preview_text.delete("1.0", tk.END)
            preview_text.insert("1.0", text)
            preview_text.yview_moveto(yview[0])
            preview_text.configure(state="disabled")

        # 预览联动：名称、导出选项、帧序位数、Phaser 参数变化时刷新
        name_entry.bind("<KeyRelease>", lambda _e: refresh_preview())
        rename_digits_entry.bind("<KeyRelease>", lambda _e: refresh_preview())
        gif_cb.configure(command=refresh_preview)
        fps_entry.bind("<KeyRelease>", lambda _e: refresh_preview())
        repeat_entry.bind("<KeyRelease>", lambda _e: refresh_preview())

        def _on_atlas_change(_e=None) -> None:
            self._phaser_atlas_last = phaser_atlas_var.get()
            refresh_preview()

        def _on_frame_fmt_change(_e=None) -> None:
            self._phaser_frame_fmt_last = phaser_frame_fmt_var.get() or "{name}/{frame}.{ext}"
            refresh_preview()

        atlas_entry.bind("<KeyRelease>", _on_atlas_change)
        frame_fmt_entry.bind("<KeyRelease>", _on_frame_fmt_change)

        # 底部按钮行
        btn_frame = tk.Frame(dlg)
        btn_frame.pack(side="bottom", fill="x", pady=(0, 10))
        btn_frame.columnconfigure(0, weight=1)

        def on_cancel() -> None:
            try:
                dlg.grab_release()
                dlg.destroy()
            except Exception:
                pass

        def on_export_click() -> None:
            name_val = (name_var.get() or "").strip() or default_name
            # 记录 Phaser 参数的最终选择，供下次作为默认值
            self._phaser_anim_enabled_last = phaser_enable_var.get()
            self._phaser_atlas_last = phaser_atlas_var.get()
            self._phaser_frame_fmt_last = phaser_frame_fmt_var.get() or "{name}/{frame}.{ext}"
            try:
                self._export_rename_digits_last = max(1, min(9, int((rename_digits_var.get() or "").strip() or "3")))
            except ValueError:
                self._export_rename_digits_last = 3

            # 若启用 Phaser 动画，则要求图集名称必填
            if phaser_enable_var.get() and not (phaser_atlas_var.get() or "").strip():
                messagebox.showinfo("导出", "启用 Phaser 动画定义时，请填写图集名称。", parent=dlg)
                dlg.lift()
                return

            if self._export_save_dir is not None and self._export_save_dir.is_dir():
                initial_dir = self._export_save_dir
            else:
                initial_dir = Path.home() / "Downloads"
            initial_file = f"{name_val}.zip"
            path_str = filedialog.asksaveasfilename(
                title="导出为 ZIP",
                defaultextension=".zip",
                initialdir=initial_dir,
                initialfile=initial_file,
                filetypes=[("ZIP 文件", "*.zip")],
            )
            self.root.focus_force()
            if not path_str:
                return

            path = Path(path_str)
            self._export_save_dir = path.parent
            self._export_name_last = name_val
            fps_local = max(1, int(self._fps_var.get()))
            src_frames_local = [self.image_files[i].name for i in sel if i < len(self.image_files)]
            if self._export_rename_var.get():
                digits = _get_rename_digits()
                frames_local = [
                    f"{name_val}_{k:0{digits}d}{Path(self.image_files[i]).suffix}"
                    for k, i in enumerate(sel, 1)
                    if i < len(self.image_files)
                ]
            else:
                frames_local = list(src_frames_local)

            # 关闭参数窗口，弹出导出进度窗口
            try:
                dlg.grab_release()
                dlg.destroy()
            except Exception:
                pass

            progress = tk.Toplevel(self.root)
            progress.title("导出")
            progress.resizable(False, False)
            tk.Label(progress, text="导出中，请稍候…", font=("", 12), padx=24, pady=16).pack()
            progress.transient(self.root)

            def do_export() -> None:
                err: Exception | None = None
                try:
                    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as zf:
                        for idx, i in enumerate(sel):
                            if i >= len(self.image_files):
                                continue
                            src = self.image_files[i]
                            arcname = frames_local[idx] if idx < len(frames_local) else src.name
                            zf.write(src, arcname)
                        frames_json_local: dict = {
                            "name": name_val,
                            "frames": frames_local,
                        }
                        # 根据导出时的参数生成 Phaser 动画定义（可选）
                        anim_block_local = _build_anim_block(name_val, frames_local)
                        if anim_block_local is not None:
                            frames_json_local["anim"] = anim_block_local
                        # meta 放在最后，包含创建时间
                        frames_json_local["meta"] = {
                            "create_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                        }
                        zf.writestr(
                            f"{name_val}.json",
                            json.dumps(frames_json_local, indent=2, ensure_ascii=False),
                        )
                        if self._export_gif_var.get():
                            gif_bytes = self._build_gif_from_frames(sel, fps_local, max_size=512)
                            if gif_bytes:
                                zf.writestr(f"{name_val}.gif", gif_bytes)
                except OSError as e:
                    err = e
                self.root.after(0, lambda: _export_done(progress, path, err))

            def _export_done(dialog: tk.Toplevel, out_path: Path, error: Exception | None) -> None:
                try:
                    dialog.grab_release()
                    dialog.destroy()
                except Exception:
                    pass
                self.root.focus_force()
                if error is not None:
                    messagebox.showerror("导出失败", str(error))
                    self.root.focus_force()
                    return
                msg = f"已保存到：\n{out_path}\n\n是否打开该文件？"
                if messagebox.askyesno("导出完成", msg, default="yes"):
                    self._open_path_with_system(out_path)
                self.root.focus_force()

            threading.Thread(target=do_export, daemon=True).start()

        def on_export_json_only() -> None:
            """仅保存 JSON，默认文件名 名称.json，保存路径逻辑与「导出」一致。"""
            name_val = (name_var.get() or "").strip() or default_name
            if phaser_enable_var.get() and not (phaser_atlas_var.get() or "").strip():
                messagebox.showinfo("导出", "启用 Phaser 动画定义时，请填写图集名称。", parent=dlg)
                dlg.lift()
                return
            if self._export_save_dir is not None and self._export_save_dir.is_dir():
                initial_dir = self._export_save_dir
            else:
                initial_dir = Path.home() / "Downloads"
            initial_file = f"{name_val}.json"
            path_str = filedialog.asksaveasfilename(
                title="导出为 JSON",
                defaultextension=".json",
                initialdir=initial_dir,
                initialfile=initial_file,
                filetypes=[("JSON 文件", "*.json"), ("所有文件", "*.*")],
            )
            self.root.focus_force()
            if not path_str:
                return
            path = Path(path_str)
            self._export_save_dir = path.parent
            self._export_name_last = name_val
            try:
                content = preview_text.get("1.0", tk.END)
                path.write_text(content, encoding="utf-8")
            except OSError as e:
                messagebox.showerror("导出失败", str(e))
                return
            msg = f"已保存到：\n{path}\n\n是否打开该文件？"
            if messagebox.askyesno("导出完成", msg, default="yes"):
                self._open_path_with_system(path)
            dlg.focus_force()

        # 从左到右：取消、导出（仅数据）、导出
        btn_export = tk.Button(btn_frame, text="导出", width=10, command=on_export_click)
        btn_export.pack(side="right", padx=(0, 8))
        tk.Button(btn_frame, text="导出（仅数据）", width=12, command=on_export_json_only).pack(side="right", padx=(0, 8))
        tk.Button(btn_frame, text="取消", width=10, command=on_cancel).pack(side="right", padx=(0, 8))

        dlg.bind("<Return>", lambda e: on_export_click())
        dlg.bind("<Escape>", lambda e: on_cancel())

        # 初始预览
        refresh_preview()

    def _show_merge_anims_dialog(self) -> None:
        """合并JSON：左侧待合并 JSON 路径列表与操作按钮，右侧合并后 JSON 预览，底部取消/导出。"""
        dlg = tk.Toplevel(self.root)
        dlg.title("合并JSON")
        dlg.resizable(True, True)
        dlg.transient(self.root)
        dlg.grab_set()

        top_frame = tk.Frame(dlg)
        top_frame.pack(side="top", fill="both", expand=True, padx=10, pady=10)

        left_frame = tk.Frame(top_frame)
        left_frame.pack(side="left", fill="both", expand=True, padx=(0, 8))

        extract_node_var = tk.StringVar(value="anim")
        extract_row = tk.Frame(left_frame)
        extract_row.pack(anchor="w", pady=(0, 4))
        tk.Label(extract_row, text="待合并节点").pack(side="left")
        extract_node_entry = tk.Entry(extract_row, textvariable=extract_node_var, width=16)
        extract_node_entry.pack(side="left", padx=(4, 0))

        merge_list_title_var = tk.StringVar(value="待合并的 JSON 文件 (0/0有效)")
        tk.Label(left_frame, textvariable=merge_list_title_var).pack(anchor="w")
        list_container = tk.Frame(left_frame)
        list_container.pack(side="top", fill="both", expand=True)
        scrollbar = ttk.Scrollbar(list_container)
        scrollbar.pack(side="right", fill="y")
        # 使用 Treeview 单列，以便通过 tag 在选中时仍保留绿/红前景色
        merge_tree = ttk.Treeview(
            list_container,
            columns=("path",),
            show="tree",
            selectmode="extended",
            height=16,
            yscrollcommand=scrollbar.set,
        )
        merge_tree.column("#0", stretch=True, minwidth=80)
        merge_tree.pack(side="left", fill="both", expand=True)
        scrollbar.config(command=merge_tree.yview)

        def _resize_tree_column(_e: tk.Event | None = None) -> None:
            w = list_container.winfo_width()
            if w > 1:
                merge_tree.column("#0", width=max(80, w - scrollbar.winfo_width() - 4))

        list_container.bind("<Configure>", _resize_tree_column)
        dlg.after(50, _resize_tree_column)
        merge_tree.tag_configure("valid", foreground="green")
        merge_tree.tag_configure("invalid", foreground="red")

        btn_row = tk.Frame(left_frame)
        btn_row.pack(side="top", fill="x", pady=(6, 0))
        _MAX_MERGE_JSON = 100

        def _normalize_path(s: str) -> str:
            try:
                return str(Path(s).resolve())
            except Exception:
                return s

        def _tree_children() -> list[str]:
            return list(merge_tree.get_children(""))

        def _existing_paths_set() -> set[str]:
            return {
                _normalize_path(merge_tree.item(iid, "text"))
                for iid in _tree_children()
            }

        def _get_extract_key() -> str:
            return (extract_node_var.get() or "").strip() or "anim"

        def _is_valid_anim_json(path_str: str) -> bool:
            key = _get_extract_key()
            if not key:
                return False
            try:
                with open(path_str, "r", encoding="utf-8") as f:
                    data = json.load(f)
                return isinstance(data, dict) and key in data
            except Exception:
                return False

        def _insert_path(path_str: str) -> None:
            tag = "valid" if _is_valid_anim_json(path_str) else "invalid"
            merge_tree.insert("", tk.END, text=path_str, tags=(tag,))

        def _sort_merge_list_by_path() -> None:
            """按绝对路径升序重排列表，并恢复当前选中项。"""
            selected_paths = {merge_tree.item(iid, "text") for iid in merge_tree.selection()}
            items: list[tuple[str, str]] = []
            for iid in _tree_children():
                path_str = merge_tree.item(iid, "text")
                tags = merge_tree.item(iid, "tags")
                tag = tags[0] if tags else "invalid"
                items.append((path_str, tag))
            for iid in _tree_children():
                merge_tree.delete(iid)
            items.sort(key=lambda x: _normalize_path(x[0]))
            for path_str, tag in items:
                merge_tree.insert("", tk.END, text=path_str, tags=(tag,))
            for iid in _tree_children():
                if merge_tree.item(iid, "text") in selected_paths:
                    merge_tree.selection_add(iid)

        def _update_list_title() -> None:
            total = len(_tree_children())
            valid = sum(
                1
                for iid in _tree_children()
                if _is_valid_anim_json(merge_tree.item(iid, "text"))
            )
            merge_list_title_var.set(f"待合并的 JSON 文件 ({valid}/{total}有效)")

        def scan_folder() -> None:
            if self._merge_export_dir is not None and self._merge_export_dir.is_dir():
                initial_dir = self._merge_export_dir
            else:
                initial_dir = Path.home() / "Downloads"
            folder = filedialog.askdirectory(
                title="选择文件夹（将递归扫描其下所有 .json）",
                initialdir=initial_dir,
            )
            if not folder:
                return
            dlg.focus_force()
            self._merge_export_dir = Path(folder)
            base = Path(folder)
            try:
                all_jsons = [p for p in base.rglob("*.json") if p.is_file()]
            except Exception:
                all_jsons = []
            if len(all_jsons) > _MAX_MERGE_JSON:
                messagebox.showinfo(
                    "合并JSON",
                    f"该文件夹下共有 {len(all_jsons)} 个 JSON 文件，超过上限 {_MAX_MERGE_JSON} 个，已停止添加。",
                    parent=dlg,
                )
                return
            existing = _existing_paths_set()
            start_idx = len(_tree_children())
            for p in all_jsons:
                if len(_tree_children()) >= _MAX_MERGE_JSON:
                    break
                norm = str(p.resolve())
                if norm in existing:
                    continue
                existing.add(norm)
                _insert_path(norm)
            children = _tree_children()
            end_idx = len(children)
            if end_idx > start_idx:
                merge_tree.selection_set(*children[start_idx:end_idx])
            _sort_merge_list_by_path()
            _update_list_title()
            refresh_merge_preview()

        def add_file() -> None:
            if self._merge_export_dir is not None and self._merge_export_dir.is_dir():
                initial_dir = self._merge_export_dir
            else:
                initial_dir = Path.home() / "Downloads"
            path_strs = filedialog.askopenfilenames(
                title="选择 JSON 文件（可多选）",
                initialdir=initial_dir,
                filetypes=[("JSON 文件", "*.json"), ("所有文件", "*.*")],
            )
            if not path_strs:
                return
            dlg.focus_force()
            self._merge_export_dir = Path(path_strs[0]).parent
            existing = _existing_paths_set()
            start_idx = len(_tree_children())
            for path_str in path_strs:
                if len(_tree_children()) >= _MAX_MERGE_JSON:
                    messagebox.showinfo("合并JSON", f"已达上限 {_MAX_MERGE_JSON} 个文件，未继续添加。", parent=dlg)
                    break
                norm = _normalize_path(path_str)
                if norm in existing:
                    continue
                existing.add(norm)
                _insert_path(norm)
            children = _tree_children()
            end_idx = len(children)
            if end_idx > start_idx:
                merge_tree.selection_set(*children[start_idx:end_idx])
            _sort_merge_list_by_path()
            _update_list_title()
            refresh_merge_preview()

        def select_all_list() -> None:
            children = _tree_children()
            if children:
                merge_tree.selection_set(*children)
            refresh_merge_preview()

        def select_valid_only() -> None:
            """仅选中合法（含 anim 节点）的 JSON 项。"""
            merge_tree.selection_remove(*merge_tree.selection())
            for iid in _tree_children():
                if _is_valid_anim_json(merge_tree.item(iid, "text")):
                    merge_tree.selection_add(iid)
            refresh_merge_preview()

        def clear_selection() -> None:
            """清空选中（不删除列表项）。"""
            merge_tree.selection_remove(*merge_tree.selection())
            refresh_merge_preview()

        def _on_merge_drop(event) -> None:
            """拖拽：文件夹递归加入其下所有 .json；文件若为 .json 则加入列表。"""
            if not _DND_AVAILABLE or not getattr(event, "data", None):
                return
            try:
                raw_list = self.root.tk.splitlist(event.data)
            except Exception:
                return
            existing = _existing_paths_set()
            new_iids: list[str] = []
            for raw in raw_list:
                s = str(raw).strip()
                if s.startswith("file://"):
                    s = unquote(s[7:].lstrip("/"))
                p = Path(s)
                if p.is_dir():
                    try:
                        all_jsons = [f for f in p.rglob("*.json") if f.is_file()]
                    except Exception:
                        all_jsons = []
                    for f in all_jsons:
                        if len(_tree_children()) >= _MAX_MERGE_JSON:
                            break
                        norm = str(f.resolve())
                        if norm in existing:
                            continue
                        existing.add(norm)
                        _insert_path(norm)
                        new_iids.append(_tree_children()[-1])
                elif p.is_file() and p.suffix.lower() == ".json":
                    if len(_tree_children()) >= _MAX_MERGE_JSON:
                        continue
                    norm = _normalize_path(str(p))
                    if norm in existing:
                        continue
                    existing.add(norm)
                    _insert_path(norm)
                    new_iids.append(_tree_children()[-1])
            if new_iids:
                merge_tree.selection_set(*new_iids)
                _sort_merge_list_by_path()
                _update_list_title()
                refresh_merge_preview()

        if _DND_AVAILABLE:
            try:
                dlg.drop_target_register(DND_FILES)
                dlg.dnd_bind("<<Drop>>", _on_merge_drop)
            except Exception:
                pass

        tk.Button(btn_row, text="扫描文件夹", command=scan_folder, width=10).pack(side="left", padx=(0, 4))
        tk.Button(btn_row, text="添加", command=add_file, width=8).pack(side="left", padx=(0, 4))
        ttk.Separator(btn_row, orient="vertical").pack(side="left", fill="y", padx=4, pady=2)
        tk.Button(btn_row, text="全选", command=select_all_list, width=6).pack(side="left", padx=(0, 4))
        tk.Button(btn_row, text="仅有效", command=select_valid_only, width=6).pack(side="left", padx=(0, 4))
        tk.Button(btn_row, text="清空", command=clear_selection, width=6).pack(side="left")

        right_frame = tk.Frame(top_frame)
        right_frame.pack(side="right", fill="both", expand=True)
        merge_node_var = tk.StringVar(value="anims")
        merge_node_row = tk.Frame(right_frame)
        merge_node_row.pack(anchor="w", pady=(0, 4))
        tk.Label(merge_node_row, text="合并节点").pack(side="left")
        merge_node_entry = tk.Entry(merge_node_row, textvariable=merge_node_var, width=16)
        merge_node_entry.pack(side="left", padx=(4, 0))
        merge_preview_title_var = tk.StringVar(value="合并后 JSON 预览 (0)")
        merge_preview_title_row = tk.Frame(right_frame)
        merge_preview_title_row.pack(fill="x")
        tk.Label(merge_preview_title_row, textvariable=merge_preview_title_var).pack(side="left")
        tk.Frame(merge_preview_title_row).pack(side="left", fill="x", expand=True)

        def _copy_merge_preview() -> None:
            try:
                content = merge_preview_text.get("1.0", tk.END)
                self.root.clipboard_clear()
                self.root.clipboard_append(content)
            except Exception:
                pass

        tk.Button(merge_preview_title_row, text="复制", width=6, command=_copy_merge_preview).pack(side="right", padx=(4, 0))
        merge_preview_text = tk.Text(
            right_frame,
            width=50,
            height=18,
            font=("Courier", 9),
            wrap="none",
        )
        merge_preview_text.pack(side="top", fill="both", expand=True)
        merge_preview_text.configure(state="disabled")

        def refresh_merge_preview() -> None:
            key = _get_extract_key()
            merge_key = (merge_node_var.get() or "").strip() or "anims"
            collected: list = []
            for iid in merge_tree.selection():
                try:
                    path_str = merge_tree.item(iid, "text")
                    with open(path_str, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    if isinstance(data, dict) and key and key in data:
                        collected.append(data[key])
                except Exception:
                    pass
            merge_preview_title_var.set(f"合并后 JSON 预览 ({len(collected)})")
            out = {
                merge_key: collected,
                "meta": {
                    "create_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                },
            }
            text = json.dumps(out, indent=2, ensure_ascii=False)
            merge_preview_text.configure(state="normal")
            yview = merge_preview_text.yview()
            merge_preview_text.delete("1.0", tk.END)
            merge_preview_text.insert("1.0", text)
            merge_preview_text.yview_moveto(yview[0])
            merge_preview_text.configure(state="disabled")

        merge_tree.bind("<<TreeviewSelect>>", lambda e: refresh_merge_preview())

        def _on_extract_node_change() -> None:
            for iid in _tree_children():
                path_str = merge_tree.item(iid, "text")
                tag = "valid" if _is_valid_anim_json(path_str) else "invalid"
                merge_tree.item(iid, tags=(tag,))
            _update_list_title()
            refresh_merge_preview()

        extract_node_entry.bind("<KeyRelease>", lambda e: _on_extract_node_change())
        merge_node_entry.bind("<KeyRelease>", lambda e: refresh_merge_preview())

        def _on_merge_list_double_click(event: tk.Event) -> None:
            iid = merge_tree.identify_row(event.y)
            if not iid:
                return
            path_str = merge_tree.item(iid, "text")
            if not path_str or not Path(path_str).is_file():
                return
            self._open_path_with_system(path_str)

        merge_tree.bind("<Double-1>", _on_merge_list_double_click)

        btn_frame = tk.Frame(dlg)
        btn_frame.pack(side="bottom", fill="x", pady=(0, 10))
        btn_frame.columnconfigure(0, weight=1)

        def on_cancel() -> None:
            try:
                dlg.grab_release()
                dlg.destroy()
            except Exception:
                pass

        def on_export() -> None:
            if self._merge_export_dir is not None and self._merge_export_dir.is_dir():
                initial_dir = self._merge_export_dir
            else:
                initial_dir = Path.home() / "Downloads"
            path_str = filedialog.asksaveasfilename(
                title="保存合并后的 JSON",
                defaultextension=".json",
                initialdir=initial_dir,
                initialfile="anims.json",
                filetypes=[("JSON 文件", "*.json"), ("所有文件", "*.*")],
            )
            if not path_str:
                return
            dlg.focus_force()
            out_path = Path(path_str)
            self._merge_export_dir = out_path.parent
            key = _get_extract_key()
            merge_key = (merge_node_var.get() or "").strip() or "anims"
            collected = []
            for iid in merge_tree.selection():
                path_str = merge_tree.item(iid, "text")
                try:
                    with open(path_str, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    if isinstance(data, dict) and key and key in data:
                        collected.append(data[key])
                except Exception:
                    pass
            try:
                out_path.write_text(
                    json.dumps(
                        {
                            merge_key: collected,
                            "meta": {
                                "create_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                            },
                        },
                        indent=2,
                        ensure_ascii=False,
                    ),
                    encoding="utf-8",
                )
            except OSError as e:
                messagebox.showerror("合并JSON", f"保存失败：{e}", parent=dlg)
                return
            msg = f"导出成功。\n\n已保存到：\n{out_path}\n\n是否打开该文件？"
            if messagebox.askyesno("合并JSON", msg, default="yes", parent=dlg):
                self._open_path_with_system(out_path)
            dlg.focus_force()

        tk.Button(btn_frame, text="导出", width=10, command=on_export).pack(side="right", padx=(0, 8))
        tk.Button(btn_frame, text="取消", width=10, command=on_cancel).pack(side="right", padx=(0, 8))
        dlg.bind("<Return>", lambda e: on_export())
        dlg.bind("<Escape>", lambda e: on_cancel())

        refresh_merge_preview()

    def _stop_animation(self) -> None:
        if self._animation_after_id is not None:
            self.root.after_cancel(self._animation_after_id)
            self._animation_after_id = None
        self._animation_indices = []
        self._animation_index = 0

    def _get_delay_ms(self) -> int:
        fps = max(1, int(self._fps_var.get()))
        return max(1, 1000 // fps)

    def _set_playing(self, playing: bool) -> None:
        self._is_playing.set(playing)
        self._play_button.config(text="⏸" if playing else "▶")
        if not playing:
            # 暂停：停止后续 schedule，但保留当前帧显示
            if self._animation_after_id is not None:
                self.root.after_cancel(self._animation_after_id)
                self._animation_after_id = None
        self._update_next_frame_button_state()

    def _update_next_frame_button_state(self) -> None:
        """「>」按钮：仅暂停且有选中帧时可用。"""
        enabled = not self._is_playing.get() and bool(self._animation_indices)
        self._btn_next_frame.config(state="normal" if enabled else "disabled")

    def _on_next_frame(self) -> None:
        """暂停时点击「>」或按向右键：当前帧 +1（到末帧后从 0 继续），并刷新显示。"""
        if not self._animation_indices or self._is_playing.get():
            return
        self._animation_index = (self._animation_index + 1) % len(self._animation_indices)
        self._show_current_frame()

    def _on_prev_frame(self) -> None:
        """暂停时按向左键：当前帧 -1（到首帧后从末帧继续），并刷新显示。"""
        if not self._animation_indices or self._is_playing.get():
            return
        self._animation_index = (self._animation_index - 1) % len(self._animation_indices)
        self._show_current_frame()

    def _select_all(self) -> None:
        if not self.image_files:
            return
        self._listbox.selection_set(0, tk.END)
        self._sync_selection_to_preview()

    def _invert_selection(self) -> None:
        n = self._listbox.size()
        if n == 0:
            return
        current = set(self._listbox.curselection())
        self._listbox.selection_clear(0, tk.END)
        for i in range(n):
            if i not in current:
                self._listbox.selection_set(i)
        self._sync_selection_to_preview()

    def _select_none(self) -> None:
        self._listbox.selection_clear(0, tk.END)
        self._sync_selection_to_preview()

    def _select_odd(self) -> None:
        n = self._listbox.size()
        if n == 0:
            return
        self._listbox.selection_clear(0, tk.END)
        for i in range(0, n, 2):
            self._listbox.selection_set(i)
        self._sync_selection_to_preview()

    def _select_even(self) -> None:
        n = self._listbox.size()
        if n == 0:
            return
        self._listbox.selection_clear(0, tk.END)
        for i in range(1, n, 2):
            self._listbox.selection_set(i)
        self._sync_selection_to_preview()

    def _select_random(self) -> None:
        n = self._listbox.size()
        if n == 0:
            return
        try:
            k = max(1, min(n, int(self._random_count_var.get().strip() or "30")))
        except ValueError:
            k = min(30, n)
        indices = random.sample(range(n), k)
        self._listbox.selection_clear(0, tk.END)
        for i in indices:
            self._listbox.selection_set(i)
        self._sync_selection_to_preview()

    def _select_by_range(self) -> None:
        """从第 a 帧起，每 b 帧共选 c 帧。a/b/c 为 1 基、正整数，自动裁剪到帧数范围内。"""
        n = self._listbox.size()
        if n == 0:
            return
        try:
            a = int((self._range_start_var.get() or "1").strip())
        except ValueError:
            a = 1
        try:
            b = int((self._range_step_var.get() or "1").strip())
        except ValueError:
            b = 1
        try:
            c = int((self._range_count_var.get() or "30").strip())
        except ValueError:
            c = 30

        a = max(1, a)
        b = max(1, b)
        c = max(1, c)

        start_idx = a - 1
        if start_idx >= n:
            # 起始帧超出范围则不做任何选择
            return

        indices: list[int] = []
        idx = start_idx
        while len(indices) < c and idx < n:
            indices.append(idx)
            idx += b

        if not indices:
            return

        self._listbox.selection_clear(0, tk.END)
        for i in indices:
            self._listbox.selection_set(i)
        self._sync_selection_to_preview()

    def _select_roll_up(self) -> None:
        n = self._listbox.size()
        if n == 0:
            return
        sel = sorted(int(i) for i in self._listbox.curselection())
        if not sel or min(sel) <= 0:
            return
        new_indices = sorted(set(max(0, i - 1) for i in sel))
        self._listbox.selection_clear(0, tk.END)
        for i in new_indices:
            self._listbox.selection_set(i)
        self._sync_selection_to_preview()

    def _select_roll_down(self) -> None:
        n = self._listbox.size()
        if n == 0:
            return
        sel = sorted(int(i) for i in self._listbox.curselection())
        if not sel or max(sel) >= n - 1:
            return
        new_indices = sorted(set(min(n - 1, i + 1) for i in sel))
        self._listbox.selection_clear(0, tk.END)
        for i in new_indices:
            self._listbox.selection_set(i)
        self._sync_selection_to_preview()

    def _on_listbox_click(self, event: tk.Event) -> None:
        """无修饰键时按「单击追加」规则处理；Shift/Command(Ctrl) 时交还默认行为。"""
        # 保留 Shift 连续选中、Command(Ctrl) 单选切换：有修饰键则不拦截
        state = getattr(event, "state", 0) or 0
        if state & 0x01:   # Shift
            return
        if state & 0x04:   # Control (Windows/Linux Ctrl)
            return
        if state & 0x08:   # Mod1 (macOS Command / Alt)
            return
        if state & 0x40:   # Mod4 (部分系统 Command)
            return
        idx = self._listbox.nearest(event.y)
        n = self._listbox.size()
        if idx < 0 or idx >= n:
            return "break"
        if (self._click_mode_var.get() or "").strip() == "单击追加":
            current = set(int(i) for i in self._listbox.curselection())
            # 单击追加：点击未选项 -> 加入；点击已选项 -> 取消该项（其余保持）
            if idx in current:
                current.remove(idx)
            else:
                current.add(idx)
            new_selection = sorted(current)
            self._listbox.selection_clear(0, tk.END)
            for i in new_selection:
                self._listbox.selection_set(i)
        else:
            self._listbox.selection_clear(0, tk.END)
            self._listbox.selection_set(idx)
        self._sync_selection_to_preview()
        return "break"

    def _on_list_select(self, event: tk.Event) -> None:
        self._sync_selection_to_preview()

    def _sync_selection_to_preview(self) -> None:
        """根据当前列表选中项更新状态栏与帧动画（程序化修改选中时也需显式调用）。"""
        sel = self._listbox.curselection()
        selected_indices = sorted(int(i) for i in sel)
        self._selected_indices = selected_indices
        total = len(self.image_files)
        self._update_status_bar(total, len(selected_indices))

        self._stop_animation()
        if not selected_indices or not self.image_files:
            self._preview_label.config(image="", text="请从左侧列表选择帧（可多选）")
            self._preview_photo = None
            self._frame_info_var.set("")
            self._update_headtail_view()
            return

        self._animation_indices = [i for i in selected_indices if i < total]
        if not self._animation_indices:
            self._update_headtail_view()
            self._update_next_frame_button_state()
            return
        self._animation_index = 0
        # 选择变化时总是更新到第一帧；仅在「动画预览」tab 且播放中时调度
        self._show_current_frame()
        self._update_headtail_view()
        self._update_next_frame_button_state()
        if self._is_playing.get() and self._is_preview_tab_active():
            self._schedule_next_tick()

    def _show_current_frame(self) -> None:
        if not self._animation_indices or not self.image_files:
            return
        idx = self._animation_indices[self._animation_index]
        path = self.image_files[idx]
        try:
            img = Image.open(path)
            mode = (self._zoom_mode_var.get() or "fit").lower()
            if mode == "fit":
                # 根据预览区域大小等比缩放
                w = max(1, self._preview_label.winfo_width())
                h = max(1, self._preview_label.winfo_height())
                # 初始布局阶段宽高可能很小，给一个合理的下限
                if w < 50 or h < 50:
                    w, h = 800, 600
                img.thumbnail((w, h), Image.Resampling.LANCZOS)
            elif mode == "x0.1":
                new_w = max(1, int(img.width * 0.1))
                new_h = max(1, int(img.height * 0.1))
                img = img.resize((new_w, new_h), Image.Resampling.LANCZOS)
            elif mode == "x0.3":
                new_w = max(1, int(img.width * 0.3))
                new_h = max(1, int(img.height * 0.3))
                img = img.resize((new_w, new_h), Image.Resampling.LANCZOS)
            elif mode == "x0.5":
                new_w = max(1, int(img.width * 0.5))
                new_h = max(1, int(img.height * 0.5))
                img = img.resize((new_w, new_h), Image.Resampling.LANCZOS)
            elif mode == "x2":
                new_w = max(1, img.width * 2)
                new_h = max(1, img.height * 2)
                # 避免极端大图导致卡顿，简单限制一下最大尺寸
                max_dim = 4096
                new_w = min(new_w, max_dim)
                new_h = min(new_h, max_dim)
                img = img.resize((new_w, new_h), Image.Resampling.LANCZOS)
            # mode == "x1" 时按原始尺寸显示（可能会超出预览区域，由 Tk 自行裁剪）

            # 色彩：仅影响预览，不改变原文件
            color_mode = (self._color_mode_var.get() or "原图").strip()
            if color_mode == "灰度":
                img = img.convert("L")
            elif color_mode == "黑白":
                gray = img.convert("L")
                # 前景白、背景黑：灰度 >= 10 为白，否则为黑
                img = gray.point(lambda x: 255 if x >= 10 else 0, mode="L")

            # 轮廓：绘制红色边框与水平/垂直中心线（L 模式先转 RGB 以便显示红色）
            if self._ruler_var.get():
                if img.mode == "L":
                    img = img.convert("RGB")
                draw = ImageDraw.Draw(img)
                w_img, h_img = img.width, img.height
                # 外边框
                draw.rectangle(
                    [(0, 0), (w_img - 1, h_img - 1)],
                    outline="red",
                    width=1,
                )
                # 中心十字线
                cx = w_img // 2
                cy = h_img // 2
                draw.line([(cx, 0), (cx, h_img - 1)], fill="red", width=1)
                draw.line([(0, cy), (w_img - 1, cy)], fill="red", width=1)

            # 背景为「图片」时：将当前帧合成到背景图上
            bg = (self._bg_var.get() or "").strip()
            if bg == "图片" and self._bg_image_path and self._bg_image_path.is_file():
                try:
                    bw, bh = img.width, img.height
                    cache = self._bg_image_cache
                    if cache is not None and cache[0] == bw and cache[1] == bh:
                        back = cache[2]
                    else:
                        with Image.open(self._bg_image_path) as bim:
                            back = bim.convert("RGB").resize((bw, bh), Image.Resampling.LANCZOS)
                        back = back.convert("RGBA")
                        self._bg_image_cache = (bw, bh, back)
                    frame_rgba = img.convert("RGBA") if img.mode != "RGBA" else img
                    img = Image.alpha_composite(back, frame_rgba).convert("RGB")
                except Exception:
                    pass

            self._preview_photo = ImageTk.PhotoImage(img)
            self._preview_label.config(image=self._preview_photo, text="")

            # 更新顶部帧信息：当前帧：n/m name wxh
            total_play = len(self._animation_indices)
            current_pos = self._animation_index + 1
            current_str = f"{current_pos:02d}"
            total_str = f"{total_play:02d}"
            w, h = (0, 0)
            if 0 <= idx < len(self._image_sizes):
                w, h = self._image_sizes[idx]
            else:
                try:
                    # 理论上不会走到这里，只作兜底
                    w, h = int(img.width), int(img.height)
                except Exception:
                    w, h = (0, 0)
            self._frame_info_var.set(f"当前帧：{current_str}/{total_str}  |  {path.name}  |  {w}x{h}")
        except Exception:
            self._preview_label.config(image="", text=f"无法加载: {path.name}")

    def _schedule_next_tick(self) -> None:
        if self._animation_after_id is not None:
            self.root.after_cancel(self._animation_after_id)
            self._animation_after_id = None
        self._animation_after_id = self.root.after(self._get_delay_ms(), self._tick_animation)

    def _is_preview_tab_active(self) -> bool:
        try:
            return self._right_notebook.index(self._right_notebook.select()) == self._preview_tab_index
        except Exception:
            return True

    def _tick_animation(self) -> None:
        """每帧回调：显示当前帧并调度下一帧，不阻塞 UI。仅在「动画预览」tab 激活时继续播放。"""
        self._animation_after_id = None
        if not self._is_playing.get():
            return
        if not self._animation_indices or not self.image_files:
            return
        if not self._is_preview_tab_active():
            return

        # 显示当前帧
        self._show_current_frame()

        # 实际帧率：用相邻两帧时间间隔的平均值
        now = time.perf_counter()
        if self._last_tick_time is not None:
            interval = now - self._last_tick_time
            if 0.001 <= interval < 5.0:  # 忽略异常间隔（如 tab 切换导致的长时间间隔）
                self._frame_interval_history.append(interval)
        self._last_tick_time = now
        if self._frame_interval_history:
            avg_interval = sum(self._frame_interval_history) / len(self._frame_interval_history)
            actual_fps = 1.0 / avg_interval
            self._preview_fps_var.set(f"预览帧率：{actual_fps:.0f}")
        else:
            self._preview_fps_var.set("预览帧率：—")

        # 计算下一帧位置（一次/循环）
        last_index = len(self._animation_indices) - 1
        if self._play_mode_var.get() == "once" and self._animation_index >= last_index:
            # 播放一次到末尾后停止
            self._set_playing(False)
            return

        self._animation_index = (self._animation_index + 1) % len(self._animation_indices)
        self._schedule_next_tick()

    def _start_playback(self) -> None:
        """开始/恢复播放；若处于一次播放的末帧，则从头重新播放。"""
        if not self._animation_indices:
            return
        self._last_tick_time = None
        self._frame_interval_history.clear()
        self._preview_fps_var.set("预览帧率：—")
        last_index = len(self._animation_indices) - 1
        if self._play_mode_var.get() == "once" and self._animation_index >= last_index:
            self._animation_index = 0
        self._set_playing(True)
        self._show_current_frame()
        if self._is_preview_tab_active():
            self._schedule_next_tick()

    def _toggle_play(self) -> None:
        if not self._animation_indices:
            return
        if self._is_playing.get():
            self._set_playing(False)
            return
        self._start_playback()

    def _on_fps_change(self, _value: str) -> None:
        # 调速：播放中则按新 fps 重新 schedule
        target = self._fps_var.get()
        self._fps_label_var.set(f"帧率：{target}")
        # 帧率变化时，更新底部栏中的帧率与时长信息
        total = len(self.image_files)
        selected_count = len(self._listbox.curselection())
        self._update_status_bar(total, selected_count)
        if self._is_playing.get() and self._animation_indices and self._is_preview_tab_active():
            self._schedule_next_tick()

    def _on_zoom_change(self, _event: tk.Event) -> None:
        value = self._zoom_combo.get()
        # 下拉展示文本与内部存储映射
        if value == "适应":
            self._zoom_mode_var.set("fit")
        elif value == "x0.1":
            self._zoom_mode_var.set("x0.1")
        elif value == "x0.3":
            self._zoom_mode_var.set("x0.3")
        elif value == "x0.5":
            self._zoom_mode_var.set("x0.5")
        elif value == "x1":
            self._zoom_mode_var.set("x1")
        elif value == "x2":
            self._zoom_mode_var.set("x2")
        # 模式变化时，只需重绘当前帧，不改变播放状态
        self._show_current_frame()

    def _on_ruler_toggle(self) -> None:
        # 开关轮廓时，重绘当前帧即可
        if self._animation_indices:
            self._show_current_frame()

    def _on_play_mode_combo_change(self) -> None:
        """播放模式下拉框：循环 -> loop，单次 -> once；切换时触发播放。"""
        val = (self._play_mode_combo.get() or "").strip()
        self._play_mode_var.set("loop" if val == "循环" else "once")
        if not self._is_playing.get() and self._animation_indices:
            self._start_playback()

    def _on_color_mode_change(self, _event: tk.Event) -> None:
        if self._animation_indices:
            self._show_current_frame()

    def _on_bg_change(self, _event: tk.Event) -> None:
        bg = self._bg_var.get()
        if bg == "图片":
            path = filedialog.askopenfilename(
                title="选择背景图片",
                filetypes=[
                    ("图片", " ".join(f"*{e}" for e in IMAGE_EXTENSIONS)),
                    ("所有文件", "*.*"),
                ],
            )
            if not path:
                self._bg_var.set("透明")
                self._bg_image_path = None
                self._bg_image_cache = None
                self._bg_combo.set("透明")
                bg = "透明"
            else:
                self._bg_image_path = Path(path)
                self._bg_image_cache = None
            if self._animation_indices:
                self._show_current_frame()
        color_map = {"透明": "#ddd", "黑": "#000000", "白": "#FFFFFF", "粉": "#FFB6C1", "图片": "#ddd"}
        self._preview_label.config(bg=color_map.get(bg, "#ddd"))

    def _on_preview_resize(self, _event: tk.Event) -> None:
        # Fit 模式下窗口尺寸变化时，自适应刷新当前帧
        if (self._zoom_mode_var.get() or "fit").lower() == "fit" and self._animation_indices:
            self._show_current_frame()

    def _on_headtail_resize(self, _event: tk.Event) -> None:
        # 首尾帧预览区域变化时刷新（fit）
        if self._selected_indices:
            self._show_headtail_frame()

    def _on_headtail_mode_change(self, _event: tk.Event) -> None:
        self._show_headtail_frame()

    def _update_headtail_view(self) -> None:
        if not getattr(self, "_headtail_info_var", None):
            return
        if not self._selected_indices or not self.image_files:
            self._headtail_info_var.set("")
            if hasattr(self, "_headtail_preview_label"):
                self._headtail_preview_label.config(image="", text="请选择帧")
            self._headtail_photo = None
            return
        i1 = self._selected_indices[0]
        i2 = self._selected_indices[-1]
        n1 = self.image_files[i1].name if i1 < len(self.image_files) else ""
        n2 = self.image_files[i2].name if i2 < len(self.image_files) else ""
        self._headtail_info_var.set(f"首帧({i1 + 1})：{n1}  ｜  尾帧({i2 + 1})：{n2}")
        self._show_headtail_frame()

    def _show_headtail_frame(self) -> None:
        if not hasattr(self, "_headtail_preview_label"):
            return
        if not self._selected_indices or not self.image_files:
            self._headtail_preview_label.config(image="", text="请选择帧")
            self._headtail_photo = None
            return
        i_head = self._selected_indices[0]
        i_tail = self._selected_indices[-1]
        if i_head >= len(self.image_files) or i_tail >= len(self.image_files):
            return
        path_a = self.image_files[i_head]
        path_b = self.image_files[i_tail]
        try:
            with Image.open(path_a) as im_a, Image.open(path_b) as im_b:
                mode = (self._headtail_mode_var.get() or "差值").strip()
                if mode == "差值":
                    # 参考动画预览「黑白」：先灰度、二值化，再异或（差异部分为白）
                    a = im_a.convert("L").point(lambda x: 255 if x >= 10 else 0, mode="L")
                    b = im_b.convert("L").point(lambda x: 255 if x >= 10 else 0, mode="L")
                    if b.size != a.size:
                        b = b.resize(a.size, Image.Resampling.NEAREST)
                    a1 = a.point(lambda x: 1 if x else 0, mode="1")
                    b1 = b.point(lambda x: 1 if x else 0, mode="1")
                    img = ImageChops.logical_xor(a1, b1).point(lambda x: 255 if x else 0, mode="L")
                else:
                    # 叠加：两张图 50% 透明度叠加
                    a = im_a.convert("RGBA")
                    b = im_b.convert("RGBA")
                    if b.size != a.size:
                        b = b.resize(a.size, Image.Resampling.LANCZOS)
                    img = Image.blend(a, b, 0.5)

            w = max(1, self._headtail_preview_label.winfo_width())
            h = max(1, self._headtail_preview_label.winfo_height())
            if w < 50 or h < 50:
                w, h = 800, 600
            img.thumbnail((w, h), Image.Resampling.LANCZOS)
            self._headtail_photo = ImageTk.PhotoImage(img)
            self._headtail_preview_label.config(image=self._headtail_photo, text="")
        except Exception:
            self._headtail_preview_label.config(image="", text="无法生成预览")
            self._headtail_photo = None

    def run(self) -> None:
        self.root.mainloop()
