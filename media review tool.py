import sys
import os
import json
import hashlib

# Reduce noisy Qt filesystem watcher warnings for unavailable/removable drives.
os.environ.setdefault("QT_LOGGING_RULES", "qt.core.filesystemwatcher.warning=false")

# Must run before 'import vlc' so python-vlc can locate libvlc.dll when frozen
if getattr(sys, 'frozen', False) and hasattr(sys, '_MEIPASS'):
    _base = sys._MEIPASS
    if hasattr(os, 'add_dll_directory'):
        os.add_dll_directory(_base)
    os.environ.setdefault('VLC_PLUGIN_PATH', os.path.join(_base, 'plugins'))
    os.environ.setdefault('PYTHON_VLC_LIB_PATH', os.path.join(_base, 'libvlc.dll'))

import subprocess
import shutil
import logging
import ctypes
from datetime import datetime

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QLabel, QPushButton,
    QFileDialog, QTreeWidget, QTreeWidgetItem, QTableWidget,
    QTableWidgetItem, QProgressBar, QSlider, QHBoxLayout,
    QVBoxLayout, QMessageBox, QSplitter, QAbstractItemView, QSizePolicy,
    QHeaderView, QCheckBox, QSpinBox, QDoubleSpinBox,
    QComboBox, QListView, QTreeView, QStyledItemDelegate
)
from PySide6.QtCore import Qt, QTimer, QEvent, QThread, Signal
from PySide6.QtGui import QKeyEvent, QColor, QMouseEvent, QCursor, QBrush, QPalette, QFont

import vlc

# =========================
# CONFIG
# =========================
VIDEO_EXTS = {
    ".mp4", ".mkv", ".avi", ".mov", ".wmv", ".m4v",
    ".mpg", ".mpeg", ".rm", ".rmvb", ".flv", ".asf",
    ".webm", ".f4v", ".m2ts"
}
IMAGE_EXTS = {
    ".jpg", ".jpeg", ".png", ".gif", ".bmp", ".tif", ".tiff", ".webp", ".heic", ".heif"
}
if getattr(sys, 'frozen', False):
    APP_BASE_DIR = os.path.dirname(sys.executable)
else:
    APP_BASE_DIR = os.path.dirname(os.path.abspath(__file__))

LOG_DIR = os.path.join(APP_BASE_DIR, 'logs')
os.makedirs(LOG_DIR, exist_ok=True)
REVIEW_STATE_FILE = os.path.join(APP_BASE_DIR, "review_state.json")
APP_SETTINGS_FILE = os.path.join(APP_BASE_DIR, "app_settings.json")

LOG_FILE = os.path.join(
    LOG_DIR,
    f"media_review_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
)
QUICK_DEST_1080 = r"R:\Collection\1a. Unchecked\1080"
APP_VERSION = "1.0"
VK_LBUTTON = 0x01
VK_RBUTTON = 0x02

logging.basicConfig(
    filename=LOG_FILE,
    level=logging.DEBUG,
    format="%(asctime)s [%(levelname)s] %(message)s"
)

def _unhandled_exception(exc_type, exc_value, exc_tb):
    logging.critical("Unhandled exception", exc_info=(exc_type, exc_value, exc_tb))
    sys.__excepthook__(exc_type, exc_value, exc_tb)

sys.excepthook = _unhandled_exception

# Counter for throttled timeline heartbeat logs
_timeline_tick = 0

# =========================
# HELPERS
# =========================

def _find_ffprobe():
    for candidate in (
        os.path.join(sys._MEIPASS, 'ffprobe.exe') if getattr(sys, 'frozen', False) else None,
        r"C:\Program Files\FFmpeg\bin\ffprobe.exe",
        "ffprobe",
    ):
        if candidate and (candidate == "ffprobe" or os.path.exists(candidate)):
            return candidate
    return "ffprobe"

_FFPROBE = _find_ffprobe()

def get_video_metadata(path):
    try:
        p = subprocess.run(
            [
                _FFPROBE, "-v", "error",
                "-select_streams", "v:0",
                "-show_entries", "stream=width,height:format=duration",
                "-of", "default=nokey=1:noprint_wrappers=1",
                path
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=8
        )
        values = [line.strip() for line in p.stdout.splitlines() if line.strip()]
        if len(values) >= 3:
            width_text, height_text, duration_text = values[0], values[1], values[2]
            width = int(width_text) if width_text.isdigit() else 0
            height = int(height_text) if height_text.isdigit() else 0
            try:
                duration_sec = float(duration_text)
            except ValueError:
                duration_sec = 0.0
            return width, height, duration_sec
    except Exception:
        pass
    return 0, 0, 0.0


def get_video_category(width, height):
    if width > 0 and height > 0:
        return "horizontal" if width >= height else "vertical"
    return "unknown"

# =========================
# MAIN APP
# =========================

class MediaReviewApp(QMainWindow):
    def __init__(self):
        super().__init__()

        self.setWindowTitle(f"Media Review Tool v{APP_VERSION}")
        self.resize(1600, 900)

        self.root_folders = []
        self.dest_folder = ""
        self.trash_folder = ""
        self.last_browse_dir = self._load_last_browse_dir()
        self.permanent_delete_enabled = False
        self.video_files = []
        self.current_index = -1
        self.decisions = {}
        self.folder_direct_stats = {}
        self.folder_children = {}
        self.folder_aggregate_cache = {}
        self.quality_stats = {}

        self.playback_rate = 1.0
        self.review_active = False
        self._left_mouse_down = False
        self._right_mouse_down = False
        self.is_muted = False
        self.last_volume = 0
        self.auto_review_enabled = True
        self.auto_play_seconds = 1.5
        self.auto_jump_minutes = 5
        self.auto_playback_rate = 1.3
        self.auto_next_action_ms = None
        self.scan_worker = None
        self.dark_mode = False

        self._build_ui()

        # Apply defaults — must come after _build_ui so the buttons exist.
        # setChecked fires the toggled signal which calls the handler directly.
        self.btn_dark.setChecked(True)
        self.btn_quick_dest.setChecked(True)
        self.btn_perm_delete.setChecked(True)

        self._init_vlc()
        QApplication.instance().installEventFilter(self)
        self.exec_worker = None

    def _empty_folder_stats(self):
        return {
            "video": [0, 0],
            "image": [0, 0],
            "other": [0, 0],
            "horizontal": [0, 0],
            "vertical": [0, 0],
            "unknown": [0, 0],
        }

    def _quality_label(self, height):
        return f"{height}p" if height and height > 0 else "Unknown"

    def _quality_sort_key(self, label):
        if label.lower() == "unknown":
            return 1, 0
        value = label[:-1] if label.endswith("p") else label
        if value.isdigit():
            return 0, -int(value)
        return 0, 0

    def _files_decision_col(self):
        return 6

    def _normalized_path(self, path):
        return os.path.normcase(os.path.abspath(path))

    def _normalized_root_folders(self):
        return sorted(self._normalized_path(root) for root in self.root_folders)

    def _review_state_key(self):
        roots = self._normalized_root_folders()
        if not roots:
            return ""
        joined = "\n".join(roots)
        return hashlib.sha256(joined.encode("utf-8")).hexdigest()

    def _load_review_state_store(self):
        try:
            if not os.path.exists(REVIEW_STATE_FILE):
                return {}
            with open(REVIEW_STATE_FILE, "r", encoding="utf-8") as handle:
                data = json.load(handle)
            return data if isinstance(data, dict) else {}
        except Exception as ex:
            logging.error("Failed to load review state: %s", ex)
            return {}

    def _write_review_state_store(self, state_store):
        try:
            temp_path = f"{REVIEW_STATE_FILE}.tmp"
            with open(temp_path, "w", encoding="utf-8") as handle:
                json.dump(state_store, handle, indent=2, sort_keys=True)
            os.replace(temp_path, REVIEW_STATE_FILE)
        except Exception as ex:
            logging.error("Failed to write review state: %s", ex)

    def _save_review_state(self):
        state_key = self._review_state_key()
        if not state_key:
            return

        decisions = {}
        for row, decision in self.decisions.items():
            if row < 0 or row >= len(self.video_files):
                continue
            decisions[self._normalized_path(self.video_files[row]["path"])] = decision

        current_path = None
        if 0 <= self.current_index < len(self.video_files):
            current_path = self._normalized_path(self.video_files[self.current_index]["path"])

        state_store = self._load_review_state_store()
        if decisions or current_path:
            state_store[state_key] = {
                "version": 1,
                "roots": self._normalized_root_folders(),
                "saved_at": datetime.now().isoformat(timespec="seconds"),
                "current_path": current_path,
                "decisions": decisions,
            }
        else:
            state_store.pop(state_key, None)
        self._write_review_state_store(state_store)

    def _restore_review_state(self):
        state_key = self._review_state_key()
        if not state_key or not self.video_files:
            return

        state = self._load_review_state_store().get(state_key)
        if not isinstance(state, dict):
            return

        path_to_row = {
            self._normalized_path(video["path"]): idx
            for idx, video in enumerate(self.video_files)
        }
        restored = 0
        for saved_path, decision in state.get("decisions", {}).items():
            row = path_to_row.get(self._normalized_path(saved_path))
            if row is None or decision not in ("MOVE", "DELETE"):
                continue
            self.decisions[row] = decision
            item = self.files_table.item(row, self._files_decision_col())
            if item is not None:
                item.setText(decision)
            self._apply_row_color(row, decision)
            restored += 1

        current_row = None
        current_path = state.get("current_path")
        if current_path:
            current_row = path_to_row.get(self._normalized_path(current_path))

        if current_row is not None and current_row not in self.decisions:
            self.current_index = current_row
        else:
            first_unmarked = self._next_unmarked_index(0)
            self.current_index = first_unmarked if first_unmarked is not None else -1

        self.update_summary()
        self.apply_decision_filter()
        if self.current_index >= 0:
            self.files_table.selectRow(self.current_index)
            self.update_video_properties(self.current_index)

        logging.info("Restored review state: roots=%s restored=%s", self.root_folders, restored)

    def _delete_saved_state(self, state_key):
        state_store = self._load_review_state_store()
        if state_key in state_store:
            state_store.pop(state_key)
            self._write_review_state_store(state_store)
            logging.info("Deleted saved state for key=%s", state_key[:8])

    def _check_and_prompt_history(self):
        state_key = self._review_state_key()
        if not state_key or not self.video_files:
            return
        state = self._load_review_state_store().get(state_key)
        if not isinstance(state, dict):
            return
        decisions = state.get("decisions", {})
        if not decisions:
            return

        saved_at = state.get("saved_at", "unknown date")
        count = len(decisions)
        roots_text = "\n".join(f"  {r}" for r in state.get("roots", self.root_folders))

        result = QMessageBox.question(
            self,
            "Restore Mark History",
            f"Saved mark history found for:\n{roots_text}\n\n"
            f"{count} mark(s) saved on {saved_at}\n\n"
            f"Restore marks from history?",
            QMessageBox.Yes | QMessageBox.No
        )

        if result == QMessageBox.Yes:
            self._restore_review_state()
        else:
            self._delete_saved_state(state_key)
            logging.info("Mark history discarded by user")

    # =========================
    # UI
    # =========================

    def _build_ui(self):
        root = QWidget()
        self.setCentralWidget(root)

        # ---------- TOP BAR ----------
        top = QHBoxLayout()

        self.root_label = QLabel("Roots: Not set")
        self.dest_label = QLabel("Destination: Not set")
        self.trash_label = QLabel("Trash: Not set")

        btn_root = QPushButton("📁 Browse Root(s)")
        btn_dest = QPushButton("Browse Destination")
        btn_quick_dest = QPushButton("1080p Quick")
        btn_quick_dest.setCheckable(True)
        btn_trash = QPushButton("Browse Trash")
        btn_perm_delete = QPushButton("Perm. Delete")
        btn_perm_delete.setCheckable(True)
        btn_scan = QPushButton("⟳  Scan")
        btn_review = QPushButton("▶  Review")
        btn_stop = QPushButton("■  Stop")
        btn_exec = QPushButton("✓  Execute")
        btn_logs = QPushButton("Logs")
        btn_scan.setObjectName("btn_primary")
        btn_review.setObjectName("btn_primary")
        btn_stop.setObjectName("btn_danger")
        btn_exec.setObjectName("btn_success")
        btn_logs.setObjectName("btn_ghost")

        btn_root.clicked.connect(self.pick_root)
        btn_dest.clicked.connect(self.pick_dest)
        btn_quick_dest.toggled.connect(self.toggle_quick_dest)
        btn_trash.clicked.connect(self.pick_trash)
        btn_perm_delete.toggled.connect(self.toggle_permanent_delete)
        btn_scan.clicked.connect(self.start_scan)
        btn_review.clicked.connect(self.start_review)
        btn_stop.clicked.connect(self.stop_review)
        btn_exec.clicked.connect(self.execute_actions)
        btn_logs.clicked.connect(lambda: os.startfile(LOG_FILE))

        top.addWidget(self.root_label)
        top.addWidget(btn_root)
        top.addSpacing(12)
        top.addWidget(self.dest_label)
        top.addWidget(btn_dest)
        top.addWidget(btn_quick_dest)
        top.addSpacing(12)
        top.addWidget(self.trash_label)
        top.addWidget(btn_trash)
        top.addWidget(btn_perm_delete)
        btn_dark = QPushButton("🌙  Dark")
        btn_dark.setCheckable(True)
        btn_dark.setObjectName("btn_dark_toggle")
        btn_dark.toggled.connect(self.toggle_dark_mode)

        top.addStretch()
        top.addWidget(btn_scan)
        top.addWidget(btn_review)
        top.addWidget(btn_stop)
        top.addWidget(btn_exec)
        top.addWidget(btn_logs)
        top.addSpacing(16)
        top.addWidget(btn_dark)
        self.btn_review = btn_review
        self.btn_stop = btn_stop
        self.btn_exec = btn_exec
        self.btn_dark = btn_dark
        self.btn_dest = btn_dest
        self.btn_quick_dest = btn_quick_dest
        self.btn_trash = btn_trash
        self.btn_perm_delete = btn_perm_delete
        self.btn_stop.setEnabled(False)
        self.btn_exec.setEnabled(False)

        # ---------- LEFT PANEL ----------
        self.folder_tree = QTreeWidget()
        self.folder_tree.setHeaderLabel("Folders")
        self.folder_tree.setFocusPolicy(Qt.NoFocus)

        self.files_table = QTableWidget(0, 7)
        self.files_table.setHorizontalHeaderLabels(
            ["#", "File", "Category", "Height", "Duration", "Size (GB)", "Decision"]
        )
        self.files_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.files_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.files_table.setFocusPolicy(Qt.NoFocus)
        self.files_table.verticalHeader().setVisible(False)
        self.files_table.setItemDelegate(DecisionColorDelegate(self.files_table))
        files_header = self.files_table.horizontalHeader()
        files_header.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        files_header.setSectionResizeMode(1, QHeaderView.Stretch)
        files_header.setSectionResizeMode(2, QHeaderView.ResizeToContents)
        files_header.setSectionResizeMode(3, QHeaderView.ResizeToContents)
        files_header.setSectionResizeMode(4, QHeaderView.ResizeToContents)
        files_header.setSectionResizeMode(5, QHeaderView.ResizeToContents)
        files_header.setSectionResizeMode(6, QHeaderView.ResizeToContents)
        self.files_table.setColumnWidth(0, 40)
        self.files_table.setColumnWidth(2, 95)
        self.files_table.setColumnWidth(3, 80)
        self.files_table.setColumnWidth(4, 90)
        self.files_table.setColumnWidth(5, 80)
        self.files_table.setColumnWidth(6, 95)
        self.files_table.itemSelectionChanged.connect(self._on_files_selection_changed)

        self.quality_table_horizontal = QTableWidget(0, 6)
        self.quality_table_horizontal.setHorizontalHeaderLabels(
            ["Quality", "Bar", "Total", "Left", "Avg Length", "Avg Size (GB)"]
        )
        self.quality_table_horizontal.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.quality_table_horizontal.setSelectionMode(QAbstractItemView.NoSelection)
        self.quality_table_horizontal.setFocusPolicy(Qt.NoFocus)
        self.quality_table_horizontal.verticalHeader().setVisible(False)
        quality_header = self.quality_table_horizontal.horizontalHeader()
        quality_header.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        quality_header.setSectionResizeMode(1, QHeaderView.Stretch)
        quality_header.setSectionResizeMode(2, QHeaderView.ResizeToContents)
        quality_header.setSectionResizeMode(3, QHeaderView.ResizeToContents)
        quality_header.setSectionResizeMode(4, QHeaderView.ResizeToContents)
        quality_header.setSectionResizeMode(5, QHeaderView.ResizeToContents)
        self.quality_table_horizontal.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

        self.quality_table_vertical = QTableWidget(0, 6)
        self.quality_table_vertical.setHorizontalHeaderLabels(
            ["Quality", "Bar", "Total", "Left", "Avg Length", "Avg Size (GB)"]
        )
        self.quality_table_vertical.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.quality_table_vertical.setSelectionMode(QAbstractItemView.NoSelection)
        self.quality_table_vertical.setFocusPolicy(Qt.NoFocus)
        self.quality_table_vertical.verticalHeader().setVisible(False)
        quality_header = self.quality_table_vertical.horizontalHeader()
        quality_header.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        quality_header.setSectionResizeMode(1, QHeaderView.Stretch)
        quality_header.setSectionResizeMode(2, QHeaderView.ResizeToContents)
        quality_header.setSectionResizeMode(3, QHeaderView.ResizeToContents)
        quality_header.setSectionResizeMode(4, QHeaderView.ResizeToContents)
        quality_header.setSectionResizeMode(5, QHeaderView.ResizeToContents)
        self.quality_table_vertical.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

        self.video_props_table = QTableWidget(0, 2)
        self.video_props_table.setHorizontalHeaderLabels(["Property", "Value"])
        self.video_props_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.video_props_table.setSelectionMode(QAbstractItemView.NoSelection)
        self.video_props_table.setFocusPolicy(Qt.NoFocus)
        self.video_props_table.verticalHeader().setVisible(False)
        props_header = self.video_props_table.horizontalHeader()
        props_header.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        props_header.setSectionResizeMode(1, QHeaderView.Stretch)
        self.video_props_table.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

        self.filter_combo = QComboBox()
        self.filter_combo.addItems(["ALL", "UNMARKED", "MOVE", "DELETE"])
        self.filter_combo.currentTextChanged.connect(self.apply_decision_filter)

        filter_row = QHBoxLayout()
        filter_row.addWidget(QLabel("Filter:"))
        filter_row.addWidget(self.filter_combo)
        filter_row.addStretch()

        files_container = QWidget()
        files_layout = QVBoxLayout(files_container)
        files_layout.setContentsMargins(0, 0, 0, 0)
        files_layout.addLayout(filter_row)
        files_layout.addWidget(self.files_table)

        # ---------- VIDEO ----------
        self.video_frame = QWidget()
        self.video_frame.setStyleSheet("background:black;")
        self.video_frame.setFocusPolicy(Qt.StrongFocus)
        self.video_frame.setAttribute(Qt.WA_NativeWindow, True)
        self.video_frame.setAttribute(Qt.WA_DontCreateNativeAncestors, True)

        self.timeline = QSlider(Qt.Horizontal)
        self.timeline.setRange(0, 1000)
        self.timeline.sliderMoved.connect(self.seek_from_slider)
        self.timeline.setFocusPolicy(Qt.NoFocus)

        self.time_label = QLabel("00:00 / 00:00")
        self.volume_label = QLabel("VOL: 0%")
        self.speed_label = QLabel("SPEED: 1.0x")
        self.auto_mode_check = QCheckBox("Auto Mode")
        self.auto_mode_check.setChecked(True)
        self.auto_mode_check.toggled.connect(self.toggle_auto_review)
        self.auto_play_spin = QDoubleSpinBox()
        self.auto_play_spin.setRange(0.5, 600.0)
        self.auto_play_spin.setSingleStep(0.5)
        self.auto_play_spin.setDecimals(1)
        self.auto_play_spin.setValue(self.auto_play_seconds)
        self.auto_play_spin.setSuffix(" s")
        self.auto_play_spin.valueChanged.connect(self.set_auto_play_seconds)
        self.auto_jump_spin = QSpinBox()
        self.auto_jump_spin.setRange(1, 180)
        self.auto_jump_spin.setValue(self.auto_jump_minutes)
        self.auto_jump_spin.setSuffix(" min")
        self.auto_jump_spin.valueChanged.connect(self.set_auto_jump_minutes)
        self.auto_speed_spin = QSpinBox()
        self.auto_speed_spin.setRange(50, 300)
        self.auto_speed_spin.setSingleStep(10)
        self.auto_speed_spin.setValue(int(self.auto_playback_rate * 100))
        self.auto_speed_spin.setSuffix(" %")
        self.auto_speed_spin.valueChanged.connect(self.set_auto_playback_rate)

        time_row = QHBoxLayout()
        time_row.addWidget(self.time_label)
        time_row.addStretch()
        time_row.addWidget(self.speed_label)
        time_row.addSpacing(12)
        time_row.addWidget(self.volume_label)

        video_layout = QVBoxLayout()
        video_layout.addWidget(self.video_frame, stretch=10)
        video_layout.addWidget(self.timeline)
        video_layout.addLayout(time_row)
        auto_row = QHBoxLayout()
        auto_row.addWidget(self.auto_mode_check)
        auto_row.addWidget(QLabel("Play:"))
        auto_row.addWidget(self.auto_play_spin)
        auto_row.addWidget(QLabel("Jump:"))
        auto_row.addWidget(self.auto_jump_spin)
        auto_row.addWidget(QLabel("Speed:"))
        auto_row.addWidget(self.auto_speed_spin)
        auto_row.addStretch()
        video_layout.addLayout(auto_row)

        left_split = QSplitter(Qt.Vertical)
        left_split.addWidget(files_container)
        left_split.setStretchFactor(0, 1)

        # ---------- CENTER ----------
        center_split = QSplitter(Qt.Horizontal)
        left_container = QWidget()
        left_layout = QVBoxLayout(left_container)
        left_layout.setContentsMargins(0, 0, 0, 0)
        left_layout.addWidget(left_split)

        right_container = QWidget()
        right_layout = QVBoxLayout(right_container)
        right_layout.setContentsMargins(0, 0, 0, 0)
        video_panel = QWidget()
        video_panel.setLayout(video_layout)
        right_layout.addWidget(video_panel)

        quality_container = QWidget()
        quality_layout = QVBoxLayout(quality_container)
        quality_layout.setContentsMargins(0, 0, 0, 0)
        quality_top = QWidget()
        quality_top_layout = QVBoxLayout(quality_top)
        quality_top_layout.setContentsMargins(0, 0, 0, 0)
        quality_top_layout.addWidget(QLabel("Video Quality - Horizontal"))
        quality_top_layout.addWidget(self.quality_table_horizontal)
        quality_top_layout.addWidget(QLabel("Video Quality - Vertical"))
        quality_top_layout.addWidget(self.quality_table_vertical)

        props_container = QWidget()
        props_layout = QVBoxLayout(props_container)
        props_layout.setContentsMargins(0, 0, 0, 0)
        props_layout.addWidget(QLabel("Video Properties"))
        props_layout.addWidget(self.video_props_table)

        quality_split = QSplitter(Qt.Vertical)
        quality_split.addWidget(quality_top)
        quality_split.addWidget(props_container)
        quality_split.setStretchFactor(0, 3)
        quality_split.setStretchFactor(1, 2)

        right_info_split = QSplitter(Qt.Vertical)
        right_info_split.addWidget(self.folder_tree)
        right_info_split.addWidget(quality_split)
        right_info_split.setStretchFactor(0, 2)
        right_info_split.setStretchFactor(1, 3)
        quality_layout.addWidget(right_info_split)

        center_split.addWidget(left_container)
        center_split.addWidget(right_container)
        center_split.addWidget(quality_container)
        center_split.setStretchFactor(0, 6)
        center_split.setStretchFactor(1, 8)
        center_split.setStretchFactor(2, 2)
        center_split.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

        # ---------- BOTTOM STATUS BAR ----------
        from PySide6.QtWidgets import QFrame
        self.progress = QProgressBar()
        self.progress.setTextVisible(True)
        self.progress.setObjectName("scan_progress")
        self.progress.setFormat("Ready")

        self.lbl_move = QLabel("✓  MOVE\n0  (0.00 GB)")
        self.lbl_delete = QLabel("✕  DELETE\n0  (0.00 GB)")
        self.lbl_unmarked = QLabel("—  UNMARKED\n0  (0.00 GB)")
        for lbl in (self.lbl_move, self.lbl_delete, self.lbl_unmarked):
            lbl.setAlignment(Qt.AlignCenter)
        self.lbl_move.setObjectName("stat_move")
        self.lbl_delete.setObjectName("stat_delete")
        self.lbl_unmarked.setObjectName("stat_unmarked")

        status_bar = QFrame()
        status_bar.setObjectName("status_bar")
        status_layout = QHBoxLayout(status_bar)
        status_layout.setContentsMargins(12, 6, 12, 6)
        status_layout.setSpacing(10)
        status_layout.addWidget(self.progress, stretch=3)
        status_layout.addWidget(self.lbl_move, stretch=2)
        status_layout.addWidget(self.lbl_delete, stretch=2)
        status_layout.addWidget(self.lbl_unmarked, stretch=2)

        # ---------- ROOT ----------
        layout = QVBoxLayout(root)
        layout.addLayout(top)
        layout.addWidget(center_split)
        layout.addWidget(status_bar)
        layout.setStretch(1, 1)
        layout.setStretch(2, 0)
        layout.setContentsMargins(8, 8, 8, 6)
        layout.setSpacing(6)

        self.apply_theme()

        # ---------- TIMERS ----------
        self.timer = QTimer(self)
        self.timer.setTimerType(Qt.PreciseTimer)
        self.timer.timeout.connect(self.update_timeline)
        self.mouse_poll_timer = QTimer(self)
        self.mouse_poll_timer.setTimerType(Qt.PreciseTimer)
        self.mouse_poll_timer.timeout.connect(self._poll_review_mouse)
        self._quality_timer = QTimer(self)
        self._quality_timer.setSingleShot(True)
        self._quality_timer.timeout.connect(self.update_quality_panel)

    # =========================
    # VLC
    # =========================

    def _init_vlc(self):
        self.vlc = vlc.Instance(
            "--no-video-title-show",
            "--avcodec-hw=d3d11va",
            "--quiet",
        )
        self.player = self.vlc.media_player_new()
        self.player.set_hwnd(int(self.video_frame.winId()))
        # Prevent VLC's embedded window from receiving native mouse/key events.
        # Without this, a click on the video frame is delivered to VLC's child
        # HWND on its own internal thread while we call stop()/set_media()/play()
        # on the main thread, creating a race condition that hard-crashes libvlc.
        self.player.video_set_mouse_input(False)
        self.player.video_set_key_input(False)
        self.player.audio_set_volume(0)
        self._update_volume_label()
        self._update_speed_label()

    # =========================
    # SCAN
    # =========================

    def _load_last_browse_dir(self):
        try:
            with open(APP_SETTINGS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            d = data.get("last_browse_dir", "")
            return d if d and os.path.isdir(d) else ""
        except Exception:
            return ""

    def _save_last_browse_dir(self, path):
        try:
            data = {}
            try:
                with open(APP_SETTINGS_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
            except Exception:
                pass
            data["last_browse_dir"] = path
            with open(APP_SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            self.last_browse_dir = path
        except Exception as e:
            logging.warning("Could not save last browse dir: %s", e)

    def pick_root(self):
        dialog = QFileDialog(self, "Select Root Folder(s)")
        dialog.setFileMode(QFileDialog.Directory)
        dialog.setOption(QFileDialog.ShowDirsOnly, True)
        dialog.setOption(QFileDialog.DontUseNativeDialog, True)
        dialog.setDirectory(self.last_browse_dir)
        for view in dialog.findChildren(QListView):
            view.setSelectionMode(QAbstractItemView.ExtendedSelection)
        for view in dialog.findChildren(QTreeView):
            view.setSelectionMode(QAbstractItemView.ExtendedSelection)
        if not dialog.exec():
            return
        paths = [p for p in dialog.selectedFiles() if os.path.isdir(p)]
        if paths:
            self._save_last_browse_dir(paths[0])
            old_state_key = self._review_state_key()
            self._set_root_folders(paths)
            new_state_key = self._review_state_key()
            if old_state_key and old_state_key != new_state_key:
                self._delete_saved_state(old_state_key)
            self._apply_default_trash()
            self._apply_default_dest()
            self.start_scan()

    def pick_dest(self):
        path = QFileDialog.getExistingDirectory(self, "Select Destination", "")
        if path:
            if self._is_subpath_any(path, self.root_folders):
                QMessageBox.warning(self, "Invalid", "Destination cannot be inside root")
                return
            if self.trash_folder and os.path.normcase(os.path.abspath(path)) == os.path.normcase(os.path.abspath(self.trash_folder)):
                QMessageBox.warning(self, "Invalid", "Destination and Trash must be different folders")
                return
            if self.btn_quick_dest.isChecked():
                self.btn_quick_dest.setChecked(False)
            self.dest_folder = path
            self.dest_label.setText(f"Destination: {path}")
            self.update_execute_enabled()

    def toggle_quick_dest(self, checked):
        self.btn_dest.setEnabled(not checked)
        if checked:
            self.dest_folder = QUICK_DEST_1080
            self.dest_label.setText(f"Destination: {self.dest_folder}")
        else:
            self._apply_default_dest()
        self.update_execute_enabled()

    def pick_trash(self):
        path = QFileDialog.getExistingDirectory(self, "Select Trash", "")
        if path:
            if self._is_subpath_any(path, self.root_folders):
                QMessageBox.warning(self, "Invalid", "Trash cannot be inside root")
                return
            if self.dest_folder and os.path.normcase(os.path.abspath(path)) == os.path.normcase(os.path.abspath(self.dest_folder)):
                QMessageBox.warning(self, "Invalid", "Trash and Destination must be different folders")
                return
            if self.btn_perm_delete.isChecked():
                self.btn_perm_delete.setChecked(False)
            self.trash_folder = path
            self.trash_label.setText(f"Trash: {path}")
            self.update_execute_enabled()

    def _apply_default_dest(self):
        if hasattr(self, "btn_quick_dest") and self.btn_quick_dest.isChecked():
            self.dest_folder = QUICK_DEST_1080
            self.dest_label.setText(f"Destination: {self.dest_folder}")
            self.update_execute_enabled()
            return
        drive = self._get_root_drive()
        if not drive:
            return
        dest_path = os.path.join(f"{drive}\\", "Selected")
        os.makedirs(dest_path, exist_ok=True)
        self.dest_folder = dest_path
        self.dest_label.setText(f"Destination: {self.dest_folder}")
        self.update_execute_enabled()

    def _apply_default_trash(self):
        if hasattr(self, "btn_perm_delete") and self.btn_perm_delete.isChecked():
            self.trash_folder = ""
            self.trash_label.setText("Trash: Permanent Delete")
            self.update_execute_enabled()
            return
        if not self.root_folders:
            return
        drive = self._get_root_drive()
        if not drive:
            return
        trash_path = os.path.join(f"{drive}\\", "Trash")
        os.makedirs(trash_path, exist_ok=True)
        self.trash_folder = trash_path
        self.trash_label.setText(f"Trash: {self.trash_folder}")
        self.update_execute_enabled()

    def toggle_permanent_delete(self, checked):
        self.permanent_delete_enabled = checked
        self.btn_trash.setEnabled(not checked)
        if checked:
            self.trash_folder = ""
            self.trash_label.setText("Trash: Permanent Delete")
        else:
            self._apply_default_trash()
        self.update_execute_enabled()

    def start_scan(self):
        if not self.root_folders:
            return
        logging.info("Scan started: roots=%s", self.root_folders)

        if self.scan_worker is not None:
            self.scan_worker.cancel()
            self.scan_worker = None

        self.stop_review()
        self.video_files.clear()
        self.decisions.clear()
        self.review_active = False
        self.current_index = -1
        self.folder_direct_stats.clear()
        self.folder_children.clear()
        self.folder_aggregate_cache.clear()
        self.quality_stats.clear()
        self.folder_tree.clear()
        self.files_table.setRowCount(0)
        self.quality_table_horizontal.setRowCount(0)
        self.quality_table_vertical.setRowCount(0)
        self.video_props_table.setRowCount(0)
        self.progress.setValue(0)
        self.progress.setFormat("Walking folders…")
        self.update_summary()

        # Fast synchronous pass: walk dirs, count files
        all_files = []
        for root_folder in self.root_folders:
            if not os.path.isdir(root_folder):
                continue
            for root, dirnames, files in os.walk(root_folder):
                self.folder_direct_stats.setdefault(root, self._empty_folder_stats())
                self.folder_children.setdefault(root, [])
                for d in dirnames:
                    child = os.path.join(root, d)
                    self.folder_children.setdefault(child, [])
                    self.folder_children[root].append(child)
                for f in files:
                    full = os.path.join(root, f)
                    ext = os.path.splitext(f)[1].lower()
                    try:
                        size_bytes = os.path.getsize(full)
                    except OSError:
                        size_bytes = 0
                    bucket = "video" if ext in VIDEO_EXTS else ("image" if ext in IMAGE_EXTS else "other")
                    self.folder_direct_stats[root][bucket][0] += 1
                    self.folder_direct_stats[root][bucket][1] += size_bytes
                    if ext in VIDEO_EXTS:
                        all_files.append({"path": full, "folder": root, "size_bytes": size_bytes})

        total = len(all_files)
        self.progress.setMaximum(max(total, 1))
        self.progress.setValue(0)
        self.progress.setFormat(f"Probing %v/{total} (%p%)")

        self.btn_review.setEnabled(False)
        self.btn_exec.setEnabled(False)

        if not all_files:
            self._finish_scan([])
            return

        self.scan_worker = ScanWorker(all_files)
        self.scan_worker.progress.connect(self._on_scan_progress)
        self.scan_worker.finished.connect(self._on_scan_finished)
        self.scan_worker.start()

    def _on_scan_progress(self, current, _total):
        self.progress.setValue(current)

    def _on_scan_finished(self, results):
        self.scan_worker = None
        self._finish_scan(results)

    def _finish_scan(self, results):
        for r in results:
            folder = r["folder"]
            category = r["category"]
            size_bytes = r["size_bytes"]
            if folder in self.folder_direct_stats:
                self.folder_direct_stats[folder][category][0] += 1
                self.folder_direct_stats[folder][category][1] += size_bytes
            quality_entry = self.quality_stats.setdefault(
                r["quality"], {"count": 0, "total_duration": 0.0, "total_size": 0.0}
            )
            quality_entry["count"] += 1
            quality_entry["total_duration"] += r["duration_sec"]
            quality_entry["total_size"] += r["size"]
            self.video_files.append({
                "path": r["path"], "name": r["name"], "size": r["size"],
                "width": r["width"], "height": r["height"],
                "duration_sec": r["duration_sec"], "category": category, "quality": r["quality"],
            })

        self.video_files.sort(key=lambda x: (
            {"horizontal": 0, "vertical": 1, "unknown": 2}.get(x["category"], 2),
            -x["height"], -x["size"],
        ))

        self.progress.setFormat(f"Done — {len(self.video_files)} videos")
        self.populate_files()
        self._check_and_prompt_history()
        self._save_review_state()
        self.update_quality_panel()
        self.populate_tree()
        self.btn_review.setEnabled(bool(self.video_files))
        self.update_execute_enabled()
        logging.info("Scan complete: videos=%s", len(self.video_files))

    def _root_for_path(self, file_path):
        normalized_path = os.path.normcase(os.path.abspath(file_path))
        matching_roots = []
        for root in self.root_folders:
            root_abs = os.path.normcase(os.path.abspath(root))
            try:
                if os.path.commonpath([normalized_path, root_abs]) == root_abs:
                    matching_roots.append(root)
            except ValueError:
                continue
        if not matching_roots:
            return None
        return max(matching_roots, key=lambda root: len(os.path.abspath(root)))

    def _roots_fully_marked_for_execute(self):
        per_root = {}
        for idx, video in enumerate(self.video_files):
            root = self._root_for_path(video["path"])
            if root is None:
                continue
            stats = per_root.setdefault(root, {"total": 0, "marked": 0})
            stats["total"] += 1
            if self.decisions.get(idx) in ("MOVE", "DELETE"):
                stats["marked"] += 1
        return [
            root for root, stats in per_root.items()
            if stats["total"] > 0 and stats["marked"] == stats["total"]
        ]

    def _clear_scan_results(self):
        self.video_files.clear()
        self.decisions.clear()
        self.quality_stats.clear()
        self.current_index = -1
        self.folder_direct_stats.clear()
        self.folder_children.clear()
        self.folder_aggregate_cache.clear()
        self.folder_tree.clear()
        self.files_table.setRowCount(0)
        self.quality_table_horizontal.setRowCount(0)
        self.quality_table_vertical.setRowCount(0)
        self.video_props_table.setRowCount(0)
        self.progress.setValue(0)
        self.progress.setFormat("Ready")
        self.update_summary()
        self.btn_review.setEnabled(False)
        self.btn_stop.setEnabled(False)
        self.update_execute_enabled()
        self._save_review_state()

    def _confirm_and_delete_completed_roots(self, roots):
        eligible_roots = []
        for root in roots:
            if not os.path.isdir(root):
                continue
            totals = self._aggregate_stats(root)
            if totals["video_count"] == 0:
                eligible_roots.append((root, totals))

        if not eligible_roots:
            return False

        summary_lines = ["Rescan summary for completed root folders:"]
        for root, totals in eligible_roots:
            summary_lines.extend([
                "",
                root,
                f"Videos remaining: {totals['video_count']} ({self._format_gb(totals['video_size'])})",
                f"Images remaining: {totals['image_count']} ({self._format_gb(totals['image_size'])})",
                f"Other remaining: {totals['other_count']} ({self._format_gb(totals['other_size'])})",
                f"Total remaining: {totals['count']} ({self._format_gb(totals['size'])})",
            ])
        summary_lines.extend([
            "",
            "Delete these root folders now?"
        ])

        confirm = QMessageBox.question(
            self,
            "Delete Completed Root Folders",
            "\n".join(summary_lines),
            QMessageBox.Yes | QMessageBox.No
        )
        if confirm != QMessageBox.Yes:
            return False

        deleted_roots = []
        errors = []
        for root, _totals in eligible_roots:
            try:
                shutil.rmtree(root)
                deleted_roots.append(root)
                logging.info("Deleted completed root folder: %s", root)
            except Exception as ex:
                errors.append(f"{root}: {ex}")
                logging.error("Failed to delete root folder %s: %s", root, ex)

        if errors:
            QMessageBox.warning(
                self,
                "Delete Failed",
                "Some root folders could not be deleted:\n" + "\n".join(errors)
            )

        if deleted_roots:
            remaining_roots = [root for root in self.root_folders if root not in deleted_roots]
            self._set_root_folders(remaining_roots)
            return True
        return False

    # =========================
    # TREE / FILES
    # =========================

    def populate_tree(self):
        for root_folder in self.root_folders:
            root_name = os.path.basename(root_folder) or root_folder
            root_item = QTreeWidgetItem([root_name])
            self.folder_tree.addTopLevelItem(root_item)
            self._populate_tree_recursive(root_folder, root_item)
        self.folder_tree.expandToDepth(1)

    def _format_gb(self, size_bytes):
        return f"{size_bytes / (1024**3):.2f} GB"

    def _populate_tree_recursive(self, folder_path, parent_item):
        totals = self._aggregate_stats(folder_path)
        base_name = os.path.basename(folder_path) or folder_path
        parent_item.setText(0, f"{base_name}: {totals['count']} ({self._format_gb(totals['size'])})")

        video_text = f"Videos: {totals['video_count']} ({self._format_gb(totals['video_size'])})"
        horizontal_text = f"Horizontal: {totals['horizontal_count']} ({self._format_gb(totals['horizontal_size'])})"
        vertical_text = f"Vertical: {totals['vertical_count']} ({self._format_gb(totals['vertical_size'])})"
        image_text = f"Images: {totals['image_count']} ({self._format_gb(totals['image_size'])})"
        other_text = f"Other: {totals['other_count']} ({self._format_gb(totals['other_size'])})"
        parent_item.addChild(QTreeWidgetItem([video_text]))
        parent_item.addChild(QTreeWidgetItem([horizontal_text]))
        parent_item.addChild(QTreeWidgetItem([vertical_text]))
        parent_item.addChild(QTreeWidgetItem([image_text]))
        parent_item.addChild(QTreeWidgetItem([other_text]))
        if totals["unknown_count"]:
            unknown_text = f"Unknown: {totals['unknown_count']} ({self._format_gb(totals['unknown_size'])})"
            parent_item.addChild(QTreeWidgetItem([unknown_text]))

        children = sorted(self.folder_children.get(folder_path, []))
        for child in children:
            child_item = QTreeWidgetItem([os.path.basename(child)])
            parent_item.addChild(child_item)
            self._populate_tree_recursive(child, child_item)

    def _aggregate_stats(self, folder_path):
        cached = self.folder_aggregate_cache.get(folder_path)
        if cached is not None:
            return cached
        direct = self.folder_direct_stats.get(
            folder_path,
            self._empty_folder_stats()
        )
        totals = {
            "video_count": direct["video"][0],
            "video_size": direct["video"][1],
            "horizontal_count": direct["horizontal"][0],
            "horizontal_size": direct["horizontal"][1],
            "vertical_count": direct["vertical"][0],
            "vertical_size": direct["vertical"][1],
            "unknown_count": direct["unknown"][0],
            "unknown_size": direct["unknown"][1],
            "image_count": direct["image"][0],
            "image_size": direct["image"][1],
            "other_count": direct["other"][0],
            "other_size": direct["other"][1],
        }
        for child in self.folder_children.get(folder_path, []):
            child_totals = self._aggregate_stats(child)
            totals["video_count"] += child_totals["video_count"]
            totals["video_size"] += child_totals["video_size"]
            totals["horizontal_count"] += child_totals["horizontal_count"]
            totals["horizontal_size"] += child_totals["horizontal_size"]
            totals["vertical_count"] += child_totals["vertical_count"]
            totals["vertical_size"] += child_totals["vertical_size"]
            totals["unknown_count"] += child_totals["unknown_count"]
            totals["unknown_size"] += child_totals["unknown_size"]
            totals["image_count"] += child_totals["image_count"]
            totals["image_size"] += child_totals["image_size"]
            totals["other_count"] += child_totals["other_count"]
            totals["other_size"] += child_totals["other_size"]

        totals["count"] = totals["video_count"] + totals["image_count"] + totals["other_count"]
        totals["size"] = totals["video_size"] + totals["image_size"] + totals["other_size"]
        self.folder_aggregate_cache[folder_path] = totals
        return totals

    def populate_files(self):
        self.files_table.setRowCount(len(self.video_files))
        for i, f in enumerate(self.video_files):
            duration_ms = int(max(0.0, f.get("duration_sec", 0.0)) * 1000)
            self.files_table.setItem(i, 0, QTableWidgetItem(str(i+1)))
            self.files_table.setItem(i, 1, QTableWidgetItem(f["name"]))
            self.files_table.setItem(i, 2, QTableWidgetItem(f["category"]))
            self.files_table.setItem(i, 3, QTableWidgetItem(f"{f['height']} px"))
            self.files_table.setItem(i, 4, QTableWidgetItem(self._format_time(duration_ms)))
            self.files_table.setItem(i, 5, QTableWidgetItem(f"{f['size']:.2f}"))
            self.files_table.setItem(i, 6, QTableWidgetItem("UNMARKED"))
            self._clear_row_color(i)   # stamp base colours so stylesheet can't override them
        self.apply_decision_filter()
        self.update_video_properties(None)

    def _fill_quality_table(self, table, category):
        rows = [f for f in self.video_files if f.get("category") == category]
        by_quality = {}
        for f in rows:
            quality = f.get("quality", "Unknown")
            entry = by_quality.setdefault(
                quality,
                {"count": 0, "total_duration": 0.0, "total_size": 0.0}
            )
            entry["count"] += 1
            entry["total_duration"] += f.get("duration_sec", 0.0)
            entry["total_size"] += f.get("size", 0.0)

        marked_by_quality = {}
        for row in self.decisions:
            video = self.video_files[row]
            if video.get("category") != category:
                continue
            quality = video.get("quality", "Unknown")
            marked_by_quality[quality] = marked_by_quality.get(quality, 0) + 1

        qualities = sorted(by_quality.keys(), key=self._quality_sort_key)
        table.setRowCount(len(qualities))
        total_videos = max(1, len(rows))

        for row, quality in enumerate(qualities):
            stats = by_quality[quality]
            total = stats["count"]
            left = max(0, total - marked_by_quality.get(quality, 0))
            avg_duration_sec = (stats["total_duration"] / total) if total else 0.0
            avg_size = (stats["total_size"] / total) if total else 0.0

            table.setItem(row, 0, QTableWidgetItem(quality))
            bar = QProgressBar()
            bar.setMinimum(0)
            bar.setMaximum(total_videos)
            bar.setValue(total)
            bar.setFormat(f"{total}")
            table.setCellWidget(row, 1, bar)
            table.setItem(row, 2, QTableWidgetItem(str(total)))
            table.setItem(row, 3, QTableWidgetItem(str(left)))
            table.setItem(
                row, 4,
                QTableWidgetItem(self._format_time(int(avg_duration_sec * 1000)))
            )
            table.setItem(row, 5, QTableWidgetItem(f"{avg_size:.2f}"))

    def update_quality_panel(self):
        if not hasattr(self, "quality_table_horizontal"):
            return
        self._fill_quality_table(self.quality_table_horizontal, "horizontal")
        self._fill_quality_table(self.quality_table_vertical, "vertical")

    def _on_files_selection_changed(self):
        selected_row = self._get_selected_row()
        self.update_video_properties(selected_row)

    def update_video_properties(self, row):
        if row is None or row < 0 or row >= len(self.video_files):
            self.video_props_table.setRowCount(0)
            return
        video = self.video_files[row]
        folder = os.path.dirname(video["path"])
        resolution = f"{video.get('width', 0)} x {video.get('height', 0)}"
        details = [
            ("Name", video.get("name", "")),
            ("Folder", folder),
            ("Size (GB)", f"{video.get('size', 0.0):.2f}"),
            ("Playback Time", self._format_time(int(max(0.0, video.get("duration_sec", 0.0)) * 1000))),
            ("Quality", video.get("quality", "Unknown")),
            ("Category", video.get("category", "unknown")),
            ("Resolution", resolution),
        ]
        self.video_props_table.setRowCount(len(details))
        for idx, (label, value) in enumerate(details):
            self.video_props_table.setItem(idx, 0, QTableWidgetItem(label))
            self.video_props_table.setItem(idx, 1, QTableWidgetItem(str(value)))

    # =========================
    # REVIEW
    # =========================

    def start_review(self):
        if not self.video_files:
            return
        self._begin_review_playback()

    def _begin_review_playback(self):
        if not self.video_files:
            return
        logging.debug("Review starting: total_files=%s", len(self.video_files))
        self.review_active = True
        self._left_mouse_down = False
        self._right_mouse_down = False
        self.mouse_poll_timer.start(30)
        self.lock_review_focus(True)
        first_unmarked = self._next_unmarked_index(0)
        self.current_index = first_unmarked if first_unmarked is not None else 0
        self.play_current()
        self.btn_review.setEnabled(False)
        self.btn_stop.setEnabled(True)
        self.update_execute_enabled()

    def stop_review(self):
        self.review_active = False
        self.timer.stop()
        self.mouse_poll_timer.stop()
        self._left_mouse_down = False
        self._right_mouse_down = False
        self.auto_next_action_ms = None
        self._hard_stop_playback()
        self.lock_review_focus(False)
        self.btn_review.setEnabled(True)
        self.btn_stop.setEnabled(False)
        self.update_execute_enabled()
        self._save_review_state()

    def _hard_stop_playback(self):
        try:
            self.player.stop()
        except Exception:
            logging.exception("VLC player.stop() raised")

    def play_current(self):
        f = self.video_files[self.current_index]["path"]
        logging.debug("play_current: index=%s path=%s", self.current_index, f)
        self._hard_stop_playback()
        try:
            media = self.vlc.media_new(f)
            self.player.set_media(media)
            try:
                media.release()
            except Exception:
                pass
            self.player.play()
            self.player.set_rate(self._effective_playback_rate())
        except Exception:
            logging.exception("VLC error in play_current: index=%s path=%s", self.current_index, f)
        self.auto_next_action_ms = None
        self.timer.start(300)
        QTimer.singleShot(100, self._log_vlc_state)
        QTimer.singleShot(200, self.update_timeline)
        QTimer.singleShot(400, self._initialize_auto_playback)
        self.files_table.selectRow(self.current_index)
        self.update_video_properties(self.current_index)
        self.video_frame.setFocus()
        self._update_volume_label()
        self._update_speed_label()

    def _log_vlc_state(self):
        try:
            state = self.player.get_state()
            logging.debug("VLC state 100ms post-play: index=%s state=%s", self.current_index, state)
            if str(state) in ("State.Error", "State.Ended", "State.NothingSpecial"):
                logging.warning("VLC unexpected state after play: index=%s state=%s path=%s",
                                self.current_index,
                                state,
                                self.video_files[self.current_index]["path"] if 0 <= self.current_index < len(self.video_files) else "?")
        except Exception:
            logging.exception("VLC error in _log_vlc_state")

    # =========================
    # TIMELINE
    # =========================

    def update_timeline(self):
        global _timeline_tick
        try:
            length = self.player.get_length()
            time = self.player.get_time()
            position = self.player.get_position()
        except Exception:
            logging.exception("VLC error reading playback state in update_timeline")
            return
        _timeline_tick += 1
        if _timeline_tick % 20 == 0:
            state = self.player.get_state()
            logging.debug(
                "timeline heartbeat: index=%s state=%s time=%s length=%s",
                self.current_index, state, time, length,
            )
        if position >= 0:
            self.timeline.setValue(int(position * 1000))
        if length > 0:
            self.time_label.setText(
                f"{self._format_time(time)} / {self._format_time(length)}"
            )
        else:
            self.time_label.setText(
                f"{self._format_time(time)} / --:--:--"
            )
        self._process_auto_review(time, length)
        self._update_speed_label()
        self._update_volume_label()

    def seek_from_slider(self, value):
        length = self.player.get_length()
        if length > 0:
            self.player.set_time(int(length * value / 1000))
            self._reset_auto_cycle()

    def toggle_auto_review(self, checked):
        self.auto_review_enabled = checked
        self.player.set_rate(self._effective_playback_rate())
        if checked:
            self._reset_auto_cycle()
        else:
            self.auto_next_action_ms = None

    def set_auto_play_seconds(self, value):
        self.auto_play_seconds = float(value)
        self._reset_auto_cycle()

    def set_auto_jump_minutes(self, value):
        self.auto_jump_minutes = value
        self._reset_auto_cycle()

    def set_auto_playback_rate(self, value):
        self.auto_playback_rate = value / 100.0
        self.player.set_rate(self._effective_playback_rate())
        self._update_speed_label()

    def _initialize_auto_playback(self):
        if not self.review_active:
            return
        logging.debug("_initialize_auto_playback: index=%s is_playing=%s", self.current_index, self.player.is_playing())
        if not self.auto_review_enabled:
            self._reset_auto_cycle()
            return
        if not self.player.is_playing():
            return
        length = self.player.get_length()
        if length <= 0:
            QTimer.singleShot(300, self._initialize_auto_playback)
            return
        start_time = min(60000, max(0, length - 250))
        self.player.set_time(int(start_time))
        self.player.set_rate(self._effective_playback_rate())
        self._reset_auto_cycle()

    def _reset_auto_cycle(self):
        if not self.auto_review_enabled or not self.review_active:
            self.auto_next_action_ms = None
            return
        current_time = self.player.get_time()
        if current_time is None or current_time < 0:
            return
        self.auto_next_action_ms = current_time + (self.auto_play_seconds * 1000)

    def _process_auto_review(self, current_time, length):
        if not self.auto_review_enabled or not self.review_active:
            return
        if self.current_index < 0:
            return
        if not self.player.is_playing():
            return
        if current_time is None or current_time < 0:
            return
        if self.auto_next_action_ms is None:
            self._reset_auto_cycle()
            return
        if current_time < self.auto_next_action_ms:
            return

        jump_ms = self.auto_jump_minutes * 60 * 1000
        if length > 0:
            target_time = min(max(0, current_time + jump_ms), max(0, length - 250))
        else:
            target_time = max(0, current_time + jump_ms)

        logging.debug("auto-jump: index=%s current_time=%s target_time=%s length=%s", self.current_index, current_time, target_time, length)
        self.player.set_time(int(target_time))
        self.player.set_rate(self._effective_playback_rate())
        self.auto_next_action_ms = int(target_time) + (self.auto_play_seconds * 1000)

    def _effective_playback_rate(self):
        return self.auto_playback_rate if self.auto_review_enabled else self.playback_rate

    def _format_time(self, ms_value):
        total_seconds = max(0, int(ms_value // 1000))
        hours = total_seconds // 3600
        minutes = (total_seconds % 3600) // 60
        seconds = total_seconds % 60
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"

    # =========================
    # KEYBOARD
    # =========================

    def eventFilter(self, obj, event):
        if event.type() == QEvent.KeyPress:
            if self.review_active:
                self.handle_review_key(event)
                return True
            if event.key() == Qt.Key_U and self.video_files:
                selected_row = self._get_selected_row()
                if selected_row is not None:
                    self.unmark_and_replay(selected_row)
                    return True
        return super().eventFilter(obj, event)

    def handle_review_key(self, e: QKeyEvent):
        if self.current_index < 0:
            return

        selected_row = self._get_selected_row()
        target_row = selected_row if selected_row is not None else self.current_index
        advance = target_row == self.current_index

        if e.key() == Qt.Key_D or e.key() == Qt.Key_Delete:
            self.mark("DELETE", target_row, advance)
        elif e.key() == Qt.Key_M:
            self.mark("MOVE", target_row, advance)
        elif e.key() == Qt.Key_U:
            self.unmark_and_replay(target_row)
        elif e.key() == Qt.Key_Space:
            self.player.pause()
        elif e.key() == Qt.Key_Right:
            delta_ms = 300000 if e.modifiers() & Qt.ShiftModifier else 5000
            self.adjust_time(delta_ms)
        elif e.key() == Qt.Key_Left:
            delta_ms = -300000 if e.modifiers() & Qt.ShiftModifier else -5000
            self.adjust_time(delta_ms)
        elif e.key() in (Qt.Key_Plus, Qt.Key_Equal):
            self.playback_rate = min(3.0, self.playback_rate + 0.1)
            self.player.set_rate(self.playback_rate)
            self._update_speed_label()
        elif e.key() == Qt.Key_Minus:
            self.playback_rate = max(0.5, self.playback_rate - 0.1)
            self.player.set_rate(self.playback_rate)
            self._update_speed_label()
        elif e.key() == Qt.Key_R:
            self.playback_rate = 1.0
            self.player.set_rate(1.0)
            self._update_speed_label()
        elif e.key() == Qt.Key_V:
            self.toggle_mute()
        elif e.key() == Qt.Key_Up:
            self.adjust_volume(5)
        elif e.key() == Qt.Key_Down:
            self.adjust_volume(-5)

    def handle_review_click(self, event: QMouseEvent):
        if self.current_index < 0 or not self._is_click_on_video(event):
            return False

        selected_row = self._get_selected_row()
        target_row = selected_row if selected_row is not None else self.current_index
        advance = target_row == self.current_index

        if event.button() == Qt.LeftButton:
            self.mark("MOVE", target_row, advance)
            return True
        if event.button() == Qt.RightButton:
            self.mark("DELETE", target_row, advance)
            return True
        return False

    def _is_click_on_video(self, event: QMouseEvent):
        if self.video_frame is None or not self.video_frame.isVisible():
            return False
        global_pos = event.globalPosition().toPoint()
        local_pos = self.video_frame.mapFromGlobal(global_pos)
        return self.video_frame.rect().contains(local_pos)

    def _is_cursor_on_video(self):
        if self.video_frame is None or not self.video_frame.isVisible():
            return False
        local_pos = self.video_frame.mapFromGlobal(QCursor.pos())
        return self.video_frame.rect().contains(local_pos)

    def _mouse_button_is_down(self, virtual_key):
        return bool(ctypes.windll.user32.GetAsyncKeyState(virtual_key) & 0x8000)

    def _poll_review_mouse(self):
        if not self.review_active:
            self._left_mouse_down = False
            self._right_mouse_down = False
            return

        left_down = self._mouse_button_is_down(VK_LBUTTON)
        right_down = self._mouse_button_is_down(VK_RBUTTON)
        cursor_on_video = self._is_cursor_on_video()

        if cursor_on_video and left_down and not self._left_mouse_down:
            self.handle_review_mouse_action(Qt.LeftButton)
        elif cursor_on_video and right_down and not self._right_mouse_down:
            self.handle_review_mouse_action(Qt.RightButton)

        self._left_mouse_down = left_down
        self._right_mouse_down = right_down

    def handle_review_mouse_action(self, button):
        if self.current_index < 0:
            return

        selected_row = self._get_selected_row()
        target_row = selected_row if selected_row is not None else self.current_index
        advance = target_row == self.current_index

        if button == Qt.LeftButton:
            self.mark("DELETE", target_row, advance)
        elif button == Qt.RightButton:
            self.mark("MOVE", target_row, advance)

    def adjust_time(self, delta_ms):
        length = self.player.get_length()
        if length <= 0:
            return
        new_time = max(0, min(length, self.player.get_time() + delta_ms))
        self.player.set_time(new_time)
        self._reset_auto_cycle()

    def adjust_volume(self, delta):
        current = self.player.audio_get_volume()
        if current < 0:
            current = 100
        if self.is_muted:
            self.is_muted = False
        new_volume = max(0, min(100, current + delta))
        self.player.audio_set_volume(new_volume)
        self.last_volume = new_volume
        self._update_volume_label()

    def toggle_mute(self):
        if self.is_muted:
            self.is_muted = False
            self.player.audio_set_volume(self.last_volume)
        else:
            self.is_muted = True
            current = self.player.audio_get_volume()
            if current > 0:
                self.last_volume = current
            self.player.audio_set_volume(0)
        self._update_volume_label()

    def _update_volume_label(self):
        if self.is_muted:
            self.volume_label.setText("VOL: MUTED")
        else:
            current = self.player.audio_get_volume()
            if current < 0:
                current = 100
            self.volume_label.setText(f"VOL: {current}%")

    def _update_speed_label(self):
        self.speed_label.setText(f"SPEED: {self._effective_playback_rate():.1f}x")

    def lock_review_focus(self, locked):
        self.folder_tree.setFocusPolicy(Qt.NoFocus if locked else Qt.ClickFocus)
        self.files_table.setFocusPolicy(Qt.NoFocus if locked else Qt.ClickFocus)
        self.timeline.setFocusPolicy(Qt.NoFocus if locked else Qt.StrongFocus)
        if locked:
            self.video_frame.setFocus()

    def _apply_row_color(self, row, decision):
        if decision == "MOVE":
            fg = QColor(74, 222, 128)   # green-400 — bright, readable on dark or light
        elif decision == "DELETE":
            fg = QColor(248, 113, 113)  # red-400 — bright, readable on dark or light
        else:
            return
        bold = QFont()
        bold.setBold(True)
        default_bg = QColor(30, 41, 59) if self.dark_mode else QColor(255, 255, 255)
        for col in range(self.files_table.columnCount()):
            item = self.files_table.item(row, col)
            if item is not None:
                item.setForeground(fg)
                item.setFont(bold)
                item.setBackground(default_bg)

    def _clear_row_color(self, row):
        bg = QColor(30, 41, 59)    if self.dark_mode else QColor(255, 255, 255)
        fg = QColor(226, 232, 240) if self.dark_mode else QColor(30, 41, 59)
        normal = QFont()
        normal.setBold(False)
        for col in range(self.files_table.columnCount()):
            item = self.files_table.item(row, col)
            if item is not None:
                item.setBackground(bg)
                item.setForeground(fg)
                item.setFont(normal)

    def _update_row_colors(self):
        for row in range(self.files_table.rowCount()):
            if row in self.decisions:
                self._apply_row_color(row, self.decisions[row])
            else:
                self._clear_row_color(row)

    def _is_subpath(self, child, parent):
        if not parent:
            return False
        child_abs = os.path.normcase(os.path.abspath(child))
        parent_abs = os.path.normcase(os.path.abspath(parent))
        try:
            return os.path.commonpath([child_abs, parent_abs]) == parent_abs
        except ValueError:
            return False

    def _is_subpath_any(self, child, parents):
        for parent in parents or []:
            if self._is_subpath(child, parent):
                return True
        return False

    def _set_root_folders(self, paths):
        normalized = []
        seen = set()
        for path in paths:
            abs_path = os.path.normcase(os.path.abspath(path))
            if abs_path in seen:
                continue
            seen.add(abs_path)
            normalized.append(path)
        self.root_folders = normalized
        if not self.root_folders:
            self.root_label.setText("Roots: Not set")
            self.root_label.setToolTip("")
            return
        if len(self.root_folders) == 1:
            label = f"Roots: {self.root_folders[0]}"
        else:
            label = f"Roots: {len(self.root_folders)} selected"
        self.root_label.setText(label)
        self.root_label.setToolTip("\n".join(self.root_folders))

    def _get_root_drive(self):
        if not self.root_folders:
            return ""
        drives = set()
        for root in self.root_folders:
            drive, _ = os.path.splitdrive(os.path.abspath(root))
            if drive:
                drives.add(drive)
        if len(drives) != 1:
            return ""
        return sorted(drives)[0]

    def update_execute_enabled(self):
        if self.review_active:
            self.btn_exec.setEnabled(False)
            return
        if not self.root_folders:
            self.btn_exec.setEnabled(False)
            return
        if not self.dest_folder or not self.trash_folder:
            if not self.permanent_delete_enabled:
                self.btn_exec.setEnabled(False)
                return
        if self._is_subpath_any(self.dest_folder, self.root_folders):
            self.btn_exec.setEnabled(False)
            return
        if self.trash_folder and self._is_subpath_any(self.trash_folder, self.root_folders):
            self.btn_exec.setEnabled(False)
            return
        if self.trash_folder and os.path.normcase(os.path.abspath(self.dest_folder)) == os.path.normcase(os.path.abspath(self.trash_folder)):
            self.btn_exec.setEnabled(False)
            return
        self.btn_exec.setEnabled(True)

    def _get_selected_row(self):
        selection = self.files_table.selectionModel()
        if selection is None or not selection.hasSelection():
            return None
        indexes = selection.selectedRows()
        if not indexes:
            return None
        return indexes[0].row()

    def _decision_for_row(self, row):
        return self.decisions.get(row, "UNMARKED")

    def _next_unmarked_index(self, start_row):
        for row in range(max(0, start_row), len(self.video_files)):
            if self._decision_for_row(row) == "UNMARKED":
                return row
        return None

    def apply_decision_filter(self):
        choice = self.filter_combo.currentText()
        for row in range(self.files_table.rowCount()):
            decision = self._decision_for_row(row)
            show_row = choice == "ALL" or decision == choice
            self.files_table.setRowHidden(row, not show_row)

    def mark(self, decision, row, advance):
        self.decisions[row] = decision
        self.files_table.item(row, self._files_decision_col()).setText(decision)
        self._apply_row_color(row, decision)
        self.update_summary()
        logging.info("Marked: index=%s decision=%s path=%s", row, decision,
                     self.video_files[row]["path"])
        if advance:
            next_row = self._next_unmarked_index(self.current_index + 1)
            if next_row is not None:
                self.current_index = next_row
                self._save_review_state()   # single save before play (crash-safe)
                self.play_current()
            else:
                self.timer.stop()
                self.stop_review()
        else:
            self._save_review_state()       # only save when not advancing
        self.apply_decision_filter()

    def unmark_and_replay(self, row):
        if row is None or row < 0 or row >= len(self.video_files):
            return
        if row in self.decisions:
            del self.decisions[row]
        self.files_table.item(row, self._files_decision_col()).setText("UNMARKED")
        self._clear_row_color(row)
        self.update_summary()
        self.apply_decision_filter()
        if not self.review_active:
            self.review_active = True
            self.lock_review_focus(True)
            self.btn_review.setEnabled(False)
            self.btn_stop.setEnabled(True)
            self.update_execute_enabled()
        self.current_index = row
        self._save_review_state()
        self.play_current()
        logging.info("Unmarked and replayed: index=%s path=%s", row, self.video_files[row]["path"])

    def update_summary(self):
        move = sum(1 for d in self.decisions.values() if d == "MOVE")
        delete = sum(1 for d in self.decisions.values() if d == "DELETE")
        unmarked = len(self.video_files) - len(self.decisions)
        size_move = sum(self.video_files[i]["size"] for i, d in self.decisions.items() if d == "MOVE")
        size_delete = sum(self.video_files[i]["size"] for i, d in self.decisions.items() if d == "DELETE")
        size_unmarked = sum(
            f["size"] for i, f in enumerate(self.video_files) if i not in self.decisions
        )
        self.lbl_move.setText(f"✓  MOVE\n{move}  ({size_move:.2f} GB)")
        self.lbl_delete.setText(f"✕  DELETE\n{delete}  ({size_delete:.2f} GB)")
        self.lbl_unmarked.setText(f"—  UNMARKED\n{unmarked}  ({size_unmarked:.2f} GB)")
        # Debounce: rebuild quality tables 200 ms after the last rapid mark
        self._quality_timer.start(200)

    # =========================
    # EXECUTE
    # =========================

    def execute_actions(self):
        if not self.btn_exec.isEnabled():
            QMessageBox.warning(self, "Error", "Execute is not available yet")
            return
        self._hard_stop_playback()
        self.timer.stop()

        stats = {
            "MOVE": {"count": 0, "size": 0.0},
            "DELETE": {"count": 0, "size": 0.0},
        }
        for idx, decision in self.decisions.items():
            size = self.video_files[idx]["size"]
            stats[decision]["count"] += 1
            stats[decision]["size"] += size

        unmarked = len(self.video_files) - len(self.decisions)
        unmarked_size = sum(
            f["size"] for i, f in enumerate(self.video_files) if i not in self.decisions
        )
        errors = []
        if stats["MOVE"]["count"] > 0 and not self.dest_folder:
            errors.append("Destination not set for MOVE actions.")
        if stats["DELETE"]["count"] > 0 and not self.trash_folder and not self.permanent_delete_enabled:
            errors.append("Trash not set for DELETE actions.")
        if self.dest_folder and self.trash_folder:
            if os.path.normcase(os.path.abspath(self.dest_folder)) == os.path.normcase(os.path.abspath(self.trash_folder)):
                errors.append("Destination and Trash must be different folders.")
            if self._is_subpath_any(self.dest_folder, self.root_folders):
                errors.append("Destination cannot be inside root.")
            if self._is_subpath_any(self.trash_folder, self.root_folders):
                errors.append("Trash cannot be inside root.")
        if errors:
            QMessageBox.warning(self, "Error", "\n".join(errors))
            return

        summary_text = (
            "Execution summary:\n"
            f"MOVE: {stats['MOVE']['count']} files | {stats['MOVE']['size']:.2f} GB\n"
            f"DELETE: {stats['DELETE']['count']} files | {stats['DELETE']['size']:.2f} GB\n"
            f"UNMARKED: {unmarked} files | {unmarked_size:.2f} GB\n\n"
            f"Roots: {', '.join(self.root_folders)}\n"
            f"Destination: {self.dest_folder}\n"
            f"Delete mode: {'Permanent Delete' if self.permanent_delete_enabled else f'Trash -> {self.trash_folder}'}"
        )

        confirm = QMessageBox.question(
            self,
            "Confirm Execution",
            summary_text,
            QMessageBox.Yes | QMessageBox.No
        )
        if confirm != QMessageBox.Yes:
            return

        completed_roots = self._roots_fully_marked_for_execute()
        self._start_execute_worker(stats, unmarked, completed_roots)

    def _start_execute_worker(self, stats, unmarked, completed_roots):
        if self.exec_worker is not None:
            QMessageBox.warning(self, "Busy", "Execution already running")
            return

        if self.trash_folder:
            os.makedirs(self.trash_folder, exist_ok=True)

        actions = []
        for idx, decision in self.decisions.items():
            if decision not in ("MOVE", "DELETE"):
                continue
            actions.append({
                "src": self.video_files[idx]["path"],
                "decision": decision,
                "dest": self.dest_folder if decision == "MOVE" else self.trash_folder,
                "permanent_delete": decision == "DELETE" and self.permanent_delete_enabled,
            })

        total_actions = len(actions)
        self.progress.setMaximum(total_actions if total_actions > 0 else 1)
        self.progress.setValue(0)
        self.progress.setFormat("Moving %v/%m (%p%)")

        self.btn_exec.setEnabled(False)
        self.btn_review.setEnabled(False)
        self.btn_stop.setEnabled(False)

        self.exec_worker = ExecuteWorker(actions)
        self.exec_worker.progress.connect(self._on_exec_progress)
        self.exec_worker.error.connect(self._on_exec_error)
        self.exec_worker.finished.connect(
            lambda: self._on_exec_finished(stats, unmarked, completed_roots)
        )
        self.exec_worker.start()

    def _on_exec_progress(self, current, total):
        self.progress.setMaximum(total if total > 0 else 1)
        self.progress.setValue(current)

    def _on_exec_error(self, message):
        logging.error("Execution error: %s", message)

    def _on_exec_finished(self, stats, unmarked, completed_roots):
        self.exec_worker = None
        logging.info("Execution completed: move=%s delete=%s unmarked=%s",
                     stats["MOVE"]["count"], stats["DELETE"]["count"], unmarked)
        current_key = self._review_state_key()
        if current_key:
            self._delete_saved_state(current_key)
        self.start_scan()
        roots_deleted = self._confirm_and_delete_completed_roots(completed_roots)
        if self.root_folders:
            if roots_deleted:
                self.start_scan()
            QMessageBox.information(self, "Done", "Execution completed. Rescan finished.")
        else:
            self._clear_scan_results()
            QMessageBox.information(
                self,
                "Done",
                "Execution completed. Rescan found no remaining videos in the deleted root folders."
            )
        self.btn_review.setEnabled(bool(self.video_files))
        self.btn_stop.setEnabled(False)
        self.update_execute_enabled()
        self._save_review_state()

    def closeEvent(self, event):
        self._save_review_state()
        self.stop_review()
        super().closeEvent(event)

    def toggle_dark_mode(self, checked):
        self.dark_mode = checked
        self.btn_dark.setText("☀  Light" if checked else "🌙  Dark")
        self.apply_theme()

    def apply_theme(self):
        self._update_row_colors()
        dm = self.dark_mode

        # ── Colour tokens ──────────────────────────────────────────────────
        bg          = "#0F172A" if dm else "#F1F5F9"
        surface     = "#1E293B" if dm else "#FFFFFF"
        surface_alt = "#334155" if dm else "#F8FAFC"
        border      = "#334155" if dm else "#E2E8F0"
        border_inp  = "#475569" if dm else "#CBD5E1"
        text        = "#F1F5F9" if dm else "#1E293B"
        text_sec    = "#94A3B8" if dm else "#64748B"
        hover_bg    = "#334155" if dm else "#F1F5F9"
        hover_bd    = "#64748B" if dm else "#94A3B8"
        active_bg   = "#475569" if dm else "#E2E8F0"
        sel_bg      = "#1E3A5F" if dm else "#EFF6FF"
        sel_fg      = "#93C5FD" if dm else "#1D4ED8"
        btn_fg      = "#CBD5E1" if dm else "#334155"
        ck_bg       = "#1E3A5F" if dm else "#EFF6FF"
        ck_bd       = "#60A5FA" if dm else "#3B82F6"
        ck_fg       = "#93C5FD" if dm else "#1D4ED8"
        prog_bg     = "#334155" if dm else "#E2E8F0"
        scr_h       = "#475569" if dm else "#CBD5E1"
        scr_hv      = "#64748B" if dm else "#94A3B8"
        dk_btn_bg   = "#334155" if dm else "#F1F5F9"
        dk_btn_bd   = "#475569" if dm else "#CBD5E1"
        dk_btn_fg   = "#F1F5F9" if dm else "#475569"
        dk_btn_hv   = "#475569" if dm else "#E2E8F0"
        ghost_fg    = text_sec
        ghost_hv_fg = "#60A5FA" if dm else "#2563EB"
        ghost_hv_bg = "#1E3A5F" if dm else "#EFF6FF"
        unmarked_bg = "#334155" if dm else "#475569"

        self.setStyleSheet(f"""
            QMainWindow, QDialog {{ background: {bg}; }}
            QWidget {{
                font-family: 'Segoe UI', 'Roboto', Arial, sans-serif;
                font-size: 13px;
                color: {text};
            }}

            /* ── Buttons – base ── */
            QPushButton {{
                background: {surface};
                border: 1.5px solid {border_inp};
                border-radius: 7px;
                padding: 5px 14px;
                color: {btn_fg};
                font-weight: 500;
                min-height: 28px;
            }}
            QPushButton:hover   {{ background: {hover_bg}; border-color: {hover_bd}; }}
            QPushButton:pressed {{ background: {active_bg}; }}
            QPushButton:disabled {{ background: {surface_alt}; border-color: {border}; color: {text_sec}; }}
            QPushButton:checked {{ background: {ck_bg}; border-color: {ck_bd}; color: {ck_fg}; }}
            QPushButton:checked:hover {{ background: {active_bg}; }}

            /* ── Named variants (fixed colours, same in both modes) ── */
            QPushButton#btn_primary {{
                background: #2563EB; border-color: #2563EB; color: #FFFFFF; font-weight: 600;
            }}
            QPushButton#btn_primary:hover    {{ background: #1D4ED8; border-color: #1D4ED8; }}
            QPushButton#btn_primary:pressed   {{ background: #1E40AF; }}
            QPushButton#btn_primary:disabled  {{ background: #BFDBFE; border-color: #BFDBFE; color: #FFFFFF; }}

            QPushButton#btn_danger {{
                background: #DC2626; border-color: #DC2626; color: #FFFFFF; font-weight: 600;
            }}
            QPushButton#btn_danger:hover     {{ background: #B91C1C; border-color: #B91C1C; }}
            QPushButton#btn_danger:disabled  {{ background: #FECACA; border-color: #FECACA; color: #FFFFFF; }}

            QPushButton#btn_success {{
                background: #15803D; border-color: #15803D; color: #FFFFFF; font-weight: 600;
            }}
            QPushButton#btn_success:hover    {{ background: #166534; border-color: #166534; }}
            QPushButton#btn_success:disabled {{ background: #BBF7D0; border-color: #BBF7D0; color: #FFFFFF; }}

            QPushButton#btn_ghost {{
                background: transparent; border-color: transparent; color: {ghost_fg};
            }}
            QPushButton#btn_ghost:hover {{
                color: {ghost_hv_fg}; background: {ghost_hv_bg}; border-color: {ghost_hv_bg};
            }}

            QPushButton#btn_dark_toggle {{
                background: {dk_btn_bg}; border: 1.5px solid {dk_btn_bd};
                border-radius: 14px; padding: 4px 14px;
                color: {dk_btn_fg}; font-weight: 600; min-width: 90px;
            }}
            QPushButton#btn_dark_toggle:hover {{ background: {dk_btn_hv}; }}

            /* ── Labels ── */
            QLabel {{ color: {text}; background: transparent; }}

            /* ── Tables ── */
            QTableWidget {{
                background: {surface};
                gridline-color: {surface_alt};
                border: 1px solid {border};
                border-radius: 8px;
                outline: none;
            }}
            QTableWidget::item {{ padding: 5px 8px; border: none; }}
            QTableWidget::item:selected {{ background: {sel_bg}; color: {sel_fg}; }}
            QTableWidget::item:hover    {{ background: {hover_bg}; }}

            /* ── Tree ── */
            QTreeWidget {{
                background: {surface};
                border: 1px solid {border};
                border-radius: 8px;
                outline: none;
                color: {text};
            }}
            QTreeWidget::item {{ padding: 3px 6px; color: {text}; }}
            QTreeWidget::item:selected {{ background: {sel_bg}; color: {sel_fg}; }}
            QTreeWidget::item:hover    {{ background: {hover_bg}; }}

            /* ── Headers ── */
            QHeaderView::section {{
                background: {surface_alt};
                padding: 7px 8px;
                border: none;
                border-bottom: 1.5px solid {border};
                font-weight: 700; font-size: 11px;
                color: {text_sec}; letter-spacing: 0.4px;
            }}
            QHeaderView {{ background: transparent; }}

            /* ── Slider ── */
            QSlider::groove:horizontal {{ height: 4px; background: {border}; border-radius: 2px; }}
            QSlider::handle:horizontal {{
                background: #2563EB; border: none;
                width: 14px; height: 14px; margin: -5px 0; border-radius: 7px;
            }}
            QSlider::sub-page:horizontal {{ background: #2563EB; border-radius: 2px; }}

            /* ── Progress bars (quality table – thin) ── */
            QProgressBar {{
                border: none; background: {prog_bg};
                border-radius: 5px; text-align: center;
                font-size: 11px; color: {text_sec};
                min-height: 10px; max-height: 10px;
            }}
            QProgressBar::chunk {{ background: #2563EB; border-radius: 5px; }}

            /* ── ComboBox ── */
            QComboBox {{
                background: {surface}; border: 1.5px solid {border_inp};
                border-radius: 7px; padding: 4px 10px; min-height: 28px; color: {text};
            }}
            QComboBox:hover {{ border-color: #2563EB; }}
            QComboBox::drop-down {{ border: none; width: 20px; }}
            QComboBox QAbstractItemView {{
                background: {surface}; border: 1px solid {border};
                selection-background-color: {sel_bg}; selection-color: {sel_fg};
                color: {text}; outline: none;
            }}

            /* ── SpinBox ── */
            QSpinBox, QDoubleSpinBox {{
                background: {surface}; border: 1.5px solid {border_inp};
                border-radius: 7px; padding: 4px 8px; min-height: 28px; color: {text};
            }}
            QSpinBox:hover, QDoubleSpinBox:hover {{ border-color: #2563EB; }}

            /* ── CheckBox ── */
            QCheckBox {{ spacing: 7px; color: {text}; }}
            QCheckBox::indicator {{
                width: 17px; height: 17px; border-radius: 4px;
                border: 2px solid {border_inp}; background: {surface};
            }}
            QCheckBox::indicator:checked {{ background: #2563EB; border-color: #2563EB; }}
            QCheckBox::indicator:hover   {{ border-color: #2563EB; }}

            /* ── Splitter ── */
            QSplitter::handle            {{ background: {border}; }}
            QSplitter::handle:horizontal {{ width: 2px; }}
            QSplitter::handle:vertical   {{ height: 2px; }}

            /* ── Scrollbars ── */
            QScrollBar:vertical   {{ background: transparent; width: 8px; border-radius: 4px; }}
            QScrollBar::handle:vertical {{
                background: {scr_h}; border-radius: 4px; min-height: 20px;
            }}
            QScrollBar::handle:vertical:hover {{ background: {scr_hv}; }}
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{ height: 0; }}
            QScrollBar:horizontal {{ background: transparent; height: 8px; border-radius: 4px; }}
            QScrollBar::handle:horizontal {{ background: {scr_h}; border-radius: 4px; }}
            QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {{ width: 0; }}

            /* ── MessageBox ── */
            QMessageBox {{ background: {surface}; }}
            QMessageBox QLabel {{ color: {text}; font-size: 13px; }}
            QMessageBox QPushButton {{ min-width: 80px; min-height: 32px; }}

            /* ── Status bar ── */
            QFrame#status_bar {{
                background: {surface};
                border-top: 1.5px solid {border};
                min-height: 56px; max-height: 56px;
            }}
            QProgressBar#scan_progress {{
                min-height: 28px; max-height: 28px;
                border-radius: 6px; font-size: 12px; font-weight: 600;
                color: #FFFFFF; background: {prog_bg};
            }}
            QProgressBar#scan_progress::chunk {{ border-radius: 6px; background: #2563EB; }}

            /* ── Stat chips (fixed vivid colours, readable in both modes) ── */
            QLabel#stat_move {{
                background: #16A34A; color: #FFFFFF;
                border-radius: 10px; padding: 6px 10px;
                font-size: 14px; font-weight: 700; min-height: 38px;
            }}
            QLabel#stat_delete {{
                background: #DC2626; color: #FFFFFF;
                border-radius: 10px; padding: 6px 10px;
                font-size: 14px; font-weight: 700; min-height: 38px;
            }}
            QLabel#stat_unmarked {{
                background: {unmarked_bg}; color: #FFFFFF;
                border-radius: 10px; padding: 6px 10px;
                font-size: 14px; font-weight: 700; min-height: 38px;
            }}

            /* ── Line edit (used in file dialog "Directory:" field etc.) ── */
            QLineEdit {{
                background: {surface};
                border: 1.5px solid {border_inp};
                border-radius: 6px;
                padding: 4px 8px;
                color: {text};
                min-height: 26px;
                selection-background-color: {sel_bg};
                selection-color: {sel_fg};
            }}
            QLineEdit:hover  {{ border-color: #2563EB; }}
            QLineEdit:focus  {{ border-color: #2563EB; }}

            /* ── Generic item views (QListView / QTreeView inside QFileDialog) ──
               Use ::viewport for the background so per-item setBackground() is
               never overridden by a widget-level background rule.              ── */
            QAbstractItemView {{
                border: 1px solid {border};
                outline: none;
                selection-background-color: {sel_bg};
                selection-color: {sel_fg};
            }}
            QAbstractItemView::viewport {{
                background: {surface};
            }}
            QAbstractItemView::item {{
                padding: 3px 6px;
            }}
            QAbstractItemView::item:selected {{
                background: {sel_bg};
                color: {sel_fg};
            }}
            QAbstractItemView::item:hover {{
                background: {hover_bg};
            }}

            /* ── File dialog toolbar (navigation buttons row) ── */
            QToolBar {{
                background: {surface_alt};
                border: none;
                spacing: 4px;
                padding: 2px 4px;
            }}
            QToolButton {{
                background: transparent;
                border: 1px solid transparent;
                border-radius: 5px;
                padding: 3px;
                color: {text};
            }}
            QToolButton:hover  {{ background: {hover_bg}; border-color: {border}; }}
            QToolButton:pressed {{ background: {active_bg}; }}

            /* ── File dialog "Look in:" combo (sidebar combo) ── */
            QFileDialog QComboBox {{
                background: {surface};
                border: 1.5px solid {border_inp};
                border-radius: 6px;
                padding: 4px 10px;
                color: {text};
                min-height: 26px;
            }}

            /* ── File dialog frame / splitter ── */
            QFileDialog QFrame {{
                background: {bg};
            }}
            QFileDialog QSplitter::handle {{
                background: {border};
            }}

            /* ── Sidebar tree / file list inside file dialog ── */
            QFileDialog QTreeView {{ border: none; color: {text}; }}
            QFileDialog QTreeView::viewport {{ background: {surface_alt}; }}
            QFileDialog QListView {{ border: none; color: {text}; }}
            QFileDialog QListView::viewport {{ background: {surface}; }}
        """)


class DecisionColorDelegate(QStyledItemDelegate):
    """Forces item BackgroundRole / ForegroundRole to render correctly even
    when a QSS rule on the parent view would otherwise override them."""

    def initStyleOption(self, option, index):
        super().initStyleOption(option, index)
        bg = index.data(Qt.ItemDataRole.BackgroundRole)
        fg = index.data(Qt.ItemDataRole.ForegroundRole)
        if bg is not None:
            option.backgroundBrush = bg if isinstance(bg, QBrush) else QBrush(bg)
        if fg is not None:
            color = fg.color() if isinstance(fg, QBrush) else fg
            if color.isValid():
                pal = QPalette(option.palette)
                pal.setColor(QPalette.ColorRole.Text, color)
                option.palette = pal


class ScanWorker(QThread):
    progress = Signal(int, int)
    finished = Signal(list)

    def __init__(self, all_files):
        super().__init__()
        self.all_files = all_files
        self._cancelled = False

    def cancel(self):
        self._cancelled = True

    def run(self):
        results = []
        total = len(self.all_files)
        for i, file_info in enumerate(self.all_files, 1):
            if self._cancelled:
                return
            width, height, duration_sec = get_video_metadata(file_info["path"])
            category = get_video_category(width, height)
            quality = f"{height}p" if height and height > 0 else "Unknown"
            results.append({
                "path": file_info["path"],
                "folder": file_info["folder"],
                "size_bytes": file_info["size_bytes"],
                "name": os.path.basename(file_info["path"]),
                "size": file_info["size_bytes"] / (1024 ** 3),
                "width": width,
                "height": height,
                "duration_sec": duration_sec,
                "category": category,
                "quality": quality,
            })
            self.progress.emit(i, total)
        self.finished.emit(results)


class ExecuteWorker(QThread):
    progress = Signal(int, int)
    error = Signal(str)

    def __init__(self, actions):
        super().__init__()
        self.actions = actions

    def run(self):
        total = len(self.actions)
        moved = 0
        for action in self.actions:
            try:
                if action.get("permanent_delete"):
                    os.remove(action["src"])
                else:
                    shutil.move(action["src"], action["dest"])
            except Exception as ex:
                self.error.emit(f"{action['src']} -> {action['dest']}: {ex}")
            moved += 1
            self.progress.emit(moved, total)

# =========================
# RUN
# =========================

if __name__ == "__main__":
    app = QApplication(sys.argv)
    win = MediaReviewApp()
    win.show()
    sys.exit(app.exec())
