# -*- mode: python ; coding: utf-8 -*-
from pathlib import Path
from PyInstaller.utils.hooks import collect_all

project_dir = Path.cwd()
venv_site_packages = project_dir / ".venv" / "Lib" / "site-packages"

datas = []
binaries = []
hiddenimports = ["vlc"]

for package_name in ("PySide6", "shiboken6"):
    pkg_datas, pkg_binaries, pkg_hiddenimports = collect_all(
        package_name,
        include_py_files=True,
    )
    datas += pkg_datas
    binaries += pkg_binaries
    hiddenimports += pkg_hiddenimports

# Bundle VLC so the frozen app finds libvlc.dll and plugins/ in sys._MEIPASS,
# which is where the source points PYTHON_VLC_LIB_PATH / VLC_PLUGIN_PATH.
vlc_dir = Path(r"C:\Program Files\VideoLAN\VLC")
binaries += [
    (str(vlc_dir / "libvlc.dll"), "."),
    (str(vlc_dir / "libvlccore.dll"), "."),
]
for _plugin in (vlc_dir / "plugins").rglob("*.dll"):
    binaries.append((str(_plugin), str(_plugin.parent.relative_to(vlc_dir))))

a = Analysis(
    ['media review tool.py'],
    pathex=[str(project_dir), str(venv_site_packages)],
    binaries=binaries,
    datas=datas,
    hiddenimports=hiddenimports,
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='media review tool',
    version='version_info.txt',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
)
