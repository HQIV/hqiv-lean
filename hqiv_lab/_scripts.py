"""Locate ``scripts/`` for HQIV Lean-aligned mirrors (single-repo layout)."""

from __future__ import annotations

import sys
from pathlib import Path

_SCRIPTS: Path | None = None


def scripts_dir() -> Path:
    global _SCRIPTS
    if _SCRIPTS is None:
        _SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
    return _SCRIPTS


def ensure_scripts_on_path() -> Path:
    root = str(scripts_dir())
    if root not in sys.path:
        sys.path.insert(0, root)
    return scripts_dir()
