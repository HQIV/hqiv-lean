"""Resolve `scripts/<name>` from repo root and run as __main__."""
from __future__ import annotations

import runpy
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
_SCRIPTS = _REPO_ROOT / "scripts"


def run_script(name: str) -> None:
    target = _SCRIPTS / name
    if not target.is_file():
        print(f"Missing: {target}", file=sys.stderr)
        sys.exit(2)
    sys.path.insert(0, str(_SCRIPTS))
    runpy.run_path(str(target), run_name="__main__")
