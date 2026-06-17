#!/usr/bin/env python3
"""Unit tests for HEP collider refinement witness."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import hqiv_hep_collider_refinements as ref


def test_witness_all_pass() -> None:
    w = ref.build_witness()
    assert w["summary"]["all_pass"] is True


def test_cli_strict() -> None:
    proc = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "hqiv_hep_collider_refinements.py"), "--strict"],
        cwd=ROOT,
        env={"PYTHONPATH": str(ROOT / "scripts"), **dict()},
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr


if __name__ == "__main__":
    test_witness_all_pass()
    test_cli_strict()
    print("ok")
