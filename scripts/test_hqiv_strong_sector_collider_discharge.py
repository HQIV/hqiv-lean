#!/usr/bin/env python3
"""Unit tests for strong-sector collider discharge witness."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

import hqiv_strong_sector_collider_discharge as dsc


def test_nonabelian_splitting_exact() -> None:
    assert abs(dsc.non_abelian_splitting_from_filter() - 2.25) < 1e-12


def test_petra_r23_near_unity() -> None:
    a = dsc.alpha_strong_running_lo(dsc.ALPHA_S_MZ, dsc.MZ_MEV, 35000.0 / 2.0)
    r = dsc.petra_r23_discharge(a, 35000.0)
    assert 0.9 < r < 1.05


def test_witness_all_pass() -> None:
    w = dsc.build_witness()
    assert w["summary"]["all_pass"] is True
    assert w["summary"]["pass"] == len(w["cases"])


def test_cli_strict() -> None:
    proc = subprocess.run(
        [sys.executable, str(SCRIPTS / "hqiv_strong_sector_collider_discharge.py"), "--strict"],
        cwd=dsc.ROOT,
        env={**os.environ, "PYTHONPATH": str(SCRIPTS)},
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, proc.stderr


if __name__ == "__main__":
    test_nonabelian_splitting_exact()
    test_petra_r23_near_unity()
    test_witness_all_pass()
    test_cli_strict()
    print("ok")
