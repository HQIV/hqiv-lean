"""Tests for optional Qiskit quantum metrics."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

pytest.importorskip("qiskit")

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from quantum_circuit_metrics import quantum_metrics_for_n  # noqa: E402


def test_quantum_metrics_n15() -> None:
    m = quantum_metrics_for_n(15, decompose_reps=0, opt_level=0)
    assert m["n"] == 15
    assert m["coarse_depth_ratio"] > 1.5
    assert m["coarse_qubit_delta"] > 0
