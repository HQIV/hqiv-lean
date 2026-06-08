#!/usr/bin/env python3
"""Qiskit circuit metrics for Shor layout comparison (optional dependency)."""

from __future__ import annotations

import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))


def qiskit_available() -> bool:
    try:
        import qiskit  # noqa: F401

        return True
    except ImportError:
        return False


def quantum_metrics_for_n(
    n: int,
    *,
    decompose_reps: int = 0,
    opt_level: int = 1,
    compare_layouts: bool = True,
) -> dict[str, Any]:
    """
    Return transpiled depth/qubit metrics for textbook vs sparse Shor layouts.

    Raises ImportError if qiskit is not installed.
    """
    if not qiskit_available():
        raise ImportError("qiskit is required for quantum metrics (pip install qiskit)")

    from orthogonal_diagonal_qiskit_poc import compare_one

    row = compare_one(
        n,
        decompose_reps=decompose_reps,
        opt_level=opt_level,
        compare_layouts=compare_layouts,
        gate_decompose_reps=1,
        gate_opt_level=3,
    )
    out = asdict(row)
    out["decompose_reps"] = decompose_reps
    out["opt_level"] = opt_level
    out["gate_decompose_reps"] = 1
    out["gate_opt_level"] = 3
    return out
