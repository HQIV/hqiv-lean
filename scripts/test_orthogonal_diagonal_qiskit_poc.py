"""Smoke tests for real-modexp Shor PoC (requires qiskit)."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

pytest.importorskip("qiskit")

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from orthogonal_diagonal_qiskit_poc import (  # noqa: E402
    build_orthogonal_diagonal_circuit,
    build_textbook_shor_circuit,
    compare_one,
    run_suite,
)
from shor_modexp import build_modular_exponentiation, choose_coprime_base  # noqa: E402


@pytest.mark.parametrize("n", [15, 143])
def test_modexp_builds(n: int) -> None:
    a = choose_coprime_base(n)
    qc = build_modular_exponentiation(n, a, num_counting_qubits=4, decompose_reps=1)
    assert qc.num_qubits >= 8


@pytest.mark.parametrize("n", [15, 143])
def test_sparse_shor_shallower_than_textbook(n: int) -> None:
    from qiskit import transpile

    tb = transpile(build_textbook_shor_circuit(n, decompose_reps=1), optimization_level=0)
    sp = transpile(
        build_orthogonal_diagonal_circuit(n, refined=False, decompose_reps=1),
        optimization_level=0,
    )
    assert sp.depth() < tb.depth()
    assert sp.num_qubits <= tb.num_qubits


def test_compare_one_row() -> None:
    row = compare_one(15, decompose_reps=1, compare_layouts=True)
    assert row.n == 15
    assert row.coarse_depth > 0
    assert row.refined_depth > 0
    assert row.coarse_depth_ratio > 1.0


def test_run_suite_json_shape() -> None:
    result = run_suite(max_bits=10, decompose_reps=1, compare_layouts=False)
    assert result["protocol"].startswith("orthogonal_diagonal_qiskit_poc/")
    assert len(result["rows"]) >= 1
