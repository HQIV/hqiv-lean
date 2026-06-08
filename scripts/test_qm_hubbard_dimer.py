#!/usr/bin/env python3
"""Regression checks for `qm_hubbard_dimer.py`."""

from __future__ import annotations

import importlib.util
import math
from pathlib import Path

import numpy as np

_SCRIPTS = Path(__file__).resolve().parent
_MOD = _SCRIPTS / "qm_hubbard_dimer.py"
_spec = importlib.util.spec_from_file_location("qm_hubbard_dimer", _MOD)
assert _spec and _spec.loader
_hub = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_hub)


def test_lambda_shell_anchor_at_m4() -> None:
    lam = _hub.lambda_shell(4, lambda0=1.7, coherence=0.25)
    assert abs(lam - (1.7 * 0.25)) < 1e-12


def test_interaction_only_spectrum() -> None:
    lam = 0.8
    H = _hub.hubbard_dimer_hamiltonian(t_hop=0.0, lam=lam)
    e = np.sort(np.linalg.eigvalsh(H))
    np.testing.assert_allclose(e, np.array([-lam, -lam, lam, lam]), atol=1e-12, rtol=0.0)


def test_noninteracting_limit_matches_kronecker_sum() -> None:
    t_hop = 1.3
    H = _hub.hubbard_dimer_hamiltonian(t_hop=t_hop, lam=0.0)
    e = np.sort(np.linalg.eigvalsh(H))
    expected = np.array([-2.0 * t_hop, 0.0, 0.0, 2.0 * t_hop], dtype=np.float64)
    np.testing.assert_allclose(e, expected, atol=1e-12, rtol=0.0)


def test_time_evolution_is_unitary() -> None:
    H = _hub.hubbard_dimer_hamiltonian(t_hop=1.0, lam=0.6)
    U = _hub.exp_iHt(H, t=math.pi / 6.0)
    np.testing.assert_allclose(U.conj().T @ U, np.eye(4), atol=1e-10, rtol=0.0)
    np.testing.assert_allclose(U @ U.conj().T, np.eye(4), atol=1e-10, rtol=0.0)


def test_double_occupancy_projector_extremes() -> None:
    ops = _hub.observables()
    d = ops["double_occupancy_proxy"]
    uu = np.array([1.0, 0.0, 0.0, 0.0], dtype=np.complex128)
    dd = np.array([0.0, 0.0, 0.0, 1.0], dtype=np.complex128)
    assert abs(_hub.expectation(uu, d) - 0.0) < 1e-12
    assert abs(_hub.expectation(dd, d) - 1.0) < 1e-12


def test_scan_rows_and_gap_nonnegative() -> None:
    scan = _hub.shell_scan(
        m_start=2,
        m_end=8,
        t_hop=1.0,
        lambda0=0.8,
        coherence=1.0,
        time=math.pi / 5.0,
    )
    rows = scan["rows"]
    assert len(rows) == 7
    for row in rows:
        assert row["gap"] >= -1e-12
        assert -0.75 - 1e-9 <= row["spin_correlation"] <= 0.25 + 1e-9


def test_closed_form_spectrum_random_samples() -> None:
    # Exact spectrum for H = -t(σx⊗I + I⊗σx) + λ(σz⊗σz):
    #   { -sqrt(λ^2 + 4 t^2), -λ, λ, sqrt(λ^2 + 4 t^2) }.
    rng = np.random.default_rng(20260413)
    for _ in range(64):
        t_hop = float(rng.uniform(-2.5, 2.5))
        lam = float(rng.uniform(-3.0, 3.0))
        H = _hub.hubbard_dimer_hamiltonian(t_hop=t_hop, lam=lam)
        e_num = np.sort(np.linalg.eigvalsh(H))
        e0 = math.sqrt(lam * lam + 4.0 * t_hop * t_hop)
        e_exact = np.sort(np.array([-e0, -lam, lam, e0], dtype=np.float64))
        np.testing.assert_allclose(e_num, e_exact, atol=1e-10, rtol=0.0)


if __name__ == "__main__":
    test_lambda_shell_anchor_at_m4()
    test_interaction_only_spectrum()
    test_noninteracting_limit_matches_kronecker_sum()
    test_time_evolution_is_unitary()
    test_double_occupancy_projector_extremes()
    test_scan_rows_and_gap_nonnegative()
    test_closed_form_spectrum_random_samples()
    print("ok")
