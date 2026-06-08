#!/usr/bin/env python3
"""Regression + reality checks for canonical half-filled Hubbard dimer."""

from __future__ import annotations

import importlib.util
import math
from pathlib import Path

import numpy as np

_SCRIPTS = Path(__file__).resolve().parent
_MOD = _SCRIPTS / "qm_hubbard_dimer_half_filled.py"
_spec = importlib.util.spec_from_file_location("qm_hubbard_dimer_half_filled", _MOD)
assert _spec and _spec.loader
_hub = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_hub)


def test_closed_form_spectrum_random_samples() -> None:
    rng = np.random.default_rng(20260413)
    for _ in range(64):
        t_hop = float(rng.uniform(-2.5, 2.5))
        U = float(rng.uniform(-4.0, 4.0))
        H = _hub.hubbard_half_filled_hamiltonian(t_hop=t_hop, U=U)
        e_num = np.sort(np.linalg.eigvalsh(H))
        e_exact = _hub.closed_form_eigenvalues(t_hop=t_hop, U=U)
        np.testing.assert_allclose(e_num, e_exact, atol=1e-10, rtol=0.0)


def test_repulsive_ground_state_is_antiferromagnetic() -> None:
    # Canonical reality check: repulsive half-filled dimer has AF tendency.
    H = _hub.hubbard_half_filled_hamiltonian(t_hop=1.0, U=2.0)
    g = _hub.ground_observables(H)
    assert g["spin_correlation"] < 0.0


def test_large_repulsive_limit_trends_to_singlet_value() -> None:
    H = _hub.hubbard_half_filled_hamiltonian(t_hop=1.0, U=12.0)
    g = _hub.ground_observables(H)
    # Approach -3/4 from above as U/t grows.
    assert g["spin_correlation"] < -0.70


def test_repulsion_suppresses_double_occupancy() -> None:
    H_attr = _hub.hubbard_half_filled_hamiltonian(t_hop=1.0, U=-4.0)
    H_rep = _hub.hubbard_half_filled_hamiltonian(t_hop=1.0, U=4.0)
    g_attr = _hub.ground_observables(H_attr)
    g_rep = _hub.ground_observables(H_rep)
    assert g_rep["double_occupancy_total"] < g_attr["double_occupancy_total"]


def test_scan_shape() -> None:
    scan = _hub.shell_scan(
        m_start=2,
        m_end=8,
        t_hop=1.0,
        lambda0=0.8,
        coherence=1.0,
        time=math.pi / 5.0,
        beta=1.0,
    )
    assert len(scan["rows"]) == 7


def test_thermal_infinite_temperature_limit() -> None:
    U = 1.7
    H = _hub.hubbard_half_filled_hamiltonian(t_hop=1.0, U=U)
    th = _hub.thermal_observables(H, beta=0.0)
    # Uniform mixture over 4 basis states.
    assert abs(th["thermal_double_occupancy_total"] - 0.5) < 1e-12
    assert abs(th["thermal_spin_correlation"] - (-0.125)) < 1e-12
    assert abs(th["thermal_energy"] - (U / 2.0)) < 1e-12


def test_thermal_low_temperature_matches_ground_state() -> None:
    H = _hub.hubbard_half_filled_hamiltonian(t_hop=1.0, U=2.0)
    g = _hub.ground_observables(H)
    th = _hub.thermal_observables(H, beta=50.0)
    assert abs(th["thermal_energy"] - g["ground_energy"]) < 1e-8
    assert abs(th["thermal_spin_correlation"] - g["spin_correlation"]) < 1e-8


if __name__ == "__main__":
    test_closed_form_spectrum_random_samples()
    test_repulsive_ground_state_is_antiferromagnetic()
    test_large_repulsive_limit_trends_to_singlet_value()
    test_repulsion_suppresses_double_occupancy()
    test_scan_shape()
    test_thermal_infinite_temperature_limit()
    test_thermal_low_temperature_matches_ground_state()
    print("ok")
