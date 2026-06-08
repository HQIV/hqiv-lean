#!/usr/bin/env python3
"""Tests for general finite many-body core utilities."""

from __future__ import annotations

import importlib.util
from pathlib import Path

import numpy as np

_SCRIPTS = Path(__file__).resolve().parent
_MOD = _SCRIPTS / "qm_general_finite_core.py"
_spec = importlib.util.spec_from_file_location("qm_general_finite_core", _MOD)
assert _spec and _spec.loader
_core = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_core)


def test_shell_coherence_params() -> None:
    p = _core.ShellCoherenceParams(lambda0=0.8, kappa=2.0, plasma_scalar_abs=0.3)
    assert abs(p.coherence - 0.6) < 1e-12
    assert abs(p.coupling(4) - 0.8 * 0.6) < 1e-12


def test_interaction_update_and_ground_summary() -> None:
    H = np.diag([0.0, 1.0]).astype(np.complex128)
    V = np.diag([1.0, -1.0]).astype(np.complex128)
    M = _core.FiniteManyBodyModel(H, {"vexp": V})
    M2 = M.with_interaction(V, 0.5)
    g = M2.ground_observables()
    assert "ground_energy" in g and "gap" in g and "vexp" in g


def test_thermal_high_temp_uniform_limit() -> None:
    H = np.diag([0.0, 2.0]).astype(np.complex128)
    O = np.diag([1.0, -1.0]).astype(np.complex128)
    M = _core.FiniteManyBodyModel(H, {"o": O})
    th = M.thermal_observables(beta=0.0)
    assert abs(th["thermal_o"] - 0.0) < 1e-12
    assert abs(th["thermal_energy"] - 1.0) < 1e-12


if __name__ == "__main__":
    test_shell_coherence_params()
    test_interaction_update_and_ground_summary()
    test_thermal_high_temp_uniform_limit()
    print("ok")
