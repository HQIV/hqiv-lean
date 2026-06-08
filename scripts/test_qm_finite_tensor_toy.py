#!/usr/bin/env python3
"""Regression checks for `qm_finite_tensor_toy.py`."""

from __future__ import annotations

import importlib.util
import math
from pathlib import Path

import numpy as np

_SCRIPTS = Path(__file__).resolve().parent
_MOD = _SCRIPTS / "qm_finite_tensor_toy.py"
_spec = importlib.util.spec_from_file_location("qm_finite_tensor_toy", _MOD)
assert _spec and _spec.loader
_qm = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_qm)


def test_kronecker_sum_spectrum_additivity() -> None:
    ha = np.diag([0.0, 1.0]).astype(np.complex128)
    hb = np.diag([0.0, 2.0]).astype(np.complex128)
    h = _qm.kronecker_sum(ha, hb)
    e = np.sort(np.linalg.eigvalsh(h))
    expected = np.sort(np.array([0.0, 1.0, 2.0, 3.0], dtype=np.float64))
    np.testing.assert_allclose(e, expected, atol=1e-10, rtol=0.0)


def test_two_qubit_zz_spectrum() -> None:
    out = _qm.demo_two_qubit_zz()
    assert out["eigenvalues"] == [-2.0, 0.0, 0.0, 2.0]


def test_unitary_roundtrip() -> None:
    ha = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128)
    hb = np.array([[0.5, 0.0], [0.0, -0.5]], dtype=np.complex128)
    h = _qm.kronecker_sum(ha, hb)
    t = 0.37
    u = _qm.exp_iHt(h, t)
    np.testing.assert_allclose(u.conj().T @ u, np.eye(4), atol=1e-10, rtol=0.0)
    np.testing.assert_allclose(u @ u.conj().T, np.eye(4), atol=1e-10, rtol=0.0)


def test_norm_preservation() -> None:
    ha = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128)
    hb = np.array([[0.0, 0.0], [0.0, 0.0]], dtype=np.complex128)
    h = _qm.kronecker_sum(ha, hb)
    psi = np.array([0.25, 0.25j, 0.5, 0.5], dtype=np.complex128)
    psi = psi / np.linalg.norm(psi)
    psi2 = _qm.exp_iHt(h, math.pi / 6.0) @ psi
    assert abs(np.linalg.norm(psi2) - 1.0) < 1e-12


if __name__ == "__main__":
    test_kronecker_sum_spectrum_additivity()
    test_two_qubit_zz_spectrum()
    test_unitary_roundtrip()
    test_norm_preservation()
    print("ok")
