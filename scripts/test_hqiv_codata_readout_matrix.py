#!/usr/bin/env python3
"""Tests for the HQIV CODATA atomic-constant readout matrix."""
from __future__ import annotations

import numpy as np
import pytest

import hqiv_codata_readout_matrix as cm


def test_matrix_reproduces_codata_constants():
    """Every atomic constant follows from (alpha, m_e) + exact SI constants."""
    for name, info in cm.reproduce_codata().items():
        assert info["rel_err"] < 1e-8, (name, info)


def test_all_readout_exponents_are_integers():
    """Knob-freeness as integrality: every power is an integer."""
    for name, (exps, _pref, _unit) in cm.READOUT_MATRIX.items():
        for x in exps:
            assert float(x).is_integer(), (name, x)


def test_only_two_primaries_carry_physics():
    """c, hbar, e are exact SI definitions; alpha and m_e are the inputs."""
    assert cm.PRIMARIES[:2] == ("alpha", "m_e")
    # c, hbar, e equal their exact/defined SI values.
    assert cm.C_SI == 299792458.0
    assert cm.E_SI == 1.602176634e-19


def test_loop_laws_depend_on_alpha_only():
    """Each loop law's net exponent vector is zero except (possibly) alpha."""
    for desc, law in cm.LOOP_LAWS.items():
        res = cm.loop_law_residual(law)
        assert np.allclose(res[1:], 0.0, atol=1e-12), (desc, res)


def test_thomson_ratio_is_a_pure_number():
    """sigma_T / r_e^2 has zero exponent on EVERY primary (pure 8pi/3)."""
    res = cm.loop_law_residual(cm.LOOP_LAWS["sigma_T/r_e^2 = 8pi/3"])
    assert np.allclose(res, 0.0, atol=1e-12)


def test_alpha_power_ladder_values():
    """The three alpha-only ratios are alpha^1, alpha^2, alpha^3/(4pi)."""
    res1 = cm.loop_law_residual(cm.LOOP_LAWS["lambdabar_C/a0 = alpha"])
    res2 = cm.loop_law_residual(cm.LOOP_LAWS["r_e/a0 = alpha^2"])
    res3 = cm.loop_law_residual(cm.LOOP_LAWS["r_e*R_inf = alpha^3/(4pi)"])
    assert res1[0] == pytest.approx(1.0)
    assert res2[0] == pytest.approx(2.0)
    assert res3[0] == pytest.approx(3.0)


def test_alpha_forced_ratios_reproduce_codata_with_codata_alpha():
    """Feeding CODATA 1/alpha into the alpha-only ratios returns CODATA ratios."""
    inv_alpha = 1.0 / cm.ALPHA_CODATA
    for row in cm.alpha_forced_from_hqiv(inv_alpha):
        assert row["rel_err"] < 1e-9, row


def test_matrix_rank_and_loop_law_count():
    """10 constants, rank 5 over 5 primaries -> 5 independent loop laws."""
    assert cm.matrix_rank() == 5
    assert len(cm.READOUT_MATRIX) - cm.matrix_rank() == 5
