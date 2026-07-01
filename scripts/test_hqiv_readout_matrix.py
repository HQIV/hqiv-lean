#!/usr/bin/env python3
"""Tests for the HQIV readout-matrix substrate (papers/readout_matrices)."""
from __future__ import annotations

import math

import numpy as np
import pytest

import hqiv_readout_matrix as rm


def test_transfer_matrix_recovered_from_engine_to_machine_precision():
    """T is not imposed: it is recoverable from the engine's outputs alone."""
    recovered = rm.recover_transfer_matrix()
    for obs, claimed in rm.TRANSFER_MATRIX.items():
        assert np.allclose(recovered[obs], np.array(claimed), atol=1e-9), obs


def test_transfer_matrix_entries_are_integers_or_half_integers():
    """Knob-freeness as integrality: every entry is a (half-)integer."""
    for obs, row in rm.TRANSFER_MATRIX.items():
        for x in row:
            assert abs(2 * x - round(2 * x)) < 1e-12, (obs, x)


def test_transfer_matrix_has_rank_three():
    """Five SI constants project onto only three independent primaries."""
    mat = np.array([rm.TRANSFER_MATRIX[k] for k in rm.TRANSFER_MATRIX])
    assert np.linalg.matrix_rank(mat, tol=1e-9) == 3


def test_conservation_laws_are_left_null_vectors_of_T():
    """Each loop law combines observable rows to the zero primal vector."""
    order = list(rm.TRANSFER_MATRIX)
    mat = np.array([rm.TRANSFER_MATRIX[k] for k in order], float)
    for law in rm.CONSERVATION_LAWS.values():
        n = np.array([law.get(k, 0) for k in order], float)
        assert np.allclose(mat.T @ n, 0.0, atol=1e-12)


def test_kratzer_and_morse_loop_constants():
    """Kratzer const = 4, Morse loop const = 1, both exact across the suite."""
    consts = rm.conservation_law_constants()
    assert consts["kratzer"]["const"] == pytest.approx(4.0, rel=1e-9)
    assert consts["kratzer"]["relative_spread"] < 1e-9
    assert consts["morse_loop"]["const"] == pytest.approx(1.0, rel=1e-9)
    assert consts["morse_loop"]["relative_spread"] < 1e-9


def test_rotational_inversion_round_trips_r_e():
    """B_e -> r_e is an exact inverse of the engine's own B_e closure."""
    for bench in rm.ms.diatomic_benchmarks():
        r = rm.ms.evaluate_diatomic(bench)
        if r.omega_e_curvature_cm1 <= 0:
            continue
        re_back = rm.r_e_from_B_e(r.B_e_cm1, r.reduced_mass_amu)
        assert re_back == pytest.approx(r.r_e_angstrom, rel=1e-6), r.name


def test_morse_range_inversion_matches_loop_law():
    """a·r_e read from √(ω_e x_e / B_e) reproduces the engine's Morse range."""
    for bench in rm.ms.diatomic_benchmarks():
        r = rm.ms.evaluate_diatomic(bench)
        if r.omega_e_curvature_cm1 <= 0:
            continue
        are_back = rm.morse_range_from_spectrum(r.omega_e_xe_cm1, r.B_e_cm1)
        assert are_back == pytest.approx(r.morse_a_re, rel=1e-9), r.name


def test_well_depth_inversion_matches_engine_D_e():
    """D_e read from ω_e²/(4 ω_e x_e) reproduces the engine's well depth."""
    for bench in rm.ms.diatomic_benchmarks():
        r = rm.ms.evaluate_diatomic(bench)
        if r.omega_e_curvature_cm1 <= 0:
            continue
        de_back = rm.well_depth_from_spectrum(r.omega_e_cm1, r.omega_e_xe_cm1)
        assert de_back == pytest.approx(r.D_e_ev, rel=1e-6), r.name


def test_closed_form_accumulated_curvature_matches_integral():
    """C(ξ) = ln ξ + (α/2) ln²ξ matches the numerical curvature integral."""
    import hqiv_shell_shape_geometry as ssg

    alpha = 3.0 / 5.0
    for xi in (1.5, 2.0, 3.0, 4.5):
        closed = math.log(xi) + (alpha / 2.0) * math.log(xi) ** 2
        assert closed == pytest.approx(ssg.curvature_integral_continuous(xi), abs=1e-6)
