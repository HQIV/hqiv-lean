#!/usr/bin/env python3
"""Tests for hqiv_coronal_plasma_backreaction.py."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_ROOT / "scripts"))

import hqiv_coronal_plasma_backreaction as cpb


class TestCoronalPlasmaBackReaction(unittest.TestCase):
    def test_heated_energy_density(self) -> None:
        self.assertAlmostEqual(cpb.heated_energy_density(100.0, 2.0), 200.0)

    def test_hot_back_field_sign(self) -> None:
        e = cpb.hot_pressure_back_reaction(1.0e20, 10.0, 1.0e5)
        self.assertLess(e, 0.0)

    def test_self_consistent_readout_positive_heating(self) -> None:
        row = cpb.coronal_plasma_backreaction_readout()
        self.assertGreater(row.q_dot_primary_w_m3, 0.0)
        self.assertGreater(row.u_hot_j_m3, 0.0)
        self.assertGreater(row.p_hot_pa, 0.0)
        self.assertLessEqual(row.heating_flux_boundary_w_m2, row.target_flux_w_m2 * 1.01)
        self.assertGreaterEqual(row.heating_flux_boundary_w_m2, row.target_flux_w_m2 * 0.99)

    def test_feedback_factor_near_unity_for_weak_backreaction(self) -> None:
        row = cpb.coronal_plasma_backreaction_readout(l_grad=1.0e12, tau_hot=0.1)
        self.assertAlmostEqual(row.feedback_factor, 1.0, delta=0.05)

    def test_linear_pass_energy_scales_with_passes(self) -> None:
        row1 = cpb.coronal_plasma_backreaction_readout(n_passes=10.0)
        row2 = cpb.coronal_plasma_backreaction_readout(n_passes=20.0)
        self.assertAlmostEqual(row2.linear_pass_energy_ev, 2.0 * row1.linear_pass_energy_ev, delta=1.0e-6)


if __name__ == "__main__":
    unittest.main()
