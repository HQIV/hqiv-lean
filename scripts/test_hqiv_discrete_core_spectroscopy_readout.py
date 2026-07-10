#!/usr/bin/env python3
"""Tests for discrete core spectroscopy."""

from __future__ import annotations

import unittest

import hqiv_discrete_core_spectroscopy_readout as core
import hqiv_lean_physics_primitives as lean


class TestDiscreteCore(unittest.TestCase):
    def test_zeff_single(self) -> None:
        self.assertAlmostEqual(core.discrete_core_zeff(8.0, 1.0), 8.0, places=12)

    def test_hydrogen_rydberg(self) -> None:
        h = core.core_1s_row(1, "H")
        self.assertAlmostEqual(h["bare_core_eV"], core.HARTREE_TO_EV / 2, places=9)

    def test_chem_shift_zero(self) -> None:
        self.assertAlmostEqual(
            core.discrete_core_chem_shift_ev(2.0, 0.0), 0.0, places=12
        )
        self.assertAlmostEqual(core.discrete_core_xps_ev(100.0, 0.0), 100.0, places=12)

    def test_screen_uses_gamma(self) -> None:
        zeff = core.discrete_core_zeff(8.0, 2.0)
        self.assertAlmostEqual(zeff, 8.0 - lean.GAMMA, places=12)

    def test_audit_identity(self) -> None:
        audit = core.build_discrete_core_audit()
        self.assertTrue(audit["all_identity_checks_pass"])


if __name__ == "__main__":
    unittest.main()
