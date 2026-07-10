#!/usr/bin/env python3
"""Tests for driven thermal conductivity assay."""

from __future__ import annotations

import unittest

import hqiv_driven_thermal_conductivity_readout as dtc
import hqiv_lean_physics_primitives as lean


class TestDrivenThermal(unittest.TestCase):
    def test_zero_gradient_identity(self) -> None:
        self.assertAlmostEqual(
            dtc.driven_phonon_thermal_conductivity(2.5, 0.0, 273.15), 2.5, places=12
        )

    def test_full_melt_softener(self) -> None:
        k = dtc.driven_phonon_thermal_conductivity(1.0, 100.0, 100.0)
        self.assertAlmostEqual(k, 1.0 / (1.0 + lean.GAMMA), places=12)

    def test_audit_identity(self) -> None:
        audit = dtc.build_driven_thermal_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        self.assertIn("H2O", {r["molecule"] for r in audit["rows"]})


if __name__ == "__main__":
    unittest.main()
