#!/usr/bin/env python3
"""Tests: molecular dipole from geometry — polarity and resultant factor from the balanced frame."""

from __future__ import annotations

import math
import unittest

import hqiv_molecular_dipole as md


class ResultantFactorTests(unittest.TestCase):
    """|Σ bond unit vectors| = sqrt(k(d-k)/(d-1)) — derived, exact."""

    def test_closed_form_matches_known_geometries(self) -> None:
        # AX2E2 bent (water): k=2, d=4 -> sqrt(4/3)
        self.assertAlmostEqual(md.resultant_factor(2, 2), math.sqrt(4 / 3), places=9)
        # AX3E1 pyramidal (ammonia): k=3, d=4 -> 1
        self.assertAlmostEqual(md.resultant_factor(3, 1), 1.0, places=9)
        # AX2E1 bent (SO2): k=2, d=3 -> 1
        self.assertAlmostEqual(md.resultant_factor(2, 1), 1.0, places=9)

    def test_all_bonded_cancels(self) -> None:
        # every domain a bond (k=d) -> 0: tetrahedral, trigonal, linear, octahedral
        for k in (2, 3, 4, 6):
            self.assertAlmostEqual(md.resultant_factor(k, 0), 0.0, places=12)

    def test_factor_equals_gram_identity(self) -> None:
        # sqrt(k(d-k)/(d-1)) for a spread of (k, lp)
        for k in range(1, 5):
            for lp in range(0, 4):
                d = k + lp
                if d <= 1:
                    continue
                expect = math.sqrt(max(0.0, k * (d - k) / (d - 1)))
                self.assertAlmostEqual(md.resultant_factor(k, lp), expect, places=9)


class PolarityTests(unittest.TestCase):
    """Polar/nonpolar classification is exact (from balance)."""

    def setUp(self) -> None:
        self.rows = {r.name: r for r in md.panel_readout()}

    def test_symmetric_molecules_are_nonpolar(self) -> None:
        for name in ("CH4", "CO2", "BF3", "BeCl2"):
            self.assertFalse(self.rows[name].polar, f"{name} should be nonpolar")
            self.assertAlmostEqual(self.rows[name].dipole_debye, 0.0, places=9)

    def test_lone_pair_molecules_are_polar(self) -> None:
        for name in ("H2O", "NH3", "HF", "SO2"):
            self.assertTrue(self.rows[name].polar, f"{name} should be polar")

    def test_dipole_ordering_matches_experiment(self) -> None:
        # bond-contribution magnitudes preserve the measured ordering H2O > HF > NH3
        r = self.rows
        self.assertGreater(r["H2O"].dipole_debye, r["NH3"].dipole_debye)
        self.assertGreater(r["HF"].dipole_debye, r["NH3"].dipole_debye)


class BondDipoleTests(unittest.TestCase):
    def test_homonuclear_bond_has_no_dipole(self) -> None:
        for z in (1, 6, 7, 8, 9):
            self.assertAlmostEqual(md.bond_dipole_debye(z, z), 0.0, places=12)
            self.assertAlmostEqual(md.bond_charge_asymmetry(z, z), 0.0, places=12)

    def test_partial_charge_is_ionic_character(self) -> None:
        # q = δ² = w (the derived ionic character)
        for zi, zj in [(9, 1), (8, 1), (7, 1), (17, 1)]:
            delta = md.bond_charge_asymmetry(zi, zj)
            self.assertAlmostEqual(md.bond_partial_charge(zi, zj), delta * delta, places=12)


if __name__ == "__main__":
    unittest.main()
