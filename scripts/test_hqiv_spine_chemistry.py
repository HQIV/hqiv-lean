#!/usr/bin/env python3
"""Parity: ``hqiv_spine_chemistry`` matches proved ``HqivSpine/Chemistry`` constants."""

from __future__ import annotations

import math
import unittest

import hqiv_atom_construction as ac
import hqiv_spine_chemistry as sc


class TestSpineChemistry(unittest.TestCase):
    def test_slater_increments(self) -> None:
        self.assertAlmostEqual(sc.SCREEN_PENETRATION_LEAK, 0.15, places=12)
        self.assertAlmostEqual(sc.SLATER_SAME_SHELL, 0.35, places=12)
        self.assertAlmostEqual(sc.SLATER_ADJACENT_SHELL, 0.85, places=12)
        self.assertAlmostEqual(sc.SLATER_DEEP_SHELL, 1.0, places=12)
        self.assertAlmostEqual(sc.slater_shielding_increment(2, 2), 0.35)
        self.assertAlmostEqual(sc.slater_shielding_increment(2, 1), 0.85)
        self.assertAlmostEqual(sc.slater_shielding_increment(3, 1), 1.0)
        self.assertAlmostEqual(sc.slater_shielding_increment(2, 3), 0.0)

    def test_atom_construction_imports_same_slater(self) -> None:
        self.assertAlmostEqual(ac.SLATER_SAME_SHELL, sc.SLATER_SAME_SHELL)
        self.assertAlmostEqual(ac.SLATER_ADJACENT_SHELL, sc.SLATER_ADJACENT_SHELL)

    def test_vsepr_tetrahedral(self) -> None:
        self.assertAlmostEqual(sc.tetrahedral_contact_cos(), -1.0 / 3.0, places=12)
        self.assertAlmostEqual(sc.balanced_unit_contacts_cos(3), -0.5, places=12)

    def test_monogamy_spectator(self) -> None:
        self.assertAlmostEqual(sc.MONOGAMY_SPECTATOR_CONTACT, 1.2, places=12)
        self.assertAlmostEqual(sc.MONOGAMY_SPECTATOR_CONTACT, 2.0 * sc.ALPHA, places=12)

    def test_h2_site_energy_reference_m(self) -> None:
        self.assertAlmostEqual(sc.h2_site_energy_same_shell(4), 1200.0, places=9)

    def test_carbon_zeff_spine(self) -> None:
        # Binding.slaterEffectiveChargeAufbau_carbon = 3.25
        self.assertAlmostEqual(sc.spine_manifest()["carbon_zeff_spine"], 3.25, places=9)

    def test_wc_hbond_counts(self) -> None:
        self.assertEqual(sc.CANONICAL_WC_HBOND_COUNTS["AT"], 2)
        self.assertEqual(sc.CANONICAL_WC_HBOND_COUNTS["GC"], 3)


if __name__ == "__main__":
    unittest.main()
