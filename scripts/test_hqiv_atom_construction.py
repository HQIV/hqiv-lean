#!/usr/bin/env python3
"""Tests for HQIV atom construction (prediction vs quarantined comparison)."""

from __future__ import annotations

import unittest

import hqiv_atom_construction as ac
import hqiv_atom_electronic_discharge as discharge


class DerivedScreeningTests(unittest.TestCase):
    def test_slater_coefficients_are_derived_from_alpha(self) -> None:
        # 0.35 / 0.85 / 1.00 reproduced EXACTLY from alpha=3/5 and referenceM=4:
        #   leak = alpha/4 = 0.15 ; same = 1/2 - leak ; adjacent = 1 - leak ; deep = 1
        self.assertAlmostEqual(ac.SLATER_SAME_SHELL, 0.35, places=12)
        self.assertAlmostEqual(ac.SLATER_ADJACENT_SHELL, 0.85, places=12)
        self.assertAlmostEqual(ac.SLATER_DEEP_SHELL, 1.00, places=12)

    def test_penetration_leak_is_alpha_over_referenceM(self) -> None:
        import hqiv_lean_physics_primitives as lean
        self.assertAlmostEqual(ac._SCREEN_PENETRATION_LEAK, lean.ALPHA / lean.REFERENCE_M)

    def test_same_adjacent_gap_is_monogamy_half(self) -> None:
        self.assertAlmostEqual(ac.SLATER_ADJACENT_SHELL - ac.SLATER_SAME_SHELL, 0.5, places=12)

    def test_effective_charge_unchanged_for_carbon_valence(self) -> None:
        # behaviour identical to the old literal table: C 2p Z_eff = 6 - (3*0.35 + 2*0.85)
        cfg = ac.electron_configuration(6)
        zeff = ac.config_effective_charge(6, len(cfg) - 1, cfg)
        self.assertAlmostEqual(zeff, 6.0 - (3 * 0.35 + 2 * 0.85), places=9)


class AtomElectronicDischargeTests(unittest.TestCase):
    def test_factorization_canonical(self) -> None:
        self.assertTrue(
            discharge.satisfies_atom_electronic_factorization(
                discharge.atom_compton_slots_canonical
            )
        )

    def test_hydrogen_triplet(self) -> None:
        self.assertEqual(discharge.atom_compton_triplet_from_charge(1), (1, 1, 1))

    def test_lithium_matches_heavy_hydride_chart(self) -> None:
        self.assertEqual(discharge.atom_compton_triplet_from_charge(3), (4, 3, 1))

    def test_oxygen_period2_slots(self) -> None:
        self.assertEqual(discharge.atom_compton_triplet_from_charge(8), (4, 3, 1))
        obs = discharge.atom_electronic_discharge_obs(8)
        self.assertEqual(obs.chemical_period, 2)
        self.assertEqual(obs.valence_count, 6)


class AtomConstructionTests(unittest.TestCase):
    def test_prediction_does_not_use_nist_in_formula(self) -> None:
        """Changing NIST table must not change derived mass."""
        h = ac.atom_readout_from_charge(1)
        old = ac.AtomComparisonLayer.NIST_ATOMIC_MASS_AMU["H"]
        ac.AtomComparisonLayer.NIST_ATOMIC_MASS_AMU["H"] = 999.0
        try:
            h2 = ac.atom_readout_from_charge(1)
            self.assertEqual(h.derived_atomic_mass_amu, h2.derived_atomic_mass_amu)
        finally:
            ac.AtomComparisonLayer.NIST_ATOMIC_MASS_AMU["H"] = old

    def test_comparison_layer_separate(self) -> None:
        row = ac.comparison_row("H")
        self.assertIsNotNone(row.nist_mass_amu)
        self.assertIsNotNone(row.relative_error_vs_nist)

    def test_electron_shells_hydrogen(self) -> None:
        self.assertEqual(ac.atom_electron_shells(1), [1])

    def test_electron_shells_helium(self) -> None:
        self.assertEqual(ac.atom_electron_shells(2), [1, 1])

    def test_site_energy_positive(self) -> None:
        for z in (1, 2, 6, 8):
            self.assertGreater(ac.atom_site_energy_trace(z), 0.0)

    def test_mass_uses_closed_mass_not_nuclear_only(self) -> None:
        r = ac.atom_readout_from_charge(8)
        self.assertGreater(r.derived_atomic_mass_amu, r.nuclear_only_mass_amu)
        expected = r.closed_mass_mev / ac.MEV_PER_AMU
        self.assertAlmostEqual(r.derived_atomic_mass_amu, expected)

    def test_hydrogen_mass_matches_nist_within_01pct(self) -> None:
        r = ac.atom_readout_from_charge(1)
        self.assertAlmostEqual(r.derived_atomic_mass_amu, 1.007825, places=5)

    def test_helium_mass_number_and_mass(self) -> None:
        r = ac.atom_readout_from_charge(2)
        self.assertEqual(r.mass_number, 4)
        self.assertAlmostEqual(r.derived_atomic_mass_amu, 3.988, places=2)

    def test_hydrogen_has_no_outside_fight(self) -> None:
        r = ac.atom_readout_from_charge(1)
        self.assertEqual(r.electronic_outside_curvature_fight_mev, 0.0)

    def test_helium_has_outside_fight(self) -> None:
        r = ac.atom_readout_from_charge(2)
        self.assertGreater(r.electronic_outside_curvature_fight_mev, 1.0)
        self.assertGreater(r.derived_atomic_mass_amu, r.nuclear_only_mass_amu)

    def test_carbon_mass_near_twelve(self) -> None:
        r = ac.atom_readout_from_charge(6)
        self.assertEqual(r.mass_number, 12)
        self.assertAlmostEqual(r.derived_atomic_mass_amu, 11.970, delta=0.05)

    def test_shell_xi_readouts_match_electrons(self) -> None:
        r = ac.atom_readout_from_charge(8)
        self.assertEqual(len(r.shell_xi_readouts), len(r.electron_shells))
        self.assertAlmostEqual(r.shell_xi_readouts[0].xi, 2.0)

    def test_first_ionization_hydrogen_order_of_magnitude(self) -> None:
        r = ac.atom_readout_from_charge(1)
        self.assertGreater(r.first_ionization_ev, 10.0)
        self.assertLess(r.first_ionization_ev, 16.0)

    def test_oxygen_valence_p_shells(self) -> None:
        shells = ac.atom_electron_shells(8)
        self.assertEqual(shells[4:8], [3, 3, 3, 3])


if __name__ == "__main__":
    unittest.main()
