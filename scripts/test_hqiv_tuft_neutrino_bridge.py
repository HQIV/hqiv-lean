#!/usr/bin/env python3
"""Tests for hqiv_tuft_neutrino_bridge.py."""

from __future__ import annotations

import math
import unittest

import hqiv_tuft_mass_spectrum_pdg_eval as tmse
import hqiv_tuft_neutrino_bridge as bridge


class TestTuftNeutrinoBridge(unittest.TestCase):
    def test_outer_dressing_matches_manual(self) -> None:
        bal = bridge.casimir_balance()
        self.assertAlmostEqual(
            bal.outer_dressing,
            bal.outer_suppression / bal.inner_trapping * tmse.TUFT_HOPF_KAPPA6,
            places=18,
        )

    def test_primary_passes_absolute_mass_caps(self) -> None:
        comp = bridge.compare_model(bridge.model_tuft_outer_t8_t10())
        self.assertTrue(bridge.passes_absolute_mass_caps(comp))
        self.assertLess(comp.sum_ev, bridge.COSMOLOGY_SUM_CAP_EV)
        self.assertLess(comp.m3_ev, bridge.LOOSE_INDIVIDUAL_MASS_CAP_EV)

    def test_primary_normal_ordering(self) -> None:
        comp = bridge.compare_model(bridge.model_tuft_outer_t8_t10())
        self.assertEqual(comp.ordering, "normal")

    def test_t10_middle_to_light_ratio(self) -> None:
        t10 = bridge.t10_mixing_phase_matrix()
        self.assertAlmostEqual(t10["middle_to_light"], 3.0, places=12)
        self.assertAlmostEqual(t10["heavy_to_middle"], 2.0, places=12)

    def test_t10_contribution_eq_holonomy_times_torsion(self) -> None:
        for g in range(3):
            n = g + 1
            hol = bridge.HOLONOMY[g]
            torsion = tmse.hopf_torsion_coefficient(n)
            self.assertAlmostEqual(
                bridge.t10_generation_phase_contribution(g),
                hol * torsion,
                places=15,
            )

    def test_t10_pmns_sin_sq_theta12(self) -> None:
        ang = bridge.t10_pmns_angles_from_ratios()
        self.assertAlmostEqual(math.sin(ang["theta12_rad"]) ** 2, 0.25, places=12)

    def test_t10_pmns_sin_sq_theta23(self) -> None:
        ang = bridge.t10_pmns_angles_from_ratios()
        self.assertAlmostEqual(math.sin(ang["theta23_rad"]) ** 2, 1.0 / 3.0, places=12)

    def test_t10_overlap_diagonal_normalized(self) -> None:
        overlap = bridge.t10_overlap_matrix()
        total = bridge.t10_phase_contribution_sum()
        for g in range(3):
            c = bridge.t10_generation_phase_contribution(g)
            self.assertAlmostEqual(overlap[g][g], math.sqrt(c / total), places=12)

    def test_t10_pmns_unitary_rows_unit_norm(self) -> None:
        u = bridge.t10_pmns_unitary_from_angles()
        for row in u:
            self.assertAlmostEqual(sum(x * x for x in row), 1.0, places=10)

    def test_t10_improves_dm21_over_outer_t8_holonomy(self) -> None:
        base = bridge.compare_model(bridge.model_tuft_outer_t8_holonomy())
        t10 = bridge.compare_model(bridge.model_tuft_outer_t8_t10())
        self.assertGreater(t10.dm21_ratio_to_pdg, base.dm21_ratio_to_pdg)

    def test_holonomy_ratios(self) -> None:
        m1, m2, m3 = bridge.neutrino_masses_from_holonomy(1.0)
        self.assertAlmostEqual(m3, 1.0)
        self.assertAlmostEqual(m2, 96 / 144)
        self.assertAlmostEqual(m1, 48 / 144)

    def test_retired_legacy_fails(self) -> None:
        comp = bridge.compare_model(bridge.model_retired_legacy_140_ladder())
        self.assertGreater(comp.sum_over_pdg_limit, 1.0e6)

    def test_no_seesaw_in_registry(self) -> None:
        for name in bridge.ALL_MODELS:
            self.assertNotIn("seesaw", name)


if __name__ == "__main__":
    unittest.main()
