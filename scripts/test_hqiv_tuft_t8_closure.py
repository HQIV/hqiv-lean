#!/usr/bin/env python3
"""Tests for T8 full sector determinant closure (Python ↔ Lean)."""

from __future__ import annotations

import math
import unittest

import hqiv_tuft_mass_spectrum_pdg_eval as tmse


class TestTuftT8Closure(unittest.TestCase):
    def test_tau_unchanged_by_t8_subleading(self) -> None:
        tau, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(5)
        tau_t8, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_t8_mev(5)
        self.assertAlmostEqual(tau_t8, tau, places=6)

    def test_mu_within_one_percent_after_t8(self) -> None:
        _, mu_t8, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_t8_mev(5)
        self.assertAlmostEqual(mu_t8 / tmse.PDG_MEV["mu"], 1.0, delta=0.005)

    def test_e_within_one_percent_after_t8(self) -> None:
        _, _, e_t8 = tmse.lepton_mass_spectrum_at_xi_from_vev_t8_mev(5)
        self.assertAlmostEqual(e_t8 / tmse.PDG_MEV["e"], 1.0, delta=0.005)

    def test_primary_chart_is_t8_full(self) -> None:
        self.assertEqual(
            tmse.lepton_mass_spectrum_at_xi_mev(5),
            tmse.lepton_mass_spectrum_at_xi_from_vev_t8_mev(5),
        )

    def test_heavy_subleading_is_unity(self) -> None:
        self.assertAlmostEqual(tmse.hopf_t8_torsion_subleading(3), 1.0, places=12)

    def test_ray_singer_coeff_matches_lean(self) -> None:
        self.assertAlmostEqual(
            tmse.TUFT_RAY_SINGER_SUBLEADING_COEFF,
            1.0 / (4.0 * math.pi),
            places=15,
        )


if __name__ == "__main__":
    unittest.main()
