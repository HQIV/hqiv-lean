#!/usr/bin/env python3
"""Tests for the primary T8 charged-lepton readout (vev → Λ_Hopf → full T8 scalar)."""

from __future__ import annotations

import unittest

import hqiv_tuft_mass_spectrum_pdg_eval as tmse


class TestTuftLeptonReadout(unittest.TestCase):
    XI = tmse.XI_LOCKIN
    PDG = {"tau": 1776.86, "mu": 105.6583755, "e": 0.5109989461}

    def test_t8_full_matches_pdg_within_2pct(self) -> None:
        tau, mu, e = tmse.lepton_mass_spectrum_at_xi_mev(self.XI)
        self.assertAlmostEqual(tau / self.PDG["tau"], 1.0, delta=0.002)
        self.assertAlmostEqual(mu / self.PDG["mu"], 1.0, delta=0.002)
        self.assertAlmostEqual(e / self.PDG["e"], 1.0, delta=0.003)

    def test_tau_unchanged_by_t8_subleading(self) -> None:
        tau_t8, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_t8_mev(self.XI)
        tau_lead, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(self.XI)
        self.assertAlmostEqual(tau_t8, tau_lead, places=6)

    def test_t8_improves_mu_e_over_leading_only(self) -> None:
        _, mu_t8, e_t8 = tmse.lepton_mass_spectrum_at_xi_from_vev_t8_mev(self.XI)
        _, mu_lead, e_lead = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(self.XI)
        err_t8 = abs(mu_t8 / self.PDG["mu"] - 1.0) + abs(e_t8 / self.PDG["e"] - 1.0)
        err_lead = abs(mu_lead / self.PDG["mu"] - 1.0) + abs(e_lead / self.PDG["e"] - 1.0)
        self.assertLess(err_t8, err_lead)


if __name__ == "__main__":
    unittest.main()
