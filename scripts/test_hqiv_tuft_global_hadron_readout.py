#!/usr/bin/env python3
"""Tests for the global TUFT hadron readout (single formula, all sectors)."""

from __future__ import annotations

import unittest

import hqiv_tuft_global_hadron_readout as tgh


class TestGlobalHadronReadout(unittest.TestCase):
    XI = tgh.XI_LOCKIN

    def test_content_weights_first_principles(self) -> None:
        w_light = (4.0 / 9.0) * (2.0 / 3.0)
        rho = tgh.TuftExcitationChannel.meson(0, 1, 0)
        omega = tgh.TuftExcitationChannel.meson(0, 1, 0, isoscalar=True)
        kstar = tgh.TuftExcitationChannel.meson(1, 0, 1)
        phi = tgh.TuftExcitationChannel.meson(1, 0, 2)
        proton = tgh.TuftExcitationChannel.baryon(0, 0)
        self.assertAlmostEqual(tgh.tuft_content_excitation_weight(rho), w_light)
        self.assertAlmostEqual(
            tgh.tuft_content_excitation_weight(omega), w_light * (1.0 + tgh.GAMMA / 2.0)
        )
        self.assertAlmostEqual(tgh.tuft_content_excitation_weight(kstar), w_light**0.5)
        self.assertAlmostEqual(tgh.tuft_content_excitation_weight(phi), 1.0)
        self.assertAlmostEqual(tgh.tuft_content_excitation_weight(proton), 1.0)

    def test_rho_omega_split(self) -> None:
        rho = tgh.tuft_excited_mass_global_at_xi_mev(
            self.XI, tgh.TuftExcitationChannel.meson(0, 1, 0, "rho")
        )
        omega = tgh.tuft_excited_mass_global_at_xi_mev(
            self.XI, tgh.TuftExcitationChannel.meson(0, 1, 0, "omega", isoscalar=True)
        )
        self.assertNotAlmostEqual(rho, omega, delta=1.0)
        self.assertAlmostEqual(rho / 775.26, 1.0, delta=0.02)
        self.assertAlmostEqual(omega / 782.65, 1.0, delta=0.02)

    def test_n_baryons_distinct_and_aligned(self) -> None:
        xi = self.XI
        m1440 = tgh.tuft_excited_mass_global_at_xi_mev(
            xi, tgh.TuftExcitationChannel.baryon(0, 2, "N(1440)", negative_parity=False)
        )
        m1520 = tgh.tuft_excited_mass_global_at_xi_mev(
            xi, tgh.TuftExcitationChannel.baryon(1, 1, "N(1520)", negative_parity=True)
        )
        m1680 = tgh.tuft_excited_mass_global_at_xi_mev(
            xi, tgh.TuftExcitationChannel.baryon(0, 3, "N(1680)", negative_parity=True)
        )
        m1710 = tgh.tuft_excited_mass_global_at_xi_mev(
            xi, tgh.TuftExcitationChannel.baryon(0, 3, "N(1710)", negative_parity=False)
        )
        self.assertNotAlmostEqual(m1440, m1520, delta=5.0)
        self.assertNotAlmostEqual(m1680, m1710, delta=5.0)
        self.assertAlmostEqual(m1440 / 1440.0, 1.0, delta=0.02)
        self.assertAlmostEqual(m1520 / 1515.0, 1.0, delta=0.02)
        self.assertAlmostEqual(m1680 / 1680.0, 1.0, delta=0.02)
        self.assertAlmostEqual(m1710 / 1710.0, 1.0, delta=0.02)

    def test_excitation_coupling_weight(self) -> None:
        mixed = tgh.TuftExcitationChannel.baryon(1, 1, negative_parity=True)
        neg_f = tgh.TuftExcitationChannel.baryon(0, 3, negative_parity=True)
        pos_f = tgh.TuftExcitationChannel.baryon(0, 3, negative_parity=False)
        self.assertAlmostEqual(tgh.tuft_excitation_coupling_weight(mixed), 8.0 / 9.0)
        self.assertAlmostEqual(
            tgh.tuft_excitation_coupling_weight(neg_f), 1.0 - tgh.GAMMA / 8.0
        )
        self.assertAlmostEqual(tgh.tuft_excitation_coupling_weight(pos_f), 1.0)

    def test_benchmark_slots(self) -> None:
        pdg = {
            "rho": 775.26,
            "omega": 782.65,
            "phi(1020)": 1019.46,
            "K*(892)": 891.66,
            "proton": 938.27208816,
            "Delta(1232)": 1232.0,
            "N(1440)": 1440.0,
            "N(1520)": 1515.0,
            "N(1680)": 1680.0,
            "N(1710)": 1710.0,
        }
        for ch in tgh.MESON_EXCITED_CHANNELS + tgh.BARYON_EXCITED_CHANNELS:
            if ch.pdg_key is None or ch.pdg_key not in pdg:
                continue
            m = tgh.tuft_excited_mass_global_at_xi_mev(self.XI, ch)
            self.assertAlmostEqual(m / pdg[ch.pdg_key], 1.0, delta=0.02, msg=ch.pdg_key)


if __name__ == "__main__":
    unittest.main()
