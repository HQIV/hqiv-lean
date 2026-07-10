#!/usr/bin/env python3
"""Unit tests for contact force / Hessian / crystal spectral-gap readouts."""

from __future__ import annotations

import math
import unittest

import hqiv_contact_force_readout as cfr
import hqiv_lean_physics_primitives as lean
import hqiv_voltage_generation_ledger as vgl


class TestContactForceReadout(unittest.TestCase):
    def test_force_and_hessian_zero_at_r0(self) -> None:
        self.assertEqual(cfr.contact_force_morse_backbone(1.0, 0.0), 0.0)
        self.assertEqual(cfr.contact_hessian_n_m(1.0, 0.0), 0.0)

    def test_morse_force_matches_strong_times_2D_over_r(self) -> None:
        d_e, r = 4.0, 1.0
        f = cfr.contact_force_morse_backbone(d_e, r)
        expected = lean.STRONG_CHANNEL_FRACTION * 2.0 * (d_e * cfr.EV_J) / (
            r * cfr.ANGSTROM_M
        )
        self.assertAlmostEqual(f, expected, places=12)

    def test_hessian_is_length_scaled_force_constant(self) -> None:
        d_e, r = 5.0, 1.5
        k = cfr.contact_hessian_n_m(d_e, r)
        expected = 2.0 * (d_e * cfr.EV_J) / (r * cfr.ANGSTROM_M) ** 2
        self.assertAlmostEqual(k, expected, places=8)

    def test_phonon_scales_as_sqrt_k_over_mu(self) -> None:
        k = 100.0
        w1 = cfr.discrete_phonon_wavenumber_cm1(k, 1.0)
        w4 = cfr.discrete_phonon_wavenumber_cm1(k, 4.0)
        self.assertAlmostEqual(w1 / w4, 2.0, places=10)

    def test_crystal_gap_nil_and_homopolar(self) -> None:
        self.assertEqual(cfr.crystal_spectral_gap([], 1.5, 0.3), 0.0)
        self.assertEqual(cfr.crystal_spectral_gap([0.0, 0.0], 3.42, 0.0), 0.0)

    def test_crystal_gap_zero_ionic_softener_identity(self) -> None:
        self.assertAlmostEqual(vgl.ionic_optical_gap_softener(0.0), 1.0, places=15)

    def test_ionic_gap_opens_on_unique_polarity(self) -> None:
        gap = cfr.crystal_spectral_gap([1.0], 1.544, 0.5)
        self.assertGreater(gap, 0.0)
        self.assertLess(gap, 1.0)

    def test_audit_identity_checks(self) -> None:
        payload = cfr.build_audit()
        self.assertTrue(payload["all_identity_checks_pass"])
        self.assertGreaterEqual(len(payload["crystal_rows"]), 8)
        metals = [r for r in payload["crystal_rows"] if r["crystal_kind"] == "metallic"]
        self.assertTrue(all(r["crystal_spectral_gap"] == 0.0 for r in metals))


if __name__ == "__main__":
    unittest.main()
