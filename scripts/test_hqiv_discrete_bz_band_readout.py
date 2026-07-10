#!/usr/bin/env python3
"""Tests for discrete Brillouin-zone electronic bands."""

from __future__ import annotations

import math
import unittest

import hqiv_discrete_bz_band_readout as bz
import hqiv_lean_physics_primitives as lean


class TestDiscreteBzBands(unittest.TestCase):
    def test_gamma_is_half_gap(self) -> None:
        eps = bz.discrete_band_dispersion_ev(2.0, 0.5, 0.0)
        self.assertAlmostEqual(eps, 1.0, places=12)

    def test_zone_edge_widens(self) -> None:
        e0 = bz.discrete_band_dispersion_ev(2.0, 0.5, 0.0)
        eX = bz.discrete_band_dispersion_ev(2.0, 0.5, math.pi)
        self.assertGreater(eX, e0)

    def test_hopping_formula(self) -> None:
        e_c = bz.contact_electronic_scale_ev(2.0)
        t = bz.discrete_band_hopping_ev(2.0, 6.0)
        self.assertAlmostEqual(
            t, lean.STRONG_CHANNEL_FRACTION * e_c / 6.0, places=12
        )

    def test_metal_zero_gap(self) -> None:
        self.assertEqual(
            bz.discrete_band_gap_ev(0.0, 2.0, covalent=False), 0.0
        )

    def test_audit_identity(self) -> None:
        audit = bz.build_discrete_bz_band_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        names = {r["name"] for r in audit["rows"]}
        self.assertIn("NaCl", names)
        self.assertIn("Si", names)
        self.assertIn("Cu", names)
        nacl = next(r for r in audit["rows"] if r["name"] == "NaCl")
        # Discrete polar gap should be O(1)–O(10) eV vs NIST ~8.5.
        self.assertGreater(nacl["gap_at_gamma_eV"], 4.0)
        self.assertLess(nacl["gap_at_gamma_eV"], 20.0)


if __name__ == "__main__":
    unittest.main()
