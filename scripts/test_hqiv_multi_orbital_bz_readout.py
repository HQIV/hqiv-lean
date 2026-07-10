#!/usr/bin/env python3
"""Tests for multi-orbital discrete BZ bands."""

from __future__ import annotations

import math
import unittest

import hqiv_lean_physics_primitives as lean
import hqiv_multi_orbital_bz_readout as mo


class TestMultiOrbitalBz(unittest.TestCase):
    def test_hopping_relations(self) -> None:
        hops = mo.multi_orbital_hoppings(2.0, 6.0)
        self.assertAlmostEqual(
            hops["t_pp"], lean.GAMMA * hops["t_ss"], places=12
        )
        self.assertAlmostEqual(
            hops["t_sp"], math.sqrt(hops["t_ss"] * hops["t_pp"]), places=12
        )
        self.assertAlmostEqual(
            hops["t_pi"], lean.STRONG_CHANNEL_FRACTION * hops["t_pp"], places=12
        )

    def test_insulator_gamma_matches_eg(self) -> None:
        hops = mo.multi_orbital_hoppings(2.0, 6.0)
        ev = mo.multi_orbital_at_ka(4.0, hops, 0.0)
        self.assertAlmostEqual(
            ev["sigma_plus_eV"] - ev["sigma_minus_eV"], 4.0, places=12
        )
        self.assertAlmostEqual(ev["V_sp"], 0.0, places=12)

    def test_metal_zero_insulating_gap(self) -> None:
        hops = mo.multi_orbital_hoppings(2.0, 12.0)
        ev = mo.multi_orbital_at_ka(0.0, hops, 0.0)
        # Metal reports no insulating gap in the audit; at Γ bands sit at 2t cos0.
        self.assertGreater(ev["sigma_plus_eV"], ev["sigma_minus_eV"] - 1e-15)

    def test_audit_identity(self) -> None:
        audit = mo.build_multi_orbital_bz_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        nacl = next(r for r in audit["rows"] if r["name"] == "NaCl")
        self.assertTrue(nacl["matches_two_band_gamma"])
        self.assertAlmostEqual(
            nacl["gap_at_gamma_eV"], nacl["two_band_gap_eV"], places=9
        )


if __name__ == "__main__":
    unittest.main()
