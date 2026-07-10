#!/usr/bin/env python3
"""Tests for discrete KS matrix / fixed point."""

from __future__ import annotations

import unittest

import hqiv_discrete_ks_readout as ks
import hqiv_discrete_scf_readout as scf


class TestDiscreteKs(unittest.TestCase):
    def test_zero_delta_is_core(self) -> None:
        ks_, kp, ksp = ks.discrete_ks_matrix(4.0, 2.0, 0.0, 1.0, 0.0)
        self.assertAlmostEqual(ks_, -2.0, places=12)
        self.assertAlmostEqual(kp, 2.0, places=12)
        self.assertAlmostEqual(ksp, 0.0, places=12)

    def test_xc_zero_at_delta0(self) -> None:
        self.assertAlmostEqual(ks.discrete_ks_xc_scale(2.0, 0.0), 0.0, places=12)

    def test_covalent_identity(self) -> None:
        fp = ks.discrete_ks_fixed_point(
            ionic_character=0.0,
            contact_scale_ev=2.0,
            band_gap0=1.3,
        )
        self.assertAlmostEqual(fp["dress"], 1.0, places=12)
        self.assertAlmostEqual(fp["ks_gap_eV"], 1.3, places=12)

    def test_dress_matches_scf(self) -> None:
        audit = ks.build_discrete_ks_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        nacl = next(r for r in audit["rows"] if r["name"] == "NaCl")
        self.assertTrue(nacl["dress_matches_scf"])
        self.assertAlmostEqual(
            nacl["ks"]["dress"],
            scf.discrete_scf_dress(nacl["ks"]["charge_excess"]),
            places=12,
        )


if __name__ == "__main__":
    unittest.main()
