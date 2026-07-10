#!/usr/bin/env python3
"""Tests for discrete SCF fixed point."""

from __future__ import annotations

import unittest

import hqiv_discrete_scf_readout as scf
import hqiv_lean_physics_primitives as lean


class TestDiscreteScf(unittest.TestCase):
    def test_dress_zero_is_one(self) -> None:
        self.assertAlmostEqual(scf.discrete_scf_dress(0.0), 1.0, places=12)

    def test_zero_ionic_zero_charge(self) -> None:
        self.assertAlmostEqual(
            scf.discrete_scf_charge_excess(0.0, 2.0, 4.0), 0.0, places=12
        )

    def test_covalent_identity(self) -> None:
        fp = scf.discrete_scf_fixed_point(
            ionic_character=0.0,
            contact_scale_ev=2.0,
            band_gap0=1.3,
            hopping0=0.3,
        )
        self.assertAlmostEqual(fp["dress"], 1.0, places=12)
        self.assertAlmostEqual(fp["band_gap_eV"], 1.3, places=12)

    def test_mix_uses_alpha(self) -> None:
        m = scf.discrete_scf_mix_charge(0.0, 1.0)
        self.assertAlmostEqual(m, lean.ALPHA, places=12)

    def test_audit_identity(self) -> None:
        audit = scf.build_discrete_scf_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        nacl = next(r for r in audit["rows"] if r["name"] == "NaCl")
        self.assertGreater(nacl["scf"]["dress"], 1.0)
        self.assertTrue(nacl["scf"]["converged"])


if __name__ == "__main__":
    unittest.main()
