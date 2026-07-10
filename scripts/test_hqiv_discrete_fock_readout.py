#!/usr/bin/env python3
"""Tests for discrete Fock matrix / fixed point."""

from __future__ import annotations

import unittest

import hqiv_discrete_fock_readout as fk
import hqiv_discrete_scf_readout as scf


class TestDiscreteFock(unittest.TestCase):
    def test_zero_delta_is_core(self) -> None:
        fs, fp, fsp = fk.discrete_fock_matrix(4.0, 2.0, 0.0, 1.0, 0.0)
        self.assertAlmostEqual(fs, -2.0, places=12)
        self.assertAlmostEqual(fp, 2.0, places=12)
        self.assertAlmostEqual(fsp, 0.0, places=12)
        self.assertAlmostEqual(fk.discrete_fock_gap(fs, fp, fsp), 4.0, places=12)

    def test_hartree_exchange_zero_at_delta0(self) -> None:
        self.assertAlmostEqual(fk.discrete_fock_hartree_u(2.0, 0.0), 0.0, places=12)
        self.assertAlmostEqual(fk.discrete_fock_exchange_k(2.0, 0.0), 0.0, places=12)

    def test_covalent_identity(self) -> None:
        fp = fk.discrete_fock_fixed_point(
            ionic_character=0.0,
            contact_scale_ev=2.0,
            band_gap0=1.3,
        )
        self.assertAlmostEqual(fp["dress"], 1.0, places=12)
        self.assertAlmostEqual(fp["fock_gap_eV"], 1.3, places=12)
        self.assertAlmostEqual(fp["n_s"], 1.0, places=8)

    def test_dress_matches_scf(self) -> None:
        audit = fk.build_discrete_fock_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        nacl = next(r for r in audit["rows"] if r["name"] == "NaCl")
        self.assertTrue(nacl["dress_matches_scf"])
        self.assertAlmostEqual(
            nacl["fock"]["dress"],
            scf.discrete_scf_dress(nacl["fock"]["charge_excess"]),
            places=12,
        )


if __name__ == "__main__":
    unittest.main()
