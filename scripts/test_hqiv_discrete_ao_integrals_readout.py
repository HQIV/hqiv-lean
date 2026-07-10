#!/usr/bin/env python3
"""Tests for discrete AO integrals."""

from __future__ import annotations

import unittest

import hqiv_discrete_ao_integrals_readout as ao
import hqiv_lean_physics_primitives as lean


class TestDiscreteAo(unittest.TestCase):
    def test_softener_zero(self) -> None:
        self.assertAlmostEqual(ao.discrete_ao_softener(0.0), 1.0, places=12)

    def test_overlap_sp_zero(self) -> None:
        self.assertAlmostEqual(
            ao.discrete_ao_overlap_sp(0.0), lean.ALPHA, places=12
        )

    def test_audit_identity(self) -> None:
        audit = ao.build_discrete_ao_audit()
        self.assertTrue(audit["all_identity_checks_pass"])

    def test_kinetic_pp_gamma(self) -> None:
        tss = ao.discrete_ao_kinetic_ss(2.0)
        tpp = ao.discrete_ao_kinetic_pp(2.0)
        self.assertAlmostEqual(tpp, lean.GAMMA * tss, places=12)


if __name__ == "__main__":
    unittest.main()
