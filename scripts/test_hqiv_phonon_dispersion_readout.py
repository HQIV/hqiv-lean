"""Tests for discrete phonon dispersion readout."""

from __future__ import annotations

import math
import unittest

import hqiv_phonon_dispersion_readout as pdr


class TestPhononDispersion(unittest.TestCase):
    def test_zone_boundary_is_twice_gamma(self) -> None:
        hess, mu = 100.0, 20.0
        g = pdr.discrete_phonon_dispersion_cm1(hess, mu, 0.0)
        self.assertAlmostEqual(g, 0.0, places=12)
        edge = pdr.discrete_phonon_dispersion_cm1(hess, mu, math.pi)
        import hqiv_contact_force_readout as cfr

        gamma = cfr.discrete_phonon_wavenumber_cm1(hess, mu)
        self.assertAlmostEqual(edge, 2.0 * gamma, places=9)

    def test_audit_identity(self) -> None:
        audit = pdr.build_phonon_dispersion_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        names = {r["name"] for r in audit["rows"]}
        self.assertIn("LiH", names)
        self.assertIn("NaCl", names)

    def test_ionic_softener_reduces_gamma(self) -> None:
        import hqiv_contact_force_readout as cfr
        import hqiv_lean_physics_primitives as lean

        soft = cfr.optical_phonon_hessian_softener(6.0, apply_softener=True)
        expect = lean.STRONG_CHANNEL_FRACTION * lean.GAMMA / 6.0
        self.assertAlmostEqual(soft, expect, places=12)
        audit = pdr.build_phonon_dispersion_audit()
        nacl = next(r for r in audit["rows"] if r["name"] == "NaCl")
        self.assertLess(nacl["optical_phonon_hessian_softener"], 1.0)
        # Softened Γ should be within ~2× of NIST TO (quarantine guardrail).
        ratio = nacl.get("gamma_vs_TO_ratio")
        self.assertIsNotNone(ratio)
        self.assertLess(ratio, 2.0)
        self.assertGreater(ratio, 0.25)


if __name__ == "__main__":
    unittest.main()
