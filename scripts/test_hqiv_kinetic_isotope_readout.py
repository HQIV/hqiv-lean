"""Tests for W4/GMTKN kinetic isotope path readout."""

from __future__ import annotations

import math
import unittest

import hqiv_kinetic_isotope_readout as kie


class TestKineticIsotopeReadout(unittest.TestCase):
    def test_heavier_tunnels_less(self) -> None:
        e, v, L = 0.0, 0.1, 1.0
        t_h = kie.path_tunnel_transmission(1000.0, e, v, L)
        t_d = kie.path_tunnel_transmission(2000.0, e, v, L)
        self.assertGreater(t_h, t_d)
        self.assertGreaterEqual(kie.kinetic_isotope_effect(1000.0, 2000.0, e, v, L), 1.0)

    def test_h2_d2_masses(self) -> None:
        mu_l, mu_h, _, _ = kie.isotope_pair_masses("H2/D2")
        self.assertLess(mu_l, mu_h)

    def test_audit_identity(self) -> None:
        audit = kie.build_kinetic_isotope_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        self.assertGreaterEqual(len(audit["rows"]), 4)
        self.assertEqual(len(audit["core_subset"]), 4)
        for row in audit["rows"]:
            self.assertNotIn("error", row)
            self.assertGreaterEqual(row["KIE"], 1.0)
            self.assertGreaterEqual(row["KIE_secondary"], 1.0)
            self.assertLessEqual(row["KIE_secondary"], row["KIE_zpe"] + 1e-12)

    def test_secondary_identity_and_softener(self) -> None:
        self.assertAlmostEqual(kie.secondary_kinetic_isotope_effect(1.0), 1.0, places=12)
        sec = kie.secondary_kinetic_isotope_effect(math.e)
        import hqiv_lean_physics_primitives as lean

        self.assertAlmostEqual(sec, math.exp(lean.GAMMA), places=12)


if __name__ == "__main__":
    unittest.main()
