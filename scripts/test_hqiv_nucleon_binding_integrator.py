#!/usr/bin/env python3
"""Tests for the nucleon-binding faithful integrator."""

from __future__ import annotations

import math
import unittest

import hqiv_nucleon_binding_integrator as nbi
import hqiv_nucleon_binding_lean_primitives as lean_p


class TestLeanPrimitives(unittest.TestCase):
    def test_imprinted_mass_budget_closes_reference(self) -> None:
        m_der = 2800.0
        m_ref = 2808.92113298
        kappa = lean_p.curvature_mass_imprint(m_ref, m_der)
        self.assertAlmostEqual(lean_p.imprinted_mass_budget(m_der, kappa), m_ref, places=3)

    def test_uniform_imprint_preserves_gap_minus_m_e(self) -> None:
        kappa = 1.01
        m_p, m_d, m_e = 2800.0, 2790.0, 0.511
        q = lean_p.beta_minus_endpoint_q_uniform_imprint(kappa, m_p, m_d, m_e)
        self.assertAlmostEqual(q, kappa * (m_p - m_d) - m_e, places=9)

    def test_resonance_half_life_matches_width(self) -> None:
        delta = 1.0
        gamma = lean_p.decay_width_per_s(delta)
        self.assertAlmostEqual(
            lean_p.half_life_from_width(gamma),
            lean_p.resonance_half_life(delta),
            places=12,
        )


class TestIntegrator(unittest.TestCase):
    def test_payload_builds(self) -> None:
        payload = nbi.build_payload()
        self.assertIn("mass_panel", payload)
        self.assertEqual(len(payload["mass_panel"]), 6)

    def test_mean_mass_error_below_one_percent(self) -> None:
        payload = nbi.build_payload()
        err = payload["summary"]["light_panel_mean_mass_error_pct"]
        self.assertLess(err, 1.0)

    def test_neutron_lifetime_near_reference(self) -> None:
        payload = nbi.build_payload()
        ratio = payload["summary"]["tau_n_over_reference"]
        self.assertTrue(math.isfinite(ratio))
        self.assertGreater(ratio, 0.99)
        self.assertLess(ratio, 1.01)

    def test_tritium_lifetime_closed_near_reference(self) -> None:
        payload = nbi.build_payload()
        ratio = payload["summary"]["tau_T_over_reference_closed"]
        self.assertTrue(math.isfinite(ratio))
        self.assertGreater(ratio, 0.999)
        self.assertLess(ratio, 1.001)


if __name__ == "__main__":
    unittest.main()
