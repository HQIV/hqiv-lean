#!/usr/bin/env python3
"""Unit tests for discrete saddle / defect formation readouts."""

from __future__ import annotations

import unittest

import hqiv_chemistry_coupled_readout as ccr
import hqiv_discrete_saddle_defect_readout as dsd
import hqiv_lean_physics_primitives as lean


class TestDiscreteSaddleDefect(unittest.TestCase):
    def test_defect_zero_at_delta0(self) -> None:
        self.assertEqual(dsd.defect_formation_energy_ev(5.0, 0.0), 0.0)

    def test_saddle_nil_and_max(self) -> None:
        self.assertEqual(dsd.discrete_saddle_barrier_ev([]), 0.0)
        self.assertEqual(dsd.discrete_saddle_barrier_ev([-1.0, 2.0, 0.5]), 2.0)

    def test_graphene_is_bind_over_20(self) -> None:
        e = dsd.defect_formation_energy_ev(4.0, 0.25)
        self.assertAlmostEqual(e, 4.0 / 20.0, places=12)

    def test_transmission_open_and_softens(self) -> None:
        self.assertAlmostEqual(ccr.barrier_transmission_from_gate(0.0, 1.0), 1.0)
        t = ccr.barrier_transmission_from_gate(1.0, 1.0)
        self.assertGreater(t, 0.0)
        self.assertLess(t, 1.0)

    def test_activation_open(self) -> None:
        self.assertAlmostEqual(ccr.activation_rate_from_saddle(3.0, 0.0, 1.0), 3.0)

    def test_harmonic_gate_strong_sq(self) -> None:
        self.assertAlmostEqual(
            dsd.harmonic_saddle_gate_ev(4.0),
            (lean.STRONG_CHANNEL_FRACTION**2) * 4.0,
        )

    def test_vacancy_excess(self) -> None:
        self.assertAlmostEqual(dsd.vacancy_excess(6.0), 1.0 / 6.0)
        self.assertAlmostEqual(dsd.vacancy_excess(4.0), 0.25)

    def test_vacancy_formation_is_defect_over_cn(self) -> None:
        e_def = dsd.defect_formation_energy_ev(6.0, 1.0 / 6.0)
        e_vac = dsd.vacancy_formation_energy_ev(6.0, 1.0 / 6.0, 6.0)
        self.assertAlmostEqual(e_vac, e_def / 6.0, places=12)
        # E_bind · γ · (4/8) / CN²
        expect = 6.0 * lean.GAMMA * lean.STRONG_CHANNEL_FRACTION / 36.0
        self.assertAlmostEqual(e_vac, expect, places=12)

    def test_grain_boundary_is_gamma_vacancy(self) -> None:
        e_vac = dsd.vacancy_formation_energy_ev(6.0, 1.0 / 6.0, 6.0)
        e_gb = dsd.grain_boundary_formation_energy_ev(6.0, 1.0 / 6.0, 6.0)
        self.assertAlmostEqual(e_gb, lean.GAMMA * e_vac, places=12)

    def test_audit_identity_checks(self) -> None:
        payload = dsd.build_audit()
        self.assertTrue(payload["all_identity_checks_pass"])
        self.assertTrue(payload["carbon_fork"]["ratio_matches_lean"])
        nacl = next(r for r in payload["crystal_rows"] if r["name"] == "NaCl")
        self.assertIn("vacancy_formation_energy_eV", nacl)
        self.assertLess(
            nacl["vacancy_formation_energy_eV"], nacl["defect_formation_energy_eV"]
        )


if __name__ == "__main__":
    unittest.main()
