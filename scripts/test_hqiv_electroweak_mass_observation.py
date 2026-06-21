#!/usr/bin/env python3
"""Tests for electroweak mass observation witness v2."""

from __future__ import annotations

import json
import unittest
from pathlib import Path

import hqiv_electroweak_mass_benchmark as emb
import hqiv_electroweak_mass_observation as emo

ROOT = Path(__file__).resolve().parents[1]
OBS = ROOT / "data" / "electroweak_mass_observations.json"


class TestLineShapeMassFactor(unittest.TestCase):
    def test_radiative_stack_fifteen_gamma_over_sixtyfour(self) -> None:
        self.assertAlmostEqual(emo.line_shape_radiative_stack_density(), 15.0 * emo.GAMMA / 64.0)

    def test_line_shape_factor_above_unity(self) -> None:
        self.assertGreater(emo.line_shape_mass_factor(), 1.0)

    def test_lep_uses_line_shape_not_collider(self) -> None:
        facilities = emo.load_facilities(json.loads(OBS.read_text()))
        lep = facilities["lep_line_shape"]
        self.assertEqual(lep.dressing_chart, "line_shape")
        self.assertAlmostEqual(lep.facility_mass_dressing_factor(), emo.line_shape_mass_factor())


class TestFacilityDressing(unittest.TestCase):
    def test_cdf_universal_b_ref(self) -> None:
        facilities = emo.load_facilities(json.loads(OBS.read_text()))
        cdf = facilities["cdf_tevatron"]
        self.assertAlmostEqual(cdf.effective_collider_reference_tesla(), 4.0)

    def test_cms_native_b_ref(self) -> None:
        facilities = emo.load_facilities(json.loads(OBS.read_text()))
        cms = facilities["cms_lhc"]
        self.assertAlmostEqual(cms.effective_collider_reference_tesla(), 3.8)
        self.assertAlmostEqual(cms.kinematic_coupling_exponent, emo.KINEMATIC_COUPLING_EXPONENT_LHC)

    def test_lep_dressing_lt_cdf(self) -> None:
        facilities = emo.load_facilities(json.loads(OBS.read_text()))
        self.assertLess(
            facilities["lep_line_shape"].facility_mass_dressing_factor(),
            facilities["cdf_tevatron"].facility_mass_dressing_factor(),
        )


class TestBenchmarkWitness(unittest.TestCase):
    def setUp(self) -> None:
        self.observations = json.loads(OBS.read_text())

    def test_cdf_within_2sigma(self) -> None:
        rows = emb.benchmark_tension_panel(self.observations)
        row = next(r for r in rows if r.case_id == "hqiv_cdf_within_2sigma")
        self.assertEqual(row.panel, "diagnostic")
        self.assertEqual(row.status, "readout")
        assert row.n_sigma is not None
        self.assertLessEqual(row.n_sigma, 2.0)

    def test_lep_within_2sigma(self) -> None:
        rows = emb.benchmark_tension_panel(self.observations)
        row = next(r for r in rows if r.case_id == "hqiv_lep_within_2sigma")
        self.assertEqual(row.panel, "diagnostic")
        self.assertEqual(row.status, "readout")

    def test_cms_within_2sigma(self) -> None:
        rows = emb.benchmark_tension_panel(self.observations)
        row = next(r for r in rows if r.case_id == "hqiv_cms_within_2sigma")
        self.assertEqual(row.panel, "diagnostic")
        self.assertEqual(row.status, "readout")

    def test_certified_blend_ordering(self) -> None:
        rows = emb.benchmark_tension_panel(self.observations)
        row = next(r for r in rows if r.case_id == "hqiv_certified_blend_ordering")
        self.assertEqual(row.panel, "diagnostic")
        self.assertEqual(row.status, "readout")

    def test_reference_sm_lt_lep_lt_cdf(self) -> None:
        rows = emb.benchmark_tension_panel(self.observations)
        row = next(r for r in rows if r.case_id == "reference_sm_lt_lep_lt_cdf")
        self.assertEqual(row.status, "pass")

    def test_witness_certificate_has_lean_theorems(self) -> None:
        cert = emo.witness_certificate(self.observations)
        self.assertIn(
            "Hqiv.Physics.lineShapeRadiativeStackDensity_eq_fifteen_gamma_over_sixtyfour",
            cert["lean_theorems"],
        )
        self.assertIn("cdf_tevatron", cert["predictions"])

    def test_lean_preset_matches_d0_exponent(self) -> None:
        facilities = emo.load_facilities(self.observations)
        d0 = facilities["d0_tevatron"]
        self.assertAlmostEqual(d0.kinematic_coupling_exponent, 11.0 / 125.0)
        self.assertAlmostEqual(d0.collider_reference_tesla, 4.0)
        self.assertAlmostEqual(d0.effective_collider_reference_tesla(), 2.0)


if __name__ == "__main__":
    unittest.main()
