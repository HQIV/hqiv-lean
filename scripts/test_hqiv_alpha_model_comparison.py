#!/usr/bin/env python3
"""Tests for HQIV alpha_EM model comparison harness."""

from __future__ import annotations

import json
import unittest
from pathlib import Path

import hqiv_alpha_model_comparison as amc
import hqiv_scale_witness as sw


class AlphaModelComparisonTests(unittest.TestCase):
    def test_global_brace_near_129(self) -> None:
        r = amc.global_brace_readout()
        self.assertAlmostEqual(r.inv_alpha, 128.93, delta=0.1)

    def test_nuclear_and_electronic_differ_for_helium(self) -> None:
        panel = amc.build_element_alpha_panel("He")
        self.assertEqual(panel.m_nuc, 6)
        self.assertNotEqual(
            panel.nuclear_tracking.inv_alpha,
            panel.electronic_outermost.inv_alpha,
        )

    def test_hydrogen_nuclear_equals_lockin(self) -> None:
        panel = amc.build_element_alpha_panel("H")
        self.assertEqual(panel.m_nuc, sw.REFERENCE_M)
        self.assertAlmostEqual(
            panel.nuclear_tracking.inv_alpha,
            panel.alpha_eff_lockin.inv_alpha,
        )

    def test_fight_hydrogen_zero(self) -> None:
        fight = amc.fight_diagnostics(1)
        self.assertEqual(fight.canonical_mev, 0.0)
        self.assertEqual(fight.nuclear_ratio_policy_mev, 0.0)

    def test_report_has_uniqueness_audit(self) -> None:
        report = amc.build_comparison_report(elements=("H", "He", "O"))
        self.assertIsNotNone(report.uniqueness_audit)
        self.assertGreater(len(report.uniqueness_audit.why_not_unique), 0)

    def test_json_roundtrip(self) -> None:
        report = amc.build_comparison_report(elements=("H",))
        payload = report.to_dict()
        self.assertIn("uniqueness_audit", payload)
        self.assertEqual(payload["rows"][0]["element"], "H")

    def test_write_json(self) -> None:
        path = Path(__file__).resolve().parents[1] / "data" / "_test_alpha_model_comparison.json"
        report = amc.build_comparison_report(elements=("H",))
        try:
            amc.write_json_report(path, report)
            data = json.loads(path.read_text(encoding="utf-8"))
            self.assertEqual(data["rows"][0]["z"], 1)
        finally:
            if path.exists():
                path.unlink()

    def test_codata_crossing_shell_in_range(self) -> None:
        m = amc.shell_index_matching_inv_alpha(sw.CODATA_INV_ALPHA, m_max=80)
        self.assertGreater(m, 15)
        self.assertLess(m, 30)


if __name__ == "__main__":
    unittest.main()
