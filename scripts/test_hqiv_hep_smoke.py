#!/usr/bin/env python3
"""Fast smoke tests (<30s): frozen benchmark contract + diagnostic panel.

Run:
  PYTHONPATH=. python3 -m unittest test_hqiv_hep_smoke -q
"""

from __future__ import annotations

import json
import unittest
from pathlib import Path

import hqiv_repo_paths as paths

ROOT = paths.repo_root(Path(__file__))
BENCHMARK_JSON = ROOT / "data" / "hep_decay_benchmark.json"
OBSERVATIONS_JSON = ROOT / "data" / "hep_decay_observations.json"

STRUCTURAL_PASS = 81
DIAGNOSTIC_COUNT = 17


class HepSmokeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if not BENCHMARK_JSON.is_file():
            raise unittest.SkipTest(f"missing {BENCHMARK_JSON}")
        if not OBSERVATIONS_JSON.is_file():
            raise unittest.SkipTest(f"missing {OBSERVATIONS_JSON}")
        cls.bench = json.loads(BENCHMARK_JSON.read_text(encoding="utf-8"))
        cls.obs = json.loads(OBSERVATIONS_JSON.read_text(encoding="utf-8"))

    def test_structural_pass_count(self) -> None:
        summary = self.bench["summary"]
        self.assertEqual(summary["fail"], 0)
        self.assertEqual(summary["pass"], STRUCTURAL_PASS)

    def test_open_channel_readout_rows(self) -> None:
        readout = sum(1 for row in self.bench["rows"] if row.get("panel") == "readout")
        self.assertEqual(readout, 567)

    def test_diagnostic_panel_definitions(self) -> None:
        panel = self.obs.get("branching_comparison_panel")
        self.assertIsInstance(panel, list)
        self.assertEqual(len(panel), DIAGNOSTIC_COUNT)

    def test_diagnostic_rows_in_benchmark(self) -> None:
        diag_rows = [r for r in self.bench["rows"] if r.get("panel") == "branching_comparison"]
        self.assertEqual(len(diag_rows), DIAGNOSTIC_COUNT)

    def test_jpsi_leptonic_branching(self) -> None:
        row = next(r for r in self.bench["rows"] if r.get("case_id") == "Jpsi_em_ee")
        self.assertAlmostEqual(row["predicted"], 0.059682, places=4)
        self.assertAlmostEqual(row["reference"], 0.059, places=3)
        if row.get("n_sigma") is not None:
            self.assertLess(row["n_sigma"], 1.0)

    def test_curated_diagnostics_within_three_sigma(self) -> None:
        diag_rows = [r for r in self.bench["rows"] if r.get("panel") == "branching_comparison"]
        with_sigma = [r for r in diag_rows if r.get("n_sigma") is not None]
        self.assertGreaterEqual(len(with_sigma), DIAGNOSTIC_COUNT - 2)
        for row in with_sigma:
            self.assertLessEqual(row["n_sigma"], 3.0, msg=row.get("case_id"))

    def test_comparison_layer_quarantine(self) -> None:
        policy = self.obs.get("comparison_policy") or self.bench.get("comparison_policy")
        self.assertIsNotNone(policy)


if __name__ == "__main__":
    unittest.main()
