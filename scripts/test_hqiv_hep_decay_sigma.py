#!/usr/bin/env python3
"""Uncertainty propagation for HEP decay benchmark."""

from __future__ import annotations

import unittest

import hqiv_hep_decay_benchmark as bench
import hqiv_hep_decay_sigma as hsig
import hqiv_lean_physics_primitives as lean


class TestHepDecaySigma(unittest.TestCase):
    def test_predicted_sigma_positive(self) -> None:
        for sid in ("D_plus", "Jpsi", "lambda_c", "B_plus", "p"):
            sig = hsig.predicted_mass_sigma_mev(sid, xi=lean.XI_LOCKIN)
            self.assertGreater(sig, 0.0, msg=sid)

    def test_n_sigma_finite(self) -> None:
        payload = bench.build_payload()
        mass_rows = [r for r in payload["rows"] if r["panel"] == "mass" and r.get("n_sigma")]
        self.assertGreater(len(mass_rows), 5)
        for row in mass_rows:
            self.assertIsNotNone(row["predicted_sigma"])
            if row["case_id"] not in ("p", "n"):
                self.assertLess(row["n_sigma"], 50.0)

    def test_benchmark_sigma_summary(self) -> None:
        payload = bench.build_payload()
        s = payload["summary"]
        self.assertIn("mean_n_sigma", s)
        self.assertIn("max_n_sigma", s)
        self.assertGreater(s["mean_n_sigma"], 0.0)


if __name__ == "__main__":
    unittest.main()
