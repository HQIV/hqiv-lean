#!/usr/bin/env python3
"""Tests for the HQIV alpha_EM IR-running bridge."""

from __future__ import annotations

import json
import math
import unittest

import hqiv_alpha_ir_running as ir


class AlphaIrRunningTests(unittest.TestCase):
    def test_bare_ladder_inverse_roundtrip(self) -> None:
        for m in (1.0, 3.0, 5.0, 14.0, 20.0):
            inv = ir.bare_inv_alpha_at_shell(m)
            self.assertAlmostEqual(ir.shell_for_bare_inv_alpha(inv), m, places=9)

    def test_bare_ladder_monotone_increasing(self) -> None:
        vals = [ir.bare_inv_alpha_at_shell(m) for m in range(0, 25)]
        self.assertTrue(all(b > a for a, b in zip(vals, vals[1:])))

    def test_w_brace_near_129(self) -> None:
        span = ir.w_to_thomson_span()
        self.assertAlmostEqual(span.w_inv_alpha, 128.93, delta=0.1)
        # W brace sits near ladder shell ~14
        self.assertAlmostEqual(span.w_ladder_shell, 14.24, delta=0.2)

    def test_thomson_crossing_near_shell_20(self) -> None:
        m = ir.shell_for_bare_inv_alpha(ir.CODATA_INV_ALPHA)
        self.assertAlmostEqual(m, 20.2, delta=0.3)

    def test_positive_run_w_to_thomson(self) -> None:
        span = ir.w_to_thomson_span()
        self.assertGreater(span.delta_inv_alpha, 0.0)
        self.assertAlmostEqual(span.pct_run, 6.29, delta=0.2)

    def test_observable_router_none_for_mass(self) -> None:
        self.assertIsNone(ir.alpha_for_observable("atomic_mass"))
        self.assertIsNone(ir.alpha_for_observable("nuclear_binding"))
        self.assertIsNone(ir.alpha_for_observable("outside_curvature_fight"))

    def test_observable_router_thomson_for_spectroscopy(self) -> None:
        a = ir.alpha_for_observable("fine_structure_spectroscopy")
        self.assertIsNotNone(a)
        assert a is not None
        self.assertAlmostEqual(1.0 / a, ir.CODATA_INV_ALPHA, places=6)

    def test_observable_router_global_brace_for_tuft(self) -> None:
        a = ir.alpha_for_observable("tuft_sector_determinant")
        self.assertIsNotNone(a)
        assert a is not None
        self.assertAlmostEqual(1.0 / a, ir.ew_brace_inv_alpha(), places=6)

    def test_unknown_observable_raises(self) -> None:
        with self.assertRaises(KeyError):
            ir.alpha_for_observable("not_a_real_observable")

    def test_report_json_roundtrip(self) -> None:
        report = ir.build_report()
        payload = json.dumps(report.to_dict())
        loaded = json.loads(payload)
        self.assertIn("scale_points", loaded)
        self.assertIn("w_to_thomson", loaded)
        self.assertEqual(len(loaded["observable_policies"]), 9)
        # need fields serialize as plain strings
        needs = {p["need"] for p in loaded["observable_policies"]}
        self.assertTrue(needs.issubset({"none", "global_brace", "ir_thomson", "shell_local_ratio"}))


if __name__ == "__main__":
    unittest.main()
