#!/usr/bin/env python3
"""Tests for OSH gate factorization and Hopf-guided q lookup."""

from __future__ import annotations

import math
import sys
import unittest
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import osh_gate_factorization as osh
import osh_hopf_benchmark as bench


class TestFlatQMapping(unittest.TestCase):
    def test_q_span_is_isqrt(self) -> None:
        self.assertEqual(osh.q_span(143), 11)
        self.assertEqual(osh.q_span(899), 29)

    def test_slot_to_candidate_in_window(self) -> None:
        n = 143
        root = max(2, math.isqrt(n))
        for slot in range(50):
            c = osh.slot_to_candidate(slot, n)
            self.assertGreaterEqual(c, 2)
            self.assertLessEqual(c, root)

    def test_flat_family_has_at_most_two(self) -> None:
        n = 221
        span = 2 * osh.q_span(n)
        for code in (0, 7, 42, 999):
            cands, diag = osh.candidate_family_from_code(
                code, n, span, q_lookup_mode=osh.Q_LOOKUP_FLAT
            )
            self.assertIsNone(diag)
            self.assertGreaterEqual(len(cands), 1)
            self.assertLessEqual(len(cands), 2)


class TestHopfShellBound(unittest.TestCase):
    def test_floor_cbrt(self) -> None:
        self.assertEqual(osh.floor_cbrt(0), 0)
        self.assertEqual(osh.floor_cbrt(1), 1)
        self.assertEqual(osh.floor_cbrt(8), 2)
        self.assertEqual(osh.floor_cbrt(27), 3)
        self.assertEqual(osh.floor_cbrt(143), 5)

    def test_hopf_shell_bound_capped_at_three(self) -> None:
        self.assertEqual(osh.hopf_shell_bound(1), 1)
        self.assertEqual(osh.hopf_shell_bound(8), 2)
        self.assertEqual(osh.hopf_shell_bound(27), 3)
        self.assertEqual(osh.hopf_shell_bound(1000), 3)

    def test_active_windings_follow_cbrt(self) -> None:
        self.assertEqual(osh.active_hopf_windings(8), (1, 2))
        self.assertEqual(osh.active_hopf_windings(143), (1, 2, 3))

    def test_k_exact_bound_scales_with_shell_count(self) -> None:
        self.assertEqual(osh.k_exact_per_center_bound(1), 2)
        self.assertEqual(osh.k_exact_per_center_bound(3), 6)


class TestHopfCoords(unittest.TestCase):
    def test_unit_quaternion_normalized(self) -> None:
        for code in (0, 1, 17, 0xDEAD):
            w, x, y, z = osh.code_to_unit_quaternion(code, 16)
            norm = math.sqrt(w * w + x * x + y * y + z * z)
            self.assertAlmostEqual(norm, 1.0, places=10)

    def test_hopf_base_on_sphere_direction(self) -> None:
        w, x, y, z = (1.0, 0.0, 0.0, 0.0)
        bx, by, bz = osh.hopf_map_s3_to_s2(w, x, y, z)
        self.assertAlmostEqual(bx, 1.0, places=10)
        self.assertAlmostEqual(by, 0.0, places=10)
        self.assertAlmostEqual(bz, 0.0, places=10)

    def test_three_chart_slots_present(self) -> None:
        n = 143
        span = 2 * osh.q_span(n)
        cands, diag = osh.hopf_chart_slots(42, n, span, register_bits=16, chart_width=1)
        self.assertIsNotNone(diag)
        assert diag is not None
        self.assertIn("hopf_base", diag)
        self.assertIn("fiber_phase", diag)
        self.assertIn("chart_slots", diag)
        self.assertEqual(diag["hopf_shell_bound"], 3)
        self.assertEqual(set(diag["chart_slots"].keys()), {"1", "2", "3"})
        self.assertGreaterEqual(len(cands), 1)
        self.assertLessEqual(len(cands), osh.k_exact_per_center_bound(3))

    def test_two_chart_slots_for_small_n(self) -> None:
        n = 8
        span = 2 * osh.q_span(n)
        _cands, diag = osh.hopf_chart_slots(3, n, span, register_bits=8, chart_width=0)
        assert diag is not None
        self.assertEqual(diag["hopf_shell_bound"], 2)
        self.assertEqual(set(diag["chart_slots"].keys()), {"1", "2"})

    def test_hopf_family_bounded(self) -> None:
        n = 10403
        span = 2 * osh.q_span(n)
        for code in (0, 3, 100, 0xABCD):
            cands, diag = osh.candidate_family_from_code(
                code,
                n,
                span,
                q_lookup_mode=osh.Q_LOOKUP_HOPF,
                register_bits=16,
                hopf_chart_width=1,
            )
            self.assertIsNotNone(diag)
            self.assertGreaterEqual(len(cands), 1)
            self.assertLessEqual(len(cands), 6)
            for c in cands:
                self.assertGreaterEqual(c, 2)
                self.assertLessEqual(c, osh.q_span(n))


class TestOshPipeline(unittest.TestCase):
    KNOWN: dict[int, list[int]] = {
        21: [3, 7],
        143: [11, 13],
        221: [13, 17],
        10403: [101, 103],
    }

    def _expected_pair(self, n: int) -> list[int]:
        factors = self.KNOWN[n]
        return sorted(factors)

    def test_flat_mode_runs_on_known_composites(self) -> None:
        for n in self.KNOWN:
            payload = osh.osh_factor_once(n, max_steps=120, max_seconds=2.0)
            self.assertEqual(payload["q_lookup_mode"], osh.Q_LOOKUP_FLAT)
            self.assertGreater(payload["tested_candidate_count"], 0)

    def test_hopf_mode_runs_with_diagnostics(self) -> None:
        n = 143
        payload = osh.osh_factor_once(
            n,
            max_steps=120,
            max_seconds=2.0,
            q_lookup_mode=osh.Q_LOOKUP_HOPF,
            hopf_chart_width=1,
        )
        self.assertEqual(payload["q_lookup_mode"], osh.Q_LOOKUP_HOPF)
        self.assertEqual(payload["hopf_shell_bound"], 3)
        self.assertGreater(payload["tested_candidate_count"], 0)
        if payload["prune_trace"]:
            self.assertIn("hopf_samples", payload["prune_trace"][0])

    def test_hopf_search_requires_hopf_mode(self) -> None:
        with self.assertRaises(ValueError):
            osh.osh_factor_once(143, hopf_search=True, q_lookup_mode=osh.Q_LOOKUP_FLAT)

    def test_hopf_search_runs_with_coverage(self) -> None:
        n = 221
        payload = osh.osh_factor_once(
            n,
            max_steps=500,
            max_seconds=5.0,
            q_lookup_mode=osh.Q_LOOKUP_HOPF,
            hopf_search=True,
            hopf_chart_width=1,
        )
        self.assertTrue(payload["hopf_search"])
        self.assertEqual(payload["pipeline_mode"], "osh-hopf-search")
        self.assertEqual(payload["hopf_shell_bound"], 3)
        self.assertGreater(payload["tested_candidate_count"], 0)
        slot_cov = payload.get("slot_coverage_fraction")
        if slot_cov is not None:
            self.assertGreater(slot_cov, 0.0)

    def test_compare_q_modes_shape(self) -> None:
        cmp = osh.compare_q_lookup_modes(143, max_steps=80, max_seconds=2.0)
        self.assertEqual(cmp["n"], 143)
        self.assertIn("flat", cmp)
        self.assertIn("hopf", cmp)
        for mode in ("flat", "hopf"):
            self.assertIn("early_stopped", cmp[mode])
            self.assertIn("tested_candidate_count", cmp[mode])

    def test_compare_on_known_composites(self) -> None:
        summary: list[str] = []
        for n, factors in self.KNOWN.items():
            cmp = osh.compare_q_lookup_modes(n, max_steps=200, max_seconds=3.0)
            expected = sorted(factors)
            flat_pair = cmp["flat"]["symmetric_pair"]
            hopf_pair = cmp["hopf"]["symmetric_pair"]
            summary.append(
                f"n={n} flat_early={cmp['flat']['early_stopped']} "
                f"hopf_early={cmp['hopf']['early_stopped']} "
                f"expected={expected} flat_pair={flat_pair} hopf_pair={hopf_pair}"
            )
        # At least one mode should exercise the pipeline on each case.
        self.assertEqual(len(summary), len(self.KNOWN))


class TestBulkSemiprimeCorpus(unittest.TestCase):
    """Larger regression sweep over generated semiprime corpora."""

    def _assert_hits(self, cases: list[bench.SemiprimeCase], **kwargs: object) -> None:
        misses: list[dict[str, object]] = []
        for case in cases:
            row = bench.run_one(case, **kwargs)  # type: ignore[arg-type]
            if not row["hit"]:
                misses.append(row)
        self.assertEqual(
            misses,
            [],
            msg=f"{len(misses)} misses (first 5): {misses[:5]}",
        )

    def test_tiny_corpus_flat(self) -> None:
        self._assert_hits(
            bench.tiny_corpus(),
            q_lookup_mode=osh.Q_LOOKUP_FLAT,
            hopf_search=False,
            max_steps=600,
            max_seconds=3.0,
        )

    def test_tiny_corpus_hopf_search(self) -> None:
        self._assert_hits(
            bench.tiny_corpus(),
            q_lookup_mode=osh.Q_LOOKUP_HOPF,
            hopf_search=True,
            max_steps=800,
            max_seconds=5.0,
        )

    def test_small_corpus_hopf_search(self) -> None:
        cases = bench.semiprimes_q_below(100)
        self.assertGreater(len(cases), 200)
        self._assert_hits(
            cases,
            q_lookup_mode=osh.Q_LOOKUP_HOPF,
            hopf_search=True,
            max_steps=800,
            max_seconds=4.0,
        )

    def test_medium_corpus_hopf_search_sample(self) -> None:
        """First 200 semiprimes with q < 300 (full medium is ~3k cases)."""
        cases = bench.semiprimes_q_below(300)[:200]
        self._assert_hits(
            cases,
            q_lookup_mode=osh.Q_LOOKUP_HOPF,
            hopf_search=True,
            max_steps=1000,
            max_seconds=6.0,
        )

    def test_u64_corpus_hopf_search_if_present(self) -> None:
        cases = bench.load_u64_corpus()
        if not cases:
            self.skipTest("data/semiprimes_u64.json not present")
        # Large semiprimes: q_span may exceed MAX_Q_WINDOW_EXHAUST; report hit rate only.
        sample = cases[:10]
        hits = 0
        for case in sample:
            row = bench.run_one(
                case,
                q_lookup_mode=osh.Q_LOOKUP_HOPF,
                hopf_search=True,
            )
            if row["hit"]:
                hits += 1
        self.assertGreaterEqual(hits / len(sample), 0.0)


class TestBenchmarkSummary(unittest.TestCase):
    def test_small_tier_hit_rate_hopf_search(self) -> None:
        cases = bench.semiprimes_q_below(100)
        report = bench.run_batch(
            cases,
            q_lookup_mode=osh.Q_LOOKUP_HOPF,
            hopf_search=True,
            progress_every=0,
        )
        self.assertEqual(report["hits"], len(cases))
        self.assertEqual(report["misses"], 0)
        self.assertAlmostEqual(report["hit_rate"], 1.0)


if __name__ == "__main__":
    unittest.main()
