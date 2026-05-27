#!/usr/bin/env python3
"""Tests for semiprime orthogonal-diagonal factoring."""

from __future__ import annotations

import math
import sys
import unittest
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import hqiv_semiprime_orthogonal_diagonal as spd
import hqiv_reverse_shor_period_selector as rss


def _prod(xs: list[int]) -> int:
    p = 1
    for x in xs:
        p *= x
    return p


class TestSlotMaps(unittest.TestCase):
    def test_reflect_slot_involutive_on_span(self) -> None:
        n = 143
        m = spd.reflection_mod(n)
        for s in (0, 3, 7, 42):
            t = spd.reflect_slot(n, s)
            self.assertEqual(spd.reflect_slot(n, t), s % m)

    def test_cofactor_in_q_window(self) -> None:
        n = 899
        for slot in range(20):
            c = spd.cofactor_candidate_from_slot(n, slot)
            self.assertGreaterEqual(c, 2)
            self.assertLessEqual(c, rss.q_span(n))


class TestPeriodAndCarrier(unittest.TestCase):
    def test_multiplicative_order_15(self) -> None:
        r, tag = spd.multiplicative_order(7, 15)
        self.assertEqual(r, 4)
        self.assertIn(tag, ("brute", "bsgs", "brute_fallback"))

    def test_bsgs_matches_brute_143(self) -> None:
        odd = 143
        for a in (3, 7, 10):
            if math.gcd(a, odd) != 1:
                continue
            rb, _ = spd.multiplicative_order(a, odd, method="brute")
            rbs, _ = spd.multiplicative_order(a, odd, method="bsgs")
            self.assertEqual(rb, rbs)

    def test_prec_scales_with_n(self) -> None:
        small = spd.mpmath_prec_bits_for_n(143, period_r=60)
        large = spd.mpmath_prec_bits_for_n(10**9 + 7, period_r=500_000)
        self.assertGreater(large, small)
        self.assertGreaterEqual(small, 128)

    def test_shor_gcd_from_period(self) -> None:
        # 21 = 3*7, order of 2 mod 21 is 6
        cands = spd.shor_gcd_candidates_from_period(2, 21, 6)
        self.assertIn(3, cands)

    def test_diagonal_carrier_support(self) -> None:
        odd = 143
        L = 11
        carrier, meta = spd.build_diagonal_carrier(L, odd, a=3, r=60)
        self.assertGreater(len(carrier.support), 0)
        self.assertGreater(meta["channel_orthogonality_ratio"], 0.0)
        self.assertGreaterEqual(meta["mpmath_prec_bits"], 128)

    def test_cf_period_matches_for_small(self) -> None:
        odd = 35
        a = 2
        r, _ = spd.multiplicative_order(a, odd)
        self.assertIsNotNone(r)
        _, meta = spd.build_diagonal_carrier(7, odd, a, r)  # type: ignore[arg-type]
        cf = meta.get("cf_period_from_peak")
        if cf is not None:
            self.assertEqual(pow(a, cf, odd), 1)


class TestSemiprimeFactorization(unittest.TestCase):
    def test_factor_143_fast(self) -> None:
        r = spd.semiprime_orthogonal_diagonal_factor(143)
        self.assertTrue(r["success"])
        self.assertEqual(sorted(r["factors"]), [11, 13])

    def test_factor_899(self) -> None:
        r = spd.semiprime_orthogonal_diagonal_factor(899)
        self.assertTrue(r["success"])
        self.assertEqual(sorted(r["factors"]), [29, 31])

    def test_auto_pipeline_143(self) -> None:
        r = rss.reverse_shor_factor(143, pipeline="auto", max_steps=10, max_seconds=0.1)
        self.assertTrue(r["success"])
        self.assertEqual(_prod(r["factors"]), 143)

    def test_medium_semiprime_101_103(self) -> None:
        n = 101 * 103
        r = spd.semiprime_orthogonal_diagonal_factor(n)
        self.assertTrue(r["success"], r)
        self.assertEqual(sorted(r["factors"]), [101, 103])


if __name__ == "__main__":
    unittest.main()
