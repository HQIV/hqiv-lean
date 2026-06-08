#!/usr/bin/env python3
"""Tests for reverse Shor / classical OSH period selector."""

from __future__ import annotations

import math
import sys
import unittest
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import hqiv_reverse_shor_period_selector as rss
import hqiv_quantum_gate_alias_probe as osh


def _prod(xs: list[int]) -> int:
    p = 1
    for x in xs:
        p *= x
    return p


def _is_prime_guess(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


class TestKetFallbackAlignment(unittest.TestCase):
    def test_ket_residual_mod_small_n(self) -> None:
        self.assertEqual(rss.ket_residual_mod(1), 1)
        self.assertEqual(rss.ket_residual_mod(4), 1)

    def test_ket_linear_fallback_matches_q_span_window(self) -> None:
        n = 143
        L = 11
        for idx in (0, 7, 42, 100):
            c = rss.ket_linear_fallback_candidate(L, n, idx)
            q = rss.q_span(n)
            self.assertGreaterEqual(c, 2)
            self.assertLessEqual(c, q)


class TestCarrierPeaking(unittest.TestCase):
    def test_carrier_merges_colliding_indices(self) -> None:
        L = 5
        reg = [
            osh.SparseKet(idx=3, amp=1.0),
            osh.SparseKet(idx=3 + osh.sparse_basis_card(L), amp=2.0),
        ]
        c = rss.carrier_from_sparse(L, reg)
        self.assertEqual(c.support, (3,))
        self.assertAlmostEqual(c.amp(3), 3.0)

    def test_mirror_witness_on_reflected_pair(self) -> None:
        L = 7
        pivot = 5
        mirror_idx = rss.reflect_flat_index(L, pivot)
        carrier = rss.SuperpositionCarrier(
            support=(pivot, mirror_idx),
            amps={pivot: 1.0, mirror_idx: 1.0},
        )
        found = False
        for tq in range(4):
            if rss.peak_support_pair(carrier, L, tq, pivot):
                found = True
                witnesses = rss.find_mirror_witnesses(L, 35, carrier, target_qubits=(tq,))
                self.assertGreater(len(witnesses), 0)
                w = witnesses[0]
                self.assertEqual(
                    w.pivot_candidate,
                    rss.ket_linear_fallback_candidate(L, 35, pivot),
                )
                break
        self.assertTrue(found, "expected some target_qubit to see mirror flip")


class TestPeriodSelectorSoundness(unittest.TestCase):
    def test_certify_matches_odd_core_witness(self) -> None:
        self.assertTrue(rss.certify_odd_core_divisor(35, 5))
        self.assertFalse(rss.certify_odd_core_divisor(35, 1))
        self.assertFalse(rss.certify_odd_core_divisor(35, 35))
        self.assertFalse(rss.certify_odd_core_divisor(35, 4))

    def test_period_selector_candidates_include_gcd(self) -> None:
        L = 11
        odd = 143
        carrier = rss.SuperpositionCarrier(support=(0, 1), amps={0: 1.0, 1: 1.0})
        peak = rss.LogicMirrorPeak(
            L=L, target_qubit=0, pivot=0, mirror_flat=rss.reflect_flat_index(L, 0), flips_target=True
        )
        w = rss.PeriodMirrorWitness(
            carrier=carrier,
            peak=peak,
            pivot_candidate=22,
            mirror_candidate=11,
        )
        cands = rss.period_selector_candidates(w, odd)
        self.assertIn(11, cands)
        self.assertIn(math.gcd(22, odd), cands)


class TestFactorization(unittest.TestCase):
    def test_factor_15(self) -> None:
        r = rss.reverse_shor_factor(15, max_steps=80, max_seconds=3.0)
        self.assertTrue(r["success"])
        self.assertEqual(sorted(r["factors"]), [3, 5])
        self.assertEqual(_prod(r["factors"]), 15)

    def test_factor_143(self) -> None:
        r = rss.reverse_shor_factor(143, max_steps=200, max_seconds=5.0)
        self.assertTrue(r["success"])
        self.assertEqual(sorted(r["factors"]), [11, 13])
        self.assertEqual(_prod(r["factors"]), 143)

    def test_factor_21_and_35(self) -> None:
        for n, expected in ((21, [3, 7]), (35, [5, 7])):
            with self.subTest(n=n):
                r = rss.reverse_shor_factor(n, max_steps=120, max_seconds=3.0)
                self.assertTrue(r["success"], r)
                self.assertEqual(sorted(r["factors"]), expected)

    def test_product_invariant_small_composites(self) -> None:
        failures: list[tuple[int, dict]] = []
        for n in range(4, 120):
            if _is_prime_guess(n):
                continue
            r = rss.reverse_shor_factor(n, max_steps=100, max_seconds=1.5)
            if r["success"]:
                self.assertEqual(_prod(r["factors"]), n)
            else:
                failures.append((n, r))
        semiprime_checks = [n for n in range(4, 120) if not _is_prime_guess(n)]
        semiprime_hits = sum(
            1
            for n in semiprime_checks
            if rss.reverse_shor_factor(n, max_steps=100, max_seconds=1.5)["success"]
        )
        self.assertGreaterEqual(
            semiprime_hits / max(1, len(semiprime_checks)),
            0.5,
            f"semiprime hit rate low; sample failures={failures[:5]}",
        )


class TestRecursive(unittest.TestCase):
    def test_recursive_143(self) -> None:
        r = rss.recursive_prime_factorization_reverse_shor(
            143, max_steps_per_node=200, max_seconds_per_node=3.0
        )
        self.assertTrue(r["verified_product"])
        self.assertEqual(r["prime_factors"], [11, 13])


if __name__ == "__main__":
    unittest.main()
