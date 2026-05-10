#!/usr/bin/env python3
"""Regression tests for Fermat/Lehman, residue gate, and peel integration."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from euclidean_factor_peel import (
    _nondivisor_small_primes,
    _passes_coprime_factor_residue_gate,
    fermat_lehman_try_factor,
    factor_peel_geometric,
    split_once_geometric,
)


class TestFermatLehman(unittest.TestCase):
    def test_fermat_balanced_semiprime(self) -> None:
        d = fermat_lehman_try_factor(221, max_fermat_steps=50_000, lehman_k_max=500)
        self.assertIsNotNone(d)
        assert d is not None
        self.assertIn(d, (13, 17))
        self.assertEqual(221 % d, 0)

    def test_lehman_unbalanced_example(self) -> None:
        # 10403 = 101 * 103; Fermat may be slow; Lehman should find a factor quickly.
        d = fermat_lehman_try_factor(10403, max_fermat_steps=100, lehman_k_max=5000)
        self.assertIsNotNone(d)
        assert d is not None
        self.assertIn(d, (101, 103))


class TestResidueGate(unittest.TestCase):
    def test_filters_impossible_multiples(self) -> None:
        m = 77  # 7 * 11
        nd = _nondivisor_small_primes(m, 20)
        self.assertIn(3, nd)
        self.assertFalse(_passes_coprime_factor_residue_gate(9, nd))
        self.assertTrue(_passes_coprime_factor_residue_gate(7, nd))
        self.assertTrue(_passes_coprime_factor_residue_gate(11, nd))


class TestPeelIntegration(unittest.TestCase):
    def test_small_composite_resolves(self) -> None:
        fac, unres = factor_peel_geometric(
            143,
            small_prime_peel=False,
            fermat_lehman=True,
            residue_gate=True,
        )
        self.assertEqual(unres, [])
        self.assertEqual(sorted(fac), [11, 13])

    def test_split_once_geometric_uses_classical_first(self) -> None:
        d = split_once_geometric(
            221,
            fermat_lehman=True,
            fermat_max_steps=100_000,
            lehman_k_max=500,
            tensor_field=False,
            sqrt_arity_prune=False,
        )
        self.assertIn(d, (13, 17))


if __name__ == "__main__":
    unittest.main()
