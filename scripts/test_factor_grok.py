#!/usr/bin/env python3
"""Tests for `factor_grok.py` (octonion_factor)."""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
_MOD = _SCRIPTS / "factor_grok.py"

_spec = importlib.util.spec_from_file_location("factor_grok", _MOD)
assert _spec and _spec.loader
fg = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fg)


def _prod(xs: list[int]) -> int:
    p = 1
    for x in xs:
        p *= x
    return p


class TestOctonionFactor(unittest.TestCase):
    def test_trivial(self) -> None:
        self.assertEqual(fg.octonion_factor(1), [])

    def test_prime(self) -> None:
        self.assertEqual(fg.octonion_factor(17), [17])

    def test_small_semiprimes_split(self) -> None:
        for p, q in ((17, 19), (101, 103)):
            with self.subTest(p=p, q=q):
                n = p * q
                out = fg.octonion_factor(n)
                self.assertEqual(sorted(out), sorted([p, q]))
                self.assertEqual(_prod(out), n)

    def test_143(self) -> None:
        self.assertEqual(fg.octonion_factor(143), [11, 13])

    def test_product_invariant_small_range(self) -> None:
        for n in range(2, 300):
            fac = fg.octonion_factor(n)
            self.assertEqual(_prod(fac), n, msg=f"n={n} -> {fac}")


if __name__ == "__main__":
    unittest.main()
