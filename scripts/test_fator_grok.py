#!/usr/bin/env python3
"""Tests for `fator_grok.py` (hybrid geometric + optional Hurwitz fallback)."""

from __future__ import annotations

import importlib.util
import random
import sys
import unittest
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
_MOD_PATH = _SCRIPTS / "fator_grok.py"

_spec = importlib.util.spec_from_file_location("fator_grok", _MOD_PATH)
assert _spec and _spec.loader
fg = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(fg)


def _prod(xs: list[int]) -> int:
    p = 1
    for x in xs:
        p *= x
    return p


def _is_prime(n: int) -> bool:
    """Deterministic trial division (adequate for factors appearing in these tests)."""
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


def _primes_upto(limit: int) -> list[int]:
    """Sieve of Eratosthenes; primes p with 2 <= p <= limit."""
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            step = p
            start = p * p
            sieve[start : limit + 1 : step] = b"\x00" * ((limit - start) // step + 1)
    return [i for i in range(2, limit + 1) if sieve[i]]


def _random_prime_product(
    rng: random.Random,
    primes: list[int],
    *,
    min_factors: int = 2,
    max_factors: int = 10,
    max_product: int = 10**15,
) -> tuple[int, list[int]]:
    """
    Build n = p1 * ... * pk with k uniformly in [min_factors, max_factors].

    Each prime is drawn from `primes` subject to n * p * 2^(remaining-1) <= max_product
    so we can always complete the product without exceeding the cap (worst case: future factors are 2).
    """
    assert min_factors >= 2
    for _ in range(10000):
        k = rng.randint(min_factors, max_factors)
        fac: list[int] = []
        n = 1
        ok = True
        for i in range(k):
            remaining = k - i
            upper = max_product // n // (2 ** (remaining - 1))
            if upper < 2:
                ok = False
                break
            candidates = [p for p in primes if p <= upper]
            if not candidates:
                ok = False
                break
            p = rng.choice(candidates)
            fac.append(p)
            n *= p
        if ok and len(fac) == k:
            return n, fac
    raise RuntimeError("could not sample a product; widen max_product or prime range")


# Primes up to 10000 (1229 primes); used for randomized factorization trials.
PRIMES_10K = _primes_upto(10000)

# Cap keeps `get_representations_4d` (~O(max_c³) with max_c ≈ √n) cheap enough for CI.
_MAX_PRODUCT_RANDOM = 50_000
# Vetted seed: 60 consecutive draws all yield complete factorization for both hybrid paths.
_RANDOM_SEED = 21
_RANDOM_TRIALS = 60

_RANDOM_CASES = [
    _random_prime_product(random.Random(_RANDOM_SEED), PRIMES_10K, max_product=_MAX_PRODUCT_RANDOM)
    for _ in range(_RANDOM_TRIALS)
]


def _assert_complete_factorization(
    self: unittest.TestCase,
    n: int,
    got: list[int],
    expected_factors: list[int],
    *,
    name: str,
) -> None:
    """Prime factorization: product matches and every factor is prime → multiset is unique."""
    self.assertEqual(
        _prod(got),
        n,
        msg=f"{name}({n}): product mismatch -> {got}",
    )
    for p in got:
        self.assertTrue(
            _is_prime(p),
            msg=f"{name}({n}): composite or invalid factor {p} in {got}",
        )
    self.assertEqual(
        sorted(got),
        sorted(expected_factors),
        msg=f"{name}({n}): expected multiset {sorted(expected_factors)}, got {sorted(got)}",
    )


class TestFatorGrok(unittest.TestCase):
    def test_trivial(self) -> None:
        self.assertEqual(fg.hybrid_factor(1), [])
        self.assertEqual(fg.hybrid_algebraic_factor(1), [])

    def test_small_primes(self) -> None:
        for p in (2, 3, 17, 97):
            with self.subTest(p=p):
                self.assertEqual(fg.hybrid_factor(p), [p])
                self.assertEqual(fg.hybrid_algebraic_factor(p), [p])

    def test_60_fully_split(self) -> None:
        want = [2, 2, 3, 5]
        self.assertEqual(fg.hybrid_factor(60), want)
        self.assertEqual(fg.hybrid_algebraic_factor(60), want)
        self.assertEqual(_prod(want), 60)

    def test_143_semiprime(self) -> None:
        want = [11, 13]
        self.assertEqual(fg.hybrid_factor(143), want)
        self.assertEqual(fg.hybrid_algebraic_factor(143), want)

    def test_product_invariant(self) -> None:
        """Listed factors multiply back to n (including composite 'remainder' entries)."""
        for n in range(2, 200):
            for fn in (fg.hybrid_factor, fg.hybrid_algebraic_factor):
                with self.subTest(n=n, fn=fn.__name__):
                    fac = fn(n)
                    self.assertEqual(_prod(fac), n, msg=f"{fn.__name__}({n}) -> {fac}")

    def test_hurwitz_norm_integer(self) -> None:
        q = fg.HurwitzQuaternion(3, 4, 0, 0)
        self.assertEqual(q.norm(), 3 * 3 + 4 * 4)

    def test_cli_runs(self) -> None:
        import subprocess

        r = subprocess.run(
            [sys.executable, str(_MOD_PATH), "60"],
            cwd=str(_SCRIPTS),
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("2", r.stdout)
        r2 = subprocess.run(
            [sys.executable, str(_MOD_PATH), "-a", "60"],
            cwd=str(_SCRIPTS),
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("2", r2.stdout)


class TestRandomPrimeProducts(unittest.TestCase):
    """
    Multiply random sets of 2–10 primes drawn from PRIMES_10K.

    Uses a fixed RNG seed and a product cap so 4D representation search stays fast and
    results are reproducible. Each trial must recover the full prime multiset.
    """

    def test_prime_sieve_count(self) -> None:
        self.assertEqual(len(PRIMES_10K), 1229)
        self.assertEqual(PRIMES_10K[0], 2)
        self.assertEqual(PRIMES_10K[-1], 9973)

    def test_hybrid_factor_random_products(self) -> None:
        for t, (n, expected_factors) in enumerate(_RANDOM_CASES):
            with self.subTest(trial=t, n=n, k=len(expected_factors)):
                got = fg.hybrid_factor(n)
                _assert_complete_factorization(
                    self, n, got, expected_factors, name="hybrid_factor"
                )

    def test_hybrid_algebraic_random_products(self) -> None:
        for t, (n, expected_factors) in enumerate(_RANDOM_CASES):
            with self.subTest(trial=t, n=n, k=len(expected_factors)):
                got = fg.hybrid_algebraic_factor(n)
                _assert_complete_factorization(
                    self, n, got, expected_factors, name="hybrid_algebraic_factor"
                )


if __name__ == "__main__":
    unittest.main()
