#!/usr/bin/env python3
"""
Tests for `factor_from_curvature.py`.

Includes **large semiprimes** n = p*q with min(p,q) > 257 so `deterministic_small_prime_factor`
(trial primes up to min(⌊n^{1/k}⌋, 257)) cannot succeed on the first pass; the oracle must
use the 3-spiral mask (neighbor-shell seeds) and prime-gradient walk.
"""

from __future__ import annotations

import sys
import unittest
from fractions import Fraction
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import factor_from_curvature as ffc  # noqa: E402


def _factor_list(n: int, *, phase_shell_mode: str = "n") -> list[int]:
    factors, _ = ffc.recursive_prime_gradient_factorization(
        n=n,
        curvature=Fraction(0, 1),
        phi=1.0,
        t=1.0,
        window=8,
        arity=2,
        depth=16,
        omega_mode="rational",
        phase_shell_mode=phase_shell_mode,
    )
    return factors


class TestLargeSemiprimes(unittest.TestCase):
    """Both primes > 257 — trial division to 257 cannot split n outright."""

    CASES: tuple[tuple[int, tuple[int, int]], ...] = (
        (263 * 269, (263, 269)),  # 70747
        (269 * 271, (269, 271)),  # 72899
        (311 * 313, (311, 313)),  # 97343
    )

    def test_recursive_factorization_matches_expected(self) -> None:
        for n, (p, q) in self.CASES:
            with self.subTest(n=n):
                fac = _factor_list(n)
                self.assertEqual(sorted(fac), sorted([p, q]), f"n={n}: got {fac}")

    def test_first_gradient_step_not_small_prime_guard_only(self) -> None:
        """First peel should not be the cheap `deterministic_small_prime_guard` shortcut."""
        n = 263 * 269
        _, trace = ffc.recursive_prime_gradient_factorization(
            n=n,
            curvature=Fraction(0, 1),
            phi=1.0,
            t=1.0,
            window=8,
            arity=2,
            depth=16,
            omega_mode="rational",
            phase_shell_mode="n",
        )
        self.assertTrue(trace, "expected non-empty gradient trace")
        self.assertNotEqual(
            trace[0].get("strategy"),
            "deterministic_small_prime_guard",
            "large semiprime should not factor on the ≤257 trial guard alone",
        )

    def test_large_semiprime_phase_shell_neighbor_curve_mid(self) -> None:
        n = 311 * 313
        fac = _factor_list(n, phase_shell_mode="neighbor_curve_mid")
        self.assertEqual(sorted(fac), [311, 313])


class TestSmallCompositeSanity(unittest.TestCase):
    """Regression: obvious small factors still resolve."""

    def test_even_and_small_prime(self) -> None:
        self.assertEqual(_factor_list(221), [13, 17])
        self.assertEqual(_factor_list(10403), [101, 103])

    def test_sixteen_is_powers_of_two(self) -> None:
        """Even shell: peel 2 repeatedly; factor list is all twos (not [2, 2, 4])."""
        self.assertEqual(_factor_list(16), [2, 2, 2, 2])


class TestPlasticShellLatticePoints(unittest.TestCase):
    def test_returns_baseline_and_new_sets(self) -> None:
        out = ffc.plastic_shell_new_lattice_points(221, plastic_steps=6, neighbor_window=1)
        self.assertEqual(out["m"], 221)
        self.assertIn("baseline_points", out)
        self.assertIn("new_points", out)
        self.assertIn("all_points", out)
        self.assertTrue(out["all_points"], "expected non-empty candidate lattice set")
        self.assertGreater(len(out["baseline_points"]), 0)

    def test_zero_plastic_steps_has_no_new_points(self) -> None:
        out = ffc.plastic_shell_new_lattice_points(221, plastic_steps=0, neighbor_window=1, adaptive_budget=False)
        self.assertEqual(out["new_points"], [])

    def test_angle_family_and_diophantine_score_present(self) -> None:
        out = ffc.plastic_shell_new_lattice_points(221, plastic_steps=6, neighbor_window=1)
        self.assertGreaterEqual(len(out["plastic_angle_family_rad"]), 3)
        self.assertTrue(out["all_points"])
        self.assertIn("diophantine_score", out["all_points"][0])

    def test_adaptive_budget_expands_steps(self) -> None:
        out = ffc.plastic_shell_new_lattice_points(221, plastic_steps=2, neighbor_window=1, adaptive_budget=True)
        self.assertGreaterEqual(out["plastic_steps"], 2)


class TestShellToSumOfCubesPlastic(unittest.TestCase):
    def test_find_small_constructible_example(self) -> None:
        out = ffc.shell_to_sum_of_cubes(3, plastic_steps=12, cube_window=8)
        self.assertTrue(out["found"])
        a, b, c = out["triple"]
        self.assertEqual(a**3 + b**3 + c**3, 3)

    def test_mod9_obstruction_reported(self) -> None:
        out = ffc.shell_to_sum_of_cubes(4, plastic_steps=12, cube_window=8)
        self.assertFalse(out["found"])
        self.assertEqual(out["reason"], "mod9_obstruction")


class TestArcStepAdditions(unittest.TestCase):
    def test_additions_is_set_difference(self) -> None:
        m = 7
        out = ffc.arc_additions_at_shell_step(m, arc_half_width_deg=8.0, plane="xy")
        cur = ffc.select_arc_45(ffc.voxel_sphere_surface(m, thickness=0.5), arc_half_width_deg=8.0, plane="xy")
        prev = ffc.select_arc_45(ffc.voxel_sphere_surface(m - 1, thickness=0.5), arc_half_width_deg=8.0, plane="xy")
        expected = sorted(cur.difference(prev))
        self.assertEqual(out["additions"], expected)
        self.assertEqual(out["additions_count"], len(expected))

    def test_m_zero_has_all_current_as_additions(self) -> None:
        out = ffc.arc_additions_at_shell_step(0, arc_half_width_deg=10.0, plane="xy")
        self.assertEqual(out["previous_arc_count"], 0)
        self.assertEqual(out["additions_count"], out["current_arc_count"])


if __name__ == "__main__":
    unittest.main()
