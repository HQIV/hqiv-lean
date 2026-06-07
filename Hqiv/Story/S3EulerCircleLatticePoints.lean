import Hqiv.Story.S3SixPolesResidual

/-!
# Gauss-circle lattice points: `r₂(n)` is not "4 for primes" (honesty guardrail)

The "Euler circle / annulus" object is the count `r₂(n)` of lattice points on the
circle `x² + y² = n` — equivalently Gaussian integers of norm `n`. The 4-fold
structure is the unit group `ℤ[i]* = {1, i, -1, -i}` (order 4).

But `r₂` on primes is sharp (Fermat / Gauss–Jacobi), and it is **not** "4":

* prime `p ≡ 1 (mod 4)` ⇒ `r₂(p) = 8` (e.g. `5 = (±1)² + (±2)²` and swaps);
* prime `p ≡ 3 (mod 4)` ⇒ `r₂(p) = 0` (no representation, e.g. `3`);
* only the prime `2` gives `r₂(2) = 4`.

So "if the axis contains a prime there are only 4 lattice points" is false: a prime
gives `8`, `0`, or (just for `2`) `4`. And exactly-`4` (`r₂ = 4`) is realized by
**composites** like `4` and `9` (the pure axis points `(±k,0),(0,±k)`), so the
4-point case is not prime-exclusive either.

This module checks the decisive direction concretely:

* `prime_five_eight_circle_points` — the prime `5` has (at least) **8** lattice
  points, not 4;
* `composite_nine_four_axis_points` — the **composite** `9` realizes the 4 axis
  points.

As in `S3PrimalitySlotDecoupling`, the controlling invariant is sums-of-two-squares
/ factorization `mod 4` (Gaussian arithmetic), which is decoupled from primality.
-/

namespace Hqiv.Story

/-- The prime `5` has **8** lattice points on its Gauss circle `x² + y² = 5`
(`r₂(5) = 8`), not 4. -/
theorem prime_five_eight_circle_points :
    ∃ S : Finset (ℤ × ℤ), S.card = 8 ∧ ∀ p ∈ S, p.1 * p.1 + p.2 * p.2 = 5 := by
  refine ⟨{(1, 2), (2, 1), (-1, 2), (1, -2), (-1, -2), (2, -1), (-2, 1), (-2, -1)},
    ?_, ?_⟩
  · decide
  · decide

/-- The **composite** `9` realizes the four pure axis points on `x² + y² = 9`
(`r₂(9) = 4`); the 4-point case is not prime-exclusive. -/
theorem composite_nine_four_axis_points :
    ¬ Nat.Prime 9 ∧
      ((3 : ℤ) * 3 + 0 * 0 = 9 ∧ (-3 : ℤ) * (-3) + 0 * 0 = 9 ∧
        (0 : ℤ) * 0 + 3 * 3 = 9 ∧ (0 : ℤ) * 0 + (-3) * (-3) = 9) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Hqiv.Story
