import Hqiv.Story.S3DivisorPairingSelectsSquares
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The Fourier-twiddle residual is the Möbius function (squarefree, not prime)

You are right that the 45° rotations are **Fourier twiddle factors**
`ω_N = e^{2πi/N}`, and that the twiddle structure produces an arithmetic
*residual*. This module names that residual exactly.

The sum of the *primitive* `N`-th roots of unity is the Ramanujan sum at `1`,

`c_N(1) = ∑_{gcd(a,N)=1} e^{2πi a / N} = μ(N)`,

a classical identity (Ramanujan / Möbius). So the twiddle residual is `μ(N)`.
But `μ(N) ≠ 0` ⇔ `N` is **squarefree** — it does **not** isolate primes:

* `prime_two_residual`, `prime_three_residual` — primes leave a residual
  (`μ p = -1`), as expected;
* `composite_six_residual` — the **composite, squarefree** `6 = 2·3` *also*
  leaves a residual (`μ 6 = 1 ≠ 0`), contradicting "residuals only for
  non-primes that are prime";
* `composite_four_no_residual` — the composite `4 = 2²` leaves **no** residual
  (`μ 4 = 0`), contradicting "residuals for everything that's not a prime".

So the twiddle/Möbius residual detects **squarefree-ness**, with primes one
sub-case among many squarefree numbers (`6, 10, 15, 21, …` all leave residuals).
The full geometric twiddle sum `∑_{k<N} ω^k = 0` cancels for *every* `N > 1`; it
is only the *primitive* (coprime) part that carries `μ`, and `μ` sees squarefree
factorization, not primality.

This is the correct, sharp version of the intuition — and it shows the same
boundary as before: the twiddle gives multiplicative/squarefree arithmetic, not
the pointwise localization of `riemannZeta` zeros onto `Re = 1/2`.
-/

namespace Hqiv.Story

open ArithmeticFunction ArithmeticFunction.Moebius

/-- A prime leaves a twiddle residual: `μ 2 = -1 ≠ 0`. -/
theorem prime_two_residual : μ 2 ≠ 0 := by
  rw [moebius_apply_prime (by norm_num)]; norm_num

/-- A prime leaves a twiddle residual: `μ 3 = -1 ≠ 0`. -/
theorem prime_three_residual : μ 3 ≠ 0 := by
  rw [moebius_apply_prime (by norm_num)]; norm_num

/-- The **composite, squarefree** `6 = 2·3` *also* leaves a residual:
`μ 6 = μ 2 · μ 3 = 1 ≠ 0`. -/
theorem composite_six_residual : μ 6 ≠ 0 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  have hcop : Nat.Coprime 2 3 := by norm_num
  rw [h6, isMultiplicative_moebius.map_mul_of_coprime hcop,
    moebius_apply_prime (by norm_num), moebius_apply_prime (by norm_num)]
  norm_num

/-- The composite `4 = 2²` leaves **no** residual (`μ 4 = 0`). -/
theorem composite_four_no_residual : μ 4 = 0 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, moebius_apply_prime_pow (by norm_num) (by norm_num)]
  norm_num

/--
**Detection theorem.** The twiddle residual `μ(N)` detects squarefree-ness, not
primality:

* `6` is composite yet leaves a residual;
* `4` is composite and leaves none.

Hence "residuals for everything that's not a prime" is false in both directions.
-/
theorem twiddle_residual_detects_squarefree_not_primality :
    (μ 6 ≠ 0 ∧ ¬ Nat.Prime 6) ∧ (μ 4 = 0 ∧ ¬ Nat.Prime 4) :=
  ⟨⟨composite_six_residual, by norm_num⟩,
   ⟨composite_four_no_residual, by norm_num⟩⟩

end Hqiv.Story
