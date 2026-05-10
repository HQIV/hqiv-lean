import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.Convergence

import Hqiv.Algebra.IntegerLatticeShellCount8
import Hqiv.Algebra.ModularThetaBridgeScaffold

/-!
# Θ₈ / `r₈` as a Mathlib `LSeries` coefficient stream (theta bridge → analytic)

`ModularThetaBridgeScaffold` names the formal `q`-coefficient stream `thetaZ8FormalCoeff = r8`.
This module packages the **same** numbers as a complex arithmetic function `ℕ → ℂ` in Mathlib’s
`LSeries` indexing convention (`0 ↦ 0`, shell `m` at index `m + 1`) and proves a **concrete**
upper bound on the abscissa of absolute convergence using the crude shell bound
`r8_le_two_mul_add_one_pow_eight` from `IntegerLatticeShellCount8`.

**Not here:** identification with a classical `ModularForm`’s `q`-expansion or Hecke invariance
(see `ThetaZ8ModularFormScaffold` for the precise `qExpansion` ↔ `r8` target bundle).

**Related:** `Hqiv.Algebra.ThetaCompletedLFunctionalScaffold` — **proved** completed Λ symmetry for
the trivial Dirichlet (`mod 1`) branch, and a **hypothesis** shape for weight-`4` completed L
(`s ↦ 4-s`); `r₈` itself is not a character L-series in Mathlib (see module doc there).
-/

namespace Hqiv.Algebra

open Complex LSeries
open scoped Topology

noncomputable section

/-- `LSeries` coefficients: index `0` unused; index `m + 1` carries shell count `r8 m`
(definitionally `thetaZ8FormalCoeff m`). -/
noncomputable def thetaZ8LSeriesCoeff : ℕ → ℂ
  | 0 => 0
  | n + 1 => (r8 n : ℂ)

@[simp]
theorem thetaZ8LSeriesCoeff_zero : thetaZ8LSeriesCoeff 0 = 0 :=
  rfl

theorem thetaZ8LSeriesCoeff_succ (n : ℕ) :
    thetaZ8LSeriesCoeff (n + 1) = (thetaZ8FormalCoeff n : ℂ) := by
  simp [thetaZ8LSeriesCoeff, thetaZ8FormalCoeff_eq_r8]

theorem norm_thetaZ8LSeriesCoeff_le (n : ℕ) (hn : n ≠ 0) :
    ‖thetaZ8LSeriesCoeff n‖ ≤ (256 : ℝ) * (n : ℝ) ^ (8 : ℝ) := by
  rcases n with _ | k
  · exact False.elim (hn rfl)
  · dsimp [thetaZ8LSeriesCoeff]
    rw [show ((r8 k : ℕ) : ℂ) = ((r8 k : ℝ) : ℂ) by simp]
    rw [Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    suffices (r8 k : ℝ) ≤ 256 * (k + 1 : ℝ) ^ 8 by simpa using this
    have hk := r8_le_two_mul_add_one_pow_eight k
    have hmono : (2 * k + 1 : ℕ) ^ 8 ≤ (2 * (k + 1)) ^ 8 :=
      Nat.pow_le_pow_left (by omega) 8
    have hk' : (r8 k : ℝ) ≤ ((2 * k + 1) ^ 8 : ℝ) := by exact_mod_cast hk
    have hmono' : ((2 * k + 1) ^ 8 : ℝ) ≤ ((2 * (k + 1)) ^ 8 : ℝ) := by exact_mod_cast hmono
    have h256' : ((2 * (k + 1)) ^ 8 : ℝ) = (256 : ℝ) * (k + 1 : ℝ) ^ 8 := by
      ring_nf
    calc
      (r8 k : ℝ) ≤ ((2 * k + 1) ^ 8 : ℝ) := hk'
      _ ≤ ((2 * (k + 1)) ^ 8 : ℝ) := hmono'
      _ = (256 : ℝ) * (k + 1 : ℝ) ^ 8 := h256'

/-- Abscissa of absolute convergence is at most `9` (`O(n⁸)` coefficients). -/
theorem abscissaOfAbsConv_thetaZ8LSeriesCoeff_le_nine :
    abscissaOfAbsConv thetaZ8LSeriesCoeff ≤ (9 : ℝ) := by
  have h :=
    LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
      (f := thetaZ8LSeriesCoeff) (x := (8 : ℝ))
      ⟨256, fun n hn => norm_thetaZ8LSeriesCoeff_le n hn⟩
  rw [show (9 : ℝ) = (8 : ℝ) + 1 by norm_num]
  exact h

end

end Hqiv.Algebra
