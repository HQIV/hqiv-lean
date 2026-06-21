import Mathlib.NumberTheory.LSeries.Convergence

import Hqiv.Geometry.HarmonicMulModCubeTriangulation

/-!
# Mul-mod local coefficients — BSD-facing fit scaffold

This module tests the smallest honest fit between the new structured mul-mod
tooling and the existing `LSeries` path.  It does **not** claim BSD, modularity,
or an elliptic-curve interface.

The coefficient keeps local residue data from the structured cascade multiplier:

`a_{n+1} = (harmonicStructuredCascadeMultiplier (n+1) mod (n+1)) / (n+1)`.

Because the residue is normalized by the shell size, the stream is uniformly
bounded by `1`, so it fits Mathlib's absolute-convergence scaffold at abscissa
`≤ 1`.  This is the first gate a BSD-facing coefficient channel must pass before
any later weight-2 modularity or elliptic-curve `L(E,s)` interface is considered.

**Related:** `MulModBSDLSeriesScaffold`, `MulModBSDCompletedLFunctionalScaffold`,
`MulModBSDEulerFactor`, `Hqiv.Story.S3MulModBSDCoefficientBridge`.
-/

namespace Hqiv.Algebra

open Complex LSeries
open Hqiv.Geometry

noncomputable section

/-- Real normalized local residue of the structured mul-mod cascade on shell `n`. -/
noncomputable def mulModBSDLocalResidueCoeffReal (n : ℕ) (hn : 0 < n) : ℝ :=
  ((harmonicStructuredCascadeMultiplier n hn % n : ℕ) : ℝ) / (n : ℝ)

/-- Complex coefficient obtained from the real normalized local residue. -/
noncomputable def mulModBSDLocalResidueCoeff (n : ℕ) (hn : 0 < n) : ℂ :=
  (mulModBSDLocalResidueCoeffReal n hn : ℂ)

/--
`LSeries`-indexed coefficient stream: index `0` is unused; shell `n+1` carries
the normalized structured mul-mod residue.
-/
noncomputable def mulModBSDLocalCoeff : ℕ → ℂ
  | 0 => 0
  | n + 1 => mulModBSDLocalResidueCoeff (n + 1) (Nat.succ_pos n)

@[simp]
theorem mulModBSDLocalCoeff_zero : mulModBSDLocalCoeff 0 = 0 :=
  rfl

theorem mulModBSDLocalCoeff_succ (n : ℕ) :
    mulModBSDLocalCoeff (n + 1) =
      (((harmonicStructuredCascadeMultiplier (n + 1) (Nat.succ_pos n) % (n + 1) : ℕ) : ℝ) /
        (n + 1 : ℝ) : ℂ) :=
  by simp [mulModBSDLocalCoeff, mulModBSDLocalResidueCoeff, mulModBSDLocalResidueCoeffReal]

/-- The local-residue coefficient is uniformly bounded by `1`. -/
theorem mulModBSDLocalResidueCoeffReal_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ mulModBSDLocalResidueCoeffReal n hn := by
  dsimp [mulModBSDLocalResidueCoeffReal]
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem mulModBSDLocalResidueCoeffReal_le_one (n : ℕ) (hn : 0 < n) :
    mulModBSDLocalResidueCoeffReal n hn ≤ 1 := by
  dsimp [mulModBSDLocalResidueCoeffReal]
  have hden : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmod :
      harmonicStructuredCascadeMultiplier n hn % n ≤ n :=
    Nat.le_of_lt (Nat.mod_lt _ hn)
  have hmod_real :
      ((harmonicStructuredCascadeMultiplier n hn % n : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hmod
  exact (div_le_one hden).mpr hmod_real

theorem norm_mulModBSDLocalCoeff_le_one {n : ℕ} (hn : n ≠ 0) :
    ‖mulModBSDLocalCoeff n‖ ≤ 1 := by
  rcases n with _ | k
  · exact False.elim (hn rfl)
  · dsimp [mulModBSDLocalCoeff, mulModBSDLocalResidueCoeff]
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (mulModBSDLocalResidueCoeffReal_nonneg (k + 1) (Nat.succ_pos k))]
    exact mulModBSDLocalResidueCoeffReal_le_one (k + 1) (Nat.succ_pos k)

/-- The bounded mul-mod local coefficient stream has absolute-convergence abscissa at most `1`. -/
theorem abscissaOfAbsConv_mulModBSDLocalCoeff_le_one :
    abscissaOfAbsConv mulModBSDLocalCoeff ≤ (1 : ℝ) :=
  LSeries.abscissaOfAbsConv_le_of_le_const
    ⟨1, fun _ hn => norm_mulModBSDLocalCoeff_le_one hn⟩

/--
Fit bundle: the structured mul-mod residue stream is already in the right shape
for the existing `LSeries` convergence machinery.
-/
structure MulModBSDCoefficientFit where
  coeff : ℕ → ℂ
  zero : coeff 0 = 0
  structured :
    ∀ n : ℕ,
      coeff (n + 1) =
        (((harmonicStructuredCascadeMultiplier (n + 1) (Nat.succ_pos n) % (n + 1) : ℕ) : ℝ) /
          (n + 1 : ℝ) : ℂ)
  bounded : ∀ {n : ℕ}, n ≠ 0 → ‖coeff n‖ ≤ 1
  abscissa_le_one : abscissaOfAbsConv coeff ≤ (1 : ℝ)

/-- The current mul-mod tooling passes the coefficient/L-series fit gate. -/
noncomputable def mulModBSDCoefficientFit : MulModBSDCoefficientFit where
  coeff := mulModBSDLocalCoeff
  zero := mulModBSDLocalCoeff_zero
  structured := mulModBSDLocalCoeff_succ
  bounded := fun hn => norm_mulModBSDLocalCoeff_le_one hn
  abscissa_le_one := abscissaOfAbsConv_mulModBSDLocalCoeff_le_one

end

end Hqiv.Algebra
