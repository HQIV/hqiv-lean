import Hqiv.Algebra.CliffordCl06SixSpinorGammaMonomialLinearIndependent
import Hqiv.Algebra.CliffordCl06SixStandardSpinorMatLiftSurjective
import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Geometry.OctonionicLightCone
import Mathlib.Data.Matrix.Basic

/-!
# Mass-operator anchors from the standard spinor ρ / γ model

Numeric ranking in `scripts/spinor_mass_operator_reality_probe.py` singled out the
**bivector commutator-square** matrix on `ℝ⁸` as a strong ρ-native probe.  This file
gives that operator and a **manifold-derived** linear combination

`α · sym(γ₀γ₁) + (φ(m)/6) · Δ`

using the proved curvature imprint `α = 3/5` (`alpha_eq_3_5`), the auxiliary ladder `φ(m)`
(`phi_of_shell`), the unit phase-lift matrix `phaseLiftDeltaMatrix`, and the standard
`spinorGammaMonomialMat` / ρ model.

The optional `64 × 64` operator is **left multiplication** by `manifoldMassOp8 m` in row-major
monomial coordinates (same convention as `spinorMonomialCoordMatrix`).

Python probe: `scripts/spinor_mass_operator_reality_probe.py`.
-/

namespace Hqiv.Physics

open Finset Matrix
open Hqiv.Algebra

namespace MassFromSpinorRho

/-- `M * Mᵀ` is symmetric for a real square matrix `M`. -/
theorem transpose_mul_self_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (c : Matrix n n ℝ) : (c * c.transpose).transpose = c * c.transpose := by
  simp [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Single-generator γ monomial: bitmask `2^i` for `i : Fin 6` (matches Python `1 << k`). -/
noncomputable def spinorSingleGammaMonomialMat (i : Fin 6) : Matrix (Fin 8) (Fin 8) ℝ :=
  spinorGammaMonomialMat
    ⟨2 ^ (i : ℕ), by
      fin_cases i <;> native_decide⟩

/--
Σ_{i < j} [γᵢ,γⱼ] · [γᵢ,γⱼ]ᵀ  over the standard Kronecker γ matrices (ρ-images of the six `ι(eₖ)`).
Same construction as `rho_bivector_commutator_sq_sum_8x8` in `spinor_mass_operator_reality_probe.py`.
-/
noncomputable def spinorBivectorCommutatorSqSumMat : Matrix (Fin 8) (Fin 8) ℝ :=
  ∑ i : Fin 6,
    ∑ j : Fin 6,
      if _h : i.val < j.val then
        let Gi := spinorSingleGammaMonomialMat i
        let Gj := spinorSingleGammaMonomialMat j
        let c := Gi * Gj - Gj * Gi
        c * c.transpose
      else
        0

theorem spinorBivectorCommutatorSqSumMat_transpose :
    spinorBivectorCommutatorSqSumMat.transpose = spinorBivectorCommutatorSqSumMat := by
  classical
  unfold spinorBivectorCommutatorSqSumMat
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with _h
  · dsimp
    rw [transpose_mul_self_transpose]
  · rw [Matrix.transpose_zero]

/-- Symmetrized γ₀γ₁ bivector (ρ-image of a simple imprint channel). -/
noncomputable def manifoldCurvatureSymBivector01 : Matrix (Fin 8) (Fin 8) ℝ :=
  (1 / 2 : ℝ) •
    (spinorSingleGammaMonomialMat 0 * spinorSingleGammaMonomialMat 1 +
      spinorSingleGammaMonomialMat 1 * spinorSingleGammaMonomialMat 0)

/--
**Manifold mass operator on `ℝ⁸`:** `α · sym(γ₀γ₁) + (φ(m)/6) · Δ`.

Here `α` is `Hqiv.alpha` (proved `3/5` via `alpha_eq_3_5`), `φ(m) = phi_of_shell m`, and
`(φ(m)/6)` is `phaseLiftCoeff m` (`PhaseLiftDelta`).
-/
noncomputable def manifoldMassOp8 (m : ℕ) : Matrix (Fin 8) (Fin 8) ℝ :=
  Hqiv.alpha • manifoldCurvatureSymBivector01 + (phaseLiftCoeff m) • phaseLiftDeltaMatrix

/--
Left-multiplication by `manifoldMassOp8 m` in row-major monomial coordinates (`Fin 64` indices).
Entry `(i,j)` is `((manifoldMassOp8 m) * spinorGammaMonomialMat j)_{row col}` with
`(row,col) = spinorRowMajorEquiv.symm i`.
-/
noncomputable def manifoldMassOp64LeftMult (m : ℕ) : Matrix (Fin 64) (Fin 64) ℝ :=
  fun i j =>
    (manifoldMassOp8 m * spinorGammaMonomialMat j) (spinorRowMajorEquiv.symm i).1
      (spinorRowMajorEquiv.symm i).2

end MassFromSpinorRho

end Hqiv.Physics
