import Hqiv.Algebra.CliffordCl06SixIdeal
import Hqiv.Algebra.CliffordSixImaginaryScaffold
import Hqiv.Algebra.OctonionSpinorCarrier
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Standard real **8×8** spinor model for abstract `Cl(0,6)`

Naive octonion **left** multiplication on `e₁,…,e₆` does **not** satisfy the mixed Clifford relations
(`Hqiv.Algebra.OctonionLeftMulCliffordObstruction`).  Here we use the classical **alphabetic**
`2×2` Kronecker construction (Toppan–Verbeek, arXiv:0903.0940, Eqs. (2)–(4)) to build six explicit
`8×8` real matrices `γ₀,…,γ₅` with `γₖ² = -I₈` and `γₖ γₗ + γₗ γₖ = 0` for `k ≠ l`.

For `Q(v) = -∑ₖ vₖ²` (`quadFormCl06Six`), any `M(v) = ∑ₖ vₖ γₖ` obeys `M(v)² = Q(v) · I₈`, hence
`CliffordAlgebra.lift` yields

`ρ_mat : CliffordCl06Six →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`,

and `algEquivMatrix'.symm` composes to

`ρ : CliffordCl06Six →ₐ[ℝ] Module.End ℝ OctonionSpinorCarrier`.

This is **not** the octonion left-mult lift; it is a concrete faithful `8`-dimensional real module for
evaluating abstract ideals in `End(ℝ⁸)`.
-/

namespace Hqiv.Algebra

open scoped BigOperators
open Finset Matrix CliffordAlgebra Module QuadraticMap

/-- The four `2×2` blocks `I, X, Z, A` from the alphabetic presentation. -/
def spinorIx : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
def spinorX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def spinorZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def spinorA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Low / mid / high `Fin 2` digits of `i : Fin 8` (`8 = 2×2×2`, row-major). -/
def fin8Lo (i : Fin 8) : Fin 2 :=
  ⟨i.val % 2, Nat.mod_lt _ (by decide : 0 < 2)⟩

def fin8Mid (i : Fin 8) : Fin 2 :=
  ⟨(i.val / 2) % 2, Nat.mod_lt _ (by decide : 0 < 2)⟩

def fin8Hi (i : Fin 8) : Fin 2 :=
  ⟨i.val / 4, by omega⟩

/-- Triple Kronecker product `A ⊗ B ⊗ C` (digit order matched to `numpy.kron`). -/
noncomputable def spinorKron3 (A B C : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => A (fin8Lo i) (fin8Lo j) * B (fin8Mid i) (fin8Mid j) * C (fin8Hi i) (fin8Hi j)

/-- The six `γ` matrices, aligned with `cl06SixBasisVec 0,…,5`. -/
noncomputable def cl06SpinorGammaMat : Fin 6 → Matrix (Fin 8) (Fin 8) ℝ
  | ⟨0, _⟩ => spinorKron3 spinorA spinorIx spinorX
  | ⟨1, _⟩ => spinorKron3 spinorA spinorIx spinorZ
  | ⟨2, _⟩ => spinorKron3 spinorA spinorA spinorA
  | ⟨3, _⟩ => spinorKron3 spinorIx spinorX spinorA
  | ⟨4, _⟩ => spinorKron3 spinorIx spinorZ spinorA
  | ⟨5, _⟩ => spinorKron3 spinorX spinorA spinorIx

theorem quadFormCl06Six_apply (v : Fin 6 → ℝ) :
    quadFormCl06Six v = -∑ i : Fin 6, v i * v i := by
  classical
  simp [quadFormCl06Six, weightedSumSquares_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, neg_mul,
    Finset.sum_neg_distrib]

/-- `∑ₖ vₖ γₖ` as a linear map into matrices (Mathlib `Fintype.linearCombination`). -/
noncomputable def cl06SpinorMatLin : (Fin 6 → ℝ) →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  Fintype.linearCombination ℝ cl06SpinorGammaMat

theorem cl06SixBasisVec_eq_piSingle (j : Fin 6) : cl06SixBasisVec j = Pi.single j (1 : ℝ) := by
  funext k
  by_cases h : k = j
  · subst h
    simp [cl06SixBasisVec, Pi.single_eq_same]
  · simp [cl06SixBasisVec, h]

set_option maxHeartbeats 800000 in
theorem cl06SpinorMatLin_mul_self (v : Fin 6 → ℝ) :
    cl06SpinorMatLin v * cl06SpinorMatLin v = (quadFormCl06Six v) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  ext i j
  simp_rw [Matrix.mul_apply, cl06SpinorMatLin, Fintype.linearCombination_apply, quadFormCl06Six_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> (
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, cl06SpinorGammaMat, spinorKron3,
      fin8Lo, fin8Mid, fin8Hi, spinorIx, spinorX, spinorZ, spinorA];
    ring_nf)

/-- Matrix algebra lift of `Cl(0,6)` for the standard spinor `γ` matrices. -/
noncomputable def cl06StandardSpinorMatLift :
    CliffordCl06Six →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  CliffordAlgebra.lift quadFormCl06Six
    ⟨cl06SpinorMatLin, fun w => by
      rw [Algebra.algebraMap_eq_smul_one, cl06SpinorMatLin_mul_self]⟩

/-- `Matrix (Fin 8) (Fin 8) ℝ ≃ₐ[ℝ] End(ℝ⁸)` for the standard basis. -/
noncomputable abbrev cl06MatAlgEquiv : Matrix (Fin 8) (Fin 8) ℝ ≃ₐ[ℝ] Module.End ℝ OctonionSpinorCarrier :=
  (algEquivMatrix' (R := ℝ) (n := Fin 8)).symm

/-- Concrete spinor representation on `OctonionSpinorCarrier = Fin 8 → ℝ`. -/
noncomputable def cl06StandardSpinorRho : CliffordCl06Six →ₐ[ℝ] Module.End ℝ OctonionSpinorCarrier :=
  cl06MatAlgEquiv.toAlgHom.comp cl06StandardSpinorMatLift

@[simp]
theorem cl06StandardSpinorMatLift_ι (j : Fin 6) :
    cl06StandardSpinorMatLift (CliffordAlgebra.ι quadFormCl06Six (cl06SixBasisVec j)) =
      cl06SpinorGammaMat j := by
  rw [cl06StandardSpinorMatLift, CliffordAlgebra.lift_ι_apply]
  simp [cl06SpinorMatLin, cl06SixBasisVec_eq_piSingle, Fintype.linearCombination_apply_single,
    one_smul]

@[simp]
theorem cl06StandardSpinorRho_ι (j : Fin 6) :
    cl06StandardSpinorRho (CliffordAlgebra.ι quadFormCl06Six (cl06SixBasisVec j)) =
      cl06MatAlgEquiv (cl06SpinorGammaMat j) := by
  simp [cl06StandardSpinorRho, cl06StandardSpinorMatLift_ι]

/-- Image of the full algebra under `ρ` (same as range of the underlying `ℝ`-linear map). -/
noncomputable def cl06StandardSpinorRhoRange : Submodule ℝ (Module.End ℝ OctonionSpinorCarrier) :=
  LinearMap.range cl06StandardSpinorRho.toLinearMap

theorem cl06StandardSpinorRhoRange_finrank_le :
    Module.finrank ℝ cl06StandardSpinorRhoRange ≤ 64 := by
  have h := Submodule.finrank_le cl06StandardSpinorRhoRange
  have hEnd : Module.finrank ℝ (Module.End ℝ OctonionSpinorCarrier) = 64 := by
    simp [OctonionSpinorCarrier, Module.finrank_linearMap, Fintype.card_fin]
  rw [hEnd] at h
  exact h.trans (Nat.le_refl _)

end Hqiv.Algebra
