import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

import Hqiv.Generators
import Hqiv.GeneratorsFromAxioms
import Hqiv.GeneratorsLieClosureData
import Hqiv.LieBracketCell.Row0Summary
import Hqiv.LieBracketCell.Row1Summary
import Hqiv.LieBracketCell.Row2Summary
import Hqiv.LieBracketCell.Row3Summary
import Hqiv.LieBracketCell.Row4Summary
import Hqiv.LieBracketCell.Row5Summary
import Hqiv.LieBracketCell.Row6Summary
import Hqiv.LieBracketCell.Row7Summary
import Hqiv.LieBracketCell.Row8Summary
import Hqiv.LieBracketCell.Row9Summary
import Hqiv.LieBracketCell.Row10Summary
import Hqiv.LieBracketCell.Row11Summary
import Hqiv.LieBracketCell.Row12Summary
import Hqiv.LieBracketCell.Row13Summary
import Hqiv.LieBracketCell.Row14Summary
import Hqiv.LieBracketCell.Row15Summary
import Hqiv.LieBracketCell.Row16Summary
import Hqiv.LieBracketCell.Row17Summary
import Hqiv.LieBracketCell.Row18Summary
import Hqiv.LieBracketCell.Row19Summary
import Hqiv.LieBracketCell.Row20Summary
import Hqiv.LieBracketCell.Row21Summary
import Hqiv.LieBracketCell.Row22Summary
import Hqiv.LieBracketCell.Row23Summary
import Hqiv.LieBracketCell.Row24Summary
import Hqiv.LieBracketCell.Row25Summary
import Hqiv.LieBracketCell.Row26Summary
import Hqiv.LieBracketCell.Row27Summary
import Hqiv.So8CoordMatrix

-- `lieBracket_in_span` is split across `Hqiv/LieBracketCell/`: 784 modules `R{i}C{j}` (each 8×8
-- entry split + `norm_num`) and 28 `Row{i}Summary` files, avoiding monolithic `i×j×a×b` case splits.
set_option maxHeartbeats 200000000

open Matrix BigOperators

namespace Hqiv

/-!
# Lie bracket closure — [so8Generator i, so8Generator j] in span of the 28

We prove that each Lie bracket lies in the ℝ-span of the 28 generators, so the
generators form a Lie subalgebra (so(8)). Coefficients from
`scripts/print_lie_bracket_closure.py` (see `Hqiv.GeneratorsLieClosureData`).
-/

/-- **Lie bracket antisymmetry:** [A, B] = -[B, A]. -/
theorem lieBracket_antisymm (A B : Matrix (Fin 8) (Fin 8) ℝ) :
    lieBracket A B = -lieBracket B A := by
  unfold lieBracket
  ext i j
  simp only [neg_apply, mul_apply, sub_apply, neg_sub]

/-- **Every Lie bracket [so8Generator i, so8Generator j]** lies in the ℝ-span of the 28 generators.
Coefficients are `lieBracketCoeff i j` (defined in GeneratorsLieClosureData). -/
theorem lieBracket_in_span (i j : Fin 28) :
    lieBracket (so8Generator i) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff i j k • so8Generator k := by
  fin_cases i
  · exact lieBracket_in_span_row0 j
  · exact lieBracket_in_span_row1 j
  · exact lieBracket_in_span_row2 j
  · exact lieBracket_in_span_row3 j
  · exact lieBracket_in_span_row4 j
  · exact lieBracket_in_span_row5 j
  · exact lieBracket_in_span_row6 j
  · exact lieBracket_in_span_row7 j
  · exact lieBracket_in_span_row8 j
  · exact lieBracket_in_span_row9 j
  · exact lieBracket_in_span_row10 j
  · exact lieBracket_in_span_row11 j
  · exact lieBracket_in_span_row12 j
  · exact lieBracket_in_span_row13 j
  · exact lieBracket_in_span_row14 j
  · exact lieBracket_in_span_row15 j
  · exact lieBracket_in_span_row16 j
  · exact lieBracket_in_span_row17 j
  · exact lieBracket_in_span_row18 j
  · exact lieBracket_in_span_row19 j
  · exact lieBracket_in_span_row20 j
  · exact lieBracket_in_span_row21 j
  · exact lieBracket_in_span_row22 j
  · exact lieBracket_in_span_row23 j
  · exact lieBracket_in_span_row24 j
  · exact lieBracket_in_span_row25 j
  · exact lieBracket_in_span_row26 j
  · exact lieBracket_in_span_row27 j

/-!
## Linear independence

The 28 generators are linearly independent (hence a basis for so(8)). We prove this
by showing that the 28×28 matrix of upper-triangle coordinates (`so8CoordMatrix`) has
nonzero determinant (script: `scripts/print_linear_independence.py` gives det = -1).
-/

/-- **det(so8CoordMatrix)² = 1** (columns orthonormal ⇒ Mᵀ M = 1 ⇒ det(Mᵀ M) = 1). -/
theorem so8CoordMatrix_det_sq_eq_one : so8CoordMatrix.det ^ 2 = 1 := by
  calc so8CoordMatrix.det ^ 2 = so8CoordMatrix.det * so8CoordMatrix.det := sq _
    _ = (so8CoordMatrixᵀ).det * so8CoordMatrix.det := by rw [det_transpose]
    _ = det (so8CoordMatrixᵀ * so8CoordMatrix) := by rw [det_mul]
    _ = det (1 : Matrix (Fin 28) (Fin 28) ℝ) := by rw [so8CoordMatrix_transpose_mul_self]
    _ = 1 := det_one

/-- **Coordinate matrix has nonzero determinant.** Follows from so8CoordMatrix_transpose_mul_self (det² = 1). -/
theorem so8CoordMatrix_det_ne_zero : so8CoordMatrix.det ≠ 0 := by
  intro h
  have h₂ : (1 : ℝ) = 0 := by
    calc
      (1 : ℝ) = so8CoordMatrix.det ^ 2 := so8CoordMatrix_det_sq_eq_one.symm
      _ = 0 := by rw [h]; norm_num
  norm_num at h₂

/-- The coordinate vector of a linear combination ∑ c_k • so8Generator k is so8CoordMatrix.mulVec c. -/
theorem coordVec_linearCombination (c : Fin 28 → ℝ) (p : Fin 28) :
    coordVec (∑ k : Fin 28, c k • so8Generator k) p = (so8CoordMatrix.mulVec c) p := by
  simp_rw [coordVec, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mulVec, dotProduct,
    so8CoordMatrix_eq_coord]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/-- so8CoordMatrix is invertible (Mᵀ * M = 1 ⇒ M has a left inverse ⇒ det invertible). -/
instance so8CoordMatrix_invertible : Invertible so8CoordMatrix := by
  have : Invertible so8CoordMatrix.det :=
    Matrix.detInvertibleOfLeftInverse so8CoordMatrix so8CoordMatrixᵀ so8CoordMatrix_transpose_mul_self
  exact Matrix.invertibleOfDetInvertible so8CoordMatrix

/-- If so8CoordMatrix.mulVec c = 0 then c = 0 (matrix is invertible, so kernel trivial). -/
theorem so8CoordMatrix_mulVec_eq_zero_imp_eq_zero (c : Fin 28 → ℝ)
    (h : so8CoordMatrix.mulVec c = 0) : c = 0 := by
  have key := inv_mulVec_eq_vec (A := so8CoordMatrix) (u := (0 : Fin 28 → ℝ)) (v := c) h.symm
  rw [mulVec_zero] at key
  exact key.symm

/-- **The 28 so8 generators are linearly independent over ℝ.** The coordinate map sends
∑ c_k • so8Generator k to so8CoordMatrix.mulVec c; det ≠ 0 implies the matrix is invertible,
so the map is injective, hence the generators are independent. -/
theorem so8_generators_linear_independent :
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h i
  have hdiff : ∑ k : Fin 28, (f k - g k) • so8Generator k = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have hcoord : so8CoordMatrix.mulVec (fun k => f k - g k) = 0 := by
    ext p
    rw [← coordVec_linearCombination (fun k => f k - g k) p, hdiff]
    simp only [coordVec, Matrix.zero_apply, Pi.zero_apply]
  have hzero := so8CoordMatrix_mulVec_eq_zero_imp_eq_zero (fun k => f k - g k) hcoord
  exact sub_eq_zero.mp (congr_fun hzero i)

/-- **Generators from first assumptions:** The 28 so(8) generators are antisymmetric,
closed under Lie bracket (with coefficients `lieBracketCoeff`), and linearly independent.
So they form a basis for a 28-dimensional Lie subalgebra (so(8)). -/
theorem generators_from_octonion_closure_theorem :
    (∀ k : Fin 28, so8Generator k + (so8Generator k)ᵀ = 0) ∧
    (∀ i j : Fin 28, ∃ f : Fin 28 → ℝ,
      lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k) ∧
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) := by
  refine ⟨so8Generator_antisymm, ?_, so8_generators_linear_independent⟩
  intro i j
  exact ⟨lieBracketCoeff i j, lieBracket_in_span i j⟩

end Hqiv
