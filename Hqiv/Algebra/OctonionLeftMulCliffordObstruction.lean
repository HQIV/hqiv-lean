import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Hqiv.Algebra.OctonionLeftMulSquare
import Hqiv.OctonionLeftMultiplication

/-!
# Octonion **left** matrices are **not** a `Cl(0,6)` matrix model on `e₁,…,e₆`

The natural HQIV matrices `L(e_k) = octonionLeftMul_*` satisfy **`L(e_k)² = -I₈`**
(`Hqiv.Algebra.OctonionLeftMulSquare`), but they **do not** satisfy the Clifford
anticommutation law
\[
  L(e_a)L(e_b) + L(e_b)L(e_a) = 0 \quad (a \neq b)
\]
that would be forced by an orthogonal **negative-definite** quadratic form on
the span of `{e_a,e_b}` inside a **linear** lift `f : (Fin 6 → ℝ) → Mat₈(ℝ)` with
`f(δ_j)=L(e_{j+1})`.

Consequently there is **no** such linear map satisfying the universal
`CliffordAlgebra.lift` hypothesis
`(f v) * (f v) = algebraMap ℝ (Matrix _ _) (Q v)` for **all** `v` when `Q` is the
standard `Cl(0,6)` form on `Fin 6 → ℝ` from `CliffordSixImaginaryScaffold` and `f`
is the unique linear extension of the six left-mult matrices.

This is a **positive** algebraic fact: it pins the exact gate for the Furey/HQIV
program — the matrix model must come from a **different** representation (e.g.
pin/spinor packaging, complexification, or a non-octonionic choice of generators),
not from naive octonion **left** multiplication on six imaginary units alone.
-/

namespace Hqiv

open Matrix Finset

/-- Mixed product `L(e₁)L(e₂) + L(e₂)L(e₁)` has a nonzero entry at `(3,3)`. -/
theorem octonionLeftMul_1_mul_2_add_mul_swap_entry_33 :
    (octonionLeftMul_1 * octonionLeftMul_2 + octonionLeftMul_2 * octonionLeftMul_1) 3 3 = 2 := by
  rw [Matrix.add_apply, mul_apply, mul_apply]
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  simp [Finset.sum_range_succ, octonionLeftMul_1, octonionLeftMul_2]
  norm_num

theorem octonionLeftMul_1_mul_2_add_mul_swap_ne_zero :
    octonionLeftMul_1 * octonionLeftMul_2 + octonionLeftMul_2 * octonionLeftMul_1 ≠ 0 := by
  intro h
  have h33 := congr_arg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M 3 3) h
  simp only [Matrix.zero_apply] at h33
  rw [octonionLeftMul_1_mul_2_add_mul_swap_entry_33] at h33
  norm_num at h33

/-- Along `(3,3)`, `(L(e₁)+L(e₂))²` disagrees with scalar `-2` times identity. -/
theorem octonionLeftMul_add_sum_square_entry_33_ne :
    ((octonionLeftMul_1 + octonionLeftMul_2) * (octonionLeftMul_1 + octonionLeftMul_2)) 3 3 ≠
      (-(2 : ℝ)) * (1 : Matrix (Fin 8) (Fin 8) ℝ) 3 3 := by
  intro h
  have hmat :
      (octonionLeftMul_1 + octonionLeftMul_2) * (octonionLeftMul_1 + octonionLeftMul_2) =
        octonionLeftMul_1 * octonionLeftMul_1 + octonionLeftMul_1 * octonionLeftMul_2 +
          octonionLeftMul_2 * octonionLeftMul_1 + octonionLeftMul_2 * octonionLeftMul_2 := by
    rw [add_mul, mul_add, mul_add]
    simp [add_assoc]
  have h11 : (octonionLeftMul_1 * octonionLeftMul_1) 3 3 = -1 := by
    rw [octonionLeftMul_1_mul_self]
    simp [Matrix.neg_apply]
  have h22 : (octonionLeftMul_2 * octonionLeftMul_2) 3 3 = -1 := by
    rw [octonionLeftMul_2_mul_self]
    simp [Matrix.neg_apply]
  have h12 :
      (octonionLeftMul_1 * octonionLeftMul_2) 3 3 + (octonionLeftMul_2 * octonionLeftMul_1) 3 3 = 2 := by
    rw [← Matrix.add_apply]
    exact octonionLeftMul_1_mul_2_add_mul_swap_entry_33
  have hl :
      ((octonionLeftMul_1 + octonionLeftMul_2) * (octonionLeftMul_1 + octonionLeftMul_2)) 3 3 = 0 := by
    rw [hmat, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h11, h22]
    rw [add_assoc (-1 : ℝ)]
    rw [h12]
    ring
  have hr : (-(2 : ℝ)) * (1 : Matrix (Fin 8) (Fin 8) ℝ) 3 3 = -2 := by
    norm_num
  rw [hl, hr] at h
  norm_num at h

end Hqiv
