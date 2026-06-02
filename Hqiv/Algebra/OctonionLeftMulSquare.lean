import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Hqiv.OctonionLeftMultiplication

/-!
# `L(e_i)^2 = -1` for octonion left-multiplication matrices

For each imaginary unit `e_{i+1}` (`i : Fin 7`), the representing matrix
`octonionLeftMul_N i` squares to **negative** the identity.

These identities are the per-generator input for a future **Clifford** map
`ι : (Fin 6 → ℝ) → Mat(8,ℝ)` along `e₁,…,e₆`: they match the quadratic relation
`ι(v)² = algebraMap ℝ (Q v)` when `Q` is negative-definite on each basis vector
(`Q(e_k) = -1`).

**Not proved here (and not automatic for a linear extension):** the full Clifford
anticommutation / lift of `CliffordAlgebra` into `Matrix (Fin 8) (Fin 8) ℝ` for
**arbitrary** linear combinations `∑ c_i L_i` — that requires the same relations
between distinct `L_i`, which is a separate calculation from the Fano table.
-/

namespace Hqiv

open Matrix Finset

private theorem octonionLeftMul_sq_aux (M : Matrix (Fin 8) (Fin 8) ℝ)
    (h : ∀ i j : Fin 8, (M * M) i j = (-1 : Matrix (Fin 8) (Fin 8) ℝ) i j) :
    M * M = (-1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  ext i j
  exact h i j

theorem octonionLeftMul_1_mul_self : octonionLeftMul_1 * octonionLeftMul_1 = (-1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  octonionLeftMul_sq_aux _ fun i j => by
    fin_cases i <;> fin_cases j <;> rw [mul_apply, sum_fin_eq_sum_range] <;> simp [sum_range_succ, octonionLeftMul_1]

theorem octonionLeftMul_2_mul_self : octonionLeftMul_2 * octonionLeftMul_2 = (-1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  octonionLeftMul_sq_aux _ fun i j => by
    fin_cases i <;> fin_cases j <;> rw [mul_apply, sum_fin_eq_sum_range] <;> simp [sum_range_succ, octonionLeftMul_2]

theorem octonionLeftMul_3_mul_self : octonionLeftMul_3 * octonionLeftMul_3 = (-1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  octonionLeftMul_sq_aux _ fun i j => by
    fin_cases i <;> fin_cases j <;> rw [mul_apply, sum_fin_eq_sum_range] <;> simp [sum_range_succ, octonionLeftMul_3]

theorem octonionLeftMul_4_mul_self : octonionLeftMul_4 * octonionLeftMul_4 = (-1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  octonionLeftMul_sq_aux _ fun i j => by
    fin_cases i <;> fin_cases j <;> rw [mul_apply, sum_fin_eq_sum_range] <;> simp [sum_range_succ, octonionLeftMul_4]

theorem octonionLeftMul_5_mul_self : octonionLeftMul_5 * octonionLeftMul_5 = (-1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  octonionLeftMul_sq_aux _ fun i j => by
    fin_cases i <;> fin_cases j <;> rw [mul_apply, sum_fin_eq_sum_range] <;> simp [sum_range_succ, octonionLeftMul_5]

theorem octonionLeftMul_6_mul_self : octonionLeftMul_6 * octonionLeftMul_6 = (-1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  octonionLeftMul_sq_aux _ fun i j => by
    fin_cases i <;> fin_cases j <;> rw [mul_apply, sum_fin_eq_sum_range] <;> simp [sum_range_succ, octonionLeftMul_6]

theorem octonionLeftMul_7_mul_self : octonionLeftMul_7 * octonionLeftMul_7 = (-1 : Matrix (Fin 8) (Fin 8) ℝ) :=
  octonionLeftMul_sq_aux _ fun i j => by
    fin_cases i <;> fin_cases j <;> rw [mul_apply, sum_fin_eq_sum_range] <;> simp [sum_range_succ, octonionLeftMul_7]

theorem octonionLeftMul_N_mul_self (N : Fin 7) :
    octonionLeftMul_N N * octonionLeftMul_N N = (-1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  fin_cases N
  · exact octonionLeftMul_1_mul_self
  · exact octonionLeftMul_2_mul_self
  · exact octonionLeftMul_3_mul_self
  · exact octonionLeftMul_4_mul_self
  · exact octonionLeftMul_5_mul_self
  · exact octonionLeftMul_6_mul_self
  · exact octonionLeftMul_7_mul_self

end Hqiv
