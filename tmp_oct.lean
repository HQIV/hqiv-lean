import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Hqiv.OctonionLeftMultiplication

open Hqiv
open scoped BigOperators

theorem octonionLeftMul_1_orthogonal :
    octonionLeftMul_1 * octonionLeftMul_1.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, octonionLeftMul_1, Finset.sum_fin_eq_sum_range,
      Finset.sum_range_succ]
  <;> norm_num
