import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Hqiv.OctonionLeftMultiplication
open Matrix Finset
set_option maxHeartbeats 0 in
set_option simp.maxSteps 200000 in
example : Hqiv.octonionLeftMul_1 * Hqiv.octonionLeftMul_2 + Hqiv.octonionLeftMul_2 * Hqiv.octonionLeftMul_1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [add_apply, mul_apply, Fin.sum_univ_succ, Hqiv.octonionLeftMul_1, Hqiv.octonionLeftMul_2, zero_apply,
      add_mul, mul_add, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_eq_add_neg]
