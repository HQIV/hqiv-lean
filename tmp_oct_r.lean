import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Hqiv.OctonionLeftMultiplication

open scoped BigOperators
open Finset Hqiv

def octonionMulVec (M : Matrix (Fin 8) (Fin 8) ℝ) (v : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun i => ∑ j : Fin 8, M i j * v j

def euclideanNormSq (v : Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 8, v i * v i

theorem octonionLeftMul_1_preserves_euclidean (v : Fin 8 → ℝ) :
    euclideanNormSq (octonionMulVec octonionLeftMul_1 v) = euclideanNormSq v := by
  simp_rw [euclideanNormSq, octonionMulVec, octonionLeftMul_1]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  ring
