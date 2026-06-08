import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Hqiv.OctonionLeftMultiplication

open scoped BigOperators
open Finset Hqiv

def octonionMatQ (M : Matrix (Fin 8) (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (M i j : ℚ)

def octonionMulVec (M : Matrix (Fin 8) (Fin 8) ℚ) (v : Fin 8 → ℚ) : Fin 8 → ℚ :=
  fun i => ∑ j : Fin 8, M i j * v j

def euclideanNormSq (v : Fin 8 → ℚ) : ℚ :=
  ∑ i : Fin 8, v i * v i

theorem octonionLeftMul_1_preserves_euclidean (v : Fin 8 → ℚ) :
    euclideanNormSq (octonionMulVec (octonionMatQ octonionLeftMul_1) v) = euclideanNormSq v := by
  simp_rw [euclideanNormSq, octonionMulVec, octonionMatQ, octonionLeftMul_1]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  ring
