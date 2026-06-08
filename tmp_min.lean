import Hqiv.Physics.StrongColorSu3LieCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open scoped BigOperators
open Complex Matrix Finset
open Hqiv.Algebra Hqiv.Physics

noncomputable section
set_option maxHeartbeats 8000000

lemma colorLieChartBracket_0_1 :
    lieBracketMat₃ (colorHalfGellMannFull (0 : Fin 8)) (colorHalfGellMannFull (1 : Fin 8)) =
      I • ∑ c : Fin 8, (colorSu3fStructure (0 : Fin 8) (1 : Fin 8) c : ℂ) • colorHalfGellMannFull c := by
  unfold lieBracketMat₃
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_eight, Matrix.of_apply,
      colorHalfGellMannFull, colorGellMannLambdaFull, colorGellMannLambda1, colorGellMannLambda2,
      colorGellMannLambda3, colorGellMannLambda4, colorGellMannLambda5, colorGellMannLambda6,
      colorGellMannLambda7, colorGellMannLambda8]
    try simp [colorSu3fStructure, colorSu3PermSign, min3, mid3, max3, colorSu3fSorted]
    try simp_rw [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    try ring_nf
    try ring
  }

end
