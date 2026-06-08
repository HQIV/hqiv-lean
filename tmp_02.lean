import Hqiv.Physics.StrongColorSu3LieCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open scoped BigOperators
open Complex Finset

noncomputable section
set_option maxHeartbeats 8000000

lemma colorLieChartBracket_0_2 :
    Hqiv.Physics.lieBracketMat₃ (Hqiv.Physics.colorHalfGellMannFull (0 : Fin 8))
        (Hqiv.Physics.colorHalfGellMannFull (2 : Fin 8)) =
      Complex.I • ∑ c : Fin 8, (Hqiv.Physics.colorSu3fStructure (0 : Fin 8) (2 : Fin 8) c : ℂ) •
        Hqiv.Physics.colorHalfGellMannFull c := by
  unfold Hqiv.Physics.lieBracketMat₃
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_eight, Matrix.of_apply,
      Hqiv.Physics.colorHalfGellMannFull, Hqiv.Physics.colorGellMannLambdaFull,
      Hqiv.Physics.colorGellMannLambda1, Hqiv.Physics.colorGellMannLambda2,
      Hqiv.Physics.colorGellMannLambda3, Hqiv.Physics.colorGellMannLambda4,
      Hqiv.Physics.colorGellMannLambda5, Hqiv.Physics.colorGellMannLambda6,
      Hqiv.Physics.colorGellMannLambda7, Hqiv.Physics.colorGellMannLambda8]
    try simp [Hqiv.Physics.colorSu3fStructure, Hqiv.Physics.colorSu3PermSign, Hqiv.Physics.min3,
      Hqiv.Physics.mid3, Hqiv.Physics.max3, Hqiv.Physics.colorSu3fSorted]
    try simp_rw [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    try simp [pow_two, Complex.I_mul_I, mul_assoc, mul_comm, mul_left_comm]
    try ring_nf
    try ring
  }

end

example : (-1 / 2 : ℂ) = Complex.I ^ 2 * (1 / 2 : ℂ) := by
  rw [Complex.I_sq]
  ring
