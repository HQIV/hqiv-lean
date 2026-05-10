import Mathlib.Tactic

import Hqiv.Algebra.PlasticRecurrence

/-!
# Plastic recurrence dynamics

Second milestone for the plastic-number program:
define the cubic recurrence explicitly and prove its basic forced relation
`u_{n+3} = u_{n+1} + u_n`, the recurrence encoded by `x^3 - x - 1`.
-/

namespace Hqiv.Algebra

/-- Scalar recurrence attached to the plastic polynomial `x^3 - x - 1` from
initial values `(u₀,u₁,u₂)`. -/
def plasticSeq (u0 u1 u2 : ℚ) : ℕ → ℚ
  | 0 => u0
  | 1 => u1
  | 2 => u2
  | n + 3 => plasticSeq u0 u1 u2 (n + 1) + plasticSeq u0 u1 u2 n

/-- Definitional recurrence law. -/
theorem plasticSeq_rec (u0 u1 u2 : ℚ) (n : ℕ) :
    plasticSeq u0 u1 u2 (n + 3) =
      plasticSeq u0 u1 u2 (n + 1) + plasticSeq u0 u1 u2 n := by
  rfl

/-- The first three values are the chosen initial data. -/
@[simp] theorem plasticSeq_zero (u0 u1 u2 : ℚ) : plasticSeq u0 u1 u2 0 = u0 := rfl
@[simp] theorem plasticSeq_one  (u0 u1 u2 : ℚ) : plasticSeq u0 u1 u2 1 = u1 := rfl
@[simp] theorem plasticSeq_two  (u0 u1 u2 : ℚ) : plasticSeq u0 u1 u2 2 = u2 := rfl

/-- Operator form: the recurrence means `X^3 - X - 1` annihilates shifted values. -/
theorem plasticSeq_annihilator (u0 u1 u2 : ℚ) (n : ℕ) :
    plasticSeq u0 u1 u2 (n + 3) - plasticSeq u0 u1 u2 (n + 1) - plasticSeq u0 u1 u2 n = 0 := by
  rw [plasticSeq_rec]
  ring

end Hqiv.Algebra

