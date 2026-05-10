import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Hqiv.Algebra.PlasticZeta3

/-!
# Plastic recurrence asymptotic scaffold

This module introduces canonical numerator/denominator-style recurrence
sequences for the plastic recurrence and proves basic positivity/monotonicity
facts used later in ratio-limit arguments.
-/

namespace Hqiv.Algebra

/-- Canonical positive recurrence seed (numerator track). -/
def plasticP : ℕ → ℚ := plasticSeq 1 1 2

/-- Canonical positive recurrence seed (denominator track). -/
def plasticQ : ℕ → ℚ := plasticSeq 1 2 3

theorem plasticP_rec (n : ℕ) :
    plasticP (n + 3) = plasticP (n + 1) + plasticP n := by
  simpa [plasticP] using plasticSeq_rec (u0 := (1 : ℚ)) (u1 := 1) (u2 := 2) n

theorem plasticQ_rec (n : ℕ) :
    plasticQ (n + 3) = plasticQ (n + 1) + plasticQ n := by
  simpa [plasticQ] using plasticSeq_rec (u0 := (1 : ℚ)) (u1 := 2) (u2 := 3) n

@[simp] theorem plasticP_zero : plasticP 0 = 1 := by rfl
@[simp] theorem plasticP_one : plasticP 1 = 1 := by rfl
@[simp] theorem plasticP_two : plasticP 2 = 2 := by rfl

@[simp] theorem plasticQ_zero : plasticQ 0 = 1 := by rfl
@[simp] theorem plasticQ_one : plasticQ 1 = 2 := by rfl
@[simp] theorem plasticQ_two : plasticQ 2 = 3 := by rfl

lemma plasticP_nonneg : ∀ n, 0 ≤ plasticP n
  | 0 => by norm_num [plasticP]
  | 1 => by norm_num [plasticP]
  | 2 => by norm_num [plasticP]
  | n + 3 =>
      by
        rw [plasticP_rec]
        exact add_nonneg (plasticP_nonneg (n + 1)) (plasticP_nonneg n)

lemma plasticQ_nonneg : ∀ n, 0 ≤ plasticQ n
  | 0 => by norm_num [plasticQ]
  | 1 => by norm_num [plasticQ]
  | 2 => by norm_num [plasticQ]
  | n + 3 =>
      by
        rw [plasticQ_rec]
        exact add_nonneg (plasticQ_nonneg (n + 1)) (plasticQ_nonneg n)

lemma plasticP_pos : ∀ n, 0 < plasticP n
  | 0 => by norm_num [plasticP]
  | 1 => by norm_num [plasticP]
  | 2 => by norm_num [plasticP]
  | n + 3 =>
      by
        rw [plasticP_rec]
        exact add_pos (plasticP_pos (n + 1)) (plasticP_pos n)

lemma plasticQ_pos : ∀ n, 0 < plasticQ n
  | 0 => by norm_num [plasticQ]
  | 1 => by norm_num [plasticQ]
  | 2 => by norm_num [plasticQ]
  | n + 3 =>
      by
        rw [plasticQ_rec]
        exact add_pos (plasticQ_pos (n + 1)) (plasticQ_pos n)

/-- Numerator track stays below denominator track for the canonical seeds. -/
lemma plasticP_le_plasticQ : ∀ n, plasticP n ≤ plasticQ n
  | 0 => by norm_num [plasticP, plasticQ]
  | 1 => by norm_num [plasticP, plasticQ]
  | 2 => by norm_num [plasticP, plasticQ]
  | n + 3 =>
      by
        rw [plasticP_rec, plasticQ_rec]
        exact add_le_add (plasticP_le_plasticQ (n + 1)) (plasticP_le_plasticQ n)

/-- Rational ratio track used in later limit statements. -/
noncomputable def plasticRatio (n : ℕ) : ℚ := plasticP n / plasticQ n

theorem plasticRatio_wellDefined (n : ℕ) : plasticQ n ≠ 0 := by
  exact ne_of_gt (plasticQ_pos n)

end Hqiv.Algebra

