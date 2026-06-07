import Hqiv.Story.S3CenteredResidualModel

/-!
# 45° projection onto the critical-line equator

This module formalizes the algebraic statement:

Rotating the functional-equation pair `(σ, 1 - σ)` by 45° separates it into

* a fixed diagonal coordinate, and
* a free/equator coordinate proportional to `σ - 1/2`.

Hence the free-axis equator (`free = 0`) is exactly the critical line
`Re(s)=1/2`.
-/

namespace Hqiv.Story

noncomputable section

/-- The two real coordinates paired by the functional equation `σ ↔ 1-σ`. -/
def functionalPair (σ : ℝ) : ℝ × ℝ :=
  (σ, 1 - σ)

/-- The diagonal coordinate after a 45° rotation in the selected two-plane. -/
noncomputable def rot45Diag (p : ℝ × ℝ) : ℝ :=
  (p.1 + p.2) / Real.sqrt 2

/-- The free/equator coordinate after the same 45° rotation. -/
noncomputable def rot45Free (p : ℝ × ℝ) : ℝ :=
  (p.1 - p.2) / Real.sqrt 2

/-- On the functional-equation pair, the 45° diagonal coordinate is fixed. -/
theorem rot45Diag_functionalPair (σ : ℝ) :
    rot45Diag (functionalPair σ) = 1 / Real.sqrt 2 := by
  unfold rot45Diag functionalPair
  ring

/-- On the functional-equation pair, the free coordinate is proportional to `2σ-1`. -/
theorem rot45Free_functionalPair (σ : ℝ) :
    rot45Free (functionalPair σ) = (2 * σ - 1) / Real.sqrt 2 := by
  unfold rot45Free functionalPair
  ring

/-- The 45° free-axis equator is exactly the midpoint `σ=1/2`. -/
theorem rot45Free_functionalPair_eq_zero_iff (σ : ℝ) :
    rot45Free (functionalPair σ) = 0 ↔ σ = (1 / 2 : ℝ) := by
  rw [rot45Free_functionalPair]
  constructor
  · intro h
    have hnum : 2 * σ - 1 = 0 := by
      exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
    linarith
  · intro h
    subst h
    norm_num

/-- The rotated free coordinate is a scaled version of critical-line deviation. -/
theorem rot45Free_functionalPair_eq_scaled_deviation (σ : ℝ) :
    rot45Free (functionalPair σ) =
      (2 / Real.sqrt 2) * (σ - (1 / 2 : ℝ)) := by
  rw [rot45Free_functionalPair]
  ring

/-- Complex-point version: the 45° free equator is exactly `Re(s)=1/2`. -/
theorem rot45Free_re_pair_eq_zero_iff (s : ℂ) :
    rot45Free (functionalPair s.re) = 0 ↔ s.re = (1 / 2 : ℝ) :=
  rot45Free_functionalPair_eq_zero_iff s.re

/--
Compatibility with the centered residual model:
the 45° free coordinate vanishes exactly when `criticalLineDeviation s` vanishes.
-/
theorem rot45Free_re_pair_eq_zero_iff_deviation_zero (s : ℂ) :
    rot45Free (functionalPair s.re) = 0 ↔ criticalLineDeviation s = 0 := by
  exact (rot45Free_re_pair_eq_zero_iff s).trans
    (criticalLineDeviation_eq_zero_iff s).symm

end
end Hqiv.Story
