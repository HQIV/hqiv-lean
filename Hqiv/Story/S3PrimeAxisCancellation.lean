import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# S³ prime-axis cancellation algebra

This module isolates the sorry-free algebra behind the S³ / quaternion-axis
story used by the RH bridge notes.

The result proved here is deliberately geometric and local:

* head/tail reflection always cancels an orbit-pair contribution;
* pointwise cancellation is exactly the balanced-imaginary condition;
* a selected single imaginary axis survives pointwise cancellation;
* for arbitrary real points (no lattice/rationality assumption), a non-single-axis
  point can cancel pointwise only by being trivial in the imaginary coordinates
  or by satisfying the explicit balance relation.

No analytic zeta-zero implication is asserted here.
-/

namespace Hqiv.Story

/-- Quaternion coordinates `[real, i, j, k]`, represented as four real coordinates. -/
abbrev QuaternionCoords := Fin 4 → ℝ

/-- The affine S³ shell equation in quaternion coordinates. -/
def OnS3 (p : QuaternionCoords) : Prop :=
  p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 = 1

/-- Sum of the imaginary coordinates selected by the critical projection. -/
def imagSum (p : QuaternionCoords) : ℝ :=
  p 1 + p 2 + p 3

/-- The 45°-normalized critical projection used by the story geometry. -/
noncomputable def criticalProj (p : QuaternionCoords) : ℝ :=
  imagSum p / Real.sqrt 2

/-- Head/tail reflection: preserve the real coordinate and reverse the imaginary tail. -/
def headTailReflect (p : QuaternionCoords) : QuaternionCoords :=
  fun i => if i = 0 then p 0 else -p i

@[simp] theorem headTailReflect_zero (p : QuaternionCoords) :
    headTailReflect p 0 = p 0 := by
  simp [headTailReflect]

@[simp] theorem headTailReflect_one (p : QuaternionCoords) :
    headTailReflect p 1 = -p 1 := by
  have h : (1 : Fin 4) ≠ 0 := by decide
  simp [headTailReflect, h]

@[simp] theorem headTailReflect_two (p : QuaternionCoords) :
    headTailReflect p 2 = -p 2 := by
  have h : (2 : Fin 4) ≠ 0 := by decide
  simp [headTailReflect, h]

@[simp] theorem headTailReflect_three (p : QuaternionCoords) :
    headTailReflect p 3 = -p 3 := by
  have h : (3 : Fin 4) ≠ 0 := by decide
  simp [headTailReflect, h]

/-- Reflection preserves the S³ shell equation. -/
theorem headTailReflect_preserves_s3 (p : QuaternionCoords) :
    OnS3 p → OnS3 (headTailReflect p) := by
  intro hp
  dsimp [OnS3] at hp ⊢
  simp
  simpa [sq] using hp

/-- The imaginary sum is odd under head/tail reflection. -/
theorem imagSum_headTailReflect (p : QuaternionCoords) :
    imagSum (headTailReflect p) = -imagSum p := by
  simp [imagSum]
  ring

/-- The critical projection is odd under head/tail reflection. -/
theorem criticalProj_headTailReflect (p : QuaternionCoords) :
    criticalProj (headTailReflect p) = -criticalProj p := by
  unfold criticalProj
  rw [imagSum_headTailReflect]
  ring

/-- Head/tail reflected orbit pairs cancel for every real point, lattice or not. -/
theorem headTail_orbit_pair_cancels (p : QuaternionCoords) :
    criticalProj p + criticalProj (headTailReflect p) = 0 := by
  rw [criticalProj_headTailReflect]
  ring

/-- Pointwise cancellation condition: the selected imaginary coordinates balance. -/
def BalancedImag (p : QuaternionCoords) : Prop :=
  imagSum p = 0

/-- Pointwise cancellation is exactly balanced imaginary content. -/
theorem criticalProj_eq_zero_iff_balanced (p : QuaternionCoords) :
    criticalProj p = 0 ↔ BalancedImag p := by
  unfold criticalProj BalancedImag
  constructor
  · intro h
    exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
  · intro h
    simp [h]

/-- No imaginary component is active. -/
def IsTrivialImag (p : QuaternionCoords) : Prop :=
  p 1 = 0 ∧ p 2 = 0 ∧ p 3 = 0

/-- Exactly one of the `i,j,k` axes is active. -/
def IsSingleAxis (p : QuaternionCoords) : Prop :=
  (p 1 ≠ 0 ∧ p 2 = 0 ∧ p 3 = 0) ∨
  (p 2 ≠ 0 ∧ p 1 = 0 ∧ p 3 = 0) ∨
  (p 3 ≠ 0 ∧ p 1 = 0 ∧ p 2 = 0)

/-- At least two of the `i,j,k` axes are active. -/
def IsTwoOrMoreAxis (p : QuaternionCoords) : Prop :=
  (p 1 ≠ 0 ∧ p 2 ≠ 0) ∨
  (p 1 ≠ 0 ∧ p 3 ≠ 0) ∨
  (p 2 ≠ 0 ∧ p 3 ≠ 0)

/-- Every real quaternion point has trivial, single-axis, or multi-axis imaginary support. -/
theorem imag_support_trichotomy (p : QuaternionCoords) :
    IsTrivialImag p ∨ IsSingleAxis p ∨ IsTwoOrMoreAxis p := by
  by_cases h1 : p 1 = 0
  · by_cases h2 : p 2 = 0
    · by_cases h3 : p 3 = 0
      · exact Or.inl ⟨h1, h2, h3⟩
      · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨h3, h1, h2⟩)))
    · by_cases h3 : p 3 = 0
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨h2, h1, h3⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, h3⟩)))
  · by_cases h2 : p 2 = 0
    · by_cases h3 : p 3 = 0
      · exact Or.inr (Or.inl (Or.inl ⟨h1, h2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h3⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))

/-- A selected single-axis contribution cannot be balanced away pointwise. -/
theorem not_balanced_of_singleAxis (p : QuaternionCoords) :
    IsSingleAxis p → ¬ BalancedImag p := by
  intro hAxis hBal
  rcases hAxis with ⟨h1, h2, h3⟩ | ⟨h2, h1, h3⟩ | ⟨h3, h1, h2⟩
  · exact h1 (by simpa [BalancedImag, imagSum, h2, h3] using hBal)
  · exact h2 (by simpa [BalancedImag, imagSum, h1, h3] using hBal)
  · exact h3 (by simpa [BalancedImag, imagSum, h1, h2] using hBal)

/-- Single-axis points survive the selected critical projection. -/
theorem criticalProj_ne_zero_of_singleAxis (p : QuaternionCoords) :
    IsSingleAxis p → criticalProj p ≠ 0 := by
  intro hAxis hzero
  exact not_balanced_of_singleAxis p hAxis ((criticalProj_eq_zero_iff_balanced p).1 hzero)

/--
Continuous/no-lattice restriction:
if a non-single-axis point cancels pointwise, then it is either trivial in the
imaginary coordinates or it is genuinely multi-axis and explicitly balanced.
-/
theorem non_single_axis_pointwise_cancel_restricted (p : QuaternionCoords)
    (hNotSingle : ¬ IsSingleAxis p) (hCancel : criticalProj p = 0) :
    IsTrivialImag p ∨ (IsTwoOrMoreAxis p ∧ BalancedImag p) := by
  have hBal : BalancedImag p := (criticalProj_eq_zero_iff_balanced p).1 hCancel
  rcases imag_support_trichotomy p with hTrivial | hSingle | hMulti
  · exact Or.inl hTrivial
  · exact False.elim (hNotSingle hSingle)
  · exact Or.inr ⟨hMulti, hBal⟩

/--
Unbalanced nontrivial imaginary content cannot fully cancel pointwise.  This is the
precise continuous analogue of the lattice restriction: reflection cancels the pair,
but a single representative vanishes only on the balanced hyperplane.
-/
theorem nontrivial_unbalanced_not_pointwise_cancel (p : QuaternionCoords)
    (_hNontrivial : ¬ IsTrivialImag p) (hUnbalanced : ¬ BalancedImag p) :
    criticalProj p ≠ 0 := by
  intro hCancel
  exact hUnbalanced ((criticalProj_eq_zero_iff_balanced p).1 hCancel)

end Hqiv.Story
