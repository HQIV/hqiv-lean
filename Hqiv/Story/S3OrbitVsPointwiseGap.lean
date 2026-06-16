import Hqiv.Story.S3RotationRigidity
import Hqiv.Story.S3ComplexResidualModel

/-!
# Orbit cancellation vs. pointwise cancellation: where the ℍ-lift stops

Lifting the analytically continued `riemannZeta` to the quaternions `ℍ` (or to any
faithful "residual" `ℂ → ℂ`) is a *re-encoding*, not a deformation: restricted to a
complex slice it is `riemannZeta` again, with the same zeros at the same real parts.
What the lift buys, geometrically, is the functional-equation symmetry `s ↔ 1-s`,
which in the 45° picture is the **orbit / reflection cancellation**.

This module records the **σ-orbit** half of the projection story:

* `orbit_free_sum_cancels` — the 45° free coordinates of a reflection pair
  `{σ, 1-σ}` **always** sum to zero (functional-equation image).
* `orbit_cancels_off_line` — this cancellation also holds for pairs **off** the line;
  orbit cancellation alone does not exclude off-line points.
* `pointwise_free_zero_iff_on_line` — pointwise vanishing of a *single* free coordinate
  holds **iff** `σ = 1/2`.

**Scope note.** The equator readout factors through `Re s` and is blind to imaginary
height; see `S3SigmaReadoutScope`.  The full ζ-zero orbit under FE + Schwarz reflection
is the quadruplet `{s, 1-s, conj s, conj (1-s)}`, collapsing to a pair on the line;
see `S3ZeroQuadrupletOrbit`.

The RH packaging equivalence remains:

`AllNontrivialZerosOnLine ↔ RiemannHypothesis` (`allNontrivialZerosOnLine_iff_RiemannHypothesis`).

That equivalence faithfully encodes Mathlib's RH predicate; closing it is RH-hard.
-/

namespace Hqiv.Story

noncomputable section

/-- The functional-equation reflection about the critical line `σ ↦ 1-σ`. -/
def reflectAboutHalf (σ : ℝ) : ℝ := 1 - σ

theorem reflectAboutHalf_involutive (σ : ℝ) :
    reflectAboutHalf (reflectAboutHalf σ) = σ := by
  unfold reflectAboutHalf; ring

/--
**Orbit cancellation (functional-equation image).** The 45° free coordinates of a
reflection pair `{σ, 1-σ}` always sum to zero — for *every* `σ`.
-/
theorem orbit_free_sum_cancels (σ : ℝ) :
    rot45Free (functionalPair σ) +
      rot45Free (functionalPair (reflectAboutHalf σ)) = 0 := by
  unfold reflectAboutHalf
  rw [rot45Free_functionalPair, rot45Free_functionalPair]
  ring

/--
**Orbit cancellation does not force the critical line.** There is a reflection
pair off the line (`σ = 0 ≠ 1/2`) whose free coordinates still cancel. Hence the
orbit/reflection mechanism alone cannot single out `Re = 1/2`.
-/
theorem orbit_cancels_off_line :
    ∃ σ : ℝ, σ ≠ (1 / 2 : ℝ) ∧
      rot45Free (functionalPair σ) +
        rot45Free (functionalPair (reflectAboutHalf σ)) = 0 := by
  refine ⟨0, by norm_num, ?_⟩
  exact orbit_free_sum_cancels 0

/--
**Pointwise cancellation is the strong condition.** A *single* 45° free coordinate
vanishes iff its point is exactly on the line. (Restatement of
`rot45Free_functionalPair_eq_zero_iff`.)
-/
theorem pointwise_free_zero_iff_on_line (σ : ℝ) :
    rot45Free (functionalPair σ) = 0 ↔ σ = (1 / 2 : ℝ) :=
  rot45Free_functionalPair_eq_zero_iff σ

/--
The remaining obligation in zeta terms: *every* nontrivial zeta zero is
**pointwise** on the line (not merely paired about it). This is literally RH.
-/
def AllNontrivialZerosOnLine : Prop :=
  ∀ s : ℂ, IsNontrivialZetaZero s → s.re = (1 / 2 : ℝ)

/--
**The gap is exactly RH.** The pointwise on-line obligation is equivalent to
Mathlib's `RiemannHypothesis`. Combined with `orbit_cancels_off_line`, this is the
precise statement that the ℍ-lift / 45° geometry delivers the functional-equation
symmetry but *not* the critical-line localization: the localization is RH.
-/
theorem allNontrivialZerosOnLine_iff_RiemannHypothesis :
    AllNontrivialZerosOnLine ↔ RiemannHypothesis := by
  constructor
  · intro h s hz hNotTrivial hNotOne
    exact h s ⟨hz, hNotTrivial, hNotOne⟩
  · intro hRH s hzz
    exact hRH s hzz.1 hzz.2.1 hzz.2.2

end

end Hqiv.Story
