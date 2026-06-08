import Hqiv.Story.S3RotationRigidity
import Hqiv.Story.S3ComplexResidualModel

/-!
# Orbit cancellation vs. pointwise cancellation: where the ℍ-lift stops

Lifting the analytically continued `riemannZeta` to the quaternions `ℍ` (or to any
faithful "residual" `ℂ → ℂ`) is a *re-encoding*, not a deformation: restricted to a
complex slice it is `riemannZeta` again, with the same zeros at the same real parts.
What the lift buys, geometrically, is the functional-equation symmetry `s ↔ 1-s`,
which in the 45° picture is the **orbit / reflection cancellation**.

This module makes the decisive distinction explicit:

* `orbit_free_sum_cancels` — the 45° free coordinates of a reflection pair
  `{σ, 1-σ}` **always** sum to zero. This is the geometric image of the functional
  equation, and it holds for *every* `σ`.
* `orbit_cancels_off_line` — therefore orbit cancellation is satisfied by pairs
  **off** the critical line (`σ ≠ 1/2`); it cannot, by itself, force `Re = 1/2`.
* `pointwise_free_zero_iff_on_line` — the strong condition is *pointwise* vanishing
  of a single free coordinate, which holds **iff** `σ = 1/2`.

So the gap between what the geometry/ℍ-lift gives for free (orbit cancellation =
functional-equation symmetry, zeros paired about `1/2`) and what RH asserts
(pointwise: every nontrivial zero *on* `1/2`) is exactly:

`AllNontrivialZerosOnLine ↔ RiemannHypothesis`  (`allNontrivialZerosOnLine_iff_RiemannHypothesis`).

The equivalence is real and proved; it shows the construction faithfully encodes
RH. But an equivalence (and the symmetry it encodes) is **not** a proof that all
zeros lie on the line: a hypothetical off-line zero `β` comes with its mirror
`1-β`, and that symmetric pair cancels on its orbit just like everything else.
Closing RH means upgrading orbit cancellation to pointwise cancellation at the
actual zeta zeros — and that upgrade is RH itself.
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
