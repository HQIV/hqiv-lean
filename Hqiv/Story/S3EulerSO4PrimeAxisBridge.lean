import Hqiv.Story.S3DiscretePrimeAxisSampling
import Hqiv.Story.PlasticTwistedEulerCharacter

/-!
# Euler prime / SO(4) cancellation slots

This module is the corrected bridge layer between the S³/SO(4) cancellation
geometry and the Euler-prime-product story.

The key distinction is pointwise: the SO(4) head/tail pair supplies a first
cancellation-pair candidate.  It does **not** assert that every real height is a
zeta zero.  Any zeta-zero conclusion must enter through a matched analytic
identification at a specific slot.
-/

namespace Hqiv.Story

noncomputable section

/-- Phase/height extracted from an S³ sample. -/
def survivorPhase (P : ScaledS3Sample) : ℝ :=
  imagSum P.coords

/-- The critical-line point with imaginary coordinate `t`. -/
def criticalLinePointAtHeight (t : ℝ) : ℂ :=
  ⟨(1 / 2 : ℝ), t⟩

@[simp] theorem criticalLinePointAtHeight_re (t : ℝ) :
    (criticalLinePointAtHeight t).re = (1 / 2 : ℝ) :=
  rfl

@[simp] theorem criticalLinePointAtHeight_im (t : ℝ) :
    (criticalLinePointAtHeight t).im = t :=
  rfl

/--
SO(4) first cancellation pair: the selected 45° head/tail orbit cancels as a
pair.  This is geometry, not a zeta-zero existence statement.
-/
def SO4FirstCancellationPair (p : QuaternionCoords) : Prop :=
  criticalProj p + criticalProj (headTailReflect p) = 0

/-- The head/tail SO(4) first cancellation pair is the proved S³ cancellation. -/
theorem so4FirstCancellationPair_headTail (p : QuaternionCoords) :
    SO4FirstCancellationPair p :=
  headTail_orbit_pair_cancels p

/-- Sample-level SO(4) first cancellation pair. -/
def S3SampleSO4FirstCancellationPair (P : ScaledS3Sample) : Prop :=
  SO4FirstCancellationPair P.coords

theorem s3SampleSO4FirstCancellationPair (P : ScaledS3Sample) :
    S3SampleSO4FirstCancellationPair P :=
  so4FirstCancellationPair_headTail P.coords

/--
Pointwise analytic/coordinate identification for the corrected bridge.

This intentionally lives here rather than importing the later zero-equivalence
modules, so the Euler/SO(4) candidate layer stays low in the import graph.
-/
def ZetaEqualsEulerSO4ResidualAt (s : ℂ) (P : ScaledS3Sample) : Prop :=
  riemannZeta s = (criticalProj P.coords : ℂ)

/--
Prime-axis Euler/SO(4) slot.

It records the actual structured object: a prime-axis sample, its SO(4)
head/tail cancellation pair, a pointwise zeta/S³ residual identification on the
critical-line candidate, and convergence of the twisted Euler partial products
to the zeta value at that same point.
-/
def PrimeAxisEulerSO4Slot (χ : PlasticTwiddleCharacter) (P : ScaledS3Sample) : Prop :=
  PrimeAxisAtScale P ∧
    S3SampleSO4FirstCancellationPair P ∧
      let s := criticalLinePointAtHeight (survivorPhase P)
      ZetaEqualsEulerSO4ResidualAt s P ∧
        Filter.Tendsto
          (fun N : ℕ => twistedEulerProductPartial χ s (primesUpTo N))
          Filter.atTop
          (nhds (riemannZeta s))

/--
Surviving samples are realized as prime-axis Euler/SO(4) slots.  This replaces
the old all-height phase coverage interface.
-/
def EulerPrimeSO4FirstCancellationRealizesStrip (χ : PlasticTwiddleCharacter) : Prop :=
  ∀ P : ScaledS3Sample, criticalProj P.coords ≠ 0 → PrimeAxisEulerSO4Slot χ P

/--
A matched Euler/SO(4) candidate for a complex point `s`.

The equality `s = criticalLinePointAtHeight ...` is the pointwise lock.  It is
where a specific candidate is matched to a specific complex point; no statement
about arbitrary heights is made.
-/
def MatchedEulerSO4CancellationAt
    (χ : PlasticTwiddleCharacter) (s : ℂ) (P : ScaledS3Sample) : Prop :=
  PrimeAxisEulerSO4Slot χ P ∧ s = criticalLinePointAtHeight (survivorPhase P)

/-- A matched Euler/SO(4) candidate lies on the critical line. -/
theorem re_eq_half_of_matchedEulerSO4CancellationAt
    {χ : PlasticTwiddleCharacter} {s : ℂ} {P : ScaledS3Sample}
    (h : MatchedEulerSO4CancellationAt χ s P) :
    s.re = (1 / 2 : ℝ) := by
  rw [h.2]
  simp [criticalLinePointAtHeight]

end

end Hqiv.Story
