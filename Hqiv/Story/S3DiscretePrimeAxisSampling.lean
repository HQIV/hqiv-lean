import Hqiv.Story.S3PrimeAxisCancellation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Discrete S³ prime-axis sampling

This module lifts the verified S³ cancellation algebra to a discrete sampling
interface.  The arithmetic/null-lattice content is kept explicit in
`S3DiscreteNullLatticeLaw`: outside the prime-axis-at-scale channel, the selected
imaginary coordinates are balanced.

From that single law and the continuous S³ lemmas, we prove:

* non-prime scales cancel;
* non-single-axis samples cancel;
* nonzero pointwise projection is equivalent to being prime-axis at scale;
* unbalanced samples are exactly the prime-axis-at-scale samples.

No analytic zeta-zero statement is introduced here.
-/

namespace Hqiv.Story

/-- A sampled point on the S³ shell, tagged by an integer scale. -/
structure ScaledS3Sample where
  scale : ℕ
  coords : QuaternionCoords
  onS3 : OnS3 coords

/-- Prime-axis-at-scale: the scale is prime and the sample has one active imaginary axis. -/
def PrimeAxisAtScale (P : ScaledS3Sample) : Prop :=
  Nat.Prime P.scale ∧ IsSingleAxis P.coords

/--
Discrete null-lattice selection law for the S³ story layer.

Interpretation: every sampled point that is not a prime-scale single-axis
representative lies on the balanced imaginary hyperplane selected by the
45°/head-tail construction.
-/
structure S3DiscreteNullLatticeLaw where
  balanced_of_not_prime_axis :
    ∀ P : ScaledS3Sample, ¬ PrimeAxisAtScale P → BalancedImag P.coords

/-- Reflected orbit pairs cancel for every sampled point. -/
theorem sampled_headTail_orbit_pair_cancels (P : ScaledS3Sample) :
    criticalProj P.coords + criticalProj (headTailReflect P.coords) = 0 :=
  headTail_orbit_pair_cancels P.coords

/-- A sample outside the prime-axis-at-scale channel cancels pointwise. -/
theorem cancels_of_not_prime_axis_at_scale
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample)
    (hNotPrimeAxis : ¬ PrimeAxisAtScale P) :
    criticalProj P.coords = 0 :=
  (criticalProj_eq_zero_iff_balanced P.coords).2
    (L.balanced_of_not_prime_axis P hNotPrimeAxis)

/-- Any sample at a non-prime scale cancels pointwise. -/
theorem non_prime_scale_cancels
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample)
    (hNotPrime : ¬ Nat.Prime P.scale) :
    criticalProj P.coords = 0 := by
  apply cancels_of_not_prime_axis_at_scale L P
  intro hPrimeAxis
  exact hNotPrime hPrimeAxis.1

/-- Any non-single-axis sample cancels pointwise under the discrete selection law. -/
theorem non_single_axis_sample_cancels
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample)
    (hNotSingle : ¬ IsSingleAxis P.coords) :
    criticalProj P.coords = 0 := by
  apply cancels_of_not_prime_axis_at_scale L P
  intro hPrimeAxis
  exact hNotSingle hPrimeAxis.2

/-- A prime-scale single-axis sample survives pointwise cancellation. -/
theorem prime_axis_at_scale_survives (P : ScaledS3Sample)
    (hPrimeAxis : PrimeAxisAtScale P) :
    criticalProj P.coords ≠ 0 :=
  criticalProj_ne_zero_of_singleAxis P.coords hPrimeAxis.2

/--
Discrete survival theorem:
under the null-lattice selection law, pointwise nonzero projection is equivalent
to prime-axis-at-scale.
-/
theorem discrete_prime_axis_survival_iff
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample) :
    criticalProj P.coords ≠ 0 ↔ PrimeAxisAtScale P := by
  constructor
  · intro hNonzero
    by_contra hNotPrimeAxis
    exact hNonzero (cancels_of_not_prime_axis_at_scale L P hNotPrimeAxis)
  · intro hPrimeAxis
    exact prime_axis_at_scale_survives P hPrimeAxis

/--
Equivalent balanced-hyperplane form:
under the null-lattice selection law, a sample is unbalanced exactly when it is
prime-axis-at-scale.
-/
theorem unbalanced_iff_prime_axis_at_scale
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample) :
    ¬ BalancedImag P.coords ↔ PrimeAxisAtScale P := by
  constructor
  · intro hUnbalanced
    by_contra hNotPrimeAxis
    exact hUnbalanced (L.balanced_of_not_prime_axis P hNotPrimeAxis)
  · intro hPrimeAxis
    exact not_balanced_of_singleAxis P.coords hPrimeAxis.2

/--
Contrapositive packaging for the analytic bridge:
if a sampled contribution is not prime-axis-at-scale, the selected representative
is in the zero channel.
-/
theorem zero_channel_of_not_prime_axis_at_scale
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample) :
    ¬ PrimeAxisAtScale P → criticalProj P.coords = 0 :=
  cancels_of_not_prime_axis_at_scale L P

end Hqiv.Story
