import Hqiv.Story.S3FortyFiveProjection

/-!
# S³ pole/zero channel

This module formalizes the "pole is a zero" phrasing in a safe algebraic form.

In Lean fields, poles are not values of a total function.  We therefore define a
pole channel as a denominator/residual vanishing condition.  For the S³ residual
detector, that denominator is `criticalProj P.coords`.

Once the zeta equation is identified with the S³ residual equation, zeta zeros
are exactly S³ pole-channel hits.  In the centered model, those hits are exactly
`Re(s)=1/2`.
-/

namespace Hqiv.Story

noncomputable section

/-- The S³ denominator/pole channel: the residual denominator vanishes. -/
def S3PoleChannel (P : ScaledS3Sample) : Prop :=
  S3ResidualZero P

/-- A pole channel tagged by prime scale, distinct from prime-axis survival. -/
def PrimeScalePoleChannel (P : ScaledS3Sample) : Prop :=
  Nat.Prime P.scale ∧ S3PoleChannel P

/-- S³ pole-channel hits are exactly balanced-imaginary residual cancellations. -/
theorem s3_pole_channel_iff_balanced (P : ScaledS3Sample) :
    S3PoleChannel P ↔ BalancedImag P.coords :=
  s3_residual_zero_iff_balanced P

/--
If zeta is identified with the S³ residual, then zeta zeros are exactly S³
pole-channel hits.
-/
theorem zeta_zero_iff_s3_pole_channel_of_eq
    {s : ℂ} {P : ScaledS3Sample}
    (hEq : ZetaEqualsS3ResidualAt s P) :
    ZetaZeroAt s ↔ S3PoleChannel P :=
  zeta_zero_iff_s3_residual_zero_of_eq hEq

/-- Centered residuals make the pole channel exactly the critical line. -/
theorem s3_pole_channel_iff_re_eq_half_of_centered
    {s : ℂ} {P : ScaledS3Sample}
    (hCenter : S3ResidualCentersCriticalLineAt s P) :
    S3PoleChannel P ↔ s.re = (1 / 2 : ℝ) := by
  constructor
  · intro hPole
    exact re_eq_half_of_centered_residual_zero hCenter hPole
  · intro hLine
    exact centered_residual_zero_of_re_eq_half hCenter hLine

/--
In a centered residual model, zeta zeros are exactly pole-channel hits of the
selected S³ sample.
-/
theorem model_zeta_zero_iff_pole_channel
    (M : S3CenteredZetaResidualModel) (s : ℂ) :
    ZetaZeroAt s ↔ S3PoleChannel (M.sample s) :=
  zeta_zero_iff_s3_pole_channel_of_eq (M.zeta_eq_residual s)

/-- In a centered residual model, pole-channel hits are exactly `Re(s)=1/2`. -/
theorem model_pole_channel_iff_re_eq_half
    (M : S3CenteredZetaResidualModel) (s : ℂ) :
    S3PoleChannel (M.sample s) ↔ s.re = (1 / 2 : ℝ) :=
  s3_pole_channel_iff_re_eq_half_of_centered (M.residual_centers_critical_line s)

/-- Combined centered model statement: zeta zeros are pole hits on the critical line. -/
theorem model_zeta_zero_iff_pole_channel_and_re_eq_half
    (M : S3CenteredZetaResidualModel) (s : ℂ) :
    ZetaZeroAt s ↔ S3PoleChannel (M.sample s) ∧ s.re = (1 / 2 : ℝ) := by
  constructor
  · intro hz
    have hPole : S3PoleChannel (M.sample s) :=
      (model_zeta_zero_iff_pole_channel M s).mp hz
    exact ⟨hPole, (model_pole_channel_iff_re_eq_half M s).mp hPole⟩
  · intro h
    exact (model_zeta_zero_iff_pole_channel M s).mpr h.1

/--
Prime-axis survivors are not pole-channel hits under the discrete law.

Thus "prime on a pole" must be represented by `PrimeScalePoleChannel`, not by
`PrimeAxisAtScale`, in the current survivor/cancellation convention.
-/
theorem not_s3_pole_channel_of_primeAxisAtScale
    (P : ScaledS3Sample)
    (hPrimeAxis : PrimeAxisAtScale P) :
    ¬ S3PoleChannel P := by
  intro hPole
  exact prime_axis_at_scale_survives P hPrimeAxis hPole

/-- Under the discrete law, every non-prime-axis sample is in the pole/zero channel. -/
theorem s3_pole_channel_of_not_primeAxisAtScale
    (L : S3DiscreteNullLatticeLaw)
    (P : ScaledS3Sample)
    (hNotPrimeAxis : ¬ PrimeAxisAtScale P) :
    S3PoleChannel P :=
  cancels_of_not_prime_axis_at_scale L P hNotPrimeAxis

end
end Hqiv.Story
