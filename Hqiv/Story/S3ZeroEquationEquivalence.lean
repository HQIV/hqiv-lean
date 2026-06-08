import Hqiv.Story.S3QuaternionOrientation

/-!
# Equating the zeta and S³ residual equations at zero

This module formalizes the requested "set the two equations equal at the `0`"
step.

If a coordinate/analytic bridge identifies the zeta value `ζ(s)` with the complex
lift of the S³ residual `criticalProj P.coords`, then the zero equations are
equivalent:

`ζ(s) = 0 ↔ criticalProj P.coords = 0`.

The module then rewrites the S³ residual zero as `BalancedImag`, and under the
discrete null-lattice law rewrites nonzero zeta values as prime-axis-at-scale
survivors.
-/

namespace Hqiv.Story

noncomputable section

/-- The S³ residual equation at zero. -/
def S3ResidualZero (P : ScaledS3Sample) : Prop :=
  criticalProj P.coords = 0

/-- The zeta equation at zero. -/
def ZetaZeroAt (s : ℂ) : Prop :=
  riemannZeta s = 0

/--
Analytic/coordinate bridge identifying the zeta equation with the S³ residual
readout at a point.
-/
def ZetaEqualsS3ResidualAt (s : ℂ) (P : ScaledS3Sample) : Prop :=
  riemannZeta s = (criticalProj P.coords : ℂ)

/-- If the two equations are equal, then their zero loci are equivalent. -/
theorem zeta_zero_iff_s3_residual_zero_of_eq
    {s : ℂ} {P : ScaledS3Sample}
    (hEq : ZetaEqualsS3ResidualAt s P) :
    ZetaZeroAt s ↔ S3ResidualZero P := by
  dsimp [ZetaEqualsS3ResidualAt] at hEq
  dsimp [ZetaZeroAt, S3ResidualZero]
  constructor
  · intro hz
    have hcp_complex : (criticalProj P.coords : ℂ) = 0 := by
      simpa [hEq] using hz
    exact Complex.ofReal_eq_zero.mp hcp_complex
  · intro hp
    simp [hEq, hp]

/-- The S³ residual zero is exactly the balanced-imaginary condition. -/
theorem s3_residual_zero_iff_balanced (P : ScaledS3Sample) :
    S3ResidualZero P ↔ BalancedImag P.coords :=
  criticalProj_eq_zero_iff_balanced P.coords

/-- Zeta zero equivalence rewritten directly as the S³ balance condition. -/
theorem zeta_zero_iff_balanced_of_eq
    {s : ℂ} {P : ScaledS3Sample}
    (hEq : ZetaEqualsS3ResidualAt s P) :
    ZetaZeroAt s ↔ BalancedImag P.coords := by
  exact (zeta_zero_iff_s3_residual_zero_of_eq hEq).trans
    (s3_residual_zero_iff_balanced P)

/--
Under the discrete S³ law and a zeta/S³ equation identification, nonzero zeta
value is equivalent to prime-axis-at-scale survival.
-/
theorem zeta_nonzero_iff_primeAxisAtScale_of_eq_and_law
    (L : S3DiscreteNullLatticeLaw)
    {s : ℂ} {P : ScaledS3Sample}
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s ≠ 0 ↔ PrimeAxisAtScale P := by
  have hZero : riemannZeta s = 0 ↔ criticalProj P.coords = 0 :=
    zeta_zero_iff_s3_residual_zero_of_eq hEq
  have hSurvive : criticalProj P.coords ≠ 0 ↔ PrimeAxisAtScale P :=
    discrete_prime_axis_survival_iff L P
  constructor
  · intro hzNonzero
    exact hSurvive.mp (fun hResidualZero => hzNonzero (hZero.mpr hResidualZero))
  · intro hPrime hZetaZero
    exact hSurvive.mpr hPrime (hZero.mp hZetaZero)

/--
Contrapositive zero-channel form:
if a sample is not prime-axis-at-scale, then any zeta value identified with its
S³ residual is zero.
-/
theorem zeta_zero_of_not_primeAxisAtScale_of_eq_and_law
    (L : S3DiscreteNullLatticeLaw)
    {s : ℂ} {P : ScaledS3Sample}
    (hEq : ZetaEqualsS3ResidualAt s P)
    (hNotPrime : ¬ PrimeAxisAtScale P) :
    riemannZeta s = 0 := by
  have hResidualZero : criticalProj P.coords = 0 :=
    cancels_of_not_prime_axis_at_scale L P hNotPrime
  exact (zeta_zero_iff_s3_residual_zero_of_eq hEq).mpr hResidualZero

/--
Prime survivor form:
if a sample is prime-axis-at-scale, then an identified zeta value is nonzero.
-/
theorem zeta_nonzero_of_primeAxisAtScale_of_eq_and_law
    (L : S3DiscreteNullLatticeLaw)
    {s : ℂ} {P : ScaledS3Sample}
    (hEq : ZetaEqualsS3ResidualAt s P)
    (hPrime : PrimeAxisAtScale P) :
    riemannZeta s ≠ 0 :=
  (zeta_nonzero_iff_primeAxisAtScale_of_eq_and_law L hEq).mpr hPrime

end
end Hqiv.Story
