import Hqiv.Story.S3ZetaResidualModel

/-!
# Centered S³ residual model

This module separates the coordinate-centering algebra from the analytic zeta
identification.

The centered residual is `s.re - 1/2`.  If an S³ sample has
`criticalProj sample = s.re - 1/2`, then residual cancellation is exactly the
critical-line condition `s.re = 1/2`.

Combining this coordinate lock with the previous zeta/residual equality model
again yields Mathlib's `RiemannHypothesis`.
-/

namespace Hqiv.Story

noncomputable section

/-- Real deviation from the critical line `Re(s)=1/2`. -/
def criticalLineDeviation (s : ℂ) : ℝ :=
  s.re - (1 / 2 : ℝ)

/-- The critical-line deviation vanishes exactly on `Re(s)=1/2`. -/
theorem criticalLineDeviation_eq_zero_iff (s : ℂ) :
    criticalLineDeviation s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  unfold criticalLineDeviation
  constructor <;> intro h <;> linarith

/-- A sample's S³ residual is centered on the critical-line deviation of `s`. -/
def S3ResidualCentersCriticalLineAt (s : ℂ) (P : ScaledS3Sample) : Prop :=
  criticalProj P.coords = criticalLineDeviation s

/--
Centered coordinate lock:
if the S³ residual is the critical-line deviation, then residual zero forces
`Re(s)=1/2`.
-/
theorem re_eq_half_of_centered_residual_zero
    {s : ℂ} {P : ScaledS3Sample}
    (hCenter : S3ResidualCentersCriticalLineAt s P)
    (hZero : S3ResidualZero P) :
    s.re = (1 / 2 : ℝ) := by
  have hDevZero : criticalLineDeviation s = 0 := by
    dsimp [S3ResidualZero] at hZero
    dsimp [S3ResidualCentersCriticalLineAt] at hCenter
    linarith
  exact (criticalLineDeviation_eq_zero_iff s).mp hDevZero

/-- Conversely, on the critical line a centered residual is zero. -/
theorem centered_residual_zero_of_re_eq_half
    {s : ℂ} {P : ScaledS3Sample}
    (hCenter : S3ResidualCentersCriticalLineAt s P)
    (hLine : s.re = (1 / 2 : ℝ)) :
    S3ResidualZero P := by
  dsimp [S3ResidualZero, S3ResidualCentersCriticalLineAt] at hCenter ⊢
  have hDevZero : criticalLineDeviation s = 0 :=
    (criticalLineDeviation_eq_zero_iff s).mpr hLine
  linarith

/-- A residual model whose S³ residual is explicitly centered on `Re(s)-1/2`. -/
structure S3CenteredZetaResidualModel where
  sample : ℂ → ScaledS3Sample
  zeta_eq_residual : ∀ s : ℂ, ZetaEqualsS3ResidualAt s (sample s)
  residual_centers_critical_line :
    ∀ s : ℂ, S3ResidualCentersCriticalLineAt s (sample s)

/-- A centered residual model gives the previous residual model. -/
def S3CenteredZetaResidualModel.toResidualModel
    (M : S3CenteredZetaResidualModel) :
    S3ZetaResidualModel where
  sample := M.sample
  zeta_eq_residual := M.zeta_eq_residual
  residual_zero_locks_re_half := by
    intro s hZero
    exact re_eq_half_of_centered_residual_zero
      (M.residual_centers_critical_line s)
      hZero

/-- Full RH closure from a centered zeta/S³ residual model. -/
theorem RiemannHypothesis_of_s3_centered_zeta_residual_model
    (M : S3CenteredZetaResidualModel) :
    RiemannHypothesis :=
  RiemannHypothesis_of_s3_zeta_residual_model M.toResidualModel

/--
Zero equation in a centered model:
`ζ(s)=0` iff the real critical-line deviation vanishes.
-/
theorem riemannZeta_zero_iff_criticalLineDeviation_zero
    (M : S3CenteredZetaResidualModel) (s : ℂ) :
    riemannZeta s = 0 ↔ criticalLineDeviation s = 0 := by
  have hResidual :
      riemannZeta s = 0 ↔ criticalProj (M.sample s).coords = 0 :=
    riemannZeta_zero_iff_model_residual_zero M.toResidualModel s
  constructor
  · intro hz
    have hZero : criticalProj (M.sample s).coords = 0 := hResidual.mp hz
    have hCenter := M.residual_centers_critical_line s
    dsimp [S3ResidualCentersCriticalLineAt] at hCenter
    linarith
  · intro hDev
    have hCenter := M.residual_centers_critical_line s
    dsimp [S3ResidualCentersCriticalLineAt] at hCenter
    have hResidualZero : criticalProj (M.sample s).coords = 0 := by
      linarith
    exact hResidual.mpr hResidualZero

/-- Zero equation in a centered model is exactly the critical-line condition. -/
theorem riemannZeta_zero_iff_re_eq_half
    (M : S3CenteredZetaResidualModel) (s : ℂ) :
    riemannZeta s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  exact (riemannZeta_zero_iff_criticalLineDeviation_zero M s).trans
    (criticalLineDeviation_eq_zero_iff s)

end
end Hqiv.Story
