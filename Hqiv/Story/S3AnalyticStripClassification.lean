import Hqiv.Story.S3AnalyticStripLift
import Hqiv.Story.S3PathCHolonomy
import Hqiv.Story.S3ZeroOrbitPathE
import Hqiv.Story.S3StripRollingProjection
import Hqiv.Story.S3CenteredResidualModel

/-!
# Whole-strip zero classification via the analytic lift

`stripPointLift` places every strip point `s = σ + it` on the cylinder carrier
`S³ ⊂ ℍ`.  Under the sample identification `StripAnalyticLiftMatches` and the
ζ bridge `ZetaEqualsS3ResidualAt`, zeros classify exactly as in Path C / Path E,
but now in **full** `(σ, t)` coordinates—not only on the critical line.

**Honesty.** All ζ-zero statements remain conditional on `ZetaEqualsS3ResidualAt`
(and the lift hypothesis).  Geometry of the cylinder and 2π periodicity is
proved in `S3AnalyticStripLift`.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## Zero loci in lift coordinates -/

theorem zeta_zero_iff_point_lift_critical_proj_zero
    {s : ℂ} {P : ScaledS3Sample}
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ criticalProj (stripPointLift s) = 0 := by
  rw [← hLift]
  exact (zeta_zero_iff_s3_residual_zero_of_eq hEq)

theorem zeta_zero_iff_point_lift_balanced
    {s : ℂ} {P : ScaledS3Sample}
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ BalancedImag (stripPointLift s) := by
  rw [← hLift]
  exact zeta_zero_iff_balanced_of_eq hEq

theorem zeta_zero_iff_point_lift_zero_producing
    {s : ℂ} {P : ScaledS3Sample}
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ ZeroProducingOrbit (stripPointLift s) := by
  rw [← hLift]
  exact zeta_zero_iff_zero_producing_orbit_of_eq hEq

theorem zeta_zero_iff_strip_analytic_cancellation
    {s : ℂ} {P : ScaledS3Sample}
    (hStrip : criticalStrip s)
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔
      stripSigmaFreeCoord s.re +
        stripHopfFiberRadius s.re * (Real.cos s.im + Real.sin s.im) = 0 :=
  (zeta_zero_iff_point_lift_critical_proj_zero hLift hEq).trans
    (by simpa [strip_point_lift_re_im] using strip_analytic_cancellation_iff s.re s.im)

/-! ## Twiddle readout on the whole strip -/

theorem strip_analytic_twiddle_vanishes_iff_balanced (σ t : ℝ) :
    stripAnalyticTwiddle σ t = 0 ↔ BalancedImag (stripAnalyticLift σ t) := by
  constructor
  · intro h
    rw [stripAnalyticTwiddle] at h
    rcases mul_eq_zero.mp h with hExp | hProj
    · exact False.elim (Complex.exp_ne_zero _ hExp)
    · exact (criticalProj_eq_zero_iff_balanced _).1 (Complex.ofReal_eq_zero.mp hProj)
  · intro hBal
    dsimp [stripAnalyticTwiddle]
    rw [(criticalProj_eq_zero_iff_balanced _).mpr hBal]
    simp

theorem zeta_zero_iff_strip_analytic_twiddle_vanishes
    {s : ℂ} {P : ScaledS3Sample}
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ stripAnalyticTwiddle s.re s.im = 0 := by
  refine (zeta_zero_iff_point_lift_critical_proj_zero hLift hEq).trans ?_
  refine (criticalProj_eq_zero_iff_balanced (stripPointLift s)).trans ?_
  simpa [strip_point_lift_re_im] using
    (strip_analytic_twiddle_vanishes_iff_balanced s.re s.im).symm

/-! ## Path C / Path E classification on the whole strip -/

/--
**Analytic-strip Path C classification** (conditional on lift + bridge).

A `ζ`-zero is exactly a balanced pointwise holonomy defect on the lifted fiber
together with Path E strip holonomy closure.
-/
theorem analytic_strip_pathC_classification
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔
      ZeroProducingOrbit (stripPointLift s) ∧ PathEStripHolonomyCloses s := by
  rw [← hLift]
  exact pathC_classification h0 h1 hEq

theorem analytic_strip_pathE_classification
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔
      BalancedImag (stripPointLift s) ∧ PathEChannelBalanceAt s := by
  rw [← hLift]
  constructor
  · intro hζ
    refine ⟨?_, (zeta_zero_iff_pathE_channel_balance h0 h1).mp hζ⟩
    exact (zero_producing_orbit_iff_balanced P.coords).mp
      ((zeta_zero_iff_zero_producing_orbit_of_eq hEq).mp hζ)
  · intro ⟨_, hPathE⟩
    exact (zeta_zero_iff_zero_producing_orbit_of_eq hEq).mpr
      ((zero_producing_orbit_iff_pathE_balance h0 h1 hEq).mpr hPathE)

theorem analytic_strip_zero_producing_iff_pathE_balance
    {s : ℂ} {P : ScaledS3Sample}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    ZeroProducingOrbit (stripPointLift s) ↔ PathEChannelBalanceAt s := by
  rw [← hLift]
  exact zero_producing_orbit_iff_pathE_balance h0 h1 hEq

/-! ## Critical line: recover rolling classification -/

theorem analytic_strip_rolling_classification_on_line
    {s : ℂ} {P : ScaledS3Sample}
    (hσ : s.re = (1 / 2 : ℝ))
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ ZeroProducingOrbit (stripRollingMap s.im) :=
  critical_strip_rolling_classification
    (rolling_matches_of_point_lift_on_line P hσ hLift) hEq

theorem analytic_strip_twiddle_classification_on_line
    {s : ℂ} {P : ScaledS3Sample}
    (hσ : s.re = (1 / 2 : ℝ))
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ rollingFourierTwiddle s.im = 0 :=
  zeta_zero_iff_rolling_twiddle_vanishes_of_match
    (rolling_matches_of_point_lift_on_line P hσ hLift) hEq

/-! ## Centered residual model with point lift -/

/--
A centered model whose samples are given by the analytic strip lift on the open
strip.
-/
def StripPointLiftCenteredModel (M : S3CenteredZetaResidualModel) : Prop :=
  ∀ s, criticalStrip s → (M.sample s).coords = stripPointLift s

theorem model_zeta_zero_iff_point_lift_orbit
    (M : S3CenteredZetaResidualModel)
    (hModel : StripPointLiftCenteredModel M) {s : ℂ} (hStrip : criticalStrip s) :
    riemannZeta s = 0 ↔ ZeroProducingOrbit (stripPointLift s) := by
  rw [← hModel s hStrip]
  exact model_zeta_zero_iff_zero_producing_orbit M s

theorem model_zeta_zero_iff_point_lift_balanced
    (M : S3CenteredZetaResidualModel)
    (hModel : StripPointLiftCenteredModel M) {s : ℂ} (hStrip : criticalStrip s) :
    riemannZeta s = 0 ↔ BalancedImag (stripPointLift s) := by
  rw [← hModel s hStrip]
  exact (model_zeta_zero_iff_zero_producing_orbit M s).trans
    (zero_producing_orbit_iff_balanced (M.sample s).coords)

theorem model_analytic_strip_cancellation
    (M : S3CenteredZetaResidualModel)
    (hModel : StripPointLiftCenteredModel M) {s : ℂ} (hStrip : criticalStrip s) :
    riemannZeta s = 0 ↔
      stripSigmaFreeCoord s.re +
        stripHopfFiberRadius s.re * (Real.cos s.im + Real.sin s.im) = 0 := by
  have hLift : StripAnalyticLiftMatches s (M.sample s) := hModel s hStrip
  exact zeta_zero_iff_strip_analytic_cancellation hStrip hLift (M.zeta_eq_residual s)

/-! ## σ-equator specialization -/

theorem zeta_zero_iff_sigma_equator_cancellation_on_line
    {s : ℂ} {P : ScaledS3Sample}
    (hσ : onStripSigmaEquator s.re)
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ Real.cos s.im + Real.sin s.im = 0 := by
  have hσ' : s.re = (1 / 2 : ℝ) := (on_strip_sigma_equator_iff s.re).mp hσ
  rw [zeta_zero_iff_point_lift_critical_proj_zero hLift hEq,
    strip_point_lift_on_critical_line hσ']
  exact strip_rolling_cancellation_iff s.im

/-!
## Status

* **Whole strip:** `zeta_zero_iff_strip_analytic_cancellation` packages zeros as
  a σ-dependent balance on the Hopf fiber.
* **Path C/E:** `analytic_strip_pathC_classification` and
  `analytic_strip_pathE_classification` extend holonomy classification off the line.
* **Critical line:** rolling and twiddle classifications recover from
  `strip_point_lift_on_critical_line`.
* **ζ identification** remains conditional on `ZetaEqualsS3ResidualAt`.
-/

end

end Hqiv.Story
