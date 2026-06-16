import Hqiv.Story.S3AnalyticStripLift
import Hqiv.Story.S3TangentOrbitCriticalLine
import Hqiv.Story.S3FortyFiveProjection
import Hqiv.Story.S3CenteredResidualModel
import Hqiv.Story.S3PathCHolonomy
import Hqiv.Story.S3AnalyticStripClassification
import Hqiv.Story.S3StripRollingProjection

/-!
# Critical line carrier bundle: circle on the line, hyperbolic envelope off it

The strip lift `stripPointLift` embeds every `s = σ + it` on `S³ ⊂ ℍ`, but the
**geometry is not uniform in σ**:

* **On `Re s = 1/2` (σ-equator):** the 45° free coordinate vanishes, the Hopf
  fiber radius is maximal (`r = 1`), the lift is the rolling map, the projection
  tangent is unimodular, FE inversion agrees with Schwarz conjugation on the
  tangent orbit, and Path C holonomy packages through `stripRollingMap`.
* **Off the line:** the free coordinate is nonzero, the Hopf circle is
  **strictly shrunk** (`r < 1`), cancellation needs the extra term
  `f(σ) + r(σ)(cos t + sin t) = 0`, the tangent modulus sorts the strip
  (`‖T‖ < 1` left, `> 1` right), and the quadruplet tangent orbit does **not**
  collapse.

The hyperbolic character off-line is in the **analytic slots** (`cosh`/`sinh`
in `sin(πs/2)` and `cos(πs/2)`), not in the `(f, r)` constraint
`f² + r² = 1` (a unit circle in the lift chart).  This module bundles the
proved line/off-line contrast — no new ζ identification.

**Honesty.** ζ-zero classification remains conditional on `ZetaEqualsS3ResidualAt`
and `StripAnalyticLiftMatches`.  The unconditional content is carrier geometry.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## Lift chart: free coordinate ↔ critical-line deviation -/

theorem strip_sigma_free_coord_eq_scaled_deviation (σ : ℝ) :
    stripSigmaFreeCoord σ = Real.sqrt 2 * (σ - (1 / 2 : ℝ)) := by
  dsimp [stripSigmaFreeCoord]
  rw [rot45Free_functionalPair_eq_scaled_deviation σ]
  have hsqrt : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 :=
    (div_eq_iff (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2))).mpr
      ((Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)).symm)
  rw [hsqrt]

theorem strip_sigma_free_coord_eq_critical_deviation (s : ℂ) :
    stripSigmaFreeCoord s.re = Real.sqrt 2 * criticalLineDeviation s := by
  unfold criticalLineDeviation
  exact strip_sigma_free_coord_eq_scaled_deviation s.re

theorem strip_sigma_free_coord_eq_zero_iff_deviation (s : ℂ) :
    stripSigmaFreeCoord s.re = 0 ↔ criticalLineDeviation s = 0 :=
  (strip_sigma_free_coord_vanishes_iff s.re).trans
    (criticalLineDeviation_eq_zero_iff s).symm

theorem strip_sigma_free_coord_ne_zero_iff (σ : ℝ) :
    stripSigmaFreeCoord σ ≠ 0 ↔ σ ≠ (1 / 2 : ℝ) :=
  not_iff_not.mpr (strip_sigma_free_coord_vanishes_iff σ)

/-! ## Hopf radius: maximal circle only on the line -/

theorem strip_sigma_free_coord_sq_pos_off_line {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσ : σ ≠ (1 / 2 : ℝ)) : 0 < stripSigmaFreeCoord σ ^ 2 := by
  rcases ne_iff_lt_or_gt.mp hσ with hlt | hgt
  · have hbound : stripSigmaFreeCoord σ ^ 2 ≤ 1 / 2 :=
      strip_sigma_free_coord_sq_le_half hσ0 hσ1
    have hne : stripSigmaFreeCoord σ ≠ 0 :=
      (strip_sigma_free_coord_ne_zero_iff σ).mpr hσ
    exact sq_pos_of_ne_zero hne
  · have hbound : stripSigmaFreeCoord σ ^ 2 ≤ 1 / 2 :=
      strip_sigma_free_coord_sq_le_half hσ0 hσ1
    have hne : stripSigmaFreeCoord σ ≠ 0 :=
      (strip_sigma_free_coord_ne_zero_iff σ).mpr hσ
    exact sq_pos_of_ne_zero hne

theorem strip_hopf_fiber_radius_le_one {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    stripHopfFiberRadius σ ≤ 1 := by
  have hsq := strip_hopf_fiber_radius_sq hσ0 hσ1
  have hf_nonneg : 0 ≤ stripSigmaFreeCoord σ ^ 2 := sq_nonneg _
  have hr_sq_le : stripHopfFiberRadius σ ^ 2 ≤ 1 := by linarith [hsq]
  have hr_nonneg : 0 ≤ stripHopfFiberRadius σ :=
    le_of_lt (strip_hopf_fiber_radius_pos hσ0 hσ1)
  rw [← Real.sqrt_one, ← Real.sqrt_sq hr_nonneg]
  exact Real.sqrt_le_sqrt hr_sq_le

theorem strip_hopf_fiber_radius_eq_one_iff {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    stripHopfFiberRadius σ = 1 ↔ σ = (1 / 2 : ℝ) := by
  have hsq := strip_hopf_fiber_radius_sq hσ0 hσ1
  constructor
  · intro hr
    have hf_zero : stripSigmaFreeCoord σ = 0 := by
      have hr_sq : stripHopfFiberRadius σ ^ 2 = 1 := by rw [hr]; norm_num
      have hf_sq : stripSigmaFreeCoord σ ^ 2 = 0 := by linarith [hsq, hr_sq]
      exact sq_eq_zero_iff.mp hf_sq
    exact (strip_sigma_free_coord_vanishes_iff σ).mp hf_zero
  · intro hσ
    subst hσ
    exact strip_hopf_fiber_radius_at_half

theorem strip_hopf_fiber_radius_lt_one_iff {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    stripHopfFiberRadius σ < 1 ↔ σ ≠ (1 / 2 : ℝ) := by
  have hle := strip_hopf_fiber_radius_le_one hσ0 hσ1
  have heq := strip_hopf_fiber_radius_eq_one_iff hσ0 hσ1
  constructor
  · intro hlt hσ
    have hr : stripHopfFiberRadius σ = 1 := heq.mpr hσ
    rw [hr] at hlt
    exact lt_irrefl _ hlt
  · intro hσ
    exact lt_of_le_of_ne hle ((heq.not).mpr hσ)

theorem strip_hopf_fiber_radius_lt_one_off_line {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσ : σ ≠ (1 / 2 : ℝ)) : stripHopfFiberRadius σ < 1 :=
  (strip_hopf_fiber_radius_lt_one_iff hσ0 hσ1).mpr hσ

/-! ## Unit-circle constraint in the (free, radius) chart -/

theorem strip_lift_free_radius_unit_circle {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    stripSigmaFreeCoord σ ^ 2 + stripHopfFiberRadius σ ^ 2 = 1 := by
  linarith [strip_hopf_fiber_radius_sq hσ0 hσ1]

/-! ## Line vs off-line cancellation -/

theorem strip_analytic_cancellation_on_line_iff (t : ℝ) :
    criticalProj (stripAnalyticLift (1 / 2) t) = 0 ↔ Real.cos t + Real.sin t = 0 :=
  strip_analytic_cancellation_on_line t

theorem strip_analytic_cancellation_off_line_needs_free {σ t : ℝ}
    (_hσ0 : 0 ≤ σ) (_hσ1 : σ ≤ 1) (hσ : σ ≠ (1 / 2 : ℝ)) :
    criticalProj (stripAnalyticLift σ t) = 0 ↔
      stripSigmaFreeCoord σ + stripHopfFiberRadius σ * (Real.cos t + Real.sin t) = 0 ∧
        stripSigmaFreeCoord σ ≠ 0 := by
  constructor
  · intro h
    refine ⟨?_, (strip_sigma_free_coord_ne_zero_iff σ).mpr hσ⟩
    exact (strip_analytic_cancellation_iff σ t).mp h
  · intro ⟨hsum, _⟩
    exact (strip_analytic_cancellation_iff σ t).mpr hsum

/-! ## Open strip: tangent hyperbolic sorting and orbit collapse -/

theorem critical_strip_off_line_tangent_not_unimodular {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    Complex.normSq (projTangent s) ≠ 1 := by
  intro h
  exact hσ ((normSq_projTangent_eq_one_iff h0 h1).mp h)

theorem critical_strip_off_line_so4_factor_nonzero {s : ℂ}
    (hσ : s.re ≠ (1 / 2 : ℝ)) : so4CriticalFactor s ≠ 0 :=
  so4CriticalFactor_ne_zero_off_line hσ

theorem critical_strip_off_line_quadruplet_does_not_collapse {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    (projTangent s)⁻¹ ≠ starRingEnd ℂ (projTangent s) := by
  intro h
  exact hσ ((projTangent_inv_eq_conj_iff h0 h1).mp h)

theorem critical_strip_left_half_tangent_disk {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re < (1 / 2 : ℝ)) :
    Complex.normSq (projTangent s) < 1 :=
  (normSq_projTangent_lt_one_iff h0 h1).mpr hσ

theorem critical_strip_right_half_tangent_exterior {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : (1 / 2 : ℝ) < s.re) :
    1 < Complex.normSq (projTangent s) :=
  (one_lt_normSq_projTangent_iff h0 h1).mpr hσ

/-! ## Critical line: unified equivalence chain -/

/--
On the open strip, these seven characterizations of the critical line agree.
This is the **carrier bundle**: the line is not one more σ-slice — it is the
unique locus where lift, tangent, equator factor, and orbit symmetries align.
-/
theorem critical_line_carrier_iff_chain {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    s.re = (1 / 2 : ℝ) ↔
      onStripSigmaEquator s.re ∧
        stripHopfFiberRadius s.re = 1 ∧
          criticalLineDeviation s = 0 ∧
            so4CriticalFactor s = 0 ∧
              Complex.normSq (projTangent s) = 1 ∧
                (projTangent s)⁻¹ = starRingEnd ℂ (projTangent s) := by
  have hσ0 : 0 ≤ s.re := h0.le
  have hσ1 : s.re ≤ 1 := h1.le
  constructor
  · intro hσ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (on_strip_sigma_equator_iff s.re).mpr hσ
    · rw [hσ]; exact strip_hopf_fiber_radius_at_half
    · exact (criticalLineDeviation_eq_zero_iff s).mpr hσ
    · exact (so4CriticalFactor_zero_iff s).mpr hσ
    · exact (normSq_projTangent_eq_one_iff h0 h1).mpr hσ
    · exact (projTangent_inv_eq_conj_iff h0 h1).mpr hσ
  · intro ⟨hEquator, hr, hDev, hcf, hTan, hCollapse⟩
    have hσ : s.re = (1 / 2 : ℝ) := (on_strip_sigma_equator_iff s.re).mp hEquator
    exact hσ

theorem critical_line_lift_is_rolling {s : ℂ} (hσ : s.re = (1 / 2 : ℝ)) :
    stripPointLift s = stripRollingMap s.im :=
  strip_point_lift_on_critical_line hσ

theorem critical_line_carrier_maximal_hopf_circle {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    s.re = (1 / 2 : ℝ) ↔ stripHopfFiberRadius s.re = 1 :=
  (strip_hopf_fiber_radius_eq_one_iff h0.le h1.le).symm

theorem critical_line_carrier_unimodular_tangent {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    s.re = (1 / 2 : ℝ) ↔ Complex.normSq (projTangent s) = 1 :=
  (normSq_projTangent_eq_one_iff h0 h1).symm

theorem critical_line_carrier_orbit_collapse {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    s.re = (1 / 2 : ℝ) ↔
      (projTangent s)⁻¹ = starRingEnd ℂ (projTangent s) :=
  (projTangent_inv_eq_conj_iff h0 h1).symm

/-! ## Holonomy: Path C on the line via rolling -/

/--
On the critical line, Path C classification reduces to the rolling map:
holonomy closure on the **full** Hopf circle, not a shrunken off-line fiber.
-/
theorem critical_line_pathC_classification_via_rolling
    {s : ℂ} {P : ScaledS3Sample}
    (hσ : s.re = (1 / 2 : ℝ))
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔
      ZeroProducingOrbit (stripRollingMap s.im) ∧ PathEStripHolonomyCloses s := by
  constructor
  · intro hζ
    refine ⟨?_, (pathE_strip_holonomy_closes_iff_zeta_zero h0 h1).mpr hζ⟩
    exact (analytic_strip_rolling_classification_on_line hσ hLift hEq).mp hζ
  · intro ⟨hRoll, _⟩
    exact (analytic_strip_rolling_classification_on_line hσ hLift hEq).mpr hRoll

theorem critical_line_pathC_rolling_only
    {s : ℂ} {P : ScaledS3Sample}
    (hσ : s.re = (1 / 2 : ℝ))
    (hLift : StripAnalyticLiftMatches s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ ZeroProducingOrbit (stripRollingMap s.im) :=
  analytic_strip_rolling_classification_on_line hσ hLift hEq

/-! ## Off-line carrier tax (unconditional geometry) -/

/--
Off the critical line on the closed strip `0 ≤ σ ≤ 1`, the lift carries a
nonzero equator offset and a strictly shrunken Hopf circle.
-/
theorem off_line_carrier_shrinks_hopf_fiber {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hσ : σ ≠ (1 / 2 : ℝ)) :
    stripSigmaFreeCoord σ ≠ 0 ∧ stripHopfFiberRadius σ < 1 := by
  refine ⟨(strip_sigma_free_coord_ne_zero_iff σ).mpr hσ, ?_⟩
  exact strip_hopf_fiber_radius_lt_one_off_line hσ0 hσ1 hσ

/--
Off the open strip, the analytic tangent is strictly inside or outside the unit
circle according to the half-plane — the hyperbolic envelope sorting `σ`.
-/
theorem off_line_hyperbolic_tangent_sorts {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hσ : s.re ≠ (1 / 2 : ℝ)) :
    (s.re < (1 / 2 : ℝ) ∧ Complex.normSq (projTangent s) < 1) ∨
      ((1 / 2 : ℝ) < s.re ∧ 1 < Complex.normSq (projTangent s)) := by
  rcases ne_iff_lt_or_gt.mp hσ with hlt | hgt
  · exact Or.inl ⟨hlt, (normSq_projTangent_lt_one_iff h0 h1).mpr hlt⟩
  · exact Or.inr ⟨hgt, (one_lt_normSq_projTangent_iff h0 h1).mpr hgt⟩

/-!
## Status

* **Line-special (unconditional):** `critical_line_carrier_iff_chain` — equator,
  maximal Hopf radius, deviation, equator factor, unimodular tangent, orbit collapse.
* **Off-line (unconditional):** shrunken fiber, extra cancellation term, tangent
  sorting, quadruplet does not collapse.
* **Holonomy (conditional):** `critical_line_pathC_classification_via_rolling` —
  Path C on the line through `stripRollingMap`; off-line uses full lift + `f(σ)`.
* **ζ identification** unchanged: `ZetaEqualsS3ResidualAt` / `StripAnalyticLiftMatches`.
-/

end

end Hqiv.Story
