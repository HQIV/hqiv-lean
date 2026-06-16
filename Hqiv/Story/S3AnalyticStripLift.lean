import Hqiv.Story.S3StripRollingProjection
import Hqiv.Story.S3FortyFiveProjection
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Analytic strip lift to S³ ⊂ ℍ

The open critical strip is a **cylinder** `σ × S¹`:

* `σ = Re(s)` enters the quaternion carrier through the 45° **free coordinate**
  `rot45Free(functionalPair σ) = (2σ − 1) / √2` on the `i` slot;
* `t = Im(s)` parametrizes the **Hopf fiber circle** on the `j`/`k` slots with radius
  `√(1 − free²)` so the lifted point stays on `S³`;
* heights modulo `2π` define the same point on the fiber (ℂ cover vs ℍ circle).

At `σ = 1/2` the free coordinate vanishes, the fiber radius is `1`, and the lift
**coincides** with `stripRollingMap` from `S3StripRollingProjection`.

**Honesty.** This module proves the geometric lift and cylinder structure only.
Identifying `ζ(s)` with a projection of `stripPointLift s` still requires
`ZetaEqualsS3ResidualAt` (or a centered residual model).
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## σ-coordinate: 45° free slot on the cylinder base -/

/-- 45° free coordinate for strip real part `σ` (vanishes on the critical line). -/
noncomputable def stripSigmaFreeCoord (σ : ℝ) : ℝ :=
  rot45Free (functionalPair σ)

theorem strip_sigma_free_coord_eq (σ : ℝ) :
    stripSigmaFreeCoord σ = (2 * σ - 1) / Real.sqrt 2 :=
  rot45Free_functionalPair σ

theorem strip_sigma_free_coord_vanishes_iff (σ : ℝ) :
    stripSigmaFreeCoord σ = 0 ↔ σ = (1 / 2 : ℝ) :=
  rot45Free_functionalPair_eq_zero_iff σ

theorem strip_sigma_free_coord_sq_le_half {σ : ℝ} (_hσ0 : 0 ≤ σ) (_hσ1 : σ ≤ 1) :
    stripSigmaFreeCoord σ ^ 2 ≤ 1 / 2 := by
  rw [strip_sigma_free_coord_eq, div_pow]
  have hbound : (2 * σ - 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * σ - 1)]
  have hden : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hden]
  nlinarith

/-! ## Hopf fiber radius at fixed σ -/

/--
Radius of the `j`/`k` Hopf circle after placing `σ` on the `i` slot.
Stays strictly positive on the closed strip `0 ≤ σ ≤ 1`.
-/
noncomputable def stripHopfFiberRadius (σ : ℝ) : ℝ :=
  Real.sqrt (1 - stripSigmaFreeCoord σ ^ 2)

theorem strip_hopf_fiber_radius_sq {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    stripHopfFiberRadius σ ^ 2 = 1 - stripSigmaFreeCoord σ ^ 2 := by
  dsimp [stripHopfFiberRadius]
  have hnonneg : 0 ≤ 1 - stripSigmaFreeCoord σ ^ 2 := by
    have := strip_sigma_free_coord_sq_le_half hσ0 hσ1
    linarith
  rw [Real.sq_sqrt hnonneg]

theorem strip_hopf_fiber_radius_pos {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    0 < stripHopfFiberRadius σ := by
  dsimp [stripHopfFiberRadius]
  apply Real.sqrt_pos.mpr
  have hle : stripSigmaFreeCoord σ ^ 2 ≤ 1 / 2 :=
    strip_sigma_free_coord_sq_le_half hσ0 hσ1
  linarith

theorem stripSigmaFreeCoord_half : stripSigmaFreeCoord (1 / 2) = 0 :=
  (strip_sigma_free_coord_vanishes_iff (1 / 2)).mpr rfl

theorem strip_hopf_fiber_radius_at_half : stripHopfFiberRadius (1 / 2) = 1 := by
  have h₀ : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h₁ : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hsq : stripHopfFiberRadius (1 / 2) ^ 2 = 1 := by
    rw [strip_hopf_fiber_radius_sq h₀ h₁, stripSigmaFreeCoord_half]
    norm_num
  have hr : 0 ≤ stripHopfFiberRadius (1 / 2) :=
    le_of_lt (strip_hopf_fiber_radius_pos h₀ h₁)
  rw [← Real.sqrt_sq hr, hsq, Real.sqrt_one]

/-! ## Full analytic lift: σ × height → S³ -/

/--
**Analytic strip lift.**  The real quaternion slot stays at the `p₀ = 0` slice; `σ`
occupies the `i` slot; height `t` rolls the `j`/`k` Hopf fiber.
-/
noncomputable def stripAnalyticLift (σ t : ℝ) : QuaternionCoords :=
  fun i =>
    match i with
    | 0 => 0
    | 1 => stripSigmaFreeCoord σ
    | 2 => stripHopfFiberRadius σ * Real.cos t
    | 3 => stripHopfFiberRadius σ * Real.sin t

/-- Lift a strip point `s = σ + it` into the quaternion carrier. -/
noncomputable def stripPointLift (s : ℂ) : QuaternionCoords :=
  stripAnalyticLift s.re s.im

theorem strip_point_lift_re_im (s : ℂ) :
    stripPointLift s = stripAnalyticLift s.re s.im :=
  rfl

theorem strip_analytic_lift_on_s3 {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (t : ℝ) :
    OnS3 (stripAnalyticLift σ t) := by
  have hfiber :
      (stripHopfFiberRadius σ * Real.cos t) ^ 2 + (stripHopfFiberRadius σ * Real.sin t) ^ 2 =
        stripHopfFiberRadius σ ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  have hsum : stripSigmaFreeCoord σ ^ 2 + stripHopfFiberRadius σ ^ 2 = 1 := by
    have := strip_hopf_fiber_radius_sq hσ0 hσ1
    linarith
  dsimp only [OnS3, stripAnalyticLift]
  have hgoal : stripSigmaFreeCoord σ ^ 2 + (stripHopfFiberRadius σ * Real.cos t) ^ 2 +
      (stripHopfFiberRadius σ * Real.sin t) ^ 2 = 1 := by
    linarith [hfiber, hsum]
  simpa [zero_add] using hgoal

theorem strip_point_lift_on_strip {s : ℂ} (h : criticalStrip s) :
    OnS3 (stripPointLift s) :=
  strip_analytic_lift_on_s3 h.1.le h.2.le s.im

/-! ## Periodicity: ℂ height cover vs ℍ circle -/

/-- Heights that differ by an integer multiple of `2π` map to the same S³ point. -/
def sameStripHeight (t₁ t₂ : ℝ) : Prop :=
  ∃ n : ℤ, t₂ = t₁ + 2 * Real.pi * (n : ℝ)

theorem sameStripHeight_refl (t : ℝ) : sameStripHeight t t :=
  ⟨0, by push_cast; ring⟩

theorem sameStripHeight_symm {t₁ t₂ : ℝ} (h : sameStripHeight t₁ t₂) :
    sameStripHeight t₂ t₁ := by
  rcases h with ⟨n, hn⟩
  refine ⟨-n, ?_⟩
  push_cast at hn ⊢
  linarith [Real.pi_pos]

theorem strip_analytic_lift_period (σ t : ℝ) (n : ℤ) :
    stripAnalyticLift σ (t + 2 * Real.pi * (n : ℝ)) = stripAnalyticLift σ t := by
  funext i
  fin_cases i
  · simp only [stripAnalyticLift, stripHopfFiberRadius, stripSigmaFreeCoord]
  · simp only [stripAnalyticLift, stripHopfFiberRadius, stripSigmaFreeCoord]
  · simp only [stripAnalyticLift, stripHopfFiberRadius, stripSigmaFreeCoord]
    refine congr_arg (fun x => stripHopfFiberRadius σ * x) ?_
    rw [show t + 2 * Real.pi * (n : ℝ) = t + (n : ℝ) * (2 * Real.pi) by ring,
      Real.cos_add_int_mul_two_pi]
  · simp only [stripAnalyticLift, stripHopfFiberRadius, stripSigmaFreeCoord]
    refine congr_arg (fun x => stripHopfFiberRadius σ * x) ?_
    rw [show t + 2 * Real.pi * (n : ℝ) = t + (n : ℝ) * (2 * Real.pi) by ring,
      Real.sin_add_int_mul_two_pi]

theorem strip_analytic_lift_respects_height (σ : ℝ) {t₁ t₂ : ℝ}
    (h : sameStripHeight t₁ t₂) :
    stripAnalyticLift σ t₁ = stripAnalyticLift σ t₂ := by
  rcases h with ⟨n, hn⟩
  rw [hn, strip_analytic_lift_period]

/-! ## Critical line = rolling map (σ-equator) -/

theorem strip_analytic_lift_eq_rolling (t : ℝ) :
    stripAnalyticLift (1 / 2) t = stripRollingMap t := by
  funext i
  fin_cases i
  · rfl
  · dsimp [stripAnalyticLift, stripRollingMap]
    exact stripSigmaFreeCoord_half
  · dsimp [stripAnalyticLift, stripRollingMap]
    rw [strip_hopf_fiber_radius_at_half, one_mul]
  · dsimp [stripAnalyticLift, stripRollingMap]
    rw [strip_hopf_fiber_radius_at_half, one_mul]

theorem strip_point_lift_on_critical_line {s : ℂ} (hσ : s.re = (1 / 2 : ℝ)) :
    stripPointLift s = stripRollingMap s.im := by
  rw [strip_point_lift_re_im, hσ, strip_analytic_lift_eq_rolling]

/-- Whole-strip sample identification (generalizes `RollingMatchesCriticalHeight`). -/
def StripAnalyticLiftMatches (s : ℂ) (P : ScaledS3Sample) : Prop :=
  P.coords = stripPointLift s

theorem rolling_matches_of_point_lift_on_line {s : ℂ} (P : ScaledS3Sample)
    (hσ : s.re = (1 / 2 : ℝ)) (hEq : P.coords = stripPointLift s) :
    RollingMatchesCriticalHeight s P := by
  constructor
  · exact hσ
  · rw [hEq, strip_point_lift_on_critical_line hσ]

theorem point_lift_of_rolling_matches {s : ℂ} (P : ScaledS3Sample)
    (hRoll : RollingMatchesCriticalHeight s P) :
    P.coords = stripPointLift s := by
  rw [hRoll.2, strip_point_lift_on_critical_line hRoll.1]

theorem strip_analytic_matches_rolling_on_line {s : ℂ} (P : ScaledS3Sample)
    (hσ : s.re = (1 / 2 : ℝ)) :
    StripAnalyticLiftMatches s P ↔ RollingMatchesCriticalHeight s P := by
  constructor
  · exact rolling_matches_of_point_lift_on_line P hσ
  · intro hRoll
    dsimp [StripAnalyticLiftMatches]
    exact point_lift_of_rolling_matches P hRoll

/-! ## 45° projection readout on the whole strip -/

theorem strip_analytic_critical_proj (σ t : ℝ) :
    criticalProj (stripAnalyticLift σ t) =
      (stripSigmaFreeCoord σ +
        stripHopfFiberRadius σ * (Real.cos t + Real.sin t)) / Real.sqrt 2 := by
  simp [criticalProj, imagSum, stripAnalyticLift]
  ring

theorem strip_analytic_critical_proj_on_line (t : ℝ) :
    criticalProj (stripAnalyticLift (1 / 2) t) =
      (Real.cos t + Real.sin t) / Real.sqrt 2 := by
  rw [strip_analytic_lift_eq_rolling, strip_rolling_critical_proj]

theorem strip_analytic_cancellation_iff (σ t : ℝ) :
    criticalProj (stripAnalyticLift σ t) = 0 ↔
      stripSigmaFreeCoord σ + stripHopfFiberRadius σ * (Real.cos t + Real.sin t) = 0 := by
  rw [strip_analytic_critical_proj]
  constructor
  · intro h
    exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
  · intro h
    rw [h]
    ring

theorem strip_analytic_cancellation_on_line (t : ℝ) :
    criticalProj (stripAnalyticLift (1 / 2) t) = 0 ↔ Real.cos t + Real.sin t = 0 := by
  rw [strip_analytic_critical_proj_on_line]
  constructor
  · intro h
    exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
  · intro h
    rw [h]
    ring

/-! ## Hopf base circle at fixed σ -/

/-- Hopf-base coordinates of the fiber at fixed `σ` and height `t`. -/
noncomputable def stripHopfCircleCoords (σ t : ℝ) : ℝ × ℝ :=
  (stripHopfFiberRadius σ * Real.cos t, stripHopfFiberRadius σ * Real.sin t)

theorem strip_hopf_circle_on_unit_radius {σ : ℝ} (_hσ0 : 0 ≤ σ) (_hσ1 : σ ≤ 1) (t : ℝ) :
    (stripHopfCircleCoords σ t).1 ^ 2 + (stripHopfCircleCoords σ t).2 ^ 2 =
      stripHopfFiberRadius σ ^ 2 := by
  dsimp [stripHopfCircleCoords]
  rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]

theorem strip_hopf_circle_period (σ t : ℝ) (n : ℤ) :
    stripHopfCircleCoords σ (t + 2 * Real.pi * (n : ℝ)) = stripHopfCircleCoords σ t := by
  dsimp [stripHopfCircleCoords]
  rw [show t + 2 * Real.pi * (n : ℝ) = t + (n : ℝ) * (2 * Real.pi) by ring]
  simp only [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-! ## Cylinder coordinates and σ-fibers -/

/--
A point on the strip cylinder: real part `σ` and a height cover coordinate `t`
(the fiber is the `S¹` obtained by identifying `t` and `t + 2πn`).
-/
structure StripCylinderCoords where
  sigma : ℝ
  height : ℝ

/-- The S³ point carried by a cylinder coordinate. -/
noncomputable def stripCylinderToS3 (c : StripCylinderCoords) : QuaternionCoords :=
  stripAnalyticLift c.sigma c.height

theorem strip_cylinder_to_s3_period (c : StripCylinderCoords) (n : ℤ) :
    stripCylinderToS3 ⟨c.sigma, c.height + 2 * Real.pi * (n : ℝ)⟩ = stripCylinderToS3 c := by
  dsimp [stripCylinderToS3]
  exact strip_analytic_lift_period c.sigma c.height n

theorem strip_point_as_cylinder (s : ℂ) :
    stripPointLift s = stripCylinderToS3 ⟨s.re, s.im⟩ :=
  rfl

/-- Critical line as the σ-equator where the 45° free coordinate vanishes. -/
def onStripSigmaEquator (σ : ℝ) : Prop :=
  stripSigmaFreeCoord σ = 0

theorem on_strip_sigma_equator_iff (σ : ℝ) :
    onStripSigmaEquator σ ↔ σ = (1 / 2 : ℝ) :=
  strip_sigma_free_coord_vanishes_iff σ

theorem on_strip_sigma_equator_lift_eq_rolling {σ : ℝ} (hσ : onStripSigmaEquator σ) (t : ℝ) :
    stripAnalyticLift σ t = stripAnalyticLift (1 / 2) t := by
  have hσ' : σ = (1 / 2 : ℝ) := (on_strip_sigma_equator_iff σ).mp hσ
  subst hσ'
  rfl

/-! ## Twiddle readout on the whole strip -/

/--
Fourier twiddle against the 45° projection amplitude, now on the full cylinder.
At `σ = 1/2` this agrees with `rollingFourierTwiddle`.
-/
noncomputable def stripAnalyticTwiddle (σ t : ℝ) : ℂ :=
  Complex.exp (I * t) * (criticalProj (stripAnalyticLift σ t) : ℂ)

theorem strip_analytic_twiddle_on_line (t : ℝ) :
    stripAnalyticTwiddle (1 / 2) t = rollingFourierTwiddle t := by
  dsimp [stripAnalyticTwiddle, rollingFourierTwiddle]
  rw [strip_analytic_lift_eq_rolling]

theorem strip_analytic_twiddle_lift_period (σ t : ℝ) (n : ℤ) :
    criticalProj (stripAnalyticLift σ (t + 2 * Real.pi * (n : ℝ))) =
      criticalProj (stripAnalyticLift σ t) := by
  rw [strip_analytic_lift_period σ t n]

/-!
## Status

* **Whole strip:** `stripPointLift s` places every `s` in the cylinder carrier on `S³`.
* **σ-equator:** `onStripSigmaEquator σ ↔ σ = 1/2`; on that slice the lift is `stripRollingMap`.
* **Circle:** `sameStripHeight` / `2π` periodicity — cover coordinate in ℂ, compact fiber in ℍ.
* **Readout:** `strip_analytic_critical_proj` and `stripAnalyticTwiddle` extend rolling twiddle to all `σ`.
* **ζ identification** remains conditional on `ZetaEqualsS3ResidualAt` / centered model.
-/

end

end Hqiv.Story
