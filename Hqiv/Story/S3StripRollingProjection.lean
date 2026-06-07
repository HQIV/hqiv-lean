import Hqiv.Story.S3ZeroProducingOrbits
import Hqiv.Story.S3InteriorPathE
import Hqiv.Story.S3FortyFiveProjection
import Hqiv.Story.S3ZetaAxisRotationProjection
import Hqiv.Story.S3ExplicitFormulaIdentity
import Hqiv.Story.S3ExplicitFormulaDualitySlot
import Mathlib.Analysis.Complex.Trigonometric

/-!
# S³ rolling up the critical strip: height, twiddle phases, and projection

Geometric picture:

* The critical strip is a **cylinder** over the real σ-axis; at fixed `σ`, height
  `t = Im(s)` parametrizes a **circle** on the pure-imaginary S³ equator.
* After the 45° readout (`criticalProj`), that circle carries **Fourier twiddle**
  content `e^{i t}` against the surviving projection amplitude.
* **Zero-producing orbits** are exactly the angles where the rolled projection
  cancels (`criticalProj = 0` ↔ `BalancedImag`).
* **Prime-axis survivors** keep nonzero projection — the geometric counterpart of
  weights in the discrete explicit-formula prime term (`primeExplicitTerm`).

**Honesty.** Rolling geometry and twiddle algebra are proved here. Identifying
`ζ(s)` with the rolled projection requires the existing bridge
`ZetaEqualsS3ResidualAt` (or a centered residual model). No bare
`ζ(s)=0 ↔ criticalProj(roll t)=0` without that identification.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real ArithmeticFunction

/-! ## Critical strip as σ × height cylinder -/

/-- Open critical strip `0 < Re(s) < 1`. -/
def criticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

/-- A strip point as its `(σ, t)` cylinder coordinates. -/
theorem critical_strip_as_cylinder (s : ℂ) :
    s = s.re + s.im * I :=
  (Complex.re_add_im s).symm

/-! ## Pure-imaginary equator on S³ -/

/--
The **real equator** of the quaternion shell: unit-norm points with vanishing real
part (the `S²` of imaginary unit quaternions inside `S³`).
-/
def realEquator (p : QuaternionCoords) : Prop :=
  p 0 = 0 ∧ OnS3 p

/-! ## Roll S³ up the strip: `t = Im(s)` parametrizes a j–k circle -/

/--
Height `t` rolls a circle on the pure-imaginary equator.  The j/k slots carry the
oscillatory (Fourier) content; the real coordinate stays at the equator slice.
-/
noncomputable def stripRollingMap (t : ℝ) : QuaternionCoords :=
  fun i =>
    match i with
    | 0 | 1 => 0
    | 2 => Real.cos t
    | 3 => Real.sin t

/-- The rolling angle is the strip height (natural null-lattice scaling is `1`). -/
noncomputable def stripRollingAngle (t : ℝ) : ℝ :=
  t

theorem strip_rolling_angle_eq_height (t : ℝ) :
    stripRollingAngle t = t :=
  rfl

theorem strip_rolling_map_on_s3 (t : ℝ) :
    OnS3 (stripRollingMap t) := by
  dsimp [OnS3, stripRollingMap]
  rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + Real.cos t ^ 2 + Real.sin t ^ 2 =
        Real.cos t ^ 2 + Real.sin t ^ 2 by ring]
  exact Real.cos_sq_add_sin_sq t

theorem rolling_on_real_equator (t : ℝ) :
    realEquator (stripRollingMap t) := by
  constructor
  · simp [realEquator, stripRollingMap]
  · exact strip_rolling_map_on_s3 t

theorem strip_rolling_critical_proj (t : ℝ) :
    criticalProj (stripRollingMap t) =
      (Real.cos t + Real.sin t) / Real.sqrt 2 := by
  simp [criticalProj, imagSum, stripRollingMap]

theorem strip_rolling_cancellation_iff (t : ℝ) :
    criticalProj (stripRollingMap t) = 0 ↔ Real.cos t + Real.sin t = 0 := by
  rw [strip_rolling_critical_proj]
  constructor
  · intro h
    exact (div_eq_zero_iff.mp h).resolve_right (by positivity)
  · intro h
    rw [h]
    ring

theorem rolling_cancellation_iff_zero_producing (t : ℝ) :
    criticalProj (stripRollingMap t) = 0 ↔ ZeroProducingOrbit (stripRollingMap t) :=
  (zero_producing_orbit_iff_critical_proj_zero (stripRollingMap t)).symm

/-! ## Fourier twiddle readout after 45° projection -/

/--
Projection of the rolled S³ point with a unit **Fourier twiddle** `e^{i t}`.

Off the balance locus the phase rotates; at cancellation the amplitude vanishes
regardless of phase.
-/
noncomputable def rollingFourierTwiddle (t : ℝ) : ℂ :=
  Complex.exp (I * t) * (criticalProj (stripRollingMap t) : ℂ)

theorem rolling_twiddle_vanishes_iff_balanced (t : ℝ) :
    rollingFourierTwiddle t = 0 ↔ BalancedImag (stripRollingMap t) := by
  constructor
  · intro h
    rw [rollingFourierTwiddle, mul_eq_zero] at h
    rcases h with hExp | hProj
    · exact False.elim (Complex.exp_ne_zero _ hExp)
    · exact (criticalProj_eq_zero_iff_balanced _).1 (Complex.ofReal_eq_zero.mp hProj)
  · intro hBal
    simp [rollingFourierTwiddle, (criticalProj_eq_zero_iff_balanced _).mpr hBal]

theorem rolling_twiddle_vanishes_iff_zero_producing (t : ℝ) :
    rollingFourierTwiddle t = 0 ↔ ZeroProducingOrbit (stripRollingMap t) := by
  rw [rolling_twiddle_vanishes_iff_balanced, zero_producing_orbit_iff_balanced]

/-! ## Critical-line sin/cos slots = strip twiddle angles -/

/--
On the critical line `s = 1/2 + i t`, the FE j/k rotation slots use angle
`π/4 + π t / 2` — the same 45°-offset circle geometry as `stripRollingMap`.
-/
theorem zeta_sin_slot_critical_line (t : ℝ) :
    zetaSinSlot (1 / 2 + t * I) =
      Complex.sin (Real.pi / 4 + (Real.pi * t / 2) * I) := by
  unfold zetaSinSlot
  congr 1
  push_cast
  ring_nf

theorem zeta_cos_slot_critical_line (t : ℝ) :
    zetaCosSlot (1 / 2 + t * I) =
      Complex.cos (Real.pi / 4 + (Real.pi * t / 2) * I) := by
  unfold zetaCosSlot
  congr 1
  push_cast
  ring_nf

/--
At the critical-line center `σ = 1/2`, the 45° free coordinate vanishes — rolling
projects onto the line where only the twiddle height `t` remains.
-/
theorem critical_line_on_45_equator :
    rot45Free (functionalPair (1 / 2)) = 0 :=
  (rot45Free_functionalPair_eq_zero_iff (1 / 2)).2 rfl

/-! ## Rolling sample identification (bridge layer) -/

/--
A sampled point on the rolled fiber at critical-line height `t = Im(s)`.
-/
def RollingMatchesCriticalHeight (s : ℂ) (P : ScaledS3Sample) : Prop :=
  s.re = (1 / 2 : ℝ) ∧ P.coords = stripRollingMap s.im

theorem rolling_matches_critical_height_on_line
    {s : ℂ} {P : ScaledS3Sample}
    (hRoll : RollingMatchesCriticalHeight s P) :
    realEquator P.coords :=
  hRoll.2 ▸ rolling_on_real_equator s.im

theorem zeta_zero_iff_rolling_cancellation_of_match
    {s : ℂ} {P : ScaledS3Sample}
    (hRoll : RollingMatchesCriticalHeight s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ criticalProj (stripRollingMap s.im) = 0 := by
  simpa [← hRoll.2] using
    (zeta_zero_iff_zero_producing_orbit_of_eq hEq).trans
      (zero_producing_orbit_iff_critical_proj_zero _)

theorem zeta_zero_iff_rolling_twiddle_vanishes_of_match
    {s : ℂ} {P : ScaledS3Sample}
    (hRoll : RollingMatchesCriticalHeight s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ rollingFourierTwiddle s.im = 0 := by
  rw [zeta_zero_iff_rolling_cancellation_of_match hRoll hEq,
    rolling_twiddle_vanishes_iff_balanced, criticalProj_eq_zero_iff_balanced]

theorem centered_model_rolling_zero_iff_balanced
    (M : S3CenteredZetaResidualModel) {s : ℂ}
    (_hLine : s.re = (1 / 2 : ℝ))
    (hRoll : (M.sample s).coords = stripRollingMap s.im) :
    riemannZeta s = 0 ↔ BalancedImag (stripRollingMap s.im) := by
  rw [← hRoll, model_zeta_zero_iff_zero_producing_orbit M s, zero_producing_orbit_iff_balanced]

/-! ## Factoring information: prime-axis survivors vs explicit-formula prime term -/

/--
A rolled fiber point survives projection exactly when it is prime-axis-at-scale
under the discrete null-lattice law.
-/
theorem rolling_survivor_iff_prime_axis
    (L : S3DiscreteNullLatticeLaw) (P : ScaledS3Sample) :
    criticalProj P.coords ≠ 0 ↔ PrimeAxisAtScale P :=
  discrete_prime_axis_survival_iff L P

theorem rolling_fiber_prime_axis_survivor
    (L : S3DiscreteNullLatticeLaw) {t : ℝ} {P : ScaledS3Sample}
    (hCoords : P.coords = stripRollingMap t)
    (hPrime : PrimeAxisAtScale P) :
    criticalProj (stripRollingMap t) ≠ 0 := by
  rw [← hCoords]
  exact prime_axis_at_scale_survives P hPrime

theorem vonMangoldt_two_pos : 0 < vonMangoldt 2 := by
  have hp : Nat.Prime 2 := by norm_num
  rw [vonMangoldt_prime_eq_log hp]
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

/--
**Factoring channel (finite truncation).** A nonzero rolled projection forces a
nonzero prime explicit-formula weight at truncation `N ≥ 2`: the Λ-side pairing
cannot vanish when the geometric survivor amplitude is nonzero.
-/
theorem rolling_survivor_forces_prime_explicit_term
    (t : ℝ) (hSurv : criticalProj (stripRollingMap t) ≠ 0) :
    primeExplicitTerm 2 (fun _ => criticalProj (stripRollingMap t)) ≠ 0 := by
  dsimp only [primeExplicitTerm]
  have h1 : (1 : ℕ) ≤ 2 := by norm_num
  rw [Finset.sum_Icc_succ_top h1]
  have hhead :
      ∑ k ∈ Finset.Icc 1 1, vonMangoldt k * criticalProj (stripRollingMap t) = 0 := by
    rw [Finset.Icc_self, Finset.sum_singleton, vonMangoldt_one_eq_zero, zero_mul]
  rw [hhead, zero_add, show (1 + 1 : ℕ) = 2 by norm_num]
  exact mul_ne_zero (ne_of_gt vonMangoldt_two_pos) hSurv

/--
Prime-axis survival on a rolled sample is the geometric face of factoring
information surviving into the explicit-formula prime channel.
-/
theorem strip_holds_factoring_via_prime_axis
    (L : S3DiscreteNullLatticeLaw) {t : ℝ} {P : ScaledS3Sample}
    (hCoords : P.coords = stripRollingMap t) :
    PrimeAxisAtScale P ↔
      primeExplicitTerm 2 (fun _ => criticalProj (stripRollingMap t)) ≠ 0 := by
  constructor
  · intro hPrime
    exact rolling_survivor_forces_prime_explicit_term t
      (hCoords ▸ prime_axis_at_scale_survives P hPrime)
  · intro hTerm
    have hSurv : criticalProj P.coords ≠ 0 := by
      intro hzero
      have hzeroTerm :
          primeExplicitTerm 2 (fun _ => criticalProj (stripRollingMap t)) = 0 := by
        dsimp only [primeExplicitTerm]
        have h1 : (1 : ℕ) ≤ 2 := by norm_num
        rw [Finset.sum_Icc_succ_top h1]
        have hhead :
            ∑ k ∈ Finset.Icc 1 1, vonMangoldt k * criticalProj (stripRollingMap t) = 0 := by
          rw [Finset.Icc_self, Finset.sum_singleton, vonMangoldt_one_eq_zero, zero_mul]
        rw [hhead, zero_add, show (1 + 1 : ℕ) = 2 by norm_num]
        exact mul_eq_zero.mpr (Or.inr (hCoords ▸ hzero))
      exact hTerm hzeroTerm
    exact (rolling_survivor_iff_prime_axis L P).mp hSurv

/-! ## Main geometric classification (conditional on rolling identification) -/

/--
**Main geometric statement (centered model).** On the critical line, with the model
sample given by rolling `Im(s)`, ζ-zeros are exactly balanced rolled orbits.
-/
theorem critical_strip_factoring_from_S3_rolling
    (M : S3CenteredZetaResidualModel) {s : ℂ}
    (_hLine : s.re = (1 / 2 : ℝ))
    (hRoll : (M.sample s).coords = stripRollingMap s.im) :
    riemannZeta s = 0 ↔ ZeroProducingOrbit (stripRollingMap s.im) := by
  rw [← hRoll, model_zeta_zero_iff_zero_producing_orbit M s]

theorem critical_strip_factoring_from_S3_rolling_twiddle
    (M : S3CenteredZetaResidualModel) {s : ℂ}
    (hLine : s.re = (1 / 2 : ℝ))
    (hRoll : (M.sample s).coords = stripRollingMap s.im) :
    riemannZeta s = 0 ↔ rollingFourierTwiddle s.im = 0 := by
  rw [critical_strip_factoring_from_S3_rolling M hLine hRoll,
    rolling_twiddle_vanishes_iff_zero_producing]

/--
Bridge form: rolling identification + `ZetaEqualsS3ResidualAt` packages the same
classification without assuming a global centered model.
-/
theorem critical_strip_rolling_classification
    {s : ℂ} {P : ScaledS3Sample}
    (hRoll : RollingMatchesCriticalHeight s P)
    (hEq : ZetaEqualsS3ResidualAt s P) :
    riemannZeta s = 0 ↔ ZeroProducingOrbit (stripRollingMap s.im) := by
  exact (zeta_zero_iff_rolling_cancellation_of_match hRoll hEq).trans
    (rolling_cancellation_iff_zero_producing s.im)

/-!
## Status

* **Cylinder:** `t = Im(s)` parametrizes `stripRollingMap t` on the S³ real equator.
* **Twiddle:** `rollingFourierTwiddle t = e^{it} · criticalProj(roll t)`; zeros of ζ
  (under bridge) ↔ twiddle amplitude vanishes.
* **FE slots:** on `s = 1/2 + it`, `zetaSinSlot` / `zetaCosSlot` use the 45°-offset
  angle `π/4 + πt/2`.
* **Factoring:** prime-axis survivors on rolled fibers ↔ nonzero `primeExplicitTerm`
  at truncation `N = 2`.
* **ζ identification** remains conditional on `ZetaEqualsS3ResidualAt` / centered model.
-/

end

end Hqiv.Story
