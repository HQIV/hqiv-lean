import Hqiv.Story.S3AnalyticStripLift
import Hqiv.Story.S3CenteredResidualModel
import Hqiv.Geometry.SpatialSliceRapidityScaffold
import Hqiv.Physics.CovariantSolution
import Hqiv.Physics.ModifiedMaxwell

/-!
# Strip equator factor ↔ rapidity-normalized jet coefficient

On the open critical strip `s = σ + it`, the 45° **equator readout**

`stripSigmaFreeCoord σ = rot45Free(functionalPair σ) = (2σ − 1)/√2`

is the pure-math coordinate separating harmonic alignment from Δ-curvature offset.

HQIV physics packages the **same scalar** as the rapidity-normalized covariant jet
coefficient `rapidityNormalizedJetCoeff φ t m = φ·t·δθ'(m)` once the strip chart
locks `φ = 1` and `t = stripSigmaFreeCoord σ / δθ'(m)`.

This is the explicit identification requested by the physics→pure-math mining program:
not an analogy — a proved equality under the canonical strip chart.

**Fiber decoupling.**  The coefficient depends on `σ` (cylinder base) only, not on
imaginary height `t = Im(s)` — matching the S³ cylinder lift in `S3AnalyticStripLift`.

**Covariant consequence.**  At vanishing HQVM metric jets, the Christoffel covariant
divergence with rapidity-normalized frozen jet equals **equator factor ×** the pure
`√(-g)`-cancelled surrogate (`covariant_div_F_O`).
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry Hqiv.Physics

noncomputable section

/-! ## Tipping denominator on positive shells -/

theorem delta_theta_prime_natCast_pos {m : ℕ} (hm : 0 < m) :
    0 < delta_theta_prime (m : ℝ) := by
  rw [delta_theta_prime_eq_arctan_mul_pi_div_two]
  exact mul_pos (Real.arctan_pos.mpr (by exact_mod_cast hm)) (by positivity)

theorem delta_theta_prime_natCast_ne_zero {m : ℕ} (hm : 0 < m) :
    delta_theta_prime (m : ℝ) ≠ 0 :=
  ne_of_gt (delta_theta_prime_natCast_pos hm)

/-! ## Canonical strip chart: lock rapidity time to equator factor -/

/--
**Strip chart time.**  With auxiliary `φ = 1`, choose rapidity time so the jet
coefficient matches the equator factor at real part `σ`.
Requires `m > 0` so `δθ'(m) ≠ 0`.
-/
noncomputable def stripEquatorJetTime (σ : ℝ) (m : ℕ) : ℝ :=
  stripSigmaFreeCoord σ / delta_theta_prime (m : ℝ)

theorem strip_equator_jet_time_def (σ : ℝ) (m : ℕ) :
    stripEquatorJetTime σ m = stripSigmaFreeCoord σ / delta_theta_prime (m : ℝ) :=
  rfl

/-! ## Main identification -/

/--
**Central identification.**  Rapidity-normalized jet coefficient equals the strip
equator factor `(2σ − 1)/√2` under the canonical chart `φ = 1`,
`t = stripEquatorJetTime σ m`.
-/
theorem rapidity_jet_coeff_eq_strip_equator_factor (σ : ℝ) {m : ℕ} (hm : 0 < m) :
    rapidityNormalizedJetCoeff 1 (stripEquatorJetTime σ m) m = stripSigmaFreeCoord σ := by
  dsimp [rapidityNormalizedJetCoeff, polarAngleFromRapidity, stripEquatorJetTime]
  field_simp [delta_theta_prime_natCast_ne_zero hm]

theorem rapidity_jet_coeff_eq_rot45_equator (σ : ℝ) {m : ℕ} (hm : 0 < m) :
    rapidityNormalizedJetCoeff 1 (stripEquatorJetTime σ m) m =
      rot45Free (functionalPair σ) := by
  rw [rapidity_jet_coeff_eq_strip_equator_factor σ hm]
  rfl

theorem rapidity_jet_coeff_eq_equator_factor (σ : ℝ) {m : ℕ} (hm : 0 < m) :
    rapidityNormalizedJetCoeff 1 (stripEquatorJetTime σ m) m =
      (2 * σ - 1) / Real.sqrt 2 := by
  rw [rapidity_jet_coeff_eq_strip_equator_factor σ hm, strip_sigma_free_coord_eq σ]

theorem strip_sigma_free_coord_eq_scaled_deviation (σ : ℝ) :
    stripSigmaFreeCoord σ = Real.sqrt 2 * (σ - (1 / 2 : ℝ)) := by
  dsimp [stripSigmaFreeCoord]
  rw [rot45Free_functionalPair_eq_scaled_deviation σ]
  have hsqrt : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 :=
    (div_eq_iff (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))).mpr
      ((Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm)
  rw [hsqrt]

theorem strip_sigma_free_coord_eq_critical_deviation (s : ℂ) :
    stripSigmaFreeCoord s.re = Real.sqrt 2 * criticalLineDeviation s := by
  rw [strip_sigma_free_coord_eq_scaled_deviation s.re]
  simp [criticalLineDeviation]

theorem rapidity_jet_coeff_eq_scaled_critical_deviation (σ : ℝ) {m : ℕ} (hm : 0 < m) :
    rapidityNormalizedJetCoeff 1 (stripEquatorJetTime σ m) m =
      Real.sqrt 2 * (σ - (1 / 2 : ℝ)) := by
  rw [rapidity_jet_coeff_eq_strip_equator_factor σ hm]
  exact strip_sigma_free_coord_eq_scaled_deviation σ

theorem rapidity_jet_coeff_eq_scaled_deviation (s : ℂ) {m : ℕ} (hm : 0 < m) :
    rapidityNormalizedJetCoeff 1 (stripEquatorJetTime s.re m) m =
      Real.sqrt 2 * criticalLineDeviation s := by
  rw [rapidity_jet_coeff_eq_strip_equator_factor s.re hm,
    strip_sigma_free_coord_eq_critical_deviation s]

theorem strip_point_equator_jet_lock (σ _t : ℝ) {m : ℕ} (hm : 0 < m) :
    rapidityNormalizedJetCoeff 1 (stripEquatorJetTime σ m) m =
      stripSigmaFreeCoord σ :=
  rapidity_jet_coeff_eq_strip_equator_factor σ hm

theorem strip_point_equator_vanishes_iff_critical_line (σ _t : ℝ) {m : ℕ} (hm : 0 < m) :
    rapidityNormalizedJetCoeff 1 (stripEquatorJetTime σ m) m = 0 ↔ σ = (1 / 2 : ℝ) := by
  rw [rapidity_jet_coeff_eq_strip_equator_factor σ hm, strip_sigma_free_coord_vanishes_iff σ]

/-! ## Chart packaging -/

/--
Canonical **critical-strip equator jet chart** at shell `m > 0`: packages the
proved coefficient lock and the `(2σ−1)/√2` readout.
-/
structure CriticalStripEquatorJetChart (σ : ℝ) (m : ℕ) where
  pos : 0 < m
  jet_time : ℝ
  jet_time_eq : jet_time = stripEquatorJetTime σ m
  coeff_eq_equator :
    rapidityNormalizedJetCoeff 1 jet_time m = stripSigmaFreeCoord σ
  coeff_eq_factor : rapidityNormalizedJetCoeff 1 jet_time m = (2 * σ - 1) / Real.sqrt 2

noncomputable def criticalStripEquatorJetChart (σ : ℝ) (m : ℕ) (hm : 0 < m) :
    CriticalStripEquatorJetChart σ m where
  pos := hm
  jet_time := stripEquatorJetTime σ m
  jet_time_eq := rfl
  coeff_eq_equator := rapidity_jet_coeff_eq_strip_equator_factor σ hm
  coeff_eq_factor := rapidity_jet_coeff_eq_equator_factor σ hm

/-! ## Covariant consequence: equator factor × pure surrogate -/

/--
At vanishing HQVM metric jets, the Christoffel covariant divergence with
rapidity-normalized frozen jet equals **strip equator factor ×** the pure
metric surrogate — the physics-side content of "Δ correction drops at flat jet,
pure harmonic channel visible, scaled by equator readout."
-/
theorem flat_jet_covariant_div_eq_equator_times_surrogate
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (σ : ℝ) {m : ℕ} (hm : 0 < m)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    covariant_div_F_O_HQVM_Christoffel F
      (rapidityNormalized_frozenFirstIndexJet_raisedChannel F N aScale Φ b 1
        (stripEquatorJetTime σ m) m)
      N aScale Φ dN da dPhi b ν =
      stripSigmaFreeCoord σ *
        covariant_div_F_O F 1 (HQVM_inverseMetric N aScale Φ) b ν := by
  rw [covariant_div_F_O_HQVM_Christoffel_rapidity_flat_frozen_jet_eq_scaled_surrogate F N aScale Φ
      dN da dPhi b ν 1 (stripEquatorJetTime σ m) m hF hN ha hΦ,
    rapidity_jet_coeff_eq_strip_equator_factor σ hm]

theorem flat_jet_covariant_div_eq_equator_factor_times_surrogate
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (σ : ℝ) {m : ℕ} (hm : 0 < m)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    covariant_div_F_O_HQVM_Christoffel F
      (rapidityNormalized_frozenFirstIndexJet_raisedChannel F N aScale Φ b 1
        (stripEquatorJetTime σ m) m)
      N aScale Φ dN da dPhi b ν =
      ((2 * σ - 1) / Real.sqrt 2) *
        covariant_div_F_O F 1 (HQVM_inverseMetric N aScale Φ) b ν := by
  rw [flat_jet_covariant_div_eq_equator_times_surrogate F σ hm N aScale Φ dN da dPhi b ν hF hN ha hΦ,
    strip_sigma_free_coord_eq σ]

/-!
**Summary.**  `rapidityNormalizedJetCoeff` is not merely "like" the equator factor —
under `CriticalStripEquatorJetChart` it **is** `(2σ−1)/√2`.  Vanishing on the critical
line (`σ = 1/2`) is simultaneous for both readouts; off-line scaling feeds the covariant
surrogate exactly through `flat_jet_covariant_div_eq_equator_times_surrogate`.
-/

end

end Hqiv.Story
