import Hqiv.Physics.ModalFrequencyHorizon
import Hqiv.Physics.TrialityRapidityWellEquivalence
import Hqiv.Physics.ActionHolonomyGlue
import Hqiv.Geometry.S7MetahorizonCasimir
import Hqiv.Geometry.QuaternionMaxwellS3OMaxwellS4Spectral
import Mathlib.Algebra.Order.Field.Basic

namespace Hqiv.Physics

open Hqiv
open Hqiv.Algebra

/-!
# Cubic-phase quarter-period relaxation (exploratory, non-breaking)

This module adds a parallel pathway that treats quarter-period relaxation as the primary
dynamical variable while keeping the existing shell/readout and affine 1-jet path intact.

- `trialityCubicPhaseAngle` upgrades the `{-1,0,+1}` CP orientation to phase angles
  `0, ± 2π/3`.
- `s7ModeOmega` / `quarterRelaxationLoad` keep the original **`S⁷`** spectral weight (unchanged
  public behavior for existing callers).
- `QuarterSpectralBridge` selects **`S⁷`**, **`S³`** (quaternion / EM-sector phase sphere), or
  **`S⁴`** (one-step extension beyond the quaternion carrier) for the `log(√λ+1)` weight inside
  `quarterRelaxationLoadTagged`.
- `RelaxedQuarterModalSpec` wraps `ModalFrequencyHorizonSpec` with a readout-dependent
  relaxation load and exposes relaxed detuned-surface/geometric-step readouts.

Use `relaxedQuarterModalFromShellNominal` for the legacy `S⁷` bridge, and
`relaxedQuarterModalFromShellNominalS3` / `relaxedQuarterModalFromShellNominalS4` for the new
hypersphere splits (lepton/charge spin on `S³`, quark-sector extension on `S⁴`).

This file is intentionally exploratory and does not replace public definitions in
`FanoResonance`/`ModalFrequencyHorizon`.

**Scope note:** the cubic-phase factor is **triality-representation** data (`So8RepIndex`) times
spectral weight and `|rapidityCPBias m|`; it is **not** multiplied into **baryon number** (or any
`ConservedContentMassBridge` quantum-number slot) in this layer—only into the relaxed detuning readouts
built from `ModalFrequencyHorizonSpec`.
-/

/-- Which unit-sphere Laplace spectrum feeds the relaxation `log(ω+1)` weight. -/
inductive QuarterSpectralBridge where
  | s7
  | s3
  | s4
deriving DecidableEq, Repr

/-- Three-phase angle attached to a triality representation: `0, ±2π/3`. -/
noncomputable def trialityCubicPhaseAngle (rep : So8RepIndex) : ℝ :=
  (2 * Real.pi / 3) * trialityCpOrientation rep

/-- Cubic-phase amplitude used by the quarter-period relaxation load. -/
noncomputable def trialityCubicPhaseAmplitude (rep : So8RepIndex) : ℝ :=
  |Real.sin (trialityCubicPhaseAngle rep)|

theorem trialityCubicPhaseAmplitude_nonneg (rep : So8RepIndex) :
    0 ≤ trialityCubicPhaseAmplitude rep := by
  unfold trialityCubicPhaseAmplitude
  positivity

theorem trialityCubicPhaseAmplitude_rep8V :
    trialityCubicPhaseAmplitude rep8V = 0 := by
  simp [trialityCubicPhaseAmplitude, trialityCubicPhaseAngle, trialityCpOrientation_rep8V]

/-- Frequency-like `S⁷` modal scale from the scalar Laplace–Beltrami eigenvalue. -/
noncomputable def s7ModeOmega (ℓ : ℕ) : ℝ :=
  Real.sqrt (Hqiv.Geometry.laplaceBeltramiEigenvalueS7 ℓ + 1)

lemma s7ModeOmega_pos (ℓ : ℕ) : 0 < s7ModeOmega ℓ := by
  unfold s7ModeOmega Hqiv.Geometry.laplaceBeltramiEigenvalueS7
  have hnonneg : 0 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 6) := by positivity
  have hpos : 0 < (ℓ : ℝ) * ((ℓ : ℝ) + 6) + 1 := by linarith
  exact Real.sqrt_pos.2 hpos

/-- Frequency-like `S³` modal scale (quaternion / unit `ℍ` phase sphere). -/
noncomputable def s3ModeOmega (ℓ : ℕ) : ℝ :=
  Real.sqrt (Hqiv.Geometry.laplaceBeltramiEigenvalueS3 ℓ + 1)

lemma s3ModeOmega_pos (ℓ : ℕ) : 0 < s3ModeOmega ℓ := by
  unfold s3ModeOmega Hqiv.Geometry.laplaceBeltramiEigenvalueS3
  have hnonneg : 0 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 2) := by positivity
  have hpos : 0 < (ℓ : ℝ) * ((ℓ : ℝ) + 2) + 1 := by linarith
  exact Real.sqrt_pos.2 hpos

/-- Frequency-like `S⁴` modal scale (extension shell one dimension beyond `ℝ⁴ ≅ ℍ`). -/
noncomputable def s4ModeOmega (ℓ : ℕ) : ℝ :=
  Real.sqrt (Hqiv.Geometry.laplaceBeltramiEigenvalueS4 ℓ + 1)

lemma s4ModeOmega_pos (ℓ : ℕ) : 0 < s4ModeOmega ℓ := by
  unfold s4ModeOmega Hqiv.Geometry.laplaceBeltramiEigenvalueS4
  have hnonneg : 0 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 3) := by positivity
  have hpos : 0 < (ℓ : ℝ) * ((ℓ : ℝ) + 3) + 1 := by linarith
  exact Real.sqrt_pos.2 hpos

/-- Unified positive modal scale `√(λ_ℓ+1)` for the selected bridge. -/
noncomputable def spectralModeOmega (br : QuarterSpectralBridge) (ℓ : ℕ) : ℝ :=
  match br with
  | .s7 => s7ModeOmega ℓ
  | .s3 => s3ModeOmega ℓ
  | .s4 => s4ModeOmega ℓ

theorem spectralModeOmega_pos (br : QuarterSpectralBridge) (ℓ : ℕ) :
    0 < spectralModeOmega br ℓ := by
  cases br
  · simpa [spectralModeOmega] using s7ModeOmega_pos ℓ
  · simpa [spectralModeOmega] using s3ModeOmega_pos ℓ
  · simpa [spectralModeOmega] using s4ModeOmega_pos ℓ

/-- Quarter period sourced from the `S⁷` mode scale. -/
noncomputable def s7ModeQuarterPeriod (ℓ : ℕ) : ℝ :=
  deltaTQuarter (s7ModeOmega ℓ) (s7ModeOmega_pos ℓ)

theorem s7ModeOmega_mul_quarter_eq_horizonQuarter (ℓ : ℕ) :
    s7ModeOmega ℓ * s7ModeQuarterPeriod ℓ = Hqiv.horizonQuarterPeriod := by
  unfold s7ModeQuarterPeriod
  simpa using omega_deltaTQuarter_eq_horizonQuarterPeriod (s7ModeOmega ℓ) (s7ModeOmega_pos ℓ)

/--
`S⁷` mode weight used in the relaxation load.
`log(ω+1)` keeps the factor positive and slowly varying at large modal index.
-/
noncomputable def s7RelaxationWeight (ℓ : ℕ) : ℝ :=
  Real.log (s7ModeOmega ℓ + 1)

theorem s7RelaxationWeight_nonneg (ℓ : ℕ) : 0 ≤ s7RelaxationWeight ℓ := by
  unfold s7RelaxationWeight
  have hω : 0 < s7ModeOmega ℓ := s7ModeOmega_pos ℓ
  have h1 : (1 : ℝ) ≤ s7ModeOmega ℓ + 1 := by linarith
  exact Real.log_nonneg h1

noncomputable def s3RelaxationWeight (ℓ : ℕ) : ℝ :=
  Real.log (s3ModeOmega ℓ + 1)

theorem s3RelaxationWeight_nonneg (ℓ : ℕ) : 0 ≤ s3RelaxationWeight ℓ := by
  unfold s3RelaxationWeight
  have hω : 0 < s3ModeOmega ℓ := s3ModeOmega_pos ℓ
  have h1 : (1 : ℝ) ≤ s3ModeOmega ℓ + 1 := by linarith
  exact Real.log_nonneg h1

noncomputable def s4RelaxationWeight (ℓ : ℕ) : ℝ :=
  Real.log (s4ModeOmega ℓ + 1)

theorem s4RelaxationWeight_nonneg (ℓ : ℕ) : 0 ≤ s4RelaxationWeight ℓ := by
  unfold s4RelaxationWeight
  have hω : 0 < s4ModeOmega ℓ := s4ModeOmega_pos ℓ
  have h1 : (1 : ℝ) ≤ s4ModeOmega ℓ + 1 := by linarith
  exact Real.log_nonneg h1

noncomputable def spectralRelaxationWeight (br : QuarterSpectralBridge) (ℓ : ℕ) : ℝ :=
  match br with
  | .s7 => s7RelaxationWeight ℓ
  | .s3 => s3RelaxationWeight ℓ
  | .s4 => s4RelaxationWeight ℓ

theorem spectralRelaxationWeight_nonneg (br : QuarterSpectralBridge) (ℓ : ℕ) :
    0 ≤ spectralRelaxationWeight br ℓ := by
  cases br
  · simpa [spectralRelaxationWeight] using s7RelaxationWeight_nonneg ℓ
  · simpa [spectralRelaxationWeight] using s3RelaxationWeight_nonneg ℓ
  · simpa [spectralRelaxationWeight] using s4RelaxationWeight_nonneg ℓ

/--
Tagged quarter-period relaxation load:

- triality cubic-phase amplitude (`rep`),
- spectral `log(ω+1)` weight from `br` at degree `ℓ`,
- rapidity/curvature CP-bias magnitude at readout shell (`m`).
-/
noncomputable def quarterRelaxationLoadTagged (br : QuarterSpectralBridge) (rep : So8RepIndex)
    (ℓ m : ℕ) : ℝ :=
  trialityCubicPhaseAmplitude rep * spectralRelaxationWeight br ℓ * |rapidityCPBias m|

theorem quarterRelaxationLoadTagged_nonneg (br : QuarterSpectralBridge) (rep : So8RepIndex)
    (ℓ m : ℕ) : 0 ≤ quarterRelaxationLoadTagged br rep ℓ m := by
  unfold quarterRelaxationLoadTagged
  exact mul_nonneg (mul_nonneg (trialityCubicPhaseAmplitude_nonneg rep)
      (spectralRelaxationWeight_nonneg br ℓ)) (abs_nonneg _)

theorem quarterRelaxationLoadTagged_rep8V (br : QuarterSpectralBridge) (ℓ m : ℕ) :
    quarterRelaxationLoadTagged br rep8V ℓ m = 0 := by
  simp [quarterRelaxationLoadTagged, trialityCubicPhaseAmplitude_rep8V]

/--
Legacy `S⁷`-only load (defeq to `quarterRelaxationLoadTagged .s7`).
Quarter-period relaxation load:

- triality cubic-phase amplitude (`rep`),
- `S⁷` spectral weight (`ℓ`),
- rapidity/curvature CP-bias magnitude at readout shell (`m`).
-/
noncomputable def quarterRelaxationLoad (rep : So8RepIndex) (ℓ m : ℕ) : ℝ :=
  quarterRelaxationLoadTagged .s7 rep ℓ m

theorem quarterRelaxationLoad_nonneg (rep : So8RepIndex) (ℓ m : ℕ) :
    0 ≤ quarterRelaxationLoad rep ℓ m :=
  quarterRelaxationLoadTagged_nonneg .s7 rep ℓ m

theorem quarterRelaxationLoad_rep8V_zero (ℓ m : ℕ) :
    quarterRelaxationLoad rep8V ℓ m = 0 :=
  quarterRelaxationLoadTagged_rep8V .s7 ℓ m

/-- Multiplicative quarter-period relaxation factor (`≥ 1`). -/
noncomputable def quarterRelaxationFactor (rep : So8RepIndex) (ℓ m : ℕ) : ℝ :=
  1 + quarterRelaxationLoad rep ℓ m

theorem quarterRelaxationFactor_pos (rep : So8RepIndex) (ℓ m : ℕ) :
    0 < quarterRelaxationFactor rep ℓ m := by
  unfold quarterRelaxationFactor
  have h : 0 ≤ quarterRelaxationLoad rep ℓ m := quarterRelaxationLoad_nonneg rep ℓ m
  linarith

/-- If a quarter-period load is controlled by the cyclic Wilson defect budget with gain `κ`,
it is controlled by the O-Maxwell kinetic aggregate using the `ActionHolonomyGlue` bound. -/
theorem quarterRelaxationLoad_le_kinetic_control
    (κ : ℝ) (hκ : 0 ≤ κ)
    (A : Fin 8 → Fin 4 → ℝ) (x : ℝ) (rep : So8RepIndex) (ℓ m : ℕ)
    (hctrl :
      quarterRelaxationLoad rep ℓ m ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) :
    quarterRelaxationLoad rep ℓ m ≤ κ * ((-4 : ℝ) * L_O_kinetic A) := by
  rcases Hqiv.Physics.cyclic_wilson_defect_sum_bounds_from_kinetic A x with ⟨_, hbudget⟩
  refine le_trans hctrl ?_
  exact mul_le_mul_of_nonneg_left hbudget hκ

/-- Same control lifted to the multiplicative relaxation factor. -/
theorem quarterRelaxationFactor_le_kinetic_control
    (κ : ℝ) (hκ : 0 ≤ κ)
    (A : Fin 8 → Fin 4 → ℝ) (x : ℝ) (rep : So8RepIndex) (ℓ m : ℕ)
    (hctrl :
      quarterRelaxationLoad rep ℓ m ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) :
    quarterRelaxationFactor rep ℓ m ≤ 1 + κ * ((-4 : ℝ) * L_O_kinetic A) := by
  unfold quarterRelaxationFactor
  have hload := quarterRelaxationLoad_le_kinetic_control κ hκ A x rep ℓ m hctrl
  linarith

/-- Parallel modal wrapper with a readout-dependent quarter-period relaxation load. -/
structure RelaxedQuarterModalSpec where
  base : ModalFrequencyHorizonSpec
  rep : So8RepIndex
  /-- Spherical-harmonic degree for the Laplace `λ_ℓ` weight (same slot for `S⁷`/`S³`/`S⁴`). -/
  spectralModeIdx : ℕ
  spectralBridge : QuarterSpectralBridge
  relaxationLoad : ℕ → ℝ
  relaxationLoad_nonneg : ∀ m : ℕ, 0 ≤ relaxationLoad m

/-- Build a relaxed modal wrapper with an explicit hypersphere bridge. -/
noncomputable def RelaxedQuarterModalSpec.fromBaseTagged
    (base : ModalFrequencyHorizonSpec) (rep : So8RepIndex) (spectralModeIdx : ℕ)
    (br : QuarterSpectralBridge) : RelaxedQuarterModalSpec where
  base := base
  rep := rep
  spectralModeIdx := spectralModeIdx
  spectralBridge := br
  relaxationLoad := fun m => quarterRelaxationLoadTagged br rep spectralModeIdx m
  relaxationLoad_nonneg := fun m => quarterRelaxationLoadTagged_nonneg br rep spectralModeIdx m

/-- Backward-compatible constructor: `S⁷` bridge (previous `fromBase` / `s7Mode` naming). -/
noncomputable def RelaxedQuarterModalSpec.fromBase
    (base : ModalFrequencyHorizonSpec) (rep : So8RepIndex) (s7Mode : ℕ) : RelaxedQuarterModalSpec :=
  RelaxedQuarterModalSpec.fromBaseTagged base rep s7Mode .s7

/-- Convenience constructor from shell-nominal modal packaging (`S⁷` weight). -/
noncomputable def relaxedQuarterModalFromShellNominal
    (rep : So8RepIndex) (spectralModeIdx shell : ℕ) : RelaxedQuarterModalSpec :=
  RelaxedQuarterModalSpec.fromBaseTagged (modalFrequencyHorizonFromShellNominal shell) rep
    spectralModeIdx .s7

/-- Same as `relaxedQuarterModalFromShellNominal`, but with `S³` Laplace weight. -/
noncomputable def relaxedQuarterModalFromShellNominalS3
    (rep : So8RepIndex) (spectralModeIdx shell : ℕ) : RelaxedQuarterModalSpec :=
  RelaxedQuarterModalSpec.fromBaseTagged (modalFrequencyHorizonFromShellNominal shell) rep
    spectralModeIdx .s3

/-- Same as `relaxedQuarterModalFromShellNominal`, but with `S⁴` Laplace weight. -/
noncomputable def relaxedQuarterModalFromShellNominalS4
    (rep : So8RepIndex) (spectralModeIdx shell : ℕ) : RelaxedQuarterModalSpec :=
  RelaxedQuarterModalSpec.fromBaseTagged (modalFrequencyHorizonFromShellNominal shell) rep
    spectralModeIdx .s4

/-- Effective quarter period after relaxation load. -/
noncomputable def RelaxedQuarterModalSpec.effectiveQuarterPeriod
    (spec : RelaxedQuarterModalSpec) (m : ℕ) : ℝ :=
  spec.base.interactionQuarterPeriod / (1 + spec.relaxationLoad m)

/-- Effective modal frequency after relaxation load. -/
noncomputable def RelaxedQuarterModalSpec.effectiveOmega
    (spec : RelaxedQuarterModalSpec) (m : ℕ) : ℝ :=
  spec.base.nominalOmega * (1 + spec.relaxationLoad m)

/-- Product identity is preserved by the reciprocal relaxation pair. -/
theorem RelaxedQuarterModalSpec.effectiveOmega_mul_effectiveQuarterPeriod
    (spec : RelaxedQuarterModalSpec) (m : ℕ) :
    spec.effectiveOmega m * spec.effectiveQuarterPeriod m = Hqiv.horizonQuarterPeriod := by
  unfold RelaxedQuarterModalSpec.effectiveOmega RelaxedQuarterModalSpec.effectiveQuarterPeriod
  have hpos : 0 < 1 + spec.relaxationLoad m := by
    have hnonneg : 0 ≤ spec.relaxationLoad m := spec.relaxationLoad_nonneg m
    linarith
  field_simp [ne_of_gt hpos]
  simp [spec.base.quarterPhase_eq_horizonQuarter]

/-- Relaxed denominator candidate derived from base detuning and relaxation factor. -/
noncomputable def RelaxedQuarterModalSpec.relaxedDetuningReadout
    (spec : RelaxedQuarterModalSpec) (m : ℕ) : ℝ :=
  spec.base.detuning1Jet m * (1 + spec.relaxationLoad m)

/-- Relaxed detuned surface readout candidate. -/
noncomputable def RelaxedQuarterModalSpec.relaxedDetunedSurfaceReadout
    (spec : RelaxedQuarterModalSpec) (m : ℕ) : ℝ :=
  shellSurface m / spec.relaxedDetuningReadout m

/-- Relaxed geometric step readout candidate. -/
noncomputable def RelaxedQuarterModalSpec.relaxedGeometricStepReadout
    (spec : RelaxedQuarterModalSpec) (m_from m_to : ℕ) : ℝ :=
  spec.relaxedDetunedSurfaceReadout m_from / spec.relaxedDetunedSurfaceReadout m_to

theorem RelaxedQuarterModalSpec.relaxedGeometricStepReadout_eq_base_mul_loadRatio
    (spec : RelaxedQuarterModalSpec) (m_from m_to : ℕ)
    (hdet_from : spec.base.detuning1Jet m_from ≠ 0)
    (hdet_to : spec.base.detuning1Jet m_to ≠ 0) :
    spec.relaxedGeometricStepReadout m_from m_to =
      spec.base.geometricStepReadout m_from m_to *
        ((1 + spec.relaxationLoad m_to) / (1 + spec.relaxationLoad m_from)) := by
  unfold RelaxedQuarterModalSpec.relaxedGeometricStepReadout
    RelaxedQuarterModalSpec.relaxedDetunedSurfaceReadout
    RelaxedQuarterModalSpec.relaxedDetuningReadout
    ModalFrequencyHorizonSpec.geometricStepReadout
    ModalFrequencyHorizonSpec.detunedSurfaceReadout
  have hpos_from : 0 < 1 + spec.relaxationLoad m_from := by
    linarith [spec.relaxationLoad_nonneg m_from]
  have hpos_to : 0 < 1 + spec.relaxationLoad m_to := by
    linarith [spec.relaxationLoad_nonneg m_to]
  field_simp [hdet_from, hdet_to, ne_of_gt hpos_from, ne_of_gt hpos_to]

theorem RelaxedQuarterModalSpec.abs_relaxedGeometricStepReadout_le_base_scaled
    (spec : RelaxedQuarterModalSpec) (m_from m_to : ℕ)
    (hdet_from : spec.base.detuning1Jet m_from ≠ 0)
    (hdet_to : spec.base.detuning1Jet m_to ≠ 0) :
    |spec.relaxedGeometricStepReadout m_from m_to| ≤
      |spec.base.geometricStepReadout m_from m_to| * (1 + spec.relaxationLoad m_to) := by
  rw [spec.relaxedGeometricStepReadout_eq_base_mul_loadRatio m_from m_to hdet_from hdet_to]
  set ratio : ℝ := (1 + spec.relaxationLoad m_to) / (1 + spec.relaxationLoad m_from)
  have hratio_nonneg : 0 ≤ ratio := by
    have hnonneg_to : 0 ≤ 1 + spec.relaxationLoad m_to := by
      linarith [spec.relaxationLoad_nonneg m_to]
    have hpos_from : 0 < 1 + spec.relaxationLoad m_from := by
      linarith [spec.relaxationLoad_nonneg m_from]
    exact div_nonneg hnonneg_to (le_of_lt hpos_from)
  have hratio_le : ratio ≤ 1 + spec.relaxationLoad m_to := by
    have hpos_from : 0 < 1 + spec.relaxationLoad m_from := by
      linarith [spec.relaxationLoad_nonneg m_from]
    have hnum_nonneg : 0 ≤ 1 + spec.relaxationLoad m_to := by
      linarith [spec.relaxationLoad_nonneg m_to]
    have hmul : (1 + spec.relaxationLoad m_to) ≤
        (1 + spec.relaxationLoad m_to) * (1 + spec.relaxationLoad m_from) := by
      nlinarith [spec.relaxationLoad_nonneg m_from, hnum_nonneg]
    exact (div_le_iff₀ hpos_from).2 hmul
  calc
    |spec.base.geometricStepReadout m_from m_to * ratio|
        = |spec.base.geometricStepReadout m_from m_to| * ratio := by
            rw [abs_mul, abs_of_nonneg hratio_nonneg]
    _ ≤ |spec.base.geometricStepReadout m_from m_to| * (1 + spec.relaxationLoad m_to) :=
          mul_le_mul_of_nonneg_left hratio_le (abs_nonneg _)

theorem RelaxedQuarterModalSpec.abs_relaxedGeometricStepReadout_le_defect_control
    (spec : RelaxedQuarterModalSpec) (m_from m_to : ℕ)
    (hdet_from : spec.base.detuning1Jet m_from ≠ 0)
    (hdet_to : spec.base.detuning1Jet m_to ≠ 0)
    (κ : ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (x : ℝ)
    (hctrl :
      spec.relaxationLoad m_to ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) :
    |spec.relaxedGeometricStepReadout m_from m_to| ≤
      |spec.base.geometricStepReadout m_from m_to| *
        (1 + κ * (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) := by
  refine le_trans (spec.abs_relaxedGeometricStepReadout_le_base_scaled m_from m_to hdet_from hdet_to) ?_
  have hfac : 1 + spec.relaxationLoad m_to ≤
      1 + κ * (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2) := by
    linarith
  exact mul_le_mul_of_nonneg_left hfac (abs_nonneg _)

theorem RelaxedQuarterModalSpec.abs_relaxedGeometricStepReadout_le_kinetic_control
    (spec : RelaxedQuarterModalSpec) (m_from m_to : ℕ)
    (hdet_from : spec.base.detuning1Jet m_from ≠ 0)
    (hdet_to : spec.base.detuning1Jet m_to ≠ 0)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (A : Fin 8 → Fin 4 → ℝ) (x : ℝ)
    (hctrl :
      spec.relaxationLoad m_to ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) :
    |spec.relaxedGeometricStepReadout m_from m_to| ≤
      |spec.base.geometricStepReadout m_from m_to| *
        (1 + κ * ((-4 : ℝ) * L_O_kinetic A)) := by
  refine le_trans (spec.abs_relaxedGeometricStepReadout_le_defect_control
      m_from m_to hdet_from hdet_to κ A x hctrl) ?_
  rcases Hqiv.Physics.cyclic_wilson_defect_sum_bounds_from_kinetic A x with ⟨_, hbudget⟩
  have hfac :
      1 + κ * (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2) ≤
        1 + κ * ((-4 : ℝ) * L_O_kinetic A) := by
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_left hbudget hκ) 1
  exact mul_le_mul_of_nonneg_left hfac (abs_nonneg _)

theorem relaxedQuarterModalFromShellNominal_rep8V_relaxedDetuning_eq_base
    (br : QuarterSpectralBridge) (spectralModeIdx shell m : ℕ) :
    (RelaxedQuarterModalSpec.fromBaseTagged (modalFrequencyHorizonFromShellNominal shell) rep8V
          spectralModeIdx br).relaxedDetuningReadout m =
      rindlerDetuningShared (m : ℝ) := by
  unfold RelaxedQuarterModalSpec.fromBaseTagged RelaxedQuarterModalSpec.relaxedDetuningReadout
  simp [quarterRelaxationLoadTagged_rep8V, modalFrequencyHorizonFromShellNominal]

theorem relaxedQuarterModalFromShellNominal_rep8V_surface_eq_detunedShellSurface
    (br : QuarterSpectralBridge) (spectralModeIdx shell m : ℕ) :
    (RelaxedQuarterModalSpec.fromBaseTagged (modalFrequencyHorizonFromShellNominal shell) rep8V
          spectralModeIdx br).relaxedDetunedSurfaceReadout m =
      detunedShellSurface m := by
  unfold RelaxedQuarterModalSpec.relaxedDetunedSurfaceReadout detunedShellSurface
  rw [relaxedQuarterModalFromShellNominal_rep8V_relaxedDetuning_eq_base]

end Hqiv.Physics
