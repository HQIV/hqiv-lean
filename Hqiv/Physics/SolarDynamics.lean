import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.ActionHolonomyGlue
import Hqiv.Physics.CoronalLongitudinalStress
import Hqiv.Physics.WeakFanoHopfBridge
import Hqiv.Physics.G2AutomorphismEnergyCost
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Hqiv.Physics.CompactObjectRotatingCrustScaffold

/-!
# HQIV solar dynamics scaffold (flux tubes, cycle discharge, sunspot pins)

**Purpose:** extend the coronal longitudinal O-Maxwell spine to the solar case:
metallic-carrier flux tubes, field-aligned currents, holonomy-discharge cycle
bookkeeping, and localized sunspot pin witnesses.

This module **does not** derive a stellar-atmosphere `φ(s)` profile from horizon
shells, nor does it prove that the Sun's observed ~11-year cycle follows from
first principles. It fixes the algebraic identities and witness bundles that
Python readout scripts consume.

## Proof status (all `Prop`, zero `sorry`)

* **§1.** Solar flux-tube shell pair and effective axial field aliases.
* **§2.** Boundary heating flux and shell-gap dependence (delegates to coronal spine).
* **§3.** Rotation/shear gate for differential-rotation coupling.
* **§4.** Holonomy-discharge cycle phase and threshold bookkeeping.
* **§5.** Sunspot pin activation witness (below threshold ⇒ inactive channel).
* **§6.** End-to-end solar flux-tube heating witness bundle.
* **§7.** Galactic outside-curvature / WHIM boundary gate and planetary magnetic
  coupling slots for environment-dressed cycle readout.

**Not claimed:** full MHD dynamo PDE, photosphere→corona shell assignment from
first principles, observed 11-year period match, or plasma opacity theory.
The §7 environment gates name **algebraic** modulators for Python readout; they
do not prove Jupiter drives the solar cycle.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-!
## §1. Solar flux-tube shell pair and effective axial field
-/

/-- Photosphere/corona shell pair for a solar magnetic flux tube. -/
abbrev SolarFluxTubeShells := CoronalColumnShells

/-- φ jump across a solar flux tube from the discrete shell ladder. -/
def solarPhiJump (cols : SolarFluxTubeShells) : ℝ :=
  coronalPhiJump cols

theorem solarPhiJump_closed_form (cols : SolarFluxTubeShells) :
    solarPhiJump cols =
      2 * ((cols.m_corona : ℝ) - (cols.m_photo : ℝ)) := by
  unfold solarPhiJump
  exact coronalPhiJump_closed_form cols

theorem solarPhiJump_nonneg (cols : SolarFluxTubeShells) :
    0 ≤ solarPhiJump cols := coronalPhiJump_nonneg cols

/-- Effective axial field along a solar flux tube: Ohmic + HQIV channels. -/
def solarEffectiveAxialField (J sigma Estar couplingLog dphi_ds : ℝ) : ℝ :=
  coronalEffectiveAxialField J sigma Estar couplingLog dphi_ds

theorem solarEffectiveAxialField_classical_limit
    (J sigma Estar couplingLog : ℝ) :
    solarEffectiveAxialField J sigma Estar couplingLog 0 = ohmicAxialField J sigma := by
  unfold solarEffectiveAxialField
  exact coronalEffectiveAxialField_classical_limit J sigma Estar couplingLog

theorem solarEffectiveAxialField_eq_ohmic_plus_hqiv
    (J sigma Estar couplingLog dphi_ds : ℝ) :
    solarEffectiveAxialField J sigma Estar couplingLog dphi_ds =
      ohmicAxialField J sigma +
        coronalLongitudinalHQIVField Estar couplingLog dphi_ds := by
  unfold solarEffectiveAxialField coronalEffectiveAxialField
  ring

/-- Axial force density on a solar flux tube. -/
def solarLongitudinalForceDensity (nq J sigma Estar couplingLog dphi_ds : ℝ) : ℝ :=
  coronalLongitudinalForceDensity nq J sigma Estar couplingLog dphi_ds

/-!
## §2. Boundary heating flux and shell-gap dependence
-/

/-- Integrated boundary heating flux for a solar flux tube (shell-ladder form). -/
def solarFluxTubeHeatingBoundaryShells
    (nq Estar couplingLog v_parallel : ℝ) (cols : SolarFluxTubeShells) : ℝ :=
  coronalHeatingFluxBoundaryShells nq Estar couplingLog v_parallel cols

theorem solarFluxTubeHeatingBoundaryShells_eq_two_shellGap
    (nq Estar couplingLog v_parallel : ℝ) (cols : SolarFluxTubeShells) :
    solarFluxTubeHeatingBoundaryShells nq Estar couplingLog v_parallel cols =
      nq * v_parallel * Estar * (3 / (20 * Real.pi)) * couplingLog *
        (2 * ((cols.m_corona : ℝ) - (cols.m_photo : ℝ))) := by
  unfold solarFluxTubeHeatingBoundaryShells
  exact coronalHeatingFluxBoundaryShells_eq_two_shellGap nq Estar couplingLog v_parallel cols

theorem solarFluxTubeHeatingBoundaryShells_zero_of_equal_shells
    (nq Estar couplingLog v_parallel : ℝ) (m : ℕ) :
    solarFluxTubeHeatingBoundaryShells nq Estar couplingLog v_parallel
        ⟨m, m, le_refl m⟩ = 0 := by
  unfold solarFluxTubeHeatingBoundaryShells
  rw [coronalHeatingFluxBoundaryShells_eq]
  rw [coronalPhiJump_zero_of_equal_shells]
  ring

/-!
## §3. Rotation / shear gate (differential rotation coupling)
-/

/-- Mid-latitude shear gate ``sin²θ |cosθ|`` for active-region belts. -/
def solarShearGate (sinColatitude : ℝ) : ℝ :=
  sinColatitude ^ 2 * abs sinColatitude

theorem solarShearGate_nonneg (sinColatitude : ℝ) :
    0 ≤ solarShearGate sinColatitude := by
  unfold solarShearGate
  positivity

theorem solarShearGate_zero_at_pole :
    solarShearGate 0 = 0 := by
  unfold solarShearGate
  simp

/-- Heliographic active-belt latitude ``90° − arccos(γ)`` (compact-object monogamy witness). -/
def solarActiveBeltMonogamyLatitudeRad : ℝ :=
  Real.pi / 2 - Real.arccos gamma_HQIV

/-- Heliographic active-belt latitude ``arcsin(√(γ/2))`` (Rindler-half witness). -/
def solarActiveBeltRindlerHalfLatitudeRad : ℝ :=
  Real.arcsin (Real.sqrt (gamma_HQIV / 2))

/-- Rotation-modulated current gate: shell gap × shear gate × phase-lift shape. -/
def solarRotationCurrentGate (cols : SolarFluxTubeShells) (sinColatitude : ℝ) : ℝ :=
  solarPhiJump cols * solarShearGate sinColatitude *
    phaseLiftShapeAtShell cols.m_corona

theorem solarRotationCurrentGate_zero_at_pole (cols : SolarFluxTubeShells) :
    solarRotationCurrentGate cols 0 = 0 := by
  unfold solarRotationCurrentGate solarShearGate
  ring

theorem solarRotationCurrentGate_zero_of_equal_shells (m : ℕ) (sinColatitude : ℝ) :
    solarRotationCurrentGate ⟨m, m, le_refl m⟩ sinColatitude = 0 := by
  unfold solarRotationCurrentGate solarPhiJump
  rw [coronalPhiJump_zero_of_equal_shells]
  ring

/-!
## §4. Holonomy-discharge cycle phase and threshold bookkeeping
-/

/-- Dimensionless cycle phase from shell gap, Hopf winding, and phase-lift shape.

`phase = Δφ · hopfShape(w) · phaseLift(m_cor)`.

The **period** is not fixed here; downstream readout supplies rotation rate. -/
def solarCyclePhase (cols : SolarFluxTubeShells) (hopfWinding : ℕ) : ℝ :=
  solarPhiJump cols * hopfFibrationShape hopfWinding *
    phaseLiftShapeAtShell cols.m_corona

theorem solarCyclePhase_zero_of_equal_shells (m : ℕ) (w : ℕ) :
    solarCyclePhase ⟨m, m, le_refl m⟩ w = 0 := by
  unfold solarCyclePhase solarPhiJump
  rw [coronalPhiJump_zero_of_equal_shells]
  ring

theorem solarCyclePhase_nonneg_of_nonneg_jump
    (cols : SolarFluxTubeShells) (w : ℕ)
    (h : 0 ≤ solarPhiJump cols) :
    0 ≤ solarCyclePhase cols w := by
  unfold solarCyclePhase
  have hhopf : 0 ≤ hopfFibrationShape w := by
    unfold hopfFibrationShape
    positivity
  have hphase : 0 ≤ phaseLiftShapeAtShell cols.m_corona := by
    unfold phaseLiftShapeAtShell
    exact le_of_lt (div_pos (automorphismEnergyCostAtShell_pos cols.m_corona)
      (automorphismEnergyCostAtShell_pos referenceM))
  exact mul_nonneg (mul_nonneg h hhopf) hphase

/-- Cycle discharge threshold: phase must exceed this for a polarity reversal event. -/
def solarCycleDischargeThreshold (threshold : ℝ) : ℝ := threshold

/-- Pin / reversal is active when accumulated phase exceeds the threshold. -/
def solarCycleDischargeActive (phase threshold : ℝ) : Prop :=
  threshold < phase

theorem solarCycleDischargeActive_false_of_le
    (phase threshold : ℝ) (h : phase ≤ threshold) :
    ¬ solarCycleDischargeActive phase threshold := by
  unfold solarCycleDischargeActive
  exact not_lt.mpr h

theorem solarCycleDischargeActive_mono_threshold
    {phase t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    solarCycleDischargeActive phase t₂ → solarCycleDischargeActive phase t₁ := by
  unfold solarCycleDischargeActive
  intro hact
  exact lt_of_le_of_lt h hact

/-- Witness packaging the cycle phase equality for Python readout. -/
structure SolarCycleDischargeWitness
    (cols : SolarFluxTubeShells) (hopfWinding : ℕ) (phase threshold : ℝ) : Prop where
  phase_eq : phase = solarCyclePhase cols hopfWinding
  threshold_eq : threshold = solarCycleDischargeThreshold threshold

theorem SolarCycleDischargeWitness.discharge_active_iff
    {cols : SolarFluxTubeShells} {w : ℕ} {phase threshold : ℝ}
    (h : SolarCycleDischargeWitness cols w phase threshold) :
    solarCycleDischargeActive phase threshold ↔ threshold < solarCyclePhase cols w := by
  rw [h.phase_eq, h.threshold_eq, solarCycleDischargeThreshold]
  rfl

/-!
## §5. Sunspot pin activation witness
-/

/-- Localized pin stress/heating contribution when the gate exceeds threshold. -/
def sunspotPinStress (gate threshold Estar couplingLog v_parallel nq : ℝ) : ℝ :=
  if threshold < gate then
    nq * v_parallel * Estar * (3 / (20 * Real.pi)) * couplingLog * gate
  else 0

theorem sunspotPinStress_zero_below_threshold
    (gate threshold Estar couplingLog v_parallel nq : ℝ)
    (h : gate ≤ threshold) :
    sunspotPinStress gate threshold Estar couplingLog v_parallel nq = 0 := by
  unfold sunspotPinStress
  simp [not_lt.mpr h]

theorem sunspotPinStress_eq_boundary_form_above_threshold
    (gate threshold Estar couplingLog v_parallel nq : ℝ)
    (h : threshold < gate) :
    sunspotPinStress gate threshold Estar couplingLog v_parallel nq =
      nq * v_parallel * Estar * (3 / (20 * Real.pi)) * couplingLog * gate := by
  unfold sunspotPinStress
  simp [h]

theorem sunspotPinStress_nonneg
    {gate threshold Estar couplingLog v_parallel nq : ℝ}
    (hnq : 0 ≤ nq) (hv : 0 ≤ v_parallel) (hE : 0 ≤ Estar)
    (hΛ : 0 ≤ couplingLog) (hgate : 0 ≤ gate) :
    0 ≤ sunspotPinStress gate threshold Estar couplingLog v_parallel nq := by
  unfold sunspotPinStress
  split_ifs with hlt
  · have hcoef : (0 : ℝ) ≤ 3 / (20 * Real.pi) := by positivity
    have h1 : 0 ≤ nq * v_parallel := mul_nonneg hnq hv
    have h2 : 0 ≤ nq * v_parallel * Estar := mul_nonneg h1 hE
    have h3 : 0 ≤ nq * v_parallel * Estar * (3 / (20 * Real.pi)) := mul_nonneg h2 hcoef
    have h4 : 0 ≤ nq * v_parallel * Estar * (3 / (20 * Real.pi)) * couplingLog :=
      mul_nonneg h3 hΛ
    exact mul_nonneg h4 hgate
  · norm_num

/-- Witness: sunspot pin channel records gate vs threshold and resulting stress. -/
structure SunspotPinWitness
    (gate threshold pinStress Estar couplingLog v_parallel nq : ℝ) : Prop where
  pinStress_eq :
    pinStress = sunspotPinStress gate threshold Estar couplingLog v_parallel nq

theorem SunspotPinWitness.pin_inactive_of_gate_le_threshold
    {gate threshold pinStress Estar couplingLog v_parallel nq : ℝ}
    (h : SunspotPinWitness gate threshold pinStress Estar couplingLog v_parallel nq)
    (hle : gate ≤ threshold) :
    pinStress = 0 := by
  rw [h.pinStress_eq, sunspotPinStress_zero_below_threshold gate threshold Estar couplingLog v_parallel nq hle]

/-!
## §6. End-to-end solar flux-tube heating witness
-/

/-- Full witness for a solar flux-tube heating readout row. -/
structure SolarFluxTubeHeatingWitness
    (nq J sigma Estar couplingLog dphi_ds v_parallel qDot : ℝ) : Prop where
  qDot_eq :
    qDot = coronalHeatingRateDensity nq J sigma Estar couplingLog dphi_ds v_parallel

theorem SolarFluxTubeHeatingWitness.qDot_classical_flat_limit
    {nq J sigma Estar couplingLog v_parallel qDot : ℝ}
    (h : SolarFluxTubeHeatingWitness nq J sigma Estar couplingLog 0 v_parallel qDot) :
    qDot = nq * (J / sigma) * v_parallel := by
  rw [h.qDot_eq, coronalHeatingRateDensity_classical_flat_limit]

/-- Boundary heating witness using shell-ladder φ jump. -/
structure SolarFluxTubeBoundaryWitness
    (nq Estar couplingLog v_parallel : ℝ) (cols : SolarFluxTubeShells) (flux : ℝ) : Prop where
  flux_eq :
    flux = solarFluxTubeHeatingBoundaryShells nq Estar couplingLog v_parallel cols

theorem SolarFluxTubeBoundaryWitness.flux_eq_two_shellGap
    {nq Estar couplingLog v_parallel : ℝ} {cols : SolarFluxTubeShells} {flux : ℝ}
    (h : SolarFluxTubeBoundaryWitness nq Estar couplingLog v_parallel cols flux) :
    flux =
      nq * v_parallel * Estar * (3 / (20 * Real.pi)) * couplingLog *
        (2 * ((cols.m_corona : ℝ) - (cols.m_photo : ℝ))) := by
  rw [h.flux_eq, solarFluxTubeHeatingBoundaryShells_eq_two_shellGap nq Estar couplingLog v_parallel cols]

/-!
## §7. Galactic outside-curvature / WHIM and planetary magnetic coupling
-/

/-- Galactic outside-curvature modulator from weak-field ``ε_gal`` (delegates to
`outsideGravityGeffModulator` in `NuclearOutsideTemperatureDynamics`). -/
def solarGalacticCurvatureModulator (phiEpsilon : ℝ) : ℝ :=
  outsideGravityGeffModulator ⟨phiEpsilon⟩

theorem solarGalacticCurvatureModulator_one_of_nonpos (phiEpsilon : ℝ)
    (h : phiEpsilon ≤ 0) :
    solarGalacticCurvatureModulator phiEpsilon = 1 := by
  unfold solarGalacticCurvatureModulator outsideGravityGeffModulator
  simp [h]

/-- WHIM filament boundary shape: ``Δφ / φ(m_ism)`` for ISM/WHIM shell pair. -/
def solarWhimBoundaryShape (mIsm mWhim : ℕ) : ℝ :=
  max 0 (2 * ((mWhim : ℝ) - (mIsm : ℝ))) / phi_of_shell mIsm

theorem solarWhimBoundaryShape_nonneg (mIsm mWhim : ℕ) :
    0 ≤ solarWhimBoundaryShape mIsm mWhim := by
  unfold solarWhimBoundaryShape
  apply div_nonneg
  · positivity
  · exact le_of_lt (phi_of_shell_pos mIsm)

/-- Planetary magnetic coupling slot: ``γ · μ_ratio · sin²(alignment)``.

`μ_ratio` is a dimensionless dipole-strength witness supplied by readout (not fitted
inside this module). `alignmentSin` is the sine of the angle between the planetary
magnetic axis and the solar spin axis. -/
def solarPlanetaryMagneticCoupling (dipoleRatio alignmentSin : ℝ) : ℝ :=
  gamma_HQIV * max dipoleRatio 0 * alignmentSin ^ 2

theorem solarPlanetaryMagneticCoupling_nonneg (dipoleRatio alignmentSin : ℝ) :
    0 ≤ solarPlanetaryMagneticCoupling dipoleRatio alignmentSin := by
  unfold solarPlanetaryMagneticCoupling
  rw [gamma_eq_2_5]
  positivity

theorem solarPlanetaryMagneticCoupling_zero_of_zero_alignment
    (dipoleRatio : ℝ) :
    solarPlanetaryMagneticCoupling dipoleRatio 0 = 0 := by
  unfold solarPlanetaryMagneticCoupling
  simp

/-- Environment-dressed cycle phase: interior holonomy phase × galactic modulator ×
planetary coupling envelope ``(1 + coupling)``. -/
def solarCycleEnvironmentPhase
    (cols : SolarFluxTubeShells) (hopfWinding : ℕ)
    (phiGalactic dipoleRatio alignmentSin : ℝ) : ℝ :=
  solarCyclePhase cols hopfWinding *
    solarGalacticCurvatureModulator phiGalactic *
    (1 + solarPlanetaryMagneticCoupling dipoleRatio alignmentSin)

/-- Witness for environment-dressed cycle phase (Python readout). -/
structure SolarCycleEnvironmentWitness
    (cols : SolarFluxTubeShells) (hopfWinding : ℕ)
    (phiGalactic dipoleRatio alignmentSin phaseEnv : ℝ) : Prop where
  phase_env_eq :
    phaseEnv =
      solarCycleEnvironmentPhase cols hopfWinding phiGalactic dipoleRatio alignmentSin

end

end Hqiv.Physics
