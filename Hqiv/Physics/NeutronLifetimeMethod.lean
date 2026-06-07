import Hqiv.Physics.DynamicIsotopeStability
import Hqiv.Physics.WeakFanoHopfBridge
import Hqiv.Algebra.PhaseLiftDelta
import Mathlib.Algebra.Order.Field.Basic

open Hqiv.Algebra

/-!
# Neutron lifetime measurement methods (bottle vs beam)

Formalizes the bottle/beam ledger:

* both methods read **Ledger III** (weak β width), not Ledger I (strong overlap);
* **UCN trap magnetic field** is the primary bottle dressing slot: `B` maps to a
  dimensionless **curvature fraction** on the weak Fano/Hopf bridge (not Zeeman energy);
* lab **temperature** is a sub-leading outside-support witness (~10³ ppm), insufficient
  alone for the ~1.2×10⁴ ppm split;
* directional expectation `τ_beam > τ_bottle` follows once trap magnetic width dressing
  exceeds the beam (near-zero `B`) dressing.

Python witness export: `neutron_method_environment_ledger` in
`scripts/hqiv_isotope_pdg_benchmark.py`.
-/

namespace Hqiv.Physics

noncomputable section

/-! ## Measurement setup -/

/-- Laboratory neutron lifetime measurement class. -/
inductive NeutronLifetimeMethod
  | bottle
  | beam
  deriving DecidableEq

/-- Method-specific environment. Temperature is metadata; trap `B` is the bottle lever. -/
structure NeutronMethodSetup where
  method : NeutronLifetimeMethod
  labTemperatureK : ℝ
  trapMagneticFieldTesla : ℝ
  hT : 0 < labTemperatureK
  hB : 0 ≤ trapMagneticFieldTesla

def bottleMethodSetup : NeutronMethodSetup where
  method := .bottle
  labTemperatureK := 4
  trapMagneticFieldTesla := 2.5
  hT := by norm_num
  hB := by norm_num

def beamMethodSetup : NeutronMethodSetup where
  method := .beam
  labTemperatureK := 300
  trapMagneticFieldTesla := 0
  hT := by norm_num
  hB := by norm_num

def trapEmbeddingActive (s : NeutronMethodSetup) : Prop :=
  s.method = .bottle

def freeBranchTransportActive (s : NeutronMethodSetup) : Prop :=
  s.method = .beam

theorem bottleMethod_trapEmbedding : trapEmbeddingActive bottleMethodSetup := rfl

theorem beamMethod_freeBranchTransport : freeBranchTransportActive beamMethodSetup := rfl

/-! ## UCN trap magnetic field as curvature on the weak bridge -/

/-- Structural unit for a superconducting UCN storage field (tesla); not fitted to τ. -/
def ucnTrapReferenceFieldTesla : ℝ := 1

/-- Magnetic field strength → dimensionless curvature fraction on the trap (`∈ [0,1]`). -/
def trapMagneticCurvatureFraction (B : ℝ) : ℝ :=
  max 0 (min 1 (B / ucnTrapReferenceFieldTesla))

theorem trapMagneticCurvatureFraction_nonneg (B : ℝ) :
    0 ≤ trapMagneticCurvatureFraction B := by
  unfold trapMagneticCurvatureFraction
  positivity

theorem trapMagneticCurvatureFraction_le_one (B : ℝ) :
    trapMagneticCurvatureFraction B ≤ 1 := by
  unfold trapMagneticCurvatureFraction
  apply max_le (by positivity)
  exact min_le_left _ _

/--
Weak width dressing from trap `B` through the default β Fano/Hopf bridge shape.

`Γ_eff = f(B) · Γ₀` with `f = 1 + γ · ρ_mag(B) · weakBridgeShape`.
This is **curvature on the weak bridge**, distinct from the neV Zeeman slot.
-/
noncomputable def trapWeakWidthFactorFromMagnetic (B : ℝ) : ℝ :=
  1 + gamma_HQIV * trapMagneticCurvatureFraction B * weakBridgeShape defaultBetaWeakBridge

theorem trapWeakWidthFactorFromMagnetic_eq (B : ℝ) :
    trapWeakWidthFactorFromMagnetic B =
      1 + gamma_HQIV * trapMagneticCurvatureFraction B * weakBridgeShape defaultBetaWeakBridge := rfl

theorem defaultBetaWeakBridge_shape_eq_one_div_eighteen :
    weakBridgeShape defaultBetaWeakBridge = (1 : ℝ) / 18 := by
  have hphase : phaseLiftShapeAtShell referenceM = 1 := by
    unfold phaseLiftShapeAtShell
    rw [div_self (automorphismEnergyCostAtShell_pos referenceM).ne']
  unfold weakBridgeShape defaultBetaWeakBridge fanoRotationShape hopfFibrationShape
    fanoVertexDistance
  simp only [hphase]
  norm_num

theorem trapWeakWidthFactorFromMagnetic_pos (B : ℝ) :
    0 < trapWeakWidthFactorFromMagnetic B := by
  unfold trapWeakWidthFactorFromMagnetic
  have hterm : 0 ≤ gamma_HQIV * trapMagneticCurvatureFraction B * weakBridgeShape defaultBetaWeakBridge := by
    rw [defaultBetaWeakBridge_shape_eq_one_div_eighteen]
    have hγ : 0 ≤ gamma_HQIV := by rw [gamma_eq_2_5]; norm_num
    exact mul_nonneg (mul_nonneg hγ (trapMagneticCurvatureFraction_nonneg B)) (by norm_num)
  linarith

theorem bottle_trap_magnetic_curvature_saturated :
    trapMagneticCurvatureFraction bottleMethodSetup.trapMagneticFieldTesla = 1 := by
  unfold trapMagneticCurvatureFraction ucnTrapReferenceFieldTesla bottleMethodSetup
  norm_num

theorem beam_trap_magnetic_curvature_zero :
    trapMagneticCurvatureFraction beamMethodSetup.trapMagneticFieldTesla = 0 := by
  unfold trapMagneticCurvatureFraction beamMethodSetup
  norm_num

theorem bottle_trap_widthFactor_gt_beam :
    trapWeakWidthFactorFromMagnetic beamMethodSetup.trapMagneticFieldTesla <
      trapWeakWidthFactorFromMagnetic bottleMethodSetup.trapMagneticFieldTesla := by
  have hbeam := beam_trap_magnetic_curvature_zero
  have hbottle := bottle_trap_magnetic_curvature_saturated
  unfold trapWeakWidthFactorFromMagnetic
  rw [hbeam, hbottle, defaultBetaWeakBridge_shape_eq_one_div_eighteen, gamma_eq_2_5]
  norm_num

/-! ## Representative comparison references (not fitted inputs) -/

def neutronLifetimeBottleRefSeconds : ℝ := 877.75
def neutronLifetimeBeamRefSeconds : ℝ := 888.0

def bottleBeamSplitFraction : ℝ :=
  neutronLifetimeBeamRefSeconds / neutronLifetimeBottleRefSeconds - 1

def bottleBeamSplitPpmWitness : ℝ := bottleBeamSplitFraction * 1e6

/-- Temperature-only outside-support ppm (4 K vs 300 K class); sub-leading control. -/
def temperatureOnlyBottleBeamPpmWitness : ℝ := 1341

theorem bottleBeamSplitFraction_pos : 0 < bottleBeamSplitFraction := by
  unfold bottleBeamSplitFraction neutronLifetimeBeamRefSeconds neutronLifetimeBottleRefSeconds
  norm_num

theorem temperature_ppm_insufficient_for_bottle_beam_split :
    temperatureOnlyBottleBeamPpmWitness < bottleBeamSplitPpmWitness := by
  unfold temperatureOnlyBottleBeamPpmWitness bottleBeamSplitPpmWitness bottleBeamSplitFraction
    neutronLifetimeBeamRefSeconds neutronLifetimeBottleRefSeconds
  norm_num

/-! ## Width dressing and directional expectation -/

/-- Multiplicative factor on the central weak width slot (`Γ_eff = f · Γ₀`). -/
structure NeutronMethodWidthDressing where
  weakWidthFactor : ℝ
  hPos : 0 < weakWidthFactor

def bottleWidthDressingExceedsBeam
    (bottle beam : NeutronMethodWidthDressing) : Prop :=
  beam.weakWidthFactor < bottle.weakWidthFactor

noncomputable def apparentHalfLifeFromCentral (τ₀ f : ℝ) : ℝ :=
  τ₀ / f

theorem apparentHalfLife_lt_central_of_widthFactor_gt_one
    (τ₀ f : ℝ) (hτ : 0 < τ₀) (hf : 1 < f) :
    apparentHalfLifeFromCentral τ₀ f < τ₀ := by
  unfold apparentHalfLifeFromCentral
  exact div_lt_self hτ hf

theorem beam_apparent_tau_gt_bottle_apparent_tau
    (τ₀ : ℝ) (hτ : 0 < τ₀)
    (bottle beam : NeutronMethodWidthDressing)
    (hDress : bottleWidthDressingExceedsBeam bottle beam) :
    apparentHalfLifeFromCentral τ₀ bottle.weakWidthFactor <
      apparentHalfLifeFromCentral τ₀ beam.weakWidthFactor := by
  simpa [apparentHalfLifeFromCentral, one_div] using
    mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt beam.hPos hDress) hτ

theorem beam_tau_gt_bottle_from_magnetic_trap_dressing
    (τ₀ : ℝ) (hτ : 0 < τ₀) :
    apparentHalfLifeFromCentral τ₀ (trapWeakWidthFactorFromMagnetic bottleMethodSetup.trapMagneticFieldTesla) <
      apparentHalfLifeFromCentral τ₀ (trapWeakWidthFactorFromMagnetic beamMethodSetup.trapMagneticFieldTesla) := by
  unfold apparentHalfLifeFromCentral
  simpa [one_div] using
    mul_lt_mul_of_pos_left
      (one_div_lt_one_div_of_lt (trapWeakWidthFactorFromMagnetic_pos _) bottle_trap_widthFactor_gt_beam)
      hτ

/--
Saturated magnetic-bottle width factor for the representative UCN trap class.
This is a method envelope, not a fit to the bottle/beam central values.
-/
theorem bottle_trap_widthFactor_eq_fortysix_over_fortyfive :
    trapWeakWidthFactorFromMagnetic bottleMethodSetup.trapMagneticFieldTesla =
      (46 : ℝ) / 45 := by
  unfold trapWeakWidthFactorFromMagnetic
  rw [bottle_trap_magnetic_curvature_saturated,
    defaultBetaWeakBridge_shape_eq_one_div_eighteen, gamma_eq_2_5]
  norm_num

theorem beam_trap_widthFactor_eq_one :
    trapWeakWidthFactorFromMagnetic beamMethodSetup.trapMagneticFieldTesla = 1 := by
  unfold trapWeakWidthFactorFromMagnetic
  rw [beam_trap_magnetic_curvature_zero]
  norm_num

/-- Predicted beam-over-bottle lifetime ratio from saturated trap curvature. -/
noncomputable def saturatedBeamOverBottleLifetimeRatio : ℝ :=
  trapWeakWidthFactorFromMagnetic bottleMethodSetup.trapMagneticFieldTesla /
    trapWeakWidthFactorFromMagnetic beamMethodSetup.trapMagneticFieldTesla

theorem saturatedBeamOverBottleLifetimeRatio_eq_fortysix_over_fortyfive :
    saturatedBeamOverBottleLifetimeRatio = (46 : ℝ) / 45 := by
  unfold saturatedBeamOverBottleLifetimeRatio
  rw [bottle_trap_widthFactor_eq_fortysix_over_fortyfive, beam_trap_widthFactor_eq_one]
  norm_num

theorem bottleBeamSplitFraction_below_saturated_trap_envelope :
    bottleBeamSplitFraction < saturatedBeamOverBottleLifetimeRatio - 1 := by
  unfold bottleBeamSplitFraction saturatedBeamOverBottleLifetimeRatio
    neutronLifetimeBeamRefSeconds neutronLifetimeBottleRefSeconds
  rw [bottle_trap_widthFactor_eq_fortysix_over_fortyfive, beam_trap_widthFactor_eq_one]
  norm_num

/--
Generic β half-life method readout: local width dressing shortens apparent lifetime,
outside support lengthens it.  This is the isotope-facility hook used for
28Al/71Ge-style method comparisons.
-/
noncomputable def apparentBetaHalfLifeFromMethod
    (τ₀ localWidthFactor outsideSupportFactor : ℝ) : ℝ :=
  τ₀ * outsideSupportFactor / localWidthFactor

theorem apparentBetaHalfLifeFromMethod_eq
    (τ₀ localWidthFactor outsideSupportFactor : ℝ) :
    apparentBetaHalfLifeFromMethod τ₀ localWidthFactor outsideSupportFactor =
      τ₀ * outsideSupportFactor / localWidthFactor := rfl

/-! ## Ledger separation (spin-statistics / strong vs weak) -/

/-- Which width slot a neutron lifetime readout uses. -/
inductive NeutronDecayWidthLedger
  | strongOverlap (omegaReadout : ℝ)
  | weakBeta (m_e ℳ : ℝ)

noncomputable def widthFromLedger : NeutronDecayWidthLedger → ℝ
  | .strongOverlap ω => freeNeutronStrongDecayWidth ω
  | .weakBeta m_e ℳ => betaWeakWidthSlot .betaMinus m_e ℳ

theorem widthFromLedger_strongOverlap (ω : ℝ) :
    widthFromLedger (.strongOverlap ω) = freeNeutronStrongDecayWidth ω := rfl

theorem widthFromLedger_weakBeta (m_e ℳ : ℝ) :
    widthFromLedger (.weakBeta m_e ℳ) = betaWeakWidthSlot .betaMinus m_e ℳ := rfl

theorem strongOverlap_ledger_ne_weakBeta_ledger (ω m_e ℳ : ℝ) :
    NeutronDecayWidthLedger.strongOverlap ω ≠ NeutronDecayWidthLedger.weakBeta m_e ℳ := by
  intro h
  cases h

def bottleAndBeamShareWeakLedger (m_e ℳ : ℝ) : NeutronDecayWidthLedger :=
  .weakBeta m_e ℳ

/-! ## Trap embedding + weak-bridge decoherence slots -/

/-- Trap-induced decoherence on the weak Fano/Hopf bridge (quantitative slot). -/
structure TrapWeakBridgeDecoherenceSlot where
  /-- Multiplicative factor on weak width; values `> 1` shorten apparent lifetime. -/
  widthFactor : ℝ
  hPos : 0 < widthFactor

noncomputable def trapDecoherenceSlotFromMagnetic (B : ℝ) : TrapWeakBridgeDecoherenceSlot where
  widthFactor := trapWeakWidthFactorFromMagnetic B
  hPos := trapWeakWidthFactorFromMagnetic_pos B

def trapDecoherenceShortensLifetime
    (slot : TrapWeakBridgeDecoherenceSlot) (τ₀ : ℝ) :
    Prop :=
  1 < slot.widthFactor →
    apparentHalfLifeFromCentral τ₀ slot.widthFactor < τ₀

theorem trapDecoherenceShortensLifetime_holds
    (slot : TrapWeakBridgeDecoherenceSlot) (τ₀ : ℝ) (hτ : 0 < τ₀) :
    trapDecoherenceShortensLifetime slot τ₀ := by
  intro hDeco
  exact apparentHalfLife_lt_central_of_widthFactor_gt_one τ₀ slot.widthFactor hτ hDeco

/-! ## Skew phase-lift certificate (Conjecture β structural layer) -/

/-- Re-export: Δ antisymmetry is proved in `Hqiv.Algebra.PhaseLiftDelta`. -/
abbrev skewPhaseLiftMatrix_antisymmetric :=
  @phaseLiftDelta_antisymm

theorem skewAlignment_predicate_separate_from_strong_width (ω m_e ℳ : ℝ) :
    NeutronDecayWidthLedger.strongOverlap ω ≠ NeutronDecayWidthLedger.weakBeta m_e ℳ :=
  strongOverlap_ledger_ne_weakBeta_ledger ω m_e ℳ

/-! ## Central width ledger brackets bottle and beam (witness band) -/

structure NeutronCentralWidthBand where
  lowSeconds : ℝ
  centralSeconds : ℝ
  highSeconds : ℝ
  hLow : lowSeconds ≤ centralSeconds
  hHigh : centralSeconds ≤ highSeconds

def neutronCentralWidthBandWitness : NeutronCentralWidthBand where
  lowSeconds := 875
  centralSeconds := 880
  highSeconds := 884
  hLow := by norm_num
  hHigh := by norm_num

def bottleRefInsideCentralBand (band : NeutronCentralWidthBand) : Prop :=
  band.lowSeconds ≤ neutronLifetimeBottleRefSeconds ∧
    neutronLifetimeBottleRefSeconds ≤ band.highSeconds

def centralBracketsBottleBeamRefs (band : NeutronCentralWidthBand) : Prop :=
  neutronLifetimeBottleRefSeconds ≤ band.centralSeconds ∧
    band.centralSeconds ≤ neutronLifetimeBeamRefSeconds

theorem bottleRef_inside_neutronCentralWidthBandWitness :
    bottleRefInsideCentralBand neutronCentralWidthBandWitness := by
  unfold bottleRefInsideCentralBand neutronCentralWidthBandWitness neutronLifetimeBottleRefSeconds
  constructor <;> norm_num

theorem central_brackets_bottle_beam_refs :
    centralBracketsBottleBeamRefs neutronCentralWidthBandWitness := by
  unfold centralBracketsBottleBeamRefs neutronCentralWidthBandWitness
    neutronLifetimeBottleRefSeconds neutronLifetimeBeamRefSeconds
  constructor <;> norm_num

#check saturatedBeamOverBottleLifetimeRatio_eq_fortysix_over_fortyfive
#check bottleBeamSplitFraction_below_saturated_trap_envelope
#check apparentBetaHalfLifeFromMethod_eq

end

end Hqiv.Physics
