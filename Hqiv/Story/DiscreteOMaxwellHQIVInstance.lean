import Hqiv.Story.DiscreteOMaxwellToYMInputs
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Geometry.OctonionicLightCone

/-!
# Concrete HQIV discrete O-Maxwell instance

This module instantiates the abstract bridge
`DiscreteOMaxwellToYMInputs` using existing HQIV shell quantities:

- phase step: fixed one-cycle shell increment (`2π`) as the baseline discrete O-Maxwell step;
- curvature support: `omega_k_at_horizon m m_lockin`;
- action density: `shell_shape m`.

It also supplies a first invariant payload tied to already-proved HQIV facts
(`omega_k_lockin_calibration`, positivity / ladder anchors), and provides a constructor that turns
those data into `YMInputsFromWellDynamics`.
-/

namespace Hqiv.Story

open Hqiv
open Hqiv.Story.MassGapCompletion
open MillenniumYangMillsDefs

noncomputable section

/-- Fano-axis labels for the HQIV discrete shell dynamics. -/
inductive HQIVAxis where
  | e1 | e2 | e3 | e4 | e5 | e6 | e7
  deriving DecidableEq, Repr

/-- Concrete discrete O-Maxwell shell action from existing HQIV shell functions. -/
def hqivDiscreteOMaxwellAction : DiscreteOMaxwellShellAction HQIVAxis where
  phaseStep := fun _a _m => 2 * Real.pi
  omega := fun _a m => omega_k_at_horizon m m_lockin
  actionDensity := fun _a m => shell_shape m

/-- The induced well dynamics for this concrete action. -/
def hqivWellDynamics : QuantumWellDynamics HQIVAxis :=
  dynamicsOfDiscreteOMaxwell hqivDiscreteOMaxwellAction

/-- Basic HQIV invariant transport payload available from current proved lemmas. -/
def hqivDiscreteOMaxwellInvariants : DiscreteOMaxwellInvariants HQIVAxis hqivWellDynamics where
  phase_lock_transport := ∀ a m, hqivWellDynamics.phaseStep a m = 2 * Real.pi
  curvature_self_support_transport := hqivWellDynamics.omega HQIVAxis.e1 m_lockin = 1
  conserved_content_transport := 0 < shell_shape_abs m_lockin

/-- These invariants are discharged by existing HQIV definitions/lemmas. -/
theorem hqivDiscreteOMaxwellInvariants_holds :
    hqivDiscreteOMaxwellInvariants.phase_lock_transport ∧
      hqivDiscreteOMaxwellInvariants.curvature_self_support_transport ∧
      hqivDiscreteOMaxwellInvariants.conserved_content_transport := by
  refine ⟨?_, ?_, ?_⟩
  · intro a m
    rfl
  · change omega_k_at_horizon m_lockin m_lockin = 1
    exact omega_k_lockin_calibration curvature_integral_m_lockin_pos
  · exact shell_shape_abs_pos m_lockin

/-- Build promotion consequences from explicit proof obligations (kept as arguments). -/
def hqivPromotionConsequencesOfProps
    {G : Type} [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G)
    (hPatch : Prop) (hLocCov : Prop) (hOPE : Prop) :
    PromotionConsequences HQIVAxis G qft hqivWellDynamics hqivDiscreteOMaxwellInvariants where
  patch_to_localOperators := hPatch
  locality_covariance_compat := hLocCov
  ope_compatibility := hOPE

/-- Build spectral consequences from explicit proof obligations (kept as arguments). -/
def hqivSpectralConsequencesOfProps
    {G : Type} [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G) (Δ : ℝ)
    (hDelta : Prop) (hGap : Prop) (hFin : Prop) :
    SpectralConsequences HQIVAxis G qft Δ hqivWellDynamics hqivDiscreteOMaxwellInvariants where
  delta_positive_from_ladder := hDelta
  gap_exclusion_from_well := hGap
  finite_mass_control_from_well := hFin

/-- Concrete bridge packaging from HQIV discrete O-Maxwell data + explicit consequence proofs. -/
def hqivDiscreteOMaxwellBridgeData
    {G : Type} [CompactSimpleGaugeGroup G] (core : ClayYangMillsCompletionData G)
    (hPatch : Prop) (hLocCov : Prop) (hOPE : Prop)
    (hDelta : Prop) (hGap : Prop) (hFin : Prop) :
    DiscreteOMaxwellYMBridgeData G where
  Axis := HQIVAxis
  action := hqivDiscreteOMaxwellAction
  core := core
  invariants := hqivDiscreteOMaxwellInvariants
  promotion_consequences := hqivPromotionConsequencesOfProps core.qft hPatch hLocCov hOPE
  spectral_consequences := hqivSpectralConsequencesOfProps core.qft core.Δ hDelta hGap hFin

/-- Convenience constructor: directly produce the YM-input package from HQIV discrete O-Maxwell data. -/
def hqivYMInputsFromDiscreteOMaxwell
    {G : Type} [CompactSimpleGaugeGroup G] (core : ClayYangMillsCompletionData G)
    (hPatch : Prop) (hLocCov : Prop) (hOPE : Prop)
    (hDelta : Prop) (hGap : Prop) (hFin : Prop) :
    YMInputsFromWellDynamics G :=
  ymInputsFromDiscreteOMaxwell
    (hqivDiscreteOMaxwellBridgeData core hPatch hLocCov hOPE hDelta hGap hFin)

end

end Hqiv.Story
