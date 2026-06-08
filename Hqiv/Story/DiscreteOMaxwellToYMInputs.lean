import Hqiv.Story.YMInputsFromWellDynamics

/-!
# Discrete O-Maxwell -> YM input bridge

This module formalizes the intended architecture:

1. A **discrete O-Maxwell shell action** (`m ↦ m+1`) provides the phase and curvature readouts.
2. A set of **transported invariants** records the conserved statements used downstream.
3. Those invariants are packaged into the granular YM bridge obligations
   (`PromotionFromDynamics`, `SpectralFromDynamics`).

No new axioms are introduced; this is a typed bridge layer for organizing subsequent proofs.
-/

namespace Hqiv.Story

open Hqiv.Story.MassGapCompletion
open MillenniumYangMillsDefs

noncomputable section

/-- Discrete O-Maxwell shell-step action (abstract interface). -/
structure DiscreteOMaxwellShellAction (Axis : Type) where
  /-- Per-axis phase increment at shell `m` (one-step dynamics). -/
  phaseStep : Axis → Nat → ℝ
  /-- Per-axis curvature-support readout (`Ω_k`) at shell `m`. -/
  omega : Axis → Nat → ℝ
  /-- Optional shell action density (kept abstract, used for future variational links). -/
  actionDensity : Axis → Nat → ℝ

/-- Dynamics extracted from the discrete O-Maxwell action. -/
def dynamicsOfDiscreteOMaxwell {Axis : Type}
    (A : DiscreteOMaxwellShellAction Axis) : QuantumWellDynamics Axis where
  phaseStep := A.phaseStep
  omega := A.omega

/-- Invariant transport payload over the same shell-step dynamics. -/
structure DiscreteOMaxwellInvariants (Axis : Type) (D : QuantumWellDynamics Axis) : Type where
  /-- Phase-lock statement (one oscillation per shell step, in chosen normalization). -/
  phase_lock_transport : Prop
  /-- Curvature self-support statement (`Ω_k` support relation preserved along shell transport). -/
  curvature_self_support_transport : Prop
  /-- Conserved-content transport statement along shell steps. -/
  conserved_content_transport : Prop

/-- Additional promotion-side consequences derived from the invariants. -/
structure PromotionConsequences (Axis : Type) (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (D : QuantumWellDynamics Axis)
    (I : DiscreteOMaxwellInvariants Axis D) : Type where
  patch_to_localOperators : Prop
  locality_covariance_compat : Prop
  ope_compatibility : Prop

/-- Additional spectral-side consequences derived from the invariants. -/
structure SpectralConsequences (Axis : Type) (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (Δ : ℝ) (D : QuantumWellDynamics Axis)
    (I : DiscreteOMaxwellInvariants Axis D) : Type where
  delta_positive_from_ladder : Prop
  gap_exclusion_from_well : Prop
  finite_mass_control_from_well : Prop

/-- Build granular promotion obligations from discrete O-Maxwell invariants and consequences. -/
def promotionFromDiscreteOMaxwell {Axis : Type} {G : Type} [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (D : QuantumWellDynamics Axis)
    (I : DiscreteOMaxwellInvariants Axis D)
    (C : PromotionConsequences Axis G qft D I) :
    PromotionFromDynamics Axis G qft D where
  typed_morphism := defaultPromotionMorphismData G qft
  patch_to_localOperators := C.patch_to_localOperators
  locality_covariance_compat := C.locality_covariance_compat
  ope_compatibility := C.ope_compatibility

/-- Build granular spectral obligations from discrete O-Maxwell invariants and consequences. -/
def spectralFromDiscreteOMaxwell {Axis : Type} {G : Type} [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (Δ : ℝ) (D : QuantumWellDynamics Axis)
    (I : DiscreteOMaxwellInvariants Axis D)
    (C : SpectralConsequences Axis G qft Δ D I) :
    SpectralFromDynamics Axis G qft Δ D where
  delta_positive_from_ladder := C.delta_positive_from_ladder
  gap_exclusion_from_well := C.gap_exclusion_from_well
  finite_mass_control_from_well := C.finite_mass_control_from_well

/-- Full packaging data: discrete action + invariants + derived bridge consequences. -/
structure DiscreteOMaxwellYMBridgeData (G : Type) [CompactSimpleGaugeGroup G] : Type 2 where
  Axis : Type
  action : DiscreteOMaxwellShellAction Axis
  core : ClayYangMillsCompletionData G
  invariants : DiscreteOMaxwellInvariants Axis (dynamicsOfDiscreteOMaxwell action)
  promotion_consequences :
    PromotionConsequences Axis G core.qft (dynamicsOfDiscreteOMaxwell action) invariants
  spectral_consequences :
    SpectralConsequences Axis G core.qft core.Δ (dynamicsOfDiscreteOMaxwell action) invariants

/-- Main constructor: from discrete O-Maxwell data to the YM-input package used by the scaffold. -/
def ymInputsFromDiscreteOMaxwell {G : Type} [CompactSimpleGaugeGroup G]
    (B : DiscreteOMaxwellYMBridgeData G) : YMInputsFromWellDynamics G where
  Axis := B.Axis
  dynamics := dynamicsOfDiscreteOMaxwell B.action
  core := B.core
  promotion_from_dynamics :=
    promotionFromDiscreteOMaxwell B.core.qft (dynamicsOfDiscreteOMaxwell B.action)
      B.invariants B.promotion_consequences
  spectral_from_dynamics :=
    spectralFromDiscreteOMaxwell B.core.qft B.core.Δ (dynamicsOfDiscreteOMaxwell B.action)
      B.invariants B.spectral_consequences

/-- Corollary: the Millennium target follows from any discrete O-Maxwell bridge package with core witness. -/
theorem yangMillsTarget_of_discreteOMaxwellBridge {G : Type} [CompactSimpleGaugeGroup G]
    (B : DiscreteOMaxwellYMBridgeData G) :
    Hqiv.Bridge.LeanDojo.YangMillsMillenniumTarget G :=
  yangMillsTarget_of_dynamicsInputs (ymInputsFromDiscreteOMaxwell B)

end

end Hqiv.Story
