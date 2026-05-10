import Hqiv.Story.WellShapeFromDynamics
import Hqiv.Story.MassGapCompletionScaffold
import Hqiv.QuantumMechanics.PatchQFTBridge

/-!
# YM input scaffold from well dynamics

This module keeps the Millennium target in view:

- gauge slot: `CompactSimpleGaugeGroup G`;
- QFT slot: `QuantumYangMillsTheory G` (inside `core`);
- bridge obligations required by the partial builder.

The point is to package these obligations as **derived from** a fixed
`QuantumWellDynamics Axis` structure, so the gauge/YM input layer is explicitly built on top of
the well dynamics.
-/

namespace Hqiv.Story

open Hqiv.Story.MassGapCompletion
open Hqiv.Story.MassGapCompletionScaffold
open Hqiv.QM
open MillenniumYangMillsDefs

/-- Typed promotion morphism payload from patch observables to Dojo local operators. -/
structure PromotionMorphismData (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) : Type 1 where
  PatchObs : Type
  /-- Region token attached to each patch observable. -/
  regionToken : PatchObs → SpacetimeRegion
  /-- Concrete promotion map into `qft.localOperators`-indexed operators. -/
  promote :
    PatchObs → GaugeInvariantLocalPolynomial G → SchwartzMap Spacetime ℝ →
      LinearOperator qft.hilbertSpace

/-- Default typed promotion morphism: use a unit patch token and the Dojo `localOperators` map. -/
def defaultPromotionMorphismData (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) : PromotionMorphismData G qft where
  PatchObs := SpacetimeRegion
  regionToken := fun R => R
  promote := fun _R p f => qft.localOperators.op p f

/-- A typed promotion morphism realizes Dojo local operators if some patch observable reproduces
the `localOperators.op` action on all test-function inputs, for every region token. -/
def PromotionMorphismData.realizesLocalOperators {G : Type} [CompactSimpleGaugeGroup G]
    {qft : QuantumYangMillsTheory G} (M : PromotionMorphismData G qft) : Prop :=
  ∀ R : SpacetimeRegion, ∃ obs : M.PatchObs,
    M.regionToken obs = R ∧ ∀ p f, M.promote obs p f = qft.localOperators.op p f

/-- The default typed promotion morphism realizes Dojo local operators by construction. -/
theorem defaultPromotionMorphismData_realizesLocalOperators (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) :
    (defaultPromotionMorphismData G qft).realizesLocalOperators := by
  intro R
  refine ⟨R, rfl, ?_⟩
  intro p f
  rfl

/-- Granular promotion obligations sourced from fixed well dynamics. -/
structure PromotionFromDynamics (Axis : Type) (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (D : QuantumWellDynamics Axis) : Type 2 where
  /-- Explicit typed morphism object carrying the promotion map. -/
  typed_morphism : PromotionMorphismData G qft
  /-- Patch/lattice observables can be promoted into the `localOperators` interface for this `qft`. -/
  patch_to_localOperators : Prop
  /-- Promoted local operators satisfy covariance/locality compatibility constraints for this construction. -/
  locality_covariance_compat : Prop
  /-- OPE coefficients are compatible with the promoted observables and chosen dynamics. -/
  ope_compatibility : Prop

/-- Granular spectral obligations sourced from fixed well dynamics. -/
structure SpectralFromDynamics (Axis : Type) (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (Δ : ℝ) (D : QuantumWellDynamics Axis) : Type where
  /-- Positivity/admissibility of `Δ` read from the ladder/well dynamics. -/
  delta_positive_from_ladder : Prop
  /-- Shell-ladder / well dynamics are linked to the Hamiltonian spectral exclusion on `(0, Δ)`. -/
  gap_exclusion_from_well : Prop
  /-- Finite mass-window control compatible with the same spectral bridge. -/
  finite_mass_control_from_well : Prop

/-- YM input package whose bridge obligations are declared as consequences of fixed well dynamics. -/
structure YMInputsFromWellDynamics (G : Type) [CompactSimpleGaugeGroup G] where
  Axis : Type
  dynamics : QuantumWellDynamics Axis
  core : ClayYangMillsCompletionData G
  /-- Non-abelian promotion side, sourced from the dynamics package. -/
  promotion_from_dynamics : PromotionFromDynamics Axis G core.qft dynamics
  /-- Spectral bridge side, sourced from the dynamics package. -/
  spectral_from_dynamics : SpectralFromDynamics Axis G core.qft core.Δ dynamics

/-- Convert dynamics-derived promotion statement into the typed scaffold obligation. -/
def promotionObligationsOfInputs {G : Type} [CompactSimpleGaugeGroup G]
    (I : YMInputsFromWellDynamics G) : PromotionObligations G I.core.qft where
  patch_to_localOperators := I.promotion_from_dynamics.patch_to_localOperators ∧
    I.promotion_from_dynamics.locality_covariance_compat
  ope_compatibility := I.promotion_from_dynamics.ope_compatibility

/-- Convert dynamics-derived spectral statement into the typed scaffold obligation. -/
def ladderSpectralObligationsOfInputs {G : Type} [CompactSimpleGaugeGroup G]
    (I : YMInputsFromWellDynamics G) : LadderSpectralObligations G I.core.qft I.core.Δ where
  delta_from_ladder := I.spectral_from_dynamics.delta_positive_from_ladder
  spectral_bridge := I.spectral_from_dynamics.gap_exclusion_from_well ∧
    I.spectral_from_dynamics.finite_mass_control_from_well

/-- Main bridge: from dynamics-based YM inputs into the partial YM scaffold. -/
def partialQFTOfDynamicsInputs {G : Type} [CompactSimpleGaugeGroup G]
    (I : YMInputsFromWellDynamics G) : PartialQuantumYangMillsTheory G :=
  PartialQuantumYangMillsTheory.ofClayCore G I.core
    (promotionObligationsOfInputs I)
    (ladderSpectralObligationsOfInputs I)

/-- Millennium target follows from any dynamics-based input package once `core` is provided. -/
theorem yangMillsTarget_of_dynamicsInputs {G : Type} [CompactSimpleGaugeGroup G]
    (I : YMInputsFromWellDynamics G) :
    Hqiv.Bridge.LeanDojo.YangMillsMillenniumTarget G :=
  yangMillsMillenniumTarget_of_partial (partialQFTOfDynamicsInputs I)

end Hqiv.Story
