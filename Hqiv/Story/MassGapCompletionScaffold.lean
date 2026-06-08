import Hqiv.Story.MassGapCompletionBundle
import Hqiv.QuantumMechanics.PatchQFTBridge

/-!
# Partial `QuantumYangMillsTheory` builder (HQIV + Clay completion)

This is the **constructive socket** for the Yang–Mills Millennium layer: you carry a full
`QuantumYangMillsTheory G` together with the **proved** HQIV abelian patch commutator layer (Ch. 7),
plus explicit `Prop` slots for work that is *not* proved here (promotion of the patch net to the
non-abelian local-operator story; a discrete-to-spectral gap bridge).

**Important:** `YangMillsExistenceAndMassGap G` is an existential over `QuantumYangMillsTheory G` and
spectral predicates only. The placeholders are **documentation / proof obligations** for a future
HQIV-aligned completion; they do **not** appear in `partialQFT_gives_millennium`, which projects the
already-assumed `ClayYangMillsCompletionData` “core”.

Lean anchors for the abelian layer:
`Hqiv.QM.patchAlgebraAt_opCommutator_zero`, packaged as `MassGap.step07_patchAbelianCommutator`.
-/

namespace Hqiv.Story.MassGapCompletionScaffold

open Hqiv.Story.MassGap
open Hqiv.Story.MassGapCompletion
open Hqiv.QM
open MillenniumYangMills MillenniumYangMillsDefs

/-- Pending bridge obligations from the HQIV patch/lattice layer to non-abelian local operators. -/
structure PromotionObligations (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) : Type where
  /-- Placeholder for a map / compatibility theorem between patch operators and `qft.localOperators`. -/
  patch_to_localOperators : Prop
  /-- Placeholder for OPE compatibility with the promoted local operators. -/
  ope_compatibility : Prop

/-- Pending bridge obligations from HQIV shell/ladder data to a spectral-gap clause for this `qft, Δ`. -/
structure LadderSpectralObligations (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (Δ : ℝ) : Type where
  /-- Placeholder for deriving the positivity / admissibility of `Δ` from HQIV ladder data. -/
  delta_from_ladder : Prop
  /-- Placeholder for connecting ladder observables to the Hamiltonian spectrum exclusion on `(0, Δ)`. -/
  spectral_bridge : Prop

/-- **Partial builder:** full Dojo theory + Clay clauses in `core`, proved HQIV patch commutator layer,
    and typed obligations for non-abelian / spectral bridge work still to be done. -/
structure PartialQuantumYangMillsTheory (G : Type) [CompactSimpleGaugeGroup G] : Type 2 where
  /-- A *complete* `QuantumYangMillsTheory` witness together with `Δ` and the three Millennium clauses. -/
  core : ClayYangMillsCompletionData G
  /-- Story Ch. 7: abelian `patchAlgebraAt` operators have vanishing commutators
      (`PatchQFTBridge.patchAlgebraAt_opCommutator_zero`). -/
  hqiv_abelian_patch_layer : step07_patchAbelianCommutator
  /-- Remaining work (1): relate patch / lattice smearing to the non-abelian `localOperators` package. -/
  promotion_obligations : PromotionObligations G core.qft
  /-- Remaining work (2): derive or import a spectral-gap story from HQIV ladder / shell readouts. -/
  ladder_spectral_obligations : LadderSpectralObligations G core.qft core.Δ

/-- HQIV discharges the abelian commutator layer unconditionally (Ch. 1–7 spine). -/
theorem hqiv_supplies_abelian_reduction : step07_patchAbelianCommutator :=
  mass_gap_story_through_patch_commutator_of_axioms

/-- Pointwise form: commutators vanish on `patchAlgebraAt` (same content as `hqiv_supplies_abelian_reduction`). -/
theorem hqiv_patch_opCommutator_pointwise (R S : SpacetimeRegion)
    (A B : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4) (hA : A ∈ patchAlgebraAt R) (hB : B ∈ patchAlgebraAt S) :
    opCommutator A B = 0 :=
  patchAlgebraAt_opCommutator_zero A B hA hB

/-- From completion **core** alone; placeholders are irrelevant to the Millennium `Prop`. -/
theorem partialQFT_gives_millennium {G : Type} [CompactSimpleGaugeGroup G]
    (P : PartialQuantumYangMillsTheory G) : YangMillsExistenceAndMassGap G :=
  yangMillsExistenceAndMassGap_of_completionData G P.core

theorem yangMillsMillenniumTarget_of_partial {G : Type} [CompactSimpleGaugeGroup G]
    (P : PartialQuantumYangMillsTheory G) : Hqiv.Bridge.LeanDojo.YangMillsMillenniumTarget G :=
  partialQFT_gives_millennium P

/-- Attach the proved HQIV abelian layer and typed bridge obligations to an existing Clay completion. -/
def PartialQuantumYangMillsTheory.ofClayCore (G : Type) [CompactSimpleGaugeGroup G]
    (core : ClayYangMillsCompletionData G)
    (promotion : PromotionObligations G core.qft)
    (ladder : LadderSpectralObligations G core.qft core.Δ) :
    PartialQuantumYangMillsTheory G where
  core := core
  hqiv_abelian_patch_layer := hqiv_supplies_abelian_reduction
  promotion_obligations := promotion
  ladder_spectral_obligations := ladder

/-- Convenience: use trivial placeholders when you only need the Millennium projection. -/
def PartialQuantumYangMillsTheory.ofClayCoreTrivialPlaceholders (G : Type) [CompactSimpleGaugeGroup G]
    (core : ClayYangMillsCompletionData G) : PartialQuantumYangMillsTheory G :=
  ofClayCore G core
    { patch_to_localOperators := True, ope_compatibility := True }
    { delta_from_ladder := True, spectral_bridge := True }

end Hqiv.Story.MassGapCompletionScaffold
