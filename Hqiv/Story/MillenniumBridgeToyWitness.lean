import Hqiv.Story.GaugeGroupFromHQIVSketch
import Hqiv.Story.MillenniumBridgePatchVacuum
import Hqiv.Story.PatchHilbertBridge
import Hqiv.Story.YMRemainingObligations
import Hqiv.Story.QuantumYangMillsHQIVInterface
import Hqiv.Story.MassGapCompletionBundle
import Hqiv.Story.MillenniumFiniteMassObstruction

/-!
# Millennium bridge toy witness (explicit Hilbert slot + assumed Clay body)

This module separates two concerns:

1. **Constructed Hilbert bridge + patch vacuum on the patch carrier.**  
   See `MillenniumBridgePatchVacuum`: `MillenniumG`, `PatchHilbert`, `patchHilbertPatchBridge`, and the
   unit vector `patchVacuum`. The identity bridge here is definitionally the same as
   `standardLatticeHilbertPatchBridge`.

2. **Clay / Dojo existential packaging for a fixed gauge type.**  
   The class `CompactSimpleGaugeGroup` and a full `QuantumYangMillsTheory` are intentionally
   heavyweight; the Story line only needs *some* inhabitant of `ClayYangMillsCompletionData G` to
   invoke `yangMillsExistenceAndMassGap_of_completionData` and pair with
   `hqivMassGapProvedSubstrate` via `HQIVYangMillsMillenniumWithSubstrate`.

For a **first** end-to-end certificate we therefore:

- expose the **explicit** standard bridge `standardLatticeHilbertPatchBridge` on
  `H = LatticeHilbert 4` (identity `incl`); and
- use **`MillenniumBridgeGauge := HQIVStoryGaugeSketch`** (concrete `CompactSimpleGaugeGroup` from
  `GaugeGroupFromHQIVSketch`) and keep the genuinely hard non-abelian ingredients as **explicit
  parameters** (`ClayYangMillsCompletionData`, an abstract `HilbertPatchBridge` on
  `core.qft.hilbertSpace`, and a witness of
  `hqiv_hilbert_bridge_local_operator_compat_weak`; see `YMRemainingObligations`).

We do **not** try to `cast` a bridge across `millenniumBridgeQFT.hilbertSpace = LatticeHilbert 4`:
that type equality does not identify the `NormedAddCommGroup` / `InnerProductSpace` diamonds, so
the honest transport is to supply `HilbertPatchBridge` directly on the carrier carried by `qft`.

Discharging these parameters is the mathematical work: build a real `QuantumYangMillsTheory`, prove the
mass-gap predicates, choose a bounded embedding `LatticeHilbert 4 →L[ℝ] H`, and align patch
observables with `localOperators` so each `localOperators.op p f` is realized as some sandwich
`patchOpAsLinearOperator` of a patch observable (weak alignment).

**No axioms, full Dojo `QuantumYangMillsTheory` interface witness (not a mass-gap YM):**
the current HQIV-facing witness is exposed in `Hqiv.Story.QuantumYangMillsHQIVInterface` as
`hqivInterfaceQuantumYangMills`; promotion-obligation discharge for that QFT is
`Hqiv.Story.hqiv_promotion_obligations_hqivInterfaceQFT` in `YMRemainingObligations`.

See `Hqiv.Story.MassGapCompletionBundle` for `yangMillsExistenceAndMassGap_of_completionData` /
`HQIVYangMillsMillenniumWithSubstrate`.

A zero Hamiltonian (as in the Poincaré Wightman toy) implies `HasMassGapSpectrum` at arbitrarily
large `Δ` but rules out `FiniteMassSpectrum`; see
`Hqiv.Story.MillenniumDojoFiniteGapObstruction` in `Hqiv.Story.MillenniumFiniteMassObstruction`.
-/

namespace Hqiv.Story

open Hqiv.QM
open Hqiv.Story.MassGapCompletion
open Hqiv.Story.MillenniumDojoFiniteGapObstruction
open MillenniumYangMills MillenniumYangMillsDefs

noncomputable section

/-- Canonical bounded ℝ-linear embedding of the patch space into itself (identity). -/
abbrev standardLatticeHilbertPatchBridge : HilbertPatchBridge (LatticeHilbert 4) :=
  HilbertPatchBridge.latticeIdentityBridge

@[simp]
theorem standardLatticeHilbertPatchBridge_incl_apply (ψ : LatticeHilbert 4) :
    standardLatticeHilbertPatchBridge.incl ψ = ψ :=
  rfl

/-- Same identity bridge as `patchHilbertPatchBridge` on `PatchHilbert = LatticeHilbert 4`. -/
@[simp]
theorem standardLatticeHilbertPatchBridge_eq_patchHilbertPatchBridge :
    standardLatticeHilbertPatchBridge = patchHilbertPatchBridge :=
  rfl

/-- Gauge slot: concrete `S₃` sketch from `GaugeGroupFromHQIVSketch` (same as `MillenniumG`). -/
abbrev MillenniumBridgeGauge : Type :=
  MillenniumG

/-- The QFT layer extracted from explicit completion data. -/
noncomputable def millenniumBridgeQFT
    (core : ClayYangMillsCompletionData MillenniumBridgeGauge) :
    QuantumYangMillsTheory MillenniumBridgeGauge :=
  core.qft

/-- Explicit bridge-side obligation package over a chosen completion core:
bounded embedding on `core.qft.hilbertSpace` + weak patch-to-`localOperators` alignment. -/
def MillenniumBridgeHilbertObligation
    (core : ClayYangMillsCompletionData MillenniumBridgeGauge) : Prop :=
  ∃ br : HilbertPatchBridge core.qft.hilbertSpace,
    hqiv_hilbert_bridge_local_operator_compat_weak core.qft br

/-- Millennium existential from explicit completion data. -/
theorem millenniumBridge_yangMillsExistenceAndMassGap
    (core : ClayYangMillsCompletionData MillenniumBridgeGauge) :
    YangMillsExistenceAndMassGap MillenniumBridgeGauge :=
  yangMillsExistenceAndMassGap_of_completionData MillenniumBridgeGauge core

/-- Substrate + Clay product, using the same explicit completion data. -/
theorem millenniumBridge_HQIVYangMillsMillenniumWithSubstrate
    (core : ClayYangMillsCompletionData MillenniumBridgeGauge) :
    HQIVYangMillsMillenniumWithSubstrate MillenniumBridgeGauge :=
  HQIVYangMillsMillenniumWithSubstrate_of_yangMillsExistenceAndMassGap MillenniumBridgeGauge
    (millenniumBridge_yangMillsExistenceAndMassGap core)

/-- Stand-alone spectral fact (does **not** use `millenniumBridgeClayCore`): a nontrivial
`QuantumYangMillsTheory` whose Wightman Hamiltonian is the zero operator cannot also satisfy
`FiniteMassSpectrum` — a genuine `hFin` layer must come from a **non-**trivially gapped Hamiltonian, not
from the constant / zero-Hamiltonian Poincaré toy alone. -/
theorem not_FiniteMassSpectrum_of_wightman_hamiltonian_eq_zero
    {G : Type} [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G)
    [hnt : Nontrivial qft.hilbertSpace] (hH : qft.wightman.hamiltonian = 0) :
    ¬FiniteMassSpectrum G qft :=
  not_FiniteMassSpectrum_of_hamiltonian_eq_zero G qft hH

end

end Hqiv.Story
