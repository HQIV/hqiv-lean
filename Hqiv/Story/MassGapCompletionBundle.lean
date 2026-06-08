import Hqiv.Story.Chapter08_ClayMillennium

/-!
# Mass-gap completion — assembling HQIV substrate with the Clay `Prop`

Everything **HQIV proves** toward the mass-gap narrative lives in the Ch 1–7 spine (through the
abelian patch commutator) plus the discrete lock-in readouts (`BaryogenesisCore`). The Clay / Lean
Dojo statement is a **single** existential over `QuantumYangMillsTheory G`; in this repo it is
spelled twice on purpose (`step07_yangMillsWitnessBundle`, `step08_yangMillsExistenceAndMassGap`) but
is **the same `Prop`** as `MillenniumYangMills.YangMillsExistenceAndMassGap G`
(`Chapter08_ClayMillennium.step07_yangMillsWitnessBundle_eq_yangMillsExistenceAndMassGap`).

This file adds:

* a **typed witness carrier** `ClayYangMillsCompletionData` (nonempty ↔ Millennium target);
* a packaged **proved substrate** `hqivMassGapProvedSubstrate`;
* a **product** `HQIVYangMillsMillenniumWithSubstrate` so any Clay proof can be tagged with the
  already-dischargeable HQIV side for free.

What remains mathematically hard is still **inhabiting** `QuantumYangMillsTheory G` (and the gap
predicates) for your chosen `CompactSimpleGaugeGroup G` — not a missing lemma in this file.

See `Hqiv.Story.MassGapCompletionScaffold` for `PartialQuantumYangMillsTheory` (core + HQIV abelian
layer + explicit placeholder obligations).
-/

namespace Hqiv.Story.MassGapCompletion

open Hqiv.Story.MassGap
open MillenniumYangMills MillenniumYangMillsDefs

/-- Typed packaging of one full Clay/Dojo witness (a `QuantumYangMillsTheory` + `Δ` + three clauses).

`QuantumYangMillsTheory` lives in `Type 2` (Hilbert space + instances), so this carrier must as well. -/
structure ClayYangMillsCompletionData (G : Type) [CompactSimpleGaugeGroup G] : Type 2 where
  qft : QuantumYangMillsTheory G
  Δ : ℝ
  hExist : ClayExistence qft
  hGap : HasMassGapSpectrum G qft Δ
  hFin : FiniteMassSpectrum G qft

/-- `Nonempty` completion data ↔ the official Millennium `Prop`. -/
theorem yangMillsExistenceAndMassGap_iff_nonempty_completionData (G : Type) [CompactSimpleGaugeGroup G] :
    YangMillsExistenceAndMassGap G ↔ Nonempty (ClayYangMillsCompletionData G) := by
  refine ⟨fun ⟨qft, Δ, hE, hG, hF⟩ => ⟨⟨qft, Δ, hE, hG, hF⟩⟩, ?_⟩
  intro h
  obtain ⟨d⟩ := h
  exact ⟨d.qft, d.Δ, d.hExist, d.hGap, d.hFin⟩

/-- Same as `yangMillsExistenceAndMassGap_iff_nonempty_completionData`, using the Story name `step07`. -/
theorem step07_yangMillsWitnessBundle_iff_nonempty_completionData (G : Type) [CompactSimpleGaugeGroup G] :
    step07_yangMillsWitnessBundle G ↔ Nonempty (ClayYangMillsCompletionData G) := by
  simpa only [step07_yangMillsWitnessBundle_eq_yangMillsExistenceAndMassGap] using
    yangMillsExistenceAndMassGap_iff_nonempty_completionData G

/-- Millennium target from explicit completion **data** (forward direction of `Nonempty`). -/
theorem yangMillsExistenceAndMassGap_of_completionData (G : Type) [CompactSimpleGaugeGroup G]
    (d : ClayYangMillsCompletionData G) : YangMillsExistenceAndMassGap G :=
  ⟨d.qft, d.Δ, d.hExist, d.hGap, d.hFin⟩

/-- Bridge re-export: `LeanDojo.YangMillsMillenniumTarget` is definitionally the same statement. -/
theorem yangMillsMillenniumTarget_of_completionData (G : Type) [CompactSimpleGaugeGroup G]
    (d : ClayYangMillsCompletionData G) : Hqiv.Bridge.LeanDojo.YangMillsMillenniumTarget G :=
  yangMillsExistenceAndMassGap_of_completionData G d

/-- Proved HQIV substrate used in the mass-gap story (Ch 1 + lock-in witness + abelian patch layer). -/
def hqivMassGapProvedSubstrate : Prop :=
  step01_lightConeAuxiliarySubstrate ∧ step05_referenceShellGapWitness ∧ step07_patchAbelianCommutator

theorem hqivMassGapProvedSubstrate_holds : hqivMassGapProvedSubstrate :=
  ⟨step01_lightConeAuxiliarySubstrate_holds, step05_referenceShellGapWitness_holds,
    mass_gap_story_through_patch_commutator_of_axioms⟩

/-- Pair the **proved** HQIV substrate with the Clay existential (same `G` slot on the right). -/
def HQIVYangMillsMillenniumWithSubstrate (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  hqivMassGapProvedSubstrate ∧ YangMillsExistenceAndMassGap G

/-- The Clay half alone determines the Millennium `Prop`; the substrate is extra information. -/
theorem yangMillsExistenceAndMassGap_of_HQIVYangMillsMillenniumWithSubstrate
    (G : Type) [CompactSimpleGaugeGroup G] (h : HQIVYangMillsMillenniumWithSubstrate G) :
    YangMillsExistenceAndMassGap G :=
  h.2

/-- Any Clay proof upgrades for free to “substrate + Clay” packaging. -/
theorem HQIVYangMillsMillenniumWithSubstrate_of_yangMillsExistenceAndMassGap
    (G : Type) [CompactSimpleGaugeGroup G] (h : YangMillsExistenceAndMassGap G) :
    HQIVYangMillsMillenniumWithSubstrate G :=
  ⟨hqivMassGapProvedSubstrate_holds, h⟩

/-- `step07` packaged as completion data + agreement with `LeanDojo` abbrev. -/
theorem yangMillsMillenniumTarget_of_step07 {G : Type} [CompactSimpleGaugeGroup G]
    (h : step07_yangMillsWitnessBundle G) : Hqiv.Bridge.LeanDojo.YangMillsMillenniumTarget G :=
  h

end Hqiv.Story.MassGapCompletion
