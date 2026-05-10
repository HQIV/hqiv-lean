import Hqiv.Story.Chapter07_PatchQFT
import Hqiv.Bridge.LeanDojoClayMillennium
import Hqiv.Story.QuantumYangMillsFromPoincareToy
import Hqiv.Story.QuantumYangMillsFromPatchHQIV

/-!
# Story — Chapter 8: Clay Millennium (Lean Dojo) problem statements and witness wiring

Vendored `Problems.YangMills.*` / `Problems.NavierStokes.*` + `Hqiv.Bridge.LeanDojo`:
sufficient conditions for the official `Prop`s. **Solving** the prizes still requires the missing
constructions (QFT+gap, or a Fefferman disjunct) — the Story only orders *what you already have*
leading up to the formal targets.

**End of linear spine** — `import Hqiv.Story.Chapter08_ClayMillennium` or `HQIVStory.lean`.

## Mass-gap narrative

- **Chapters 1–7 (proved):** geometry → ladder → baryogenesis readouts → fluid sign → **abelian**
  patch commutators (`step07_patchAbelianCommutator`).
- **Dojo YM *interface* without gap:** the **HQIV-facing** witness is
  `Hqiv.Story.QuantumYangMillsFromPatchHQIV.hqivInterfaceQuantumYangMills` (same minimal Schwartz spine
  as the toy constructor; patch jets packaged separately). This chapter **imports**
  `QuantumYangMillsFromPatchHQIV` so `MassGap.nonempty_hqivInterface_quantumYangMills` can be stated here
  without an import cycle (patch Wightman now pulls ladder data from **`LadderGapCandidateWell`**, not
  `SketchesConsumedLadderWell`). The **1D toy** entry point `QuantumYangMillsFromPoincareToy` remains
  imported for the existing `nonempty_poincareToy_quantumYangMills` lemma name.
- **YM *promotion* obligations** for the interface witness:
  `Hqiv.Story.hqiv_promotion_obligations_hqivInterfaceQFT` in `Hqiv.Story.YMRemainingObligations`.
- **Clay YM:** `step07_yangMillsWitnessBundle G` is **definitionally the same** `Prop` as
  `MillenniumYangMills.YangMillsExistenceAndMassGap G` (hence the same as `step08`); naming it “step 7”
  is narrative placement only. It is **not** derived from the abelian patch layer. The lemma
  `step08_yangMills_of_witnessBundle` is therefore the identity on that `Prop`.

## Step 4 (still open): Schwartz / Wightman alignment

Cycle removal lets Chapter 8 **see** `hqivPatchJetOperatorValuedDistribution`, but **identifying** it
with `QuantumYangMillsTheory.field_operators` on real Schwartz tests (and upgrading Wightman data off
the toy spine) is the separate analytic **`SchwartzRealToComplexLift` + W4 cyclicity** track — not
proved in this file.
-/

namespace Hqiv.Story.MassGap

open Hqiv.Bridge.LeanDojo MillenniumYangMills MillenniumYangMillsDefs
open Hqiv.Story.QuantumYangMillsFromPoincareToy
open Hqiv.Story.QuantumYangMillsFromPatchHQIV

/-- Dojo / Clay **target** `Prop` (same existential shape as `YangMillsExistenceAndMassGap G`). -/
def step07_yangMillsWitnessBundle (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (qft : QuantumYangMillsTheory G) (Δ : ℝ),
    ClayExistence qft ∧ HasMassGapSpectrum G qft Δ ∧ FiniteMassSpectrum G qft

/-- Clay target: existence of a nontrivial YM QFT with a **positive mass gap** in the Dojo spectral sense. -/
abbrev step08_yangMillsExistenceAndMassGap (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  YangMillsExistenceAndMassGap G

/-- Same `Prop` as the official Millennium statement (the existential is copied verbatim in `step07`). -/
theorem step07_yangMillsWitnessBundle_eq_yangMillsExistenceAndMassGap (G : Type)
    [CompactSimpleGaugeGroup G] :
    step07_yangMillsWitnessBundle G = YangMillsExistenceAndMassGap G :=
  rfl

/-- `step08` is an abbrev for that same `Prop`, so it agrees with `step07`. -/
theorem step07_yangMillsWitnessBundle_eq_step08 (G : Type) [CompactSimpleGaugeGroup G] :
    step07_yangMillsWitnessBundle G = step08_yangMillsExistenceAndMassGap G :=
  rfl

/-- Trivial: `step07` and `step08` are the same `Prop`. -/
theorem step08_yangMills_of_witnessBundle (G : Type) [CompactSimpleGaugeGroup G]
    (h : step07_yangMillsWitnessBundle G) :
    step08_yangMillsExistenceAndMassGap G :=
  h

/-- Full **proved** spine through the abelian patch layer (Ch 1–7). -/
theorem mass_gap_story_through_patch_commutator (h1 : step01_lightConeAuxiliarySubstrate) :
    step07_patchAbelianCommutator :=
  step07_of_step06 (step06_of_step05 (step05_of_step04 (step04_of_step03 (step03_of_step02 (step02_of_step01 h1)))))

/-- Convenience: Ch 1 discharged by `step01_lightConeAuxiliarySubstrate_holds`. -/
theorem mass_gap_story_through_patch_commutator_of_axioms : step07_patchAbelianCommutator :=
  mass_gap_story_through_patch_commutator step01_lightConeAuxiliarySubstrate_holds

/-- Patch-side spectral gap witness from the ladder Hamiltonian packaging:
`PatchWightmanMassGapOnSpectrum (ladderGapCandidate / 2)`.

This is a **nonzero** gap statement on `patchHamiltonian` (Story patch Wightman layer), separate from
the full Dojo `QuantumYangMillsTheory` mass-gap witness. -/
theorem patch_wightman_positive_gap_window :
    Hqiv.Story.PatchWightmanMassGapOnSpectrum (Hqiv.Story.ladderGapCandidate / 2) :=
  Hqiv.Story.patchWightman_massGapOnSpectrum

/-- Clay YM **from an explicit Dojo witness** (the only place non-abelian data enters). -/
theorem yangMills_existence_and_mass_gap_of_dojo_witness (G : Type) [CompactSimpleGaugeGroup G]
    (hYM : step07_yangMillsWitnessBundle G) :
    step08_yangMillsExistenceAndMassGap G :=
  step08_yangMills_of_witnessBundle G hYM

theorem nonempty_poincareToy_quantumYangMills (G : Type) [CompactSimpleGaugeGroup G] :
    Nonempty (QuantumYangMillsTheory G) :=
  ⟨poincareToyQuantumYangMills G⟩

/-- Same `Nonempty` certificate as `QuantumYangMillsHQIVInterface.nonempty_hqivInterface_quantumYangMills`,
now available from Chapter 8 after decoupling patch Wightman from the `SketchesConsumedLadderWell`
completion import cycle (`LadderGapCandidateWell`). -/
theorem nonempty_hqivInterface_quantumYangMills (G : Type) [CompactSimpleGaugeGroup G] :
    Nonempty (QuantumYangMillsTheory G) :=
  ⟨hqivInterfaceQuantumYangMills G⟩

end Hqiv.Story.MassGap
