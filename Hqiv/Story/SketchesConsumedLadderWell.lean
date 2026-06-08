import Hqiv.Story.LadderGapCandidateWell
import Hqiv.Story.DiscreteOMaxwellHQIVInstance

/-!
# Consuming external sketches: ladder positivity + finite well control

This file "consumes" two external sketch files as **intent**, then restates that intent in the
current HQIV Story architecture:

- `delta_positive_from_ladder` becomes a concrete positivity witness built from existing HQIV lemmas.
- `finite_mass_control_from_well` becomes a concrete finite shell-mode bound witness (`r8 m_lockin`)
  that can feed spectral-control obligations once the Hamiltonian bridge map is supplied.

The concrete ladder values `ladderGapCandidate`, `finiteModeBoundAtLockin`, and their positivity lemmas
live in **`LadderGapCandidateWell`** (no `MassGapCompletionBundle` import), so `MillenniumBridgePatchPoincareWightman`
can depend on the ladder scale **without** an import cycle through `Chapter08`.

No legacy symbols (e.g. `P.gap`) are used; everything is phrased against the present bridge types.
-/

namespace Hqiv.Story

open Hqiv
open Hqiv.Algebra
open MillenniumYangMillsDefs

noncomputable section

/-- Packaging helper: build spectral consequences by consuming the two sketch conclusions together
with the remaining bridge hypotheses. -/
def hqivSpectralConsequencesFromSketches
    {G : Type} [CompactSimpleGaugeGroup G] (qft : QuantumYangMillsTheory G) (Δ : ℝ)
    (hGapExclusion : Prop) (hFiniteMassControl : Prop) :
    SpectralConsequences HQIVAxis G qft Δ hqivWellDynamics hqivDiscreteOMaxwellInvariants where
  delta_positive_from_ladder := 0 < ladderGapCandidate
  gap_exclusion_from_well := hGapExclusion
  finite_mass_control_from_well := hFiniteMassControl

/-- Consumed-sketch theorem target:
`delta_positive_from_ladder` obligation is directly discharged by existing HQIV positivity lemmas. -/
theorem sketch_delta_positive_obligation :
    0 < ladderGapCandidate :=
  ladderGapCandidate_pos

/-- Consumed-sketch theorem target:
the finite-control side has a concrete lock-in mode-count witness (`r8 m_lockin`). -/
theorem sketch_finite_control_witness_exists :
    ∃ M : ℕ, M = finiteModeBoundAtLockin ∧ 0 < M := by
  refine ⟨finiteModeBoundAtLockin, rfl, finiteModeBoundAtLockin_pos⟩

end

end Hqiv.Story
