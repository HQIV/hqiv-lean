import Hqiv.Story.PatchHilbertBridge
import Hqiv.Story.DiscreteOMaxwellHQIVInstance
import Hqiv.Story.YMRemainingObligations

/-!
# O-Maxwell + patch QM → Dojo / YM slot (construction hub)

The **Dojo** side still wants a full `QuantumYangMillsTheory G` inside `ClayYangMillsCompletionData G`.
HQIV already separates the work into layers that *inform* that slot without pretending the Clay body
is constructed:

## Discrete shell (proved HQIV data → well dynamics)

* `DiscreteOMaxwellToYMInputs` packages an abstract `DiscreteOMaxwellShellAction` into
  `QuantumWellDynamics` plus `YMInputsFromWellDynamics` once a `ClayYangMillsCompletionData` core and
  consequence fields are supplied.
* `DiscreteOMaxwellHQIVInstance` instantiates the shell with `omega_k_at_horizon`, `shell_shape`, and
  the locked-in ladder anchors; `hqivDiscreteOMaxwellInvariants_holds` discharges the basic invariant
  record.

## Patch quantum mechanics (finite carrier ↔ Dojo Hilbert bridge)

* `LatticeHilbert 4` is the ℂ⁴ patch carrier (`Hqiv.QuantumMechanics.HorizonFreeFieldScaffold`).
* `HilbertPatchBridge` is the ℝ-linear sandwich link into any Dojo `QuantumYangMillsTheory.hilbertSpace`.
* `YMRemainingObligations` states the promotion / `localOperators` alignment obligations on top of
  that bridge.

## Continuum O-Maxwell + light-cone anchored QM/QFT (heavy hub — import only when needed)

* `Hqiv.Physics.LightConeMaxwellQFTBridge` is the single narrative import for **null ladder / continuum
  φ–Maxwell closure / horizon limits** feeding QM scaffolds (`ContinuumManyBodyQFTScaffold`,
  `HorizonLimitedRenormLocality`, `PatchQFTBridge`, …).  It is **not** imported here to keep the
  default Story spine light; pull it in when you add morphisms from continuum data into the Dojo
  types.

Use the `Hqiv.Story.OMaxwellQMToDojo` namespace below as stable **names** for “what fills the slot
informally today” while Clay+QFT axioms shrink.
-/

namespace Hqiv.Story

open Hqiv.QM
open Hqiv.Story.MassGapCompletion
open MillenniumYangMillsDefs

namespace OMaxwellQMToDojo

noncomputable section

/-- Patch QM carrier shared with `HilbertPatchBridge` / `YMRemainingObligations`. -/
abbrev PatchQM : Type :=
  LatticeHilbert 4

/-- HQIV discrete O-Maxwell shell action feeding `hqivWellDynamics`. -/
noncomputable def OMaxwellDiscreteShell : DiscreteOMaxwellShellAction HQIVAxis :=
  hqivDiscreteOMaxwellAction

/-- Induced well dynamics (`phaseStep` / `omega`) used by `YMInputsFromWellDynamics`. -/
noncomputable def OMaxwellWellDynamics : QuantumWellDynamics HQIVAxis :=
  hqivWellDynamics

/-- Invariant payload used when building `DiscreteOMaxwellYMBridgeData` / `ymInputsFromDiscreteOMaxwell`. -/
noncomputable def OMaxwellStoryInvariants : DiscreteOMaxwellInvariants HQIVAxis OMaxwellWellDynamics :=
  hqivDiscreteOMaxwellInvariants

/-- Convenience: the three basic invariants are already proved for the HQIV instance. -/
theorem OMaxwellStoryInvariants_holds :
    OMaxwellStoryInvariants.phase_lock_transport ∧
      OMaxwellStoryInvariants.curvature_self_support_transport ∧
      OMaxwellStoryInvariants.conserved_content_transport :=
  hqivDiscreteOMaxwellInvariants_holds

/-- After a Clay core is supplied, this is the same `YMInputsFromWellDynamics` packaging as
`hqivYMInputsFromDiscreteOMaxwell` (kept as a one-line anchor for search / refactoring). -/
noncomputable def ymInputsAfterClay {G : Type} [CompactSimpleGaugeGroup G]
    (core : ClayYangMillsCompletionData G) (hPatch hLocCov hOPE hDelta hGap hFin : Prop) :
    YMInputsFromWellDynamics G :=
  hqivYMInputsFromDiscreteOMaxwell core hPatch hLocCov hOPE hDelta hGap hFin

/-- Preferred constructor when you want the **existing patch QFT/QM corpus** to discharge the
promotion/spectral obligations directly:
use `YMRemainingObligations.hqivYMInputsFromDynamicsRemaining` (no raw `Prop` placeholders). -/
noncomputable def ymInputsAfterClay_fromPatchQFTQM
    {G : Type} [CompactSimpleGaugeGroup G] (core : ClayYangMillsCompletionData G) :
    YMInputsFromWellDynamics G :=
  hqivYMInputsFromDynamicsRemaining core

end

end OMaxwellQMToDojo

end Hqiv.Story
