import Hqiv.Story.QuantumYangMillsFromPatchHQIV

/-!
# HQIV-aligned Dojo Yang-Mills interface witness

Stable **names** for the Dojo `QuantumYangMillsTheory` slot live here. The construction is
promoted through `Hqiv.Story.QuantumYangMillsFromPatchHQIV`, which exposes the HQIV patch jet
`hqivPatchJetOperatorValuedDistribution` alongside the certified interface witness.
-/

namespace Hqiv.Story

open MillenniumYangMillsDefs
open Hqiv.Story.QuantumYangMillsFromPatchHQIV

namespace QuantumYangMillsHQIVInterface

/-- HQIV-facing alias for the certified Dojo-shaped `QuantumYangMillsTheory` interface witness. -/
noncomputable abbrev hqivInterfaceQuantumYangMills
    (G : Type) [CompactSimpleGaugeGroup G] : QuantumYangMillsTheory G :=
  QuantumYangMillsFromPatchHQIV.hqivInterfaceQuantumYangMills G

/-- Constructive nonemptiness of the Dojo `QuantumYangMillsTheory` slot, through the
current HQIV interface witness. -/
theorem nonempty_hqivInterface_quantumYangMills
    (G : Type) [CompactSimpleGaugeGroup G] :
    Nonempty (QuantumYangMillsTheory G) :=
  QuantumYangMillsFromPatchHQIV.nonempty_hqivInterface_quantumYangMills G

end QuantumYangMillsHQIVInterface
end Hqiv.Story

