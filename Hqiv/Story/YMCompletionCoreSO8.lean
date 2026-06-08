import Hqiv.Story.HQIVSO8GaugeGroupConstruction
import Hqiv.Story.YMRemainingObligations

/-!
# SO(8) completion-core endpoint for YM

This module specializes the generic completion-data bridge to the concrete SO(8) gauge carrier
`HQIVSO8Gauge`.

The remaining hard ingredient is a witness of
`Nonempty (ClayYangMillsCompletionData HQIVSO8Gauge)`.
Once provided, the Clay `YangMillsExistenceAndMassGap` target follows immediately.

Use `Hqiv.Story.SO8CompletionCoreWitness` for a field-by-field constructor scaffold.
-/

namespace Hqiv.Story

open Hqiv.Story.MassGapCompletion
open MillenniumYangMills

noncomputable section

/-- Typed completion-core carrier specialized to the SO(8) gauge choice. -/
abbrev SO8CompletionCore : Type 2 :=
  ClayYangMillsCompletionData HQIVSO8Gauge

/-- Minimal "final-mile" witness needed to close the YM target for SO(8). -/
abbrev SO8CompletionCoreNonempty : Prop :=
  Nonempty SO8CompletionCore

/-- If an SO(8) completion core is available, the Clay YM target is obtained immediately. -/
theorem yangMillsExistenceAndMassGap_of_so8_completion_core
    (core : SO8CompletionCore) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge :=
  yangMillsExistenceAndMassGap_of_completion_core (G := HQIVSO8Gauge) core

/-- Nonempty completion-data witness form of the same endpoint theorem. -/
theorem yangMillsExistenceAndMassGap_of_so8_completion_core_nonempty
    (hCore : SO8CompletionCoreNonempty) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge := by
  rcases hCore with ⟨core⟩
  exact yangMillsExistenceAndMassGap_of_so8_completion_core core

/-- Equivalent formulation: SO(8) completion-data nonemptiness matches the Clay YM proposition. -/
theorem so8_yangMillsExistenceAndMassGap_iff_completion_core_nonempty :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge ↔
      SO8CompletionCoreNonempty :=
  yangMillsExistenceAndMassGap_iff_nonempty_completionData HQIVSO8Gauge

end

end Hqiv.Story

