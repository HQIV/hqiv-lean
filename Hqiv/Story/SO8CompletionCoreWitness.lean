import Hqiv.Story.YMCompletionCoreSO8

/-!
# SO(8) completion-core witness scaffold

This file is the constructor-facing scaffold for the last missing input to the SO(8) YM endpoint:

`Nonempty (ClayYangMillsCompletionData HQIVSO8Gauge)`.

It does not add axioms; it packages the exact fields that must be supplied and gives the immediate
bridge theorem to `YangMillsExistenceAndMassGap HQIVSO8Gauge`.
-/

namespace Hqiv.Story

open Hqiv.Story.MassGapCompletion
open MillenniumYangMills MillenniumYangMillsDefs

noncomputable section

/-- Field-by-field obligations for constructing an SO(8) completion core. -/
structure SO8CompletionCoreObligations : Type 2 where
  qft : QuantumYangMillsTheory HQIVSO8Gauge
  Δ : ℝ
  hExist : ClayExistence qft
  hGap : HasMassGapSpectrum HQIVSO8Gauge qft Δ
  hFin : FiniteMassSpectrum HQIVSO8Gauge qft

/-- Build `SO8CompletionCore` from explicit obligations. -/
def mkSO8CompletionCore (h : SO8CompletionCoreObligations) : SO8CompletionCore :=
  { qft := h.qft
    Δ := h.Δ
    hExist := h.hExist
    hGap := h.hGap
    hFin := h.hFin }

/-- The obligations package is exactly what is needed for nonempty completion data. -/
theorem so8CompletionCoreNonempty_of_obligations
    (h : SO8CompletionCoreObligations) :
    SO8CompletionCoreNonempty :=
  ⟨mkSO8CompletionCore h⟩

/-- Final SO(8) YM endpoint, parameterized by the explicit obligations package. -/
theorem yangMillsExistenceAndMassGap_of_so8_obligations
    (h : SO8CompletionCoreObligations) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge :=
  yangMillsExistenceAndMassGap_of_so8_completion_core_nonempty
    (so8CompletionCoreNonempty_of_obligations h)

/-- Convenience unpacking theorem for direct field-style use. -/
theorem yangMillsExistenceAndMassGap_of_so8_fields
    (qft : QuantumYangMillsTheory HQIVSO8Gauge) (Δ : ℝ)
    (hExist : ClayExistence qft)
    (hGap : HasMassGapSpectrum HQIVSO8Gauge qft Δ)
    (hFin : FiniteMassSpectrum HQIVSO8Gauge qft) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge :=
  yangMillsExistenceAndMassGap_of_so8_obligations
    { qft := qft, Δ := Δ, hExist := hExist, hGap := hGap, hFin := hFin }

end

end Hqiv.Story

