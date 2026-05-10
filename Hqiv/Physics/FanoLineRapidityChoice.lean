import Hqiv.Physics.FanoLine
import Hqiv.Physics.TrialityRapidityWellEquivalence

namespace Hqiv.Physics

open Hqiv

/-!
# Programmatic Fano line choice from shell / rapidity readouts

The Fano plane at each tag vertex has **three** incident projective lines; see
`FanoLine.ofVertexChoice` in `FanoLine.lean` and the sorted label list
`incidentLineAt`.

A readout shell `m` yields a **triality tick** `m % 3` and hence cycles which of
the three lines is used. The **magnitude** of the expected small CP-odd
rapidity/curvature skew is `|rapidityCPBias m|` (same baryogenesis channel as
`TrialityRapidityWellEquivalence`); it is not used here as a continuous line
selector, only as an explicit **cross reference** to the `omega_k` / lock-in
story behind the double-well / Mexican-hat *scalar* layer.

`fanoLineFromVertexShell` is the single entry point you can use for **every**
`FanoVertex` and shell index.
-/

/-- Triality index from readout shell: `0,1,2,0,1,2,…` (canonical `m % 3` tick). -/
def shellRapidityIncidentIndex (m : ℕ) : Fin 3 :=
  ⟨m % 3, Nat.mod_lt m (by decide)⟩

/-- Fano line for vertex `v` with incident slot chosen from shell `m` (lock-in / rapidity readout). -/
def fanoLineFromVertexShell (v : FanoVertex) (m : ℕ) : FanoLine :=
  ofIndex (incidentLineAt v (shellRapidityIncidentIndex m))

theorem shellRapidityIncidentIndex_mod_three (m : ℕ) :
    (shellRapidityIncidentIndex m).val = m % 3 := rfl

theorem fanoLineFromVertexShell_eq_ofVertexChoice (v : FanoVertex) (m : ℕ) :
    fanoLineFromVertexShell v m = FanoLine.ofVertexChoice v (shellRapidityIncidentIndex m) := by
  simp [fanoLineFromVertexShell, FanoLine.ofVertexChoice]

theorem fanoLineFromVertexShell_eq_ofTag
    (v : FanoVertex) (m : ℕ) (h : m % 3 = 0) :
    fanoLineFromVertexShell v m = FanoLine.ofTag v := by
  have hj : shellRapidityIncidentIndex m = (0 : Fin 3) := by
    apply Fin.ext
    show (shellRapidityIncidentIndex m).val = (0 : Fin 3).val
    simpa [shellRapidityIncidentIndex, Fin.val_zero] using h
  calc
    fanoLineFromVertexShell v m
        = ofIndex (incidentLineAt v 0) := by simp [fanoLineFromVertexShell, hj]
    _ = ofIndex (incidentLineLabelLowest v) := by rw [incidentLineAt_zero_eq_lowest]
    _ = FanoLine.ofTag v := by simp [FanoLine.ofTag, FanoLine.ofIncidentVertex]

/-- CP-bias at `m` (baryogenesis / curvature ratio channel; same as quarter-period scaffolds). -/
noncomputable def rapidityLineCPBias (m : ℕ) : ℝ :=
  rapidityCPBias m

theorem rapidityLineCPBias_eq (m : ℕ) :
    rapidityLineCPBias m = omega_k_at_horizon m m_lockin - 1 := by
  simp [rapidityLineCPBias, rapidityCPBias_eq_curvature_ratio_minus_one]

end Hqiv.Physics
