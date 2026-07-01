import HqivSpine.Physics.TuftBeltramiAnchor
import HqivSpine.Physics.GenerationDetunedLadder
import HqivSpine.Physics.GenerationResonanceLadder
import HqivSpine.Physics.ClosureAction
import HqivSpine.Physics.NowSliceCausalDiamond
import HqivSpine.Physics.LeptonAbsoluteScale
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.TuftBeltramiMassFunctional` — Beltrami mass label from the TUFT chart diamond

`TuftBeltramiAnchor` pinned the spectral label `λ_min(n) = d_n = n+1`. This module ties that label to
the **causal-diamond chart** and the **Hopf carrier layer**:

1. Generation `n` sits on TUFT chart row `m = tuftChartShell n = n+1`.
2. The balanced-horizon diamond event at that row has coordinate age `t = m = λ_min(n)`.
3. With `φ = 1`, `Φ = 0` on the reference null template through lock-in, the apex lapse is
   `N = 1 + t = λ_min(n) + 1` — one unit above the Beltrami label (the diamond opening offset).
4. **Mass readout** at lock-in uses the universal lock-in lapse `N = 5` times the chart/Beltrami
   factor `λ_min(n)` — the same rule recorded in `LeptonAbsoluteScale`.

**Honest scope.** This derives the **chart ↔ Beltrami ↔ diamond** identification and shows the
lepton bookkeeping rule is the TUFT mass functional on the lock-in apex. Sector
`constituent − binding` on nested Hopf rows is discharged in `SectorNestedHopfBinding` (Hopf-weighted
`E_bind_at_hopf_shell`); this module keeps the carrier-layer alias `tuftHopfFiberWeight`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.TuftBeltramiMassFunctional

open HqivSpine.Physics
open HqivSpine.Physics.TuftBeltramiAnchor
open HqivSpine.Physics.CausalDiamond
open HqivSpine.Physics.GenerationDetunedLadder
open HqivSpine.Physics.GenerationResonanceLadder
open HqivSpine.Physics.LeptonAbsoluteScale
open HqivSpine.Physics.NowSliceFromLattice

/-! ## Causal-diamond events on TUFT chart rows -/

/-- **TUFT chart event** — balanced-horizon diamond apex at chart row `m = n+1`. -/
noncomputable def tuftChartEvent (n : ℕ) : Event :=
  horizonEventAtShell (tuftChartShell n)

theorem tuftChartEvent_shell (n : ℕ) :
    (tuftChartEvent n).shell = tuftChartShell n := rfl

theorem tuftChartReadout_shell (n : ℕ) :
    (readoutAtShell (tuftChartShell n)).shell = tuftChartShell n := rfl

/-- Chart-row index equals the Beltrami minimal label (as reals). -/
theorem tuftChartShell_eq_beltrami (n : ℕ) :
    (tuftChartShell n : ℝ) = tuftMinimalBeltramiEigenvalue n := by
  simp [tuftChartShell, tuftMinimalBeltramiEigenvalue, tuftFiberMultiplicity]

/-- **Dimensionless Beltrami mass factor** at Hopf winding `n`. -/
noncomputable def tuftBeltramiMassFactor (n : ℕ) : ℝ :=
  tuftMinimalBeltramiEigenvalue n

theorem tuftBeltramiMassFactor_eq_chartShell (n : ℕ) :
    tuftBeltramiMassFactor n = (tuftChartShell n : ℝ) :=
  tuftChartShell_eq_beltrami n

theorem tuftBeltramiMassFactor_eq_succ (n : ℕ) :
    tuftBeltramiMassFactor n = (n : ℝ) + 1 :=
  tuftMinimalBeltrami_eq_succ n

/-! ## Diamond apex data on chart rows (φ = 1, Φ = 0 through lock-in) -/

theorem tuftChartIntegrable_shell_le_lockin {n : ℕ} (hn : hopfIntegrableWinding n) :
    tuftChartShell n ≤ referenceM := by
  rcases hn with rfl | rfl | rfl
  · simp [tuftChartShell, referenceM_eq_four]
  · simp [tuftChartShell, referenceM_eq_four]
  · simp [tuftChartShell, referenceM_eq_four]

theorem tuftChartEvent_phi_one (n : ℕ) :
    (tuftChartEvent n).slice.phi = 1 := by
  unfold tuftChartEvent Event.slice
  exact nowSliceOf_phi _

theorem tuftChartEvent_bigPhi_zero {n : ℕ} (hn : hopfIntegrableWinding n) :
    (tuftChartEvent n).slice.bigPhi = 0 :=
  horizonEventAtShell_bigPhi_zero (tuftChartShell n) (tuftChartIntegrable_shell_le_lockin hn)

/-- Coordinate age on the chart row equals the Beltrami label. -/
theorem tuftChartEvent_coordinateAge_eq_beltrami (n : ℕ) :
    (tuftChartEvent n).slice.apparentAge = tuftBeltramiMassFactor n := by
  unfold tuftChartEvent tuftBeltramiMassFactor
  rw [horizonEventAtShell_apparentAge, tuftChartShell_eq_beltrami]

/-- Apex lapse on the chart row is one unit above the Beltrami label: `N = λ_min + 1`. -/
theorem tuftChartEvent_massUnit_eq_beltrami_succ {n : ℕ} (hn : hopfIntegrableWinding n) :
    (tuftChartEvent n).slice.massUnit = tuftBeltramiMassFactor n + 1 := by
  have hΦ := tuftChartEvent_bigPhi_zero hn
  have hφ := tuftChartEvent_phi_one n
  have ht := tuftChartEvent_coordinateAge_eq_beltrami n
  rw [NowSlice.massUnit_eq, hΦ, hφ, ht]
  ring

theorem tuftChartEvent_massUnit_lockin :
    (tuftChartEvent hopfLockinWinding).slice.massUnit = tuftBeltramiMassFactor hopfLockinWinding + 1 := by
  exact tuftChartEvent_massUnit_eq_beltrami_succ hopfIntegrableWinding_three

theorem tuftChartEvent_massUnit_heavy_eq_five :
    (tuftChartEvent hopfLockinWinding).slice.massUnit = 5 := by
  rw [tuftChartEvent_massUnit_lockin, tuftBeltramiMassFactor_eq_succ, hopfLockinWinding]
  norm_num

/-! ## Hopf fiber localization (carrier layer) -/

/-- Hopf fiber–base weight `n/(n+2)` at the same winding (`ClosureAction`). -/
noncomputable def tuftHopfFiberWeight (n : ℕ) : ℝ := hopfFibrationShape n

theorem tuftHopfFiberWeight_eq (n : ℕ) : tuftHopfFiberWeight n = (n : ℝ) / (n + 2) := rfl

theorem tuftHopfFiberWeight_pos {n : ℕ} (hn : 0 < n) : 0 < tuftHopfFiberWeight n :=
  hopfFibrationShape_pos hn

/-! ## Lock-in mass readout functional -/

/-- **TUFT Beltrami mass readout** on slice `s` at winding `n`. -/
noncomputable def tuftBeltramiMassReadout (s : NowSlice) (n : ℕ) : ℝ :=
  s.readout (tuftBeltramiMassFactor n)

theorem tuftBeltramiMassReadout_eq (s : NowSlice) (n : ℕ) :
    tuftBeltramiMassReadout s n = s.massUnit * tuftBeltramiMassFactor n := by
  unfold tuftBeltramiMassReadout tuftBeltramiMassFactor
  rfl

/-- Lepton readout = heavy-hopf TUFT readout × resonance descent from shell ladder. -/
theorem leptonMassReadout_eq_tuftBeltrami_resonance (s : NowSlice) (g : LeptonGeneration) :
    leptonMassReadout s g =
      tuftBeltramiMassReadout s 3 * detunedHopfWeight 3 / generationResonanceDescent g.winding := by
  rw [leptonMassReadout_eq, tuftBeltramiMassReadout_eq,
    generationResonanceMassFactor_eq_anchor_over_descent
      (by rcases g with _ | _ | _ <;> simp [LeptonGeneration.winding]),
    generationMassFactor_heavy, detunedHopfWeight_heavy, tuftBeltramiMassFactor_eq_succ]
  ring

theorem lockin_leptonMassReadout_eq_tuft_resonance (g : LeptonGeneration) :
    leptonMassReadout lockinNowSlice g =
      tuftBeltramiMassReadout lockinNowSlice 3 * detunedHopfWeight 3 /
        generationResonanceDescent g.winding :=
  leptonMassReadout_eq_tuftBeltrami_resonance lockinNowSlice g

/-! ## Generation steps from the chart functional -/

theorem tuftBeltramiMassReadout_ratio (s : NowSlice) (n₁ n₂ : ℕ) (hN : s.massUnit ≠ 0) :
    tuftBeltramiMassReadout s n₂ / tuftBeltramiMassReadout s n₁ =
      tuftBeltramiMassFactor n₂ / tuftBeltramiMassFactor n₁ := by
  rw [tuftBeltramiMassReadout_eq, tuftBeltramiMassReadout_eq]
  field_simp [hN]

theorem tuftBeltramiMassReadout_mu_e (s : NowSlice) (hN : s.massUnit ≠ 0) :
    tuftBeltramiMassReadout s 2 / tuftBeltramiMassReadout s 1 = (3 : ℝ) / 2 := by
  calc
    tuftBeltramiMassReadout s 2 / tuftBeltramiMassReadout s 1
        = tuftBeltramiMassFactor 2 / tuftBeltramiMassFactor 1 :=
      tuftBeltramiMassReadout_ratio s 1 2 hN
    _ = (3 : ℝ) / 2 := by simp [tuftBeltramiMassFactor_eq_succ]; norm_num

theorem tuftBeltramiMassReadout_tau_mu (s : NowSlice) (hN : s.massUnit ≠ 0) :
    tuftBeltramiMassReadout s 3 / tuftBeltramiMassReadout s 2 = (4 : ℝ) / 3 := by
  calc
    tuftBeltramiMassReadout s 3 / tuftBeltramiMassReadout s 2
        = tuftBeltramiMassFactor 3 / tuftBeltramiMassFactor 2 :=
      tuftBeltramiMassReadout_ratio s 2 3 hN
    _ = (4 : ℝ) / 3 := by simp [tuftBeltramiMassFactor_eq_succ]; norm_num

/-! ## Capstone -/

/-- **TUFT/Beltrami mass-functional closure** — chart row, diamond apex, and readout factor aligned. -/
structure TuftBeltramiMassFunctionalClosure where
  /-- Chart index equals Beltrami label. -/
  chart_eq_beltrami : ∀ n, (tuftChartShell n : ℝ) = tuftMinimalBeltramiEigenvalue n
  /-- Coordinate age on the chart event equals `λ_min`. -/
  coordinate_age : ∀ n, (tuftChartEvent n).slice.apparentAge = tuftBeltramiMassFactor n
  /-- Balanced chart lapse `N = λ_min + 1` on integrable windings. -/
  chart_lapse_offset :
    ∀ {n}, hopfIntegrableWinding n →
      (tuftChartEvent n).slice.massUnit = tuftBeltramiMassFactor n + 1
  /-- Heavy chart at lock-in: `N = 5`, `λ_min = 4`. -/
  heavy_lockin :
    (tuftChartEvent hopfLockinWinding).slice.massUnit = 5 ∧
    tuftBeltramiMassFactor hopfLockinWinding = 4
  /-- Lepton readout = heavy-hopf TUFT readout × resonance descent from shell ladder. -/
  lepton_matches :
    ∀ (s : NowSlice) (g : LeptonGeneration),
      leptonMassReadout s g =
        tuftBeltramiMassReadout s 3 * detunedHopfWeight 3 / generationResonanceDescent g.winding

def tuftBeltramiMassFunctionalClosure : TuftBeltramiMassFunctionalClosure where
  chart_eq_beltrami := fun n => tuftChartShell_eq_beltrami n
  coordinate_age := fun n => tuftChartEvent_coordinateAge_eq_beltrami n
  chart_lapse_offset := fun hn => tuftChartEvent_massUnit_eq_beltrami_succ hn
  heavy_lockin :=
    ⟨tuftChartEvent_massUnit_heavy_eq_five, by
      rw [tuftBeltramiMassFactor_eq_succ, hopfLockinWinding]; norm_num⟩
  lepton_matches := fun s g => leptonMassReadout_eq_tuftBeltrami_resonance s g

end HqivSpine.Physics.TuftBeltramiMassFunctional
