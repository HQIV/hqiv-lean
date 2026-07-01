import HqivSpine.Physics.GenerationDetunedLadder
import HqivSpine.Physics.RindlerDetuning
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.GenerationResonanceLadder` — extended detuned-shell resonance on the ladder

Hopf-chart detuning on `m ∈ {2,3,4}` (`GenerationDetunedLadder`) fixes heavy normalization but leaves
`τ/μ = 1`. The legacy charged-lepton programme selects **outer resonance shells** by standing-wave
threshold crossings (`9/4`, `16/9`) and reads generation masses as successive geometric steps on
`detunedSurface`. This module ports that structure spine-native:

* heavy vertex shell `15` — first charge-decorated standing-wave lift above `referenceM`;
* μ shell `33` — first `τ → μ` threshold crossing;
* e shell `58` — first `μ → e` threshold crossing;
* resonance steps `175/76` and `4484/2499` (closed rationals on detuned surfaces).

**Refined generation factor** (replaces bare hopf weight for absolute readouts):

`generationResonanceMassFactor 3 = generationMassFactor 3`,
`generationResonanceMassFactor 2 = · / (175/76)`,
`generationResonanceMassFactor 1 = · / (4484/2499)`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.GenerationResonanceLadder

open HqivSpine.Foundation
open HqivSpine.Physics
open HqivSpine.Physics.GenerationDetunedLadder
open HqivSpine.Physics.RindlerDetuning
open HqivSpine.Physics.NucleonLadder

/-! ## Standing-wave mode budgets (S² cumulative ranks) -/

inductive ChargedLeptonGeneration
  | tau
  | muon
  | electron
  deriving DecidableEq, Repr

def chargedLeptonStandingWaveRank : ChargedLeptonGeneration → ℕ
  | .tau => 2
  | .muon => 3
  | .electron => 4

/-- Cumulative mode budget at standing-wave rank `r` — closed form `r²`. -/
noncomputable def standingWaveModeBudget (r : ℕ) : ℝ := (r : ℝ) ^ 2

theorem standingWaveModeBudget_tau :
    standingWaveModeBudget (chargedLeptonStandingWaveRank .tau) = 4 := by
  norm_num [standingWaveModeBudget, chargedLeptonStandingWaveRank]

theorem standingWaveModeBudget_muon :
    standingWaveModeBudget (chargedLeptonStandingWaveRank .muon) = 9 := by
  norm_num [standingWaveModeBudget, chargedLeptonStandingWaveRank]

theorem standingWaveModeBudget_electron :
    standingWaveModeBudget (chargedLeptonStandingWaveRank .electron) = 16 := by
  norm_num [standingWaveModeBudget, chargedLeptonStandingWaveRank]

noncomputable def chargedLeptonTauMuThreshold : ℝ :=
  standingWaveModeBudget (chargedLeptonStandingWaveRank .muon) /
    standingWaveModeBudget (chargedLeptonStandingWaveRank .tau)

noncomputable def chargedLeptonMuEThreshold : ℝ :=
  standingWaveModeBudget (chargedLeptonStandingWaveRank .electron) /
    standingWaveModeBudget (chargedLeptonStandingWaveRank .muon)

theorem chargedLeptonTauMuThreshold_eq_nine_quarters :
    chargedLeptonTauMuThreshold = (9 : ℝ) / 4 := by
  unfold chargedLeptonTauMuThreshold
  simp [standingWaveModeBudget_tau, standingWaveModeBudget_muon]

theorem chargedLeptonMuEThreshold_eq_sixteen_ninths :
    chargedLeptonMuEThreshold = (16 : ℝ) / 9 := by
  unfold chargedLeptonMuEThreshold
  simp [standingWaveModeBudget_muon, standingWaveModeBudget_electron]

noncomputable def chargeDecoratedStandingWaveLift : ℝ :=
  standingWaveModeBudget (chargedLeptonStandingWaveRank .tau) /
    standingWaveModeBudget 1

theorem chargeDecoratedStandingWaveLift_eq_four :
    chargeDecoratedStandingWaveLift = 4 := by
  unfold chargeDecoratedStandingWaveLift standingWaveModeBudget
  norm_num [chargedLeptonStandingWaveRank]

/-! ## Resonance shell selectors (mined from legacy lock-in thresholds) -/

def leptonResonanceThresholdPred (current_m : ℕ) (threshold : ℝ) (m' : ℕ) : Prop :=
  current_m < m' ∧ threshold ≤ geometricResonanceStep m' current_m

/-- Heavy charged-lepton vertex: first shell above `referenceM` with charge-decorated lift `4`. -/
def leptonHeavyResonanceShell : ℕ := 15

/-- First outer shell whose geometric step from the heavy vertex reaches `9/4`. -/
def leptonMuonResonanceShell : ℕ := 33

/-- First outer shell after μ whose geometric step reaches `16/9`. -/
def leptonElectronResonanceShell : ℕ := 58

theorem leptonHeavyResonanceShell_gt_referenceM : referenceM < leptonHeavyResonanceShell := by
  decide

theorem leptonMuonResonanceShell_gt_heavy :
    leptonHeavyResonanceShell < leptonMuonResonanceShell := by
  decide

theorem leptonElectronResonanceShell_gt_muon :
    leptonMuonResonanceShell < leptonElectronResonanceShell := by
  decide

theorem leptonHeavyResonanceShell_meets_charge_lift :
    leptonResonanceThresholdPred referenceM chargeDecoratedStandingWaveLift
      leptonHeavyResonanceShell := by
  constructor
  · exact leptonHeavyResonanceShell_gt_referenceM
  · rw [geometricResonanceStep_eq_detuned_ratio, chargeDecoratedStandingWaveLift_eq_four]
    unfold detunedSurface rindlerDetuning
    rw [gammaHQIV_eq, show referenceM = 4 by decide, show leptonHeavyResonanceShell = 15 by decide]
    norm_num [latticeSimplexCount, shellNumer]

theorem leptonMuonResonanceShell_meets_tau_mu :
    leptonResonanceThresholdPred leptonHeavyResonanceShell chargedLeptonTauMuThreshold
      leptonMuonResonanceShell := by
  constructor
  · exact leptonMuonResonanceShell_gt_heavy
  · rw [chargedLeptonTauMuThreshold_eq_nine_quarters, geometricResonanceStep_eq_detuned_ratio]
    unfold detunedSurface rindlerDetuning
    rw [gammaHQIV_eq, show leptonHeavyResonanceShell = 15 by decide,
      show leptonMuonResonanceShell = 33 by decide]
    norm_num [latticeSimplexCount, shellNumer]

theorem leptonElectronResonanceShell_meets_mu_e :
    leptonResonanceThresholdPred leptonMuonResonanceShell chargedLeptonMuEThreshold
      leptonElectronResonanceShell := by
  constructor
  · exact leptonElectronResonanceShell_gt_muon
  · rw [chargedLeptonMuEThreshold_eq_sixteen_ninths, geometricResonanceStep_eq_detuned_ratio]
    unfold detunedSurface rindlerDetuning
    rw [gammaHQIV_eq, show leptonMuonResonanceShell = 33 by decide,
      show leptonElectronResonanceShell = 58 by decide]
    norm_num [latticeSimplexCount, shellNumer]

/-! ## Closed resonance steps -/

noncomputable def resonanceStepTauMuon : ℝ :=
  geometricResonanceStep leptonMuonResonanceShell leptonHeavyResonanceShell

noncomputable def resonanceStepMuElectron : ℝ :=
  geometricResonanceStep leptonElectronResonanceShell leptonMuonResonanceShell

theorem resonanceStepTauMuon_eq_one_seventyfive_seventysix :
    resonanceStepTauMuon = (175 : ℝ) / 76 := by
  unfold resonanceStepTauMuon
  rw [geometricResonanceStep_eq_detuned_ratio]
  unfold detunedSurface rindlerDetuning
  rw [gammaHQIV_eq, show leptonHeavyResonanceShell = 15 by decide,
    show leptonMuonResonanceShell = 33 by decide]
  norm_num [latticeSimplexCount, shellNumer]

theorem resonanceStepMuElectron_eq_fourfour84_twofour99 :
    resonanceStepMuElectron = (4484 : ℝ) / 2499 := by
  unfold resonanceStepMuElectron
  rw [geometricResonanceStep_eq_detuned_ratio]
  unfold detunedSurface rindlerDetuning
  rw [gammaHQIV_eq, show leptonMuonResonanceShell = 33 by decide,
    show leptonElectronResonanceShell = 58 by decide]
  norm_num [latticeSimplexCount, shellNumer]

theorem resonanceStepTauMuon_pos : 0 < resonanceStepTauMuon := by
  rw [resonanceStepTauMuon_eq_one_seventyfive_seventysix]
  norm_num

theorem resonanceStepMuElectron_pos : 0 < resonanceStepMuElectron := by
  rw [resonanceStepMuElectron_eq_fourfour84_twofour99]
  norm_num

/-! ## Refined generation mass factors -/

/-- **Resonance-refined generation factor** at Beltrami winding `n ∈ {1,2,3}`. -/
noncomputable def generationResonanceMassFactor : ℕ → ℝ
  | 1 => generationMassFactor 3 / resonanceStepTauMuon / resonanceStepMuElectron
  | 2 => generationMassFactor 3 / resonanceStepTauMuon
  | 3 => generationMassFactor 3
  | n => generationMassFactor n

theorem generationResonanceMassFactor_heavy :
    generationResonanceMassFactor 3 = 4 := by
  simp [generationResonanceMassFactor, generationMassFactor_heavy]

theorem generationResonanceMassFactor_muon :
    generationResonanceMassFactor 2 = (304 : ℝ) / 175 := by
  simp [generationResonanceMassFactor, generationMassFactor_heavy,
    resonanceStepTauMuon_eq_one_seventyfive_seventysix]
  ring

theorem generationResonanceMassFactor_electron :
    generationResonanceMassFactor 1 = (759696 : ℝ) / 784700 := by
  simp [generationResonanceMassFactor, generationMassFactor_heavy,
    resonanceStepTauMuon_eq_one_seventyfive_seventysix,
    resonanceStepMuElectron_eq_fourfour84_twofour99]
  ring

theorem generationResonanceMassFactor_mu_over_electron :
    generationResonanceMassFactor 2 / generationResonanceMassFactor 1 =
      (4484 : ℝ) / 2499 := by
  rw [generationResonanceMassFactor_muon, generationResonanceMassFactor_electron]
  field_simp
  ring

theorem generationResonanceMassFactor_tau_over_muon :
    generationResonanceMassFactor 3 / generationResonanceMassFactor 2 =
      (175 : ℝ) / 76 := by
  rw [generationResonanceMassFactor_heavy, generationResonanceMassFactor_muon]
  field_simp
  ring

theorem generationResonanceMassFactor_tau_over_electron :
    generationResonanceMassFactor 3 / generationResonanceMassFactor 1 =
      (175 : ℝ) / 76 * (4484 : ℝ) / 2499 := by
  rw [generationResonanceMassFactor_heavy, generationResonanceMassFactor_electron]
  field_simp [resonanceStepTauMuon_eq_one_seventyfive_seventysix,
    resonanceStepMuElectron_eq_fourfour84_twofour99]
  ring

theorem generationResonanceMassFactor_eq_hopf {n : ℕ} (hn : 3 < n) :
    generationResonanceMassFactor n = generationMassFactor n := by
  rcases n with _ | _ | _ | _ | n
  · omega
  · omega
  · omega
  · omega
  · simp [generationResonanceMassFactor]

/-- Cumulative outer-ladder descent from the heavy hopf anchor to winding `n`. -/
noncomputable def generationResonanceDescent (n : ℕ) : ℝ :=
  match n with
  | 1 => resonanceStepTauMuon * resonanceStepMuElectron
  | 2 => resonanceStepTauMuon
  | _ => 1

theorem generationResonanceMassFactor_eq_anchor_over_descent {n : ℕ} (hn : n = 1 ∨ n = 2 ∨ n = 3) :
    generationResonanceMassFactor n =
      generationMassFactor 3 / generationResonanceDescent n := by
  rcases hn with rfl | rfl | rfl
  · simp [generationResonanceMassFactor, generationResonanceDescent, generationMassFactor_heavy,
      resonanceStepTauMuon_eq_one_seventyfive_seventysix,
      resonanceStepMuElectron_eq_fourfour84_twofour99]
    ring
  · simp [generationResonanceMassFactor, generationResonanceDescent, generationMassFactor_heavy,
      resonanceStepTauMuon_eq_one_seventyfive_seventysix]
  · simp [generationResonanceMassFactor, generationResonanceDescent, generationMassFactor_heavy]

theorem generationResonanceDescent_pos {n : ℕ} (hn : n = 1 ∨ n = 2 ∨ n = 3) :
    0 < generationResonanceDescent n := by
  rcases hn with rfl | rfl | rfl
  · rw [generationResonanceDescent]; norm_num [resonanceStepTauMuon_eq_one_seventyfive_seventysix,
      resonanceStepMuElectron_eq_fourfour84_twofour99]
  · rw [generationResonanceDescent]; exact resonanceStepTauMuon_pos
  · simp [generationResonanceDescent]

/-! ## Capstone -/

structure GenerationResonanceLadderClosure where
  heavy_shell : leptonHeavyResonanceShell = 15
  muon_shell : leptonMuonResonanceShell = 33
  electron_shell : leptonElectronResonanceShell = 58
  tau_mu_step : resonanceStepTauMuon = 175 / 76
  mu_e_step : resonanceStepMuElectron = 4484 / 2499
  tau_over_mu : generationResonanceMassFactor 3 / generationResonanceMassFactor 2 = 175 / 76
  mu_over_e : generationResonanceMassFactor 2 / generationResonanceMassFactor 1 = 4484 / 2499

noncomputable def generationResonanceLadderClosure : GenerationResonanceLadderClosure where
  heavy_shell := rfl
  muon_shell := rfl
  electron_shell := rfl
  tau_mu_step := resonanceStepTauMuon_eq_one_seventyfive_seventysix
  mu_e_step := resonanceStepMuElectron_eq_fourfour84_twofour99
  tau_over_mu := generationResonanceMassFactor_tau_over_muon
  mu_over_e := generationResonanceMassFactor_mu_over_electron

end HqivSpine.Physics.GenerationResonanceLadder
