import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.OctonionicZeta
import Hqiv.Physics.SurfaceWaveSelfClock
import Hqiv.Physics.ModalFrequencyHorizon
import Hqiv.Geometry.SphericalHarmonicsBridge
import Hqiv.Physics.SpinStatistics

namespace Hqiv.Physics

open scoped Real
open Hqiv

/-!
# Lepton generations parallel to quark lock-in (heavy vertex at the lock-in **readout**)

This module separates the **anchored** part of the charged-lepton story from the
still-open **outer-horizon placement** problem (which `ℕ` readout coordinates to use for μ/e).

**Conceptual framing:** three charged-lepton **species** come from the same **threefold generation
slot** as quarks (`Hqiv.Algebra.So8RepIndex` / triality in `SMEmbedding`—the **Spin(8) / octonion**
embedding formalized here). What this file pins is not “the τ particle lives on one integer,” but
**which horizon-area readout** anchors the heavy vertex: `referenceM` is the **export index** for that
evaluation. A standing-wave picture allows **support bands**; natural indices remain the **chart**
where `shellSurface` and detuned ratios are evaluated.

**Anchored now:** the τ-generation line is selected as the first shell at or above `referenceM`
that supports the charge-decorated standing-wave lift; μ and e are then selected by successive
standing-wave lifts (`τ→μ`, `μ→e`) instead of a fixed octave constant.

**Substrate trace:** `referenceM` unfolds to `qcdShell + latticeStepCount` in `OctonionicLightCone`;
those naturals are the **lowest substrate pins** in Lean, below `α`/`γ` and `T_lockin` formulas.

**Threshold rule (not Koide):** μ/e readouts are the first outer crossings where
`geometricResonanceStep` reaches standing-wave-lift thresholds derived from spherical-harmonic
cumulative mode budgets (`τ→μ = 9/4`, `μ→e = 16/9`). This keeps the selector tied to standing-wave
rank growth rather than fixed shell IDs.

Lock-in supplies the **birth** condition; `SurfaceWaveSelfClock` + rapidity updates model relaxation
along the horizon ladder.

**Charged-lepton resonance factors** (`effectiveSurface`, `resonance_k_*`, `m_tau_Pl` as τ mass
in `E_Pl = 1` units, …) live in `ChargedLeptonResonance`, using the outer-horizon selection exposed here.

This module therefore provides:
- a derived heavy-shell selector `leptonHeavyVertexShell` starting from `referenceM`,
- a reusable interface `OuterHorizonLeptonShellSelection` for future first-principles picks,
- a modal-frequency wrapper (`leptonModalFrequencySpec`) with horizon quarter-period compatibility, and
- a first derived threshold selector on the existing detuned-surface ladder,
- and the resulting order / temperature / resonance facts used downstream.
-/

/-- Spin-only baseline shell (neutrino-side readout chart). -/
def spinOnlyBaselineShell : ℕ := referenceM

/-- Standing-wave rank for the spin-only fermion rung. -/
def spinOnlyStandingWaveRank : ℕ := 1

/-- Standing-wave rank for the charge-decorated fermion rung. -/
def chargeDecoratedStandingWaveRank : ℕ := 2

/-- Charged-lepton generation labels for standing-wave rank assignment. -/
inductive ChargedLeptonGeneration
  | tau
  | muon
  | electron
  deriving DecidableEq, Repr

/-- Standing-wave rank by charged-lepton generation (same spin/statistics class, higher overtones outward). -/
def chargedLeptonStandingWaveRank : ChargedLeptonGeneration → ℕ
  | .tau => 2
  | .muon => 3
  | .electron => 4

/-- S² cumulative standing-wave mode budget at rank `r` (via `L = r - 1`). -/
noncomputable def standingWaveModeBudget (r : ℕ) : ℝ :=
  Hqiv.sphericalHarmonicCumulativeCount (r - 1)

theorem standingWaveModeBudget_spinOnly :
    standingWaveModeBudget spinOnlyStandingWaveRank = 1 := by
  unfold standingWaveModeBudget spinOnlyStandingWaveRank Hqiv.sphericalHarmonicCumulativeCount
  norm_num

theorem standingWaveModeBudget_chargeDecorated :
    standingWaveModeBudget chargeDecoratedStandingWaveRank = 4 := by
  unfold standingWaveModeBudget chargeDecoratedStandingWaveRank Hqiv.sphericalHarmonicCumulativeCount
  norm_num

theorem standingWaveModeBudget_tau :
    standingWaveModeBudget (chargedLeptonStandingWaveRank .tau) = 4 := by
  unfold standingWaveModeBudget chargedLeptonStandingWaveRank Hqiv.sphericalHarmonicCumulativeCount
  norm_num

theorem standingWaveModeBudget_muon :
    standingWaveModeBudget (chargedLeptonStandingWaveRank .muon) = 9 := by
  unfold standingWaveModeBudget chargedLeptonStandingWaveRank Hqiv.sphericalHarmonicCumulativeCount
  norm_num

theorem standingWaveModeBudget_electron :
    standingWaveModeBudget (chargedLeptonStandingWaveRank .electron) = 16 := by
  unfold standingWaveModeBudget chargedLeptonStandingWaveRank Hqiv.sphericalHarmonicCumulativeCount
  norm_num

/-- Quantum-number lift from spin-only to charge-decorated standing-wave content. -/
noncomputable def chargeDecoratedStandingWaveLift : ℝ :=
  standingWaveModeBudget chargeDecoratedStandingWaveRank /
    standingWaveModeBudget spinOnlyStandingWaveRank

theorem chargeDecoratedStandingWaveLift_eq_four :
    chargeDecoratedStandingWaveLift = 4 := by
  unfold chargeDecoratedStandingWaveLift
  rw [standingWaveModeBudget_chargeDecorated, standingWaveModeBudget_spinOnly]
  norm_num

/-- Charged-lepton modes are fermionic (half-integer spin class). -/
def chargedLeptonSpinClass : SpinClass := SpinClass.halfInteger

theorem chargedLeptonSpinClass_is_halfInteger :
    chargedLeptonSpinClass = SpinClass.halfInteger := rfl

/-- Generic threshold predicate for first-shell selectors on geometric resonance readouts. -/
def leptonResonanceThresholdPred (current_m : ℕ) (threshold : ℝ) (m' : ℕ) : Prop :=
  current_m < m' ∧ threshold ≤ geometricResonanceStep m' current_m

noncomputable instance decidable_leptonResonanceThresholdPred (current_m : ℕ) (threshold : ℝ)
    (m' : ℕ) : Decidable (leptonResonanceThresholdPred current_m threshold m') :=
  by
    classical
    infer_instance

theorem exists_leptonResonanceThresholdPred (current_m : ℕ) (threshold : ℝ) :
    ∃ m' : ℕ, leptonResonanceThresholdPred current_m threshold m' := by
  have hden : RindlerDenDeltaPos 0 current_m := by
    unfold RindlerDenDeltaPos rindlerDenWithDelta
    rw [c_rindler_shared_eq_one_fifth]
    have hm : (0 : ℝ) ≤ (current_m : ℝ) := Nat.cast_nonneg current_m
    nlinarith
  have heff0 : 0 < effCorrected 0 current_m := effCorrected_pos 0 current_m hden
  obtain ⟨m₀, hm₀⟩ := exists_eff_gt 0 (by norm_num) (threshold * effCorrected 0 current_m)
  let m' := max (current_m + 1) m₀
  refine ⟨m', ?_⟩
  constructor
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  · unfold geometricResonanceStep
    rw [← effCorrected_zero_eq_detunedShellSurface m',
      ← effCorrected_zero_eq_detunedShellSurface current_m,
      le_div_iff₀ heff0]
    have hm' : m₀ ≤ m' := Nat.le_max_right _ _
    have heff1 : effCorrected 0 m₀ ≤ effCorrected 0 m' := by
      by_cases hlt : m₀ < m'
      · exact (effCorrected_strictMono_nat (by norm_num) hlt).le
      · have hle' : m' ≤ m₀ := Nat.not_lt.mp hlt
        have heq : m₀ = m' := Nat.le_antisymm hm' hle'
        rw [heq]
    exact (lt_of_lt_of_le hm₀ heff1).le

/-- First shell after `current_m` whose geometric resonance step clears `threshold`. -/
noncomputable def firstShellAtOrAboveResonanceThreshold (current_m : ℕ) (threshold : ℝ) : ℕ :=
  Nat.find (exists_leptonResonanceThresholdPred current_m threshold)

theorem firstShellAtOrAboveResonanceThreshold_spec (current_m : ℕ) (threshold : ℝ) :
    leptonResonanceThresholdPred current_m threshold
      (firstShellAtOrAboveResonanceThreshold current_m threshold) :=
  Nat.find_spec (exists_leptonResonanceThresholdPred current_m threshold)

theorem firstShellAtOrAboveResonanceThreshold_gt (current_m : ℕ) (threshold : ℝ) :
    current_m < firstShellAtOrAboveResonanceThreshold current_m threshold :=
  (firstShellAtOrAboveResonanceThreshold_spec current_m threshold).1

theorem firstShellAtOrAboveResonanceThreshold_min (current_m : ℕ) (threshold : ℝ) {m' : ℕ}
    (hm : leptonResonanceThresholdPred current_m threshold m') :
    firstShellAtOrAboveResonanceThreshold current_m threshold ≤ m' :=
  Nat.find_min' (exists_leptonResonanceThresholdPred current_m threshold) hm

/--
Heavy charged-lepton shell from standing-wave quantum numbers:
the first shell above the spin-only baseline where the geometric resonance readout
reaches the charge-decorated standing-wave lift (`4`).
-/
noncomputable def leptonHeavyVertexShell : ℕ :=
  firstShellAtOrAboveResonanceThreshold spinOnlyBaselineShell chargeDecoratedStandingWaveLift

/-- Interface for a charged-lepton shell selection on the outer horizon. -/
structure OuterHorizonLeptonShellSelection where
  muonShell : ℕ
  electronShell : ℕ
  heavy_lt_muon : leptonHeavyVertexShell < muonShell
  muon_lt_electron : muonShell < electronShell

/--
Modal wrapper at the τ/lock-in vertex.

The current implementation uses the nominal self-clock frequency at `referenceM` as its readout
source while keeping the interaction horizon relation explicit.
-/
noncomputable def leptonModalFrequencySpec : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal leptonHeavyVertexShell

theorem leptonModalFrequencySpec_quarterPhase_eq_horizonQuarter :
    leptonModalFrequencySpec.nominalOmega * leptonModalFrequencySpec.interactionQuarterPeriod =
      Hqiv.horizonQuarterPeriod := by
  simpa [leptonModalFrequencySpec] using
    (modalFrequencyHorizonFromShellNominal leptonHeavyVertexShell).quarterPhase_eq_horizonQuarter

theorem leptonModalFrequencySpec_detuning_affine (m : ℕ) :
    leptonModalFrequencySpec.detuning1Jet m = 1 + (gamma_HQIV / 2) * (m : ℝ) := by
  simpa [leptonModalFrequencySpec] using
    (modalFrequencyHorizonFromShellNominal_detuning_affine leptonHeavyVertexShell) m

/-- Current provisional μ shell witness (one rung above heavy selector). -/
noncomputable def provisionalLeptonMuonShell : ℕ := leptonHeavyVertexShell + 1

/-- Current provisional e shell witness (one rung above provisional μ). -/
noncomputable def provisionalLeptonElectronShell : ℕ := provisionalLeptonMuonShell + 1

/-- Standing-wave lift from τ to μ generation. -/
noncomputable def chargedLeptonTauMuStandingWaveLift : ℝ :=
  standingWaveModeBudget (chargedLeptonStandingWaveRank .muon) /
    standingWaveModeBudget (chargedLeptonStandingWaveRank .tau)

/-- Standing-wave lift from μ to e generation. -/
noncomputable def chargedLeptonMuEStandingWaveLift : ℝ :=
  standingWaveModeBudget (chargedLeptonStandingWaveRank .electron) /
    standingWaveModeBudget (chargedLeptonStandingWaveRank .muon)

/-- Threshold for the first τ → μ crossing from standing-wave rank lift. -/
noncomputable def chargedLeptonTauMuThreshold : ℝ := chargedLeptonTauMuStandingWaveLift

/-- Threshold for the first μ → e crossing from standing-wave rank lift. -/
noncomputable def chargedLeptonMuEThreshold : ℝ := chargedLeptonMuEStandingWaveLift

theorem chargedLeptonTauMuThreshold_value :
    chargedLeptonTauMuThreshold = (9 : ℝ) / 4 := by
  unfold chargedLeptonTauMuThreshold chargedLeptonTauMuStandingWaveLift
  simp [standingWaveModeBudget_muon, standingWaveModeBudget_tau]

theorem chargedLeptonMuEThreshold_value :
    chargedLeptonMuEThreshold = (16 : ℝ) / 9 := by
  unfold chargedLeptonMuEThreshold chargedLeptonMuEStandingWaveLift
  simp [standingWaveModeBudget_electron, standingWaveModeBudget_muon]

theorem chargedLeptonTauMuThreshold_gt_one : 1 < chargedLeptonTauMuThreshold := by
  rw [chargedLeptonTauMuThreshold_value]
  norm_num

theorem chargedLeptonMuEThreshold_gt_one : 1 < chargedLeptonMuEThreshold := by
  rw [chargedLeptonMuEThreshold_value]
  norm_num

/-- At `δ = 0`, the shared Rindler denominator is positive on every shell. -/
theorem rindlerDenDeltaPos_zero (m : ℕ) : RindlerDenDeltaPos 0 m := by
  unfold RindlerDenDeltaPos rindlerDenWithDelta
  rw [c_rindler_shared_eq_one_fifth]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-- The undetuned geometric resonance step is the `δ = 0` corrected surface ratio. -/
theorem geometricResonanceStep_eq_effCorrected_zero_ratio (m_from m_to : ℕ) :
    geometricResonanceStep m_from m_to = effCorrected 0 m_from / effCorrected 0 m_to := by
  unfold geometricResonanceStep
  rw [effCorrected_zero_eq_detunedShellSurface, effCorrected_zero_eq_detunedShellSurface]

/-- Charge-decorated μ support on the outer ladder: first shell beyond the heavy τ shell whose
geometric resonance step clears the charged-lepton τ → μ threshold. -/
def chargeDecoratedMuonSupportPred (m' : ℕ) : Prop :=
  leptonResonanceThresholdPred leptonHeavyVertexShell chargedLeptonTauMuThreshold m'

/-- First outer shell whose τ-based geometric resonance step reaches the charged-lepton τ → μ threshold. -/
noncomputable def derivedLeptonMuonShell : ℕ :=
  firstShellAtOrAboveResonanceThreshold leptonHeavyVertexShell chargedLeptonTauMuThreshold

/-- First outer shell after μ whose geometric resonance step reaches the charged-lepton μ → e threshold. -/
noncomputable def derivedLeptonElectronShell : ℕ :=
  firstShellAtOrAboveResonanceThreshold derivedLeptonMuonShell chargedLeptonMuEThreshold

/-- Charge-decorated e support on the outer ladder: first shell beyond μ whose geometric
resonance step clears the charged-lepton μ → e threshold. -/
def chargeDecoratedElectronSupportPred (m' : ℕ) : Prop :=
  leptonResonanceThresholdPred derivedLeptonMuonShell chargedLeptonMuEThreshold m'

theorem derivedLeptonMuonShell_gt_heavy :
    leptonHeavyVertexShell < derivedLeptonMuonShell :=
  firstShellAtOrAboveResonanceThreshold_gt _ _

theorem derivedLeptonElectronShell_gt_muon :
    derivedLeptonMuonShell < derivedLeptonElectronShell :=
  firstShellAtOrAboveResonanceThreshold_gt _ _

theorem derivedLeptonMuonShell_meets_threshold :
    chargedLeptonTauMuThreshold ≤
      geometricResonanceStep derivedLeptonMuonShell leptonHeavyVertexShell :=
  (firstShellAtOrAboveResonanceThreshold_spec _ _).2

theorem derivedLeptonElectronShell_meets_threshold :
    chargedLeptonMuEThreshold ≤
      geometricResonanceStep derivedLeptonElectronShell derivedLeptonMuonShell :=
  (firstShellAtOrAboveResonanceThreshold_spec _ _).2

theorem derivedLeptonMuonShell_is_chargeDecorated_support :
    chargeDecoratedMuonSupportPred derivedLeptonMuonShell := by
  simpa [chargeDecoratedMuonSupportPred, derivedLeptonMuonShell] using
    (firstShellAtOrAboveResonanceThreshold_spec leptonHeavyVertexShell chargedLeptonTauMuThreshold)

theorem derivedLeptonElectronShell_is_chargeDecorated_support :
    chargeDecoratedElectronSupportPred derivedLeptonElectronShell := by
  simpa [chargeDecoratedElectronSupportPred, derivedLeptonElectronShell] using
    (firstShellAtOrAboveResonanceThreshold_spec derivedLeptonMuonShell chargedLeptonMuEThreshold)

theorem derivedLeptonMuonShell_is_first_threshold_crossing {m' : ℕ}
    (hm : leptonResonanceThresholdPred leptonHeavyVertexShell chargedLeptonTauMuThreshold m') :
    derivedLeptonMuonShell ≤ m' :=
  firstShellAtOrAboveResonanceThreshold_min _ _ hm

theorem derivedLeptonElectronShell_is_first_threshold_crossing {m' : ℕ}
    (hm : leptonResonanceThresholdPred derivedLeptonMuonShell chargedLeptonMuEThreshold m') :
    derivedLeptonElectronShell ≤ m' :=
  firstShellAtOrAboveResonanceThreshold_min _ _ hm

theorem derivedLeptonMuonShell_is_first_chargeDecorated_support {m' : ℕ}
    (hm : chargeDecoratedMuonSupportPred m') :
    derivedLeptonMuonShell ≤ m' :=
  derivedLeptonMuonShell_is_first_threshold_crossing (by simpa [chargeDecoratedMuonSupportPred] using hm)

theorem derivedLeptonElectronShell_is_first_chargeDecorated_support {m' : ℕ}
    (hm : chargeDecoratedElectronSupportPred m') :
    derivedLeptonElectronShell ≤ m' :=
  derivedLeptonElectronShell_is_first_threshold_crossing
    (by simpa [chargeDecoratedElectronSupportPred] using hm)

/-- Present shell-selection witness used by the charged-lepton modules until a derived rule exists. -/
noncomputable def provisionalOuterHorizonLeptonShellSelection : OuterHorizonLeptonShellSelection where
  muonShell := provisionalLeptonMuonShell
  electronShell := provisionalLeptonElectronShell
  heavy_lt_muon := by
    simp [provisionalLeptonMuonShell]
  muon_lt_electron := by
    simp [provisionalLeptonElectronShell]

/-- Threshold-derived shell-selection witness exported to downstream resonance modules. -/
noncomputable def thresholdDerivedOuterHorizonLeptonShellSelection : OuterHorizonLeptonShellSelection where
  muonShell := derivedLeptonMuonShell
  electronShell := derivedLeptonElectronShell
  heavy_lt_muon := derivedLeptonMuonShell_gt_heavy
  muon_lt_electron := derivedLeptonElectronShell_gt_muon

/-- The exported charged-lepton shell selector is exactly the first charge-decorated support rule
on the current exact-shell proxy. -/
theorem thresholdDerivedOuterHorizonLeptonShellSelection_realizes_chargeDecorated_support :
    chargeDecoratedMuonSupportPred thresholdDerivedOuterHorizonLeptonShellSelection.muonShell ∧
      chargeDecoratedElectronSupportPred thresholdDerivedOuterHorizonLeptonShellSelection.electronShell := by
  exact ⟨derivedLeptonMuonShell_is_chargeDecorated_support,
    derivedLeptonElectronShell_is_chargeDecorated_support⟩

/-- Active shell-selection witness exported to downstream resonance modules. -/
noncomputable def currentOuterHorizonLeptonShellSelection : OuterHorizonLeptonShellSelection :=
  thresholdDerivedOuterHorizonLeptonShellSelection

/--
Modal readout map used by the current lepton selectors.

For now this is a thin compatibility wrapper: threshold-derived shell selection remains the active
implementation, and this map records that it is consumed as a readout from the modal interface.
-/
noncomputable def outerHorizonLeptonShellSelectionFromModal
    (_spec : ModalFrequencyHorizonSpec) : OuterHorizonLeptonShellSelection :=
  thresholdDerivedOuterHorizonLeptonShellSelection

theorem currentOuterHorizonLeptonShellSelection_eq_modal_readout :
    currentOuterHorizonLeptonShellSelection =
      outerHorizonLeptonShellSelectionFromModal leptonModalFrequencySpec := by
  rfl

/-- **μ-generation shell** (strictly larger than `leptonHeavyVertexShell`). -/
noncomputable def leptonMuonShell : ℕ := currentOuterHorizonLeptonShellSelection.muonShell

/-- **e-generation shell** (strictly larger than `leptonMuonShell`). -/
noncomputable def leptonElectronShell : ℕ := currentOuterHorizonLeptonShellSelection.electronShell

/-- Temperature at the τ / lock-in lepton fanovertex: equals **`T_lockin`**. -/
noncomputable def T_lockin_now_lepton_fanovertex : ℝ :=
  T leptonHeavyVertexShell

theorem spinOnlyBaselineShell_eq_referenceM : spinOnlyBaselineShell = referenceM :=
  rfl

theorem leptonHeavyVertexShell_gt_spinOnlyBaseline :
    spinOnlyBaselineShell < leptonHeavyVertexShell := by
  simpa [leptonHeavyVertexShell] using
    firstShellAtOrAboveResonanceThreshold_gt spinOnlyBaselineShell chargeDecoratedStandingWaveLift

theorem leptonHeavyVertexShell_gt_referenceM :
    referenceM < leptonHeavyVertexShell := by
  simpa [spinOnlyBaselineShell_eq_referenceM] using leptonHeavyVertexShell_gt_spinOnlyBaseline

theorem currentOuterHorizonLeptonShellSelection_eq_thresholdDerived :
    currentOuterHorizonLeptonShellSelection = thresholdDerivedOuterHorizonLeptonShellSelection := by
  rfl

theorem leptonMuonShell_eq_derived :
    leptonMuonShell = derivedLeptonMuonShell := by
  rfl

theorem leptonElectronShell_eq_derived :
    leptonElectronShell = derivedLeptonElectronShell := by
  rfl

theorem leptonHeavyVertexShell_gt_m_lockin :
    m_lockin < leptonHeavyVertexShell := by
  simpa [m_lockin_eq_referenceM] using leptonHeavyVertexShell_gt_referenceM

theorem T_lockin_now_lepton_fanovertex_lt_T_lockin :
    T_lockin_now_lepton_fanovertex < T_lockin := by
  unfold T_lockin_now_lepton_fanovertex T_lockin
  rw [T_eq, T_eq]
  have h' : ((m_lockin : ℝ) + 1) < ((leptonHeavyVertexShell : ℝ) + 1) := by
    exact_mod_cast Nat.succ_lt_succ leptonHeavyVertexShell_gt_m_lockin
  exact one_div_lt_one_div_of_lt (by positivity) h'

theorem T_strict_drop_of_shell_lt {m n : ℕ} (h : m < n) : T n < T m := by
  rw [T_eq, T_eq]
  have h' : (m + 1 : ℝ) < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ h
  exact one_div_lt_one_div_of_lt (by positivity) h'

theorem lepton_shells_ordered_from_selection
    (selection : OuterHorizonLeptonShellSelection) :
    leptonHeavyVertexShell < selection.muonShell ∧ selection.muonShell < selection.electronShell := by
  exact ⟨selection.heavy_lt_muon, selection.muon_lt_electron⟩

theorem lepton_shells_ordered :
    leptonHeavyVertexShell < leptonMuonShell ∧ leptonMuonShell < leptonElectronShell := by
  simpa [leptonMuonShell, leptonElectronShell, currentOuterHorizonLeptonShellSelection] using
    lepton_shells_ordered_from_selection currentOuterHorizonLeptonShellSelection

theorem shellSurface_lepton_chain_strict_from_selection
    (selection : OuterHorizonLeptonShellSelection) :
    shellSurface leptonHeavyVertexShell < shellSurface selection.muonShell ∧
      shellSurface selection.muonShell < shellSurface selection.electronShell := by
  rcases lepton_shells_ordered_from_selection selection with ⟨hμ, he⟩
  constructor
  ·
    unfold shellSurface
    have hμ' : (leptonHeavyVertexShell : ℝ) < selection.muonShell := by
      exact_mod_cast hμ
    nlinarith
  ·
    unfold shellSurface
    have he' : (selection.muonShell : ℝ) < selection.electronShell := by
      exact_mod_cast he
    nlinarith

theorem shellSurface_lepton_chain_strict :
    shellSurface leptonHeavyVertexShell < shellSurface leptonMuonShell ∧
      shellSurface leptonMuonShell < shellSurface leptonElectronShell := by
  simpa [leptonMuonShell, leptonElectronShell, currentOuterHorizonLeptonShellSelection] using
    shellSurface_lepton_chain_strict_from_selection currentOuterHorizonLeptonShellSelection

/-- τ → μ geometric step (detuned surfaces), same combinator as quark internal octaves. -/
noncomputable def geometricResonanceStep_lepton_tau_mu : ℝ :=
  geometricResonanceStep leptonHeavyVertexShell leptonMuonShell

/-- μ → e geometric step. -/
noncomputable def geometricResonanceStep_lepton_mu_e : ℝ :=
  geometricResonanceStep leptonMuonShell leptonElectronShell

theorem geometricResonanceStep_lepton_tau_mu_pos : 0 < geometricResonanceStep_lepton_tau_mu :=
  geometricResonanceStep_pos leptonHeavyVertexShell leptonMuonShell

theorem geometricResonanceStep_lepton_mu_e_pos : 0 < geometricResonanceStep_lepton_mu_e :=
  geometricResonanceStep_pos leptonMuonShell leptonElectronShell

/-- Ladder temperature drops along μ and e (larger `m` ⇒ smaller `T(m)`). -/
theorem T_lepton_mu_lt_T_tau : T leptonMuonShell < T leptonHeavyVertexShell := by
  exact T_strict_drop_of_shell_lt lepton_shells_ordered.1

theorem T_lepton_e_lt_T_mu : T leptonElectronShell < T leptonMuonShell := by
  exact T_strict_drop_of_shell_lt lepton_shells_ordered.2

/-- τ birth line is evaluated on the charge-decorated heavy selector shell. -/
theorem lepton_tau_birth_on_chargeDecorated_heavy_shell :
    selfClockPhase leptonHeavyVertexShell 0 =
      comptonAngularFrequency leptonHeavyVertexShell * (Real.pi / 2) := by
  simp [selfClockPhase, add_zero]

end Hqiv.Physics
