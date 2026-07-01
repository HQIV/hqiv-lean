import HqivSpine.Physics.Baryogenesis
import HqivSpine.Physics.NowSliceCausalDiamond
import HqivSpine.Physics.NowSliceFromLattice
import HqivSpine.Physics.BBN
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.BaryogenesisShellLadder` — η(m) on the discrete shell ladder

Extends lock-in baryogenesis to **every balanced-horizon shell** via the causal-diamond
evaluation map. The observer at shell `m` on `S³NullReference referenceM` carries discrete
`Ω_k(m) = omegaKPartial m`; the imprint at the same shell is `δ_E(m)`; their product is the
baryon-asymmetry readout

`η(m) = Ω_k(m) · δ_E(m) = etaAtShell m`.

This closes `Frontiers.baryonAsymmetryScaleFrontier`: no continuous-ξ chart, no `η_observed`
input. Comparison to `eta_observed_comparison` stays quarantined in `Baryogenesis`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.BaryogenesisShellLadder

open HqivSpine.Physics
open HqivSpine.Physics.ContinuousHorizon
open HqivSpine.Physics.CausalDiamond
open HqivSpine.Physics.NowSliceFromLattice
open scoped BigOperators

/-! ## Discrete η on the ladder -/

/-- **Shell-ladder baryon asymmetry** `η(m) = Ω_k(m) · δ_E(m)` from discrete lattice data only. -/
noncomputable def etaAtShell (m : ℕ) : ℝ := omegaKPartial m * deltaE m

theorem etaAtShell_eq (m : ℕ) : etaAtShell m = omegaKPartial m * deltaE m := rfl

theorem etaAtShell_zero : etaAtShell 0 = 0 := by
  unfold etaAtShell
  have hω : omegaKPartial 0 = 0 := by
    unfold omegaKPartial
    rw [omegaKChart_eq]
    have hξ0 : xiOfShell 0 = 1 := by unfold xiOfShell; norm_num
    rw [hξ0, continuousCurvaturePrimitive_one, zero_div]
  rw [hω, zero_mul]

theorem etaAtShell_lockin : etaAtShell referenceM = deltaE referenceM := by
  unfold etaAtShell
  rw [omegaKPartial_at_referenceM, one_mul]

theorem etaAtShell_pos {m : ℕ} (hm : 0 < m) : 0 < etaAtShell m := by
  unfold etaAtShell
  exact mul_pos (omegaKPartial_pos hm) (deltaE_pos m)

/-- **Event evaluation** agrees with the ladder formula on the balanced reference horizon. -/
theorem readoutAtShell_eta_eq (m : ℕ) :
    (readoutAtShell m).eta_at_shell = etaAtShell m := by
  dsimp [readoutAtShell, etaAtShell]
  rw [baryonAsymmetry_eq, horizonEventAtShell_slice_omegaK]

theorem readoutAtShell_baryonToPhoton {m : ℕ} (hm : m = referenceM) :
    (readoutAtShell m).eta_at_shell = BBN.baryonToPhoton lockinNowSlice := by
  rw [readoutAtShell_eta_eq, hm, etaAtShell_lockin]
  dsimp [BBN.baryonToPhoton]
  rw [baryonAsymmetry_lockin, lockinNowSlice_fields.2.2.1, one_mul]

/-! ## Capstone -/

/-- **Shell-ladder baryogenesis closure** — discrete `η(m)` on every horizon shell. -/
structure BaryogenesisShellLadderClosure where
  /-- Ladder formula `η(m) = Ω_k(m)·δ_E(m)`. -/
  eta_formula : ∀ m, etaAtShell m = omegaKPartial m * deltaE m
  /-- Lock-in agrees with `Baryogenesis` / `BBN`. -/
  eta_lockin : etaAtShell referenceM = deltaE referenceM
  /-- Causal-diamond readout matches the ladder. -/
  readout_agrees : ∀ m, (readoutAtShell m).eta_at_shell = etaAtShell m
  /-- Shell `0` carries no asymmetry (`Ω_k(0) = 0`). -/
  eta_zero : etaAtShell 0 = 0
  /-- Positive on every post-initial shell. -/
  eta_pos : ∀ {m}, 0 < m → 0 < etaAtShell m

noncomputable def baryogenesisShellLadderClosure : BaryogenesisShellLadderClosure where
  eta_formula := fun _ => rfl
  eta_lockin := etaAtShell_lockin
  readout_agrees := readoutAtShell_eta_eq
  eta_zero := etaAtShell_zero
  eta_pos := fun hm => etaAtShell_pos hm

end HqivSpine.Physics.BaryogenesisShellLadder
