import HqivSpine.Physics.NucleonLadder
import HqivSpine.Physics.TuftBeltramiAnchor
import HqivSpine.Physics.RindlerDetuning
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.GenerationDetunedLadder` — δ-corrected generation weights on Hopf chart rows

Bare Beltrami labels `λ_min(n) = n + 1` are necessary but insufficient for fermion hierarchy.
Each Hopf winding `n ∈ {1,2,3}` carries chart shell `m = n + 1` and detuned hopf weight
`w(n) = S̃(referenceM)/S̃(n + 1)`. The **generation mass factor** is `λ_min(n) · w(n)`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.GenerationDetunedLadder

open HqivSpine.Foundation
open HqivSpine.Physics
open HqivSpine.Physics.NucleonLadder
open HqivSpine.Physics.TuftBeltramiAnchor
open HqivSpine.Physics.RindlerDetuning

def hopfChartShell (n : ℕ) : ℕ := n + 1

theorem hopfChartShell_eq_tuft (n : ℕ) : hopfChartShell n = tuftChartShell n := by
  unfold hopfChartShell tuftChartShell; rfl

theorem hopfChartShell_heavy : hopfChartShell 3 = referenceM := by
  unfold hopfChartShell referenceM; decide

noncomputable def detunedHopfWeight (n : ℕ) : ℝ :=
  detunedSurface referenceM / detunedSurface (hopfChartShell n)

theorem detunedHopfWeight_pos (n : ℕ) : 0 < detunedHopfWeight n := by
  unfold detunedHopfWeight
  exact div_pos (detunedSurface_pos referenceM) (detunedSurface_pos (hopfChartShell n))

theorem detunedHopfWeight_heavy : detunedHopfWeight 3 = 1 := by
  unfold detunedHopfWeight
  rw [hopfChartShell_heavy]
  field_simp [ne_of_gt (detunedSurface_pos referenceM)]

noncomputable def generationMassFactor (n : ℕ) : ℝ :=
  beltramiMinEigenvalue n * detunedHopfWeight n

theorem generationMassFactor_pos {n : ℕ} (_hn : 0 < n) :
    0 < generationMassFactor n := by
  unfold generationMassFactor
  exact mul_pos (beltramiMinEigenvalue_pos n) (detunedHopfWeight_pos n)

theorem generationMassFactor_heavy :
    generationMassFactor 3 = 4 := by
  rw [generationMassFactor, beltramiMinEigenvalue_eq_succ, detunedHopfWeight_heavy]
  norm_num

theorem generationMassFactor_muon :
    generationMassFactor 2 = 4 := by
  rw [generationMassFactor, beltramiMinEigenvalue_eq_succ]
  unfold detunedHopfWeight hopfChartShell detunedSurface rindlerDetuning
  rw [gammaHQIV_eq, show referenceM = 4 by decide]
  norm_num [latticeSimplexCount, shellNumer, rindlerDetuning]

theorem generationMassFactor_electron :
    generationMassFactor 1 = 35 / 9 := by
  rw [generationMassFactor, beltramiMinEigenvalue_eq_succ]
  unfold detunedHopfWeight hopfChartShell detunedSurface rindlerDetuning
  rw [gammaHQIV_eq, show referenceM = 4 by decide]
  norm_num [latticeSimplexCount, shellNumer, rindlerDetuning]

theorem generationMassFactor_mu_over_electron :
    generationMassFactor 2 / generationMassFactor 1 = 36 / 35 := by
  rw [generationMassFactor_muon, generationMassFactor_electron]
  norm_num

theorem generationMassFactor_tau_over_muon :
    generationMassFactor 3 / generationMassFactor 2 = 1 := by
  rw [generationMassFactor_heavy, generationMassFactor_muon]
  norm_num

structure GenerationDetunedLadderClosure where
  heavy_normalisation : detunedHopfWeight 3 = 1
  muon_factor : generationMassFactor 2 = 4
  electron_factor : generationMassFactor 1 = 35 / 9
  mu_over_e : generationMassFactor 2 / generationMassFactor 1 = 36 / 35
  tau_over_mu : generationMassFactor 3 / generationMassFactor 2 = 1

noncomputable def generationDetunedLadderClosure : GenerationDetunedLadderClosure where
  heavy_normalisation := detunedHopfWeight_heavy
  muon_factor := generationMassFactor_muon
  electron_factor := generationMassFactor_electron
  mu_over_e := generationMassFactor_mu_over_electron
  tau_over_mu := generationMassFactor_tau_over_muon

end HqivSpine.Physics.GenerationDetunedLadder
