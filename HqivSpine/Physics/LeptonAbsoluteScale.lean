import HqivSpine.Physics.GenerationDetunedLadder
import HqivSpine.Physics.GenerationResonanceLadder
import HqivSpine.Physics.MassLadder
import HqivSpine.Physics.NowSliceFromLattice
import HqivSpine.Physics.NowSliceCausalDiamond
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.LeptonAbsoluteScale` — charged leptons as now-scale multiples

Generation masses combine **Hopf-chart detuning** on `m ∈ {2,3,4}` with **extended detuned-shell
resonance** on outer ladder shells `15 → 33 → 58` (`GenerationResonanceLadder`).

`m_ℓ(s, n) = massUnit(s) · generationResonanceMassFactor(n)`.

At lock-in (`massUnit = 5`): `τ = 20`, `μ = 304/35`, `e = 759696/78470` (dimensionless spine units).
Ratios: `μ/e = 4484/2499`, `τ/μ = 175/76`, `τ/e = 175/76 · 4484/2499`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.LeptonAbsoluteScale

open HqivSpine.Physics
open HqivSpine.Physics.GenerationDetunedLadder
open HqivSpine.Physics.GenerationResonanceLadder
open HqivSpine.Physics.CausalDiamond
open HqivSpine.Physics.NowSliceFromLattice

/-! ## Generation windings on the Beltrami ladder -/

inductive LeptonGeneration
  | electron
  | muon
  | tau
  deriving DecidableEq, Repr

def LeptonGeneration.winding : LeptonGeneration → ℕ
  | .electron => 1
  | .muon => 2
  | .tau => 3

theorem LeptonGeneration.winding_strict :
    LeptonGeneration.winding .electron < LeptonGeneration.winding .muon ∧
      LeptonGeneration.winding .muon < LeptonGeneration.winding .tau := by
  constructor <;> decide

/-! ## Absolute scale = now-scale × resonance-refined factor -/

/-- **Dimensionless lepton factor** at winding `n`: hopf detuning × outer resonance descent. -/
noncomputable def leptonGroundFactor (n : ℕ) : ℝ := generationResonanceMassFactor n

theorem leptonGroundFactor_eq (n : ℕ) :
    leptonGroundFactor n = generationResonanceMassFactor n := rfl

def leptonElectronWinding : ℕ := LeptonGeneration.winding .electron

theorem leptonElectronWinding_eq_one : leptonElectronWinding = 1 := rfl

noncomputable def leptonMassReadout (s : NowSlice) (g : LeptonGeneration) : ℝ :=
  s.readout (leptonGroundFactor g.winding)

theorem leptonMassReadout_eq (s : NowSlice) (g : LeptonGeneration) :
    leptonMassReadout s g = s.massUnit * generationResonanceMassFactor g.winding := by
  unfold leptonMassReadout leptonGroundFactor
  rfl

theorem leptonMassReadout_electron (s : NowSlice) :
    leptonMassReadout s .electron = s.massUnit * (759696 / 784700) := by
  rw [leptonMassReadout_eq, LeptonGeneration.winding, generationResonanceMassFactor_electron]

theorem leptonMassReadout_muon (s : NowSlice) :
    leptonMassReadout s .muon = s.massUnit * (304 / 175) := by
  rw [leptonMassReadout_eq, LeptonGeneration.winding, generationResonanceMassFactor_muon]

theorem leptonMassReadout_tau (s : NowSlice) :
    leptonMassReadout s .tau = s.massUnit * 4 := by
  rw [leptonMassReadout_eq, LeptonGeneration.winding, generationResonanceMassFactor_heavy]

theorem generationResonanceMassFactor_pos {n : ℕ} (hn : n = 1 ∨ n = 2 ∨ n = 3) :
    0 < generationResonanceMassFactor n := by
  rcases hn with rfl | rfl | rfl
  · rw [generationResonanceMassFactor_electron]; norm_num
  · rw [generationResonanceMassFactor_muon]; norm_num
  · rw [generationResonanceMassFactor_heavy]; norm_num

theorem leptonMassReadout_pos (s : NowSlice) (g : LeptonGeneration)
    (hPhi : 0 < 1 + s.bigPhi) (hphi : 0 ≤ s.phi) (ht : 0 ≤ s.apparentAge) :
    0 < leptonMassReadout s g := by
  rw [leptonMassReadout_eq]
  exact mul_pos (s.massUnit_pos hPhi hphi ht)
    (generationResonanceMassFactor_pos (by rcases g with _ | _ | _ <;> decide))

/-! ## Generation ratios (resonance ladder) -/

theorem leptonMassReadout_muon_over_electron (s : NowSlice) (hN : s.massUnit ≠ 0) :
    leptonMassReadout s .muon / leptonMassReadout s .electron = 4484 / 2499 := by
  rw [leptonMassReadout_eq, leptonMassReadout_eq, LeptonGeneration.winding, LeptonGeneration.winding,
    generationResonanceMassFactor_muon, generationResonanceMassFactor_electron]
  field_simp [hN]
  norm_num [generationResonanceMassFactor_muon, generationResonanceMassFactor_electron]

theorem leptonMassReadout_tau_over_muon (s : NowSlice) (hN : s.massUnit ≠ 0) :
    leptonMassReadout s .tau / leptonMassReadout s .muon = 175 / 76 := by
  rw [leptonMassReadout_eq, leptonMassReadout_eq, LeptonGeneration.winding, LeptonGeneration.winding,
    generationResonanceMassFactor_heavy, generationResonanceMassFactor_muon]
  field_simp [hN]
  norm_num [generationResonanceMassFactor_heavy, generationResonanceMassFactor_muon]

theorem leptonMassReadout_tau_over_electron (s : NowSlice) (hN : s.massUnit ≠ 0) :
    leptonMassReadout s .tau / leptonMassReadout s .electron =
      (175 : ℝ) / 76 * 4484 / 2499 := by
  rw [leptonMassReadout_eq, leptonMassReadout_eq, LeptonGeneration.winding, LeptonGeneration.winding,
    generationResonanceMassFactor_heavy, generationResonanceMassFactor_electron]
  field_simp [hN]
  norm_num [generationResonanceMassFactor_heavy, generationResonanceMassFactor_electron,
    generationResonanceMassFactor_tau_over_electron]

/-! ## Lock-in diamond readout -/

theorem lockin_leptonMassReadout_electron :
    leptonMassReadout lockinNowSlice .electron = 3798480 / 784700 := by
  rw [leptonMassReadout_electron, lockinNowSlice_massUnit]
  norm_num

theorem lockin_leptonMassReadout_muon :
    leptonMassReadout lockinNowSlice .muon = 304 / 35 := by
  rw [leptonMassReadout_muon, lockinNowSlice_massUnit]
  ring

theorem lockin_leptonMassReadout_tau :
    leptonMassReadout lockinNowSlice .tau = 20 := by
  rw [leptonMassReadout_tau, lockinNowSlice_massUnit]
  norm_num

theorem lockin_leptonMassReadout_from_diamond :
    leptonMassReadout lockinEvent.slice .electron = 3798480 / 784700 ∧
    leptonMassReadout lockinEvent.slice .muon = 304 / 35 ∧
    leptonMassReadout lockinEvent.slice .tau = 20 := by
  rw [lockinEvent_slice_eq]
  exact ⟨lockin_leptonMassReadout_electron, lockin_leptonMassReadout_muon,
    lockin_leptonMassReadout_tau⟩

/-! ## Capstone -/

structure LeptonAbsoluteScaleClosure where
  electron_factor : leptonGroundFactor leptonElectronWinding = 759696 / 784700
  readout_formula : ∀ (s : NowSlice) (g : LeptonGeneration),
    leptonMassReadout s g = s.massUnit * generationResonanceMassFactor g.winding
  generation_ratios :
    (∀ s, s.massUnit ≠ 0 →
        leptonMassReadout s .muon / leptonMassReadout s .electron = (4484 : ℝ) / 2499) ∧
      (∀ s, s.massUnit ≠ 0 →
        leptonMassReadout s .tau / leptonMassReadout s .muon = (175 : ℝ) / 76)
  lockin_masses :
    leptonMassReadout lockinNowSlice .electron = 3798480 / 784700 ∧
    leptonMassReadout lockinNowSlice .muon = 304 / 35 ∧
    leptonMassReadout lockinNowSlice .tau = 20

noncomputable def leptonAbsoluteScaleClosure : LeptonAbsoluteScaleClosure where
  electron_factor := by
    rw [leptonGroundFactor_eq, leptonElectronWinding_eq_one, generationResonanceMassFactor_electron]
  readout_formula := fun _ _ => leptonMassReadout_eq _ _
  generation_ratios :=
    ⟨fun s hN => leptonMassReadout_muon_over_electron s hN,
      fun s hN => leptonMassReadout_tau_over_muon s hN⟩
  lockin_masses :=
    ⟨lockin_leptonMassReadout_electron, lockin_leptonMassReadout_muon,
      lockin_leptonMassReadout_tau⟩

end HqivSpine.Physics.LeptonAbsoluteScale
