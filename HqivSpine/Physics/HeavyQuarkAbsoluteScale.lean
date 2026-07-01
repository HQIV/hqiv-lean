import HqivSpine.Physics.MassLadder
import HqivSpine.Physics.GenerationResonanceLadder
import HqivSpine.Physics.LeptonAbsoluteScale
import HqivSpine.Physics.ColorCasimir
import HqivSpine.Physics.NowSliceFromLattice
import HqivSpine.Physics.NowSliceCausalDiamond
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.HeavyQuarkAbsoluteScale` — quark constituents as now-scale multiples

**Derived** in `SectorNestedHopfBinding`: the three-slot quark content-class trace on nested Hopf
chart shells, with cross-sector prefactor `(l_q/l_ℓ)² = 9/4 = C_A/C_F` from trace geometry
(`ContentClassCompositeTrace`). Generation ratios inside the quark sector follow the same **detuned generation factors**
(`GenerationDetunedLadder`) with cross-sector prefactor `(l_q/l_ℓ)² = 9/4`.

`m_q(s, n) = massUnit(s) · (9/4) · generationResonanceMassFactor(n)`.

Heavy-flavour **constituent scales** are the second- and third-generation readouts (charm/strange
and top/bottom on the shared generation ladder). No top/bottom GeV literals; MeV labels stay in the
comparison layer.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.HeavyQuarkAbsoluteScale

open HqivSpine.Physics
open HqivSpine.Physics.GenerationResonanceLadder
open HqivSpine.Physics.LeptonAbsoluteScale
open HqivSpine.Physics.CausalDiamond
open HqivSpine.Physics.NowSliceFromLattice

/-! ## Generation windings (parallel to leptons) -/

/-- Quark generation on the Beltrami integrability ladder. -/
inductive QuarkGeneration
  | first
  | second
  | third
  deriving DecidableEq, Repr

/-- Beltrami winding `n` (`λ_min = n + 1`) for each quark generation. -/
def QuarkGeneration.winding : QuarkGeneration → ℕ
  | .first => 1
  | .second => 2
  | .third => 3

theorem QuarkGeneration.winding_strict :
    QuarkGeneration.winding .first < QuarkGeneration.winding .second ∧
      QuarkGeneration.winding .second < QuarkGeneration.winding .third := by
  constructor <;> decide

/-- Reference Beltrami winding shared with the lepton electron (`λ_min(1) = 2`). -/
def quarkReferenceWinding : ℕ := LeptonAbsoluteScale.leptonElectronWinding

theorem quarkReferenceWinding_eq_one : quarkReferenceWinding = 1 := rfl

/-! ## Absolute scale = now-scale × complexity × Beltrami -/

/-- **Dimensionless quark factor** at winding `n`. -/
noncomputable def quarkGroundFactor (n : ℕ) : ℝ :=
  intrinsicWaveComplexity .quark / intrinsicWaveComplexity .chargedLepton *
    generationResonanceMassFactor n

theorem quarkGroundFactor_eq_detuned (n : ℕ) :
    quarkGroundFactor n = 9 * generationResonanceMassFactor n / 4 := by
  unfold quarkGroundFactor intrinsicWaveComplexity conservedTripleCount
  ring

theorem quarkGroundFactor_eq (n : ℕ) :
    quarkGroundFactor n = 9 * generationResonanceMassFactor n / 4 :=
  quarkGroundFactor_eq_detuned n

theorem quarkGroundFactor_eq_complexity_ratio (n : ℕ) :
    quarkGroundFactor n =
      intrinsicWaveComplexity .quark / intrinsicWaveComplexity .chargedLepton *
        generationResonanceMassFactor n := by
  rw [quarkGroundFactor_eq_detuned]
  unfold intrinsicWaveComplexity conservedTripleCount
  ring

/-- **Quark constituent readout** at generation `g`. -/
noncomputable def quarkMassReadout (s : NowSlice) (g : QuarkGeneration) : ℝ :=
  s.readout (quarkGroundFactor g.winding)

theorem quarkMassReadout_eq (s : NowSlice) (g : QuarkGeneration) :
    quarkMassReadout s g = s.massUnit * quarkGroundFactor g.winding := by
  unfold quarkMassReadout quarkGroundFactor
  rfl

theorem quarkMassReadout_first (s : NowSlice) :
    quarkMassReadout s .first = s.massUnit * (6837264 / 3138800) := by
  rw [quarkMassReadout_eq, QuarkGeneration.winding, quarkGroundFactor_eq_detuned,
    generationResonanceMassFactor_electron]
  ring

theorem quarkMassReadout_second (s : NowSlice) :
    quarkMassReadout s .second = s.massUnit * (684 / 175) := by
  rw [quarkMassReadout_eq, QuarkGeneration.winding, quarkGroundFactor_eq_detuned,
    generationResonanceMassFactor_muon]
  ring

theorem quarkMassReadout_third (s : NowSlice) :
    quarkMassReadout s .third = s.massUnit * 9 := by
  rw [quarkMassReadout_eq, QuarkGeneration.winding, quarkGroundFactor_eq_detuned,
    generationResonanceMassFactor_heavy]
  ring

/-- **Heavy-flavour constituent scales** on the generation ladder. -/
noncomputable abbrev charmConstituentScale (s : NowSlice) : ℝ := quarkMassReadout s .second

noncomputable abbrev strangeConstituentScale (s : NowSlice) : ℝ := quarkMassReadout s .second

noncomputable abbrev topConstituentScale (s : NowSlice) : ℝ := quarkMassReadout s .third

noncomputable abbrev bottomConstituentScale (s : NowSlice) : ℝ := quarkMassReadout s .third

theorem quarkMassReadout_pos (s : NowSlice) (g : QuarkGeneration)
    (hPhi : 0 < 1 + s.bigPhi) (hphi : 0 ≤ s.phi) (ht : 0 ≤ s.apparentAge) :
    0 < quarkMassReadout s g := by
  rw [quarkMassReadout_eq]
  exact mul_pos (s.massUnit_pos hPhi hphi ht) (by
    rcases g with _ | _ | _ <;> norm_num [QuarkGeneration.winding, quarkGroundFactor_eq,
      generationResonanceMassFactor_electron, generationResonanceMassFactor_muon,
      generationResonanceMassFactor_heavy])

/-! ## Cross-sector: quark / lepton = 9/4 at matched generation -/

theorem quark_over_lepton_same_generation (s : NowSlice) (g : QuarkGeneration)
    (hL : LeptonGeneration) (hw : g.winding = hL.winding) (hN : s.massUnit ≠ 0) :
    quarkMassReadout s g / leptonMassReadout s hL = (9 : ℝ) / 4 := by
  rw [quarkMassReadout_eq, leptonMassReadout_eq, hw, quarkGroundFactor_eq_detuned]
  have hgen : 0 < generationResonanceMassFactor hL.winding := by
    rcases hL with _ | _ | _ <;> exact generationResonanceMassFactor_pos (by decide)
  field_simp [hN, ne_of_gt hgen]

theorem quark_over_lepton_same_generation_casimir (s : NowSlice) (g : QuarkGeneration)
    (hL : LeptonGeneration) (hw : g.winding = hL.winding) (hN : s.massUnit ≠ 0) :
    quarkMassReadout s g / leptonMassReadout s hL =
      casimirAdjoint / casimirFundamental colourCount := by
  rw [quark_over_lepton_same_generation s g hL hw hN, casimir_ratio_nine_quarters]

/-! ## Intra-quark generation ratios -/

theorem quarkMassReadout_second_over_first (s : NowSlice) (hN : s.massUnit ≠ 0) :
    quarkMassReadout s .second / quarkMassReadout s .first = 4484 / 2499 := by
  rw [quarkMassReadout_second, quarkMassReadout_first]
  field_simp [hN]
  norm_num [generationResonanceMassFactor_muon, generationResonanceMassFactor_electron,
    quarkGroundFactor_eq_detuned]

theorem quarkMassReadout_third_over_second (s : NowSlice) (hN : s.massUnit ≠ 0) :
    quarkMassReadout s .third / quarkMassReadout s .second = 175 / 76 := by
  rw [quarkMassReadout_third, quarkMassReadout_second]
  field_simp [hN]
  norm_num [generationResonanceMassFactor_heavy, generationResonanceMassFactor_muon,
    quarkGroundFactor_eq_detuned]

theorem quarkMassReadout_second_over_first_eq (s : NowSlice) (hN : s.massUnit ≠ 0) :
    quarkMassReadout s .second / quarkMassReadout s .first = (4484 : ℝ) / 2499 := by
  exact quarkMassReadout_second_over_first s hN

theorem quarkMassReadout_third_over_second_eq (s : NowSlice) (hN : s.massUnit ≠ 0) :
    quarkMassReadout s .third / quarkMassReadout s .second = (175 : ℝ) / 76 := by
  exact quarkMassReadout_third_over_second s hN

/-! ## Lock-in diamond -/

theorem lockin_quarkMassReadout_first :
    quarkMassReadout lockinNowSlice .first = 34186320 / 3138800 := by
  rw [quarkMassReadout_first, lockinNowSlice_massUnit]
  norm_num

theorem lockin_quarkMassReadout_second :
    quarkMassReadout lockinNowSlice .second = 3420 / 175 := by
  rw [quarkMassReadout_second, lockinNowSlice_massUnit]
  norm_num

theorem lockin_quarkMassReadout_third :
    quarkMassReadout lockinNowSlice .third = 45 := by
  rw [quarkMassReadout_third, lockinNowSlice_massUnit]
  norm_num

theorem lockin_charm_eq_strange :
    charmConstituentScale lockinNowSlice = strangeConstituentScale lockinNowSlice := rfl

theorem lockin_top_eq_bottom :
    topConstituentScale lockinNowSlice = bottomConstituentScale lockinNowSlice := rfl

theorem lockin_quark_over_lepton_tau :
    quarkMassReadout lockinNowSlice .third / leptonMassReadout lockinNowSlice .tau = 9 / 4 := by
  rw [quarkMassReadout_third, leptonMassReadout_tau, lockinNowSlice_massUnit]
  norm_num

/-! ## Capstone -/

/-- **Heavy-quark absolute-scale closure** — constituent scales from `massUnit` and detuned ratios. -/
structure HeavyQuarkAbsoluteScaleClosure where
  ground_factor : ∀ n, quarkGroundFactor n = 9 * generationResonanceMassFactor n / 4
  casimir_cross_sector :
    ∀ (s : NowSlice) (g : QuarkGeneration) (hL : LeptonGeneration),
      g.winding = hL.winding → s.massUnit ≠ 0 →
        quarkMassReadout s g / leptonMassReadout s hL = casimirAdjoint / casimirFundamental colourCount
  generation_ratios :
    (∀ s, s.massUnit ≠ 0 →
        quarkMassReadout s .second / quarkMassReadout s .first = (4484 : ℝ) / 2499) ∧
      (∀ s, s.massUnit ≠ 0 →
        quarkMassReadout s .third / quarkMassReadout s .second = (175 : ℝ) / 76)
  lockin_scales :
    quarkMassReadout lockinNowSlice .first = 34186320 / 3138800 ∧
    charmConstituentScale lockinNowSlice = 3420 / 175 ∧
    topConstituentScale lockinNowSlice = 45

noncomputable def heavyQuarkAbsoluteScaleClosure : HeavyQuarkAbsoluteScaleClosure where
  ground_factor := fun n => quarkGroundFactor_eq n
  casimir_cross_sector := fun s g hL hw hN =>
    quark_over_lepton_same_generation_casimir s g hL hw hN
  generation_ratios :=
    ⟨fun s hN => quarkMassReadout_second_over_first_eq s hN,
      fun s hN => quarkMassReadout_third_over_second_eq s hN⟩
  lockin_scales :=
    ⟨lockin_quarkMassReadout_first, lockin_quarkMassReadout_second, lockin_quarkMassReadout_third⟩

end HqivSpine.Physics.HeavyQuarkAbsoluteScale
