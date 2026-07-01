import HqivSpine.Physics.GenerationDetunedLadder
import HqivSpine.Physics.GenerationResonanceLadder
import HqivSpine.Physics.NestedHopfBinding
import HqivSpine.Physics.ContentClassCompositeTrace
import HqivSpine.Physics.LeptonAbsoluteScale
import HqivSpine.Physics.HeavyQuarkAbsoluteScale
import HqivSpine.Physics.ColorCasimir
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.SectorNestedHopfBinding` — sector traces on nested Hopf rows

Extends `NestedHopfBinding` with **derived** composite traces from `ContentClassCompositeTrace`:

* charged leptons use the two-slot trace (`l = 2`), not the nucleon three-slot reuse;
* neutrinos use the one-slot trace (`l = 1`);
* quarks use the three-slot trace (`l = 3`), matching the nucleon valence pattern;
* binding on each Hopf chart row is `E_bind_at_hopf_shell` with fiber weight `n/(n+2)` in the
  coupling cell (`hopfBindingCouplingAtShell`);
* the proton-style inversion `M = constituent − E_bind` yields the Beltrami readout at the
  sector ground factor `contentClassGroundFactor c n`.

The cross-sector offset `9/4` is the squared trace-count ratio `(3/2)²`, equalling
`intrinsicWaveComplexity` and `C_A / C_F`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.SectorNestedHopfBinding

open HqivSpine.Physics
open HqivSpine.Physics.NestedHopfBinding
open HqivSpine.Physics.ContentClassCompositeTrace
open HqivSpine.Physics.TuftBeltramiMassFunctional
open HqivSpine.Physics.GenerationDetunedLadder
open HqivSpine.Physics.GenerationResonanceLadder
open HqivSpine.Physics.LeptonAbsoluteScale
open HqivSpine.Physics.HeavyQuarkAbsoluteScale
open HqivSpine.Physics.NucleonLadder
open scoped BigOperators

/-! ## Sector binding on nested Hopf chart shells -/

/-- **Sector network binding** on nested Hopf row `s` at content class `c`. -/
noncomputable def hopfShellBindingFor (c : FermionContentClass) (s : IntegrableHopfShell)
    (coupling : ℝ := 1) : ℝ :=
  E_bind_at_hopf_shell s (contentClassWeight c) coupling

theorem hopfShellBindingFor_eq (c : FermionContentClass) (s : IntegrableHopfShell) (coupling : ℝ) :
    hopfShellBindingFor c s coupling =
      E_bind_at_hopf_shell s (contentClassWeight c) coupling := rfl

theorem hopfShellBindingFor_eq_base_scaled (c : FermionContentClass) (s : IntegrableHopfShell)
    (coupling : ℝ) :
    hopfShellBindingFor c s coupling =
      hopfFibrationShape s.winding *
        E_bind_from_network (chartShell s) (contentClassWeight c) coupling := by
  rw [hopfShellBindingFor_eq, E_bind_at_hopf_shell_eq]

theorem hopfShellBindingFor_closed_form (c : FermionContentClass) (s : IntegrableHopfShell)
    (coupling : ℝ) :
    hopfShellBindingFor c s coupling =
      hopfFibrationShape s.winding * (conservedTripleCount c : ℝ) *
        (latticeSimplexCount (chartShell s) : ℝ) * alphaEffAtShell (chartShell s) coupling := by
  rw [hopfShellBindingFor_eq_base_scaled, E_bind_contentClass]
  ring

theorem hopfShellBindingFor_chargedLepton_ne_nucleon :
    hopfShellBindingFor .chargedLepton weakShell 1 ≠ hopfShellBinding weakShell 1 := by
  apply ne_of_lt
  rw [hopfShellBindingFor_closed_form, hopfShellBinding_closed_form, chartShell_weak,
    weakShell_winding, hopfFibrationShape_one]
  have hα := alphaEffAtShell_one_pos 2
  have hcount : (0 : ℝ) < (latticeSimplexCount 2 : ℝ) := by exact_mod_cast latticeSimplexCount_pos 2
  simp [conservedTripleCount]
  nlinarith [hα, hcount]

theorem hopfShellBindingFor_neutrino_ne_chargedLepton :
    hopfShellBindingFor .neutrino weakShell 1 ≠ hopfShellBindingFor .chargedLepton weakShell 1 := by
  apply ne_of_lt
  rw [hopfShellBindingFor_closed_form, hopfShellBindingFor_closed_form, chartShell_weak,
    weakShell_winding, hopfFibrationShape_one]
  have hα := alphaEffAtShell_one_pos 2
  have hcount : (0 : ℝ) < (latticeSimplexCount 2 : ℝ) := by exact_mod_cast latticeSimplexCount_pos 2
  simp [conservedTripleCount]
  nlinarith [hα, hcount]

theorem hopfShellBindingFor_quark_eq_nucleon (s : IntegrableHopfShell) (coupling : ℝ) :
    hopfShellBindingFor .quark s coupling = hopfShellBinding s coupling := by
  rw [hopfShellBindingFor_eq, hopfShellBinding_eq_nucleon, nucleonWeight_eq_contentClass_quark]

/-! ## Constituent − binding = sector readout -/

/-- Sector Beltrami readout at Hopf winding `n`. -/
noncomputable def sectorBeltramiReadout (slice : NowSlice) (c : FermionContentClass) (n : ℕ) : ℝ :=
  slice.readout (contentClassGroundFactor c n)

theorem sectorBeltramiReadout_eq (slice : NowSlice) (c : FermionContentClass) (n : ℕ) :
    sectorBeltramiReadout slice c n = slice.massUnit * contentClassGroundFactor c n := by
  unfold sectorBeltramiReadout; rfl

theorem sectorBeltramiReadout_chargedLepton (slice : NowSlice) (n : ℕ) :
    sectorBeltramiReadout slice .chargedLepton n = tuftBeltramiMassReadout slice n := by
  rw [sectorBeltramiReadout_eq, tuftBeltramiMassReadout_eq]
  exact congr_arg _ (by simp [contentClassGroundFactor_chargedLepton, tuftBeltramiMassFactor_eq_succ])

theorem sectorBeltramiReadout_quark (slice : NowSlice) (n : ℕ) :
    sectorBeltramiReadout slice .quark n =
      slice.massUnit * contentClassGroundFactor .quark n := by
  rw [sectorBeltramiReadout_eq]

theorem sectorBeltramiReadout_neutrino (slice : NowSlice) (n : ℕ) :
    sectorBeltramiReadout slice .neutrino n =
      slice.massUnit * contentClassGroundFactor .neutrino n := by
  rw [sectorBeltramiReadout_eq]

/-- Constituent on sector `c` at Hopf row `s`. -/
noncomputable def hopfShellSectorConstituent (slice : NowSlice) (c : FermionContentClass)
    (s : IntegrableHopfShell) : ℝ :=
  sectorBeltramiReadout slice c s.winding + hopfShellBindingFor c s 1

/-- Composite mass from the sector trace at the chart shell. -/
noncomputable def hopfShellSectorComposite (slice : NowSlice) (c : FermionContentClass)
    (s : IntegrableHopfShell) : ℝ :=
  M_composite_at_hopf_shell s (hopfShellSectorConstituent slice c s) (contentClassWeight c) 1

theorem hopfShellSectorComposite_eq_readout (slice : NowSlice) (c : FermionContentClass)
    (s : IntegrableHopfShell) :
    hopfShellSectorComposite slice c s = sectorBeltramiReadout slice c s.winding := by
  unfold hopfShellSectorComposite hopfShellSectorConstituent hopfShellBindingFor
    M_composite_at_hopf_shell
  ring

/-! ## Charged leptons on nested Hopf rows -/

theorem leptonMassReadout_eq_sector_hopf_composite (slice : NowSlice) (g : LeptonGeneration) :
    leptonMassReadout slice g =
      hopfShellSectorComposite slice .chargedLepton heavyShell *
        detunedHopfWeight 3 / generationResonanceDescent g.winding := by
  rw [leptonMassReadout_eq_tuftBeltrami_resonance, hopfShellSectorComposite_eq_readout,
    sectorBeltramiReadout_chargedLepton, heavyShell_winding, detunedHopfWeight_heavy]

theorem leptonGroundFactor_eq_contentClass_scaled (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 3) :
    leptonGroundFactor n =
      contentClassGroundFactor .chargedLepton 3 * detunedHopfWeight 3 / generationResonanceDescent n := by
  rw [leptonGroundFactor_eq, generationResonanceMassFactor_eq_anchor_over_descent hn,
    contentClassGroundFactor_chargedLepton, generationMassFactor_heavy, detunedHopfWeight_heavy]
  rcases hn with rfl | rfl | rfl <;> simp [generationResonanceDescent] <;> ring

/-! ## Quarks on nested Hopf rows -/

def quarkHopfShell : QuarkGeneration → IntegrableHopfShell
  | .first => weakShell
  | .second => strongShell
  | .third => heavyShell

theorem quarkHopfShell_winding (g : QuarkGeneration) :
    (quarkHopfShell g).winding = g.winding := by
  rcases g with _ | _ | _ <;> rfl

theorem quarkGroundFactor_eq_contentClass_scaled (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 3) :
    quarkGroundFactor n =
      contentClassGroundFactor .quark 3 * detunedHopfWeight 3 / generationResonanceDescent n := by
  rw [quarkGroundFactor_eq_detuned, generationResonanceMassFactor_eq_anchor_over_descent hn,
    contentClassGroundFactor_quark, generationMassFactor_heavy, detunedHopfWeight_heavy]
  rcases hn with rfl | rfl | rfl <;> simp [generationResonanceDescent] <;> ring

theorem quarkMassReadout_eq_sector_hopf_composite (slice : NowSlice) (g : QuarkGeneration) :
    quarkMassReadout slice g =
      slice.massUnit * contentClassGroundFactor .quark 3 * detunedHopfWeight 3 /
        generationResonanceDescent g.winding := by
  have hn : g.winding = 1 ∨ g.winding = 2 ∨ g.winding = 3 := by
    rcases g with _ | _ | _ <;> simp [QuarkGeneration.winding]
  rw [quarkMassReadout_eq, quarkGroundFactor_eq_contentClass_scaled g.winding hn]
  ring

/-! ## Neutrinos on nested Hopf rows (one-slot trace) -/

theorem hopfShellBinding_neutrino_over_chargedLepton (s : IntegrableHopfShell) :
    hopfShellBindingFor .neutrino s 1 / hopfShellBindingFor .chargedLepton s 1 = (1 : ℝ) / 2 := by
  rw [hopfShellBindingFor_closed_form, hopfShellBindingFor_closed_form]
  have hα := alphaEffAtShell_one_pos (chartShell s)
  have hcount : (0 : ℝ) < (latticeSimplexCount (chartShell s) : ℝ) :=
    by exact_mod_cast latticeSimplexCount_pos (chartShell s)
  field_simp [integrableHopfFibrationShape_ne_zero s, hcount, hα]
  simp only [conservedTripleCount]
  ring

theorem sectorReadout_chargedLepton_over_neutrino (slice : NowSlice) (n : ℕ) (hN : slice.massUnit ≠ 0) :
    sectorBeltramiReadout slice .chargedLepton n / sectorBeltramiReadout slice .neutrino n = 4 := by
  have hden : contentClassGroundFactor .neutrino n ≠ 0 := by
    rw [contentClassGroundFactor_neutrino]
    positivity
  calc
    sectorBeltramiReadout slice .chargedLepton n / sectorBeltramiReadout slice .neutrino n
        = contentClassGroundFactor .chargedLepton n / contentClassGroundFactor .neutrino n := by
            rw [sectorBeltramiReadout_eq, sectorBeltramiReadout_eq]
            field_simp [hN, hden]
    _ = 4 := contentClassGroundFactor_chargedLepton_over_neutrino n

/-! ## Cross-sector: binding `3/2`, readout `9/4` = `C_A / C_F` -/

theorem hopfShellBinding_quark_over_chargedLepton (s : IntegrableHopfShell) :
    hopfShellBindingFor .quark s 1 / hopfShellBindingFor .chargedLepton s 1 = (3 : ℝ) / 2 := by
  rw [hopfShellBindingFor_closed_form, hopfShellBindingFor_closed_form]
  have hα := alphaEffAtShell_one_pos (chartShell s)
  have hcount : (0 : ℝ) < (latticeSimplexCount (chartShell s) : ℝ) :=
    by exact_mod_cast latticeSimplexCount_pos (chartShell s)
  field_simp [integrableHopfFibrationShape_ne_zero s, hcount, hα]
  simp only [conservedTripleCount]
  ring

theorem sectorReadout_quark_over_chargedLepton (slice : NowSlice) (n : ℕ) (hN : slice.massUnit ≠ 0) :
    sectorBeltramiReadout slice .quark n / sectorBeltramiReadout slice .chargedLepton n =
      (9 : ℝ) / 4 := by
  have hden : contentClassGroundFactor .chargedLepton n ≠ 0 := by
    rw [contentClassGroundFactor_chargedLepton]
    positivity
  calc
    sectorBeltramiReadout slice .quark n / sectorBeltramiReadout slice .chargedLepton n
        = contentClassGroundFactor .quark n / contentClassGroundFactor .chargedLepton n := by
            rw [sectorBeltramiReadout_eq, sectorBeltramiReadout_eq]
            field_simp [hN, hden]
    _ = (9 : ℝ) / 4 := contentClassGroundFactor_quark_over_chargedLepton n

theorem quark_over_lepton_hopf_same_generation (slice : NowSlice) (g : QuarkGeneration)
    (hL : LeptonGeneration) (_hw : g.winding = hL.winding) (hN : slice.massUnit ≠ 0) :
    hopfShellSectorComposite slice .quark (quarkHopfShell g) /
      hopfShellSectorComposite slice .chargedLepton (leptonHopfShell hL) =
      casimirAdjoint / casimirFundamental colourCount := by
  rw [hopfShellSectorComposite_eq_readout, hopfShellSectorComposite_eq_readout,
    show (quarkHopfShell g).winding = g.winding from quarkHopfShell_winding g,
    show (leptonHopfShell hL).winding = hL.winding from leptonHopfShell_winding hL, _hw,
    sectorReadout_quark_over_chargedLepton slice hL.winding hN]
  exact casimir_ratio_nine_quarters.symm

/-! ## Heavy row: quark sector = proton binding pattern -/

theorem hopfShellBindingFor_quark_heavy_eq_proton :
    hopfShellBindingFor .quark heavyShell 1 = hopfShellBinding heavyShell 1 := by
  exact hopfShellBindingFor_quark_eq_nucleon heavyShell 1

/-! ## Capstone -/

structure SectorNestedHopfBindingClosure where
  /-- Content-class traces are derived (`contentClassCompositeTraceClosure`). -/
  content_traces : Nonempty ContentClassCompositeTrace.ContentClassCompositeTraceClosure
  /-- Charged-lepton binding ≠ nucleon reuse on the weak Hopf row. -/
  lepton_not_nucleon_trace :
    hopfShellBindingFor .chargedLepton weakShell 1 ≠ hopfShellBinding weakShell 1
  /-- Neutrino one-slot binding ≠ charged-lepton two-slot on the weak Hopf row. -/
  neutrino_not_chargedLepton_trace :
    hopfShellBindingFor .neutrino weakShell 1 ≠ hopfShellBindingFor .chargedLepton weakShell 1
  /-- Lepton composite = heavy-hopf composite × resonance descent. -/
  lepton_sector_composite :
    ∀ (slice : NowSlice) (g : LeptonGeneration),
      leptonMassReadout slice g =
        hopfShellSectorComposite slice .chargedLepton heavyShell *
          detunedHopfWeight 3 / generationResonanceDescent g.winding
  /-- Quark readout = heavy content-class factor × resonance descent. -/
  quark_sector_composite :
    ∀ (slice : NowSlice) (g : QuarkGeneration),
      quarkMassReadout slice g =
        slice.massUnit * contentClassGroundFactor .quark 3 * detunedHopfWeight 3 /
          generationResonanceDescent g.winding
  /-- Cross-sector readout `9/4` = `C_A / C_F` at matched generation. -/
  casimir_cross_sector :
    ∀ (slice : NowSlice) (g : QuarkGeneration) (hL : LeptonGeneration),
      g.winding = hL.winding → slice.massUnit ≠ 0 →
        hopfShellSectorComposite slice .quark (quarkHopfShell g) /
          hopfShellSectorComposite slice .chargedLepton (leptonHopfShell hL) =
            casimirAdjoint / casimirFundamental colourCount
  /-- Charged-lepton / neutrino readout ratio `4 = l_ℓ²/l_ν²` at matched winding. -/
  charged_lepton_over_neutrino_readout :
    ∀ (slice : NowSlice) (n : ℕ), slice.massUnit ≠ 0 →
      sectorBeltramiReadout slice .chargedLepton n / sectorBeltramiReadout slice .neutrino n = 4
  /-- Quark heavy-row binding matches proton nested Hopf binding. -/
  quark_heavy_is_proton :
    hopfShellBindingFor .quark heavyShell 1 = hopfShellBinding heavyShell 1

def sectorNestedHopfBindingClosure : SectorNestedHopfBindingClosure where
  content_traces := ⟨contentClassCompositeTraceClosure⟩
  lepton_not_nucleon_trace := hopfShellBindingFor_chargedLepton_ne_nucleon
  neutrino_not_chargedLepton_trace := hopfShellBindingFor_neutrino_ne_chargedLepton
  lepton_sector_composite := fun slice g =>
    leptonMassReadout_eq_sector_hopf_composite slice g
  quark_sector_composite := fun slice g =>
    quarkMassReadout_eq_sector_hopf_composite slice g
  casimir_cross_sector := fun slice g hL hw hN =>
    quark_over_lepton_hopf_same_generation slice g hL hw hN
  charged_lepton_over_neutrino_readout := fun slice n hN =>
    sectorReadout_chargedLepton_over_neutrino slice n hN
  quark_heavy_is_proton := hopfShellBindingFor_quark_heavy_eq_proton

end HqivSpine.Physics.SectorNestedHopfBinding
