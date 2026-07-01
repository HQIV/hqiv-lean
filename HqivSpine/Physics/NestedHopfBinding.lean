import HqivSpine.Physics.GenerationDetunedLadder
import HqivSpine.Physics.TuftBeltramiAnchor
import HqivSpine.Physics.TuftBeltramiMassFunctional
import HqivSpine.Physics.CurvatureKernel
import HqivSpine.Physics.TrappedCasimir
import HqivSpine.Physics.Binding
import HqivSpine.Physics.ClosureAction
import HqivSpine.Physics.NucleonLadder
import HqivSpine.Physics.Proton
import HqivSpine.Physics.LeptonAbsoluteScale
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.NestedHopfBinding` — the 8×8 network on nested Hopf chart shells

Mined from legacy `HopfShellComplex`, `TrappedCasimirBindingBridge`, and `GluonCurvatureArtifact`
into the clean spine **without** legacy imports, GeV anchors, or PDG tables.

**Ontology.** Three integrable Hopf windings `n ∈ {1,2,3}` (weak / strong / heavy) sit on TUFT chart
rows `m = n+1`. The **same** `so(8)` composite-trace binding network (`Binding`, `TrappedCasimir`)
evaluates at the chart shell `m`; the **contact** slot uses Hopf winding `n` in `CurvatureKernel.contactArg`,
the **ladder** slot uses shell `m` in `ladderArg`. Binding is trapped Casimir zero-point × trace
selection — not an independent gluon sector.

**Mass pattern (proton-style).** Constituent at chart `m` is Beltrami readout plus network binding;
composite mass `M = constituent − E_bind` equals the readout — the inversion already proved for the
proton (`proton_readout_iff_binding`), now placed on each nested Hopf row.

**Hopf fiber in binding.** `hopfFibrationShape n = n/(n+2)` enters the **per-generator coupling cell**
on nested Hopf rows (`hopfBindingCouplingAtShell`). Trapped Casimir still supplies the shell budget;
the Hopf shape localizes the fiber fraction of that budget on the winding-`n` chart row. At lock-in
(`n = 3`) this is the same `(3/5)` factor used in `NucleonLadder.protonHopfBinding`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.NestedHopfBinding

open HqivSpine.Physics
open HqivSpine.Physics.TuftBeltramiAnchor
open HqivSpine.Physics.TuftBeltramiMassFunctional
open HqivSpine.Physics.NucleonLadder
open HqivSpine.Physics.GenerationDetunedLadder
open HqivSpine.Physics.GenerationResonanceLadder
open HqivSpine.Physics.LeptonAbsoluteScale
open scoped BigOperators

/-! ## Integrable Hopf shells (windings 1 / 2 / 3) -/

/-- An integrable Hopf shell: positive winding `n ∈ {1,2,3}`. -/
structure IntegrableHopfShell where
  winding : ℕ
  h : hopfIntegrableWinding winding

/-- Weak-sector shell (`S³` chart row `m = 2`). -/
def weakShell : IntegrableHopfShell := ⟨1, hopfIntegrableWinding_one⟩

/-- Strong-sector shell (`m = 3`). -/
def strongShell : IntegrableHopfShell := ⟨2, hopfIntegrableWinding_two⟩

/-- Heavy-sector shell (`m = 4` = lock-in). -/
def heavyShell : IntegrableHopfShell := ⟨3, hopfIntegrableWinding_three⟩

theorem weakShell_winding : weakShell.winding = 1 := rfl

theorem strongShell_winding : strongShell.winding = 2 := rfl

theorem heavyShell_winding : heavyShell.winding = 3 := rfl

/-- TUFT chart row `m = n+1` for this shell. -/
def chartShell (s : IntegrableHopfShell) : ℕ := tuftChartShell s.winding

theorem chartShell_eq_winding_succ (s : IntegrableHopfShell) :
    chartShell s = s.winding + 1 := rfl

theorem chartShell_weak : chartShell weakShell = 2 := rfl

theorem chartShell_strong : chartShell strongShell = 3 := rfl

theorem chartShell_heavy : chartShell heavyShell = referenceM := by
  rw [chartShell, heavyShell_winding, show (3 : ℕ) = hopfLockinWinding from rfl, ← tuftHeavyChartShell]
  exact tuftHeavyChartShell_eq_referenceM

/-! ## Contact vs ladder kernels on nested rows -/

/-- Hopf **contact** log-kernel at the shell's winding. -/
noncomputable def contactKernel (s : IntegrableHopfShell) (c : ℝ := 1) : ℝ :=
  curvatureLogKernel (contactArg s.winding) c

/-- **Ladder** log-kernel at the shell's chart row. -/
noncomputable def ladderKernel (s : IntegrableHopfShell) (c : ℝ := 1) : ℝ :=
  curvatureLogKernel (ladderArg (chartShell s)) c

theorem contactKernel_eq_phaseLift_form (s : IntegrableHopfShell) :
    contactArg s.winding = 1 + phaseLiftCoeff s.winding * alphaEM := by
  unfold contactArg phaseLiftCoeff
  ring

theorem contactArg_lt_ladderArg_chart_one : contactArg 1 < ladderArg 2 := by
  norm_num [contactArg, ladderArg, phi, alphaEM_eq, tuftChartShell]

theorem contactArg_lt_ladderArg_chart_two : contactArg 2 < ladderArg 3 := by
  norm_num [contactArg, ladderArg, phi, alphaEM_eq, tuftChartShell]

theorem contactArg_lt_ladderArg_chart_three : contactArg 3 < ladderArg 4 := by
  norm_num [contactArg, ladderArg, phi, alphaEM_eq, tuftChartShell]

/-- Contact amplification is strictly below ladder amplification on each nested row. -/
theorem integrableContactKernel_lt_ladder (s : IntegrableHopfShell) (c : ℝ) (hc : 0 < c) :
    contactKernel s c < ladderKernel s c := by
  unfold contactKernel ladderKernel
  rw [chartShell_eq_winding_succ]
  rcases s with ⟨w, hw⟩
  rcases hw with rfl | rfl | rfl
  · exact curvatureLogKernel_lt_of_arg_lt c (contactArg 1) (ladderArg 2) hc
      (by linarith [one_lt_contactArg 1]) contactArg_lt_ladderArg_chart_one
  · exact curvatureLogKernel_lt_of_arg_lt c (contactArg 2) (ladderArg 3) hc
      (by linarith [one_lt_contactArg 2]) contactArg_lt_ladderArg_chart_two
  · exact curvatureLogKernel_lt_of_arg_lt c (contactArg 3) (ladderArg 4) hc
      (by linarith [one_lt_contactArg 3]) contactArg_lt_ladderArg_chart_three

/-! ## Hopf fiber–base weight in the binding coupling cell -/

/-- **Hopf-weighted shell coupling:** fiber–base fraction `n/(n+2)` times the trapped Casimir cell. -/
noncomputable def hopfBindingCouplingAtShell (s : IntegrableHopfShell) (k : So8Index) (c : ℝ := 1) : ℝ :=
  hopfFibrationShape s.winding * bindingCouplingAtShell (chartShell s) k c

theorem hopfBindingCouplingAtShell_eq (s : IntegrableHopfShell) (k : So8Index) (c : ℝ) :
    hopfBindingCouplingAtShell s k c =
      hopfFibrationShape s.winding * bindingCouplingAtShell (chartShell s) k c := rfl

/-- **Binding energy on a nested Hopf row** — trace weights times Hopf-localized coupling. -/
noncomputable def E_bind_at_hopf_shell (s : IntegrableHopfShell) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  ∑ k : So8Index, w k * hopfBindingCouplingAtShell s k c

theorem E_bind_at_hopf_shell_eq (s : IntegrableHopfShell) (w : NetworkWeight) (c : ℝ) :
    E_bind_at_hopf_shell s w c =
      hopfFibrationShape s.winding * E_bind_from_network (chartShell s) w c := by
  unfold E_bind_at_hopf_shell E_bind_from_network hopfBindingCouplingAtShell
  conv_lhs =>
    arg 2; ext k
    rw [show w k * (hopfFibrationShape s.winding * bindingCouplingAtShell (chartShell s) k c) =
      hopfFibrationShape s.winding * (w k * bindingCouplingAtShell (chartShell s) k c) from by ring]
  rw [← Finset.mul_sum]

theorem E_bind_at_hopf_shell_eq_trappedCasimir (s : IntegrableHopfShell) (w : NetworkWeight) (c : ℝ) :
    E_bind_at_hopf_shell s w c =
      hopfFibrationShape s.winding *
        ((∑ k : So8Index, w k) * trappedCasimirCell (chartShell s) c *
          (latticeSimplexCount (chartShell s) : ℝ)) := by
  rw [E_bind_at_hopf_shell_eq, E_bind_from_network_eq_sum_trappedCells]

/-- **Composite mass on a nested Hopf row** — subtract the Hopf-localized binding. -/
noncomputable def M_composite_at_hopf_shell (s : IntegrableHopfShell) (M_constituent : ℝ)
    (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  M_constituent - E_bind_at_hopf_shell s w c

theorem M_composite_at_hopf_shell_eq (s : IntegrableHopfShell) (M_constituent : ℝ)
    (w : NetworkWeight) (c : ℝ) :
    M_composite_at_hopf_shell s M_constituent w c =
      M_constituent - E_bind_at_hopf_shell s w c := rfl

theorem hopfFibrationShape_ne_zero {n : ℕ} (hn : 0 < n) : hopfFibrationShape n ≠ 0 :=
  ne_of_gt (hopfFibrationShape_pos hn)

theorem integrableHopfFibrationShape_ne_zero (s : IntegrableHopfShell) :
    hopfFibrationShape s.winding ≠ 0 := by
  rcases s with ⟨w, hw⟩
  rcases hw with rfl | rfl | rfl
  · exact hopfFibrationShape_ne_zero (by decide : 0 < (1 : ℕ))
  · exact hopfFibrationShape_ne_zero (by decide : 0 < (2 : ℕ))
  · exact hopfFibrationShape_ne_zero (by decide : 0 < (3 : ℕ))

/-! ## Binding network at the chart shell -/

/-- **Network binding** on the nested Hopf row (default nucleon trace, `c = 1`). -/
noncomputable def hopfShellBinding (s : IntegrableHopfShell) (c : ℝ := 1) : ℝ :=
  E_bind_at_hopf_shell s nucleonWeight c

theorem hopfShellBinding_eq_nucleon (s : IntegrableHopfShell) (c : ℝ) :
    hopfShellBinding s c = E_bind_at_hopf_shell s nucleonWeight c := rfl

theorem hopfShellBinding_eq_base_scaled (s : IntegrableHopfShell) (c : ℝ) :
    hopfShellBinding s c =
      hopfFibrationShape s.winding * E_bind_from_network (chartShell s) nucleonWeight c := by
  rw [hopfShellBinding_eq_nucleon, E_bind_at_hopf_shell_eq]

theorem hopfShellBinding_heavy_eq_referenceM :
    hopfShellBinding heavyShell 1 =
      hopfFibrationShape heavyShell.winding *
        E_bind_from_network referenceM nucleonWeight 1 := by
  rw [hopfShellBinding_eq_base_scaled, chartShell_heavy]

theorem hopfShellBinding_eq_trappedCasimir (s : IntegrableHopfShell) (c : ℝ) :
    hopfShellBinding s c =
      hopfFibrationShape s.winding *
        ((∑ k : So8Index, nucleonWeight k) * trappedCasimirCell (chartShell s) c *
          (latticeSimplexCount (chartShell s) : ℝ)) :=
  E_bind_at_hopf_shell_eq_trappedCasimir s nucleonWeight c

theorem hopfShellBinding_closed_form (s : IntegrableHopfShell) (c : ℝ) :
    hopfShellBinding s c =
      hopfFibrationShape s.winding * 3 * (latticeSimplexCount (chartShell s) : ℝ) *
        alphaEffAtShell (chartShell s) c := by
  rw [hopfShellBinding_eq_base_scaled, E_bind_nucleon]
  ring

theorem hopfShellBinding_pos (s : IntegrableHopfShell) :
    0 < hopfShellBinding s 1 := by
  rw [hopfShellBinding_eq_base_scaled]
  have hshape : 0 < hopfFibrationShape s.winding := by
    rcases s with ⟨w, hw⟩
    rcases hw with rfl | rfl | rfl
    · exact hopfFibrationShape_pos (by decide : 0 < (1 : ℕ))
    · exact hopfFibrationShape_pos (by decide : 0 < (2 : ℕ))
    · exact hopfFibrationShape_pos (by decide : 0 < (3 : ℕ))
  exact mul_pos hshape (E_bind_nucleon_pos (chartShell s))

/-! ## Constituent − binding = Beltrami readout (proton pattern on each row) -/

/-- Constituent mass on a Hopf row: Beltrami readout plus binding at the chart shell. -/
noncomputable def hopfShellConstituent (slice : NowSlice) (s : IntegrableHopfShell) : ℝ :=
  tuftBeltramiMassReadout slice s.winding + hopfShellBinding s 1

/-- Composite mass from the network at the chart shell. -/
noncomputable def hopfShellCompositeMass (slice : NowSlice) (s : IntegrableHopfShell) : ℝ :=
  M_composite_at_hopf_shell s (hopfShellConstituent slice s) nucleonWeight 1

theorem hopfShellComposite_eq_beltrami_readout (slice : NowSlice) (s : IntegrableHopfShell) :
    hopfShellCompositeMass slice s = tuftBeltramiMassReadout slice s.winding := by
  unfold hopfShellCompositeMass hopfShellConstituent M_composite_at_hopf_shell hopfShellBinding
  ring

theorem hopfShell_readout_iff_binding (slice : NowSlice) (s : IntegrableHopfShell) :
    M_composite_at_hopf_shell s (hopfShellConstituent slice s) nucleonWeight 1 =
      tuftBeltramiMassReadout slice s.winding ↔
        hopfShellBinding s 1 =
          hopfShellConstituent slice s - tuftBeltramiMassReadout slice s.winding := by
  unfold hopfShellConstituent M_composite_at_hopf_shell hopfShellBinding
  constructor <;> intro h <;> linarith

/-! ## Heavy row = proton lock-in -/

theorem heavyShell_binding_eq_proton_hopf :
    hopfShellBinding heavyShell 1 = protonHopfBinding 1 := by
  rw [hopfShellBinding_eq_base_scaled, chartShell_heavy, protonHopfBinding_eq, heavyShell_winding]
  rfl

theorem heavyShell_binding_eq_proton_lockin :
    hopfShellBinding heavyShell 1 = protonHopfBinding 1 :=
  heavyShell_binding_eq_proton_hopf

theorem protonConstituent_eq_hopf_heavy (slice : NowSlice) :
    protonConstituent slice (leptonGroundFactor heavyShell.winding) =
      hopfShellConstituent slice heavyShell := by
  unfold protonConstituent hopfShellConstituent
  have hread : protonReadout slice (leptonGroundFactor heavyShell.winding) =
      tuftBeltramiMassReadout slice heavyShell.winding := by
    rw [protonReadout_eq, tuftBeltramiMassReadout_eq, leptonGroundFactor_eq, heavyShell_winding,
      generationResonanceMassFactor_heavy, tuftBeltramiMassFactor_eq_succ]
    norm_num
  rw [hread, heavyShell_binding_eq_proton_hopf]

/-- Lepton generation on its nested Hopf row (winding `1 / 2 / 3`). -/
def leptonHopfShell : LeptonGeneration → IntegrableHopfShell
  | .electron => weakShell
  | .muon => strongShell
  | .tau => heavyShell

theorem leptonHopfShell_winding (g : LeptonGeneration) :
    (leptonHopfShell g).winding = g.winding := by
  rcases g with _ | _ | _ <;> rfl

theorem leptonMassReadout_eq_hopf_composite (slice : NowSlice) (g : LeptonGeneration) :
    leptonMassReadout slice g =
      hopfShellCompositeMass slice heavyShell * detunedHopfWeight 3 /
        generationResonanceDescent g.winding := by
  rw [leptonMassReadout_eq_tuftBeltrami_resonance, hopfShellComposite_eq_beltrami_readout,
    heavyShell_winding, detunedHopfWeight_heavy]

/-! ## Capstone -/

/-- **Nested Hopf binding closure** — chart shells carry the 8×8 network; contact < ladder;
composite = Beltrami readout; Hopf fiber weight in the coupling cell. -/
structure NestedHopfBindingClosure where
  /-- Chart rows `2 / 3 / 4`. -/
  chart_rows :
    chartShell weakShell = 2 ∧
    chartShell strongShell = 3 ∧
    chartShell heavyShell = referenceM
  /-- Contact kernel below ladder kernel on every integrable row. -/
  contact_below_ladder : ∀ (s : IntegrableHopfShell) (c : ℝ), 0 < c →
    contactKernel s c < ladderKernel s c
  /-- Hopf fiber–base weight enters the binding coupling cell. -/
  binding_hopf_shape :
    ∀ (s : IntegrableHopfShell) (w : NetworkWeight) (c : ℝ),
      E_bind_at_hopf_shell s w c =
        hopfFibrationShape s.winding * E_bind_from_network (chartShell s) w c
  /-- Binding is trapped Casimir on the chart shell, Hopf-localized. -/
  binding_trapped :
    ∀ (s : IntegrableHopfShell) (c : ℝ) (k : So8Index),
      hopfBindingCouplingAtShell s k c =
        hopfFibrationShape s.winding * trappedCasimirEnergy (chartShell s) / 4 *
          normalizedSelection (chartShell s) c
  /-- Composite mass on each row equals the TUFT Beltrami readout. -/
  composite_is_readout :
    ∀ (slice : NowSlice) (s : IntegrableHopfShell),
      hopfShellCompositeMass slice s = tuftBeltramiMassReadout slice s.winding
  /-- Heavy row binding is proton Hopf-localized lock-in binding. -/
  heavy_is_proton_binding :
    hopfShellBinding heavyShell 1 = protonHopfBinding 1

def nestedHopfBindingClosure : NestedHopfBindingClosure where
  chart_rows := ⟨chartShell_weak, chartShell_strong, chartShell_heavy⟩
  contact_below_ladder := fun s c hc => integrableContactKernel_lt_ladder s c hc
  binding_hopf_shape := fun s w c => E_bind_at_hopf_shell_eq s w c
  binding_trapped := fun s c k => by
    rw [hopfBindingCouplingAtShell_eq,
      bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection (chartShell s) k c]
    ring
  composite_is_readout := fun slice s => hopfShellComposite_eq_beltrami_readout slice s
  heavy_is_proton_binding := heavyShell_binding_eq_proton_hopf

end HqivSpine.Physics.NestedHopfBinding
