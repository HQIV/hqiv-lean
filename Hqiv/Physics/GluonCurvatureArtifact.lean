import Hqiv.Physics.TrappedCasimirBindingBridge
import Hqiv.Physics.HadronMassReadout
import Hqiv.Physics.StrongColorSu3ChartClosure
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.ContinuousXiCoupling

/-!
# Gluon-as-curvature-artifact closure (paper cone)

Companion to `papers/gluon_curvature_artifact/hqiv_gluon_as_curvature_artifact.tex`.

## Unified strong-sector kernel (discharged)

Both Hopf **contact** trapping and O-Maxwell **ladder** trace selection are instances of
one curvature log amplification

`curvatureLogAmplification x c = 1 + c · α · log x`,

evaluated at two chart coordinates on the same strong-sector spine:

| Readout slot | Log argument `x` | Role |
|---|---|---|
| Inner contact (T11/T12) | `1 + (φ(w)/6)·α` on winding `w` | Inner Casimir / vev-scale trapping |
| Shell ladder (binding) | `φ(m)+1` on chart shell `m = w+1` | `α_eff(m)` / normalized SO(8) selection |

The log arguments are **not equal** (`x_contact < x_ladder` on every integrable shell);
the **kernel** is shared. Normalized trace selection is the ladder instance divided by
`42 · (φ(m)/2)` — not a third independent mechanism.

Optional: `lake build HQIVStrongColorSu3Certificate` for the finite `su(3)` chart Lie law.
-/

namespace Hqiv.Physics

open Hqiv

/-!
## Chart shell index
-/

def hopfChartShellIndex (s : Hqiv.Topology.HopfShell) : ℕ := s.winding + 1

theorem hopfChartShellIndex_t12_heavy : hopfChartShellIndex t12_heavy_shell = 4 := by
  rw [hopfChartShellIndex, t12_heavy_shell_winding_eq_three]

theorem hopfShellForGeneration_chartShellIndex_zero :
    hopfChartShellIndex (hopfShellForGeneration 0) = 2 := by
  rw [hopfShellForGeneration_zero]; dsimp [hopfChartShellIndex, Hqiv.Topology.mkIntegrable]

theorem hopfShellForGeneration_chartShellIndex_one :
    hopfChartShellIndex (hopfShellForGeneration 1) = 3 := by
  rw [hopfShellForGeneration_one]; dsimp [hopfChartShellIndex, Hqiv.Topology.mkIntegrable]

theorem hopfShellForGeneration_chartShellIndex_two :
    hopfChartShellIndex (hopfShellForGeneration 2) = 4 := by
  rw [hopfShellForGeneration_two]; dsimp [hopfChartShellIndex, Hqiv.Topology.mkIntegrable]

/-!
## Trace-selection log kernel (alias for ladder instance)
-/

noncomputable def traceSelectionLogAmplification (m : ℕ) (c : ℝ := 1) : ℝ :=
  1 + c * alpha * Real.log (Hqiv.phi_of_shell m + 1)

theorem oneOverAlphaEffAtShell_eq_bare_times_traceSelectionLogAmplification
    (m : ℕ) (c : ℝ) :
    oneOverAlphaEffAtShell m c =
      oneOverAlphaBare * traceSelectionLogAmplification m c := by
  unfold oneOverAlphaEffAtShell traceSelectionLogAmplification oneOverAlphaBare
  ring

theorem alphaEffAtShell_eq_inv_bare_traceSelection_times (m : ℕ) (c : ℝ) :
    alphaEffAtShell m c =
      (oneOverAlphaBare * traceSelectionLogAmplification m c)⁻¹ := by
  unfold alphaEffAtShell
  rw [oneOverAlphaEffAtShell_eq_bare_times_traceSelectionLogAmplification]

theorem normalizedSO8TraceSelection_eq_inv_bare_traceSelection_casimir
    (m : ℕ) (c : ℝ) :
    normalizedSO8TraceSelection m c =
      (oneOverAlphaBare * traceSelectionLogAmplification m c * casimirPerModeZeroPoint m)⁻¹ := by
  unfold normalizedSO8TraceSelection
  rw [alphaEffAtShell_eq_inv_bare_traceSelection_times]
  field_simp [ne_of_gt (casimirPerModeZeroPoint_pos m)]

/-!
## Unified curvature log kernel
-/

/-- Contact chart coordinate: phase-lift slot `1 + (φ(w)/6)·α`. -/
noncomputable def hopfContactLogInnerArgument (s : Hqiv.Topology.HopfShell) : ℝ :=
  1 + Hqiv.Algebra.phaseLiftCoeff s.winding * s.curvatureImprintAlpha

/-- **Single strong-sector log kernel:** `1 + c·α·log x` (requires `x > 0` for the log). -/
noncomputable def curvatureLogAmplification (x : ℝ) (c : ℝ := 1) : ℝ :=
  1 + c * alpha * Real.log x

/-- Ladder chart coordinate: auxiliary-field slot `φ(m)+1` (binding / `α_eff` side). -/
noncomputable def ladderLogArgumentAtChartShell (m : ℕ) : ℝ :=
  Hqiv.phi_of_shell m + 1

theorem hopfContactLogInnerArgument_eq_ladderPhaseLiftSlot
    (s : Hqiv.Topology.HopfShell) (hα : s.effectiveAlpha = none) :
    hopfContactLogInnerArgument s =
      1 + Hqiv.Algebra.phaseLiftCoeff s.winding * alpha := by
  unfold hopfContactLogInnerArgument
  rw [Hqiv.Topology.HopfShell.curvatureImprintAlpha_eq_global s hα]

theorem phaseLiftCoeff_eq_phi_over_six (w : ℕ) :
    Hqiv.Algebra.phaseLiftCoeff w = Hqiv.phi_of_shell w / 6 := rfl

theorem hopfContactLogInnerArgument_eq_contactPhaseLiftSlot
    (s : Hqiv.Topology.HopfShell) (hα : s.effectiveAlpha = none) :
    hopfContactLogInnerArgument s =
      1 + (Hqiv.phi_of_shell s.winding / 6) * alpha := by
  rw [hopfContactLogInnerArgument_eq_ladderPhaseLiftSlot s hα, phaseLiftCoeff_eq_phi_over_six]

theorem curvatureLogAmplification_pos (x : ℝ) (c : ℝ) (hc : 0 ≤ c) (hx : 1 < x) :
    0 < curvatureLogAmplification x c := by
  unfold curvatureLogAmplification
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hα : 0 ≤ alpha := by rw [alpha_eq_3_5]; norm_num
  nlinarith [mul_nonneg (mul_nonneg hc hα) (le_of_lt hlog)]

/-!
## Both legacy slots are kernel instances
-/

theorem hopfTrappedSelectionFromShell_eq_curvatureLogAmplification_contact
    (s : Hqiv.Topology.HopfShell) (c : ℝ) (hα : s.effectiveAlpha = none) :
    hopfTrappedSelectionFromShell s c =
      curvatureLogAmplification (hopfContactLogInnerArgument s) c := by
  unfold hopfTrappedSelectionFromShell curvatureLogAmplification hopfContactLogInnerArgument
  rw [Hqiv.Topology.HopfShell.curvatureImprintAlpha_eq_global s hα]

theorem traceSelectionLogAmplification_eq_curvatureLogAmplification_ladder
    (m : ℕ) (c : ℝ) :
    traceSelectionLogAmplification m c =
      curvatureLogAmplification (ladderLogArgumentAtChartShell m) c := by
  unfold traceSelectionLogAmplification curvatureLogAmplification ladderLogArgumentAtChartShell
  ring

theorem traceSelectionLogAmplification_eq_one_add_c_logPhiXi (m : ℕ) (c : ℝ) :
    traceSelectionLogAmplification m c = 1 + c * logPhiXi (xiOfShell m) := by
  unfold traceSelectionLogAmplification logPhiXi
  rw [phiOfXi_xiOfShell m]
  ring

theorem oneOverAlphaEffAtShell_eq_bare_times_curvatureLogAmplification_ladder
    (m : ℕ) (c : ℝ) :
    oneOverAlphaEffAtShell m c =
      oneOverAlphaBare * curvatureLogAmplification (ladderLogArgumentAtChartShell m) c := by
  rw [← traceSelectionLogAmplification_eq_curvatureLogAmplification_ladder]
  exact oneOverAlphaEffAtShell_eq_bare_times_traceSelectionLogAmplification m c

theorem normalizedSO8TraceSelection_eq_inv_bare_ladderKernel_casimir
    (m : ℕ) (c : ℝ) :
    normalizedSO8TraceSelection m c =
      (oneOverAlphaBare * curvatureLogAmplification (ladderLogArgumentAtChartShell m) c *
        casimirPerModeZeroPoint m)⁻¹ := by
  rw [← traceSelectionLogAmplification_eq_curvatureLogAmplification_ladder]
  exact normalizedSO8TraceSelection_eq_inv_bare_traceSelection_casimir m c

/-!
## Contact vs ladder log arguments on chart shells (integrable trio)
-/

theorem hopfContactLogInnerArgument_generation_zero :
    hopfContactLogInnerArgument (hopfShellForGeneration 0) = (7 / 5 : ℝ) := by
  unfold hopfContactLogInnerArgument
  rw [hopfShellForGeneration_zero]
  dsimp [Hqiv.Topology.mkIntegrable, Hqiv.Topology.HopfShell.curvatureImprintAlpha]
  rw [alpha_eq_3_5, Hqiv.Algebra.phaseLiftCoeff, Hqiv.phi_of_shell_closed_form,
    Hqiv.phiTemperatureCoeff_eq_two]
  norm_num

theorem ladderLogArgumentAtChartShell_two : ladderLogArgumentAtChartShell 2 = (7 : ℝ) := by
  unfold ladderLogArgumentAtChartShell
  rw [Hqiv.phi_of_shell_closed_form, Hqiv.phiTemperatureCoeff_eq_two]
  norm_num

theorem contactLogArgument_lt_ladderLogArgument_chart_two :
    hopfContactLogInnerArgument (hopfShellForGeneration 0) <
      ladderLogArgumentAtChartShell 2 := by
  rw [hopfContactLogInnerArgument_generation_zero, ladderLogArgumentAtChartShell_two]
  norm_num

theorem hopfContactLogInnerArgument_generation_one :
    hopfContactLogInnerArgument (hopfShellForGeneration 1) = (8 / 5 : ℝ) := by
  unfold hopfContactLogInnerArgument
  rw [hopfShellForGeneration_one]
  dsimp [Hqiv.Topology.mkIntegrable, Hqiv.Topology.HopfShell.curvatureImprintAlpha]
  rw [alpha_eq_3_5, Hqiv.Algebra.phaseLiftCoeff, Hqiv.phi_of_shell_closed_form,
    Hqiv.phiTemperatureCoeff_eq_two]
  norm_num

theorem ladderLogArgumentAtChartShell_three : ladderLogArgumentAtChartShell 3 = (9 : ℝ) := by
  unfold ladderLogArgumentAtChartShell
  rw [Hqiv.phi_of_shell_closed_form, Hqiv.phiTemperatureCoeff_eq_two]
  norm_num

theorem contactLogArgument_lt_ladderLogArgument_chart_three :
    hopfContactLogInnerArgument (hopfShellForGeneration 1) <
      ladderLogArgumentAtChartShell 3 := by
  rw [hopfContactLogInnerArgument_generation_one, ladderLogArgumentAtChartShell_three]
  norm_num

theorem hopfContactLogInnerArgument_t12_heavy :
    hopfContactLogInnerArgument t12_heavy_shell = (9 / 5 : ℝ) := by
  unfold hopfContactLogInnerArgument
  rw [t12_heavy_shell_winding_eq_three, phaseLiftCoeff_three_eq_four_thirds,
    t12_heavy_shell_curvatureImprintAlpha]
  norm_num

theorem ladderLogArgumentAtChartShell_four : ladderLogArgumentAtChartShell 4 = (11 : ℝ) := by
  unfold ladderLogArgumentAtChartShell
  rw [Hqiv.phi_of_shell_closed_form, Hqiv.phiTemperatureCoeff_eq_two]
  norm_num

theorem contactLogArgument_lt_ladderLogArgument_chart_four :
    hopfContactLogInnerArgument t12_heavy_shell < ladderLogArgumentAtChartShell 4 := by
  rw [hopfContactLogInnerArgument_t12_heavy, ladderLogArgumentAtChartShell_four]
  norm_num

theorem hopfTrappedSelectionFromShell_t12_heavy_one :
    hopfTrappedSelectionFromShell t12_heavy_shell 1 =
      1 + (3 / 5 : ℝ) * Real.log (9 / 5) := by
  rw [hopfTrappedSelectionFromShell_eq_curvatureLogAmplification_contact _ _ (by
    unfold t12_heavy_shell Hqiv.Topology.mkIntegrable; rfl),
    hopfContactLogInnerArgument_t12_heavy]
  unfold curvatureLogAmplification
  rw [alpha_eq_3_5]
  ring

theorem traceSelectionLogAmplification_four_one :
    traceSelectionLogAmplification 4 1 = 1 + (3 / 5 : ℝ) * Real.log (11 : ℝ) := by
  rw [traceSelectionLogAmplification_eq_curvatureLogAmplification_ladder]
  unfold curvatureLogAmplification ladderLogArgumentAtChartShell
  rw [alpha_eq_3_5, Hqiv.phi_of_shell_closed_form, Hqiv.phiTemperatureCoeff_eq_two]
  norm_num

theorem hopfTrappedSelectionFromShell_t12_lt_traceSelectionLogAmplification_four :
    hopfTrappedSelectionFromShell t12_heavy_shell 1 < traceSelectionLogAmplification 4 1 := by
  rw [hopfTrappedSelectionFromShell_t12_heavy_one, traceSelectionLogAmplification_four_one]
  have hlog : Real.log (9 / 5 : ℝ) < Real.log 11 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  nlinarith [hlog]

theorem hopfContactLogInnerArgument_one_lt_globalAlpha
    (s : Hqiv.Topology.HopfShell) (hα : s.effectiveAlpha = none) :
    1 < hopfContactLogInnerArgument s := by
  unfold hopfContactLogInnerArgument
  rw [Hqiv.Topology.HopfShell.curvatureImprintAlpha_eq_global s hα, alpha_eq_3_5]
  nlinarith [Hqiv.Algebra.phaseLiftCoeff_pos s.winding]

theorem hopfKernel_lt_ladderKernel_of_contact_lt_ladder
    (s : Hqiv.Topology.HopfShell) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (hα : s.effectiveAlpha = none)
    (hlt : hopfContactLogInnerArgument s < ladderLogArgumentAtChartShell m) :
    hopfTrappedSelectionFromShell s c < traceSelectionLogAmplification m c := by
  rw [hopfTrappedSelectionFromShell_eq_curvatureLogAmplification_contact s c hα,
    traceSelectionLogAmplification_eq_curvatureLogAmplification_ladder]
  unfold curvatureLogAmplification
  have hx := hopfContactLogInnerArgument_one_lt_globalAlpha s hα
  have hx_pos : 0 < hopfContactLogInnerArgument s := by linarith
  have hlog : Real.log (hopfContactLogInnerArgument s) < Real.log (ladderLogArgumentAtChartShell m) :=
    Real.log_lt_log hx_pos hlt
  have hαpos : 0 < alpha := by rw [alpha_eq_3_5]; norm_num
  have hmul :=
    mul_lt_mul_of_pos_left hlog (mul_pos hc hαpos)
  linarith

/-!
## Strong-sector kernel bridge (discharged on integrable shells)
-/

structure StrongSectorCurvatureKernelBridge (s : Hqiv.Topology.HopfShell) (m : ℕ) (c : ℝ) where
  chart_index : hopfChartShellIndex s = m
  contact_is_kernel :
    hopfTrappedSelectionFromShell s c = curvatureLogAmplification (hopfContactLogInnerArgument s) c
  ladder_is_kernel :
    traceSelectionLogAmplification m c = curvatureLogAmplification (ladderLogArgumentAtChartShell m) c
  contact_log_lt_ladder :
    hopfContactLogInnerArgument s < ladderLogArgumentAtChartShell m
  kernel_ordering :
    hopfTrappedSelectionFromShell s c < traceSelectionLogAmplification m c

theorem strongSectorCurvatureKernelBridge_mk
    (s : Hqiv.Topology.HopfShell) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (hα : s.effectiveAlpha = none)
    (hm : hopfChartShellIndex s = m)
    (hlt : hopfContactLogInnerArgument s < ladderLogArgumentAtChartShell m) :
    StrongSectorCurvatureKernelBridge s m c where
  chart_index := hm
  contact_is_kernel := hopfTrappedSelectionFromShell_eq_curvatureLogAmplification_contact s c hα
  ladder_is_kernel := traceSelectionLogAmplification_eq_curvatureLogAmplification_ladder m c
  contact_log_lt_ladder := hlt
  kernel_ordering := hopfKernel_lt_ladderKernel_of_contact_lt_ladder s m c hc hα hlt

theorem hopfShellForGeneration_zero_effectiveAlpha :
    (hopfShellForGeneration 0).effectiveAlpha = none := by
  rw [hopfShellForGeneration_zero]; rfl

theorem hopfShellForGeneration_one_effectiveAlpha :
    (hopfShellForGeneration 1).effectiveAlpha = none := by
  rw [hopfShellForGeneration_one]; rfl

theorem t12_heavy_shell_effectiveAlpha :
    t12_heavy_shell.effectiveAlpha = none := by
  unfold t12_heavy_shell Hqiv.Topology.mkIntegrable; rfl

noncomputable def strongSectorKernelBridge_generation_zero :
    StrongSectorCurvatureKernelBridge (hopfShellForGeneration 0) 2 1 :=
  strongSectorCurvatureKernelBridge_mk (hopfShellForGeneration 0) 2 1 (by norm_num)
    hopfShellForGeneration_zero_effectiveAlpha hopfShellForGeneration_chartShellIndex_zero
    contactLogArgument_lt_ladderLogArgument_chart_two

noncomputable def strongSectorKernelBridge_generation_one :
    StrongSectorCurvatureKernelBridge (hopfShellForGeneration 1) 3 1 :=
  strongSectorCurvatureKernelBridge_mk (hopfShellForGeneration 1) 3 1 (by norm_num)
    hopfShellForGeneration_one_effectiveAlpha hopfShellForGeneration_chartShellIndex_one
    contactLogArgument_lt_ladderLogArgument_chart_three

noncomputable def strongSectorCurvatureKernelBridge_heavy_chart :
    StrongSectorCurvatureKernelBridge t12_heavy_shell 4 1 :=
  strongSectorCurvatureKernelBridge_mk t12_heavy_shell 4 1 (by norm_num)
    t12_heavy_shell_effectiveAlpha hopfChartShellIndex_t12_heavy
    contactLogArgument_lt_ladderLogArgument_chart_four

/-!
## QCD binding alias + finite colour chart
-/

theorem E_bind_QCD_from_network_eq_E_bind_from_network
    (m : ℕ) (w : NetworkWeight) (c : ℝ) :
    E_bind_QCD_from_network m w c = E_bind_from_network m w c := rfl

/-!
## Bundled ontology certificate
-/

structure GluonCurvatureOntologyDischarged where
  heavy_trapped_witness : T11T12TrappedCasimirWitness t12_heavy_shell 4 1
  qcd_binding_is_network : ∀ (m : ℕ) (w : NetworkWeight) (c : ℝ),
    E_bind_QCD_from_network m w c = E_bind_from_network m w c
  kernel_bridge_light : StrongSectorCurvatureKernelBridge (hopfShellForGeneration 0) 2 1
  kernel_bridge_middle : StrongSectorCurvatureKernelBridge (hopfShellForGeneration 1) 3 1
  kernel_bridge_heavy : StrongSectorCurvatureKernelBridge t12_heavy_shell 4 1
  color_chart_has_sorted_triple_table : colorSu3SortedNonzeroTriples.Nonempty

noncomputable def gluonCurvatureOntologyDischarged : GluonCurvatureOntologyDischarged where
  heavy_trapped_witness := t11T12TrappedCasimirWitnessHeavyChart
  qcd_binding_is_network := E_bind_QCD_from_network_eq_E_bind_from_network
  kernel_bridge_light := strongSectorKernelBridge_generation_zero
  kernel_bridge_middle := strongSectorKernelBridge_generation_one
  kernel_bridge_heavy := strongSectorCurvatureKernelBridge_heavy_chart
  color_chart_has_sorted_triple_table :=
    ⟨((0, 1, 2) : Fin 8 × Fin 8 × Fin 8), by simp [colorSu3SortedNonzeroTriples]⟩

#check gluonCurvatureOntologyDischarged
#check StrongSectorCurvatureKernelBridge
#check curvatureLogAmplification

end Hqiv.Physics
