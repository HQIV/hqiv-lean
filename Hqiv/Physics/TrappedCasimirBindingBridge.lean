import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.BoundStates
import Hqiv.Physics.CasimirForceFromAction
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Topology.HopfShellComplex

/-!
# Trapped Casimir ↔ binding coupling (T11/T12 closure layer)

**Ontology:** hadronic binding is not an independent gluon sector; it is trapped
Planck/Casimir zero-point on the closed carrier, filtered by an SO(8) composite-trace
selection.  The binding cell `latticeSimplexCount m · α_eff(m)` factorizes as

`available_modes m / 4 · (φ(m)/2) · (α_eff(m) / (φ(m)/2))`.

The middle slot is per-mode trapped zero-point; the last slot is the normalized SO(8)
trace selection.  T11/T12 Hopf contact data supplies the **contact amplification**
witness on integrable shells; proving it reproduces `α_eff/(φ/2)` shell-by-shell
remains open except at the structural identification below.

No new axioms; no `sorry`.
-/

namespace Hqiv.Physics

open Hqiv

/-!
## Normalized SO(8) selection and trapped Casimir cell
-/

/-- Per-generator SO(8) trace selection: effective coupling relative to one Casimir mode cell. -/
noncomputable def normalizedSO8TraceSelection (m : ℕ) (c : ℝ := 1) : ℝ :=
  alphaEffAtShell m c / casimirPerModeZeroPoint m

/-- One lattice site's trapped Casimir coupling (`α_eff` packaged as mode cell × selection). -/
noncomputable def trappedCasimirCouplingCell (m : ℕ) (c : ℝ := 1) : ℝ :=
  casimirPerModeZeroPoint m * normalizedSO8TraceSelection m c

/-- Full trapped zero-point budget at shell `m` (`available_modes · φ/2`). -/
noncomputable def trappedCasimirEnergyAtShell (m : ℕ) : ℝ :=
  available_modes m * casimirPerModeZeroPoint m

theorem casimirPerModeZeroPoint_pos (m : ℕ) : 0 < casimirPerModeZeroPoint m := by
  rw [casimirPerModeZeroPoint_eq_phi_half]
  exact div_pos (phi_of_shell_pos m) (by norm_num : (0 : ℝ) < 2)

theorem oneOverAlphaEffAtShell_pos (m : ℕ) (c : ℝ) (hc : 0 ≤ c) : 0 < oneOverAlphaEffAtShell m c := by
  unfold oneOverAlphaEffAtShell oneOverAlphaBare
  have h42 : 0 < (42 : ℝ) := by norm_num
  have hlog : 0 ≤ Real.log (phi_of_shell m + 1) := by
    apply Real.log_nonneg
    have hphi : 1 ≤ phi_of_shell m + 1 := by
      have hphi2 : (2 : ℝ) ≤ phi_of_shell m := phi_of_shell_ge_two m
      nlinarith
    linarith
  have hα : 0 ≤ alpha := by rw [alpha_eq_3_5]; positivity
  have hterm : 0 ≤ c * alpha * Real.log (phi_of_shell m + 1) :=
    mul_nonneg (mul_nonneg hc hα) hlog
  have hden : 0 < 1 + c * alpha * Real.log (phi_of_shell m + 1) := by linarith
  exact mul_pos h42 hden

theorem alphaEffAtShell_pos (m : ℕ) (c : ℝ) (hc : 0 ≤ c) : 0 < alphaEffAtShell m c := by
  unfold alphaEffAtShell
  exact inv_pos.mpr (oneOverAlphaEffAtShell_pos m c hc)

theorem normalizedSO8TraceSelection_pos (m : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    0 < normalizedSO8TraceSelection m c := by
  unfold normalizedSO8TraceSelection
  exact div_pos (alphaEffAtShell_pos m c hc) (casimirPerModeZeroPoint_pos m)

theorem trappedCasimirCouplingCell_eq_alphaEffAtShell (m : ℕ) (c : ℝ) :
    trappedCasimirCouplingCell m c = alphaEffAtShell m c := by
  unfold trappedCasimirCouplingCell normalizedSO8TraceSelection
  field_simp [ne_of_gt (casimirPerModeZeroPoint_pos m)]

theorem normalizedSO8TraceSelection_eq_alpha_over_casimirPerMode (m : ℕ) (c : ℝ) :
    normalizedSO8TraceSelection m c = alphaEffAtShell m c / casimirPerModeZeroPoint m := rfl

theorem trappedCasimirEnergyAtShell_eq_available_modes_times_perMode (m : ℕ) :
    trappedCasimirEnergyAtShell m = available_modes m * casimirPerModeZeroPoint m := rfl

/-!
## Binding cell = lattice × trapped Casimir cell
-/

theorem trappedCasimirEnergyAtShell_eq_electronShellCasimirEnergy (m : ℕ) :
    trappedCasimirEnergyAtShell m = electronShellCasimirEnergy m := by
  unfold trappedCasimirEnergyAtShell electronShellCasimirEnergy
  rw [casimirPerModeZeroPoint_eq_phi_half]
  unfold omegaCasimir
  ring

theorem bindingCouplingAtShell_eq_lattice_trappedCasimirCell
    (m : ℕ) (k : So8Index) (c : ℝ) :
    bindingCouplingAtShell m k c =
      (latticeSimplexCount m : ℝ) * trappedCasimirCouplingCell m c := by
  unfold bindingCouplingAtShell
  rw [← trappedCasimirCouplingCell_eq_alphaEffAtShell]

theorem bindingCouplingAtShell_eq_availableModes_quarter_trappedCasimirCell
    (m : ℕ) (k : So8Index) (c : ℝ) :
    bindingCouplingAtShell m k c =
      available_modes m / 4 * trappedCasimirCouplingCell m c := by
  rw [bindingCouplingAtShell_eq_lattice_trappedCasimirCell]
  unfold available_modes
  ring

theorem bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection
    (m : ℕ) (k : So8Index) (c : ℝ) :
    bindingCouplingAtShell m k c =
      trappedCasimirEnergyAtShell m / 4 * normalizedSO8TraceSelection m c := by
  rw [bindingCouplingAtShell_eq_availableModes_quarter_trappedCasimirCell]
  unfold trappedCasimirCouplingCell normalizedSO8TraceSelection
  rw [trappedCasimirEnergyAtShell_eq_available_modes_times_perMode]
  field_simp [ne_of_gt (casimirPerModeZeroPoint_pos m)]

theorem E_bind_from_network_eq_sum_trappedCasimirCells
    (m : ℕ) (w : NetworkWeight) (c : ℝ) :
    E_bind_from_network m w c =
      (∑ k : So8Index, w k) * trappedCasimirCouplingCell m c *
        (latticeSimplexCount m : ℝ) := by
  unfold E_bind_from_network
  simp_rw [bindingCouplingAtShell_eq_lattice_trappedCasimirCell]
  rw [← Finset.sum_mul]
  ring

/-!
## T11/T12 Hopf contact trapping (integrable shells)
-/

/-- Hopf-shell contact trapping factor (T11 phase-lift + T12 imprint). -/
noncomputable def hopfTrappedSelectionFromShell (s : Hqiv.Topology.HopfShell) (c : ℝ := 1) : ℝ :=
  1 + c * s.curvatureImprintAlpha *
    Real.log (1 + Hqiv.Algebra.phaseLiftCoeff s.winding * s.curvatureImprintAlpha)

theorem t12_heavy_shell_winding_eq_three :
    t12_heavy_shell.winding = 3 := by
  unfold t12_heavy_shell Hqiv.Topology.mkIntegrable
  decide

theorem heavy_hopf_trappedSelection_eq_t12 (c : ℝ) :
    trappingSelectionFromHeavyHopfShellWithAlpha
      (Hqiv.Topology.HopfShell.curvatureImprintAlpha t12_heavy_shell) c =
      hopfTrappedSelectionFromShell t12_heavy_shell c := by
  unfold trappingSelectionFromHeavyHopfShellWithAlpha hopfTrappedSelectionFromShell
  rw [t12_heavy_shell_curvatureImprintAlpha, t12_heavy_shell_winding_eq_three]

theorem hopfTrappedSelectionFromShell_pos (s : Hqiv.Topology.HopfShell) (c : ℝ)
    (hc : 0 ≤ c) (hα : 0 < s.curvatureImprintAlpha) :
    0 < hopfTrappedSelectionFromShell s c := by
  unfold hopfTrappedSelectionFromShell
  have hpl : 0 < Hqiv.Algebra.phaseLiftCoeff s.winding :=
    Hqiv.Algebra.phaseLiftCoeff_pos s.winding
  have hinside : 1 < 1 + Hqiv.Algebra.phaseLiftCoeff s.winding * s.curvatureImprintAlpha := by
    nlinarith [Hqiv.Algebra.phaseLiftCoeff_pos s.winding, hα]
  have hlog : 0 < Real.log (1 + Hqiv.Algebra.phaseLiftCoeff s.winding * s.curvatureImprintAlpha) :=
    Real.log_pos hinside
  have hterm :
      0 ≤ c * s.curvatureImprintAlpha *
        Real.log (1 + Hqiv.Algebra.phaseLiftCoeff s.winding * s.curvatureImprintAlpha) :=
    mul_nonneg (mul_nonneg hc (le_of_lt hα)) (le_of_lt hlog)
  linarith

theorem t12_heavy_hopfTrappedSelection_pos :
    0 < hopfTrappedSelectionFromShell t12_heavy_shell 1 :=
  hopfTrappedSelectionFromShell_pos t12_heavy_shell 1 (by norm_num) (by
    rw [t12_heavy_shell_curvatureImprintAlpha]
    norm_num)

/-- **Ordering lemma only:** heavy T11 contact coefficient exceeds the T13 outer
witness factor `1/140`.  This does not validate neutrino masses — the derived
ladder overshoots PDG/cosmology by many orders of magnitude (see audit doc). -/
theorem heavyHopfTorsionCoefficient_gt_outerHorizonNeutrinoSuppression :
    t12_heavy_torsion_coeff > outerHorizonNeutrinoSuppression := by
  rw [t12_heavy_torsion_coeff_eq_four_fifths, outerHorizonNeutrinoSuppression_eq_inv_140]
  norm_num

/-!
## Closure predicate (structural + witness)
-/

/-- T11/T12 data is present on shell `m` and the binding cell is trapped Casimir × selection. -/
structure T11T12TrappedCasimirWitness (s : Hqiv.Topology.HopfShell) (m : ℕ) (c : ℝ) where
  chartShell : s.winding + 1 = m
  binding_is_trapped :
    ∀ k : So8Index,
      bindingCouplingAtShell m k c =
        trappedCasimirEnergyAtShell m / 4 * normalizedSO8TraceSelection m c

/-- Bundled witness at the heavy TUFT chart shell (export pin `referenceM` today). -/
noncomputable def t11T12TrappedCasimirWitnessHeavyChart : T11T12TrappedCasimirWitness t12_heavy_shell 4 1 where
  chartShell := by rw [t12_heavy_shell_winding_eq_three]
  binding_is_trapped := fun k =>
    bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection 4 k 1

/-- **Conditional closure:** network binding uses trapped Casimir cells when weights are supplied. -/
theorem E_bind_from_network_eq_trappedCasimir_quarter_selection
    (m : ℕ) (w : NetworkWeight) (c : ℝ) (k : So8Index) :
    w k * bindingCouplingAtShell m k c =
      w k * trappedCasimirEnergyAtShell m / 4 * normalizedSO8TraceSelection m c := by
  rw [bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection]
  ring

#check trappedCasimirCouplingCell_eq_alphaEffAtShell
#check bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection
#check heavyHopfTorsionCoefficient_gt_outerHorizonNeutrinoSuppression
#check t11T12TrappedCasimirWitnessHeavyChart

end Hqiv.Physics
