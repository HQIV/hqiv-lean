import Hqiv.QuantumChemistry.H2

/-!
# Molecule outputs: site-energy layer and generalization

Lean-side output layer for molecular site-energy expressions:

* concrete two-site (`H₂`) and three-site (`H₂O`) outputs,
* generalized `n`-site output maps and budget identities.

This stays on the canonical finite-site first-principles chain
(`available_modes`, `phi_of_shell`, finite-patch budgets).
-/

namespace Hqiv.QuantumChemistry

open Hqiv

/-- Molecule output on the canonical finite-site site-energy trace. -/
noncomputable def moleculeSiteOutput {n : ℕ} (s : FiniteSiteChemistrySpec n) : ℝ :=
  siteEnergyTrace s

theorem moleculeSiteOutput_nonneg {n : ℕ} (s : FiniteSiteChemistrySpec n) :
    0 ≤ moleculeSiteOutput s :=
  siteEnergyTrace_nonneg s

/-- Molecule output on the canonical finite-site mode-budget trace. -/
noncomputable def moleculeModeBudgetOutput {n : ℕ} (s : FiniteSiteChemistrySpec n) : ℝ :=
  siteModeBudgetTrace s

theorem moleculeModeBudgetOutput_nonneg {n : ℕ} (s : FiniteSiteChemistrySpec n) :
    0 ≤ moleculeModeBudgetOutput s :=
  siteModeBudgetTrace_nonneg s

theorem moleculeModeBudgetOutput_fromPhiTime_unit {n : ℕ} (s : FiniteSiteChemistrySpec n) :
    siteModeBudgetTraceFromPhiTime s 1 = moleculeModeBudgetOutput s :=
  siteModeBudgetTraceFromPhiTime_unit_eq_siteModeBudgetTrace s

/-- Three-site specification (e.g. O/H/H indexing for an H₂O scaffold). -/
def h2oSiteSpec (mO mH₁ mH₂ : ℕ) : FiniteSiteChemistrySpec 3 where
  shell := fun i =>
    if (i : ℕ) = 0 then mO else if (i : ℕ) = 1 then mH₁ else mH₂

/-- Concrete H₂ output alias from the dedicated two-site module. -/
noncomputable def h2Output (mLeft mRight : ℕ) : ℝ :=
  h2SiteEnergyTrace mLeft mRight

/-- H₂ output on the QFT/QM-mode budget channel (same shells as `h2Output`). -/
noncomputable def h2ModeBudgetOutput (mLeft mRight : ℕ) : ℝ :=
  moleculeModeBudgetOutput (h2Spec mLeft mRight)

/-- Concrete H₂O-site output (site-energy only; pair terms are separate). -/
noncomputable def h2oOutput (mO mH₁ mH₂ : ℕ) : ℝ :=
  Hqiv.ProteinResearch.latticeFullModeEnergy mO +
    Hqiv.ProteinResearch.latticeFullModeEnergy mH₁ +
    Hqiv.ProteinResearch.latticeFullModeEnergy mH₂

theorem h2Output_same_shell_closed_form (m : ℕ) :
    h2Output m m = 8 * (m + 2 : ℝ) * (m + 1 : ℝ) ^ 2 :=
  h2SiteEnergyTrace_same_shell_closed_form m

theorem h2Output_referenceM_numeric :
    h2Output Hqiv.referenceM Hqiv.referenceM = 1200 :=
  h2SiteEnergyTrace_referenceM_numeric

theorem h2ModeBudgetOutput_eq_sum_accessibleShellBudgets (mLeft mRight : ℕ) :
    h2ModeBudgetOutput mLeft mRight =
      Hqiv.Physics.accessibleModeBudgetUpToShell mLeft +
      Hqiv.Physics.accessibleModeBudgetUpToShell mRight := by
  unfold h2ModeBudgetOutput moleculeModeBudgetOutput siteModeBudgetTrace h2Spec
  simp

theorem h2ModeBudgetOutput_fromPhiTime_unit (mLeft mRight : ℕ) :
    siteModeBudgetTraceFromPhiTime (h2Spec mLeft mRight) 1 = h2ModeBudgetOutput mLeft mRight := by
  simpa [h2ModeBudgetOutput] using moleculeModeBudgetOutput_fromPhiTime_unit (h2Spec mLeft mRight)

theorem h2oOutput_eq_sum_siteEnergies (mO mH₁ mH₂ : ℕ) :
    h2oOutput mO mH₁ mH₂ =
      Hqiv.ProteinResearch.latticeFullModeEnergy mO +
      Hqiv.ProteinResearch.latticeFullModeEnergy mH₁ +
      Hqiv.ProteinResearch.latticeFullModeEnergy mH₂ :=
  rfl

end Hqiv.QuantumChemistry
