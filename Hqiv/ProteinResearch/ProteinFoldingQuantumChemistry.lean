import Mathlib.Algebra.BigOperators.Ring.Finset
import Hqiv.QuantumChemistry.FiniteSiteQuantumChemistry

/-!
# Protein folding: research wrapper over canonical quantum-chemistry module

Canonical finite-site quantum-chemistry proofs now live in:

* `Hqiv.QuantumChemistry.FiniteSiteQuantumChemistry`

This `ProteinResearch` file remains as a compatibility layer so research modules and
existing imports keep working while the formal chemistry stack is organized in a more
traditional module path.
-/

namespace Hqiv.ProteinResearch

variable {n : ℕ}

abbrev ProteinFoldingSiteEnergySpec (n : ℕ) := Hqiv.QuantumChemistry.FiniteSiteChemistrySpec n

noncomputable def siteEnergyTrace {n : ℕ} (s : ProteinFoldingSiteEnergySpec n) : ℝ :=
  Hqiv.QuantumChemistry.siteEnergyTrace s

noncomputable def siteModeBudgetTrace {n : ℕ} (s : ProteinFoldingSiteEnergySpec n) : ℝ :=
  Hqiv.QuantumChemistry.siteModeBudgetTrace s

noncomputable def siteModeBudgetTraceFromPhiTime {n : ℕ} (s : ProteinFoldingSiteEnergySpec n) (t : ℝ) : ℝ :=
  Hqiv.QuantumChemistry.siteModeBudgetTraceFromPhiTime s t

theorem latticeFullModeEnergy_nonneg (m : ℕ) : 0 ≤ latticeFullModeEnergy m :=
  Hqiv.QuantumChemistry.latticeFullModeEnergy_nonneg m

theorem listLatticeEnergySum_nonneg (shells : List ℕ) : 0 ≤ listLatticeEnergySum shells :=
  Hqiv.QuantumChemistry.listLatticeEnergySum_nonneg shells

theorem atomSiteEnergyMatrix_trace_nonneg (shell : Fin n → ℕ) :
    0 ≤ Matrix.trace (atomSiteEnergyMatrix shell) :=
  Hqiv.QuantumChemistry.atomSiteEnergyMatrix_trace_nonneg shell

theorem siteEnergyTrace_nonneg (s : ProteinFoldingSiteEnergySpec n) : 0 ≤ siteEnergyTrace s :=
  Hqiv.QuantumChemistry.siteEnergyTrace_nonneg s

theorem siteModeBudgetTrace_nonneg (s : ProteinFoldingSiteEnergySpec n) :
    0 ≤ siteModeBudgetTrace s :=
  Hqiv.QuantumChemistry.siteModeBudgetTrace_nonneg s

theorem siteModeBudgetTraceFromPhiTime_nonneg
    (s : ProteinFoldingSiteEnergySpec n) (t : ℝ) :
    0 ≤ siteModeBudgetTraceFromPhiTime s t :=
  Hqiv.QuantumChemistry.siteModeBudgetTraceFromPhiTime_nonneg s t

theorem siteModeBudgetTraceFromPhiTime_unit_eq_siteModeBudgetTrace
    (s : ProteinFoldingSiteEnergySpec n) :
    siteModeBudgetTraceFromPhiTime s 1 = siteModeBudgetTrace s :=
  Hqiv.QuantumChemistry.siteModeBudgetTraceFromPhiTime_unit_eq_siteModeBudgetTrace s

end Hqiv.ProteinResearch
