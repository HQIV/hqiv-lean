import Hqiv.QuantumChemistry.FiniteSiteQuantumChemistry

/-!
# H₂ finite-site first-principles layer

This module specializes the canonical finite-site chemistry bridge to a two-site
(`Fin 2`) hydrogen molecule scaffold. The site-energy law is inherited from the
same HQIV shell ladder (`available_modes`, `phi_of_shell`) with no fitted term.
-/

namespace Hqiv.QuantumChemistry

open Hqiv

/-- Two-site shell assignment for an H₂ scaffold. -/
def h2Spec (mLeft mRight : ℕ) : FiniteSiteChemistrySpec 2 where
  shell := fun i => if (i : ℕ) = 0 then mLeft else mRight

/-- H₂ canonical site-energy trace from the finite-site chemistry bridge. -/
noncomputable def h2SiteEnergyTrace (mLeft mRight : ℕ) : ℝ :=
  siteEnergyTrace (h2Spec mLeft mRight)

theorem h2SiteEnergyTrace_eq (mLeft mRight : ℕ) :
    h2SiteEnergyTrace mLeft mRight =
      Hqiv.ProteinResearch.latticeFullModeEnergy mLeft +
      Hqiv.ProteinResearch.latticeFullModeEnergy mRight := by
  unfold h2SiteEnergyTrace siteEnergyTrace h2Spec Hqiv.ProteinResearch.atomSiteEnergyMatrix
  simp [Matrix.trace_diagonal]

theorem h2SiteEnergyTrace_nonneg (mLeft mRight : ℕ) :
    0 ≤ h2SiteEnergyTrace mLeft mRight := by
  rw [h2SiteEnergyTrace_eq]
  exact add_nonneg (latticeFullModeEnergy_nonneg mLeft) (latticeFullModeEnergy_nonneg mRight)

theorem h2SiteEnergyTrace_same_shell (m : ℕ) :
    h2SiteEnergyTrace m m = 2 * Hqiv.ProteinResearch.latticeFullModeEnergy m := by
  rw [h2SiteEnergyTrace_eq]
  ring

/-- Closed form at equal shells: directly from `available_modes` and `phi_of_shell`. -/
theorem h2SiteEnergyTrace_same_shell_closed_form (m : ℕ) :
    h2SiteEnergyTrace m m = 8 * (m + 2 : ℝ) * (m + 1 : ℝ) ^ 2 := by
  rw [h2SiteEnergyTrace_same_shell, latticeFullModeEnergy_closed_form]
  ring

/-- Proton anchor shell (`referenceM = 4`) from the light-cone ladder. -/
theorem referenceM_eq_four : Hqiv.referenceM = 4 := by
  unfold Hqiv.referenceM Hqiv.qcdShell Hqiv.stepsFromQCDToLockin Hqiv.latticeStepCount
  norm_num

/-- H₂ equal-shell trace at the proton anchor `m = referenceM = 4`. -/
theorem h2SiteEnergyTrace_referenceM_eq :
    h2SiteEnergyTrace Hqiv.referenceM Hqiv.referenceM =
      8 * (Hqiv.referenceM + 2 : ℝ) * (Hqiv.referenceM + 1 : ℝ) ^ 2 := by
  simpa using h2SiteEnergyTrace_same_shell_closed_form Hqiv.referenceM

/-- Numeric closed form at the proton anchor shell `m = 4`. -/
theorem h2SiteEnergyTrace_referenceM_numeric :
    h2SiteEnergyTrace Hqiv.referenceM Hqiv.referenceM = 1200 := by
  have h4 : h2SiteEnergyTrace 4 4 = 1200 := by
    have h := h2SiteEnergyTrace_same_shell_closed_form 4
    norm_num at h
    exact h
  simpa [referenceM_eq_four] using h4

end Hqiv.QuantumChemistry
