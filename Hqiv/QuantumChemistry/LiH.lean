import Hqiv.QuantumChemistry.FiniteSiteQuantumChemistry

/-!
# LiH finite-site orbital scaffold (`s` + `p`)

This module extends the finite-site chemistry bridge to the first non-`s` benchmark:
LiH valence bookkeeping with explicit `p`-channel weight on Li.

We keep the same HQIV shell ladder and finite sums; no classical molecular PDE closure
is introduced here.
-/

namespace Hqiv.QuantumChemistry

open Hqiv

/-- Three-site valence scaffold for LiH:
`0 = Li(s)`, `1 = Li(p)`, `2 = H(s)`. -/
def lihValenceSpec (mLiS mLiP mH : ℕ) : OrbitalSiteChemistrySpec 3 where
  shell := fun i =>
    if (i : ℕ) = 0 then mLiS else if (i : ℕ) = 1 then mLiP else mH
  channel := fun i =>
    if (i : ℕ) = 0 then .s else if (i : ℕ) = 1 then .p else .s

/-- Channel-faithful LiH valence site-energy trace (`s=1`, `p=3`). -/
noncomputable def lihValenceSiteEnergyTrace (mLiS mLiP mH : ℕ) : ℝ :=
  orbitalWeightedSiteEnergyTrace (lihValenceSpec mLiS mLiP mH)

theorem lihValenceSiteEnergyTrace_eq (mLiS mLiP mH : ℕ) :
    lihValenceSiteEnergyTrace mLiS mLiP mH =
      Hqiv.ProteinResearch.latticeFullModeEnergy mLiS +
      3 * Hqiv.ProteinResearch.latticeFullModeEnergy mLiP +
      Hqiv.ProteinResearch.latticeFullModeEnergy mH := by
  unfold lihValenceSiteEnergyTrace orbitalWeightedSiteEnergyTrace lihValenceSpec
  simp [orbitalDegeneracy, Fin.sum_univ_three]

theorem lihValenceSiteEnergyTrace_nonneg (mLiS mLiP mH : ℕ) :
    0 ≤ lihValenceSiteEnergyTrace mLiS mLiP mH := by
  rw [lihValenceSiteEnergyTrace_eq]
  nlinarith [latticeFullModeEnergy_nonneg mLiS, latticeFullModeEnergy_nonneg mLiP,
    latticeFullModeEnergy_nonneg mH]

/-- `s`-only proxy (kept for calibration comparison). -/
noncomputable def lihSOnlyProxySiteEnergyTrace (mLiS mH : ℕ) : ℝ :=
  Hqiv.ProteinResearch.latticeFullModeEnergy mLiS +
    Hqiv.ProteinResearch.latticeFullModeEnergy mH

/-- Explicit Li `p`-shell uplift over the `s`-only proxy. -/
noncomputable def lihPShellUpliftSiteEnergy (mLiP : ℕ) : ℝ :=
  3 * Hqiv.ProteinResearch.latticeFullModeEnergy mLiP

theorem lihValenceSiteEnergyTrace_eq_proxy_plus_pUplift (mLiS mLiP mH : ℕ) :
    lihValenceSiteEnergyTrace mLiS mLiP mH =
      lihSOnlyProxySiteEnergyTrace mLiS mH + lihPShellUpliftSiteEnergy mLiP := by
  rw [lihValenceSiteEnergyTrace_eq]
  unfold lihSOnlyProxySiteEnergyTrace lihPShellUpliftSiteEnergy
  ring

/-- Channel-faithful LiH valence mode-budget trace (`accessibleModeBudgetUpToShell`). -/
noncomputable def lihValenceModeBudgetTrace (mLiS mLiP mH : ℕ) : ℝ :=
  orbitalWeightedModeBudgetTrace (lihValenceSpec mLiS mLiP mH)

theorem lihValenceModeBudgetTrace_eq (mLiS mLiP mH : ℕ) :
    lihValenceModeBudgetTrace mLiS mLiP mH =
      Hqiv.Physics.accessibleModeBudgetUpToShell mLiS +
      3 * Hqiv.Physics.accessibleModeBudgetUpToShell mLiP +
      Hqiv.Physics.accessibleModeBudgetUpToShell mH := by
  unfold lihValenceModeBudgetTrace orbitalWeightedModeBudgetTrace lihValenceSpec
  simp [orbitalDegeneracy, Fin.sum_univ_three]

theorem lihValenceModeBudgetTrace_nonneg (mLiS mLiP mH : ℕ) :
    0 ≤ lihValenceModeBudgetTrace mLiS mLiP mH := by
  rw [lihValenceModeBudgetTrace_eq]
  nlinarith [Hqiv.Physics.accessibleModeBudgetUpToShell_nonneg mLiS,
    Hqiv.Physics.accessibleModeBudgetUpToShell_nonneg mLiP,
    Hqiv.Physics.accessibleModeBudgetUpToShell_nonneg mH]

end Hqiv.QuantumChemistry

