import Hqiv.QuantumChemistry.FiniteSiteQuantumChemistry
import Hqiv.Physics.ReadoutGaugeSeed

/-!
# LiH finite-site orbital scaffold (`s` + `p`)

This module extends the finite-site chemistry bridge to the first non-`s` benchmark:
LiH valence bookkeeping with explicit `p`-channel weight on Li.

We keep the same HQIV shell ladder and finite sums; no classical molecular PDE closure
is introduced here.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics

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

/-! ## LiH Compton-shell ξ / Ωₖ bridge -/

/-- Li(s) shell used by the Compton LiH readout. -/
def lihComptonLiSShell : ℕ := 4

/-- Li(p) shell used by the Compton LiH readout. -/
def lihComptonLiPShell : ℕ := 3

/-- H(s) shell used by the Compton LiH readout. -/
def lihComptonHSShell : ℕ := 1

theorem lihValenceSpec_compton_LiS :
    (lihValenceSpec lihComptonLiSShell lihComptonLiPShell lihComptonHSShell).shell
      ⟨0, by decide⟩ = lihComptonLiSShell := by
  simp [lihValenceSpec]

theorem lihValenceSpec_compton_LiP :
    (lihValenceSpec lihComptonLiSShell lihComptonLiPShell lihComptonHSShell).shell
      ⟨1, by decide⟩ = lihComptonLiPShell := by
  simp [lihValenceSpec]

theorem lihValenceSpec_compton_HS :
    (lihValenceSpec lihComptonLiSShell lihComptonLiPShell lihComptonHSShell).shell
      ⟨2, by decide⟩ = lihComptonHSShell := by
  simp [lihValenceSpec]

/-- Canonical Compton LiH valence assignment: `lihValenceSpec 4 3 1`. -/
noncomputable def lihComptonValenceSpec : OrbitalSiteChemistrySpec 3 :=
  lihValenceSpec lihComptonLiSShell lihComptonLiPShell lihComptonHSShell

theorem lihComptonValenceSpec_eq :
    lihComptonValenceSpec =
      lihValenceSpec lihComptonLiSShell lihComptonLiPShell lihComptonHSShell := rfl

/--
The three Compton shells used by `lihComptonValenceSpec` are exactly
`lihComptonLiSShell = 4`, `lihComptonLiPShell = 3`, and `lihComptonHSShell = 1`.
-/
theorem lihComptonUsedShells_eq_spec :
    lihComptonLiSShell = 4 ∧
      lihComptonLiPShell = 3 ∧
        lihComptonHSShell = 1 ∧
          lihComptonValenceSpec.shell ⟨0, by decide⟩ = lihComptonLiSShell ∧
            lihComptonValenceSpec.shell ⟨1, by decide⟩ = lihComptonLiPShell ∧
              lihComptonValenceSpec.shell ⟨2, by decide⟩ = lihComptonHSShell := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact lihValenceSpec_compton_LiS
  · exact lihValenceSpec_compton_LiP
  · exact lihValenceSpec_compton_HS

/--
Local increment form of the discrete-continuous Ωₖ bridge at one integer shell.

This is intentionally weaker than `ContinuousXiPath.OmegaKIntegerBridge`: LiH only
needs adjacent increments at its three Compton readout shells, not a global
identification of the analytic primitive with the finite null-lattice sum.
-/
def lihLocalOmegaKIncrementBridge (n : ℕ) : Prop :=
  ContinuousXiPath.omegaK_xi (xiOfShell (n + 1)) -
      ContinuousXiPath.omegaK_xi (xiOfShell n) =
    omega_k_partial (n + 1) - omega_k_partial n

/-- Finite Ωₖ bridge payload for the LiH Compton shells `(4,3,1)`. -/
structure LiHComptonOmegaKBridge where
  liS : lihLocalOmegaKIncrementBridge lihComptonLiSShell
  liP : lihLocalOmegaKIncrementBridge lihComptonLiPShell
  hS : lihLocalOmegaKIncrementBridge lihComptonHSShell

theorem lihLocalOmegaKIncrementBridge_from_global
    (hΩ : Hqiv.readoutOmegaKIntegerBridge) (n : ℕ) :
    lihLocalOmegaKIncrementBridge n :=
  ContinuousXiPath.omegaK_xi_integer_increment_bridge hΩ n

theorem liHComptonOmegaKBridge_from_global
    (hΩ : Hqiv.readoutOmegaKIntegerBridge) : LiHComptonOmegaKBridge where
  liS := lihLocalOmegaKIncrementBridge_from_global hΩ lihComptonLiSShell
  liP := lihLocalOmegaKIncrementBridge_from_global hΩ lihComptonLiPShell
  hS := lihLocalOmegaKIncrementBridge_from_global hΩ lihComptonHSShell

theorem imprintWeightedReadoutPhase_xi_matches_integer_step_of_local_bridge
    {n : ℕ} (hΩ : lihLocalOmegaKIncrementBridge n) :
    Hqiv.imprintWeightedReadoutPhase_xi_alias
        (xiOfShell n) (xiOfShell (n + 1)) =
      Hqiv.imprintWeightedReadoutPhase n := by
  unfold Hqiv.imprintWeightedReadoutPhase_xi_alias
  unfold ContinuousXiPath.imprintWeightedReadoutPhase_xi
  unfold Hqiv.imprintWeightedReadoutPhase
  rw [ContinuousXiPath.phi_xi_chart]
  rw [hΩ]

/-- Li(s) Compton shell: continuous-ξ and discrete imprint phases match at `m = 4`. -/
theorem lihCompton_LiS_imprintWeightedReadoutPhase_xi_matches
    (hΩ : LiHComptonOmegaKBridge) :
    Hqiv.imprintWeightedReadoutPhase_xi_alias
        (xiOfShell lihComptonLiSShell) (xiOfShell (lihComptonLiSShell + 1)) =
      Hqiv.imprintWeightedReadoutPhase lihComptonLiSShell :=
  imprintWeightedReadoutPhase_xi_matches_integer_step_of_local_bridge hΩ.liS

/-- Li(p) Compton shell: continuous-ξ and discrete imprint phases match at `m = 3`. -/
theorem lihCompton_LiP_imprintWeightedReadoutPhase_xi_matches
    (hΩ : LiHComptonOmegaKBridge) :
    Hqiv.imprintWeightedReadoutPhase_xi_alias
        (xiOfShell lihComptonLiPShell) (xiOfShell (lihComptonLiPShell + 1)) =
      Hqiv.imprintWeightedReadoutPhase lihComptonLiPShell :=
  imprintWeightedReadoutPhase_xi_matches_integer_step_of_local_bridge hΩ.liP

/-- H(s) Compton shell: continuous-ξ and discrete imprint phases match at `m = 1`. -/
theorem lihCompton_HS_imprintWeightedReadoutPhase_xi_matches
    (hΩ : LiHComptonOmegaKBridge) :
    Hqiv.imprintWeightedReadoutPhase_xi_alias
        (xiOfShell lihComptonHSShell) (xiOfShell (lihComptonHSShell + 1)) =
      Hqiv.imprintWeightedReadoutPhase lihComptonHSShell :=
  imprintWeightedReadoutPhase_xi_matches_integer_step_of_local_bridge hΩ.hS

end Hqiv.QuantumChemistry

