import Hqiv.QuantumChemistry.LiH
import Hqiv.Geometry.BondedHorizonCasimir
import Hqiv.Geometry.ComptonNuclearTorus
import Hqiv.Physics.ComptonIRWindow

/-!
# LiH derivation scaffold (no empirical calibration)

This module packages a derivation-first LiH dissociation indicator in HQIV dimensionless units.
No fitted rescale is introduced.

Ingredients:

* bonded-horizon non-additivity (`bondHorizonSurplusDimless 4 3 1`),
* explicit Li `p`-channel uplift from the orbital-resolved finite-site chemistry layer.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics

/-- LiH dissociation-style bonded surplus in dimensionless HQIV units (`4 -> 3 + 1`). -/
noncomputable def lihBondedSurplusDimless
    (cfg : Hqiv.Geometry.NuclearTorusConfig := Hqiv.Geometry.defaultNuclearTorus) : ℝ :=
  Hqiv.Geometry.bondHorizonSurplusDimless 4 3 1 cfg

theorem lihBondedSurplusDimless_eq
    (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihBondedSurplusDimless cfg = Hqiv.Geometry.bondHorizonSurplusDimless 4 3 1 cfg := rfl

/-- Orbital-resolution correction over an `s`-only LiH proxy. -/
noncomputable def lihDerivedElectronicCorrectionDimless (mLiS mLiP mH : ℕ) : ℝ :=
  lihValenceSiteEnergyTrace mLiS mLiP mH - lihSOnlyProxySiteEnergyTrace mLiS mH

theorem lihDerivedElectronicCorrection_eq_p_uplift (mLiS mLiP mH : ℕ) :
    lihDerivedElectronicCorrectionDimless mLiS mLiP mH = lihPShellUpliftSiteEnergy mLiP := by
  unfold lihDerivedElectronicCorrectionDimless
  rw [lihValenceSiteEnergyTrace_eq_proxy_plus_pUplift]
  ring

theorem latticeFullModeEnergy_pos (m : ℕ) : 0 < Hqiv.ProteinResearch.latticeFullModeEnergy m := by
  rw [latticeFullModeEnergy_closed_form]
  positivity

theorem lihPShellUpliftSiteEnergy_nonneg (mLiP : ℕ) :
    0 ≤ lihPShellUpliftSiteEnergy mLiP := by
  unfold lihPShellUpliftSiteEnergy
  nlinarith [latticeFullModeEnergy_nonneg mLiP]

theorem lihPShellUpliftSiteEnergy_pos (mLiP : ℕ) :
    0 < lihPShellUpliftSiteEnergy mLiP := by
  unfold lihPShellUpliftSiteEnergy
  nlinarith [latticeFullModeEnergy_pos mLiP]

/-- Derivation-first LiH indicator in dimensionless units:
bonded-horizon surplus plus orbital (`p`) correction. -/
noncomputable def lihDerivedDissociationIndicatorDimless
    (mLiS mLiP mH : ℕ)
    (cfg : Hqiv.Geometry.NuclearTorusConfig := Hqiv.Geometry.defaultNuclearTorus) : ℝ :=
  lihBondedSurplusDimless cfg + lihDerivedElectronicCorrectionDimless mLiS mLiP mH

theorem lihDerivedDissociationIndicator_eq_bond_plus_p
    (mLiS mLiP mH : ℕ) (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihDerivedDissociationIndicatorDimless mLiS mLiP mH cfg =
      lihBondedSurplusDimless cfg + lihPShellUpliftSiteEnergy mLiP := by
  unfold lihDerivedDissociationIndicatorDimless
  rw [lihDerivedElectronicCorrection_eq_p_uplift]

theorem lihDerivedDissociationIndicator_ge_bond
    (mLiS mLiP mH : ℕ) (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihBondedSurplusDimless cfg ≤ lihDerivedDissociationIndicatorDimless mLiS mLiP mH cfg := by
  rw [lihDerivedDissociationIndicator_eq_bond_plus_p]
  nlinarith [lihPShellUpliftSiteEnergy_nonneg mLiP]

theorem lihDerivedDissociationIndicator_gt_bond
    (mLiS mLiP mH : ℕ) (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihBondedSurplusDimless cfg < lihDerivedDissociationIndicatorDimless mLiS mLiP mH cfg := by
  rw [lihDerivedDissociationIndicator_eq_bond_plus_p]
  nlinarith [lihPShellUpliftSiteEnergy_pos mLiP]

theorem lihDerivedDissociationIndicator_neg_iff_bond_plus_p_neg
    (mLiS mLiP mH : ℕ) (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihDerivedDissociationIndicatorDimless mLiS mLiP mH cfg < 0 ↔
      lihBondedSurplusDimless cfg + lihPShellUpliftSiteEnergy mLiP < 0 := by
  rw [lihDerivedDissociationIndicator_eq_bond_plus_p]

theorem lihDerivedDissociationIndicator_pos_iff_bond_plus_p_pos
    (mLiS mLiP mH : ℕ) (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    0 < lihDerivedDissociationIndicatorDimless mLiS mLiP mH cfg ↔
      0 < lihBondedSurplusDimless cfg + lihPShellUpliftSiteEnergy mLiP := by
  rw [lihDerivedDissociationIndicator_eq_bond_plus_p]

theorem lih_p_channel_necessity
    (mLiS mLiP mH : ℕ) :
    lihDerivedElectronicCorrectionDimless mLiS mLiP mH = lihPShellUpliftSiteEnergy mLiP := by
  exact lihDerivedElectronicCorrection_eq_p_uplift mLiS mLiP mH

/-- Participation-weighted LiH `p`-channel correction (`η_p ∈ (0,1)` from phase window). -/
noncomputable def lihDerivedElectronicCorrectionWithParticipationDimless
    (ηp : ℝ) (mLiP : ℕ) : ℝ :=
  ηp * lihPShellUpliftSiteEnergy mLiP

theorem lihDerivedElectronicCorrectionWithParticipation_nonneg
    (ηp : ℝ) (hηp : 0 ≤ ηp) (mLiP : ℕ) :
    0 ≤ lihDerivedElectronicCorrectionWithParticipationDimless ηp mLiP := by
  unfold lihDerivedElectronicCorrectionWithParticipationDimless
  exact mul_nonneg hηp (lihPShellUpliftSiteEnergy_nonneg mLiP)

theorem lihDerivedElectronicCorrectionWithParticipation_le_full
    (ηp : ℝ) (hηp1 : ηp ≤ 1) (mLiP : ℕ) :
    lihDerivedElectronicCorrectionWithParticipationDimless ηp mLiP ≤
      lihPShellUpliftSiteEnergy mLiP := by
  unfold lihDerivedElectronicCorrectionWithParticipationDimless
  have hU : 0 ≤ lihPShellUpliftSiteEnergy mLiP := lihPShellUpliftSiteEnergy_nonneg mLiP
  nlinarith [mul_le_mul_of_nonneg_right hηp1 hU]

/-- Compton/IR-window induced participation `η_p = x/θ` for LiH. -/
noncomputable def lihComptonParticipationEta (x : ℝ) : ℝ :=
  Hqiv.Physics.phaseParticipationEta x

theorem lihComptonParticipationEta_mem_unit
    (x : ℝ) (hx0 : 0 < x) (hxθ : x < Hqiv.Physics.phaseTheta) :
    0 < lihComptonParticipationEta x ∧ lihComptonParticipationEta x < 1 := by
  unfold lihComptonParticipationEta
  exact Hqiv.Physics.phaseParticipationEta_mem_unit x hx0 hxθ

/-- LiH participation-weighted indicator:
bonded-horizon surplus plus phase-window weighted Li `p` uplift. -/
noncomputable def lihDerivedDissociationIndicatorWithParticipationDimless
    (ηp : ℝ) (mLiP : ℕ)
    (cfg : Hqiv.Geometry.NuclearTorusConfig := Hqiv.Geometry.defaultNuclearTorus) : ℝ :=
  lihBondedSurplusDimless cfg + lihDerivedElectronicCorrectionWithParticipationDimless ηp mLiP

theorem lihDerivedDissociationIndicatorWithParticipation_ge_bond
    (ηp : ℝ) (hηp : 0 ≤ ηp) (mLiP : ℕ) (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihBondedSurplusDimless cfg ≤
      lihDerivedDissociationIndicatorWithParticipationDimless ηp mLiP cfg := by
  unfold lihDerivedDissociationIndicatorWithParticipationDimless
  nlinarith [lihDerivedElectronicCorrectionWithParticipation_nonneg ηp hηp mLiP]

theorem lihDerivedDissociationIndicatorWithParticipation_le_full_uplift
    (ηp : ℝ) (hηp1 : ηp ≤ 1) (mLiP : ℕ)
    (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihDerivedDissociationIndicatorWithParticipationDimless ηp mLiP cfg ≤
      lihBondedSurplusDimless cfg + lihPShellUpliftSiteEnergy mLiP := by
  unfold lihDerivedDissociationIndicatorWithParticipationDimless
  nlinarith [lihDerivedElectronicCorrectionWithParticipation_le_full ηp hηp1 mLiP]

theorem lihDerivedDissociationIndicatorWithParticipation_phase_window_control
    (x : ℝ) (hx0 : 0 < x) (hxθ : x < Hqiv.Physics.phaseTheta) (mLiP : ℕ)
    (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihBondedSurplusDimless cfg ≤
      lihDerivedDissociationIndicatorWithParticipationDimless (lihComptonParticipationEta x) mLiP cfg ∧
    lihDerivedDissociationIndicatorWithParticipationDimless (lihComptonParticipationEta x) mLiP cfg ≤
      lihBondedSurplusDimless cfg + lihPShellUpliftSiteEnergy mLiP := by
  rcases lihComptonParticipationEta_mem_unit x hx0 hxθ with ⟨hη0, hη1⟩
  have hη0' : 0 ≤ lihComptonParticipationEta x := le_of_lt hη0
  have hη1' : lihComptonParticipationEta x ≤ 1 := le_of_lt hη1
  constructor
  · exact lihDerivedDissociationIndicatorWithParticipation_ge_bond
      (lihComptonParticipationEta x) hη0' mLiP cfg
  · exact lihDerivedDissociationIndicatorWithParticipation_le_full_uplift
      (lihComptonParticipationEta x) hη1' mLiP cfg

/-- LiH bonded surplus using Compton/IR-window sourced nuclear torus angles. -/
noncomputable def lihBondedSurplusDimlessComptonWindow
    (E : Fin 3 → ℝ) (ħ : ℝ) (hħ : 0 < ħ) (t : Fin 3 → ℝ) : ℝ :=
  lihBondedSurplusDimless (cfg := Hqiv.Geometry.comptonLinkedNuclearTorusConfig E ħ hħ t)

theorem lihBondedSurplusDimlessComptonWindow_eq
    (E : Fin 3 → ℝ) (ħ : ℝ) (hħ : 0 < ħ) (t : Fin 3 → ℝ) :
    lihBondedSurplusDimlessComptonWindow E ħ hħ t =
      Hqiv.Geometry.bondHorizonSurplusDimless 4 3 1
        (Hqiv.Geometry.comptonLinkedNuclearTorusConfig E ħ hħ t) := rfl

/-! ## Compton valence + formally justified imprint readouts -/

/-- LiH dissociation indicator at the canonical Compton shells `(4,3,1)`. -/
noncomputable def lihComptonDerivedDissociationIndicatorDimless
    (cfg : Hqiv.Geometry.NuclearTorusConfig := Hqiv.Geometry.defaultNuclearTorus) : ℝ :=
  lihDerivedDissociationIndicatorDimless lihComptonLiSShell lihComptonLiPShell lihComptonHSShell cfg

theorem lihComptonDerivedDissociationIndicator_eq_bond_plus_p
    (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihComptonDerivedDissociationIndicatorDimless cfg =
      lihBondedSurplusDimless cfg + lihPShellUpliftSiteEnergy lihComptonLiPShell := by
  unfold lihComptonDerivedDissociationIndicatorDimless
  exact lihDerivedDissociationIndicator_eq_bond_plus_p lihComptonLiSShell lihComptonLiPShell
    lihComptonHSShell cfg

/--
At the Compton `(4,3,1)` sites, discrete and continuous-ξ imprint phases agree on each
integer step once `LiHComptonOmegaKBridge` is supplied.
-/
theorem lihCompton_imprintWeightedReadoutPhases_justified
    (hΩ : LiHComptonOmegaKBridge) :
    Hqiv.imprintWeightedReadoutPhase_xi_alias (xiOfShell lihComptonLiSShell)
        (xiOfShell (lihComptonLiSShell + 1)) =
      Hqiv.imprintWeightedReadoutPhase lihComptonLiSShell ∧
      Hqiv.imprintWeightedReadoutPhase_xi_alias (xiOfShell lihComptonLiPShell)
        (xiOfShell (lihComptonLiPShell + 1)) =
      Hqiv.imprintWeightedReadoutPhase lihComptonLiPShell ∧
      Hqiv.imprintWeightedReadoutPhase_xi_alias (xiOfShell lihComptonHSShell)
        (xiOfShell (lihComptonHSShell + 1)) =
      Hqiv.imprintWeightedReadoutPhase lihComptonHSShell := by
  refine ⟨?_, ?_, ?_⟩
  · exact lihCompton_LiS_imprintWeightedReadoutPhase_xi_matches hΩ
  · exact lihCompton_LiP_imprintWeightedReadoutPhase_xi_matches hΩ
  · exact lihCompton_HS_imprintWeightedReadoutPhase_xi_matches hΩ

/--
Gauge-seed `ω` at the Li(p) Compton shell may be taken from either the discrete imprint
phase or the continuous-ξ chart slot; the bridge identifies them.
-/
theorem lihCompton_LiP_seedPotential_omega_from_discrete_imprint
    (hΩ : LiHComptonOmegaKBridge) (θ : ℝ) :
    Hqiv.seedPotentialMinimalCycle (Hqiv.imprintWeightedReadoutPhase lihComptonLiPShell) θ =
      Hqiv.seedPotentialMinimalCycle
        (Hqiv.imprintWeightedReadoutPhase_xi_alias (xiOfShell lihComptonLiPShell)
          (xiOfShell (lihComptonLiPShell + 1))) θ := by
  have hphase := lihCompton_LiP_imprintWeightedReadoutPhase_xi_matches hΩ
  rw [hphase]

/--
Compton dissociation indicator packaged with formally justified per-site imprint phases.
The indicator formula is unchanged; the `have` block records that readout phases on the
three Compton shells are licensed by `lihCompton_imprintWeightedReadoutPhases_justified`.
-/
theorem lihComptonDerivedDissociationIndicator_with_justified_readouts
    (hΩ : LiHComptonOmegaKBridge)
    (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihComptonDerivedDissociationIndicatorDimless cfg =
      lihBondedSurplusDimless cfg + lihPShellUpliftSiteEnergy lihComptonLiPShell := by
  have _hReadouts := lihCompton_imprintWeightedReadoutPhases_justified hΩ
  exact lihComptonDerivedDissociationIndicator_eq_bond_plus_p cfg

/--
Participation-weighted Compton indicator at the canonical shells, with the same imprint
phase justification on the Li `p` readout coordinate `m = 3`.
-/
theorem lihComptonDerivedDissociationIndicatorWithParticipation_phase_readout_justified
    (hΩ : LiHComptonOmegaKBridge) (ηp : ℝ)
    (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    lihDerivedDissociationIndicatorWithParticipationDimless ηp lihComptonLiPShell cfg =
      lihBondedSurplusDimless cfg +
        lihDerivedElectronicCorrectionWithParticipationDimless ηp lihComptonLiPShell := by
  have _hLiP :=
    lihCompton_LiP_imprintWeightedReadoutPhase_xi_matches hΩ
  unfold lihDerivedDissociationIndicatorWithParticipationDimless
  unfold lihDerivedElectronicCorrectionWithParticipationDimless
  rfl

end Hqiv.QuantumChemistry

