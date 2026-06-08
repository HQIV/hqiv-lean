import Hqiv.QuantumChemistry.LiHDerivation
import Hqiv.QuantumChemistry.DynamicBindingChart
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.BBNNetworkFromWeights
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Physics.ContinuousXiCoupling

/-!
# LiH dynamic binding on the post-T12/T13 shell chart

This module theorizes the **dynamic** LiH binding readout by wiring the same
post-lock-in machinery used in bulk baryogenesis / BBN into the finite-site
LiH scaffold:

* `tuftVevFactorAtXi` — heavy-lepton gap ratio against the proton lock-in slice,
* Compton-valence geometric mean of those factors on shells `(4,3,1)`,
* phase-window participation `η_p` on the bond surplus (not the full `p` uplift),
* binding-curvature feedback `(1 + baryogenesis_binding_curvature_correction)`,
* hydrogen λ-anchor conversion `eVPerLambdaUnit_S7HydrogenAnchor`.

**Convention.** `lihDynamicBindingEnergyEv` uses the **chemist** sign: positive means
bound.  This is *not* the raw thermodynamic surplus sign from
`BondedHorizonCasimir` (where lower joint Casimir is deeper).  The participation
readout isolates the **bonding channel** weighted by `η_p`.

No numeric fit to experiment is introduced here; structural theorems only.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Hqiv.Geometry
open scoped BigOperators

noncomputable section

/-!
## Dynamic vev factor and per-shell site energies
-/

theorem tuftVevFactorAtXi_pos {ξ : ℝ}
    (hξ : 0 < heavy_lepton_gap_at_xi ξ) : 0 < tuftVevFactorAtXi ξ := by
  unfold tuftVevFactorAtXi
  have h0 : heavy_lepton_gap_at_xi 5 ≠ 0 := by
    rw [heavy_lepton_gap_at_lockin_eq_four_fifths]
    norm_num
  exact div_pos hξ (by rw [heavy_lepton_gap_at_lockin_eq_four_fifths]; norm_num)

/-- Per-shell site energy modulated by the dynamic vev factor at `ξ = m + 1`. -/
noncomputable def dynamicSiteEnergyAtShell (m : ℕ) : ℝ :=
  Hqiv.ProteinResearch.latticeFullModeEnergy m * tuftVevFactorAtXi (xiOfShell m)

theorem dynamicSiteEnergyAtShell_eq_static_at_lockin :
    dynamicSiteEnergyAtShell lihComptonLiSShell =
      Hqiv.ProteinResearch.latticeFullModeEnergy lihComptonLiSShell := by
  unfold dynamicSiteEnergyAtShell
  have hξ : xiOfShell lihComptonLiSShell = 5 := by
    unfold xiOfShell lihComptonLiSShell
    norm_num
  rw [hξ, tuftVevFactorAtXi_lockin, mul_one]

private theorem lihComptonHeavyGap_pos (m : ℕ) (hm : 1 < xiOfShell m) :
    0 < heavy_lepton_gap_at_xi (xiOfShell m) := by
  unfold heavy_lepton_gap_at_xi
  have hscale : 0 < effective_casimir_scale_at_xi (xiOfShell m) :=
    effective_casimir_scale_at_xi_pos (xiOfShell m) hm
  have hξpos : 0 < xiOfShell m := lt_trans (by norm_num) hm
  have hden : 0 < effective_casimir_scale_at_xi 5 :=
    effective_casimir_scale_at_xi_pos 5 (by norm_num)
  have hquot : 0 < effective_casimir_scale_at_xi (xiOfShell m) / effective_casimir_scale_at_xi 5 :=
    div_pos hscale hden
  have hf : 0 < (4 / 5 : ℝ) := by norm_num
  have hξ : 0 < xiOfShell m / 5 := div_pos hξpos (by norm_num)
  exact mul_pos (mul_pos hf hξ) hquot

theorem dynamicSiteEnergyAtShell_nonneg (m : ℕ)
    (hξ : 1 < xiOfShell m) :
    0 ≤ dynamicSiteEnergyAtShell m := by
  unfold dynamicSiteEnergyAtShell
  apply mul_nonneg (latticeFullModeEnergy_nonneg m)
  exact le_of_lt (tuftVevFactorAtXi_pos (lihComptonHeavyGap_pos m hξ))

theorem dynamicSiteEnergyAtShell_le_static_of_vev_le_one {m : ℕ}
    (h : tuftVevFactorAtXi (xiOfShell m) ≤ 1) :
    dynamicSiteEnergyAtShell m ≤ Hqiv.ProteinResearch.latticeFullModeEnergy m := by
  unfold dynamicSiteEnergyAtShell
  simpa using mul_le_mul_of_nonneg_left h (latticeFullModeEnergy_nonneg m)

/-!
## Compton-valence dynamic trace and geometric vev mean
-/

/-- Dynamic valence site-energy trace on the canonical Compton `(4,3,1)` assignment. -/
noncomputable def lihDynamicValenceSiteEnergyTrace (ηp : ℝ) : ℝ :=
  dynamicSiteEnergyAtShell lihComptonLiSShell +
    ηp * (3 : ℝ) * dynamicSiteEnergyAtShell lihComptonLiPShell +
    dynamicSiteEnergyAtShell lihComptonHSShell

theorem lihDynamicValenceSiteEnergyTrace_eq_weighted_p (ηp : ℝ) :
    lihDynamicValenceSiteEnergyTrace ηp =
      dynamicSiteEnergyAtShell lihComptonLiSShell +
        ηp * (3 : ℝ) * Hqiv.ProteinResearch.latticeFullModeEnergy lihComptonLiPShell *
          tuftVevFactorAtXi (xiOfShell lihComptonLiPShell) +
        dynamicSiteEnergyAtShell lihComptonHSShell := by
  unfold lihDynamicValenceSiteEnergyTrace dynamicSiteEnergyAtShell
  ring

/-- Geometric mean of `tuftVevFactorAtXi` on the three Compton readout shells. -/
noncomputable def lihComptonTuftVevGeometricMean : ℝ :=
  Real.rpow (
    tuftVevFactorAtXi (xiOfShell lihComptonLiSShell) *
      tuftVevFactorAtXi (xiOfShell lihComptonLiPShell) *
      tuftVevFactorAtXi (xiOfShell lihComptonHSShell)) (1 / 3)

private theorem lihComptonTuftVevProduct_pos :
    0 < tuftVevFactorAtXi (xiOfShell lihComptonLiSShell) *
      tuftVevFactorAtXi (xiOfShell lihComptonLiPShell) *
      tuftVevFactorAtXi (xiOfShell lihComptonHSShell) := by
  have hLiS : 1 < xiOfShell lihComptonLiSShell := by unfold xiOfShell lihComptonLiSShell; norm_num
  have hLiP : 1 < xiOfShell lihComptonLiPShell := by unfold xiOfShell lihComptonLiPShell; norm_num
  have hH : 1 < xiOfShell lihComptonHSShell := by unfold xiOfShell lihComptonHSShell; norm_num
  have h1 := tuftVevFactorAtXi_pos (lihComptonHeavyGap_pos lihComptonLiSShell hLiS)
  have h2 := tuftVevFactorAtXi_pos (lihComptonHeavyGap_pos lihComptonLiPShell hLiP)
  have h3 := tuftVevFactorAtXi_pos (lihComptonHeavyGap_pos lihComptonHSShell hH)
  exact mul_pos (mul_pos h1 h2) h3

theorem lihComptonTuftVevGeometricMean_pos : 0 < lihComptonTuftVevGeometricMean := by
  unfold lihComptonTuftVevGeometricMean
  exact Real.rpow_pos_of_pos lihComptonTuftVevProduct_pos _

/-!
## Binding-curvature feedback and dynamic binding core
-/

/-- Mean contact ξ on the LiH Compton triplet. -/
noncomputable def lihComptonXiMean : ℝ :=
  dynamicComptonXiMean dynamicComptonTripletHeavyHydride

/-- Dynamic binding-curvature correction at LiH contact ξ (no fixed κ_bind). -/
noncomputable def lihBindingCurvatureCorrection : ℝ :=
  dynamicBindingCurvatureCorrectionAtXi lihComptonXiMean

/-- First-order binding feedback on the dynamic LiH readout. -/
noncomputable def lihBindingCurvatureFeedbackFactor : ℝ :=
  dynamicBindingCurvatureFeedbackAtXi lihComptonXiMean

theorem lihBindingCurvatureFeedbackFactor_eq :
    lihBindingCurvatureFeedbackFactor = 1 + lihBindingCurvatureCorrection := by
  unfold lihBindingCurvatureFeedbackFactor lihBindingCurvatureCorrection
    dynamicBindingCurvatureFeedbackAtXi

theorem lihBindingCurvatureFeedbackFactor_one_le
    (h : 0 ≤ lihBindingCurvatureCorrection) :
    1 ≤ lihBindingCurvatureFeedbackFactor := by
  unfold lihBindingCurvatureFeedbackFactor
  linarith

/--
Dimless dynamic binding core:

`η_p · bond_surplus(4→3+1) · geomean(tuftVevFactorAtXi) · (1 + binding_curvature_correction)`.

The full `p`-shell uplift enters only through the separate participation indicator
(`lihDerivedDissociationIndicatorWithParticipationDimless`), not here.
-/
noncomputable def lihDynamicBindingCoreDimless
    (ηp : ℝ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  ηp * lihBondedSurplusDimless cfg * lihComptonTuftVevGeometricMean *
    lihBindingCurvatureFeedbackFactor

theorem lihDynamicBindingCoreDimless_eq
    (ηp : ℝ) (cfg : NuclearTorusConfig) :
    lihDynamicBindingCoreDimless ηp cfg =
      ηp * lihBondedSurplusDimless cfg * lihComptonTuftVevGeometricMean *
        lihBindingCurvatureFeedbackFactor := rfl

theorem lihDynamicBindingCoreDimless_pos
    (ηp : ℝ) (cfg : NuclearTorusConfig)
    (hηp : 0 < ηp) (hbond : 0 < lihBondedSurplusDimless cfg)
    (hfb : 0 < lihBindingCurvatureFeedbackFactor) :
    0 < lihDynamicBindingCoreDimless ηp cfg := by
  unfold lihDynamicBindingCoreDimless
  exact mul_pos (mul_pos (mul_pos hηp hbond) lihComptonTuftVevGeometricMean_pos) hfb

/-- Dynamic LiH binding energy in eV (chemist convention: positive = bound). -/
noncomputable def lihDynamicBindingEnergyEv
    (ηp : ℝ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  lihDynamicBindingCoreDimless ηp cfg * eVPerLambdaUnit_S7HydrogenAnchor

theorem lihDynamicBindingEnergyEv_eq
    (ηp : ℝ) (cfg : NuclearTorusConfig) :
    lihDynamicBindingEnergyEv ηp cfg =
      lihDynamicBindingCoreDimless ηp cfg * eVPerLambdaUnit_S7HydrogenAnchor := rfl

theorem lihDynamicBindingEnergyEv_pos
    (ηp : ℝ) (cfg : NuclearTorusConfig)
    (hηp : 0 < ηp) (hbond : 0 < lihBondedSurplusDimless cfg)
    (hfb : 0 < lihBindingCurvatureFeedbackFactor) :
    0 < lihDynamicBindingEnergyEv ηp cfg := by
  unfold lihDynamicBindingEnergyEv
  exact mul_pos (lihDynamicBindingCoreDimless_pos ηp cfg hηp hbond hfb)
    (by unfold eVPerLambdaUnit_S7HydrogenAnchor hydrogenGroundIP_eV; norm_num)

/-!
## Compton participation packaging
-/

/-- Dynamic binding with Compton phase-window participation `η_p = x / θ`. -/
noncomputable def lihDynamicBindingEnergyEvCompton
    (x : ℝ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  lihDynamicBindingEnergyEv (lihComptonParticipationEta x) cfg

theorem lihDynamicBindingEnergyEvCompton_eq
    (x : ℝ) (cfg : NuclearTorusConfig) :
    lihDynamicBindingEnergyEvCompton x cfg =
      lihDynamicBindingEnergyEv (lihComptonParticipationEta x) cfg := rfl

theorem lihDynamicBindingEnergyEvCompton_pos_of_window
    (x : ℝ) (cfg : NuclearTorusConfig)
    (hx0 : 0 < x) (hxθ : x < Hqiv.Physics.phaseTheta)
    (hbond : 0 < lihBondedSurplusDimless cfg)
    (hfb : 0 < lihBindingCurvatureFeedbackFactor) :
    0 < lihDynamicBindingEnergyEvCompton x cfg := by
  rcases lihComptonParticipationEta_mem_unit x hx0 hxθ with ⟨hη0, _⟩
  exact lihDynamicBindingEnergyEv_pos (lihComptonParticipationEta x) cfg hη0 hbond hfb

theorem dynamicComptonTuftVevGeometricMean_eq_lih :
    dynamicComptonTuftVevGeometricMean dynamicComptonTripletHeavyHydride =
      lihComptonTuftVevGeometricMean := by
  unfold dynamicComptonTuftVevGeometricMean lihComptonTuftVevGeometricMean
  simp [dynamicComptonTripletHeavyHydride, DynamicComptonTriplet.xiAt, DynamicComptonTriplet.shellAt,
    xiOfShell, lihComptonLiSShell, lihComptonLiPShell, lihComptonHSShell, Fin.isValue]

theorem lihDynamicBindingCoreDimless_eq_dynamicBindingCoreDimlessAtXi
    (ηp : ℝ) (cfg : NuclearTorusConfig) :
    lihDynamicBindingCoreDimless ηp cfg =
      dynamicBindingCoreDimlessAtXi ηp (lihBondedSurplusDimless cfg) lihComptonTuftVevGeometricMean
        (dynamicComptonXiMean dynamicComptonTripletHeavyHydride) := by
  unfold lihDynamicBindingCoreDimless dynamicBindingCoreDimlessAtXi dynamicComptonXiMean
    dynamicComptonTripletHeavyHydride DynamicComptonTriplet.xiAt lihComptonLiSShell lihComptonLiPShell
    lihComptonHSShell xiOfShell
  ring

theorem dynamicBindingEnergyEv_eq_lih
    (ηp : ℝ) (cfg : NuclearTorusConfig) :
    dynamicBindingEnergyEv (lihDynamicBindingCoreDimless ηp cfg) =
      lihDynamicBindingEnergyEv ηp cfg := by
  unfold dynamicBindingEnergyEv lihDynamicBindingEnergyEv
  ring

theorem diatomicBondSurplusDimless_eq_lih_bond :
    diatomicBondSurplusDimless 4 3 1 = lihBondedSurplusDimless := by
  unfold diatomicBondSurplusDimless lihBondedSurplusDimless
  rfl

end

end Hqiv.QuantumChemistry
