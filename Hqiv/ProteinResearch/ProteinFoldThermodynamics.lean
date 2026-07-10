import Hqiv.QuantumChemistry.CurvatureContactNetwork
import Hqiv.QuantumChemistry.PhaseGeometryDensity
import Hqiv.Physics.HQIVCollectiveModes
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.ProteinResearch.ProteinSolventPhaseGeometry

/-!
# Protein fold thermodynamics — cryo crystal vs physiological folding

X-ray / cryo-EM structures are measured on a **frozen aqueous network** (ice-like bulk ρ,
periodic lattice not released).  In vivo folding proceeds in **liquid cytosol** at
``proteinFoldingTemperatureKelvin`` where the melt-comparison bulk ρ applies.

This module bridges ``ThermodynamicEnvironment`` (``CurvatureContactNetwork``) to the
protein chemistry spine:

1. **T → ξ** via ``foldXiFromTemperatureK`` (Hopf ``xi_from_physical_T``, no fit).
2. **T → bulk aqueous ρ** via ``aqueousBulkCurvatureAtT`` (ice crystalline vs liquid melt).
3. **γ-only thermal dress** on basin amplitude and peptide contact breathing.

Python mirror: ``hqiv_lab/protein_solvent_phase.py``,
``scripts/hqiv_thermodynamic_phase_from_tp.py``.
-/

namespace Hqiv.ProteinResearch

open Hqiv
open Hqiv.Physics
open Hqiv.QuantumChemistry
open Real

/-!
## Reference temperatures (Kelvin anchors, not fitted potentials)
-/

/-- CODATA Boltzmann constant in MeV/K (witness for K → MeV ladder). -/
noncomputable def boltzmannMeVPerKelvin : ℝ := 8.617333262145e-11

/-- Laboratory temperature → MeV slot for ``xi_from_physical_T``. -/
noncomputable def temperatureKelvinToMeV (T_K : ℝ) : ℝ :=
  boltzmannMeVPerKelvin * T_K

/-- Contact horizon ξ at fold temperature: ``ξ = T_Pl / T`` (``HopfShellBeltramiMassBridge``). -/
noncomputable def foldXiFromTemperatureK (T_K : ℝ) : ℝ :=
  xi_from_physical_T (temperatureKelvinToMeV T_K) hopfT_Pl_MeV

/-- H₂O bulk solid→liquid comparison (~ice Ih melt at 1 atm; Python ``characteristic_temperatures_K``). -/
noncomputable def h2oBulkMeltTemperatureKelvin : ℝ := 273.15

/-- Cryo crystallography / cryo-EM buffer reference (frozen aqueous network). -/
noncomputable def cryoCrystallographyTemperatureKelvin : ℝ := 100

/-- Physiological protein-folding box (cytosol; Python ``ThermodynamicEnvironment.protein_cytosol``). -/
noncomputable def proteinFoldingTemperatureKelvin : ℝ := 310.15

/-- Collective-relax anneal anchor (``HQIVCollectiveModes.annealTemperatureKelvin``). -/
theorem protein_folding_temperature_eq_collective_anneal :
    proteinFoldingTemperatureKelvin = annealTemperatureKelvin + 0.15 := by
  unfold proteinFoldingTemperatureKelvin annealTemperatureKelvin
  norm_num

theorem cryo_below_h2o_melt :
    cryoCrystallographyTemperatureKelvin < h2oBulkMeltTemperatureKelvin := by
  unfold cryoCrystallographyTemperatureKelvin h2oBulkMeltTemperatureKelvin
  norm_num

theorem physiological_above_h2o_melt :
    h2oBulkMeltTemperatureKelvin < proteinFoldingTemperatureKelvin := by
  unfold h2oBulkMeltTemperatureKelvin proteinFoldingTemperatureKelvin
  norm_num

theorem boltzmannMeVPerKelvin_pos : 0 < boltzmannMeVPerKelvin := by
  unfold boltzmannMeVPerKelvin
  norm_num

theorem temperatureKelvinToMeV_pos (T_K : ℝ) (hT : 0 < T_K) : 0 < temperatureKelvinToMeV T_K := by
  unfold temperatureKelvinToMeV
  exact mul_pos boltzmannMeVPerKelvin_pos hT

theorem cryo_below_physiological :
    cryoCrystallographyTemperatureKelvin < proteinFoldingTemperatureKelvin := by
  unfold cryoCrystallographyTemperatureKelvin proteinFoldingTemperatureKelvin
  norm_num

/-!
## Phase-linked bulk aqueous ρ (ice network vs melt-released liquid)
-/

/-- Solvent phase readout for the polypeptide fold box (not small-molecule gas/liquid enum). -/
inductive ProteinFoldSolventPhase
  | frozenAqueous
  | liquidAqueous
  deriving DecidableEq, Repr

/-- Classify bulk aqueous phase from T relative to H₂O melt. -/
noncomputable def proteinFoldSolventPhaseAtT (T_K T_melt_K : ℝ) : ProteinFoldSolventPhase :=
  if T_K < T_melt_K then .frozenAqueous else .liquidAqueous

/--
Bulk homogeneous curvature fraction for aqueous solvent at temperature ``T_K``.

Below melt: **crystalline ice** network (``crystallineIceCurvatureFraction``).
At/above melt: **liquid melt comparison** (periodic lattice released, ρ = 1).
-/
noncomputable def aqueousBulkCurvatureAtT (T_K T_melt_K : ℝ) : ℝ :=
  if T_K < T_melt_K then crystallineIceCurvatureFraction else aqueousBulkCurvatureFraction

theorem aqueousBulkAtT_cryo_uses_ice :
    aqueousBulkCurvatureAtT cryoCrystallographyTemperatureKelvin h2oBulkMeltTemperatureKelvin =
      crystallineIceCurvatureFraction := by
  unfold aqueousBulkCurvatureAtT
  rw [if_pos cryo_below_h2o_melt]

theorem aqueousBulkAtT_physiological_uses_liquid :
    aqueousBulkCurvatureAtT proteinFoldingTemperatureKelvin h2oBulkMeltTemperatureKelvin =
      aqueousBulkCurvatureFraction := by
  unfold aqueousBulkCurvatureAtT
  rw [if_neg (not_lt.mpr (le_of_lt physiological_above_h2o_melt))]

theorem cryo_fold_solvent_phase_frozen :
    proteinFoldSolventPhaseAtT cryoCrystallographyTemperatureKelvin h2oBulkMeltTemperatureKelvin =
      .frozenAqueous := by
  unfold proteinFoldSolventPhaseAtT
  rw [if_pos cryo_below_h2o_melt]

theorem physiological_fold_solvent_phase_liquid :
    proteinFoldSolventPhaseAtT proteinFoldingTemperatureKelvin h2oBulkMeltTemperatureKelvin =
      .liquidAqueous := by
  unfold proteinFoldSolventPhaseAtT
  rw [if_neg (not_lt.mpr (le_of_lt physiological_above_h2o_melt))]

theorem aqueousBulkAtT_physiological_eq_one :
    aqueousBulkCurvatureAtT proteinFoldingTemperatureKelvin h2oBulkMeltTemperatureKelvin = 1 := by
  rw [aqueousBulkAtT_physiological_uses_liquid, aqueousBulkCurvatureFraction_eq_one]

/-!
## T-dressed solvent site + contact budget (extends ``ProteinSolventPhaseGeometry``)
-/

/-- Solvent ρ at a contact site with **temperature-selected** bulk background. -/
noncomputable def solventCurvatureDensityAtSiteAtT
    (ρLocalNetwork rContact T_K T_melt_K : ℝ) : ℝ :=
  let wBulk := orbitalBulkDominanceWeight aqueousBulkPivotAngstrom rContact
  clampMediumDensity (
    wBulk * aqueousBulkCurvatureAtT T_K T_melt_K + (1 - wBulk) * ρLocalNetwork)

/-- Effective contact curvature weight at laboratory ``(T, P)`` (ξ from T, bulk ρ from melt). -/
noncomputable def contactCurvatureWeightAtEnv
    (env : ThermodynamicEnvironment) (ρSite ρLocal : ℝ) : ℝ :=
  proteinEffectiveCurvatureBudget
    (foldXiFromTemperatureK env.temperatureK) ρSite ρLocal

theorem contactCurvatureWeightAtEnv_eq_effective_budget
    (env : ThermodynamicEnvironment) (ρSite ρLocal : ℝ) :
    contactCurvatureWeightAtEnv env ρSite ρLocal =
      proteinEffectiveCurvatureBudget (foldXiFromTemperatureK env.temperatureK) ρSite ρLocal := rfl

/-- Cytosolic fold environment (310.15 K, STP pressure witness). -/
noncomputable def proteinCytosolEnvironment : ThermodynamicEnvironment :=
  { temperatureK := proteinFoldingTemperatureKelvin
    pressurePa := 101325 }

/-!
## γ-only thermal dress on Ramachandran / contact scales (weak channel)

Exponent ``γ/6`` matches α-helix ψ dress; ``γ/16`` mirrors allotrope ``thermal_contact_scale``.
Reference ``T_ref = h2oBulkMeltTemperatureKelvin`` (melt comparison anchor).
-/

noncomputable def thermalBasinAmplitude (T_K T_ref_K : ℝ) : ℝ :=
  (max T_K T_ref_K / max T_ref_K 1e-30) ^ (gamma_HQIV / 6)

noncomputable def thermalPeptideContactScale (T_K T_ref_K : ℝ) : ℝ :=
  (max T_K T_ref_K / max T_ref_K 1e-30) ^ (gamma_HQIV / 16)

theorem thermalBasinAmplitude_at_melt_eq_one :
    thermalBasinAmplitude h2oBulkMeltTemperatureKelvin h2oBulkMeltTemperatureKelvin = 1 := by
  unfold thermalBasinAmplitude h2oBulkMeltTemperatureKelvin gamma_HQIV
  norm_num

theorem thermalPeptideContactScale_at_melt_eq_one :
    thermalPeptideContactScale h2oBulkMeltTemperatureKelvin h2oBulkMeltTemperatureKelvin = 1 := by
  unfold thermalPeptideContactScale h2oBulkMeltTemperatureKelvin gamma_HQIV
  norm_num

theorem cryo_temperature_pos : 0 < cryoCrystallographyTemperatureKelvin := by
  unfold cryoCrystallographyTemperatureKelvin; norm_num

theorem physiological_temperature_pos : 0 < proteinFoldingTemperatureKelvin := by
  unfold proteinFoldingTemperatureKelvin; norm_num

theorem foldXiFromTemperatureK_antitone {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (h : T₁ < T₂) :
    foldXiFromTemperatureK T₂ < foldXiFromTemperatureK T₁ := by
  unfold foldXiFromTemperatureK xi_from_physical_T
  have h₁ : 0 < temperatureKelvinToMeV T₁ := temperatureKelvinToMeV_pos T₁ hT₁
  have hMeV : temperatureKelvinToMeV T₁ < temperatureKelvinToMeV T₂ := by
    unfold temperatureKelvinToMeV
    exact mul_lt_mul_of_pos_left h boltzmannMeVPerKelvin_pos
  have hPl : 0 < hopfT_Pl_MeV := by unfold hopfT_Pl_MeV; norm_num
  exact div_lt_div_of_pos_left hPl h₁ hMeV

theorem fold_xi_cryo_gt_physiological :
    foldXiFromTemperatureK cryoCrystallographyTemperatureKelvin >
      foldXiFromTemperatureK proteinFoldingTemperatureKelvin :=
  foldXiFromTemperatureK_antitone cryo_temperature_pos physiological_temperature_pos cryo_below_physiological

end Hqiv.ProteinResearch
