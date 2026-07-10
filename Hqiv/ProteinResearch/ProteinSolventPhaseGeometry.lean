import Hqiv.Physics.DynamicCentreGeometry
import Hqiv.QuantumChemistry.PhaseDiagramMixture
import Hqiv.Physics.HomogeneousCurvatureSecondOrder

/-!
# Aqueous protein folding: bulk water ρ + heavy-atom inverse-square augmentation

Python mirror: ``horizon_physics/proteins/phase_geometry_density.py``.

At physiological fold conditions bulk **liquid** H₂O supplies homogeneous curvature density
via ``meltComparisonCurvatureDensityFraction`` (periodic lattice released at melt comparison).

**Crystalline ice** reference uses ``crystallineCurvatureDensityFractionH2OIceIh`` /
``tetrahedralMeltDensityRatio`` — network-derived, not a fitted constant.

Heavy atoms in the polypeptide augment the local solvent readout via inverse-square weights —
the same spine as ``orbitalLocalCurvatureFraction`` / ``orbitalBulkDominanceWeight`` in
``PhaseGeometryDensity``, scaled to Å contacts instead of planetary radii.

The augmented ρ feeds ``homogeneousCurvatureBudgetAtXi`` and modulates horizon EM
screening in the Python folding stack (``build_horizon_poles`` / ``grad_horizon_full``).
No fitted force field; geometry witnesses only.
-/

namespace Hqiv.ProteinResearch

open Hqiv
open Hqiv.Physics
open Hqiv.QuantumChemistry

/-- Bulk aqueous fold baseline: melt-side comparison (periodic lattice released). -/
noncomputable def aqueousBulkCurvatureFraction : ℝ := meltComparisonCurvatureDensityFraction

theorem aqueousBulkCurvatureFraction_eq_meltComparison :
    aqueousBulkCurvatureFraction = meltComparisonCurvatureDensityFraction := rfl

theorem aqueousBulkCurvatureFraction_eq_one :
    aqueousBulkCurvatureFraction = 1 := by
  unfold aqueousBulkCurvatureFraction meltComparisonCurvatureDensityFraction
  rfl

/-- Dynamic crystalline ice ρ at fold reference (tetrahedral H-bond network, n_inter = 4). -/
noncomputable def crystallineIceCurvatureFraction : ℝ :=
  crystallineCurvatureDensityFractionH2OIceIh

/-- Legacy alias: bulk liquid-water curvature fraction at fold comparison. -/
noncomputable def bulkLiquidWaterCurvatureFraction : ℝ := aqueousBulkCurvatureFraction

theorem bulkLiquidWaterCurvatureFraction_eq_one :
    bulkLiquidWaterCurvatureFraction = 1 := aqueousBulkCurvatureFraction_eq_one

/-- Inverse-square local slot at contact distance ``rContact`` with reference radius ``rRef``. -/
noncomputable def heavyAtomLocalCurvatureSlot (rRef rContact : ℝ) : ℝ :=
  orbitalLocalCurvatureFraction rRef rContact

/-- Effective solvent ρ at a site: bulk liquid blended with local heavy-atom network ρ. -/
noncomputable def solventCurvatureDensityAtSite (ρLocalNetwork rContact rBulkPivot : ℝ) : ℝ :=
  let wBulk := orbitalBulkDominanceWeight rBulkPivot rContact
  clampMediumDensity (wBulk * aqueousBulkCurvatureFraction + (1 - wBulk) * ρLocalNetwork)

/-- Local heavy-atom coordination excess above the homogeneous solvent background. -/
noncomputable def solventCoordinationExcess (ρHom ρLocalRaw : ℝ) : ℝ :=
  nucleationCoordinationExcess ρHom ρLocalRaw

/-- Homogeneous curvature budget for a protein horizon contact at propagation ξ. -/
noncomputable def proteinHorizonCurvatureBudget (ξ ρSite : ℝ) : ℝ :=
  homogeneousCurvatureBudgetFromPhase ξ ρSite

/-- Effective protein contact budget: homogeneous solvent + heavy-atom defect channel. -/
noncomputable def proteinEffectiveCurvatureBudget (ξ ρSite ρLocalRaw : ℝ) : ℝ :=
  effectiveCurvatureBudgetAtXi ξ ρSite (solventCoordinationExcess ρSite ρLocalRaw)

theorem proteinHorizonCurvatureBudget_dilute (ξ : ℝ) :
    proteinHorizonCurvatureBudget ξ 0 = 1 := by
  unfold proteinHorizonCurvatureBudget homogeneousCurvatureBudgetFromPhase
  exact homogeneousCurvatureBudgetFromPhase_dilute ξ

theorem proteinHorizonCurvatureBudget_bulk_liquid (ξ : ℝ) :
    proteinHorizonCurvatureBudget ξ aqueousBulkCurvatureFraction =
      homogeneousCurvatureBudgetFromPhase ξ 1 := by
  rw [proteinHorizonCurvatureBudget, aqueousBulkCurvatureFraction_eq_one]

theorem proteinEffectiveCurvatureBudget_eq_effective
    (ξ ρSite ρLocalRaw : ℝ) :
    proteinEffectiveCurvatureBudget ξ ρSite ρLocalRaw =
      effectiveCurvatureBudgetAtXi ξ ρSite
        (nucleationCoordinationExcess ρSite ρLocalRaw) := rfl

theorem clampMediumDensity_le_one (ρ : ℝ) : clampMediumDensity ρ ≤ 1 := by
  unfold clampMediumDensity
  rcases le_total 0 (min 1 ρ) with hnonneg | h_nonpos
  · simpa [max_eq_left hnonneg] using min_le_right (1 : ℝ) ρ
  · simpa [max_comm, max_eq_right h_nonpos] using zero_le_one

/-!
## Directional local shape curvature (backbone-flow anisotropy)

Python mirror: ``hqiv_lab/protein_solvent_phase.directional_local_network_rho``.

Bulk aqueous ρ dominates at long range; **local network ρ** rises when a tertiary contact chord
aligns with backbone tangent flow (intra-helix axial register) or is transverse (sheet–helix cross
register).  This is the protein analogue of bulk density vs local orientation in the water melt spine.
-/

/-- Directional register slot (maps from ``TertiaryContactKind`` in ``MiniproteinChemistryDynamics``). -/
inductive DirectionalContactRegister
  | helixAxial
  | helixSheetCross
  | sheetStrand
  | hydrophobicBurial
  | terminusCap
  deriving DecidableEq, Repr

/-- Å-scale first-shell aqueous pivot (H-bond reference; Python ``AQUEOUS_BULK_PIVOT_ANGSTROM``). -/
noncomputable def aqueousBulkPivotAngstrom : ℝ := 2.8

/-- Directional local ρ for intra-helix axial contacts (flow-aligned chord). -/
noncomputable def directionalHelixAxialLocalRho (flowAlignment : ℝ) : ℝ :=
  clampMediumDensity (0.30 + 0.70 * |flowAlignment|)

/-- Directional local ρ for sheet–helix cross register (transverse chord). -/
noncomputable def directionalHelixSheetCrossLocalRho (flowAlignment : ℝ) : ℝ :=
  clampMediumDensity (0.20 + 0.55 * (1 - |flowAlignment|))

/-- Register-kind local ρ slot (flow alignment ∈ [0, 1] supplied by geometry readout). -/
noncomputable def directionalLocalNetworkRho (r : DirectionalContactRegister) (flowAlignment : ℝ) : ℝ :=
  match r with
  | .helixAxial => directionalHelixAxialLocalRho flowAlignment
  | .helixSheetCross => directionalHelixSheetCrossLocalRho flowAlignment
  | .sheetStrand => clampMediumDensity (0.40 + 0.35 * |flowAlignment|)
  | .hydrophobicBurial => 0.35
  | .terminusCap => 0.25

theorem directional_helix_axial_local_rho_bounded (t : ℝ) :
    directionalHelixAxialLocalRho t ≤ 1 := by
  simpa only [directionalHelixAxialLocalRho] using clampMediumDensity_le_one (0.30 + 0.70 * |t|)

theorem directional_helix_sheet_cross_local_rho_bounded (t : ℝ) :
    directionalHelixSheetCrossLocalRho t ≤ 1 := by
  simpa only [directionalHelixSheetCrossLocalRho] using clampMediumDensity_le_one (0.20 + 0.55 * (1 - |t|))

/-- Curvature-dressed SSE weight at a contact horizon (effective budget). -/
noncomputable def contactCurvatureWeight (ξ ρSite ρLocal : ℝ) : ℝ :=
  proteinEffectiveCurvatureBudget ξ ρSite ρLocal

theorem contact_curvature_weight_eq_effective_budget (ξ ρSite ρLocal : ℝ) :
    contactCurvatureWeight ξ ρSite ρLocal = proteinEffectiveCurvatureBudget ξ ρSite ρLocal := rfl

theorem solvent_site_at_contact_uses_bulk_pivot (ρLocal rContact : ℝ) :
    solventCurvatureDensityAtSite ρLocal rContact aqueousBulkPivotAngstrom ≤ 1 := by
  unfold solventCurvatureDensityAtSite
  exact clampMediumDensity_le_one _

/-!
## Two-liquid interface dress (LDL/HDL at protein–solvent contacts)

Python mirror: ``hqiv_lab/protein_solvent_phase.local_low_density_fraction_at_interface``.

Hydrophobic burial biases local tetrahedral (LDL-like) participation; hydrophilic exposure
releases toward HDL-like bulk.  Uses ``interfaceLowDensityFractionBoost = γ·α`` from the
phase-diagram spine — no fitted interface potentials.
-/

/-- Solvent exposure class at a tertiary contact horizon. -/
inductive SolventInterfaceExposure
  | hydrophilic
  | hydrophobic
  | neutral
  deriving DecidableEq, Repr

/-- LDL boost at hydrophobic interfaces: ``γ·α`` (``PhaseDiagramMixture`` spine). -/
noncomputable def interfaceLowDensityFractionBoost : ℝ := gamma_HQIV * alpha

/--
Local ``f_LDL`` at an interface given bulk fraction ``fBulk`` from the (T,P) engine.

* Hydrophobic: ``f + (1−f)·γ·α`` toward LDL.
* Hydrophilic: ``f·(1−α)`` toward HDL.
* Neutral: ``f`` unchanged.
-/
noncomputable def localLowDensityFractionAtInterface (fBulk : ℝ) (exposure : SolventInterfaceExposure) : ℝ :=
  match exposure with
  | .hydrophobic =>
      clampMediumDensity (fBulk + (1 - fBulk) * interfaceLowDensityFractionBoost)
  | .hydrophilic =>
      clampMediumDensity (fBulk * (1 - alpha))
  | .neutral =>
      clampMediumDensity fBulk

/-- Mixture ρ_curv at an interface from local ``f_LDL``. -/
noncomputable def solventCurvatureAtInterface (fLocal : ℝ) : ℝ :=
  h2oLiquidMixtureCurvatureFraction fLocal

theorem localLowDensityFractionAtInterface_hydrophobic_ge_bulk
    (fBulk : ℝ) (hf : 0 ≤ fBulk) (hf1 : fBulk ≤ 1) :
    fBulk ≤ localLowDensityFractionAtInterface fBulk .hydrophobic := by
  unfold localLowDensityFractionAtInterface interfaceLowDensityFractionBoost
  simp only [SolventInterfaceExposure.hydrophobic, clampMediumDensity]
  have hraw_ge : fBulk ≤ fBulk + (1 - fBulk) * (gamma_HQIV * alpha) := by
    unfold gamma_HQIV alpha; nlinarith [hf, hf1]
  have hraw_le : fBulk + (1 - fBulk) * (gamma_HQIV * alpha) ≤ 1 := by
    unfold gamma_HQIV alpha; nlinarith [hf, hf1]
  have hraw_nonneg : 0 ≤ fBulk + (1 - fBulk) * (gamma_HQIV * alpha) := by
    unfold gamma_HQIV alpha; nlinarith [hf, hf1]
  have heq : max 0 (min 1 (fBulk + (1 - fBulk) * (gamma_HQIV * alpha))) =
      fBulk + (1 - fBulk) * (gamma_HQIV * alpha) := by
    rw [min_eq_right hraw_le, max_eq_right hraw_nonneg]
  rw [heq]
  exact hraw_ge

theorem localLowDensityFractionAtInterface_hydrophilic_le_bulk
    (fBulk : ℝ) (hf : 0 ≤ fBulk) :
    localLowDensityFractionAtInterface fBulk .hydrophilic ≤ fBulk := by
  unfold localLowDensityFractionAtInterface
  simp only [SolventInterfaceExposure.hydrophilic, clampMediumDensity]
  set x := fBulk * (1 - alpha)
  have hx0 : 0 ≤ x := by unfold x alpha; nlinarith [hf]
  have hx_le : x ≤ fBulk := by unfold x alpha; nlinarith [hf]
  have hclamp : max 0 (min 1 x) ≤ x := by
    by_cases hx1 : x ≤ 1
    · rw [min_eq_right hx1, max_eq_right hx0]
    · have hx1' : 1 < x := lt_of_not_ge hx1
      rw [min_eq_left (le_of_lt hx1'), max_eq_right (by linarith)]
      linarith
  exact le_trans hclamp hx_le

/-!
## Local H–O–H angle mixture at protein–solvent interfaces

Torque-tree ``dynamicCentreAngleRad`` supplies the gas-phase HDL slot; ``centreAngleRadFromDomains 4``
supplies the LDL tetrahedral network reference.  The mixture slot ties folding contacts to the
same angle spine as ``PhaseDiagramMixture`` (Python ``hoh_angle_mixture_deg``).
-/

noncomputable def localHohAngleMixtureAtInterface (fLocal : ℝ) : ℝ :=
  hohAngleMixtureSlot fLocal (centreAngleRadFromDomains 4) (dynamicCentreAngleRad 8 2)

/-- Scale Å pivot by local tetrahedral opening vs gas reference (no tabulated degrees). -/
noncomputable def aqueousHbPivotDressFromAngle (θMix θGas : ℝ) : ℝ :=
  if θGas = 0 then 1 else θMix / θGas

noncomputable def aqueousHbPivotAtInterface (fLocal : ℝ) : ℝ :=
  aqueousBulkPivotAngstrom *
    aqueousHbPivotDressFromAngle (localHohAngleMixtureAtInterface fLocal) (dynamicCentreAngleRad 8 2)

end Hqiv.ProteinResearch
