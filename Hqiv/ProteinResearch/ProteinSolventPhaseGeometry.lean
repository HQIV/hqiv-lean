import Hqiv.QuantumChemistry.PhaseGeometryDensity
import Hqiv.Physics.HomogeneousCurvatureSecondOrder

/-!
# Aqueous protein folding: bulk water ρ + heavy-atom inverse-square augmentation

Python mirror: ``horizon_physics/proteins/phase_geometry_density.py``.

At physiological fold conditions bulk liquid H₂O supplies homogeneous curvature density
ρ_bulk = 1 on the liquid reference scale.  Heavy atoms in the polypeptide augment the
**local** solvent readout via inverse-square weights — the same spine as
``orbitalLocalCurvatureFraction`` / ``orbitalBulkDominanceWeight`` in
``PhaseGeometryDensity``, scaled to Å contacts instead of planetary radii.

The augmented ρ feeds ``homogeneousCurvatureBudgetAtXi`` and modulates horizon EM
screening in the Python folding stack (``build_horizon_poles`` / ``grad_horizon_full``).
No fitted force field; geometry witnesses only.
-/

namespace Hqiv.ProteinResearch

open Hqiv
open Hqiv.Physics
open Hqiv.QuantumChemistry

/-- Bulk liquid-water curvature fraction at fold comparison (ρ_liquid_ref = 1). -/
noncomputable def bulkLiquidWaterCurvatureFraction : ℝ := liquidReferenceDensityH2O / liquidReferenceDensityH2O

theorem bulkLiquidWaterCurvatureFraction_eq_one :
    bulkLiquidWaterCurvatureFraction = 1 := by
  unfold bulkLiquidWaterCurvatureFraction liquidReferenceDensityH2O
  norm_num

/-- Inverse-square local slot at contact distance ``rContact`` with reference radius ``rRef``. -/
noncomputable def heavyAtomLocalCurvatureSlot (rRef rContact : ℝ) : ℝ :=
  orbitalLocalCurvatureFraction rRef rContact

/-- Effective solvent ρ at a site: bulk liquid blended with local heavy-atom network ρ. -/
noncomputable def solventCurvatureDensityAtSite (ρLocalNetwork rContact rBulkPivot : ℝ) : ℝ :=
  let wBulk := orbitalBulkDominanceWeight rBulkPivot rContact
  clampMediumDensity (wBulk * bulkLiquidWaterCurvatureFraction + (1 - wBulk) * ρLocalNetwork)

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
    proteinHorizonCurvatureBudget ξ bulkLiquidWaterCurvatureFraction =
      homogeneousCurvatureBudgetFromPhase ξ 1 := by
  rw [proteinHorizonCurvatureBudget, bulkLiquidWaterCurvatureFraction_eq_one]

theorem proteinEffectiveCurvatureBudget_eq_effective
    (ξ ρSite ρLocalRaw : ℝ) :
    proteinEffectiveCurvatureBudget ξ ρSite ρLocalRaw =
      effectiveCurvatureBudgetAtXi ξ ρSite
        (nucleationCoordinationExcess ρSite ρLocalRaw) := rfl

end Hqiv.ProteinResearch
