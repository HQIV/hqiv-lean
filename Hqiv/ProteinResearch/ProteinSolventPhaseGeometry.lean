import Hqiv.QuantumChemistry.PhaseGeometryDensity
import Hqiv.QuantumChemistry.PhaseAllotropeDerivation
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

end Hqiv.ProteinResearch
