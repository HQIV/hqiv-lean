import Hqiv.QuantumChemistry.PhaseGeometryDensity

/-!
# Phase allotrope derivation (structural layer)

Allotropes are **derived** from monomer geometry (VSEPR motif + intermolecular
coordination), not chosen from a static name table.

Python package: `hqiv_lab` (`derive_allotropes`, `preferred_allotrope`).
Unit cells feed `PhaseGeometryDensity` for ρ and material response.
-/

namespace Hqiv.QuantumChemistry

/-- Intermolecular packing motif (Python `IntermolecularMotif`). -/
inductive IntermolecularMotif
  | tetrahedralHbond
  | pyramidalHbond
  | apolarClosePack
  | linearChain
  | diatomic
  | generic
  deriving DecidableEq

/-- Named allotrope label from a packing template. -/
structure AllotropeLabel where
  name : String

/-- Derived unit cell witness (lattice constants in ångström). -/
structure DerivedUnitCell where
  allotrope : String
  moleculesPerCell : ℕ
  aAngstrom : ℝ
  bAngstrom : ℝ
  cAngstrom : ℝ
  crystal : CrystalSystem

/-- Allotrope candidate with density and ranking score (Python sorts by `score`). -/
structure AllotropeCandidate where
  label : AllotropeLabel
  cell : DerivedUnitCell
  densityGPerCm3 : ℝ
  curvatureDensityFraction : ℝ
  score : ℝ
  motif : IntermolecularMotif

/-- H₂O tetrahedral motif implies ice-Ih as the preferred hexagonal template. -/
def intermolecularMotifH2O : IntermolecularMotif := .tetrahedralHbond

def allotropeLabelIceIh : AllotropeLabel := ⟨"Ih"⟩

/-- Motif → at least one template exists (structural placeholder; enumeration in Python). -/
theorem motif_h2o_has_ice_ih_label :
    intermolecularMotifH2O = .tetrahedralHbond ∧
      allotropeLabelIceIh.name = "Ih" := by
  constructor <;> rfl

/-- Derived ρ_curvature ∈ [0,1] when solid density is below liquid reference. -/
theorem curvatureFraction_from_density_le_one (ρSolid ρLiquid : ℝ)
    (hρ : 0 ≤ ρSolid) (hL : 0 < ρLiquid) :
    curvatureDensityFraction ρSolid ρLiquid ≤ 1 :=
  curvatureDensityFraction_le_one ρSolid ρLiquid

end Hqiv.QuantumChemistry
