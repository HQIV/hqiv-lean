import Hqiv.QuantumChemistry.PhaseGeometryDensity

/-!
# Phase allotrope derivation (structural layer)

Allotropes are **derived** from monomer geometry (VSEPR motif + intermolecular
coordination), not chosen from a static name table.

Python package: `hqiv_lab` (`derive_allotropes`, `preferred_allotrope`).
Unit cells feed `PhaseGeometryDensity` for ρ and material response.

Bulk tetrahedral H-bond networks shrink the intermolecular well by overlapping neighbor
covalent lapses: Python ``neighbor_covalent_lapse_overlap_factor``.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Algebra
open Hqiv.Physics

/-- Intermolecular packing motif (Python `IntermolecularMotif`). -/
inductive IntermolecularMotif
  | tetrahedralHbond
  | pyramidalHbond
  | apolarClosePack
  | linearChain
  | ionicLattice
  | metallicLattice
  | diatomic
  | polyolHbond
  | peptideLayer
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

/-- Bulk tetrahedral H-bond overlap: ``1 − γ·(4/8)/n_inter`` on the H-bond leg (Python mirror). -/
noncomputable def neighborCovalentLapseOverlapFactor (nInter : ℕ) (motif : IntermolecularMotif) : ℝ :=
  match motif with
  | .tetrahedralHbond =>
      let n := max nInter 1
      1 - gamma_HQIV * strongChannelFraction / (n : ℝ)
  | _ => 1

/-- Cap overlap at 1/2 (bulk tetrahedral floor; Python ``neighbor_covalent_lapse_overlap_factor``). -/
noncomputable def neighborCovalentLapseOverlapFactorCapped (nInter : ℕ) (motif : IntermolecularMotif) : ℝ :=
  max (1 / 2 : ℝ) (neighborCovalentLapseOverlapFactor nInter motif)

/-- Halogen zigzag chain: compress strong H···X leg (Python ``halogen_strong_hbond_leg_factor``). -/
noncomputable def halogenStrongHbondLegFactor (zHeavy : ℕ) (motif : IntermolecularMotif) : ℝ :=
  match motif with
  | .linearChain =>
      if zHeavy < 9 then 1
      else
        let zSlot := (max (zHeavy - 8) 0 : ℝ) / zHeavy
        max (1 / 2 : ℝ) (1 - gamma_HQIV * strongChannelFraction * zSlot)
  | _ => 1

/-- Bm21b zigzag orthorhombic breathing (Python ``linear_chain_zigzag_lattice_open_factor``). -/
noncomputable def linearChainZigzagLatticeOpenFactor (nInter : ℕ) (motif : IntermolecularMotif) : ℝ :=
  match motif with
  | .linearChain =>
      let n := max nInter 1
      1 + gamma_HQIV / (6 * n)
  | _ => 1

theorem neighborCovalentLapseOverlapFactor_tetrahedral_four :
    neighborCovalentLapseOverlapFactor 4 .tetrahedralHbond = 1 - gamma_HQIV * strongChannelFraction / 4 := by
  simp [neighborCovalentLapseOverlapFactor, gamma_HQIV, strongChannelFraction]

theorem halogenStrongHbondLegFactor_hf :
    halogenStrongHbondLegFactor 9 .linearChain = 1 - gamma_HQIV * strongChannelFraction / 9 := by
  simp only [halogenStrongHbondLegFactor, IntermolecularMotif.linearChain, ↓reduceIte]
  rw [gamma_eq_2_5, strongChannelFraction_eq_four_eighths]
  norm_num

theorem linearChainZigzagLatticeOpenFactor_hf :
    linearChainZigzagLatticeOpenFactor 2 .linearChain = 1 + gamma_HQIV / 12 := by
  simp only [linearChainZigzagLatticeOpenFactor, IntermolecularMotif.linearChain, ↓reduceIte]
  rw [gamma_eq_2_5]
  norm_num

/-- Crystalline coordination reference for lattice participation (Python ``crystalline_coordination_reference``). -/
def crystallineCoordinationReference : IntermolecularMotif → ℕ
  | .tetrahedralHbond => 4
  | .pyramidalHbond => 3
  | .linearChain => 2
  | .ionicLattice => 6
  | .metallicLattice => 12
  | .polyolHbond => 4
  | .peptideLayer => 4
  | _ => 4

/-- Dynamic min(ρ_s, ρ_m)/max from packing geometry (no fitted melt constants).

Returns ``(ratio, solidDenser)``; Python ``molecular_melt_density_ratio``.
-/
noncomputable def molecularMeltDensityRatio (motif : IntermolecularMotif) (nInter zHeavy : ℕ) :
    ℝ × Bool :=
  let n := max nInter 1
  match motif with
  | .tetrahedralHbond =>
      let overlap := neighborCovalentLapseOverlapFactorCapped n .tetrahedralHbond
      (clampMediumDensity (overlap * phaseLiftCoeff 3 / (1 + alpha)), false)
  | .pyramidalHbond =>
      let openCell := 1 + gamma_HQIV / 4
      (clampMediumDensity (1 / openCell), false)
  | .apolarClosePack =>
      (clampMediumDensity (1 - gamma_HQIV / 4), true)
  | .linearChain =>
      let openChain := linearChainZigzagLatticeOpenFactor n motif
      (clampMediumDensity (1 / max openChain 1), false)
  | .polyolHbond =>
      (clampMediumDensity (tetrahedralMeltDensityRatio n), true)
  | .peptideLayer =>
      let openCell := 1 + gamma_HQIV / 8
      (clampMediumDensity (1 / openCell), true)
  | _ => (1, false)

/-- ρ at melt comparison from solid ρ and dynamic ratio (Python ``melt_density_g_cm3_from_solid``). -/
noncomputable def meltDensityGPerCm3FromSolid (ρSolid ratio : ℝ) (solidDenser : Bool) : ℝ :=
  if ρSolid ≤ 0 ∨ ratio ≤ 0 then 0
  else if solidDenser then ρSolid * ratio else ρSolid / ratio

/-- Motif → at least one template exists (structural placeholder; enumeration in Python). -/
theorem motif_h2o_has_ice_ih_label :
    intermolecularMotifH2O = .tetrahedralHbond ∧
      allotropeLabelIceIh.name = "Ih" := by
  constructor <;> rfl

theorem polyol_melt_uses_tetrahedral_ratio (n : ℕ) :
    (molecularMeltDensityRatio .polyolHbond n 8).1 =
      clampMediumDensity (tetrahedralMeltDensityRatio (max n 1)) := by
  simp [molecularMeltDensityRatio, tetrahedralMeltDensityRatio]

theorem peptide_layer_melt_open_cell :
    (molecularMeltDensityRatio .peptideLayer 4 7).1 =
      clampMediumDensity (1 / (1 + gamma_HQIV / 8)) := by
  simp [molecularMeltDensityRatio]

/-- Derived ρ_curvature ∈ [0,1] when solid density is below liquid reference. -/
theorem curvatureFraction_from_density_le_one (ρSolid ρLiquid : ℝ)
    (hρ : 0 ≤ ρSolid) (hL : 0 < ρLiquid) :
    curvatureDensityFraction ρSolid ρLiquid ≤ 1 :=
  curvatureDensityFraction_le_one ρSolid ρLiquid

end Hqiv.QuantumChemistry
