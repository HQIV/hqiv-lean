import Hqiv.QuantumChemistry.PhaseAllotropeDerivation
import Hqiv.QuantumChemistry.PhaseGeometryDensity
import Hqiv.Physics.DynamicCentreGeometry

/-!
# Foundation chemistry witnesses (sugars, polyols, peptides)

Tier-1/2 condensed-phase validation uses **network-derived** melt ratios only —
no fitted ρ, n, or T_melt constants.  External NIST/COD values are comparison
witnesses in Python ``foundation_panel.py`` (not Lean inputs).

Polyol motif melt reuses ``tetrahedralMeltDensityRatio`` (ice spine).
Peptide-layer melt reuses the γ/8 layer-open slot (half the pyramidal γ/4 cell).
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics

/-- Foundation polyol motif (Python ``IntermolecularMotif.POLYOL_HBOND``). -/
def intermolecularMotifPolyol : IntermolecularMotif := .polyolHbond

/-- Foundation peptide crystal motif (Python ``IntermolecularMotif.PEPTIDE_LAYER``). -/
def intermolecularMotifPeptideLayer : IntermolecularMotif := .peptideLayer

/-- Polyol melt ratio at ``n_inter`` OH contacts — identical to tetrahedral spine. -/
noncomputable def polyolMeltDensityRatio (nInter : ℕ) : ℝ :=
  tetrahedralMeltDensityRatio nInter

theorem polyol_melt_ratio_eq_tetrahedral (n : ℕ) :
    polyolMeltDensityRatio n = tetrahedralMeltDensityRatio n := rfl

/-- Peptide-layer melt open cell ``1 + γ/8`` (Python ``peptide_layer`` packing). -/
noncomputable def peptideLayerOpenCell : ℝ := 1 + gamma_HQIV / 8

theorem peptide_layer_melt_ratio_eq_inverse_open_cell (n z : ℕ) :
    (molecularMeltDensityRatio .peptideLayer n z).1 =
      clampMediumDensity (1 / peptideLayerOpenCell) := by
  simp [molecularMeltDensityRatio, peptideLayerOpenCell]

/-- Steric domain count for sp³ pyranose ring carbons (four bonds, zero lone pairs). -/
theorem pyranose_ring_steric_domains :
    stericDomainCount 4 (centreLonePairCount 6 4) = 4 := by decide

/-- Pyranose chair ring bond count (Python ``PYRANOSE_RING_BOND_COUNT``). -/
def pyranoseRingBondCount : ℕ := 6

/-- Across-ring span / mean ring bond: ``2(1+α+γ/4)`` (cyclohexane-type chair projection). -/
noncomputable def pyranoseChairDiameterFactor : ℝ := 2 * (1 + alpha + gamma_HQIV / 4)

/-- Chair puckering open cell on intermolecular contact (pyramidal γ/4 slot). -/
noncomputable def pyranoseChairOpenCell : ℝ := 1 + gamma_HQIV / 4

/-- Ring-graph nn contact span from mean ring bond length [Å]. -/
noncomputable def pyranoseExocyclicOhDressFactor (nInter : ℕ) : ℝ :=
  Real.sqrt (1 + strongChannelFraction * (max nInter 1 : ℝ) / pyranoseRingBondCount)

noncomputable def pyranoseRingContactSpan (ringMeanBond nInter : ℕ) : ℝ :=
  ringMeanBond * pyranoseChairDiameterFactor * pyranoseChairOpenCell *
    pyranoseExocyclicOhDressFactor nInter

/-- Molecules per cell from polyol crystalline coordination reference (= 4). -/
def pyranoseMoleculesPerCell : ℕ := crystallineCoordinationReference .polyolHbond

/-- In-plane ring tile axis multiplier (ortho shear slot). -/
noncomputable def pyranoseChairInPlaneAxisFactor : ℝ := Real.sqrt 2 * (1 + alpha / 2)

/-- Long inter-layer H-bond stack axis. -/
noncomputable def pyranoseChairStackAxisFactor : ℝ :=
  (1 + alpha + gamma_HQIV / 4) * Real.sqrt 2 * Real.sqrt (1 + strongChannelFraction / 4)

/-- Ring² closure + diatomic glide compress on short axis. -/
noncomputable def pyranoseChairShortAxisRingCompress : ℝ :=
  1 + gamma_HQIV / (pyranoseRingBondCount ^ 2 + 2)

noncomputable def pyranoseChairShortAxisFactor : ℝ :=
  (1 + gamma_HQIV / 4) / (1 + alpha / 4) / pyranoseChairShortAxisRingCompress

theorem pyranose_chair_short_axis_ring_compress_rational :
    pyranoseChairShortAxisRingCompress = 1 + (2 / 5) / 38 := by
  rw [pyranoseChairShortAxisRingCompress, pyranoseRingBondCount, gamma_eq_2_5]
  norm_num

theorem pyranose_molecules_per_cell_eq_four :
    pyranoseMoleculesPerCell = 4 := by
  simp [pyranoseMoleculesPerCell, crystallineCoordinationReference]

/-- Disaccharide / multi-ring Bravais edge scale ``n_rings^(1/3)``. -/
noncomputable def pyranoseDisaccharideCellScale (nRings : ℕ) : ℝ :=
  if nRings ≤ 1 then 1 else (nRings : ℝ) ^ ((1 : ℝ) / 3)

theorem pyranose_disaccharide_cell_scale_unit (n : ℕ) (h : n ≤ 1) :
    pyranoseDisaccharideCellScale n = 1 := by
  unfold pyranoseDisaccharideCellScale
  have h' : ¬ 1 < n := by omega
  simp [h']

theorem pyranose_chair_diameter_factor_rational :
    pyranoseChairDiameterFactor = 17 / 5 := by
  rw [pyranoseChairDiameterFactor, alpha, gamma_eq_2_5]
  norm_num

/-- Triol liquid density factor above T_melt: ``1 + γ/6``. -/
noncomputable def polyolTriolLiquidDensityFactor : ℝ := 1 + gamma_HQIV / 6

theorem polyol_triol_liquid_density_factor_rational :
    polyolTriolLiquidDensityFactor = 16 / 15 := by
  rw [polyolTriolLiquidDensityFactor, gamma_eq_2_5]
  norm_num

/-- Monomer alcohol liquid density factor above T_melt: ``1 + γ/4`` (sheet register slot). -/
noncomputable def monomerPolyolLiquidDensityFactor : ℝ := 1 + gamma_HQIV / 4

theorem monomer_polyol_liquid_density_factor_rational :
    monomerPolyolLiquidDensityFactor = 11 / 10 := by
  rw [monomerPolyolLiquidDensityFactor, gamma_eq_2_5]
  norm_num

theorem pyranose_chair_open_cell_rational :
    pyranoseChairOpenCell = 11 / 10 := by
  rw [pyranoseChairOpenCell, gamma_eq_2_5]
  norm_num

end Hqiv.QuantumChemistry
