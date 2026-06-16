import Hqiv.QuantumChemistry.PeptideBackboneGeometry
import Hqiv.ProteinResearch.ProteinSolventPhaseGeometry

/-!
# Miniprotein fold witnesses (Trp-cage foundation gate)

Python mirrors:
  • ``hqiv_lab/miniprotein_backbone.py`` — derived φ/ψ placement
  • ``hqiv_lab/miniprotein_fold.py`` — secondary-structure + hydrophobic closure
  • ``scripts/hqiv_miniprotein_fold_audit.py`` — PDB Cα grading only

PDB coordinates are **comparison witnesses**, never fold inputs.
-/

namespace Hqiv.ProteinResearch

open Hqiv
open Hqiv.QuantumChemistry
open Real

/-- Ramachandran alpha basin: ``φ = −π/3``. -/
noncomputable def ramachandranAlphaPhi : ℝ := -Real.pi / 3

/-- Legacy alpha ψ (undressed); prefer ``ramachandranAlphaPsiDressed`` in ``MiniproteinFoldSpine``. -/
noncomputable def ramachandranAlphaPsi : ℝ := -Real.pi / 4

/-- Ramachandran beta basin: ``φ = −2π/3``, ``ψ = +2π/3``. -/
noncomputable def ramachandranBetaPhi : ℝ := -2 * Real.pi / 3

noncomputable def ramachandranBetaPsi : ℝ := 2 * Real.pi / 3

/-- Trp-cage (1L2Y) fold pass threshold [Å] from foundation panel. -/
noncomputable def trpCageCaRmsdPassAngstrom : ℝ := 5

/-- Gly–Gly dipeptide crystal gate [Å]. -/
noncomputable def glyGlyCaRmsdPassAngstrom : ℝ := 2

theorem trp_cage_ca_rmsd_pass_eq_five : trpCageCaRmsdPassAngstrom = 5 := rfl

theorem gly_gly_ca_rmsd_pass_eq_two : glyGlyCaRmsdPassAngstrom = 2 := rfl

/-- Helix Cα_i–Cα_{i+3} pitch scale (alias of ``helixCaIi3DistanceScale``). -/
noncomputable def helixCaIi3DistanceScale : ℝ := Hqiv.QuantumChemistry.helixCaIi3DistanceScale

/-- Compact miniprotein terminus scale: ``√(n/6)``. -/
noncomputable def compactTerminusLengthScale (n : ℕ) : ℝ :=
  Real.sqrt ((max n 2 : ℝ) / 6)

theorem helix_ca_i_i3_scale_eq_peptide_geometry :
    helixCaIi3DistanceScale = Hqiv.QuantumChemistry.helixCaIi3DistanceScale := rfl

theorem helix_ca_i_i3_scale_rational :
    helixCaIi3DistanceScale = 17 / 10 := by
  exact Hqiv.QuantumChemistry.helix_ca_i_i3_scale_rational

end Hqiv.ProteinResearch
