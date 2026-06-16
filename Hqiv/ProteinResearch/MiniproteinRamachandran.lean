import Hqiv.ProteinResearch.MiniproteinFoldSpine
import Hqiv.ProteinResearch.MiniproteinFoldWitness

/-!
# Ramachandran dihedral basins (derived φ/ψ slots)

Python mirror: ``hqiv_lab/miniprotein_backbone.py``.
-/

namespace Hqiv.ProteinResearch

open Hqiv
open Real

/-- Alpha-helix ψ with 3.6-turn dress (canonical; replaces legacy ``ramachandranAlphaPsi``). -/
noncomputable def ramachandranAlphaPsiCanonical : ℝ := ramachandranAlphaPsiDressed

/-- Coil / extended control: ``φ = ψ = π``. -/
noncomputable def ramachandranCoilPhi : ℝ := ramachandranExtendedDihedral

noncomputable def ramachandranCoilPsi : ℝ := ramachandranExtendedDihedral

/-- Trans peptide bond ω (planar amide). -/
noncomputable def peptideOmegaRad : ℝ := Real.pi

structure RamachandranPair where
  phi : ℝ
  psi : ℝ

noncomputable def ramachandranForSS (ss : SecondaryStructure) : RamachandranPair :=
  match ss with
  | .helix => { phi := ramachandranAlphaPhi, psi := ramachandranAlphaPsiCanonical }
  | .strand => { phi := ramachandranBetaPhi, psi := ramachandranBetaPsi }
  | .coil => { phi := ramachandranCoilPhi, psi := ramachandranCoilPsi }

theorem ramachandran_helix_phi :
    (ramachandranForSS .helix).phi = -Real.pi / 3 := rfl

theorem ramachandran_helix_psi_dressed :
    (ramachandranForSS .helix).psi = ramachandranAlphaPsiDressed := rfl

theorem ramachandran_strand_phi :
    (ramachandranForSS .strand).phi = -2 * Real.pi / 3 := rfl

theorem ramachandran_strand_psi :
    (ramachandranForSS .strand).psi = 2 * Real.pi / 3 := rfl

theorem ramachandran_coil_dihedrals :
    (ramachandranForSS .coil).phi = Real.pi ∧
    (ramachandranForSS .coil).psi = Real.pi := by
  constructor <;> rfl

/-- α-weighted bridge between unlike SS neighbors (optional coil override). -/
noncomputable def ramachandranSheetHelixBridge (left right : SecondaryStructure) : RamachandranPair :=
  let pl := ramachandranForSS left
  let pr := ramachandranForSS right
  {
    phi := alpha * pr.phi + (1 - alpha) * pl.phi
    psi := alpha * pr.psi + (1 - alpha) * pl.psi
  }

theorem ramachandran_sheet_helix_bridge_uses_alpha :
    (ramachandranSheetHelixBridge .strand .helix).phi =
      alpha * ramachandranAlphaPhi + (1 - alpha) * ramachandranBetaPhi := by
  simp only [ramachandranSheetHelixBridge, ramachandranForSS, ramachandranAlphaPhi, ramachandranBetaPhi]

theorem peptide_omega_is_pi : peptideOmegaRad = Real.pi := rfl

end Hqiv.ProteinResearch
