import Hqiv.ProteinResearch.MiniproteinFoldSpine
import Hqiv.ProteinResearch.MiniproteinFoldWitness
import Hqiv.ProteinResearch.MiniproteinRamachandranRegister

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

/-!
## Compact miniprotein basins (positive-φ hairpin / cage register)

Literature Trp-cage–class NMR models sit in a **strap** strand slot (φ = γπ, ψ = απ/2),
a **distorted helix** slot (φ = (γ + α/2)π/2, ψ = γπ/3), and a **helix-exit** coil
(φ = γπ, ψ = −(α + γ/3)π).  All slots use only forced α, γ.
-/

/-- Hairpin strap strand (positive φ): φ = γπ. -/
noncomputable def ramachandranStrapPhi : ℝ := gamma_HQIV * Real.pi

/-- Hairpin strap strand: ψ = (α/2)π. -/
noncomputable def ramachandranStrapPsi : ℝ := (alpha / 2) * Real.pi

theorem ramachandran_strap_phi_eq_gamma_pi :
    ramachandranStrapPhi = (2 / 5 : ℝ) * Real.pi := by
  rw [ramachandranStrapPhi, gamma_eq_2_5]

theorem ramachandran_strap_psi_eq_alpha_half_pi :
    ramachandranStrapPsi = (3 / 10 : ℝ) * Real.pi := by
  rw [ramachandranStrapPsi, alpha_eq_3_5]
  ring

/-- Compact / distorted helix (cage-class positive φ): φ = (γ + α/2)π/2. -/
noncomputable def ramachandranDistortedHelixPhi : ℝ :=
  (gamma_HQIV + alpha / 2) * Real.pi / 2

/-- Compact helix ψ slot: ψ = γπ/3. -/
noncomputable def ramachandranDistortedHelixPsi : ℝ := gamma_HQIV * Real.pi / 3

theorem ramachandran_distorted_helix_phi_rational :
    ramachandranDistortedHelixPhi = (7 / 20 : ℝ) * Real.pi := by
  rw [ramachandranDistortedHelixPhi, gamma_eq_2_5, alpha_eq_3_5]
  ring

theorem ramachandran_distorted_helix_psi_rational :
    ramachandranDistortedHelixPsi = (2 / 15 : ℝ) * Real.pi := by
  rw [ramachandranDistortedHelixPsi, gamma_eq_2_5]
  ring

/-- C-terminal helix-exit coil: ψ = −(α + γ/3)π. -/
noncomputable def ramachandranHelixExitPsi : ℝ := -(alpha + gamma_HQIV / 3) * Real.pi

theorem ramachandran_helix_exit_psi_rational :
    ramachandranHelixExitPsi = -(11 / 15 : ℝ) * Real.pi := by
  rw [ramachandranHelixExitPsi, alpha_eq_3_5, gamma_eq_2_5]
  ring

noncomputable def ramachandranStrapPair : RamachandranPair :=
  { phi := ramachandranStrapPhi, psi := ramachandranStrapPsi }

noncomputable def ramachandranDistortedHelixPair : RamachandranPair :=
  { phi := ramachandranDistortedHelixPhi, psi := ramachandranDistortedHelixPsi }

noncomputable def ramachandranHelixExitPair : RamachandranPair :=
  { phi := ramachandranStrapPhi, psi := ramachandranHelixExitPsi }

/-- Strap → distorted-helix turn at blend parameter α (sheet–helix hairpin coil). -/
noncomputable def ramachandranStrapHelixTurn : RamachandranPair :=
  let ps := ramachandranStrapPair
  let pd := ramachandranDistortedHelixPair
  {
    phi := (1 - alpha) * ps.phi + alpha * pd.phi
    psi := (1 - alpha) * ps.psi + alpha * pd.psi
  }

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

/-- Witness-free Ramachandran pair for each proved register basin. -/
noncomputable def basinRamachandranPair (b : RamachandranBasin) : RamachandranPair :=
  match b with
  | .alpha => ramachandranForSS .helix
  | .beta => ramachandranForSS .strand
  | .strap => ramachandranStrapPair
  | .distortedHelix => ramachandranDistortedHelixPair
  | .extended => ramachandranForSS .coil
  | .sheetHelixTurn => ramachandranSheetHelixBridge .strand .helix
  | .strapHelixTurn => ramachandranStrapHelixTurn
  | .helixExit => ramachandranHelixExitPair

theorem basin_alpha_is_canonical_helix :
    basinRamachandranPair .alpha = ramachandranForSS .helix := rfl

theorem basin_strap_is_strap_pair :
    basinRamachandranPair .strap = ramachandranStrapPair := rfl

theorem basin_distorted_helix_is_distorted_pair :
    basinRamachandranPair .distortedHelix = ramachandranDistortedHelixPair := rfl

theorem basin_sheet_helix_turn_is_alpha_bridge :
    (basinRamachandranPair .sheetHelixTurn).phi =
      alpha * ramachandranAlphaPhi + (1 - alpha) * ramachandranBetaPhi := by
  simp only [basinRamachandranPair, ramachandranSheetHelixBridge, ramachandranForSS,
    ramachandranAlphaPhi, ramachandranBetaPhi]

theorem basin_strap_helix_turn_blends_strap_distorted :
    (basinRamachandranPair .strapHelixTurn).phi =
      (1 - alpha) * ramachandranStrapPhi + alpha * ramachandranDistortedHelixPhi := by
  simp only [basinRamachandranPair, ramachandranStrapHelixTurn, ramachandranStrapPair,
    ramachandranDistortedHelixPair, ramachandranStrapPhi, ramachandranDistortedHelixPhi]

theorem peptide_omega_is_pi : peptideOmegaRad = Real.pi := rfl

end Hqiv.ProteinResearch
