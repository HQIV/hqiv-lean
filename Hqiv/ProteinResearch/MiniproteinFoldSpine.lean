import Hqiv.QuantumChemistry.PeptideBackboneGeometry
import Hqiv.ProteinResearch.MiniproteinFoldWitness

/-!
# Miniprotein fold spine (secondary structure + tertiary contact rules)

Python mirrors:
  • ``hqiv_lab/miniprotein_backbone.py`` — Ramachandran basins
  • ``hqiv_lab/miniprotein_contacts.py`` — tertiary contact graph
  • ``hqiv_lab/miniprotein_fold.py`` — scaffold contact count + Trp-cage SS map

PDB / COD coordinates remain comparison witnesses only (see ``MiniproteinFoldWitness``).
-/

namespace Hqiv.ProteinResearch

open Hqiv
open Hqiv.QuantumChemistry
open Real

/-- Secondary-structure class for backbone dihedral assignment. -/
inductive SecondaryStructure
  | helix
  | strand
  | coil
  deriving DecidableEq, Repr

/-- Ramachandran alpha ψ slot with 3.6-turn dress: ``−π/4 · (1 + γ/6)``. -/
noncomputable def ramachandranAlphaPsiDressed : ℝ :=
  -Real.pi / 4 * (1 + gamma_HQIV / 6)

theorem ramachandran_alpha_psi_dressed_rational_factor :
    ramachandranAlphaPsiDressed = -Real.pi / 4 * (16 / 15) := by
  rw [ramachandranAlphaPsiDressed, gamma_eq_2_5]
  norm_num

/-- Extended-chain control dihedral (φ = ψ = π). -/
noncomputable def ramachandranExtendedDihedral : ℝ := Real.pi

/-- O(1) linear protein-network contact count (cluster + covalent + hyperclosure). -/
def proteinScaffoldContactCount (nResidues : ℕ) : ℕ :=
  let n := nResidues
  if n ≤ 1 then n
  else if n = 2 then 3
  else 2 * n

theorem protein_scaffold_contact_count_one : proteinScaffoldContactCount 1 = 1 := rfl

theorem protein_scaffold_contact_count_two : proteinScaffoldContactCount 2 = 3 := rfl

theorem protein_scaffold_contact_count_twenty : proteinScaffoldContactCount 20 = 40 := rfl

/-- Tertiary Cα contact kind (Python ``TertiaryContact.kind``). -/
inductive TertiaryContactKind
  | helix_i3
  | helix_i4
  | sheet_i2
  | helix_sheet
  | hydrophobic
  | terminus
  deriving DecidableEq, Repr

/-- Contact kind ranks duplicate-pair resolution (lower = keep; Python ``TERTIARY_CONTACT_KIND_RANK``). -/
def tertiaryContactKindRank (k : TertiaryContactKind) : ℕ :=
  match k with
  | .helix_i3 => 0
  | .helix_i4 => 1
  | .sheet_i2 => 2
  | .helix_sheet => 3
  | .terminus => 4
  | .hydrophobic => 5

theorem tertiary_contact_kind_rank_helix_i3 : tertiaryContactKindRank .helix_i3 = 0 := rfl

theorem tertiary_contact_kind_rank_hydrophobic : tertiaryContactKindRank .hydrophobic = 5 := rfl

/-- Closure pass index from contact kind (locality order; no force multiplier). -/
def tertiaryContactPass (k : TertiaryContactKind) : ℕ :=
  match k with
  | .helix_i3 | .helix_i4 | .sheet_i2 | .helix_sheet => 0
  | .hydrophobic => 1
  | .terminus => 2

theorem tertiary_contact_pass_helix_i3 : tertiaryContactPass .helix_i3 = 0 := rfl

theorem tertiary_contact_pass_terminus : tertiaryContactPass .terminus = 2 := rfl

/-- Hydrophobic residue alphabet (Python ``HYDROPHOBIC_RESIDUES``). -/
def hydrophobicResidues : List Char := ['W', 'L', 'I', 'V', 'F', 'M', 'Y']

def isHydrophobicResidue (c : Char) : Bool := hydrophobicResidues.contains c

theorem trp_is_hydrophobic : isHydrophobicResidue 'W' = true := by decide

/-- Trp-cage (TC5b / 1L2Y) sequence length. -/
def trpCageSequence : String := "NLYIQWLKDGGPSSGRPPPS"

theorem trp_cage_sequence_length : trpCageSequence.length = 20 := by decide

/-- Trp-cage β-strand residues (1-based indices). -/
def trpCageStrandResidues : List ℕ := [2, 3, 4]

/-- Trp-cage α-helix residues (1-based). -/
def trpCageHelixResidues : List ℕ := List.range' 7 11

/-- Trp-cage coil residues (1-based). -/
def trpCageCoilResidues : List ℕ := [1, 5, 6, 18, 19, 20]

theorem trp_cage_helix_residue_count : trpCageHelixResidues.length = 11 := by decide

theorem trp_cage_ss_partition :
    trpCageStrandResidues.length + trpCageHelixResidues.length +
      trpCageCoilResidues.length = trpCageSequence.length := by decide

/-- Compact miniprotein end-to-end scale ``contact · √(n/6)``. -/
noncomputable def compactTerminusCaDistanceScale (nResidues : ℕ) : ℝ :=
  compactTerminusLengthScale nResidues

/-- Minimum sequence length for terminus closure contact. -/
def tertiaryTerminusMinResidues : ℕ := 12

/-- Hydrophobic pair minimum sequence separation (0-based). -/
def hydrophobicMinSeparation : ℕ := 4

/-- Derived tertiary contact distance uses peptide backbone contact at ``n_inter`` OH. -/
noncomputable def derivedTertiaryContactScale (meanBond : ℝ) (nInter : ℕ) : ℝ :=
  peptideBackboneContactDistance meanBond nInter

end Hqiv.ProteinResearch
