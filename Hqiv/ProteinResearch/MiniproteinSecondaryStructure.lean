import Hqiv.ProteinResearch.MiniproteinRamachandran

/-!
# Secondary-structure assignment from 1-based residue lists

Python mirror: ``hqiv_lab/miniprotein_contacts.ss_per_residue``.
-/

namespace Hqiv.ProteinResearch

/-- Lookup SS class at 1-based residue index (default coil). -/
def secondaryStructureAt (strand helix coil : List ℕ) (oneBased : ℕ) : SecondaryStructure :=
  if strand.contains oneBased then .strand
  else if helix.contains oneBased then .helix
  else .coil

/-- Per-residue SS list for sequence length ``n`` (0-based list index). -/
def secondaryStructurePerResidue (n : ℕ) (strand helix coil : List ℕ) : List SecondaryStructure :=
  (List.range n).map fun i => secondaryStructureAt strand helix coil (i + 1)

/-- Trp-cage literature SS map (1L2Y / TC5b), 0-based list. -/
def trpCageSecondaryStructure : List SecondaryStructure :=
  [.coil, .strand, .strand, .strand, .coil, .coil,
   .helix, .helix, .helix, .helix, .helix, .helix, .helix, .helix, .helix, .helix, .helix,
   .coil, .coil, .coil]

theorem trp_cage_ss_from_lists :
    trpCageSecondaryStructure =
      secondaryStructurePerResidue 20 trpCageStrandResidues trpCageHelixResidues trpCageCoilResidues := by
  native_decide

theorem trp_cage_ss_length : trpCageSecondaryStructure.length = 20 := by decide

theorem trp_cage_residue1_is_coil :
    trpCageSecondaryStructure.get ⟨0, by decide⟩ = .coil := by decide

theorem trp_cage_residue2_is_strand :
    trpCageSecondaryStructure.get ⟨1, by decide⟩ = .strand := by decide

theorem trp_cage_residue7_is_helix :
    trpCageSecondaryStructure.get ⟨6, by decide⟩ = .helix := by decide

def trpCageHelixRunOk : Bool :=
  (trpCageSecondaryStructure.drop 6).take 11 |>.all (· == .helix)

theorem trp_cage_helix_run_length : trpCageHelixRunOk = true := by decide

end Hqiv.ProteinResearch
