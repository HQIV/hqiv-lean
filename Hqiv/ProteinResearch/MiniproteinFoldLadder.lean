import Hqiv.ProteinResearch.MiniproteinChemistryDynamics
import Hqiv.ProteinResearch.MiniproteinRegisterContacts

/-!
# Miniprotein fold ladder (1L2Y sub-traces, witness-free geometry)

Python mirror: ``hqiv_lab/miniprotein_fold.FRAGMENT_FOLD_SPECS`` + ``fold_trp_cage``.

Each target is a **sub-trace** of PDB 1L2Y (Trp-cage).  PDB Cα coordinates grade predictions
only; fold inputs are register profiles + derived tertiary contacts (``MiniproteinChemistryDynamics``).
-/

namespace Hqiv.ProteinResearch

open Real

/-- Ladder fragment names in difficulty order (Python audit row order). -/
def foldLadderFragmentNames : List String :=
  ["beta_strand_3", "hairpin_turn_5", "alpha_helix_4", "helix_6", "sheet_helix_6",
   "sheet_helix_8", "helix_8", "sheet_helix_10", "cage_core_14"]

theorem fold_ladder_fragment_count : foldLadderFragmentNames.length = 9 := by decide

/-- Hairpin turn coil (1L2Y res 2–6): ``LYIQW``. -/
def hairpinTurn5Sequence : String := "LYIQW"

def hairpinTurn5SecondaryStructure : List SecondaryStructure :=
  [.strand, .strand, .strand, .coil, .coil]

theorem hairpin_turn_5_ss_length :
    hairpinTurn5SecondaryStructure.length = hairpinTurn5Sequence.length := by decide

/-- Helix body with proline (1L2Y res 7–12): ``LKDGGP``. -/
def helix6Sequence : String := "LKDGGP"

def helix6SecondaryStructure : List SecondaryStructure :=
  List.replicate 6 .helix

/-- Sheet–helix hairpin with 3-res helix (1L2Y res 2–9): ``LYIQWLKD``. -/
def sheetHelix8Sequence : String := "LYIQWLKD"

def sheetHelix8SecondaryStructure : List SecondaryStructure :=
  [.strand, .strand, .strand, .coil, .coil, .helix, .helix, .helix]

/-- Compact distorted helix body (1L2Y res 7–14): ``LKDGGPSS``. -/
def helix8Sequence : String := "LKDGGPSS"

def helix8SecondaryStructure : List SecondaryStructure :=
  List.replicate 8 .helix

/-- Trp register N-terminal core (1L2Y res 2–12): ``LYIQWLKDGGP``. -/
def sheetHelix10Sequence : String := "LYIQWLKDGGP"

def sheetHelix10SecondaryStructure : List SecondaryStructure :=
  [.strand, .strand, .strand, .coil, .coil, .helix, .helix, .helix, .helix, .helix, .helix]

/-- Strand + helix sans C-terminal coil (1L2Y res 2–15): ``LYIQWLKDGGPSSG``. -/
def cageCore14Sequence : String := "LYIQWLKDGGPSSG"

def cageCore14SecondaryStructure : List SecondaryStructure :=
  [.strand, .strand, .strand, .coil, .coil,
   .helix, .helix, .helix, .helix, .helix, .helix, .helix, .helix, .helix]

/-- 1L2Y inclusive residue ranges for witness slicing (comparison only). -/
def hairpinTurn5ResidueRange : ℕ × ℕ := (2, 6)
def helix6ResidueRange : ℕ × ℕ := (7, 12)
def sheetHelix8ResidueRange : ℕ × ℕ := (2, 9)
def helix8ResidueRange : ℕ × ℕ := (7, 14)
def sheetHelix10ResidueRange : ℕ × ℕ := (2, 12)
def cageCore14ResidueRange : ℕ × ℕ := (2, 15)

/-- Competitive Cα RMSD gate [Å] for every ladder fragment (strict `<`; AlphaFold-class). -/
noncomputable def competitiveLadderPassAngstrom : ℝ := 2

/-- RMSD pass gates [Å] — grade witnesses only; all fragments share the competitive bar. -/
noncomputable def hairpinTurn5PassAngstrom : ℝ := competitiveLadderPassAngstrom
noncomputable def helix6PassAngstrom : ℝ := competitiveLadderPassAngstrom
noncomputable def sheetHelix8PassAngstrom : ℝ := competitiveLadderPassAngstrom
noncomputable def helix8PassAngstrom : ℝ := competitiveLadderPassAngstrom
noncomputable def sheetHelix10PassAngstrom : ℝ := competitiveLadderPassAngstrom
noncomputable def cageCore14PassAngstrom : ℝ := competitiveLadderPassAngstrom

theorem ladder_pass_gates_are_competitive :
    hairpinTurn5PassAngstrom = 2 ∧ helix6PassAngstrom = 2 ∧
      sheetHelix8PassAngstrom = 2 ∧ helix8PassAngstrom = 2 ∧
      sheetHelix10PassAngstrom = 2 ∧ cageCore14PassAngstrom = 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-!
## Derived tertiary contact counts (pinned; Python ``build_tertiary_contact_graph``)
-/

def sheetHelix6SecondaryStructure : List SecondaryStructure :=
  [.strand, .strand, .strand, .coil, .coil, .helix]

theorem sheet_helix_6_tertiary_contacts :
    countTertiaryContactsHairpin "LYIQWL" sheetHelix6SecondaryStructure false = 3 := by
  native_decide

theorem sheet_helix_8_tertiary_contacts :
    countTertiaryContactsHairpin sheetHelix8Sequence sheetHelix8SecondaryStructure false = 7 := by
  native_decide

theorem helix_8_tertiary_contacts :
    countTertiaryContacts helix8Sequence helix8SecondaryStructure = 9 := by native_decide

theorem sheet_helix_10_tertiary_contacts :
    countTertiaryContacts sheetHelix10Sequence sheetHelix10SecondaryStructure = 12 := by native_decide

theorem cage_core_14_tertiary_contacts :
    countTertiaryContacts cageCore14Sequence cageCore14SecondaryStructure = 19 := by native_decide

theorem cage_core_14_uses_trp_register :
    registerTrpCage.name = "trp_cage" := rfl

theorem sheet_helix_10_uses_trp_register_coil_turn :
    registerTrpCage.coilBetweenStrandAndHelix = .sheetHelixTurn := rfl

theorem helix_8_uses_compact_distorted_register :
    registerCompact.helix = .distortedHelix := register_compact_helix_is_distorted

theorem helix_6_uses_trp_cage_segmented_register :
    registerTrpCage.helixBody = some .distortedHelix := register_trp_cage_helix_body

theorem helix_6_ss_length :
    helix6SecondaryStructure.length = helix6Sequence.length := by decide

theorem hairpin_turn_5_strand_slot :
    registerHairpin.strand = .strap := register_hairpin_strand_is_strap

end Hqiv.ProteinResearch
