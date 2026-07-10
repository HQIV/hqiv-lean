import Hqiv.ProteinResearch.MiniproteinFoldSpine

/-!
# Ramachandran register profiles — **deprecated**

Use ``MiniproteinBasinReadout`` (8×8 carrier + Ω readout).  This file retains
``RamachandranBasin`` labels and ``basinRamachandranPair`` witnesses only.
-/

namespace Hqiv.ProteinResearch

/-- Proved Ramachandran basin slots used in the register. -/
inductive RamachandranBasin
  | alpha
  | beta
  | strap
  | distortedHelix
  | extended
  | sheetHelixTurn
  | strapHelixTurn
  | helixExit
  deriving DecidableEq, Repr

structure RegisterProfile where
  name : String
  strand : RamachandranBasin
  helix : RamachandranBasin
  coil : RamachandranBasin
  coilBetweenStrandAndHelix : RamachandranBasin
  coilAfterHelix : Option RamachandranBasin := none
  helixWhenSingleton : Option RamachandranBasin := none
  helixNCap : Option RamachandranBasin := none
  helixBody : Option RamachandranBasin := none
  helixCCap : Option RamachandranBasin := none
  deriving Repr

def registerCanonical : RegisterProfile :=
  { name := "canonical"
    strand := .beta
    helix := .alpha
    coil := .extended
    coilBetweenStrandAndHelix := .extended }

def registerCanonicalTurn : RegisterProfile :=
  { name := "canonical_turn"
    strand := .beta
    helix := .alpha
    coil := .extended
    coilBetweenStrandAndHelix := .sheetHelixTurn }

def registerHairpin : RegisterProfile :=
  { name := "hairpin"
    strand := .strap
    helix := .alpha
    coil := .extended
    coilBetweenStrandAndHelix := .sheetHelixTurn
    helixWhenSingleton := some .strap }

def registerCompact : RegisterProfile :=
  { name := "compact"
    strand := .strap
    helix := .distortedHelix
    coil := .extended
    coilBetweenStrandAndHelix := .strapHelixTurn
    coilAfterHelix := some .helixExit }

def registerTrpCage : RegisterProfile :=
  { name := "trp_cage"
    strand := .strap
    helix := .distortedHelix
    coil := .extended
    coilBetweenStrandAndHelix := .sheetHelixTurn
    coilAfterHelix := some .helixExit
    helixNCap := some .strap
    helixBody := some .distortedHelix
    helixCCap := some .helixExit }

theorem register_trp_cage_helix_n_cap :
    registerTrpCage.helixNCap = some .strap := rfl

theorem register_trp_cage_helix_body :
    registerTrpCage.helixBody = some .distortedHelix := rfl

theorem register_trp_cage_helix_c_cap :
    registerTrpCage.helixCCap = some .helixExit := rfl

theorem register_hairpin_strand_is_strap :
    registerHairpin.strand = .strap := rfl

theorem register_compact_helix_is_distorted :
    registerCompact.helix = .distortedHelix := rfl

theorem register_canonical_turn_uses_sheet_turn :
    registerCanonicalTurn.coilBetweenStrandAndHelix = .sheetHelixTurn := rfl

theorem register_trp_cage_sheet_helix_turn_basin :
    registerTrpCage.coilBetweenStrandAndHelix = .sheetHelixTurn := rfl

theorem register_hairpin_sheet_helix_turn_basin :
    registerHairpin.coilBetweenStrandAndHelix = .sheetHelixTurn := rfl

end Hqiv.ProteinResearch
