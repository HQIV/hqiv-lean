import Hqiv.ProteinResearch.MiniproteinRamachandran
import Hqiv.ProteinResearch.MiniproteinRamachandranRegister

/-!
# Register profile → tertiary contact coupling (derived from profile fields)

Python mirror: ``hqiv_lab/miniprotein_register.register_contact_coupling``.

Witness-free: topology flags and bound-state target slots follow **basin slots** on the
register struct (``helix``, ``strand``, ``helixBody``, ``helixWhenSingleton``), not
profile-name conditionals.  Segmented Trp-cage (``helixBody = some .distortedHelix``)
keeps canonical β sheet i+2 and α helix i±3,4 contact targets until segmented strap-sheet
proofs land; closure bridges the gap from strap strand φ/ψ.
-/

namespace Hqiv.ProteinResearch

/-- Profiles that select strap NeRF sheet i+2 targets (``strap_sheet_i2``). -/
def strapSheetI2Profiles : List RegisterProfile :=
  [registerHairpin, registerCompact]

/-- Profiles that select distorted-helix i+3/i+4 targets (``compact_helix``). -/
def compactHelixContactProfiles : List RegisterProfile :=
  [registerCompact]

def profileUsesStrapSheetI2 (p : RegisterProfile) : Prop :=
  p.name = "hairpin" ∨ p.name = "compact"

def profileUsesCompactHelixContacts (p : RegisterProfile) : Prop :=
  p.name = "compact"

theorem hairpin_uses_strap_sheet_i2 :
    profileUsesStrapSheetI2 registerHairpin := by
  simp [profileUsesStrapSheetI2, registerHairpin]

theorem compact_profile_uses_strap_sheet_i2 :
    profileUsesStrapSheetI2 registerCompact := by
  simp [profileUsesStrapSheetI2, registerCompact]

theorem compact_profile_uses_distorted_helix_contacts :
    profileUsesCompactHelixContacts registerCompact := by
  simp [profileUsesCompactHelixContacts, registerCompact]

theorem trp_cage_not_strap_sheet_i2_profile :
    ¬ profileUsesStrapSheetI2 registerTrpCage := by
  simp [profileUsesStrapSheetI2, registerTrpCage]

theorem trp_cage_strap_strand_slot :
    registerTrpCage.strand = .strap := rfl

theorem trp_cage_distorted_helix_body :
    registerTrpCage.helixBody = some .distortedHelix := rfl

/-- Strap strand φ slot (γπ) used by Trp-cage register. -/
theorem trp_cage_strand_phi_eq_gamma_pi :
    ramachandranStrapPhi = gamma_HQIV * Real.pi := rfl

end Hqiv.ProteinResearch
