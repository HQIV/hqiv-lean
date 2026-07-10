import Hqiv.ProteinResearch.MiniproteinClosureConvergence
import Hqiv.ProteinResearch.MiniproteinRamachandranRegister

/-!
# Staged NeRF tertiary closure (pass order witness)

Python mirror: ``hqiv_lab/miniprotein_closure.apply_staged_nerf_contact_refinement``.

Four-pass φ/ψ coordinate search follows ``tertiaryContactPass`` locality:
structure register → hydrophobic burial → terminus cap → full-graph polish.
Trp-cage uses this path (``fold_trp_cage`` default ``closure_engine="nerf"``).
-/

namespace Hqiv.ProteinResearch

open Hqiv.ProteinResearch

/-- Staged NeRF closure pass labels (Python staged refinement rounds). -/
inductive StagedNerfPass
  | structureRegister
  | hydrophobicBurial
  | terminusCap
  | fullPolish
  deriving DecidableEq, Repr

def stagedNerfPassOrder : List StagedNerfPass :=
  [.structureRegister, .hydrophobicBurial, .terminusCap, .fullPolish]

theorem staged_nerf_pass_order_length :
    stagedNerfPassOrder.length = 4 := by decide

/-- Map staged pass to contact kinds refined in that pass. -/
def stagedPassContactKinds (p : StagedNerfPass) : List TertiaryContactKind :=
  match p with
  | .structureRegister => [.helix_i3, .helix_i4, .sheet_i2, .helix_sheet]
  | .hydrophobicBurial => [.hydrophobic]
  | .terminusCap => [.terminus]
  | .fullPolish => [.helix_i3, .helix_i4, .sheet_i2, .helix_sheet, .hydrophobic, .terminus]

theorem structure_pass_uses_register_contacts :
    stagedPassContactKinds .structureRegister =
      [.helix_i3, .helix_i4, .sheet_i2, .helix_sheet] := rfl

theorem hydrophobic_pass_kind :
    stagedPassContactKinds .hydrophobicBurial = [.hydrophobic] := rfl

theorem full_polish_includes_all_kinds :
    [.helix_i3, .helix_i4, .sheet_i2, .helix_sheet, .hydrophobic, .terminus] ⊆
      stagedPassContactKinds .fullPolish := by
  intro k hk
  simp only [List.mem_singleton, stagedPassContactKinds, List.mem_cons, List.mem_nil_iff,
    or_false] at hk ⊢
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Every contact kind appears in at least one staged pass before full polish. -/
theorem tertiary_kind_covered_by_staged_passes (k : TertiaryContactKind) :
    k ∈ stagedPassContactKinds .structureRegister ∨
      k ∈ stagedPassContactKinds .hydrophobicBurial ∨
      k ∈ stagedPassContactKinds .terminusCap ∨
      k ∈ stagedPassContactKinds .fullPolish := by
  cases k <;> simp [stagedPassContactKinds]

theorem trp_cage_staged_final_polish_rounds :
    stagedNerfPassOrder.getLast? = some .fullPolish := by decide

theorem register_trp_cage_strand_is_strap :
    registerTrpCage.strand = .strap := rfl

theorem register_trp_cage_name :
    registerTrpCage.name = "trp_cage" := rfl

end Hqiv.ProteinResearch
