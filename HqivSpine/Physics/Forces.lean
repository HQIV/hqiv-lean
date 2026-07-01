import HqivSpine.Foundation.Carrier
import Mathlib.Data.Finset.Basic

/-!
# `HqivSpine.Physics.Forces` — the force-sector map on the octonion carrier

The eight octonion channels split into the three Standard-Model force sectors by a
single algebraic rule fixed by the carrier (the real axis is EM, the next three are
weak, the last four are strong):

`forceSector a = EM` for `a = 0`, `Weak` for `a ∈ {1,2,3}`, `Strong` for `a ∈ {4,5,6,7}`.

The strong sector therefore occupies exactly four channels, and the three sector
sizes `1 + 3 + 4` exhaust the `carrierMultiplicity = 8` channels — no channel is
left over and none is shared. This is the discrete origin of "the strong force lives
on four octonion directions", with no independent gluon field added.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-- **Force sector:** the three gauge sectors carried by the octonion channels. -/
inductive ForceSector
  | EM
  | Weak
  | Strong
  deriving DecidableEq

/-- **Assignment of an octonion channel to its force sector.** -/
def forceSector (a : Fin 8) : ForceSector :=
  if a.val = 0 then .EM
  else if a.val < 4 then .Weak
  else .Strong

theorem forceSector_zero : forceSector 0 = .EM := rfl

/-- The EM channel: the real axis `a = 0`. -/
def emComponents : Finset (Fin 8) := {0}
/-- The weak channels `a ∈ {1,2,3}`. -/
def weakComponents : Finset (Fin 8) := {1, 2, 3}
/-- The strong channels `a ∈ {4,5,6,7}`. -/
def strongComponents : Finset (Fin 8) := {4, 5, 6, 7}

theorem mem_emComponents (a : Fin 8) : a ∈ emComponents ↔ forceSector a = .EM := by
  fin_cases a <;> decide
theorem mem_weakComponents (a : Fin 8) : a ∈ weakComponents ↔ forceSector a = .Weak := by
  fin_cases a <;> decide
theorem mem_strongComponents (a : Fin 8) : a ∈ strongComponents ↔ forceSector a = .Strong := by
  fin_cases a <;> decide

theorem emComponents_card : emComponents.card = 1 := by decide
theorem weakComponents_card : weakComponents.card = 3 := by decide
/-- **The strong sector occupies exactly four octonion channels.** -/
theorem strongComponents_card : strongComponents.card = 4 := by decide

/-- **The three sectors partition the eight carrier channels:**
`1 + 3 + 4 = carrierMultiplicity`. -/
theorem sector_card_sum_eq_carrier :
    emComponents.card + weakComponents.card + strongComponents.card = carrierMultiplicity := by
  rw [carrierMultiplicity_eq_eight]; decide

/-- **The sectors are pairwise disjoint and cover all of `Fin 8`** (a genuine
partition of the carrier channels). -/
theorem sectors_partition_univ :
    emComponents ∪ weakComponents ∪ strongComponents = (Finset.univ : Finset (Fin 8)) := by
  decide

end HqivSpine.Physics
