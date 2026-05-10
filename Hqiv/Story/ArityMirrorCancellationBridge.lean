import Hqiv.Story.ArityInterceptProofSpine
import Hqiv.Geometry.QuantumFactorGateFrontier

/-!
# Arity mirror cancellation bridge (Story)

This module explicitly **imports and composes** two already-established theorem tracks:

1. `ArityInterceptProofSpine` (prime/composite split for higher arities `k ≥ 3`),
2. `QuantumFactorGateFrontier` (`#Q`-shell arity-slot coverage).

It gives a small bridge lemma shape for the user narrative:
slot-level arity coverage exists on the shell, while prime shells still reject
higher-arity intercepts in the proof range.
-/

namespace Hqiv.Story

open Hqiv.Geometry.QuantumFactorGateFrontier

/--
Prime shell bridge:
if an arity `k` lies in the `#Q` shell window (`2 ≤ k ≤ qSpan p`) and `k ≥ 3`,
then a slot witness exists for `k`, but the prime still has no higher-arity intercept.

This composes:
* `arityCoverage_exists_slot` from `QuantumFactorGateFrontier`,
* `prime_no_intercepts_in_proof_range` from `ArityInterceptProofSpine`.
-/
theorem prime_shell_slot_exists_and_no_intercept_ge3
    (intercept : InterceptRel)
    (C : ArityInterceptClassification intercept)
    (p k : ℕ)
    (hp : Nat.Prime p)
    (hk3 : 3 ≤ k)
    (hkQ : k ≤ qSpan p) :
    (∃ slot, cofactorCandidateFromSlot p slot = k) ∧ ¬ intercept p k := by
  have hk2 : 2 ≤ k := le_trans (by decide : 2 ≤ 3) hk3
  refine ⟨arityCoverage_exists_slot p k hk2 hkQ, ?_⟩
  exact prime_no_intercepts_in_proof_range intercept C p k hp hk3

/--
Mirror-slot packaging for a shell arity:
if `k` is represented by some slot `slot`, we can always form a reflected pair
`(slot, reflectSlot n slot)` in the doubled-span mirror geometry.

This is the finite-shell geometric witness used by cancellation narratives.
-/
theorem shell_mirror_pair_exists_of_slot
    (n k slot : ℕ)
    (hslot : cofactorCandidateFromSlot n slot = k) :
    ∃ s₁ s₂ : ℕ,
      cofactorCandidateFromSlot n s₁ = k ∧ s₂ = reflectSlot n s₁ := by
  refine ⟨slot, reflectSlot n slot, hslot, rfl⟩

end Hqiv.Story

