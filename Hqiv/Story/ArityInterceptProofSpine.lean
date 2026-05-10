import Mathlib.Data.Nat.Prime.Basic

/-!
# Arity intercept proof spine (Story)

This Story module records the intended arithmetic proof split:

1. **Arity-2 discharge** (`2` rolls over the order-2 pole channel),
2. **Main proof range** on arities `k ≥ 3`,
3. Composite-vs-prime classification by higher-order intercept existence.

The file is intentionally hypothesis-explicit and compile-safe: no `axiom`, no `sorry`.
-/

namespace Hqiv.Story

/-- Intercept relation: `intercept n k` means shell/number `n` intercepts arity `k`. -/
abbrev InterceptRel := ℕ → ℕ → Prop

/-- Arity-2 pole discharge bundle (special channel kept separate from the main proof range). -/
structure TwoArityPoleDischarge (intercept : InterceptRel) where
  /-- `2` always intercepts the 2-arity pole. -/
  two_hits_order2 : intercept 2 2
  /-- Optional extension: all positive powers of two inherit an order-2 intercept witness. -/
  two_power_hits_order2 : ∀ r : ℕ, intercept (2 ^ r) 2

/-- Main `k ≥ 3` range bundle: composites have intercepts, primes do not. -/
structure HighArityInterceptTheory (intercept : InterceptRel) where
  /-- Composite shells have a higher-order intercept (`k ≥ 3`). -/
  composite_has_intercept_ge3 :
    ∀ n : ℕ, 2 ≤ n → ¬ Nat.Prime n →
      ∃ k : ℕ, 3 ≤ k ∧ intercept n k
  /-- Primes have no higher-order intercepts (`k ≥ 3`). -/
  prime_no_intercept_ge3 :
    ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → ¬ intercept p k

/--
Combined classification package:
arity-2 discharge + high-arity (`k ≥ 3`) arithmetic classification.
-/
structure ArityInterceptClassification (intercept : InterceptRel) where
  twoArity : TwoArityPoleDischarge intercept
  highArity : HighArityInterceptTheory intercept

/-- Eliminator form: expose all four core statements as direct theorem outputs. -/
theorem arity_intercept_proof_spine
    (intercept : InterceptRel)
    (C : ArityInterceptClassification intercept) :
    intercept 2 2 ∧
    (∀ r : ℕ, intercept (2 ^ r) 2) ∧
    (∀ n : ℕ, 2 ≤ n → ¬ Nat.Prime n → ∃ k : ℕ, 3 ≤ k ∧ intercept n k) ∧
    (∀ p k : ℕ, Nat.Prime p → 3 ≤ k → ¬ intercept p k) := by
  refine ⟨C.twoArity.two_hits_order2, C.twoArity.two_power_hits_order2, ?_, ?_⟩
  · exact C.highArity.composite_has_intercept_ge3
  · exact C.highArity.prime_no_intercept_ge3

/--
Corollary focused on the user-stated proof region:
for any prime `p`, no intercept exists in the proof range `k ≥ 3`.
-/
theorem prime_no_intercepts_in_proof_range
    (intercept : InterceptRel)
    (C : ArityInterceptClassification intercept)
    (p k : ℕ) (hp : Nat.Prime p) (hk : 3 ≤ k) :
    ¬ intercept p k :=
  C.highArity.prime_no_intercept_ge3 p k hp hk

end Hqiv.Story
