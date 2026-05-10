import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

/-!
# Plastic intercept-order -> zero-channel bridge (theorem shapes)

This module records the two theorem targets requested by the plastic/sphere-arity
construction:

1. **Intercept order classification**
   - composite shells admit higher-order intercepts (`k ≥ 3`)
   - primes and powers of two are restricted to low-order channels

2. **Zero-channel bridge**
   - the intercept profile induces the near-zero phase-cancellation witness used by
     `PlasticZetaPhaseProbe`.

These are compile-safe theorem statements packaged as explicit hypothesis bundles
for immediate use in downstream files.
-/

namespace Hqiv.Geometry

/-- Prime or pure power-of-two shell class. -/
def IsPrimeOrTwoPower (n : ℕ) : Prop :=
  Nat.Prime n ∨ ∃ r : ℕ, n = 2 ^ r

/--
Intercept-order classification hypothesis for a shell family.

`intercept n k` means "shell `n` has an intercept at arity/order `k`".
-/
structure InterceptOrderClassification
    (intercept : ℕ → ℕ → Prop) where
  /-- Every composite shell has a higher-order (`k ≥ 3`) intercept. -/
  composite_has_higher_order :
    ∀ n : ℕ, 2 ≤ n → ¬ Nat.Prime n →
      ∃ k : ℕ, 3 ≤ k ∧ intercept n k
  /-- Prime or two-power shells are confined to low-order channels (`k ≤ 2`). -/
  prime_or_two_power_low_order_only :
    ∀ n k : ℕ, IsPrimeOrTwoPower n → intercept n k → k ≤ 2

/--
The requested classification theorem (eliminator form):
extract both clauses as reusable consequences.
-/
theorem intercept_order_classification
    (intercept : ℕ → ℕ → Prop)
    (H : InterceptOrderClassification intercept) :
    (∀ n : ℕ, 2 ≤ n → ¬ Nat.Prime n →
      ∃ k : ℕ, 3 ≤ k ∧ intercept n k) ∧
    (∀ n k : ℕ, IsPrimeOrTwoPower n → intercept n k → k ≤ 2) := by
  exact ⟨H.composite_has_higher_order, H.prime_or_two_power_low_order_only⟩

/--
Bridge hypothesis from intercept profile to a concrete zeta-phase probe witness.

This packages the "zeros from intercept-channel structure" claim in the same style
as existing HQIV probe bundles.
-/
structure ZeroChannelOfInterceptProfile
    (intercept : ℕ → ℕ → Prop) where
  snaps : List (ℕ × ℕ × ℕ)
  knownZeros : List ℝ
  tEff : ℕ → ℕ → ℕ → ℝ
  zetaAbsAtHalfLine : ℝ → ℝ
  δ : ℝ
  η : ℝ
  /-- Intercept profile compatibility on sampled snaps. -/
  hSnapInterceptProfile :
    ∀ p m k : ℕ, (p, m, k) ∈ snaps → intercept p k
  /-- Channel-level cancellation claim exposed as a near-zero witness. -/
  hChannelNearZero :
    ∃ p m k : ℕ, (p, m, k) ∈ snaps ∧
      ∃ t0 : ℝ, t0 ∈ knownZeros ∧
        |tEff p m k - t0| < δ ∧
        zetaAbsAtHalfLine (tEff p m k) < η

/--
The requested zero-channel theorem shape.

Conclusion is exactly the near-zero witness form used by
`PlasticZetaPhaseProbe.nearZeroWitness`.
-/
theorem zero_channel_of_intercept_profile
    (intercept : ℕ → ℕ → Prop)
    (Z : ZeroChannelOfInterceptProfile intercept) :
    ∃ p m k : ℕ, (p, m, k) ∈ Z.snaps ∧
      ∃ t0 : ℝ, t0 ∈ Z.knownZeros ∧
        |Z.tEff p m k - t0| < Z.δ ∧
        Z.zetaAbsAtHalfLine (Z.tEff p m k) < Z.η := by
  exact Z.hChannelNearZero

end Hqiv.Geometry
