import Hqiv.Story.S3DiscretePrimeAxisSampling

/-!
# Primality is decoupled from imaginary-slot count (honesty guardrail)

The S³ cancellation half is proved: a lattice point with two or three nonzero
imaginary components (`twoAxis` / `full`) cancels under reflection, while a
single-axis point survives. What is **not** a theorem — and is in fact false for
the literal sum-of-squares lattice — is the arithmetic encoding

> "an integer is prime ⇔ its lattice point is single-axis `[p,0,0]`,
>  composite ⇔ two/three slots filled."

Here is the precise reason. A scale `N` admits a *genuine* single-axis point
`(a, b, 0, 0)/N` (real part and exactly one imaginary part, both nonzero) iff

`a² + b² = N²` with `a, b > 0`,

i.e. iff `N` is the hypotenuse of a Pythagorean triple. By Fermat / the
two-squares theorem this is the **Gaussian** condition "`N` has a prime factor
`≡ 1 (mod 4)`". That selects primes *mod 4* of the additive arithmetic — it does
**not** coincide with primality, and composites satisfy it freely.

This module proves the decoupling with explicit witnesses:

* `three_not_hypotenuse` — the prime `3` has **no** nondegenerate single-axis
  point (`3` is not a hypotenuse);
* `twentyfive_is_hypotenuse` — the composite `25` **does** (`7² + 24² = 25²`).

Consequently the "only primes survive as single-axis" reading cannot be a fact of
the geometry: it is the *imposed* `S3DiscreteNullLatticeLaw` assumption. The sphere
sees additive (sum-of-squares / Gaussian) structure, not the multiplicative prime
atoms of the Euler product, so this encoding is an extra hypothesis, not a
consequence of S³.
-/

namespace Hqiv.Story

/-- The prime `3` is **not** a hypotenuse: there is no nondegenerate single-axis
lattice point at scale `3` (no `a,b > 0` with `a² + b² = 3²`). -/
theorem three_not_hypotenuse :
    ∀ a b : ℕ, 0 < a → 0 < b → a * a + b * b = 9 → False := by
  intro a b ha hb h
  have haa : 0 < a * a := Nat.mul_pos ha ha
  have hbb : 0 < b * b := Nat.mul_pos hb hb
  have ha2 : a ≤ 2 := by
    by_contra hh; push_neg at hh
    have : 9 ≤ a * a := by nlinarith
    omega
  have hb2 : b ≤ 2 := by
    by_contra hh; push_neg at hh
    have : 9 ≤ b * b := by nlinarith
    omega
  interval_cases a <;> interval_cases b <;> omega

/-- The composite `25` **is** a hypotenuse: `7² + 24² = 25²`, so scale `25` carries
a genuine single-axis point even though `25` is not prime. -/
theorem twentyfive_is_hypotenuse : (7 : ℕ) * 7 + 24 * 24 = 25 * 25 := by
  norm_num

/--
**Decoupling theorem.** Single-axis capability (being a hypotenuse / sum of two
positive squares) does not coincide with primality:

* `3` is prime yet has no nondegenerate single-axis point;
* `25` is composite yet has one (`7² + 24² = 25²`).

So "primes are single-axis, composites are multi-axis" is not carried by the
sum-of-squares lattice; it is the separate `S3DiscreteNullLatticeLaw` assumption.
-/
theorem singleAxis_capability_decoupled_from_primality :
    (Nat.Prime 3 ∧ (∀ a b : ℕ, 0 < a → 0 < b → a * a + b * b = 9 → False)) ∧
      (¬ Nat.Prime 25 ∧ (7 : ℕ) * 7 + 24 * 24 = 25 * 25) :=
  ⟨⟨by norm_num, three_not_hypotenuse⟩, ⟨by norm_num, twentyfive_is_hypotenuse⟩⟩

end Hqiv.Story
