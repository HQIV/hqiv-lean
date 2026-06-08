import Hqiv.Story.S3PrimalitySlotDecoupling

/-!
# The "non-reflected" divisor selects squares, not primes (honesty guardrail)

This module tests the proposal: *a composite produces a non-reflected pair on the
line, leaving a residual, so only primes occupy the zeros.*

The multiplicative divisor pairing `d ↦ n/d` is an involution. A pair `(d, n/d)`
is **non-reflected** precisely when it is a fixed point of that involution, i.e.

`d = n/d`  ⇔  `d · d = n`  ⇔  `n` is a perfect square (with `d = √n`).

So the "non-reflected / self-paired" central element behaves the **opposite** of
the claim:

* `prime_not_perfect_square` — a prime has **no** non-reflected divisor (a prime
  is never a perfect square), so its only divisor pair `(1, p)` is a genuine
  reflected pair `1 ↔ p`. Under the reflection-cancellation logic, the prime
  *cancels*.
* `four_balanced_divisor` — the **composite** `4` *does* have a non-reflected
  divisor `2` (`2·2 = 4`); it is the one that survives.

Hence divisor self-pairing selects perfect squares and **excludes** primes. It
cannot "force only primes to occupy the poles."

A further category note (not formalized, but decisive): the nontrivial zeros of
`riemannZeta` are **not** indexed by integers or primes — there are `~ T log T`
of them below height `T`, at transcendental heights on the line. Primes enter
`ζ` *multiplicatively* via the Euler product and are *dual* to the zeros through
the explicit formula; they are not located *at* the zeros. So "composites leave
residuals, primes occupy zeros" is a category mismatch on top of the involution
issue above.
-/

namespace Hqiv.Story

/-- A "non-reflected" / self-paired divisor: a fixed point `d = n/d` of the
divisor involution, equivalently `d · d = n`. -/
def NonReflectedDivisor (n d : ℕ) : Prop := d * d = n

/-- A prime has **no** non-reflected divisor: it is never a perfect square. So a
prime's divisor structure is purely the reflected pair `(1, p)`. -/
theorem prime_not_perfect_square {p : ℕ} (hp : Nat.Prime p) :
    ¬ ∃ d : ℕ, NonReflectedDivisor p d := by
  rintro ⟨d, hd⟩
  unfold NonReflectedDivisor at hd
  have hdvd : d ∣ p := ⟨d, hd.symm⟩
  rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | hpp
  · subst h1
    have h2 := hp.two_le
    omega
  · subst hpp
    have h2 := hp.two_le
    nlinarith [hd, h2]

/-- The composite `4` **does** have a non-reflected divisor `2` (`2·2 = 4`). -/
theorem four_balanced_divisor : NonReflectedDivisor 4 2 := by
  unfold NonReflectedDivisor; norm_num

/--
**Selection theorem.** The non-reflected (self-paired) divisor selects perfect
squares and excludes primes:

* every prime lacks one;
* the composite `4` has one.

This is the opposite of "only primes survive at the poles."
-/
theorem nonReflectedDivisor_selects_squares_not_primes :
    (∀ p : ℕ, Nat.Prime p → ¬ ∃ d : ℕ, NonReflectedDivisor p d) ∧
      NonReflectedDivisor 4 2 :=
  ⟨fun _ hp => prime_not_perfect_square hp, four_balanced_divisor⟩

end Hqiv.Story
