import Hqiv.Story.S3TwiddleResidualMoebius

/-!
# No finite rotational symmetry can isolate the primes (honesty guardrail)

The refinement here is genuinely structured: the 45° rotation is `e^{iπ/4}`, an
**8th root of unity** (8-fold symmetry), and primes `> 3` obey a **6-fold** law:
every prime `> 3` is `≡ ±1 (mod 6)`, i.e. lives in the `φ(6)=2` residue classes
coprime to `6`. Both facts are correct.

The claim under test is that the 6-fold "pure" slot cancels *only* composites
(primes fully cancel; the rest leave a rotation residual). This module shows that
**no finite `N`-fold symmetry** — 6-fold, 8-fold, or any modulus `N` — can isolate
primes, because the "primitive/pure" residue class always contains composites.

* `sixfold_slot_has_composite` — `25 ≡ 1 (mod 6)`, coprime to `6`, composite. The
  6-fold pure slot already leaks (`25, 35, 49, 55, …`).
* `eightfold_slot_has_composite` — `9 ≡ 1 (mod 8)`, coprime to `8`, composite.
* `no_finite_symmetry_isolates_primes` — **for every modulus `N`** there is a
  composite coprime to `N`: the square `p²` of any prime `p > N`. A fixed
  rotational symmetry is a fixed modulus, so the wheel always leaks prime-squares
  and their products.

This is exactly why prime detection requires *unboundedly many* moduli (sieving
up to `√x`), not a single finite rotation order. A finite symmetry gives a wheel
(coprimality to a fixed `N`); it can never certify primality.
-/

namespace Hqiv.Story

/-- The 6-fold "pure" slot (coprime to 6, `≡ ±1 mod 6`) already contains a
composite: `25`. -/
theorem sixfold_slot_has_composite :
    Nat.Coprime 25 6 ∧ 25 % 6 = 1 ∧ ¬ Nat.Prime 25 :=
  ⟨by decide, by norm_num, by norm_num⟩

/-- The 8-fold "pure" slot (coprime to 8) already contains a composite: `9`. -/
theorem eightfold_slot_has_composite :
    Nat.Coprime 9 8 ∧ 9 % 8 = 1 ∧ ¬ Nat.Prime 9 :=
  ⟨by decide, by norm_num, by norm_num⟩

/--
**Impossibility theorem.** For *every* modulus `N ≥ 1` there is a composite number
coprime to `N` (greater than 1): namely `p · p` for any prime `p > N`. Hence no
finite `N`-fold rotational symmetry / wheel can isolate the primes — the
"primitive" class always leaks composites.
-/
theorem no_finite_symmetry_isolates_primes (N : ℕ) (hN : 1 ≤ N) :
    ∃ m : ℕ, Nat.Coprime m N ∧ 1 < m ∧ ¬ Nat.Prime m := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have hp2 : 2 ≤ p := hp.two_le
  have hndvd : ¬ p ∣ N := by
    intro h
    have hple : p ≤ N := Nat.le_of_dvd (by omega) h
    omega
  have hco : Nat.Coprime p N := (hp.coprime_iff_not_dvd).mpr hndvd
  refine ⟨p * p, Nat.Coprime.mul_left hco hco, ?_, ?_⟩
  · nlinarith [hp2]
  · intro hPrime
    rcases hPrime.eq_one_or_self_of_dvd p (dvd_mul_right p p) with h | h
    · omega
    · nlinarith [h, hp2]

end Hqiv.Story
