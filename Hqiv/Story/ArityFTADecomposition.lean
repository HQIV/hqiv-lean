import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic

/-!
# Arity decomposition from FTA (Story)

This module packages arithmetic facts we use as the formal "FTA backbone":

* prime-factor list uniqueness/injectivity on positive shells,
* prime/composite partition for `n ≥ 2`,
* composite shells admit nontrivial factor-pair witnesses.

These statements are designed to feed the arity-mirror cancellation and
`k = 3` residue modules.
-/

namespace Hqiv.Story

/-- Arity signature = total prime multiplicity (`Ω(n)`) from the prime factor list. -/
def aritySignature (n : ℕ) : ℕ :=
  n.primeFactorsList.length

/-- FTA injectivity on positive shells via equality of prime-factor lists. -/
theorem eq_of_primeFactorsList_eq {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.primeFactorsList = b.primeFactorsList) :
    a = b := by
  exact Nat.eq_of_perm_primeFactorsList ha hb (h ▸ List.Perm.refl _)

/-- Equal prime-factor lists imply equal arity signatures. -/
theorem aritySignature_eq_of_primeFactorsList_eq {a b : ℕ}
    (h : a.primeFactorsList = b.primeFactorsList) :
    aritySignature a = aritySignature b := by
  unfold aritySignature
  simpa [h]

/-- Prime shells are exactly the prime residue channel. -/
def PrimeResidueChannel (n : ℕ) : Prop := Nat.Prime n

/-- Composite shells carry the nontrivial mirror-cancellation channel. -/
def CompositeChannel (n : ℕ) : Prop := 2 ≤ n ∧ ¬ Nat.Prime n

/-- For `n ≥ 2`, arithmetic partition: prime residue or composite channel. -/
theorem prime_or_composite_channel (n : ℕ) (hn : 2 ≤ n) :
    PrimeResidueChannel n ∨ CompositeChannel n := by
  by_cases hp : Nat.Prime n
  · exact Or.inl hp
  · exact Or.inr ⟨hn, hp⟩

/-- Prime residue has canonical FTA list form `[p]`. -/
theorem primeResidue_primeFactorsList_singleton {p : ℕ}
    (hp : PrimeResidueChannel p) :
    p.primeFactorsList = [p] :=
  Nat.primeFactorsList_prime hp

/-- Composite channel admits a nontrivial factor pair witness. -/
theorem compositeChannel_has_nontrivial_factor_pair {n : ℕ}
    (hc : CompositeChannel n) :
    ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = n := by
  rcases hc with ⟨hn2, hnotPrime⟩
  rcases (Nat.not_prime_iff_exists_mul_eq hn2).mp hnotPrime with ⟨a, b, ha_lt, hb_lt, hab⟩
  have ha_ne1 : a ≠ 1 := by
    intro ha1
    subst ha1
    have hb_eq_n : b = n := by simpa [one_mul] using hab
    exact (lt_irrefl n) (hb_eq_n ▸ hb_lt)
  have hb_ne1 : b ≠ 1 := by
    intro hb1
    subst hb1
    have ha_eq_n : a = n := by simpa [mul_one] using hab
    exact (lt_irrefl n) (ha_eq_n ▸ ha_lt)
  have ha_ne0 : a ≠ 0 := by
    intro ha0
    subst ha0
    have : n = 0 := by simpa using hab.symm
    exact (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hn2)) this.symm
  have hb_ne0 : b ≠ 0 := by
    intro hb0
    subst hb0
    have : n = 0 := by simpa using hab.symm
    exact (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hn2)) this.symm
  have ha_gt1 : 1 < a := by
    exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha_ne0)) (Ne.symm ha_ne1)
  have hb_gt1 : 1 < b := by
    exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb_ne0)) (Ne.symm hb_ne1)
  exact ⟨a, b, ha_gt1, hb_gt1, hab⟩

end Hqiv.Story

