import Hqiv.Story.S3RHZeroSetBridge
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# FE slot discharge for nontrivial zeta zeros

Nontrivial zeros cannot sit at negative integers `s = -n`: the only negative-integer
zeros are the trivial even slots `s = -2(m+1)`.
-/

namespace Hqiv.Story

noncomputable section

open Complex

theorem neg_nat_cast_eq_neg_two_mul (n m : ℕ) :
    (-n : ℂ) = -2 * (m + 1) ↔ n = 2 * (m + 1) := by
  constructor
  · intro h
    replace h := congr_arg Complex.re h
    simp at h
    exact_mod_cast h
  · intro h
    subst h
    simp

private lemma natCast_two_mul (m : ℕ) : (2 * (m + 1) : ℂ) = 2 * ↑(m + 1) := by
  simp [Nat.cast_mul]

private theorem riemannZeta_even_pos_ne_zero (m : ℕ) : riemannZeta (2 * ↑(m + 1)) ≠ 0 := by
  refine fun hz => riemannZeta_ne_zero_of_one_le_re ?_ hz
  rw [← natCast_two_mul]
  simp [ofReal_re]
  norm_cast
  omega

private theorem bernoulli'_two_mul_succ_ne_zero (m : ℕ) : bernoulli' (2 * (m + 1)) ≠ 0 := by
  by_contra h0
  have hb : bernoulli (2 * (m + 1)) = 0 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by omega : 2 * (m + 1) ≠ 1), h0]
  have hz : riemannZeta (2 * ↑(m + 1)) = 0 := by
    have hζ := riemannZeta_two_mul_nat (show m + 1 ≠ 0 by omega)
    rw [← natCast_two_mul] at hζ ⊢
    rw [hζ, hb]
    simp
  exact riemannZeta_even_pos_ne_zero m hz

private theorem riemannZeta_neg_odd_nat_ne_zero {n : ℕ} (ho : Odd n) : riemannZeta (-n) ≠ 0 := by
  intro hz
  rw [riemannZeta_neg_nat_eq_bernoulli'] at hz
  rcases Odd.exists_bit1 ho with ⟨m, rfl⟩
  have hb : bernoulli' (2 * (m + 1)) ≠ 0 := bernoulli'_two_mul_succ_ne_zero m
  rcases div_eq_zero_iff.mp hz with hnum | hden
  · exact hb (by simpa using neg_eq_zero.mp hnum)
  · norm_cast at hden

theorem neg_nat_zeta_zero_is_trivial (n : ℕ) (hz : riemannZeta (-n) = 0) :
    ∃ m : ℕ, (-n : ℂ) = -2 * (m + 1) := by
  suffices ∃ m, n = 2 * (m + 1) by
    rcases this with ⟨m, hn⟩
    refine ⟨m, ?_⟩
    rw [neg_nat_cast_eq_neg_two_mul, hn]
  rcases n.even_or_odd with he | ho
  · rcases he with ⟨k, rfl⟩
    match k with
    | 0 => simp [riemannZeta_zero] at hz
    | k' + 1 => exact ⟨k', by omega⟩
  · exact absurd hz (riemannZeta_neg_odd_nat_ne_zero ho)

/-- Nontrivial zeros are never negative-integer points. -/
theorem nontrivial_zero_fe_slot (s : ℂ) (h : IsNontrivialZetaZero s) (n : ℕ) :
    s ≠ (-n : ℂ) := by
  intro hn
  have hz : riemannZeta (-n) = 0 := by simpa [hn] using h.1
  rcases neg_nat_zeta_zero_is_trivial n hz with ⟨m, hslot⟩
  exact h.2.1 ⟨m, by simpa [hn] using hslot⟩

end

end Hqiv.Story
