/-
  HQIV Algebra: the composition-algebra laws of 𝕆
  ================================================

  Capstone of the Cayley–Dickson ladder. On the concrete octonions
  `𝕆 = CayleyDickson³ ℝ` we discharge the genuinely non-trivial
  composition-algebra facts — the ones that *fail* one rung higher (the
  sedenions `CayleyDickson⁴ ℝ` are neither alternative nor a composition
  algebra), so these are real theorems, not formalities:

  * **alternativity** `x(xy) = (xx)y`, `(yx)x = y(xx)` and **flexibility**;
  * **norm multiplicativity** `‖xy‖ = ‖x‖·‖y‖` (the eight-square identity);
  * as a corollary, `𝕆` has **no zero divisors**.

  Each is a polynomial identity in the eight real coordinates, so after
  splitting to the `ℝ` leaves (`ext`) and unfolding the Cayley–Dickson
  multiplication/conjugation/norm, `ring` closes the goal.

  No `sorry`, no new `axiom`, no `native_decide`.
-/

import Hqiv.Algebra.CayleyDicksonNorm

namespace Hqiv.Algebra

namespace CayleyDickson

-- Make `ext` recurse through every Cayley–Dickson layer down to the `ℝ` leaves.
attribute [local ext] CayleyDickson.ext

/-! ### Unfolding lemmas for the recursive hypercomplex norm -/

section unfold
variable {R : Type*} {A : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [NonAssocRing A] [StarRing A] [Module R A] [NormedHypercomplex R A]

/-- One layer of the Cayley–Dickson norm: `‖a‖ = ‖a.fst‖ + ‖(a.snd)*‖`. -/
lemma hcnorm_cd (a : CayleyDickson A) :
    hcnorm (R := R) a = hcnorm (R := R) a.fst + hcnorm (R := R) (star a.snd) := rfl

end unfold

/-- The base-case norm on `ℝ` is the square. -/
lemma hcnorm_real (r : ℝ) : hcnorm (R := ℝ) r = r ^ 2 := rfl

/-! ### Alternativity and flexibility -/

set_option maxHeartbeats 4000000 in
/-- **Left alternativity**: `x · (x · y) = (x · x) · y`. -/
theorem octonion_mul_left_alt (x y : 𝕆) : x * (x * y) = (x * x) * y := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, neg_mul, mul_neg,
    sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd] <;> ring

set_option maxHeartbeats 4000000 in
/-- **Right alternativity**: `(y · x) · x = y · (x · x)`. -/
theorem octonion_mul_right_alt (x y : 𝕆) : (y * x) * x = y * (x * x) := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, neg_mul, mul_neg,
    sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd] <;> ring

set_option maxHeartbeats 4000000 in
/-- **Flexibility**: `(x · y) · x = x · (y · x)`. -/
theorem octonion_mul_flexible (x y : 𝕆) : (x * y) * x = x * (y * x) := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, neg_mul, mul_neg,
    sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd] <;> ring

/-! ### Norm multiplicativity (the eight-square identity) -/

set_option maxHeartbeats 8000000 in
/-- **The octonionic norm is multiplicative**: `‖x · y‖ = ‖x‖ · ‖y‖`.

This is the Degen eight-square identity; it makes `𝕆` a composition algebra. -/
theorem octonion_hcnorm_mul (x y : 𝕆) :
    hcnorm (R := ℝ) (x * y) = hcnorm (R := ℝ) x * hcnorm (R := ℝ) y := by
  simp only [hcnorm_cd, hcnorm_real, mul_fst, mul_snd, star_fst, star_snd, star_trivial,
    neg_mul, mul_neg, sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd,
    sub_fst, sub_snd]
  ring

/-! ### Corollary: no zero divisors -/

/-- `𝕆` has **no zero divisors**: a product vanishes only if a factor does.
A direct consequence of norm multiplicativity together with definiteness of the
norm. -/
theorem octonion_eq_zero_or_eq_zero_of_mul_eq_zero (x y : 𝕆) (h : x * y = 0) :
    x = 0 ∨ y = 0 := by
  have hn : hcnorm (R := ℝ) x * hcnorm (R := ℝ) y = 0 := by
    rw [← octonion_hcnorm_mul, h]; simp [hcnorm_cd, hcnorm_real]
  rcases mul_eq_zero.mp hn with hx | hy
  · exact Or.inl (hcnorm_eq_zero (R := ℝ) x hx)
  · exact Or.inr (hcnorm_eq_zero (R := ℝ) y hy)

end CayleyDickson

end Hqiv.Algebra
