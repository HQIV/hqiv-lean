import HqivSpine.Algebra.CayleyDickson
import HqivSpine.Foundation.Fano

/-!
# `HqivSpine.Algebra.Octonion` — norm, division, basis, laws, Fano bridge

Capstone of the doubling tower. On `𝕆 = CayleyDickson³ ℝ` we:

* equip the tower with a real-valued hypercomplex norm `‖a‖·1 = a·star a`, giving a
  two-sided inverse `a⁻¹ = ‖a‖⁻¹·star a` (the octonions are a division algebra);
* exhibit the standard basis `e₀ … e₇`, the imaginary squares `eᵢ² = −1`, and the
  seven oriented Fano-line products;
* discharge the genuinely non-trivial composition-algebra laws — alternativity,
  flexibility, norm multiplicativity (the eight-square identity), conjugation as a
  norm-preserving anti-automorphism `star (x·y) = star y · star x`, and the three
  **Moufang identities** (the strongest associativity-like laws of an alternative
  algebra) — that *fail* one rung higher (the sedenions), hence no zero divisors;
* show the products land exactly on the abstractly-derived Fano incidence in
  `HqivSpine.Foundation`.

No `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Algebra

namespace CayleyDickson

variable {R : Type*} {A : Type*}

/-! ### Compatibility classes threaded through one doubling -/

section compat
variable [CommSemiring R]
variable [NonUnitalNonAssocRing A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

instance : IsScalarTower R (CayleyDickson A) (CayleyDickson A) where
  smul_assoc r a b := by
    ext
    · show ((r • a) * b).fst = (r • (a * b)).fst
      simp only [mul_fst, smul_fst, smul_snd, smul_sub, smul_mul_assoc, mul_smul_comm]
    · show ((r • a) * b).snd = (r • (a * b)).snd
      simp only [mul_snd, smul_fst, smul_snd, smul_add, smul_mul_assoc, mul_smul_comm]

end compat

section starmodule
variable [CommSemiring R] [Star R] [TrivialStar R]
variable [NonUnitalNonAssocRing A] [StarRing A]
variable [Module R A] [StarModule R A]

instance : StarModule R (CayleyDickson A) where
  star_smul r a := by
    ext
    · simp only [star_fst, smul_fst, star_smul]
    · simp only [star_snd, smul_snd, smul_neg, star_trivial]

end starmodule

section smulcomm
variable [CommSemiring R] [Star R] [TrivialStar R]
variable [NonUnitalNonAssocRing A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

instance : SMulCommClass R (CayleyDickson A) (CayleyDickson A) where
  smul_comm r a b := by
    ext
    · show (r • (a * b)).fst = (a * (r • b)).fst
      simp only [mul_fst, smul_fst, smul_snd, smul_sub, smul_mul_assoc, mul_smul_comm,
        star_smul, star_trivial]
    · show (r • (a * b)).snd = (a * (r • b)).snd
      simp only [mul_snd, smul_fst, smul_snd, smul_add, smul_mul_assoc, mul_smul_comm,
        star_smul, star_trivial]

end smulcomm

/-! ### The hypercomplex norm -/

/-- A real-valued hypercomplex norm: a definite quadratic form realizing
`‖a‖·1 = a·star a` (and the conjugate-side identity), exactly what is needed to
write the inverse `a⁻¹ = ‖a‖⁻¹·star a`. -/
class NormedHypercomplex (R : Type*) (A : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [NonAssocSemiring A] [Module R A] [Star A] where
  hcnorm : A → R
  hcnorm_mul : ∀ a, hcnorm a • (1 : A) = a * star a
  hcnorm_mul' : ∀ a, hcnorm a • (1 : A) = star a * a
  hcnorm_nonneg : ∀ a, 0 ≤ hcnorm a
  hcnorm_eq_zero : ∀ a, hcnorm a = 0 → a = 0

export NormedHypercomplex (hcnorm hcnorm_mul hcnorm_mul' hcnorm_nonneg hcnorm_eq_zero)

/-- `ℝ` carries the square norm `a ↦ a²`. -/
instance : NormedHypercomplex ℝ ℝ where
  hcnorm a := a ^ 2
  hcnorm_mul a := by simp [pow_two, star_trivial, smul_eq_mul]
  hcnorm_mul' a := by simp [pow_two, star_trivial, smul_eq_mul]
  hcnorm_nonneg a := sq_nonneg a
  hcnorm_eq_zero a := fun h => by rwa [pow_two, mul_self_eq_zero] at h

section normed
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [NonAssocRing A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NormedHypercomplex R A]

/-- The Cayley–Dickson doubling of a hypercomplex norm: `‖(a, b)‖ = ‖a‖ + ‖b*‖`. -/
instance : NormedHypercomplex R (CayleyDickson A) where
  hcnorm a := hcnorm a.fst + hcnorm (star a.snd)
  hcnorm_mul a := by
    ext
    · simp only [add_smul, add_fst, smul_fst, one_fst', hcnorm_mul, mul_fst, star_fst,
        star_snd, star_star, star_neg, neg_mul, sub_neg_eq_add]
    · simp only [smul_snd, one_snd', smul_zero, mul_snd, star_fst, star_snd, star_star,
        neg_mul]
      abel
  hcnorm_mul' a := by
    ext
    · rw [smul_fst, one_fst', add_smul, hcnorm_mul' (R := R) a.fst,
        hcnorm_mul (R := R) (star a.snd)]
      simp only [mul_fst, star_fst, star_snd, star_star, mul_neg, sub_neg_eq_add]
    · rw [smul_snd, one_snd', smul_zero]
      simp only [mul_snd, star_fst, star_snd, neg_mul]
      abel
  hcnorm_nonneg a := add_nonneg (hcnorm_nonneg (R := R) a.fst) (hcnorm_nonneg (R := R) (star a.snd))
  hcnorm_eq_zero a := by
    intro h
    have hf := hcnorm_nonneg (R := R) a.fst
    have hs := hcnorm_nonneg (R := R) (star a.snd)
    have hfst : hcnorm (R := R) a.fst = 0 := by linarith
    have hsnd : hcnorm (R := R) (star a.snd) = 0 := by linarith
    have e1 : a.fst = 0 := hcnorm_eq_zero (R := R) _ hfst
    have e2 : star a.snd = 0 := hcnorm_eq_zero (R := R) _ hsnd
    have e2' : a.snd = 0 := by
      have := congrArg star e2; simpa using this
    exact (eq_zero_iff a).mpr ⟨e1, e2'⟩

end normed

/-! ### The one-sided inverse -/

/-- The hypercomplex inverse `a⁻¹ := ‖a‖⁻¹·star a`. -/
def hcinv (R : Type*) {A : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [NonAssocSemiring A] [Module R A] [Star A] [NormedHypercomplex R A] (a : A) : A :=
  (hcnorm (R := R) a)⁻¹ • star a

section inv
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [NonAssocRing A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NormedHypercomplex R A]

omit [IsScalarTower R A A] in
/-- Right inverse: `a · a⁻¹ = 1` for `a ≠ 0`. -/
lemma mul_hcinv_cancel (a : A) (ha : a ≠ 0) : a * hcinv R a = 1 := by
  have hnorm : hcnorm (R := R) a ≠ 0 := fun h => ha (hcnorm_eq_zero (R := R) a h)
  rw [hcinv, mul_smul_comm, ← hcnorm_mul (R := R) a, smul_smul,
    inv_mul_cancel₀ hnorm, one_smul]

omit [SMulCommClass R A A] in
/-- Left inverse: `a⁻¹ · a = 1` for `a ≠ 0`. -/
lemma hcinv_mul_cancel (a : A) (ha : a ≠ 0) : hcinv R a * a = 1 := by
  have hnorm : hcnorm (R := R) a ≠ 0 := fun h => ha (hcnorm_eq_zero (R := R) a h)
  rw [hcinv, smul_mul_assoc, ← hcnorm_mul' (R := R) a, smul_smul,
    inv_mul_cancel₀ hnorm, one_smul]

end inv

/-! ### The octonions are a two-sided division algebra -/

/-- The octonionic inverse, packaged as `⁻¹`. `𝕆` is non-associative, so this is
not a `DivisionRing`; the two-sided cancellation laws are recorded explicitly. -/
noncomputable instance : Inv 𝕆 := ⟨hcinv ℝ⟩

@[simp] lemma octonion_inv_def (a : 𝕆) : a⁻¹ = hcinv ℝ a := rfl

theorem octonion_mul_inv (a : 𝕆) (ha : a ≠ 0) : a * a⁻¹ = 1 := mul_hcinv_cancel a ha
theorem octonion_inv_mul (a : 𝕆) (ha : a ≠ 0) : a⁻¹ * a = 1 := hcinv_mul_cancel a ha

/-! ### Norm unfolding lemmas -/

section unfold
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [NonAssocRing A] [StarRing A] [Module R A] [NormedHypercomplex R A]

/-- One layer of the norm: `‖a‖ = ‖a.fst‖ + ‖(a.snd)*‖`. -/
lemma hcnorm_cd (a : CayleyDickson A) :
    hcnorm (R := R) a = hcnorm (R := R) a.fst + hcnorm (R := R) (star a.snd) := rfl

end unfold

/-- The base-case norm on `ℝ` is the square. -/
lemma hcnorm_real (r : ℝ) : hcnorm (R := ℝ) r = r ^ 2 := rfl

/-! ### The standard octonion basis `e₀ … e₇`

An element is `⟨⟨⟨a,b⟩,⟨c,d⟩⟩, ⟨⟨e,f⟩,⟨g,h⟩⟩⟩` with `a … h : ℝ`; `eₙ` is the unit
vector in slot `n`. -/

/-- `e₀ = 1`. -/
def e0 : 𝕆 := 1
/-- `e₁`. -/
def e1 : 𝕆 := ⟨⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
/-- `e₂`. -/
def e2 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨1, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
/-- `e₃`. -/
def e3 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 1⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
/-- `e₄`. -/
def e4 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨1, 0⟩, ⟨0, 0⟩⟩⟩
/-- `e₅`. -/
def e5 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 1⟩, ⟨0, 0⟩⟩⟩
/-- `e₆`. -/
def e6 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨1, 0⟩⟩⟩
/-- `e₇`. -/
def e7 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 1⟩⟩⟩

/-- The seven imaginary units, indexed by the Fano points `Fin 7` (`p ↦ e_{p+1}`). -/
def eImag : Fin 7 → 𝕆
  | 0 => e1
  | 1 => e2
  | 2 => e3
  | 3 => e4
  | 4 => e5
  | 5 => e6
  | 6 => e7

-- Make `ext` recurse through every doubling layer to the `ℝ` leaves.
attribute [local ext] CayleyDickson.ext

/-- Split to the eight real leaves, unfold the basis and multiplication, finish. -/
local macro "octonion_compute" : tactic =>
  `(tactic|
    (ext <;>
      simp only [e0, e1, e2, e3, e4, e5, e6, e7, mul_fst, mul_snd, star_fst, star_snd,
        star_trivial, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd, one_fst', one_snd',
        zero_fst, zero_snd] <;>
      ring))

/-! ### Unit and squares -/

theorem e0_mul (x : 𝕆) : e0 * x = x := by rw [e0, one_mul]
theorem mul_e0 (x : 𝕆) : x * e0 = x := by rw [e0, mul_one]

theorem e1_sq : e1 * e1 = -e0 := by octonion_compute
theorem e2_sq : e2 * e2 = -e0 := by octonion_compute
theorem e3_sq : e3 * e3 = -e0 := by octonion_compute
theorem e4_sq : e4 * e4 = -e0 := by octonion_compute
theorem e5_sq : e5 * e5 = -e0 := by octonion_compute
theorem e6_sq : e6 * e6 = -e0 := by octonion_compute
theorem e7_sq : e7 * e7 = -e0 := by octonion_compute

/-! ### The seven oriented Fano-line products -/

theorem e1_mul_e2 : e1 * e2 = e3 := by octonion_compute
theorem e1_mul_e4 : e1 * e4 = e5 := by octonion_compute
theorem e1_mul_e7 : e1 * e7 = e6 := by octonion_compute
theorem e2_mul_e4 : e2 * e4 = e6 := by octonion_compute
theorem e2_mul_e5 : e2 * e5 = e7 := by octonion_compute
theorem e3_mul_e4 : e3 * e4 = e7 := by octonion_compute
theorem e3_mul_e6 : e3 * e6 = e5 := by octonion_compute

/-- Sample anticommutativity: swapping factors reverses the sign. -/
theorem e2_mul_e1 : e2 * e1 = -e3 := by octonion_compute

/-! ### Alternativity, flexibility, norm multiplicativity -/

set_option maxHeartbeats 4000000 in
/-- **Left alternativity** `x·(x·y) = (x·x)·y`. -/
theorem octonion_mul_left_alt (x y : 𝕆) : x * (x * y) = (x * x) * y := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, neg_mul, mul_neg,
    sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd] <;> ring

set_option maxHeartbeats 4000000 in
/-- **Right alternativity** `(y·x)·x = y·(x·x)`. -/
theorem octonion_mul_right_alt (x y : 𝕆) : (y * x) * x = y * (x * x) := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, neg_mul, mul_neg,
    sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd] <;> ring

set_option maxHeartbeats 4000000 in
/-- **Flexibility** `(x·y)·x = x·(y·x)`. -/
theorem octonion_mul_flexible (x y : 𝕆) : (x * y) * x = x * (y * x) := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, neg_mul, mul_neg,
    sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd] <;> ring

set_option maxHeartbeats 8000000 in
/-- **Norm multiplicativity** `‖x·y‖ = ‖x‖·‖y‖` (the Degen eight-square identity);
this makes `𝕆` a composition algebra. -/
theorem octonion_hcnorm_mul (x y : 𝕆) :
    hcnorm (R := ℝ) (x * y) = hcnorm (R := ℝ) x * hcnorm (R := ℝ) y := by
  simp only [hcnorm_cd, hcnorm_real, mul_fst, mul_snd, star_fst, star_snd, star_trivial,
    neg_mul, mul_neg, sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd,
    sub_fst, sub_snd]
  ring

/-- **No zero divisors:** a product vanishes only if a factor does. -/
theorem octonion_eq_zero_or_eq_zero_of_mul_eq_zero (x y : 𝕆) (h : x * y = 0) :
    x = 0 ∨ y = 0 := by
  have hn : hcnorm (R := ℝ) x * hcnorm (R := ℝ) y = 0 := by
    rw [← octonion_hcnorm_mul, h]; simp [hcnorm_cd, hcnorm_real]
  rcases mul_eq_zero.mp hn with hx | hy
  · exact Or.inl (hcnorm_eq_zero (R := ℝ) x hx)
  · exact Or.inr (hcnorm_eq_zero (R := ℝ) y hy)

/-! ### Conjugation as an anti-automorphism -/

set_option maxHeartbeats 4000000 in
/-- **Conjugation reverses products:** `star (x·y) = star y · star x`. With norm
multiplicativity this is the second composition-algebra structure law — the star is a
norm-preserving anti-automorphism. -/
theorem octonion_star_mul (x y : 𝕆) : star (x * y) = star y * star x := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, star_star,
    neg_mul, mul_neg, sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd,
    sub_fst, sub_snd] <;> ring

set_option maxHeartbeats 4000000 in
/-- **Conjugation preserves the norm:** `‖star x‖ = ‖x‖`. -/
theorem octonion_hcnorm_star (x : 𝕆) :
    hcnorm (R := ℝ) (star x) = hcnorm (R := ℝ) x := by
  simp only [hcnorm_cd, hcnorm_real, star_fst, star_snd, star_trivial,
    neg_fst, neg_snd, neg_neg]
  ring

/-- **The conjugate is the inverse up to norm:** `star x = ‖x‖ · x⁻¹` for `x ≠ 0`
(so `⁻¹` is genuinely the normalized conjugation). -/
theorem octonion_star_eq_norm_smul_inv (x : 𝕆) (hx : x ≠ 0) :
    star x = hcnorm (R := ℝ) x • x⁻¹ := by
  have hnorm : hcnorm (R := ℝ) x ≠ 0 := fun h => hx (hcnorm_eq_zero (R := ℝ) x h)
  rw [octonion_inv_def, hcinv, smul_smul, mul_inv_cancel₀ hnorm, one_smul]

/-! ### The Moufang identities

The Moufang identities are the strongest associativity-like laws that survive in a
non-associative alternative algebra; they hold in `𝕆` (and fail at the sedenions). Each
is a degree-`4` identity over the eight real leaves, closed by `ring`. -/

set_option maxHeartbeats 16000000 in
/-- **Left Moufang identity** `z·(x·(z·y)) = ((z·x)·z)·y`. -/
theorem octonion_moufang_left (x y z : 𝕆) : z * (x * (z * y)) = ((z * x) * z) * y := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, neg_mul, mul_neg,
    sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd] <;> ring

set_option maxHeartbeats 16000000 in
/-- **Right Moufang identity** `x·(z·(y·z)) = ((x·z)·y)·z`. -/
theorem octonion_moufang_right (x y z : 𝕆) : x * (z * (y * z)) = ((x * z) * y) * z := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, neg_mul, mul_neg,
    sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd] <;> ring

set_option maxHeartbeats 16000000 in
/-- **Middle Moufang identity** `(z·x)·(y·z) = z·((x·y)·z)`. -/
theorem octonion_moufang_middle (x y z : 𝕆) : (z * x) * (y * z) = z * ((x * y) * z) := by
  ext <;> simp only [mul_fst, mul_snd, star_fst, star_snd, star_trivial, neg_mul, mul_neg,
    sub_neg_eq_add, neg_neg, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd] <;> ring

/-! ### Bridge to the Foundation Fano incidence -/

/-- Each of the seven Foundation lines is realized by an oriented product of the
corresponding imaginary units: the multiplication is supported exactly on the
abstractly-derived `PG(2,2)` incidence. -/
theorem cd_basis_realizes_fanoLine (L : Fin 7) :
    ∃ a b c : Fin 7,
      HqivSpine.Foundation.fanoLine L = {a, b, c} ∧ eImag a * eImag b = eImag c := by
  fin_cases L
  · exact ⟨0, 1, 2, by decide, e1_mul_e2⟩
  · exact ⟨0, 3, 4, by decide, e1_mul_e4⟩
  · exact ⟨0, 6, 5, by decide, e1_mul_e7⟩
  · exact ⟨1, 3, 5, by decide, e2_mul_e4⟩
  · exact ⟨1, 4, 6, by decide, e2_mul_e5⟩
  · exact ⟨2, 3, 6, by decide, e3_mul_e4⟩
  · exact ⟨2, 5, 4, by decide, e3_mul_e6⟩

/-- The three imaginary units on any Foundation line close multiplicatively
(collinear in the sense of `HqivSpine.Foundation.collinearImag`). -/
theorem cd_fano_product_collinear (L : Fin 7) :
    ∃ a b c : Fin 7,
      HqivSpine.Foundation.collinearImag a b c ∧ eImag a * eImag b = eImag c := by
  obtain ⟨a, b, c, hL, hprod⟩ := cd_basis_realizes_fanoLine L
  refine ⟨a, b, c, ⟨L, ?_, ?_, ?_⟩, hprod⟩ <;> rw [hL] <;> simp

end CayleyDickson

end HqivSpine.Algebra
