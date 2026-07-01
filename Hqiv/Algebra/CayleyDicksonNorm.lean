/-
  HQIV Algebra: the hypercomplex norm and the one-sided inverse on 𝕆
  ==================================================================

  Follow-up to `Hqiv.Algebra.CayleyDickson`. We equip the Cayley–Dickson tower
  with a real-valued "hypercomplex norm" satisfying `‖a‖ · 1 = a · star a`, and
  use it to produce a multiplicative inverse `a⁻¹ := ‖a‖⁻¹ · star a` for every
  nonzero element. Specialized to `𝕆 = CayleyDickson³ ℝ`, this exhibits the
  octonions as a (right) division algebra.

  **Attribution.** As with the base module, the norm/inverse construction follows
  the octonions formalization of Filippo A. E. Nuccio and Matthieu Piquerez
  (https://plmlab.math.cnrs.fr/nuccio/octonions, Apache-2.0), re-derived against
  the current toolchain. In particular `LinearOrderedField` (used there) is now
  spelled `[Field R] [LinearOrder R] [IsStrictOrderedRing R]`.

  No `sorry`, no new `axiom`, no `native_decide`.
-/

import Hqiv.Algebra.CayleyDickson

namespace Hqiv.Algebra

namespace CayleyDickson

variable {R : Type*} {A : Type*}

/-! ### Scalar-tower / commutativity / star-linearity compatibility

These instances thread the compatibility classes through one Cayley–Dickson
doubling, so that the whole tower `𝕆 = CayleyDickson³ ℝ` acquires them by
instance resolution from the `ℝ` base case. -/

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

/-- A real-valued "hypercomplex norm" on `A`: a quadratic form realizing
`‖a‖ · 1 = a · star a`, nonnegative and definite. This is exactly what is needed
to write down the inverse `a⁻¹ = ‖a‖⁻¹ · star a`. -/
class NormedHypercomplex (R : Type*) (A : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [NonAssocSemiring A] [Module R A] [Star A] where
  hcnorm : A → R
  hcnorm_mul : ∀ a, hcnorm a • (1 : A) = a * star a
  /-- Conjugate-side norm identity. This is *not* free from `hcnorm_mul` because
  `a * star a` and `star a * a` differ in a non-commutative algebra; it holds
  recursively along the Cayley–Dickson tower and is exactly what is needed for
  the *left* inverse. -/
  hcnorm_mul' : ∀ a, hcnorm a • (1 : A) = star a * a
  hcnorm_nonneg : ∀ a, 0 ≤ hcnorm a
  hcnorm_eq_zero : ∀ a, hcnorm a = 0 → a = 0

export NormedHypercomplex (hcnorm hcnorm_mul hcnorm_mul' hcnorm_nonneg hcnorm_eq_zero)

/-- ℝ carries the square norm `a ↦ a²`. -/
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

/-- The Cayley–Dickson doubling of a hypercomplex norm:
`‖(a, b)‖ = ‖a‖ + ‖b*‖`. -/
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
      have := congrArg star e2
      simpa using this
    exact (eq_zero_iff a).mpr ⟨e1, e2'⟩

end normed

/-! ### The one-sided inverse -/

/-- The hypercomplex inverse `a⁻¹ := ‖a‖⁻¹ · star a`. -/
def hcinv (R : Type*) {A : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [NonAssocSemiring A] [Module R A] [Star A] [NormedHypercomplex R A] (a : A) : A :=
  (hcnorm (R := R) a)⁻¹ • star a

section inv
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [NonAssocRing A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NormedHypercomplex R A]

omit [IsScalarTower R A A] in
/-- Every nonzero element has a right inverse: `a · a⁻¹ = 1`. -/
lemma mul_hcinv_cancel (a : A) (ha : a ≠ 0) : a * hcinv R a = 1 := by
  have hnorm : hcnorm (R := R) a ≠ 0 := fun h => ha (hcnorm_eq_zero (R := R) a h)
  rw [hcinv, mul_smul_comm, ← hcnorm_mul (R := R) a, smul_smul,
    inv_mul_cancel₀ hnorm, one_smul]

omit [SMulCommClass R A A] in
/-- Every nonzero element has a left inverse: `a⁻¹ · a = 1`. Uses the
conjugate-side norm identity `star a · a = ‖a‖·1`. -/
lemma hcinv_mul_cancel (a : A) (ha : a ≠ 0) : hcinv R a * a = 1 := by
  have hnorm : hcnorm (R := R) a ≠ 0 := fun h => ha (hcnorm_eq_zero (R := R) a h)
  rw [hcinv, smul_mul_assoc, ← hcnorm_mul' (R := R) a, smul_smul,
    inv_mul_cancel₀ hnorm, one_smul]

end inv

/-! ### The octonions are a (two-sided) division algebra -/

/-- Every nonzero octonion has a right inverse, with inverse `a⁻¹ = ‖a‖⁻¹ · star a`. -/
theorem octonion_mul_hcinv_cancel (a : 𝕆) (ha : a ≠ 0) : a * hcinv ℝ a = 1 :=
  mul_hcinv_cancel a ha

/-- Every nonzero octonion has a matching left inverse. -/
theorem octonion_hcinv_mul_cancel (a : 𝕆) (ha : a ≠ 0) : hcinv ℝ a * a = 1 :=
  hcinv_mul_cancel a ha

/-- The octonionic inverse `a⁻¹ := ‖a‖⁻¹ · star a`, packaged as the `⁻¹` operation.
`𝕆` is non-associative, so this is *not* a `DivisionRing`/`GroupWithZero`; the
two-sided cancellation laws are recorded explicitly below. -/
noncomputable instance : Inv 𝕆 := ⟨hcinv ℝ⟩

@[simp] lemma octonion_inv_def (a : 𝕆) : a⁻¹ = hcinv ℝ a := rfl

/-- `a · a⁻¹ = 1` for nonzero `a : 𝕆`. -/
theorem octonion_mul_inv (a : 𝕆) (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  mul_hcinv_cancel a ha

/-- `a⁻¹ · a = 1` for nonzero `a : 𝕆`. -/
theorem octonion_inv_mul (a : 𝕆) (ha : a ≠ 0) : a⁻¹ * a = 1 :=
  hcinv_mul_cancel a ha

end CayleyDickson

end Hqiv.Algebra
