import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# `HqivSpine.Algebra.CayleyDickson` — the octonions by doubling

A typeclass-based (not matrix-based) construction of the octonions, obtained by
iterating the Cayley–Dickson doubling three times over `ℝ`:

`𝕆 := CayleyDickson (CayleyDickson (CayleyDickson ℝ))`.

We get an honest algebraic object — `AddCommGroup`, non-associative `NonAssocRing`,
`StarRing` anti-homomorphism, `ℝ`-module — all by instance resolution, and prove
the dimension ladder `1, 2, 4, 8` as a real vector-space dimension theorem.

**Attribution.** The construction follows the octonion formalization of
Filippo A. E. Nuccio and Matthieu Piquerez
(https://plmlab.math.cnrs.fr/nuccio/octonions, Apache-2.0), re-derived against the
current Mathlib toolchain using `StarRing`.

No `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Algebra

/-- **The Cayley–Dickson double of `A`.** An element `(fst, snd)` is read as
`fst + snd · ℓ` for a new imaginary unit `ℓ`. -/
@[ext]
structure CayleyDickson (A : Type*) where
  fst : A
  snd : A

namespace CayleyDickson

variable {R : Type*} {A : Type*}

/-! ### Additive group (componentwise) -/

section addgroup
variable [AddCommGroup A]

instance : Zero (CayleyDickson A) := ⟨⟨0, 0⟩⟩
instance : Add (CayleyDickson A) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (CayleyDickson A) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance : Sub (CayleyDickson A) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance : SMul ℕ (CayleyDickson A) := ⟨fun n x => ⟨n • x.fst, n • x.snd⟩⟩
instance : SMul ℤ (CayleyDickson A) := ⟨fun n x => ⟨n • x.fst, n • x.snd⟩⟩

/-- Forgetful map to the underlying pair, an additive isomorphism. -/
def toProd (x : CayleyDickson A) : A × A := (x.fst, x.snd)

omit [AddCommGroup A] in
lemma toProd_injective : Function.Injective (toProd : CayleyDickson A → A × A) := by
  intro x y h
  ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

instance : AddCommGroup (CayleyDickson A) :=
  toProd_injective.addCommGroup toProd rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] lemma zero_fst : (0 : CayleyDickson A).fst = 0 := rfl
@[simp] lemma zero_snd : (0 : CayleyDickson A).snd = 0 := rfl
@[simp] lemma add_fst (a b : CayleyDickson A) : (a + b).fst = a.fst + b.fst := rfl
@[simp] lemma add_snd (a b : CayleyDickson A) : (a + b).snd = a.snd + b.snd := rfl
@[simp] lemma neg_fst (a : CayleyDickson A) : (-a).fst = -a.fst := rfl
@[simp] lemma neg_snd (a : CayleyDickson A) : (-a).snd = -a.snd := rfl
@[simp] lemma sub_fst (a b : CayleyDickson A) : (a - b).fst = a.fst - b.fst := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_fst, neg_fst]
@[simp] lemma sub_snd (a b : CayleyDickson A) : (a - b).snd = a.snd - b.snd := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_snd, neg_snd]

@[simp] lemma eq_zero_iff (a : CayleyDickson A) : a = 0 ↔ a.fst = 0 ∧ a.snd = 0 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h; ext; exacts [h.1, h.2]

end addgroup

/-! ### Multiplication and the non-associative ring structure -/

section mul
variable [NonUnitalNonAssocRing A] [StarRing A]

/-- Cayley–Dickson multiplication `(a, b)(c, d) = (a c − d* b,  d a + b c*)`. -/
def mul (x y : CayleyDickson A) : CayleyDickson A :=
  ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩

@[simp] lemma mul_def_fst (x y : CayleyDickson A) :
    (mul x y).fst = x.fst * y.fst - star y.snd * x.snd := rfl
@[simp] lemma mul_def_snd (x y : CayleyDickson A) :
    (mul x y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

lemma mul_left_distrib (a b c : CayleyDickson A) : mul a (b + c) = mul a b + mul a c := by
  ext
  · simp only [mul_def_fst, add_fst, add_snd, mul_add, star_add, add_mul, sub_add_eq_sub_sub]
    abel
  · simp only [mul_def_snd, add_fst, add_snd, add_mul, mul_add, star_add]
    abel

lemma mul_right_distrib (a b c : CayleyDickson A) : mul (a + b) c = mul a c + mul b c := by
  ext
  · simp only [mul_def_fst, add_fst, add_snd, add_mul, mul_add, sub_add_eq_sub_sub]
    abel
  · simp only [mul_def_snd, add_fst, add_snd, mul_add, add_mul]
    abel

@[simp] lemma mul_zero' (a : CayleyDickson A) : mul a 0 = 0 := by
  ext <;> simp [mul_def_fst, mul_def_snd]

@[simp] lemma zero_mul' (a : CayleyDickson A) : mul 0 a = 0 := by
  ext <;> simp [mul_def_fst, mul_def_snd]

instance : NonUnitalNonAssocRing (CayleyDickson A) where
  mul := mul
  left_distrib := mul_left_distrib
  right_distrib := mul_right_distrib
  zero_mul := zero_mul'
  mul_zero := mul_zero'

@[simp] lemma mul_fst (a b : CayleyDickson A) :
    (a * b).fst = a.fst * b.fst - star b.snd * a.snd := rfl
@[simp] lemma mul_snd (a b : CayleyDickson A) :
    (a * b).snd = b.snd * a.fst + a.snd * star b.fst := rfl

/-! ### Star (conjugation), bundled as a single `StarRing` -/

/-- Cayley–Dickson conjugation `(a, b)* = (a*, -b)`. -/
def starCD (a : CayleyDickson A) : CayleyDickson A := ⟨star a.fst, -a.snd⟩

@[simp] lemma starCD_fst (a : CayleyDickson A) : (starCD a).fst = star a.fst := rfl
@[simp] lemma starCD_snd (a : CayleyDickson A) : (starCD a).snd = -a.snd := rfl

lemma starCD_involutive (a : CayleyDickson A) : starCD (starCD a) = a := by
  ext
  · apply star_star
  · simp

lemma starCD_add (a b : CayleyDickson A) : starCD (a + b) = starCD a + starCD b := by
  ext
  · apply star_add
  · simp; abel

lemma starCD_mul (a b : CayleyDickson A) : starCD (a * b) = starCD b * starCD a := by
  ext
  · simp only [starCD_fst, starCD_snd, mul_fst, star_sub, star_mul, star_star,
      star_neg, neg_mul, mul_neg, neg_neg]
  · simp only [starCD_fst, starCD_snd, mul_snd, star_star, neg_mul, neg_add]
    abel

instance : StarRing (CayleyDickson A) where
  star := starCD
  star_involutive := starCD_involutive
  star_add := starCD_add
  star_mul := starCD_mul

@[simp] lemma star_fst (a : CayleyDickson A) : (star a).fst = star a.fst := rfl
@[simp] lemma star_snd (a : CayleyDickson A) : (star a).snd = -a.snd := rfl

end mul

/-! ### `R`-module (componentwise) -/

section module
variable [Semiring R] [AddCommGroup A] [Module R A]

instance : Module R (CayleyDickson A) where
  smul r a := ⟨r • a.fst, r • a.snd⟩
  one_smul a := by ext <;> apply one_smul
  mul_smul r s a := by ext <;> apply mul_smul
  smul_zero r := by ext <;> apply smul_zero
  smul_add r a b := by ext <;> apply smul_add
  add_smul r s a := by ext <;> apply add_smul
  zero_smul a := by ext <;> apply zero_smul

@[simp] lemma smul_fst (r : R) (a : CayleyDickson A) : (r • a).fst = r • a.fst := rfl
@[simp] lemma smul_snd (r : R) (a : CayleyDickson A) : (r • a).snd = r • a.snd := rfl

/-- The componentwise linear equivalence `CayleyDickson A ≃ₗ[R] A × A`. The clean
handle that makes the doubling visible to dimension theory. -/
def equivProd : CayleyDickson A ≃ₗ[R] A × A where
  toFun x := (x.fst, x.snd)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end module

/-! ### Finite-dimensional doubling -/

section findim
variable {R : Type*} {A : Type*} [Field R] [AddCommGroup A] [Module R A]

instance instFiniteDimensional [FiniteDimensional R A] :
    FiniteDimensional R (CayleyDickson A) :=
  Module.Finite.equiv (equivProd (R := R) (A := A)).symm

/-- **Dimension doubling:** `dim (CayleyDickson A) = 2 · dim A`. -/
theorem finrank_cayleyDickson [FiniteDimensional R A] :
    Module.finrank R (CayleyDickson A) = 2 * Module.finrank R A := by
  rw [(equivProd (R := R) (A := A)).finrank_eq, Module.finrank_prod]; ring

end findim

/-! ### Unital structure -/

section unital
variable [NonAssocRing A] [StarRing A]

/-- The unit `(1, 0)`. -/
def one : CayleyDickson A := ⟨1, 0⟩

omit [StarRing A] in
@[simp] lemma one_fst : (one : CayleyDickson A).fst = 1 := rfl
omit [StarRing A] in
@[simp] lemma one_snd : (one : CayleyDickson A).snd = 0 := rfl

lemma one_mul' (a : CayleyDickson A) : mul one a = a := by
  ext <;> simp [mul_def_fst, mul_def_snd, one]

lemma mul_one' (a : CayleyDickson A) : mul a one = a := by
  ext
  · simp only [mul_def_fst, one_fst, one_snd, star_zero, zero_mul, mul_one, sub_zero]
  · simp only [mul_def_snd, one_fst, one_snd, star_one, zero_mul, mul_one, zero_add]

instance : NonAssocRing (CayleyDickson A) where
  one := one
  one_mul := one_mul'
  mul_one := mul_one'

@[simp] lemma one_fst' : (1 : CayleyDickson A).fst = 1 := rfl
@[simp] lemma one_snd' : (1 : CayleyDickson A).snd = 0 := rfl

end unital

end CayleyDickson

/-! ## The octonions `𝕆` -/

namespace CayleyDickson

/-- The octonions, as the third Cayley–Dickson double of `ℝ`. -/
abbrev Octonion : Type := CayleyDickson (CayleyDickson (CayleyDickson ℝ))

@[inherit_doc] notation "𝕆" => Octonion

-- The full real octonion algebra is available purely by instance resolution.
example : AddCommGroup 𝕆 := inferInstance
example : NonAssocRing 𝕆 := inferInstance
example : StarMul 𝕆 := inferInstance
noncomputable example : Module ℝ 𝕆 := inferInstance
example : FiniteDimensional ℝ 𝕆 := inferInstance

/-- **The octonions have real dimension 8.** Three doublings over `ℝ` give
`dim ℝ 𝕆 = 2·2·2·1 = 8`, matching the carrier multiplicity forced by 3D growth
(`HqivSpine.Foundation.carrierMultiplicity = 8`). -/
theorem finrank_real_octonion : Module.finrank ℝ 𝕆 = 8 := by
  show Module.finrank ℝ (CayleyDickson (CayleyDickson (CayleyDickson ℝ))) = 8
  rw [finrank_cayleyDickson, finrank_cayleyDickson, finrank_cayleyDickson, Module.finrank_self]

end CayleyDickson

end HqivSpine.Algebra
