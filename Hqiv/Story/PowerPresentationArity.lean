import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# Power presentations, presentation arity, and twiddle period (Story)

The bare natural **`729 : ℕ`** does not remember whether you read it as **`3^6`** or **`9^3`**.
This module makes that distinction **typed**:

* `PowerTower p` is a small **abstract syntax tree** of iterated powers over a fixed base prime `p`.
* `evalTower` maps a presentation to its numeric value (`ℕ`).
* `presentationArity` assigns an **arity label** used for Fourier / twiddle bookkeeping.  It is
  **intentionally not** `ArithmeticFunction.Ω` on `evalTower`: two presentations of the same
  number can carry **different** arity labels.

The recursion rule is chosen so the canonical Story examples line up:

* `3^6` as a single atom → arity **`6 + 1 = 7`**,
* `(3^2)^3 = 9^3` as a nest → arity **`(2 + 1) + 3 - 2 = 4`**.

Finally we record the **twiddle period** **`2π / k`**, definitionally equal to **`4π / (2k)`**, and
a tiny **ordered-factor** API where **`swap`** preserves the product (commutative “same axis” hook).

## Factor lists: parity and “45°” reflection (commutative monoid facts)

For **`List ℕ`** interpreted as an **ordered factor list** (`List.prod`):

* **Every** list satisfies **`xs.prod = xs.reverse.prod`** (`list_nat_prod_eq_reverse_prod`): reversing
  the order is the list-level reflection; it never changes the product on `ℕ`.
* If the list has **even** length, **`swapAdjacentPairReflect`** swaps each adjacent pair
  `(a,b) ↦ (b,a)` down the list; the product is unchanged — this is the formal “reflect each pair
  across the commutative axis”.
* If the list has **odd** length and is nonempty, the same adjacent-pair reflection applies to the
  **tail** (even length), leaving the **head** as the unpaired factor: **`head * (reflect tail).prod`**
  still equals **`xs.prod`** (`odd_length_head_mul_swapTail_eq_prod`).

So the even/odd split is only about **how the reflection decomposes**; the underlying identity is
always **commutativity** / **reverse invariance** of the list product.

**Parity packaging:** `list_nat_prod_eq_reverse_prod` is the statement that holds for **every** factor
list; `swapAdjacentPairReflect_perm` + `swapAdjacentPairReflect_preserves_prod` give the **even**
adjacent-pair reflection; `odd_length_head_mul_swapTail_eq_prod` packages the **odd** case as
“reflect the even tail, keep the head” with the **same** product.
-/

namespace Hqiv.Story

/-- Iterated-power presentations over a fixed prime base `p`. -/
inductive PowerTower (p : ℕ) : Type
  /-- Outer shape `p^e` with `e > 0`. -/
  | atom (e : ℕ) (he : 0 < e) : PowerTower p
  /-- Outer shape `(innerVal)^e` with `e > 0`, where `innerVal` is itself a presentation. -/
  | nest (inner : PowerTower p) (e : ℕ) (he : 0 < e) : PowerTower p

namespace PowerTower

variable {p : ℕ}

/-- Denotation of a presentation as a natural power tower. -/
def evalTower (hp : Nat.Prime p) : PowerTower p → ℕ
  | atom e _ => p ^ e
  | nest inner e _ => evalTower hp inner ^ e

/--
Presentation-local arity slot (Story / twiddle axis index, **not** `Ω` on `evalTower`).

* `atom e`  ↦ `e + 1`
* `nest t e` ↦ `presentationArity t + e - 2`

This matches the user-stated anchors on `729 = 3^6 = 9^3` for the prime `p = 3`.
-/
def presentationArity : PowerTower p → ℕ
  | atom e _ => e + 1
  | nest inner e _ => presentationArity inner + e - 2

/-! ### Canonical `729` presentations (base `3`) -/

/-- `3^6` written as a single atom (`arity = 7`). -/
def threePowSix : PowerTower 3 :=
  atom 6 (by decide : 0 < 6)

/-- `(3^2)^3 = 9^3` written as a nest (`arity = 4`). -/
def nineCubedAsNest : PowerTower 3 :=
  nest (atom 2 (by decide : 0 < 2)) 3 (by decide : 0 < 3)

theorem evalTower_threePowSix :
    evalTower (by decide : Nat.Prime 3) threePowSix = 729 := by
  native_decide

theorem evalTower_nineCubedAsNest :
    evalTower (by decide : Nat.Prime 3) nineCubedAsNest = 729 := by
  native_decide

theorem presentationArity_threePowSix :
    presentationArity threePowSix = 7 := by
  rfl

theorem presentationArity_nineCubedAsNest :
    presentationArity nineCubedAsNest = 4 := by
  rfl

theorem same_eval_different_presentationArity :
    evalTower (by decide : Nat.Prime 3) threePowSix =
      evalTower (by decide : Nat.Prime 3) nineCubedAsNest ∧
      presentationArity threePowSix ≠ presentationArity nineCubedAsNest := by
  refine And.intro ?_ (by decide : (7 : ℕ) ≠ 4)
  native_decide

end PowerTower

/-! ## Fourier twiddle period: `2π/k` (= `4π/(2k)`) -/

/-- Fundamental twiddle period `2π / k` radians (Fourier `k`-fold periodicity). -/
noncomputable def twiddlePeriod (k : ℕ) (hk : 0 < k) : ℝ :=
  have _hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  2 * Real.pi / (k : ℝ)

theorem twiddlePeriod_eq_four_pi_div_two_mul (k : ℕ) (hk : 0 < k) :
    twiddlePeriod k hk = 4 * Real.pi / (2 * (k : ℝ)) := by
  unfold twiddlePeriod
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  field_simp [hk0]
  ring

/-! ## Ordered factors: swap stays on the same “axis” (same product) -/

/-- An **ordered** factor pair `(a,b)` for commutative multiplication stories. -/
structure OrderedFactor where
  /-- Left factor. -/
  a : ℕ
  /-- Right factor. -/
  b : ℕ

namespace OrderedFactor

/-- Product `a * b`. -/
def prod (f : OrderedFactor) : ℕ :=
  f.a * f.b

/-- Swap the two factors (same unordered information, reversed order). -/
def swap (f : OrderedFactor) : OrderedFactor :=
  ⟨f.b, f.a⟩

theorem swap_prod (f : OrderedFactor) : (swap f).prod = f.prod := by
  simp [prod, swap, mul_comm]

/-- Example on `729`: the split `243 * 3` versus its swap `3 * 243` (same product). -/
def factor243_times3 : OrderedFactor :=
  ⟨243, 3⟩

theorem factor243_times3_prod : factor243_times3.prod = 729 := by
  native_decide

theorem swap_factor243_times3_prod :
    (swap factor243_times3).prod = 729 := by
  rw [swap_prod, factor243_times3_prod]

/-- Another symmetric split: `27 * 27`. -/
def factor27_times27 : OrderedFactor :=
  ⟨27, 27⟩

theorem factor27_times27_prod : factor27_times27.prod = 729 := by
  native_decide

end OrderedFactor

/-! ## Lists of factors: even vs odd length, same commutative reflection facts -/

namespace FactorListReflection

open List

/-- Reflect each adjacent pair `(a,b) ↦ (b,a)`; only defined when the list has even length. -/
def swapAdjacentPairReflect : (xs : List ℕ) → xs.length % 2 = 0 → List ℕ
  | [], _ => []
  | [_], h => False.elim (by simp at h)
  | x :: y :: ys, h =>
      have ht : ys.length % 2 = 0 := by
        cases ys <;> simp [Nat.add_mod] at h ⊢ <;> omega
      y :: x :: swapAdjacentPairReflect ys ht

/-- Reversing an ordered factor list does not change its product (`ℕ` is commutative). -/
theorem list_nat_prod_eq_reverse_prod (xs : List ℕ) : xs.prod = xs.reverse.prod :=
  (List.prod_reverse xs).symm

theorem swapAdjacentPairReflect_perm (xs : List ℕ) (h : xs.length % 2 = 0) :
    swapAdjacentPairReflect xs h ~ xs := by
  cases xs with
  | nil => rfl
  | cons x xs' =>
    cases xs' with
    | nil =>
      simp [List.length] at h
    | cons y ys =>
      have ht : ys.length % 2 = 0 := by
        cases ys <;> simp [Nat.add_mod] at h ⊢ <;> omega
      have hop :
          swapAdjacentPairReflect (x :: y :: ys) h ~ y :: x :: ys := by
        simpa [swapAdjacentPairReflect, ht] using Perm.cons y (Perm.cons x (swapAdjacentPairReflect_perm ys ht))
      exact Perm.trans hop (Perm.swap y x ys).symm

theorem swapAdjacentPairReflect_preserves_prod (xs : List ℕ) (h : xs.length % 2 = 0) :
    (swapAdjacentPairReflect xs h).prod = xs.prod :=
  Perm.prod_eq (swapAdjacentPairReflect_perm xs h)

theorem odd_length_tail_even (xs : List ℕ) (h : xs.length % 2 = 1) (hxs : xs ≠ []) :
    xs.tail.length % 2 = 0 := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons x tl =>
    simp [List.length_cons] at h ⊢
    omega

/--
Odd-length nonempty list: reflect adjacent pairs in the **even-length tail**; the **head** is the
unpaired factor.  The product is unchanged — same commutative mechanism as the even case.
-/
theorem odd_length_head_mul_swapTail_eq_prod (xs : List ℕ) (h : xs.length % 2 = 1) (hxs : xs ≠ []) :
    xs.head hxs *
        (swapAdjacentPairReflect xs.tail (odd_length_tail_even xs h hxs)).prod =
      xs.prod := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons x tl =>
    have htl := odd_length_tail_even (x :: tl) h hxs
    simp [List.prod_cons, swapAdjacentPairReflect_preserves_prod tl htl]

end FactorListReflection

end Hqiv.Story
