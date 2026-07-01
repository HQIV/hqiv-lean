import Hqiv.Algebra.CliffordCl06SixSpinorGammaMatInt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Spinor monomial Gram matrix (`W`) over `ℤ` — *genuinely* the identity

For each bitmask `m : Fin 64`, `spinorGammaMonomialMatZ m` is the ordered `γ` product in the
integral Kronecker model (`CliffordCl06SixSpinorGammaMatInt`).  The **normalized Frobenius**
pairing is the `64 × 64` integer matrix
`Wᵢⱼ := (1/8) * ∑_{a,b : Fin 8} (Mᵢ)ₐᵦ * (Mⱼ)ₐᵦ`.

## Closed form: `W = I₆₄`

The 64 γ-monomials are `8×8` signed permutation matrices built as triple Kronecker products of
the `2×2` matrices `{I, X, Z, A}`.  They are therefore **Frobenius-orthonormal up to the factor
`8`**, i.e. `spinorMonomialGramFrobSum i j = 8 · δᵢⱼ` and `W = I`.  We prove this *here, in Lean*,
via the Kronecker **mixed-product property**: the `8×8` Frobenius pairing of two `Kron3` matrices
factorizes into the product of three `2×2` Frobenius pairings, collapsing the heavy `8×8`
computation to a cheap `2×2` one.

This replaces the previous external-script axioms (`eight_dvd_…` divisibility and the `ZMod 101`
determinant certificate): both are now *theorems*, and the **entire chain is axiom-clean**
(`propext`/`Classical.choice`/`Quot.sound`, no `native_decide`).  The structural reduction
(`spinorKron3Z_mul`, `…_eq_kron`, `…_eq_frob2_prod`) collapses the `8×8` problem to a `2×2` one;
the residual finite check (`frob2_prod_monoSlot'`) is closed by plain kernel `decide` after
`maskFinset_sort_eq` rewrites the `Finset.sort` to a kernel-reducible `List.finRange` filter (so
the kernel can actually evaluate the `64 × 64` table — `decide` introduces no trust axioms,
unlike `native_decide`).
-/

namespace Hqiv.Algebra

open scoped BigOperators

open Matrix Finset

/-- Frobenius inner-product sum `∑_{a,b} (Mᵢ)ₐᵦ (Mⱼ)ₐᵦ` over `ℤ` (without the `1/8` normalization). -/
def spinorMonomialGramFrobSum (i j : Fin 64) : ℤ :=
  ∑ a : Fin 8, ∑ b : Fin 8, spinorGammaMonomialMatZ i a b * spinorGammaMonomialMatZ j a b

/-! ## Kronecker mixed-product reduction (`8×8 → 2×2`) -/

/-- A sum over `Fin 8` of a product split along the `2×2×2` digit decomposition
factorizes into the product of the three `Fin 2` sums. -/
lemma sum_fin8_factor (f g h : Fin 2 → ℤ) :
    ∑ k : Fin 8, f (fin8Lo k) * g (fin8Mid k) * h (fin8Hi k)
      = (∑ x, f x) * (∑ y, g y) * (∑ z, h z) := by
  simp only [Fin.sum_univ_eight, Fin.sum_univ_two]
  norm_num [fin8Lo, fin8Mid, fin8Hi]
  ring

/-- Double-sum version: a `Fin 8 × Fin 8` Frobenius-style sum whose summand splits
along the `2×2×2` digit decomposition factorizes into three `Fin 2 × Fin 2` sums. -/
lemma sum_fin8_sq_factor (f g h : Fin 2 → Fin 2 → ℤ) :
    (∑ a : Fin 8, ∑ b : Fin 8,
        f (fin8Lo a) (fin8Lo b) * g (fin8Mid a) (fin8Mid b) * h (fin8Hi a) (fin8Hi b))
      = (∑ x, ∑ y, f x y) * (∑ x, ∑ y, g x y) * (∑ x, ∑ y, h x y) := by
  simp only [Fin.sum_univ_eight, Fin.sum_univ_two]
  norm_num [fin8Lo, fin8Mid, fin8Hi]
  ring

/-- Kronecker mixed-product property for the triple `2⊗2⊗2` layout over `ℤ`. -/
lemma spinorKron3Z_mul (A B C A' B' C' : Matrix (Fin 2) (Fin 2) ℤ) :
    spinorKron3Z A B C * spinorKron3Z A' B' C'
      = spinorKron3Z (A * A') (B * B') (C * C') := by
  ext i j
  simp only [spinorKron3Z, Matrix.mul_apply, Fin.sum_univ_eight, Fin.sum_univ_two]
  norm_num [fin8Lo, fin8Mid, fin8Hi]
  ring

/-- `Kron3 1 1 1` is the `8×8` identity. -/
lemma spinorKron3Z_one : spinorKron3Z 1 1 1 = (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  ext i j
  simp only [spinorKron3Z, Matrix.one_apply, fin8Lo, fin8Mid, fin8Hi]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    have : ¬ (i.val % 2 = j.val % 2 ∧ i.val / 2 % 2 = j.val / 2 % 2 ∧ i.val / 4 = j.val / 4) := by
      rintro ⟨h1, h2, h3⟩
      exact h (Fin.ext (by omega))
    simp only [Fin.mk.injEq]
    rcases not_and_or.mp this with h1 | hrest
    · rw [if_neg h1]; ring
    · rcases not_and_or.mp hrest with h2 | h3
      · rw [if_neg h2]; ring
      · rw [if_neg h3]; ring

/-! ### Per-slot `2×2` factors of the six γ matrices -/

/-- Slot-0 (`lo`) `2×2` factor of `γ k`. -/
def gslot0 : Fin 6 → Matrix (Fin 2) (Fin 2) ℤ
  | ⟨0, _⟩ => spinorAZ  | ⟨1, _⟩ => spinorAZ  | ⟨2, _⟩ => spinorAZ
  | ⟨3, _⟩ => spinorIxZ | ⟨4, _⟩ => spinorIxZ | ⟨5, _⟩ => spinorXZ

/-- Slot-1 (`mid`) `2×2` factor of `γ k`. -/
def gslot1 : Fin 6 → Matrix (Fin 2) (Fin 2) ℤ
  | ⟨0, _⟩ => spinorIxZ | ⟨1, _⟩ => spinorIxZ | ⟨2, _⟩ => spinorAZ
  | ⟨3, _⟩ => spinorXZ  | ⟨4, _⟩ => spinorZZ  | ⟨5, _⟩ => spinorAZ

/-- Slot-2 (`hi`) `2×2` factor of `γ k`. -/
def gslot2 : Fin 6 → Matrix (Fin 2) (Fin 2) ℤ
  | ⟨0, _⟩ => spinorXZ | ⟨1, _⟩ => spinorZZ | ⟨2, _⟩ => spinorAZ
  | ⟨3, _⟩ => spinorAZ | ⟨4, _⟩ => spinorAZ | ⟨5, _⟩ => spinorIxZ

/-- Each γ matrix is the `Kron3` of its three slot factors (definitional). -/
lemma cl06SpinorGammaMatZ_eq_kron (k : Fin 6) :
    cl06SpinorGammaMatZ k = spinorKron3Z (gslot0 k) (gslot1 k) (gslot2 k) := by
  fin_cases k <;> rfl

/-! ### Slotwise factorization of γ-monomials -/

/-- Folding the γ product over a list of indices equals the `Kron3` of the three
slotwise `2×2` products — the central structural step. -/
lemma foldl_gamma_eq_kron (L : List (Fin 6)) :
    ∀ P Q R : Matrix (Fin 2) (Fin 2) ℤ,
      L.foldl (fun A i => A * cl06SpinorGammaMatZ i) (spinorKron3Z P Q R)
        = spinorKron3Z (L.foldl (fun A i => A * gslot0 i) P)
                       (L.foldl (fun A i => A * gslot1 i) Q)
                       (L.foldl (fun A i => A * gslot2 i) R) := by
  induction L with
  | nil => intro P Q R; rfl
  | cons a L ih =>
    intro P Q R
    simp only [List.foldl_cons]
    rw [cl06SpinorGammaMatZ_eq_kron, spinorKron3Z_mul]
    exact ih _ _ _

/-- Slot-0 `2×2` product over the (sorted) bitmask of `m`. -/
def monoSlot0 (m : Fin 64) : Matrix (Fin 2) (Fin 2) ℤ :=
  ((cl06SpinorGammaMaskFinset m).sort (· ≤ ·)).foldl (fun A i => A * gslot0 i) 1

/-- Slot-1 `2×2` product over the (sorted) bitmask of `m`. -/
def monoSlot1 (m : Fin 64) : Matrix (Fin 2) (Fin 2) ℤ :=
  ((cl06SpinorGammaMaskFinset m).sort (· ≤ ·)).foldl (fun A i => A * gslot1 i) 1

/-- Slot-2 `2×2` product over the (sorted) bitmask of `m`. -/
def monoSlot2 (m : Fin 64) : Matrix (Fin 2) (Fin 2) ℤ :=
  ((cl06SpinorGammaMaskFinset m).sort (· ≤ ·)).foldl (fun A i => A * gslot2 i) 1

/-- Every γ-monomial is the `Kron3` of its three slotwise `2×2` products. -/
lemma spinorGammaMonomialMatZ_eq_kron (m : Fin 64) :
    spinorGammaMonomialMatZ m
      = spinorKron3Z (monoSlot0 m) (monoSlot1 m) (monoSlot2 m) := by
  rw [spinorGammaMonomialMatZ, monoSlot0, monoSlot1, monoSlot2, ← spinorKron3Z_one,
    foldl_gamma_eq_kron]

/-! ### Frobenius pairing factorizes into three `2×2` pairings -/

/-- `2×2` Frobenius inner product `∑_{x,y} P x y · Q x y`. -/
def frob2 (P Q : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := ∑ x, ∑ y, P x y * Q x y

/-- The `8×8` Frobenius pairing of two γ-monomials factorizes into the product of the
three slotwise `2×2` Frobenius pairings. -/
lemma spinorMonomialGramFrobSum_eq_frob2_prod (i j : Fin 64) :
    spinorMonomialGramFrobSum i j
      = frob2 (monoSlot0 i) (monoSlot0 j) * frob2 (monoSlot1 i) (monoSlot1 j)
          * frob2 (monoSlot2 i) (monoSlot2 j) := by
  rw [spinorMonomialGramFrobSum, frob2, frob2, frob2, ← sum_fin8_sq_factor]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp only [spinorGammaMonomialMatZ_eq_kron, spinorKron3Z]
  ring

/-! ### Kernel-reducible reformulation (eliminates `Finset.sort`, enabling plain `decide`)

`decide` cannot reduce `Finset.sort`/`Finset.filter` (they are `Multiset = Quotient`-based).  We
therefore rewrite the sorted bitmask to a `List.finRange` filter, which the kernel *can* evaluate,
and run the residual `64 × 64` check by plain `decide` (no `native_decide`, no trust axiom). -/

/-- The sorted bitmask as a kernel-reducible `List.finRange` filter. -/
def monomialMaskList (m : Fin 64) : List (Fin 6) :=
  (List.finRange 6).filter (fun k => (m.val >>> k.val) % 2 == 1)

/-- The `Finset.sort` of the γ-mask equals the kernel-reducible `List.finRange` filter. -/
lemma maskFinset_sort_eq (m : Fin 64) :
    (cl06SpinorGammaMaskFinset m).sort (· ≤ ·) = monomialMaskList m := by
  refine (Finset.sortedLT_sort _).eq_of_mem_iff
    (List.Pairwise.sortedLT
      (List.Pairwise.filter _ (List.sortedLT_finRange 6).pairwise)) ?_
  intro a
  simp only [Finset.mem_sort, cl06SpinorGammaMaskFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, monomialMaskList, List.mem_filter, List.mem_finRange, beq_iff_eq]

/-- Slot-0 product over the kernel-reducible mask list (`= monoSlot0`). -/
def monoSlot0' (m : Fin 64) : Matrix (Fin 2) (Fin 2) ℤ :=
  (monomialMaskList m).foldl (fun A i => A * gslot0 i) 1

/-- Slot-1 product over the kernel-reducible mask list (`= monoSlot1`). -/
def monoSlot1' (m : Fin 64) : Matrix (Fin 2) (Fin 2) ℤ :=
  (monomialMaskList m).foldl (fun A i => A * gslot1 i) 1

/-- Slot-2 product over the kernel-reducible mask list (`= monoSlot2`). -/
def monoSlot2' (m : Fin 64) : Matrix (Fin 2) (Fin 2) ℤ :=
  (monomialMaskList m).foldl (fun A i => A * gslot2 i) 1

lemma monoSlot0_eq' (m : Fin 64) : monoSlot0 m = monoSlot0' m := by
  rw [monoSlot0, monoSlot0', maskFinset_sort_eq]

lemma monoSlot1_eq' (m : Fin 64) : monoSlot1 m = monoSlot1' m := by
  rw [monoSlot1, monoSlot1', maskFinset_sort_eq]

lemma monoSlot2_eq' (m : Fin 64) : monoSlot2 m = monoSlot2' m := by
  rw [monoSlot2, monoSlot2', maskFinset_sort_eq]

set_option maxHeartbeats 4000000 in
/-- The reduced `2×2` orthonormality identity over all `64 × 64` mask pairs, in the
kernel-reducible form — closed by plain `decide` (no trust axioms).

Each factor is a tiny `2×2` Frobenius pairing of products of `{I, X, Z, A}`; the `8×8` form was
intractable, but this `2×2` form is kernel-decidable. -/
lemma frob2_prod_monoSlot' (i j : Fin 64) :
    frob2 (monoSlot0' i) (monoSlot0' j) * frob2 (monoSlot1' i) (monoSlot1' j)
        * frob2 (monoSlot2' i) (monoSlot2' j) = 8 * (if i = j then 1 else 0) := by
  revert i j
  decide

/-- The reduced `2×2` orthonormality identity over all `64 × 64` mask pairs. -/
lemma frob2_prod_spinorMonomialGram (i j : Fin 64) :
    frob2 (monoSlot0 i) (monoSlot0 j) * frob2 (monoSlot1 i) (monoSlot1 j)
        * frob2 (monoSlot2 i) (monoSlot2 j) = 8 * (if i = j then 1 else 0) := by
  simp only [monoSlot0_eq', monoSlot1_eq', monoSlot2_eq']
  exact frob2_prod_monoSlot' i j

/-- **Closed form of the Frobenius sum:** the γ-monomials are Frobenius-orthonormal up to `8`. -/
theorem spinorMonomialGramFrobSum_eq (i j : Fin 64) :
    spinorMonomialGramFrobSum i j = 8 * (if i = j then 1 else 0) := by
  rw [spinorMonomialGramFrobSum_eq_frob2_prod, frob2_prod_spinorMonomialGram]

/--
Divisibility of each Frobenius sum by `8` — now a **theorem** (was an external-script axiom),
immediate from the closed form `spinorMonomialGramFrobSum_eq`.
-/
theorem eight_dvd_spinorMonomialGramFrobSum (i j : Fin 64) :
    8 ∣ spinorMonomialGramFrobSum i j :=
  ⟨_, spinorMonomialGramFrobSum_eq i j⟩

/-- Normalized Frobenius Gram matrix `W` with entries in `ℤ`. -/
def spinorMonomialGramColumns : Matrix (Fin 64) (Fin 64) ℤ :=
  fun i j => spinorMonomialGramFrobSum i j / 8

theorem spinorMonomialGramFrobSum_eq_mul_spinorMonomialGramColumns (i j : Fin 64) :
    spinorMonomialGramFrobSum i j = 8 * spinorMonomialGramColumns i j := by
  simp [spinorMonomialGramColumns, Int.mul_ediv_cancel' (eight_dvd_spinorMonomialGramFrobSum i j)]

/-- **The normalized Gram matrix is the identity.** -/
theorem spinorMonomialGramColumns_eq_one :
    spinorMonomialGramColumns = (1 : Matrix (Fin 64) (Fin 64) ℤ) := by
  ext i j
  rw [spinorMonomialGramColumns, spinorMonomialGramFrobSum_eq,
    Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0), Matrix.one_apply]

/-- `det W = 1 ≠ 0` — now a **theorem** (was derived from the `ZMod 101` script axiom),
immediate from `W = I`. -/
theorem spinorMonomialGramColumns_det_ne_zero : spinorMonomialGramColumns.det ≠ 0 := by
  rw [spinorMonomialGramColumns_eq_one, Matrix.det_one]
  exact one_ne_zero

end Hqiv.Algebra
