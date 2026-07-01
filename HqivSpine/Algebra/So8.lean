import HqivSpine.Foundation.Carrier
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# `HqivSpine.Algebra.So8` — the rotation algebra `𝔰𝔬(n)` as real matrices

The carrier's rotation algebra is a genuine matrix Lie algebra, not a bookkeeping
number. We build `𝔰𝔬(n)` from the standard skew-symmetric basis and read off its
dimension by *exact* linear algebra — no floating-point orthonormality, no `axiom`,
no `native_decide`, and crucially **no `28×28` determinant**:

* `skewMatrices n` — the submodule of skew-symmetric `n×n` real matrices;
* `skewGen i j = single i j 1 − single j i 1` — the generator of the `(i,j)` plane;
* these are linearly independent and span (`skew_repr`), so they form `skewBasis`;
* hence `finrank (skewMatrices n) = #{(i,j) : i < j}`, and for `n = 8` this is `28`
  by `decide`;
* the commutator preserves skew-symmetry (`bracket_mem`), giving a genuine
  Lie-closure certificate `skewGen_so_closure` (antisymmetry + bracket-closure +
  independence) for the standard basis.

This is the determinant-free `𝔰𝔬(8)` the rest of the gauge layer sits inside.
-/

namespace HqivSpine.Algebra

open Matrix BigOperators

variable (n : ℕ)

/-- Ordered index pairs `i < j` in `Fin n`: the indexing set of the skew basis. -/
abbrev OrderedPair (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

/-- The submodule of real `n × n` skew-symmetric matrices (`Aᵀ = -A`) — i.e. `𝔰𝔬(n)`. -/
def skewMatrices : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | Aᵀ = -A}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [transpose_add, ha, hb, neg_add]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [transpose_smul, ha, smul_neg]

variable {n}

@[simp] lemma mem_skewMatrices {A : Matrix (Fin n) (Fin n) ℝ} :
    A ∈ skewMatrices n ↔ Aᵀ = -A := Iff.rfl

/-- Transpose of a single-entry matrix swaps the indices. -/
lemma transpose_single (i j : Fin n) (c : ℝ) :
    (single i j c)ᵀ = single j i c := by
  ext a b
  simp only [transpose_apply, single_apply, and_comm]

/-- The standard skew generator attached to a pair `(i, j)`: the infinitesimal
rotation of the `(i,j)`-plane. -/
def skewGen (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  single i j 1 - single j i 1

/-- Entrywise value of a skew generator. -/
lemma skewGen_apply (i j a b : Fin n) :
    skewGen i j a b
      = (if i = a ∧ j = b then (1 : ℝ) else 0) - (if j = a ∧ i = b then 1 else 0) := by
  simp [skewGen, single_apply]

/-- Every standard generator is skew-symmetric (lies in `𝔰𝔬(n)`). -/
lemma skewGen_mem (i j : Fin n) : skewGen i j ∈ skewMatrices n := by
  rw [mem_skewMatrices, skewGen, transpose_sub, transpose_single, transpose_single, neg_sub]

/-- **Entry extraction.** Evaluating a coefficient combination of skew generators at
the matrix entry of an ordered pair `p` returns exactly the coefficient `c p`. This
is the load-bearing exact computation behind both independence and spanning. -/
lemma sum_skewGen_apply (c : OrderedPair n → ℝ) (p : OrderedPair n) :
    (∑ q : OrderedPair n, c q • skewGen q.1.1 q.1.2) p.1.1 p.1.2 = c p := by
  obtain ⟨⟨a, b⟩, hab⟩ := p
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨(a, b), hab⟩ : OrderedPair n)]
  · have hne : a ≠ b := ne_of_lt hab
    rw [skewGen_apply]; simp [hne, hne.symm]
  · intro q _ hq
    rw [skewGen_apply]
    have h1 : ¬ (q.1.1 = a ∧ q.1.2 = b) := fun ⟨e1, e2⟩ =>
      hq (Subtype.ext (Prod.ext_iff.mpr ⟨e1, e2⟩))
    have h2 : ¬ (q.1.2 = a ∧ q.1.1 = b) := by
      rintro ⟨e1, e2⟩
      have hlt : q.1.1 < q.1.2 := q.2
      rw [e1, e2] at hlt
      exact absurd (hab.trans hlt) (lt_irrefl a)
    simp [h1, h2]
  · intro h; exact absurd (Finset.mem_univ _) h

variable (n) in
/-- **Linear independence of the standard skew generators** (general `n`). -/
theorem skewGen_linearIndependent :
    LinearIndependent ℝ (fun p : OrderedPair n => skewGen p.1.1 p.1.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have hp := sum_skewGen_apply g p
  rw [hg] at hp
  simpa using hp.symm

/-- **Spanning / representation.** Every skew-symmetric matrix is the combination of
standard generators with its own upper-triangle entries as coefficients. -/
lemma skew_repr {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = -A) :
    A = ∑ p : OrderedPair n, A p.1.1 p.1.2 • skewGen p.1.1 p.1.2 := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rcases lt_trichotomy x y with hlt | heq | hgt
  · rw [Finset.sum_eq_single (⟨(x, y), hlt⟩ : OrderedPair n)]
    · rw [skewGen_apply]; simp [ne_of_lt hlt, (ne_of_lt hlt).symm]
    · intro q _ hq
      rw [skewGen_apply]
      have h1 : ¬ (q.1.1 = x ∧ q.1.2 = y) := fun ⟨e1, e2⟩ =>
        hq (Subtype.ext (Prod.ext_iff.mpr ⟨e1, e2⟩))
      have h2 : ¬ (q.1.2 = x ∧ q.1.1 = y) := by
        rintro ⟨e1, e2⟩
        have hlt2 : q.1.1 < q.1.2 := q.2
        rw [e1, e2] at hlt2
        exact absurd (hlt.trans hlt2) (lt_irrefl x)
      simp [h1, h2]
    · intro h; exact absurd (Finset.mem_univ _) h
  · subst heq
    have hdiag : A x x = 0 := by
      have h := congrFun (congrFun hA x) x
      simp only [transpose_apply, neg_apply] at h
      linarith
    rw [hdiag]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [skewGen_apply]
    have h1 : ¬ (q.1.1 = x ∧ q.1.2 = x) := by
      rintro ⟨e1, e2⟩; have hlt := q.2; rw [e1, e2] at hlt; exact lt_irrefl x hlt
    have h2 : ¬ (q.1.2 = x ∧ q.1.1 = x) := by
      rintro ⟨e1, e2⟩; have hlt := q.2; rw [e1, e2] at hlt; exact lt_irrefl x hlt
    simp [h1, h2]
  · rw [Finset.sum_eq_single (⟨(y, x), hgt⟩ : OrderedPair n)]
    · rw [skewGen_apply]
      have hne : y ≠ x := ne_of_lt hgt
      have hAxy : A x y = -(A y x) := by
        have h := congrFun (congrFun hA x) y
        simp only [transpose_apply, neg_apply] at h
        linarith
      simp [hne, hne.symm]
      linarith [hAxy]
    · intro q _ hq
      rw [skewGen_apply]
      have h1 : ¬ (q.1.1 = x ∧ q.1.2 = y) := by
        rintro ⟨e1, e2⟩
        have hlt2 : q.1.1 < q.1.2 := q.2
        rw [e1, e2] at hlt2
        exact absurd (hlt2.trans hgt) (lt_irrefl x)
      have h2 : ¬ (q.1.2 = x ∧ q.1.1 = y) := fun ⟨e1, e2⟩ =>
        hq (Subtype.ext (Prod.ext_iff.mpr ⟨e2, e1⟩))
      simp [h1, h2]
    · intro h; exact absurd (Finset.mem_univ _) h

variable (n) in
/-- **The standard skew basis** of `𝔰𝔬(n)`. -/
noncomputable def skewBasis : Module.Basis (OrderedPair n) ℝ (skewMatrices n) :=
  Module.Basis.mk
    (v := fun p => ⟨skewGen p.1.1 p.1.2, skewGen_mem p.1.1 p.1.2⟩)
    (by
      apply LinearIndependent.of_comp (skewMatrices n).subtype
      exact skewGen_linearIndependent n)
    (by
      rintro ⟨A, hA⟩ -
      rw [mem_skewMatrices] at hA
      have hrepr := skew_repr hA
      have hval : (⟨A, hA⟩ : skewMatrices n)
          = ∑ p : OrderedPair n,
              A p.1.1 p.1.2 • (⟨skewGen p.1.1 p.1.2, skewGen_mem _ _⟩ : skewMatrices n) := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finset_sum]
        simp only [SetLike.val_smul]
        exact hrepr
      rw [hval]
      exact Submodule.sum_mem _ (fun p _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)))

variable (n) in
/-- **Dimension of `𝔰𝔬(n)`** equals the number of ordered index pairs `i < j`. -/
theorem finrank_skewMatrices :
    Module.finrank ℝ (skewMatrices n) = Fintype.card (OrderedPair n) :=
  Module.finrank_eq_card_basis (skewBasis n)

/-- Worked low-dimensional analogue: `dim 𝔰𝔬(4) = 6`. -/
theorem finrank_so4 : Module.finrank ℝ (skewMatrices 4) = 6 := by
  rw [finrank_skewMatrices]; decide

/-- **The carrier rotation algebra has dimension `28`,** from genuine linear algebra
(`decide` on `#{(i,j) : i < j, i,j < 8} = 28` — no determinant, no `native_decide`). -/
theorem finrank_so8 : Module.finrank ℝ (skewMatrices 8) = 28 := by
  rw [finrank_skewMatrices]; decide

open HqivSpine.Foundation in
/-- **Bridge to the foundation count.** The genuine linear-algebra dimension of the
carrier's rotation algebra equals the derived `soDim carrierMultiplicity = 28`. -/
theorem finrank_skew_carrier_eq_soDim :
    Module.finrank ℝ (skewMatrices carrierMultiplicity) = soDim carrierMultiplicity := by
  rw [carrierMultiplicity_eq_eight, finrank_so8, soDim_eight]

/-! ### Genuine Lie closure of `𝔰𝔬(n)` -/

/-- Matrix commutator `[A, B] = A·B − B·A`. -/
def bracket (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := A * B - B * A

/-- The skew-symmetric matrices are closed under the commutator:
`[A,B]ᵀ = BᵀAᵀ − AᵀBᵀ = BA − AB = −[A,B]`. -/
lemma bracket_mem {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ skewMatrices n) (hB : B ∈ skewMatrices n) :
    bracket A B ∈ skewMatrices n := by
  rw [mem_skewMatrices] at hA hB ⊢
  rw [bracket, transpose_sub, transpose_mul, transpose_mul, hA, hB,
    neg_mul_neg, neg_mul_neg, neg_sub]

variable (n) in
/-- **Axiom-free `𝔰𝔬(n)` Lie-closure certificate** for the standard skew basis:

1. every generator is antisymmetric;
2. every commutator of generators is a finite linear combination of generators
   (closure — *free* from `skew_repr`, since brackets of skew matrices are skew);
3. the generators are linearly independent. -/
theorem skewGen_so_closure :
    (∀ p : OrderedPair n, (skewGen p.1.1 p.1.2)ᵀ + skewGen p.1.1 p.1.2 = 0) ∧
    (∀ p q : OrderedPair n, ∃ f : OrderedPair n → ℝ,
        bracket (skewGen p.1.1 p.1.2) (skewGen q.1.1 q.1.2)
          = ∑ r : OrderedPair n, f r • skewGen r.1.1 r.1.2) ∧
    LinearIndependent ℝ (fun p : OrderedPair n => skewGen p.1.1 p.1.2) := by
  refine ⟨?_, ?_, skewGen_linearIndependent n⟩
  · intro p
    have h := skewGen_mem (n := n) p.1.1 p.1.2
    rw [mem_skewMatrices] at h
    rw [h, neg_add_cancel]
  · intro p q
    have hb : bracket (skewGen p.1.1 p.1.2) (skewGen q.1.1 q.1.2) ∈ skewMatrices n :=
      bracket_mem (skewGen_mem _ _) (skewGen_mem _ _)
    rw [mem_skewMatrices] at hb
    exact ⟨fun r => (bracket (skewGen p.1.1 p.1.2) (skewGen q.1.1 q.1.2)) r.1.1 r.1.2,
      skew_repr hb⟩

/-- The carrier instance: a genuine axiom-free `𝔰𝔬(8)` Lie-closure certificate. -/
theorem skewGen_so8_closure :
    (∀ p : OrderedPair 8, (skewGen p.1.1 p.1.2)ᵀ + skewGen p.1.1 p.1.2 = 0) ∧
    (∀ p q : OrderedPair 8, ∃ f : OrderedPair 8 → ℝ,
        bracket (skewGen p.1.1 p.1.2) (skewGen q.1.1 q.1.2)
          = ∑ r : OrderedPair 8, f r • skewGen r.1.1 r.1.2) ∧
    LinearIndependent ℝ (fun p : OrderedPair 8 => skewGen p.1.1 p.1.2) :=
  skewGen_so_closure 8

end HqivSpine.Algebra
