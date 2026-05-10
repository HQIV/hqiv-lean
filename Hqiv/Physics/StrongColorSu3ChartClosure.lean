import Hqiv.Physics.QuarkColorCarrierGaugeScaffold
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring

/-!
# Strong color: full `su(3)` Gell–Mann chart + structure constants

Completes the **abstract `3 × 3` chart** story from `QuarkColorCarrierGaugeScaffold`:

* Hermitian **Gell–Mann matrices** `λ₁ … λ₈` (`colorGellMannLambdaFull`).
* Half-generators **`T^a = λ^a / 2`** (`colorHalfGellMannFull`), agreeing with `colorHalfGellMann` on the
  first three slots (`colorHalfGellMannFull_eq_embedThree`).
* Totally antisymmetric **real structure constants** `f^{abc}` (`colorSu3fStructure`) in the
  standard textbook convention (sorted triples `012`, `036`, `045`, `135`, `146`, `234`, `256` at
  `1/2` or `1`; and `347`, `567` at `√3/2`).
* **Eight-channel covariant schematic term** (`colorTripletCovariantTermFull`).
* Canonical **sorted nonzero triples** (`colorSu3SortedNonzeroTriples`) for the `f^{ijk}` table on `i<j<k`.
* Optional **`f^{abc}` certificate** (54 nonzero `@[simp]` lemmas + generator script): build target
  `HQIVStrongColorSu3Certificate` (`lake build HQIVStrongColorSu3Certificate`; see
  `Hqiv/Physics/StrongColorSu3LieCertificate.lean` and `scripts/gen_strong_color_su3_f_simp.py`). This stays
  out of the default `HQIVLEAN` cone so it elaborates only when you ask for it.
* Global chart Lie law `[T^a,T^b] = \mathrm{i}\sum_c f^{abc}T^c` for **all** `(a,b)` is still a **target**;
  layer it on the certificate table (`colorSu3fSorted_congrProofs`, `Finset.sum_eq_single`, per-chart
  `fin_cases`) when you extend the optional build.

The structural carrier lift `colorGellMannEmbed_chart_lieBracket_smul` in `StrongColorCarrierClosure` maps any
chart identity to `8×8` once `lieBracketMat₃` is known on the triplet.

**Remark (hypercharge / `U(1)_Y`):** the remaining Cartan direction in `su(3)` is `T^8 ∝ λ₈`; embedding `U(1)_Y`
along that axis (and aligning it with the unused octonion direction / Fano-plane bookkeeping) is the natural
next gauge patch before packaging the full SM algebra inside `End(ℂ⁸)` compatibly with `Spin(8)` triality.
-/

open scoped BigOperators InnerProductSpace
open Complex Finset Matrix EuclideanSpace PiLp WithLp
open Hqiv.Algebra

namespace Hqiv.Physics

noncomputable section

/-- `λ₄` (Hermitian). -/
def colorGellMannLambda4 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1; 0, 0, 0; 1, 0, 0]

/-- `λ₅` (Hermitian). -/
def colorGellMannLambda5 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, -I; 0, 0, 0; I, 0, 0]

/-- `λ₆` (Hermitian). -/
def colorGellMannLambda6 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, 1; 0, 1, 0]

/-- `λ₇` (Hermitian). -/
def colorGellMannLambda7 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, -I; 0, I, 0]

/-- `λ₈ = (1/√3) diag(1,1,-2)` (Hermitian). -/
noncomputable def colorGellMannLambda8 : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 : ℂ) / Real.sqrt 3) • !![(1 : ℂ), 0, 0; 0, 1, 0; 0, 0, (-2 : ℂ)]

/-- All eight Gell–Mann matrices on the `Fin 3` triplet chart. -/
def colorGellMannLambdaFull (a : Fin 8) : Matrix (Fin 3) (Fin 3) ℂ :=
  match a with
  | 0 => colorGellMannLambda1
  | 1 => colorGellMannLambda2
  | 2 => colorGellMannLambda3
  | 3 => colorGellMannLambda4
  | 4 => colorGellMannLambda5
  | 5 => colorGellMannLambda6
  | 6 => colorGellMannLambda7
  | 7 => colorGellMannLambda8

/-- Half Gell–Mann generators `T^a = λ^a / 2` for `a = 0 … 7`. -/
noncomputable def colorHalfGellMannFull (a : Fin 8) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 : ℂ) / 2) • colorGellMannLambdaFull a

theorem colorHalfGellMannFull_eq_embedThree (a : Fin 3) :
    colorHalfGellMannFull (Fin.castLE (by decide : 3 ≤ 8) a) = colorHalfGellMann a := by
  fin_cases a <;> rfl

theorem colorHalfGellMannFull_zero : colorHalfGellMannFull 0 = colorHalfGellMann ⟨0, by decide⟩ := by
  simp [colorHalfGellMannFull, colorHalfGellMann, colorGellMannLambdaFull, colorGellMannLambda1]

theorem colorHalfGellMannFull_one : colorHalfGellMannFull 1 = colorHalfGellMann ⟨1, by decide⟩ := by
  simp [colorHalfGellMannFull, colorHalfGellMann, colorGellMannLambdaFull, colorGellMannLambda2]

theorem colorHalfGellMannFull_two : colorHalfGellMannFull 2 = colorHalfGellMann ⟨2, by decide⟩ := by
  simp [colorHalfGellMannFull, colorHalfGellMann, colorGellMannLambdaFull, colorGellMannLambda3]

/-! ### `f^{abc}` tensor (totally antisymmetric, real) -/

/-- Value on strictly increasing triples `(i < j < k)` for the **Hermitian** Gell–Mann basis used here
(signs fixed so `[T^a,T^b] = I • ∑_c f^{abc} T^c` holds for all `a,b`). -/
noncomputable def colorSu3fSorted (i j k : Fin 8) (hij : i < j) (hjk : j < k) : ℝ :=
  match i, j, k with
  | 0, 1, 2 => 1
  | 0, 3, 6 => (1 / 2 : ℝ)
  | 0, 4, 5 => (-1 / 2 : ℝ)
  | 1, 3, 5 => (1 / 2 : ℝ)
  | 1, 4, 6 => (1 / 2 : ℝ)
  | 2, 3, 4 => (1 / 2 : ℝ)
  | 2, 5, 6 => (-1 / 2 : ℝ)
  | 3, 4, 7 => (Real.sqrt 3 / 2 : ℝ)
  | 5, 6, 7 => (Real.sqrt 3 / 2 : ℝ)
  | _, _, _ => 0

/-- `colorSu3fSorted` does not depend on which proofs witness `i < j` and `j < k`. -/
theorem colorSu3fSorted_congrProofs (i j k : Fin 8) (hij hij' : i < j) (hjk hjk' : j < k) :
    colorSu3fSorted i j k hij hjk = colorSu3fSorted i j k hij' hjk' :=
  rfl

noncomputable def min3 (a b c : Fin 8) : Fin 8 := min (min a b) c

noncomputable def max3 (a b c : Fin 8) : Fin 8 := max (max a b) c

/-- Middle element when `a`, `b`, `c` are pairwise distinct (otherwise unused). -/
noncomputable def mid3 (a b c : Fin 8) : Fin 8 :=
  let i := min3 a b c
  let k := max3 a b c
  if _ : a ≠ i ∧ a ≠ k then a else if _ : b ≠ i ∧ b ≠ k then b else c

/-- Sign of the permutation sorting `(a,b,c)` into `(min3, mid3, max3)`; `0` on a repeated index. -/
noncomputable def colorSu3PermSign (a b c : Fin 8) : ℤ :=
  if _ : a = b ∨ b = c ∨ c = a then 0
  else
    let i := min3 a b c
    let j := mid3 a b c
    let k := max3 a b c
    if a = i ∧ b = j ∧ c = k then 1
    else if a = i ∧ b = k ∧ c = j then -1
    else if a = j ∧ b = i ∧ c = k then -1
    else if a = j ∧ b = k ∧ c = i then 1
    else if a = k ∧ b = i ∧ c = j then 1
    else if a = k ∧ b = j ∧ c = i then -1
    else 0

/-- Totally antisymmetric structure constants `f^{abc}` (real). -/
noncomputable def colorSu3fStructure (a b c : Fin 8) : ℝ :=
  if _ : a = b ∨ b = c ∨ c = a then 0
  else
    let i := min3 a b c
    let j := mid3 a b c
    let k := max3 a b c
    if hij : i < j then
      if hjk : j < k then
        (colorSu3PermSign a b c : ℝ) * colorSu3fSorted i j k hij hjk
      else 0
    else 0

/-! ### Canonical sorted triples for the `f^{ijk}` table (`i < j < k`) -/

/-- The nine strictly-increasing triples carrying the nonzero sorted values in `colorSu3fSorted`. -/
noncomputable def colorSu3SortedNonzeroTriples : Finset (Fin 8 × Fin 8 × Fin 8) :=
  List.toFinset [
    ((0 : Fin 8), 1, 2),
    (0, 3, 6),
    (0, 4, 5),
    (1, 3, 5),
    (1, 4, 6),
    (2, 3, 4),
    (2, 5, 6),
    (3, 4, 7),
    (5, 6, 7),
  ]

/-
Implementation note: `colorSu3fSorted_congrProofs` removes proof-irrelevance friction in `colorSu3fSorted`.
The optional `HQIVStrongColorSu3Certificate` target adds the generated `@[simp]` `f^{abc}` atoms; use them
after `Fin.sum_univ_eight` when closing matrix chart goals.
-/

/-! ### Global `su(3)` bracket on the chart (algebraic skeleton) -/

theorem lieBracketMat₃_neg_swap (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    lieBracketMat₃ A B = -lieBracketMat₃ B A := by
  simp [lieBracketMat₃, sub_eq_add_neg]

/-- Schematic covariant slot with all eight color generators. -/
noncomputable def colorTripletCovariantTermFull (g : ℝ) (G : Fin 8 → ℂ) (ψ : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ∑ a : Fin 8, (-I * (g : ℂ) * G a) • (colorHalfGellMannFull a).mulVec ψ

end -- noncomputable section

end Hqiv.Physics
