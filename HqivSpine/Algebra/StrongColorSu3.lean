import HqivSpine.Algebra.StrongColor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# `HqivSpine.Algebra.StrongColorSu3` — full eight-generator `su(3)` chart

Completes the triplet chart from `StrongColor` with Hermitian Gell–Mann matrices `λ₁…λ₈`,
half-generators `T^a = λ^a/2`, totally antisymmetric structure constants `f^{abc}`, and the
eight-channel covariant schematic term.

The global Lie law `[T^a,T^b] = Complex.I • ∑_c f^{abc} T^c` is proved in
`StrongColorSu3LieLaw` (certificate layer; regenerate via
`python3 scripts/gen_strong_color_su3_lie_chart_law.py --spine`).

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Algebra.StrongColor

noncomputable section

open Complex Matrix Finset
open scoped BigOperators

/-- `λ₄` (Hermitian). -/
def gellMann4 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1; 0, 0, 0; 1, 0, 0]

/-- `λ₅` (Hermitian). -/
def gellMann5 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, -Complex.I; 0, 0, 0; Complex.I, 0, 0]

/-- `λ₆` (Hermitian). -/
def gellMann6 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, 1; 0, 1, 0]

/-- `λ₇` (Hermitian). -/
def gellMann7 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0]

/-- `λ₈ = (1/√3) diag(1,1,-2)` (Hermitian). -/
noncomputable def gellMann8 : Matrix (Fin 3) (Fin 3) ℂ :=
  let s := (1 / Real.sqrt 3 : ℝ)
  !![Complex.ofReal s, (0 : ℂ), (0 : ℂ); (0 : ℂ), Complex.ofReal s, (0 : ℂ);
    (0 : ℂ), (0 : ℂ), Complex.ofReal (-2 * s)]

theorem gellMann8_hermitian : gellMann8.conjTranspose = gellMann8 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gellMann8, Matrix.conjTranspose, Matrix.of_apply, Complex.conj_ofReal, Complex.ofReal,
      Complex.star_def, Complex.ext_iff]

/-- All eight Gell–Mann matrices on the `Fin 3` triplet chart. -/
def gellMannFull (a : Fin 8) : Matrix (Fin 3) (Fin 3) ℂ :=
  match a with
  | 0 => gellMann1
  | 1 => gellMann2
  | 2 => gellMann3
  | 3 => gellMann4
  | 4 => gellMann5
  | 5 => gellMann6
  | 6 => gellMann7
  | 7 => gellMann8

/-- Half Gell–Mann generators `T^a = λ^a / 2` for `a = 0 … 7`. -/
noncomputable def halfGellMannFull (a : Fin 8) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 : ℂ) / 2) • gellMannFull a

theorem halfGellMannFull_eq_embedThree (a : Fin 3) :
    halfGellMannFull (Fin.castLE (by decide : 3 ≤ 8) a) = halfGellMann a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [halfGellMannFull, halfGellMann, gellMannFull, gellMann, gellMann1, gellMann2, gellMann3]

/-! ### `f^{abc}` tensor (totally antisymmetric, real) -/

/-- Value on strictly increasing triples `(i < j < k)` for the Hermitian Gell–Mann basis. -/
noncomputable def su3fSorted (i j k : Fin 8) (hij : i < j) (hjk : j < k) : ℝ :=
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

theorem su3fSorted_congrProofs (i j k : Fin 8) (hij hij' : i < j) (hjk hjk' : j < k) :
    su3fSorted i j k hij hjk = su3fSorted i j k hij' hjk' :=
  rfl

noncomputable def min3 (a b c : Fin 8) : Fin 8 := min (min a b) c

noncomputable def max3 (a b c : Fin 8) : Fin 8 := max (max a b) c

noncomputable def mid3 (a b c : Fin 8) : Fin 8 :=
  let i := min3 a b c
  let k := max3 a b c
  if _ : a ≠ i ∧ a ≠ k then a else if _ : b ≠ i ∧ b ≠ k then b else c

/-- Sign of the permutation sorting `(a,b,c)` into `(min3, mid3, max3)`. -/
noncomputable def su3PermSign (a b c : Fin 8) : ℤ :=
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
noncomputable def su3fStructure (a b c : Fin 8) : ℝ :=
  if _ : a = b ∨ b = c ∨ c = a then 0
  else
    let i := min3 a b c
    let j := mid3 a b c
    let k := max3 a b c
    if hij : i < j then
      if hjk : j < k then
        (su3PermSign a b c : ℝ) * su3fSorted i j k hij hjk
      else 0
    else 0

/-- The nine strictly-increasing triples carrying nonzero sorted values. -/
noncomputable def su3SortedNonzeroTriples : Finset (Fin 8 × Fin 8 × Fin 8) :=
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

theorem lieBracketMat3_neg_swap (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    lieBracketMat3 A B = -lieBracketMat3 B A := by
  simp [lieBracketMat3, sub_eq_add_neg]

theorem lieBracketMat3_I_smul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    lieBracketMat3 (Complex.I • A) (Complex.I • B) = -lieBracketMat3 A B := by
  ext i j
  simp [lieBracketMat3, Matrix.mul_apply, Matrix.smul_apply, smul_smul, Complex.I_mul_I,
    Fin.sum_univ_three, sub_eq_add_neg, neg_smul]
  ring

theorem gellMannFull_hermitian (a : Fin 8) : (gellMannFull a).conjTranspose = gellMannFull a := by
  fin_cases a
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [gellMannFull, gellMann1, Matrix.conjTranspose, Matrix.of_apply, Complex.conj_ofReal,
        Complex.conj_I, map_zero]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [gellMannFull, gellMann2, Matrix.conjTranspose, Matrix.of_apply, Complex.conj_ofReal,
        Complex.conj_I, map_zero]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [gellMannFull, gellMann3, Matrix.conjTranspose, Matrix.of_apply, Complex.conj_ofReal,
        Complex.conj_I, map_zero]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [gellMannFull, gellMann4, Matrix.conjTranspose, Matrix.of_apply, Complex.conj_ofReal,
        Complex.conj_I, map_zero]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [gellMannFull, gellMann5, Matrix.conjTranspose, Matrix.of_apply, Complex.conj_ofReal,
        Complex.conj_I, map_zero]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [gellMannFull, gellMann6, Matrix.conjTranspose, Matrix.of_apply, Complex.conj_ofReal,
        Complex.conj_I, map_zero]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [gellMannFull, gellMann7, Matrix.conjTranspose, Matrix.of_apply, Complex.conj_ofReal,
        Complex.conj_I, map_zero]
  · exact gellMann8_hermitian

theorem halfGellMannFull_hermitian (a : Fin 8) :
    (halfGellMannFull a).conjTranspose = halfGellMannFull a := by
  simp [halfGellMannFull, gellMannFull_hermitian, Matrix.conjTranspose_smul, Complex.conj_ofReal]

theorem halfGellMannFull_re_symm (a : Fin 8) (i j : Fin 3) :
    (halfGellMannFull a i j).re = (halfGellMannFull a j i).re := by
  have := congrFun (congrFun (halfGellMannFull_hermitian a) j) i
  simp [Matrix.conjTranspose_apply, Complex.ext_iff, Complex.conj_re, Complex.conj_im] at this
  exact this.1

theorem halfGellMannFull_im_antisymm (a : Fin 8) (i j : Fin 3) :
    (halfGellMannFull a i j).im = -(halfGellMannFull a j i).im := by
  have := congrFun (congrFun (halfGellMannFull_hermitian a) j) i
  simp [Matrix.conjTranspose_apply, Complex.ext_iff, Complex.conj_re, Complex.conj_im] at this
  have h := this.2
  linarith

theorem halfGellMannFull_I_antiHermitian (a : Fin 8) :
    (Complex.I • halfGellMannFull a).conjTranspose = -(Complex.I • halfGellMannFull a) := by
  simp [Matrix.conjTranspose_smul, halfGellMannFull_hermitian, star_smul, Complex.conj_I, neg_smul]

/-- Schematic covariant slot with all eight colour generators. -/
noncomputable def tripletCovariantTermFull (g : ℝ) (G : Fin 8 → ℂ) (ψ : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ∑ a : Fin 8, (-Complex.I * (g : ℂ) * G a) • (halfGellMannFull a).mulVec ψ

end

end HqivSpine.Algebra.StrongColor
