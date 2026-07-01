import HqivSpine.Algebra.So8
import HqivSpine.Algebra.StrongColorSu3
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Algebra.SkewChartBridge` — chart Lie algebras inside `𝔰𝔬(n)` (general `n`)

* **`skewPad`**: block-zero inclusion `𝔰𝔬(m) ↪ 𝔰𝔬(n)` when `m ≤ n`;
* **`complexToReal6` / `su3RealGen`**: standard realification `su(3) ↪ 𝔰𝔬(6)`;
* closure (`su3RealGen_mem`, `su3RealGen_lieBracket`) in `SkewChartBridgeSu3Closure`.

We do **not** fix a Spin(8) triality-compatible complex structure on the octonion carrier.
-/

namespace HqivSpine.Algebra

noncomputable section

open Complex Matrix Finset
open scoped BigOperators
open StrongColor

/-! ## `𝔰𝔬(m) ↪ 𝔰𝔬(n)` via block-zero padding -/

namespace SkewPad

variable {m n : ℕ}

def skewPad (hm : m ≤ n) (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if hi : i.val < m then
      if hj : j.val < m then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else 0

theorem skewPad_add (hm : m ≤ n) (A B : Matrix (Fin m) (Fin m) ℝ) :
    skewPad hm (A + B) = skewPad hm A + skewPad hm B := by
  ext i j
  simp only [skewPad, Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem skewPad_smul (hm : m ≤ n) (c : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    skewPad hm (c • A) = c • skewPad hm A := by
  ext i j
  simp only [skewPad, Matrix.smul_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem skewPad_neg (hm : m ≤ n) (A : Matrix (Fin m) (Fin m) ℝ) :
    skewPad hm (-A) = -skewPad hm A := by
  ext i j
  simp only [skewPad, Matrix.neg_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem skewPad_transpose (hm : m ≤ n) (A : Matrix (Fin m) (Fin m) ℝ) :
    (skewPad hm A)ᵀ = skewPad hm (Aᵀ) := by
  ext i j; simp [skewPad, Matrix.of_apply, transpose_apply, Fin.ext_iff]; split_ifs <;> simp

theorem skewPad_mem (hm : m ≤ n) {A : Matrix (Fin m) (Fin m) ℝ} (hA : A ∈ skewMatrices m) :
    skewPad hm A ∈ skewMatrices n := by
  rw [mem_skewMatrices] at hA ⊢
  rw [skewPad_transpose, hA, skewPad_neg]

end SkewPad

/-! ## `su(3) ↪ 𝔰𝔬(6)` via block realification -/

namespace Su3RealSkew

open SkewPad

def block6 (i : Fin 6) : Fin 2 :=
  match i with
  | 0 | 1 | 2 => 0
  | 3 | 4 | 5 => 1

def fin6to3 (i : Fin 6) : Fin 3 :=
  match i with
  | 0 | 3 => 0
  | 1 | 4 => 1
  | 2 | 5 => 2

/-- Standard real `6 × 6` matrix for a `3 × 3` complex matrix (`[[Re, −Im], [Im, Re]]`). -/
def complexToReal6 (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun i j =>
    match block6 i, block6 j with
    | 0, 0 => (X (fin6to3 i) (fin6to3 j)).re
    | 0, 1 => -(X (fin6to3 i) (fin6to3 j)).im
    | 1, 0 => (X (fin6to3 i) (fin6to3 j)).im
    | 1, 1 => (X (fin6to3 i) (fin6to3 j)).re

def su3RealGen (a : Fin 8) : Matrix (Fin 6) (Fin 6) ℝ :=
  complexToReal6 (Complex.I • halfGellMannFull a)

theorem su3RealGen_eq_complexToReal6 (a : Fin 8) :
    su3RealGen a = complexToReal6 (Complex.I • halfGellMannFull a) := rfl

def su3RealGenPad (n : ℕ) (hn : 6 ≤ n) (a : Fin 8) : Matrix (Fin n) (Fin n) ℝ :=
  SkewPad.skewPad hn (su3RealGen a)

end Su3RealSkew

end

end HqivSpine.Algebra
