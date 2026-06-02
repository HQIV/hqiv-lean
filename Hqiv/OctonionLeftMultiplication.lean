import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Hqiv

/-!
# Octonion left-multiplication matrices L(e_1) .. L(e_7)

From the **first assumptions**: the algebra O = ℝ⁸ with Fano-plane multiplication;
left multiplication by the imaginary unit e_i is a linear map, hence an 8×8 real
matrix **L(e_i)**. Source: `HQVM/matrices.py` (`_build_left_multiplications`).
L(e_7) is the colour-preferred axis (paper).

To regenerate: `PYTHONPATH=~/Repos/HQIV python3 scripts/print_lean_octonion_L.py`
-/

/-- L(e_1) (imaginary unit 1). -/
def octonionLeftMul_1 : Matrix (Fin 8) (Fin 8) ℝ := !![
    (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)
  ]

/-- L(e_2) (imaginary unit 2). -/
def octonionLeftMul_2 : Matrix (Fin 8) (Fin 8) ℝ := !![
    (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ);
    (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)
  ]

/-- L(e_3) (imaginary unit 3). -/
def octonionLeftMul_3 : Matrix (Fin 8) (Fin 8) ℝ := !![
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ);
    (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ);
    (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)
  ]

/-- L(e_4) (imaginary unit 4). -/
def octonionLeftMul_4 : Matrix (Fin 8) (Fin 8) ℝ := !![
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ);
    (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)
  ]

/-- L(e_5) (imaginary unit 5). -/
def octonionLeftMul_5 : Matrix (Fin 8) (Fin 8) ℝ := !![
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ);
    (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)
  ]

/-- L(e_6) (imaginary unit 6). -/
def octonionLeftMul_6 : Matrix (Fin 8) (Fin 8) ℝ := !![
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)
  ]

/-- L(e_7) (imaginary unit 7, colour-preferred axis). -/
def octonionLeftMul_7 : Matrix (Fin 8) (Fin 8) ℝ := !![
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ);
    (1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)
  ]

/-- Entry lemmas for L(e_4) at indices where fin_cases + norm_num may not reduce (antisymmetry proof). -/
lemma octonionLeftMul_4_2_4 : octonionLeftMul_4 2 4 = 0 := rfl
lemma octonionLeftMul_4_4_2 : octonionLeftMul_4 4 2 = 0 := rfl
lemma octonionLeftMul_4_2_6 : octonionLeftMul_4 2 6 = 1 := rfl
lemma octonionLeftMul_4_6_2 : octonionLeftMul_4 6 2 = -1 := rfl
lemma octonionLeftMul_4_3_5 : octonionLeftMul_4 3 5 = 0 := rfl
lemma octonionLeftMul_4_5_3 : octonionLeftMul_4 5 3 = 0 := rfl
lemma octonionLeftMul_4_3_7 : octonionLeftMul_4 3 7 = 1 := rfl
lemma octonionLeftMul_4_7_3 : octonionLeftMul_4 7 3 = -1 := rfl

/-- Entry lemmas for L(e_5) at indices where fin_cases + norm_num may not reduce (antisymmetry proof). -/
lemma octonionLeftMul_5_2_4 : octonionLeftMul_5 2 4 = 0 := rfl
lemma octonionLeftMul_5_4_2 : octonionLeftMul_5 4 2 = 0 := rfl
lemma octonionLeftMul_5_3_5 : octonionLeftMul_5 3 5 = 0 := rfl
lemma octonionLeftMul_5_5_3 : octonionLeftMul_5 5 3 = 0 := rfl

/-- **L(e_{N+1}) as a map** from Fin 7 (N=0..6 → e_1..e_7). -/
def octonionLeftMul_N (N : Fin 7) : Matrix (Fin 8) (Fin 8) ℝ :=
  match N with
  | 0 => octonionLeftMul_1
  | 1 => octonionLeftMul_2
  | 2 => octonionLeftMul_3
  | 3 => octonionLeftMul_4
  | 4 => octonionLeftMul_5
  | 5 => octonionLeftMul_6
  | 6 => octonionLeftMul_7

/-! ## Selected full-column signatures (Fano / associator witness shortcuts)

`simp` with `Matrix.of_apply` and the defining `octonionLeftMul_*` matches — no extra `norm_num`.
-/

/-- Column 3 of `L(e_1)`: the product e₁e₃ in ℝ⁸. -/
theorem octonionLeftMul_1_k_3 (k : Fin 8) :
    octonionLeftMul_1 k 3 = if k = 6 then (-1 : ℝ) else 0 := by
  fin_cases k <;> simp [octonionLeftMul_1, Matrix.of_apply]

theorem octonionLeftMul_3_k_5 (k : Fin 8) :
    octonionLeftMul_3 k 5 = if k = 2 then (-1 : ℝ) else 0 := by
  fin_cases k <;> simp [octonionLeftMul_3, Matrix.of_apply]

theorem octonionLeftMul_6_k_5 (k : Fin 8) :
    octonionLeftMul_6 k 5 = if k = 3 then (-1 : ℝ) else 0 := by
  fin_cases k <;> simp [octonionLeftMul_6, Matrix.of_apply]

theorem octonionLeftMul_1_k_2 (k : Fin 8) :
    octonionLeftMul_1 k 2 = if k = 7 then (1 : ℝ) else 0 := by
  fin_cases k <;> simp [octonionLeftMul_1, Matrix.of_apply]

theorem octonionLeftMul_1_k_6 (k : Fin 8) :
    octonionLeftMul_1 k 6 = if k = 3 then (1 : ℝ) else 0 := by
  fin_cases k <;> simp [octonionLeftMul_1, Matrix.of_apply]

theorem octonionLeftMul_2_k_3 (k : Fin 8) :
    octonionLeftMul_2 k 3 = if k = 6 then (1 : ℝ) else 0 := by
  fin_cases k <;> simp [octonionLeftMul_2, Matrix.of_apply]

theorem octonionLeftMul_7_k_3 (k : Fin 8) :
    octonionLeftMul_7 k 3 = if k = 4 then (1 : ℝ) else 0 := by
  fin_cases k <;> simp [octonionLeftMul_7, Matrix.of_apply]

/-!
## Next steps (GeneratorsFromAxioms)

- **g₂**: Define the 14 commutators [L(e_i), L(e_j)] for i < j using `lieBracket`.
- Prove the Lie algebra generated by g₂ ∪ {phaseLiftDelta} is spanned by the 28
  so8Generators (Generators.lean).
-/

end Hqiv
