import Hqiv.Algebra.CliffordCl06SixStandardSpinorRho
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Integer (`ℤ`) spinor `γ` matrices and `γ`-monomials

Mirror of `CliffordCl06SixStandardSpinorRho` at coefficients in `ℤ`, using the same triple
Kronecker bitmask layout.  Casting into `ℝ` commutes with Kronecker product and with the six fixed
blocks, so the `ℝ` model used by `cl06SpinorGammaMat` is exactly `Matrix.map (algebraMap ℤ ℝ)` of
this layer.
-/

namespace Hqiv.Algebra

open Matrix Finset

/-- Same mask convention as `cl06SpinorGammaMaskFinset` in `CliffordCl06SixStandardSpinorMatLiftSurjective`. -/
def cl06SpinorGammaMaskFinset (m : Fin 64) : Finset (Fin 6) :=
  univ.filter fun i : Fin 6 => (m.val >>> i.val) % 2 = 1

/-! ## `2 × 2` blocks over `ℤ` -/

def spinorIxZ : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 1]
def spinorXZ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
def spinorZZ : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]
def spinorAZ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

def spinorKron3Z (A B C : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j =>
    A (fin8Lo i) (fin8Lo j) * B (fin8Mid i) (fin8Mid j) * C (fin8Hi i) (fin8Hi j)

def cl06SpinorGammaMatZ : Fin 6 → Matrix (Fin 8) (Fin 8) ℤ
  | ⟨0, _⟩ => spinorKron3Z spinorAZ spinorIxZ spinorXZ
  | ⟨1, _⟩ => spinorKron3Z spinorAZ spinorIxZ spinorZZ
  | ⟨2, _⟩ => spinorKron3Z spinorAZ spinorAZ spinorAZ
  | ⟨3, _⟩ => spinorKron3Z spinorIxZ spinorXZ spinorAZ
  | ⟨4, _⟩ => spinorKron3Z spinorIxZ spinorZZ spinorAZ
  | ⟨5, _⟩ => spinorKron3Z spinorXZ spinorAZ spinorIxZ

def spinorGammaMonomialMatZ (m : Fin 64) : Matrix (Fin 8) (Fin 8) ℤ :=
  (cl06SpinorGammaMaskFinset m).sort (· ≤ ·)|>.foldl
    (fun A i => A * cl06SpinorGammaMatZ i) (1 : Matrix (Fin 8) (Fin 8) ℤ)

/-! ## Cast lemmas (`algebraMap ℤ ℝ`) -/

theorem spinorKron3Z_map (A B C : Matrix (Fin 2) (Fin 2) ℤ) :
    (spinorKron3Z A B C).map (algebraMap ℤ ℝ) =
      spinorKron3 (A.map (algebraMap ℤ ℝ)) (B.map (algebraMap ℤ ℝ)) (C.map (algebraMap ℤ ℝ)) := by
  ext i j
  simp only [spinorKron3Z, spinorKron3, Matrix.map_apply, map_mul]

theorem spinorIxZ_map : spinorIxZ.map (algebraMap ℤ ℝ) = spinorIx := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [spinorIxZ, spinorIx, Matrix.map_apply, map_one, map_zero]

theorem spinorXZ_map : spinorXZ.map (algebraMap ℤ ℝ) = spinorX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [spinorXZ, spinorX, Matrix.map_apply, map_one, map_zero]

theorem spinorZZ_map : spinorZZ.map (algebraMap ℤ ℝ) = spinorZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [spinorZZ, spinorZ, Matrix.map_apply, map_one, map_zero, map_neg]

theorem spinorAZ_map : spinorAZ.map (algebraMap ℤ ℝ) = spinorA := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [spinorAZ, spinorA, Matrix.map_apply, map_one, map_zero, map_neg]

theorem cl06SpinorGammaMatZ_map (k : Fin 6) :
    (cl06SpinorGammaMatZ k).map (algebraMap ℤ ℝ) = cl06SpinorGammaMat k := by
  fin_cases k <;>
    (simp only [cl06SpinorGammaMatZ, cl06SpinorGammaMat]; rw [spinorKron3Z_map]; simp only
      [spinorAZ_map, spinorIxZ_map, spinorXZ_map, spinorZZ_map])

end Hqiv.Algebra
