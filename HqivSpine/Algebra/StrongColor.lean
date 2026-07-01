import HqivSpine.Physics.ColorCasimir
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# `HqivSpine.Algebra.StrongColor` — minimal `su(3)` triplet chart

Golfed from legacy `QuarkColorCarrierGaugeScaffold` / `StrongColorSu3ChartClosure`:
Gell–Mann `λ₁,λ₂,λ₃`, half-generators `T^a = λ^a/2`, and the local `su(2)` commutator inside
`su(3)`. The full eight-generator chart, `f^{abc}` table, global Lie law, and matrix-element
pipeline live in `StrongColorSu3`, `StrongColorSu3LieLaw`, and `NonAbelianMatrixElement`.
-/

namespace HqivSpine.Algebra.StrongColor

noncomputable section

open Complex Matrix

/-- `λ₁` (Hermitian). -/
def gellMann1 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 0]

/-- `λ₂` (Hermitian). -/
def gellMann2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0]

/-- `λ₃` (Hermitian). -/
def gellMann3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, -1, 0; 0, 0, 0]

def gellMann (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  match a with
  | 0 => gellMann1
  | 1 => gellMann2
  | 2 => gellMann3

/-- Matrix commutator on the colour triplet chart. -/
def lieBracketMat3 (A B : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  A * B - B * A

/-- Half Gell–Mann generators `T^a = λ^a/2`. -/
def halfGellMann (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 : ℂ) / 2) • gellMann a

/-- The minimal `su(2)` commutator inside `su(3)`: `[T¹,T²] = i T³`. -/
theorem halfGellMann_comm_12 :
    lieBracketMat3 (halfGellMann 0) (halfGellMann 1) = Complex.I • halfGellMann 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lieBracketMat3, halfGellMann, gellMann, gellMann1, gellMann2, gellMann3,
      Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_three, Matrix.of_apply,
      Complex.I_mul_I] <;>
    ring_nf

/-- Sorted structure constant on `(0,1,2)`: `f^{012} = 1`. -/
def fStructure012 : ℝ := 1

/-- Colour rank from foundation: `N_c = transverseDim = 3`. -/
def colourRank : ℕ := HqivSpine.Foundation.transverseDim

theorem colourRank_eq_three : colourRank = 3 := rfl

/-- Schematic covariant term `-i g ∑_a G_a T^a ψ`. -/
def tripletCovariantTerm (g : ℝ) (G : Fin 3 → ℂ) (ψ : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ∑ a : Fin 3, (-Complex.I * (g : ℂ) * G a) • (halfGellMann a).mulVec ψ

structure strongColorTripletDischarged : Prop where
  su2_comm : lieBracketMat3 (halfGellMann 0) (halfGellMann 1) = Complex.I • halfGellMann 2
  colour_rank : colourRank = 3

theorem strongColorTripletDischarged_holds : strongColorTripletDischarged where
  su2_comm := halfGellMann_comm_12
  colour_rank := colourRank_eq_three

end

end HqivSpine.Algebra.StrongColor
