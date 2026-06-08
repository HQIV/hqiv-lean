import Hqiv.Physics.QuarkColorCarrierGaugeScaffold
import Hqiv.Physics.StrongColorSu3ChartClosure
import Hqiv.Algebra.WeakInComplexStructure

/-!
# Strong color sector: carrier closure (EW-style `B` embed + Lie bracket)

`QuarkColorCarrierGaugeScaffold` fixes the abstract `Fin 3 → ℂ` chart, inclusion into
`WeakComplexOctonionCarrier`, and half Gell–Mann matrices on the **active** `3 × 3` chart.

This module closes the sector in the **same sense** as `weakPauliEmbed` in
`Hqiv.Algebra.WeakInComplexStructure`:

* **`colorTripletB`** — `8 × 3` matrix whose columns are the orthonormal coordinate directions on
  octonion slots `2,3,4` (coefficient vectors of `colorTripletInclCoeff` for the standard basis).
  Satisfies **`colorTripletBᴴ * colorTripletB = 1₃`** and **`colorTripletB.mulVec ψ = colorTripletInclCoeff ψ`**.
* **`colorGellMannEmbed`** — conjugate any `3 × 3` operator into `8 × 8` on the carrier:
  `M ↦ colorTripletB * M * colorTripletBᴴ`.
* **Multiplication / Lie closure on the carrier** — `colorGellMannEmbed_mul` and
  `colorGellMannEmbed_lieBracket` mirror `weakPauliEmbed_mul` / `weakPauliEmbed_lieBracket`.
* **Intertwining with inclusion** — `colorGellMannEmbed_mulVec_intertwine` packages the same
  `B.mulVec (M.mulVec v) = (B M Bᴴ).mulVec (B.mulVec v)` identity used for Pauli.

The existing one-line commutator on the chart (`colorHalfGellMann_comm_12`) then **lifts** to the
carrier by `colorGellMannEmbed_lieBracket` (see `colorGellMannEmbed_halfGellMann_comm_12`).

Full eight-generator data (`colorHalfGellMannFull`, `colorSu3fStructure`, `colorTripletCovariantTermFull`)
lives in `Hqiv.Physics.StrongColorSu3ChartClosure`. The generic lift
`colorGellMannEmbed_chart_lieBracket_smul` packages any future chart identity
`lieBracketMat₃ A B = Complex.I • R` into the same normalisation on the carrier.
-/

open scoped BigOperators InnerProductSpace
open Complex Finset Matrix EuclideanSpace PiLp WithLp
open Hqiv.Algebra

namespace Hqiv.Physics

noncomputable section

/-- `8 × 3` matrix: orthonormal columns supported on `colorTripletOctonionSlot 0,1,2` (= rows `2,3,4`). -/
noncomputable def colorTripletB : Matrix (Fin 8) (Fin 3) ℂ :=
  Matrix.of fun (r : Fin 8) (c : Fin 3) => if r = colorTripletOctonionSlot c then (1 : ℂ) else 0

theorem colorTripletB_mulVec_eq_colorTripletInclCoeff (ψ : Fin 3 → ℂ) :
    colorTripletB.mulVec ψ = colorTripletInclCoeff ψ := by
  funext r
  fin_cases r <;> simp [colorTripletB, Matrix.mulVec, dotProduct, colorTripletInclCoeff,
    colorTripletOctonionSlot, Fin.sum_univ_three]

theorem colorTripletB_conjTranspose_mul_self : colorTripletBᴴ * colorTripletB = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorTripletB, Matrix.conjTranspose, Matrix.mul_apply, Matrix.of_apply, colorTripletOctonionSlot,
      mul_ite, mul_one, mul_zero]

/-- Conjugate an abstract `3 × 3` color operator into an `8 × 8` operator on the octonion carrier. -/
noncomputable def colorGellMannEmbed (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  colorTripletB * M * colorTripletBᴴ

theorem colorGellMannEmbed_map_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorTripletB * A * colorTripletBᴴ * colorTripletB * B * colorTripletBᴴ =
      colorTripletB * (A * B) * colorTripletBᴴ := by
  rw [Matrix.mul_assoc (colorTripletB * A), colorTripletB_conjTranspose_mul_self, Matrix.mul_one,
    Matrix.mul_assoc colorTripletB A B]

theorem colorGellMannEmbed_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed A * colorGellMannEmbed B = colorGellMannEmbed (A * B) := by
  simpa [colorGellMannEmbed, Matrix.mul_assoc] using colorGellMannEmbed_map_mul A B

theorem colorGellMannEmbed_map_sub (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed (A - B) = colorGellMannEmbed A - colorGellMannEmbed B := by
  simp [colorGellMannEmbed, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

theorem colorGellMannEmbed_lieBracket (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed (lieBracketMat₃ A B) = lieBracketMat₈ (colorGellMannEmbed A) (colorGellMannEmbed B) := by
  simp [lieBracketMat₃, lieBracketMat₈, colorGellMannEmbed_map_sub, colorGellMannEmbed_mul]

theorem colorGellMannEmbed_mulVec_intertwine (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) :
    colorTripletB.mulVec (M.mulVec v) = (colorGellMannEmbed M).mulVec (colorTripletB.mulVec v) := by
  unfold colorGellMannEmbed
  have hmat :
      colorTripletB * M = colorTripletB * M * colorTripletBᴴ * colorTripletB := by
    simp [Matrix.mul_assoc, colorTripletB_conjTranspose_mul_self]
  calc
    colorTripletB.mulVec (M.mulVec v) = (colorTripletB * M).mulVec v := Matrix.mulVec_mulVec v colorTripletB M
    _ = (colorTripletB * M * colorTripletBᴴ * colorTripletB).mulVec v := by rw [← hmat]
    _ = (colorTripletB * M * colorTripletBᴴ).mulVec (colorTripletB.mulVec v) :=
      (Matrix.mulVec_mulVec v (colorTripletB * M * colorTripletBᴴ) colorTripletB).symm

theorem colorGellMannEmbed_mulVec_inclCoeff (M : Matrix (Fin 3) (Fin 3) ℂ) (ψ : Fin 3 → ℂ) :
    (colorGellMannEmbed M).mulVec (colorTripletInclCoeff ψ) = colorTripletInclCoeff (M.mulVec ψ) := by
  simpa [← colorTripletB_mulVec_eq_colorTripletInclCoeff ψ,
    ← colorTripletB_mulVec_eq_colorTripletInclCoeff (M.mulVec ψ)] using
    (colorGellMannEmbed_mulVec_intertwine M ψ).symm

/-- Embedded triplet on the carrier transforms under `colorGellMannEmbed M` like the abstract chart. -/
theorem colorGellMannEmbed_mulVec_colorTripletToCarrier (M : Matrix (Fin 3) (Fin 3) ℂ) (ψ : Fin 3 → ℂ) :
    toLp 2 ((colorGellMannEmbed M).mulVec (colorTripletInclCoeff ψ)) = colorTripletToCarrier (M.mulVec ψ) := by
  simp [colorTripletToCarrier, colorGellMannEmbed_mulVec_inclCoeff M ψ]

theorem colorGellMannEmbed_smul (c : ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    colorGellMannEmbed (c • M) = c • colorGellMannEmbed M := by
  simp [colorGellMannEmbed, Matrix.mul_smul, Matrix.smul_mul]

/-- Lift a chart commutator `lieBracketMat₃ A B = Complex.I • R` to the carrier (`8 × 8`). -/
theorem colorGellMannEmbed_chart_lieBracket_smul {A B R : Matrix (Fin 3) (Fin 3) ℂ}
    (h : lieBracketMat₃ A B = Complex.I • R) :
    lieBracketMat₈ (colorGellMannEmbed A) (colorGellMannEmbed B) = Complex.I • colorGellMannEmbed R := by
  calc
    lieBracketMat₈ (colorGellMannEmbed A) (colorGellMannEmbed B)
        = colorGellMannEmbed (lieBracketMat₃ A B) := (colorGellMannEmbed_lieBracket A B).symm
    _ = colorGellMannEmbed (Complex.I • R) := by rw [h]
    _ = Complex.I • colorGellMannEmbed R := colorGellMannEmbed_smul Complex.I R

theorem colorGellMannEmbed_halfGellMann_comm_12 :
    lieBracketMat₈ (colorGellMannEmbed (colorHalfGellMann 0)) (colorGellMannEmbed (colorHalfGellMann 1)) =
      Complex.I • colorGellMannEmbed (colorHalfGellMann 2) := by
  have hlb : lieBracketMat₃ (colorHalfGellMann 0) (colorHalfGellMann 1) = Complex.I • colorHalfGellMann 2 := by
    simpa [lieBracketMat₃] using colorHalfGellMann_comm_12
  calc
    lieBracketMat₈ (colorGellMannEmbed (colorHalfGellMann 0)) (colorGellMannEmbed (colorHalfGellMann 1))
        = colorGellMannEmbed (lieBracketMat₃ (colorHalfGellMann 0) (colorHalfGellMann 1)) :=
          (colorGellMannEmbed_lieBracket (colorHalfGellMann 0) (colorHalfGellMann 1)).symm
    _ = colorGellMannEmbed (Complex.I • colorHalfGellMann 2) := by rw [hlb]
    _ = Complex.I • colorGellMannEmbed (colorHalfGellMann 2) := colorGellMannEmbed_smul Complex.I _

end -- noncomputable section

end Hqiv.Physics
