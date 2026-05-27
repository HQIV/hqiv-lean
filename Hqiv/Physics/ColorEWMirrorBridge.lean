import Hqiv.Algebra.G2Embedding
import Hqiv.Physics.StrongColorCarrierClosure

/-!
# Color as the EW-style gauge-on-carrier mirror

This module is deliberately a **bookkeeping bridge**.  It records that the color sector now follows the
same formal carrier pattern as the electroweak sector:

| role | electroweak side | color side |
| --- | --- | --- |
| abstract chart | `Fin 2 → ℂ` | `Fin 3 → ℂ` |
| carrier column matrix | `Hqiv.Algebra.weakDoubletB` | `colorTripletB` |
| coefficient inclusion | `Hqiv.Algebra.weakDoubletInclCoeff` | `colorTripletInclCoeff` |
| embedded generators | `Hqiv.Algebra.weakPauliEmbed` | `colorGellMannEmbed` |
| chart Lie data | Pauli commutators in `Hqiv.Algebra.WeakInComplexStructure` | Gell-Mann chart data in `StrongColorSu3ChartClosure` |

The theorems below do not re-prove any `su(3)` closure table.  They only package existing facts:
orthonormal `BᴴB = 1`, slot-disjoint coefficient inclusions, carrier/chart intertwining, and Lie-bracket
lifting by conjugation.

**Honest obstruction.**  Importing `Hqiv.Algebra.G2Embedding` here is only a pointer to the next layer:
this file does **not** claim `𝔰𝔲(3) ⊂ 𝔤₂`, does **not** prove a span inclusion into the `g₂Generator`
family, and does **not** prove the representation split `8 = 3 ⊕ 3̄ ⊕ 1 ⊕ 1`.  The next missing theorem is
a span-level bridge from embedded color generators to the octonion-derived `G₂` layer fixing the preferred
axis.

The probe at the bottom records one concrete obstruction for the present chart: the anti-Hermitian
embedded `λ₂/2` color action is **not** in the complex span of the current 14 `g2Generator` matrices.
That is evidence that the eventual `G₂ ⊃ SU(3)` bridge needs an alignment/conjugation step, not a direct
reuse of this coordinate chart.
-/

open scoped BigOperators InnerProductSpace
open Complex Finset Matrix EuclideanSpace PiLp WithLp
open Hqiv.Algebra

namespace Hqiv.Physics

noncomputable section

/-- One row in the EW/color carrier analogy table. -/
structure ColorEWMirrorRow where
  role : String
  electroweak : String
  color : String
deriving Repr, DecidableEq

/-- The bookkeeping table: weak doublet chart and color triplet chart are parallel carrier packages. -/
def colorEWMirrorAnalogyTable : List ColorEWMirrorRow :=
  [ { role := "abstract chart", electroweak := "Fin 2 -> C", color := "Fin 3 -> C" }
  , { role := "carrier column matrix", electroweak := "weakDoubletB", color := "colorTripletB" }
  , { role := "coefficient inclusion", electroweak := "weakDoubletInclCoeff", color := "colorTripletInclCoeff" }
  , { role := "embedded generators", electroweak := "weakPauliEmbed", color := "colorGellMannEmbed" }
  ]

/-- Both carrier column matrices are isometries on their active charts (`BᴴB = 1`). -/
theorem colorEWMirror_B_conjTranspose_mul_self :
    weakDoubletBᴴ * weakDoubletB = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      colorTripletBᴴ * colorTripletB = (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  ⟨weakDoubletB_conjTranspose_mul_self, colorTripletB_conjTranspose_mul_self⟩

/-- The color triplet coefficient inclusion is zero on the weak chart slots `0,1`. -/
theorem colorTripletInclCoeff_zero_on_weak_slots (ψ : Fin 3 → ℂ) (i : Fin 8) (h : (i : ℕ) < 2) :
    colorTripletInclCoeff ψ i = 0 := by
  fin_cases i <;> simp [colorTripletInclCoeff] at h ⊢

/-- The weak coefficient inclusion is zero on the color triplet slots `2,3,4`. -/
theorem weakDoubletInclCoeff_zero_on_color_slots (v : Fin 2 → ℂ) (c : Fin 3) :
    weakDoubletInclCoeff v (colorTripletOctonionSlot c) = 0 := by
  fin_cases c <;> simp [weakDoubletInclCoeff, colorTripletOctonionSlot]

/-- The coordinate weak-doublet chart and color-triplet chart are orthogonal in the shared carrier. -/
theorem colorEWMirror_coeff_inclusions_orthogonal (v : Fin 2 → ℂ) (ψ : Fin 3 → ℂ) :
    weakCarrierCinner (weakDoubletInclusion v) (colorTripletToCarrier ψ) = 0 := by
  rw [weakCarrierCinner_eq_inner]
  dsimp only [weakDoubletInclusion, colorTripletToCarrier]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct]
  rw [Fin.sum_univ_eight]
  simp [weakDoubletInclCoeff, colorTripletInclCoeff]

/-- Weak Pauli and color Gell-Mann carrier embeddings both intertwine chart multiplication with `B`. -/
theorem colorEWMirror_mulVec_intertwine_pattern :
    (∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ),
        weakDoubletB.mulVec (M.mulVec v) = (weakPauliEmbed M).mulVec (weakDoubletB.mulVec v)) ∧
      (∀ (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ),
        colorTripletB.mulVec (M.mulVec v) = (colorGellMannEmbed M).mulVec (colorTripletB.mulVec v)) :=
  ⟨weakPauliEmbed_mulVec_intertwine, colorGellMannEmbed_mulVec_intertwine⟩

/-- Weak Pauli and color Gell-Mann carrier embeddings both lift chart Lie brackets by conjugation. -/
theorem colorEWMirror_lieBracket_lift_pattern :
    (∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
        weakPauliEmbed (lieBracketMat₂ A B) = lieBracketMat₈ (weakPauliEmbed A) (weakPauliEmbed B)) ∧
      (∀ A B : Matrix (Fin 3) (Fin 3) ℂ,
        colorGellMannEmbed (lieBracketMat₃ A B) =
          lieBracketMat₈ (colorGellMannEmbed A) (colorGellMannEmbed B)) :=
  ⟨weakPauliEmbed_lieBracket, colorGellMannEmbed_lieBracket⟩

/-! ## Option-B probe: a direct chart-to-`G₂` span obstruction -/

/-- Sparse entry functional used to test the current `G₂` chart against the embedded color chart. -/
def colorG2ProbeFunctional (M : Matrix (Fin 8) (Fin 8) ℂ) : ℂ :=
  2 * M 0 1 + 2 * M 0 5 - M 1 4 + M 2 3

/-- The same sparse entry probe as a complex-linear functional. -/
def colorG2ProbeLinear : Matrix (Fin 8) (Fin 8) ℂ →ₗ[ℂ] ℂ where
  toFun := colorG2ProbeFunctional
  map_add' A B := by
    simp [colorG2ProbeFunctional]
    ring
  map_smul' c A := by
    simp [colorG2ProbeFunctional]
    ring

/-- The probe functional annihilates every current `g2Generator`, after complexifying entries. -/
theorem colorG2ProbeFunctional_g2Generator_zero (k : Fin 14) :
    colorG2ProbeFunctional ((g2Generator k).map Complex.ofReal) = 0 := by
  fin_cases k <;>
    simp [colorG2ProbeFunctional, g2Generator, Hqiv.g2_comm_12, Hqiv.g2_comm_13, Hqiv.g2_comm_14,
      Hqiv.g2_comm_15, Hqiv.g2_comm_16, Hqiv.g2_comm_17, Hqiv.g2_comm_23, Hqiv.g2_comm_24,
      Hqiv.g2_comm_25, Hqiv.g2_comm_26, Hqiv.g2_comm_27, Hqiv.g2_comm_34, Hqiv.g2_comm_35,
      Hqiv.g2_comm_36, Hqiv.lieBracket, Hqiv.octonionLeftMul_1, Hqiv.octonionLeftMul_2,
      Hqiv.octonionLeftMul_3, Hqiv.octonionLeftMul_4, Hqiv.octonionLeftMul_5,
      Hqiv.octonionLeftMul_6, Hqiv.octonionLeftMul_7] <;>
    ring_nf

/-- The same probe detects the anti-Hermitian embedded `λ₂/2` color action. -/
theorem colorG2ProbeFunctional_I_colorGellMann_one :
    colorG2ProbeFunctional (Complex.I • colorGellMannEmbed (colorHalfGellMannFull 1)) = (1 / 2 : ℂ) := by
  simp [colorG2ProbeFunctional, colorGellMannEmbed, colorTripletB, colorTripletOctonionSlot,
    colorHalfGellMannFull, colorGellMannLambdaFull, colorGellMannLambda2, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, Fin.sum_univ_three]
  rw [mul_comm (2⁻¹ : ℂ) Complex.I, ← mul_assoc, Complex.I_mul_I]
  norm_num

theorem colorG2ProbeLinear_I_colorGellMann_one :
    colorG2ProbeLinear (Complex.I • colorGellMannEmbed (colorHalfGellMannFull 1)) = (1 / 2 : ℂ) :=
  colorG2ProbeFunctional_I_colorGellMann_one

/--
Option-B probe result: in the present coordinates, the anti-Hermitian embedded `λ₂/2` color generator is
not a complex linear combination of the 14 current `g2Generator` matrices.

This is not a no-go theorem for `G₂ ⊃ SU(3)`; it only says the direct chart used by
`colorGellMannEmbed` is not already aligned with the current `G₂` basis.
-/
theorem I_colorGellMannEmbed_one_not_mem_current_g2_span (c : Fin 14 → ℂ) :
    (∑ k : Fin 14, c k • ((g2Generator k).map Complex.ofReal)) ≠
      Complex.I • colorGellMannEmbed (colorHalfGellMannFull 1) := by
  intro h
  have hprobe := congrArg colorG2ProbeLinear h
  have hleft :
      colorG2ProbeLinear (∑ k : Fin 14, c k • ((g2Generator k).map Complex.ofReal)) = 0 := by
    simp [colorG2ProbeLinear, colorG2ProbeFunctional_g2Generator_zero]
  rw [hleft, colorG2ProbeLinear_I_colorGellMann_one] at hprobe
  norm_num at hprobe

end -- noncomputable section

end Hqiv.Physics
