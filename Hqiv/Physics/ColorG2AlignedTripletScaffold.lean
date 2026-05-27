import Hqiv.Physics.ColorEWMirrorBridge

/-!
# `G₂`-axis–aligned complex triplet scaffold (archival probe)

Classical `SU(3) ⊂ G₂` stories fix an imaginary unit (here the HQIV octonion axis `e₇`) and identify a
complex `3`-plane in the complementary `ℝ⁶` by pairing basis vectors.  This file packages one concrete
**orthonormal** `8 × 3` embed matrix `g2AlignedTripletB` whose columns are the three normalized complex
lines

`(e₁ + Complex.I * e₆) / √2`, `(e₂ + Complex.I * e₅) / √2`, `(e₃ + Complex.I * e₄) / √2`

on `Fin 8` coefficient indices matching `Hqiv.Algebra.octonionBasis`.

**What is proved (bookkeeping + one probe identity).**

* `g2AlignedTripletBᴴ * g2AlignedTripletB = 1₃` and the same `B M Bᴴ` conjugation API as
  `colorGellMannEmbed` (`g2AlignedGellMannEmbed_mul`, `g2AlignedGellMannEmbed_lieBracket`, …).
* The sparse `colorG2ProbeFunctional` from `ColorEWMirrorBridge` **vanishes** on
  `Complex.I • g2AlignedGellMannEmbed (colorHalfGellMannFull 1)` (embedded anti-Hermitian `λ₂/2` in this
  aligned chart).

**Honest status (not proved here).**

* Probe zero is **necessary but not sufficient** for membership in the complex span of the `14` current
  `g2Generator` matrices.  Separately, a numeric least-squares check on the real `8 × 8` commutator basis
  suggests the aligned embedded `Complex.I • T²` matrix is **still not** a real linear combination of
  those `14` generators — so alignment removes the *specific* linear obstruction used in
  `I_colorGellMannEmbed_one_not_mem_current_g2_span`, but does **not** by itself close a Lie subalgebra
  identification with `𝔰𝔲(3)`.

This module is intentionally isolated so it can be archived or dropped without disturbing the main
`ColorEWMirrorBridge` certificate cone.
-/

open scoped BigOperators InnerProductSpace
open Complex Finset Matrix EuclideanSpace PiLp WithLp
open Hqiv.Algebra

namespace Hqiv.Physics

noncomputable section

/-- `1 / √2` as a complex scalar (matches the usual `SU(3) ⊂ G₂` complex-line normalisation). -/
noncomputable def g2AlignedInvSqrtTwo : ℂ :=
  (Real.sqrt 2)⁻¹

/-- `8 × 3` matrix: orthonormal columns on the paired imaginary lines `(e₁,e₆)`, `(e₂,e₅)`, `(e₃,e₄)`. -/
noncomputable def g2AlignedTripletB : Matrix (Fin 8) (Fin 3) ℂ :=
  Matrix.of fun (r : Fin 8) (c : Fin 3) =>
    match c with
    | ⟨0, _⟩ =>
        if r = 1 then g2AlignedInvSqrtTwo
        else if r = 6 then Complex.I * g2AlignedInvSqrtTwo else 0
    | ⟨1, _⟩ =>
        if r = 2 then g2AlignedInvSqrtTwo
        else if r = 5 then Complex.I * g2AlignedInvSqrtTwo else 0
    | ⟨2, _⟩ =>
        if r = 3 then g2AlignedInvSqrtTwo
        else if r = 4 then Complex.I * g2AlignedInvSqrtTwo else 0

theorem g2AlignedTripletB_conjTranspose_mul_self :
    g2AlignedTripletBᴴ * g2AlignedTripletB = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have h2 : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
    simp [← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h] at h2
    norm_num at h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, g2AlignedTripletB, g2AlignedInvSqrtTwo,
      Matrix.of_apply, Fin.sum_univ_eight, mul_ite, Complex.conj_ofReal, Complex.conj_I] <;>
    field_simp [hne] <;>
    rw [h2] <;>
    ring_nf <;>
    norm_num

/-- Conjugate a `3 × 3` color chart operator into `8 × 8` along the `g2AlignedTripletB` triplet. -/
noncomputable def g2AlignedGellMannEmbed (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  g2AlignedTripletB * M * g2AlignedTripletBᴴ

theorem g2AlignedGellMannEmbed_map_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    g2AlignedTripletB * A * g2AlignedTripletBᴴ * g2AlignedTripletB * B * g2AlignedTripletBᴴ =
      g2AlignedTripletB * (A * B) * g2AlignedTripletBᴴ := by
  rw [Matrix.mul_assoc (g2AlignedTripletB * A), g2AlignedTripletB_conjTranspose_mul_self, Matrix.mul_one,
    Matrix.mul_assoc g2AlignedTripletB A B]

theorem g2AlignedGellMannEmbed_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    g2AlignedGellMannEmbed A * g2AlignedGellMannEmbed B = g2AlignedGellMannEmbed (A * B) := by
  simpa [g2AlignedGellMannEmbed, Matrix.mul_assoc] using g2AlignedGellMannEmbed_map_mul A B

theorem g2AlignedGellMannEmbed_map_sub (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    g2AlignedGellMannEmbed (A - B) = g2AlignedGellMannEmbed A - g2AlignedGellMannEmbed B := by
  simp [g2AlignedGellMannEmbed, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

theorem g2AlignedGellMannEmbed_lieBracket (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    g2AlignedGellMannEmbed (lieBracketMat₃ A B) =
      lieBracketMat₈ (g2AlignedGellMannEmbed A) (g2AlignedGellMannEmbed B) := by
  simp [lieBracketMat₃, lieBracketMat₈, g2AlignedGellMannEmbed_map_sub, g2AlignedGellMannEmbed_mul]

theorem g2AlignedGellMannEmbed_mulVec_intertwine (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) :
    g2AlignedTripletB.mulVec (M.mulVec v) = (g2AlignedGellMannEmbed M).mulVec (g2AlignedTripletB.mulVec v) := by
  unfold g2AlignedGellMannEmbed
  have hmat :
      g2AlignedTripletB * M = g2AlignedTripletB * M * g2AlignedTripletBᴴ * g2AlignedTripletB := by
    simp [Matrix.mul_assoc, g2AlignedTripletB_conjTranspose_mul_self]
  calc
    g2AlignedTripletB.mulVec (M.mulVec v) = (g2AlignedTripletB * M).mulVec v := Matrix.mulVec_mulVec v g2AlignedTripletB M
    _ = (g2AlignedTripletB * M * g2AlignedTripletBᴴ * g2AlignedTripletB).mulVec v := by rw [← hmat]
    _ = (g2AlignedTripletB * M * g2AlignedTripletBᴴ).mulVec (g2AlignedTripletB.mulVec v) :=
      (Matrix.mulVec_mulVec v (g2AlignedTripletB * M * g2AlignedTripletBᴴ) g2AlignedTripletB).symm

theorem g2AlignedGellMannEmbed_smul (c : ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    g2AlignedGellMannEmbed (c • M) = c • g2AlignedGellMannEmbed M := by
  simp [g2AlignedGellMannEmbed, Matrix.mul_smul, Matrix.smul_mul]

theorem g2AlignedGellMannEmbed_chart_lieBracket_smul {A B R : Matrix (Fin 3) (Fin 3) ℂ}
    (h : lieBracketMat₃ A B = Complex.I • R) :
    lieBracketMat₈ (g2AlignedGellMannEmbed A) (g2AlignedGellMannEmbed B) =
      Complex.I • g2AlignedGellMannEmbed R := by
  calc
    lieBracketMat₈ (g2AlignedGellMannEmbed A) (g2AlignedGellMannEmbed B)
        = g2AlignedGellMannEmbed (lieBracketMat₃ A B) := (g2AlignedGellMannEmbed_lieBracket A B).symm
    _ = g2AlignedGellMannEmbed (Complex.I • R) := by rw [h]
    _ = Complex.I • g2AlignedGellMannEmbed R := g2AlignedGellMannEmbed_smul Complex.I R

/-! ## Same `G₂` probe as `ColorEWMirrorBridge`: obstruction cleared on this alignment -/

theorem colorG2ProbeFunctional_I_g2AlignedGellMannEmbed_halfGellMannFull_one :
    colorG2ProbeFunctional (Complex.I • g2AlignedGellMannEmbed (colorHalfGellMannFull 1)) = 0 := by
  rw [colorHalfGellMannFull_one]
  simp [colorG2ProbeFunctional, g2AlignedGellMannEmbed, g2AlignedTripletB, g2AlignedInvSqrtTwo,
    colorHalfGellMann, colorGellMannLambda2, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fin.sum_univ_three, mul_zero, add_zero, zero_add, zero_mul]

end -- noncomputable section

end Hqiv.Physics
