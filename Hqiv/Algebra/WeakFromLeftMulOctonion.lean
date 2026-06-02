import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Abel
import Hqiv.OctonionLeftMultiplication
import Hqiv.Algebra.G2Embedding

/-!
# Electroweak-style packaging from left-multiplication matrices

This module records the **Δ–plane / extra-imaginary** linear combinations used in HQIV
sandbox explorations: a real “complex structure” operator built from
`L(e₁)` and `L(e₇)`, and candidate `W⁺`, `W⁻`, `Z` matrices built from the extra
left-multiplications `L(e₂)`, `L(e₃)`, `L(e₄)`.

**What is proved here (structural only).**

* For imaginary units, `L(eᵢ)ᵀ = -L(eᵢ)` (`G2Embedding`), hence
  `J := (L(e₁) - L(e₇)ᵀ)/2` equals `(L(e₁)+L(e₇))/2` and is **skew-symmetric** (so it
  lies in `𝔰𝔬(8)` on the carrier).
* The hypercharge-style combination `Z := L(e₄) - (1/2) L(e₁)` is **skew-symmetric**.

**What is *not* claimed.**

Matrix commutators of the normalized `W⁺`, `W⁻` combinations below do **not**
coincide with rescalings of this `Z` on the frozen `Hqiv.OctonionLeftMultiplication`
tables (verified independently in Python against the same entries). Therefore
this file does **not** assert an `𝔰𝔲(2)` Lie closure for these raw `GL(8,ℝ)`
combinations.

For **proved** `𝔰𝔲(2)_L` generators inside the closed octonion-derived algebra, use
`Hqiv.Algebra.SMEmbedding` (`su2_L_gen_*` built from `g2Generator` commutators).

**Associator / non-associativity.** The octonion associator on vectors is
`Hqiv.Algebra.octonionAssociator` in `OctonionBasics`; it is the correct HQIV hook
for “non-associative correction” at the carrier level. Matrix commutators
`[L(e_i),L(e_j)]` instead span the derivation algebra `𝔤₂ ⊂ 𝔰𝔬(8)`.

**Reference (narrative + numerics):** `HQVM/matrices.py`, `papers/paper/octonion_lightcone_to_oshoracle.tex`
(EW scaffolding paragraph).
-/

open Matrix

namespace Hqiv.Algebra

/-- **Δ-induced complex-structure operator** (matrix form).
Since `L(e₇)ᵀ = -L(e₇)`, this equals `(L(e₁)+L(e₇))/2`. -/
noncomputable def weakComplexStructureJ : Matrix (Fin 8) (Fin 8) ℝ :=
  (1 / 2 : ℝ) • (Hqiv.octonionLeftMul_1 - (Hqiv.octonionLeftMul_7)ᵀ)

theorem weakComplexStructureJ_eq_half_L1_add_L7 :
    weakComplexStructureJ = (1 / 2 : ℝ) • (Hqiv.octonionLeftMul_1 + Hqiv.octonionLeftMul_7) := by
  unfold weakComplexStructureJ
  have h :
      Hqiv.octonionLeftMul_1 - (Hqiv.octonionLeftMul_7)ᵀ =
        Hqiv.octonionLeftMul_1 + Hqiv.octonionLeftMul_7 := by
    rw [leftMul_7_antisymm, sub_neg_eq_add]
  rw [h]

theorem weakComplexStructureJ_skew : weakComplexStructureJ + weakComplexStructureJᵀ = 0 := by
  rw [weakComplexStructureJ_eq_half_L1_add_L7]
  rw [transpose_smul, transpose_add, leftMul_1_antisymm, leftMul_7_antisymm]
  rw [← smul_add]
  have hsum :
      Hqiv.octonionLeftMul_1 + Hqiv.octonionLeftMul_7 + (-Hqiv.octonionLeftMul_1 + -Hqiv.octonionLeftMul_7) = 0 := by
    abel
  rw [hsum, smul_zero]

/-- Candidate `W⁺` from `L(e₂) ± J·L(e₃)` with the usual `1/√2` normalization. -/
noncomputable def weakWplusFromLeftMul : Matrix (Fin 8) (Fin 8) ℝ :=
  (Real.sqrt 2)⁻¹ • (Hqiv.octonionLeftMul_2 + weakComplexStructureJ * Hqiv.octonionLeftMul_3)

/-- Candidate `W⁻` (minus sign between the two terms). -/
noncomputable def weakWminusFromLeftMul : Matrix (Fin 8) (Fin 8) ℝ :=
  (Real.sqrt 2)⁻¹ • (Hqiv.octonionLeftMul_2 - weakComplexStructureJ * Hqiv.octonionLeftMul_3)

/-- Candidate neutral generator `L(e₄) - (1/2) L(e₁)` (hypercharge-mixing narrative). -/
noncomputable def weakZFromLeftMul : Matrix (Fin 8) (Fin 8) ℝ :=
  Hqiv.octonionLeftMul_4 - (1 / 2 : ℝ) • Hqiv.octonionLeftMul_1

theorem weakZFromLeftMul_skew : weakZFromLeftMul + weakZFromLeftMulᵀ = 0 := by
  unfold weakZFromLeftMul
  rw [transpose_sub, transpose_smul, leftMul_4_antisymm, leftMul_1_antisymm, smul_neg]
  abel

end Hqiv.Algebra
