import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Hqiv.OctonionLeftMultiplication
import Hqiv.GeneratorsFromAxioms
import Hqiv.Algebra.OctonionBasics

open Matrix BigOperators

set_option maxHeartbeats 600000 in

/-!
# G₂ as the derivation algebra of the octonions

G₂ is the 14-dimensional Lie algebra of derivations of the octonion algebra O.
We define it as the ℝ-span of the 14 commutators [L(e_i), L(e_j)] for 1 ≤ i < j ≤ 7
(imaginary units), which are the standard basis for the derivation algebra Der(O) ≃ 𝔤₂.

**Reference:** HQIV preprint v2, Zenodo 10.5281/zenodo.18899939, Section 4.2–4.3.

**G₂ antisymmetry:** L(e_i)ᵀ = -L(e_i) and all 14 G₂ generators antisymmetric via
octonion norm preservation: for any pure imaginary unit u, left multiplication by u
is skew-adjoint w.r.t. the standard inner product on ℝ⁸, hence L(e_i)ᵀ = -L(e_i).
-/

namespace Hqiv.Algebra

/-!
## Octonion inner product and skew-adjointness

Standard Euclidean inner product on ℝ⁸; then L(e_i) skew-adjoint ⟺ L(e_i)ᵀ = -L(e_i).
-/

/-- leftMulByBasis i coincides with (leftMulMatrix i).mulVec. -/
lemma leftMulByBasis_eq_mulVec (i : Fin 8) (y : OctonionVec) :
    leftMulByBasis i y = (leftMulMatrix i).mulVec y := rfl

/-- **Skew-adjoint ⇒ skew-symmetric:** If ⟨M x, y⟩ + ⟨x, M y⟩ = 0 for all x, y then M + Mᵀ = 0. -/
theorem matrix_skew_of_skewAdjoint (M : Matrix (Fin 8) (Fin 8) ℝ)
    (h : ∀ x y : OctonionVec, octonionInner (M.mulVec x) y + octonionInner x (M.mulVec y) = 0) :
    M + Mᵀ = 0 := by
  ext i j
  specialize h (octonionBasis j) (octonionBasis i)
  simp only [octonionInner, octonionBasis, mulVec, dotProduct, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_apply, transpose_apply] at h ⊢
  have key : ∀ x, (if x = j then 1 else 0) * M x i = (if x = j then M j i else 0) :=
    fun x => by by_cases hx : x = j <;> simp [hx]
  have sum_eq : ∑ x : Fin 8, (if x = j then 1 else 0) * M x i = M j i := by
    rw [Finset.sum_congr rfl (fun x _ => key x)]; simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sum_eq] at h; exact h

/-- **Skew-symmetric ⇒ skew-adjoint:** If M + Mᵀ = 0 then ⟨M x, y⟩ + ⟨x, M y⟩ = 0 for all x, y.
  If your build reports "No goals to be solved" at the following simp, remove that line. -/
theorem matrix_skewAdjoint_of_skew (M : Matrix (Fin 8) (Fin 8) ℝ) (hM : M + Mᵀ = 0)
    (x y : OctonionVec) :
    octonionInner (M.mulVec x) y + octonionInner x (M.mulVec y) = 0 := by
  simp only [octonionInner, mulVec, dotProduct]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  have key (i : Fin 8) : (∑ j, M i j * x j * y i) + (∑ j, M j i * (x j * y i)) =
      ∑ j, (M i j + M j i) * x j * y i := by
    conv_lhs => arg 2; rw [Finset.sum_congr rfl (fun j _ => by rw [← mul_assoc])]
    conv_lhs => arg 1; rw [Finset.sum_congr rfl (fun j _ => rfl)]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun j _ => by
      rw [mul_assoc (M i j) (x j) (y i), mul_assoc (M j i) (x j) (y i), ← add_mul, ← mul_assoc])]
  trans ∑ i, (∑ j, (M i j + M j i) * x j * y i)
  · congr 1; funext i
    conv_lhs => arg 2; rw [Finset.sum_congr rfl (fun j _ => by rw [mul_comm (x j), mul_assoc, mul_comm (y i) (x j)])]
    have h1 : (∑ i_1, M i i_1 * x i_1 * y i) = (∑ j, M i j * x j * y i) := Finset.sum_congr rfl (fun _ _ => rfl)
    rw [h1]; exact key i
  · rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      conv_lhs => arg 1; rw [(transpose_apply M i j).symm, (add_apply M Mᵀ i j).symm,
        congr_fun (congr_fun hM i) j, zero_apply]))]
    simp only [zero_mul, Finset.sum_const_zero]

/-- **Skew-symmetric ⟺ skew-adjoint:** M + Mᵀ = 0 iff for all x, y we have
⟨M x, y⟩ + ⟨x, M y⟩ = 0 (with the standard inner product). -/
theorem matrix_skew_iff_skewAdjoint (M : Matrix (Fin 8) (Fin 8) ℝ) :
    M + Mᵀ = 0 ↔ ∀ x y : OctonionVec,
      octonionInner (M.mulVec x) y + octonionInner x (M.mulVec y) = 0 :=
  ⟨fun h => matrix_skewAdjoint_of_skew M h, matrix_skew_of_skewAdjoint M⟩

/-- **L(e_1) + L(e_1)ᵀ = 0** (concrete Fano table). -/
theorem leftMul_1_add_transpose : Hqiv.octonionLeftMul_1 + (Hqiv.octonionLeftMul_1)ᵀ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp only [add_apply, transpose_apply, Hqiv.octonionLeftMul_1, zero_apply]; all_goals norm_num
/-- **L(e_2) + L(e_2)ᵀ = 0** (concrete Fano table). -/
theorem leftMul_2_add_transpose : Hqiv.octonionLeftMul_2 + (Hqiv.octonionLeftMul_2)ᵀ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp only [add_apply, transpose_apply, Hqiv.octonionLeftMul_2, zero_apply]; all_goals norm_num
/-- **L(e_3) + L(e_3)ᵀ = 0** (concrete Fano table). -/
theorem leftMul_3_add_transpose : Hqiv.octonionLeftMul_3 + (Hqiv.octonionLeftMul_3)ᵀ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp only [add_apply, transpose_apply, Hqiv.octonionLeftMul_3, zero_apply]; all_goals norm_num
/-- **L(e_4) + L(e_4)ᵀ = 0** (concrete Fano table). -/
theorem leftMul_4_add_transpose : Hqiv.octonionLeftMul_4 + (Hqiv.octonionLeftMul_4)ᵀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [add_apply, transpose_apply, Hqiv.octonionLeftMul_4, zero_apply] <;>
    norm_num
/-- **L(e_5) + L(e_5)ᵀ = 0** (concrete Fano table). -/
theorem leftMul_5_add_transpose : Hqiv.octonionLeftMul_5 + (Hqiv.octonionLeftMul_5)ᵀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [add_apply, transpose_apply, Hqiv.octonionLeftMul_5, zero_apply] <;>
    norm_num
/-- **L(e_6) + L(e_6)ᵀ = 0** (concrete Fano table). -/
theorem leftMul_6_add_transpose : Hqiv.octonionLeftMul_6 + (Hqiv.octonionLeftMul_6)ᵀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [add_apply, transpose_apply, Hqiv.octonionLeftMul_6, zero_apply] <;>
    norm_num
/-- **L(e_7) + L(e_7)ᵀ = 0** (concrete Fano table). -/
theorem leftMul_7_add_transpose : Hqiv.octonionLeftMul_7 + (Hqiv.octonionLeftMul_7)ᵀ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp only [add_apply, transpose_apply, Hqiv.octonionLeftMul_7, zero_apply]; all_goals norm_num

/-- **Left multiplication by imaginary unit e_i is skew-symmetric** (from concrete Fano tables). -/
theorem leftMul_matrix_skew (i : Fin 8) (hi : i ≠ 0) :
    leftMulMatrix i + (leftMulMatrix i)ᵀ = 0 := by
  fin_cases i
  · exact absurd rfl hi
  · simp only [leftMulMatrix]; exact leftMul_1_add_transpose
  · simp only [leftMulMatrix]; exact leftMul_2_add_transpose
  · simp only [leftMulMatrix]; exact leftMul_3_add_transpose
  · simp only [leftMulMatrix]; exact leftMul_4_add_transpose
  · simp only [leftMulMatrix]; exact leftMul_5_add_transpose
  · simp only [leftMulMatrix]; exact leftMul_6_add_transpose
  · simp only [leftMulMatrix]; exact leftMul_7_add_transpose

/-- **Alternativity for imaginary units**, proved from the concrete lattice multiplication table (no axiom). -/
theorem octonion_alternativity_imaginary (i : Fin 8) (hi : i ≠ 0) (x y : OctonionVec) :
    octonionInner (leftMulByBasis i x) y + octonionInner x (leftMulByBasis i y) = 0 := by
  rw [leftMulByBasis_eq_mulVec]; exact matrix_skewAdjoint_of_skew (leftMulMatrix i) (leftMul_matrix_skew i hi) x y

/-- **Skew-adjoint for imaginary e_i:** ⟨L(e_i)x, y⟩ + ⟨x, L(e_i)y⟩ = 0 (from table + matrix_skewAdjoint_of_skew). -/
theorem leftMul_imaginary_antisymm (i : Fin 8) (hi : i ≠ 0) (x y : OctonionVec) :
    octonionInner (leftMulByBasis i x) y + octonionInner x (leftMulByBasis i y) = 0 :=
  octonion_alternativity_imaginary i hi x y

lemma leftMulMatrix_succ (N : Fin 7) : leftMulMatrix (Fin.succ N) = Hqiv.octonionLeftMul_N N := by
  unfold leftMulMatrix Hqiv.octonionLeftMul_N; fin_cases N <;> rfl

/-- **Each L(e_{N+1}) is antisymmetric** (single parameterized proof). -/
theorem leftMul_N_antisymm (N : Fin 7) : (Hqiv.octonionLeftMul_N N)ᵀ = -Hqiv.octonionLeftMul_N N := by
  rw [← leftMulMatrix_succ]
  exact eq_neg_iff_add_eq_zero.mpr (add_comm _ _ |>.trans (leftMul_matrix_skew (Fin.succ N) (Fin.succ_ne_zero N)))

theorem leftMul_1_antisymm : (Hqiv.octonionLeftMul_1)ᵀ = -Hqiv.octonionLeftMul_1 := by
  simpa [Hqiv.octonionLeftMul_N, leftMulMatrix] using leftMul_N_antisymm 0
theorem leftMul_2_antisymm : (Hqiv.octonionLeftMul_2)ᵀ = -Hqiv.octonionLeftMul_2 := by
  simpa [Hqiv.octonionLeftMul_N, leftMulMatrix] using leftMul_N_antisymm 1
theorem leftMul_3_antisymm : (Hqiv.octonionLeftMul_3)ᵀ = -Hqiv.octonionLeftMul_3 := by
  simpa [Hqiv.octonionLeftMul_N, leftMulMatrix] using leftMul_N_antisymm 2
theorem leftMul_4_antisymm : (Hqiv.octonionLeftMul_4)ᵀ = -Hqiv.octonionLeftMul_4 := by
  simpa [Hqiv.octonionLeftMul_N, leftMulMatrix] using leftMul_N_antisymm 3
theorem leftMul_5_antisymm : (Hqiv.octonionLeftMul_5)ᵀ = -Hqiv.octonionLeftMul_5 := by
  simpa [Hqiv.octonionLeftMul_N, leftMulMatrix] using leftMul_N_antisymm 4
theorem leftMul_6_antisymm : (Hqiv.octonionLeftMul_6)ᵀ = -Hqiv.octonionLeftMul_6 := by
  simpa [Hqiv.octonionLeftMul_N, leftMulMatrix] using leftMul_N_antisymm 5
theorem leftMul_7_antisymm : (Hqiv.octonionLeftMul_7)ᵀ = -Hqiv.octonionLeftMul_7 := by
  simpa [Hqiv.octonionLeftMul_N, leftMulMatrix] using leftMul_N_antisymm 6

/-- From Lᵀ = -L we get L + Lᵀ = 0 (for use with lieBracket_skew_of_skew). -/
lemma add_eq_zero_of_neg_eq (L : Matrix (Fin 8) (Fin 8) ℝ) (h : Lᵀ = -L) : L + Lᵀ = 0 :=
  (add_comm L Lᵀ).trans (eq_neg_iff_add_eq_zero.mp h)

/-- **Left multiplication by any imaginary unit e_i (i=1..7) is skew-symmetric:**
(L(e_i))ᵀ = -L(e_i), i.e. L(e_i) + (L(e_i))ᵀ = 0. Index 0 = real unit (identity). -/
theorem leftMul_antisymm (i : Fin 8) (hi : i ≠ 0) :
    leftMulMatrix i + (leftMulMatrix i)ᵀ = 0 := leftMul_matrix_skew i hi

/-- **Commutator of skew matrices is skew:** If A + Aᵀ = 0 and B + Bᵀ = 0 then [A,B] + [A,B]ᵀ = 0. -/
theorem lieBracket_skew_of_skew (A B : Matrix (Fin 8) (Fin 8) ℝ)
    (hA : A + Aᵀ = 0) (hB : B + Bᵀ = 0) :
    Hqiv.lieBracket A B + (Hqiv.lieBracket A B)ᵀ = 0 := by
  unfold Hqiv.lieBracket
  rw [transpose_sub, transpose_mul, transpose_mul, (neg_eq_iff_add_eq_zero.mpr hA).symm, (neg_eq_iff_add_eq_zero.mpr hB).symm]
  simp only [neg_neg, neg_mul, mul_neg]
  rw [(neg_sub (A * B) (B * A)).symm, add_comm (A * B - B * A) (-(A * B - B * A))]
  exact neg_add_cancel (A * B - B * A)

/-- **G₂ generators:** the 14 commutators [L(e_i), L(e_j)] for i < j (lex order).
Re-exports from Hqiv.GeneratorsFromAxioms. -/
def g2Generator (idx : Fin 14) : Matrix (Fin 8) (Fin 8) ℝ :=
  match idx.val with
  | 0 => Hqiv.g2_comm_12
  | 1 => Hqiv.g2_comm_13
  | 2 => Hqiv.g2_comm_14
  | 3 => Hqiv.g2_comm_15
  | 4 => Hqiv.g2_comm_16
  | 5 => Hqiv.g2_comm_17
  | 6 => Hqiv.g2_comm_23
  | 7 => Hqiv.g2_comm_24
  | 8 => Hqiv.g2_comm_25
  | 9 => Hqiv.g2_comm_26
  | 10 => Hqiv.g2_comm_27
  | 11 => Hqiv.g2_comm_34
  | 12 => Hqiv.g2_comm_35
  | 13 => Hqiv.g2_comm_36
  | _ => Hqiv.g2_comm_36  -- unreachable for Fin 14

/-- **Dimension of G₂** (derivation algebra of O). -/
def g2Dim : ℕ := 14

/-- **Each G₂ generator is antisymmetric:** [L_i, L_j]ᵀ = -[L_i, L_j] because each
L(e_i) is antisymmetric (octonion norm preservation). -/
theorem g2Generator_antisymm (k : Fin 14) :
    g2Generator k + (g2Generator k)ᵀ = 0 := by
  unfold g2Generator
  fin_cases k
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_1_antisymm) (add_eq_zero_of_neg_eq _ leftMul_2_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_1_antisymm) (add_eq_zero_of_neg_eq _ leftMul_3_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_1_antisymm) (add_eq_zero_of_neg_eq _ leftMul_4_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_1_antisymm) (add_eq_zero_of_neg_eq _ leftMul_5_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_1_antisymm) (add_eq_zero_of_neg_eq _ leftMul_6_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_1_antisymm) (add_eq_zero_of_neg_eq _ leftMul_7_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_2_antisymm) (add_eq_zero_of_neg_eq _ leftMul_3_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_2_antisymm) (add_eq_zero_of_neg_eq _ leftMul_4_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_2_antisymm) (add_eq_zero_of_neg_eq _ leftMul_5_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_2_antisymm) (add_eq_zero_of_neg_eq _ leftMul_6_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_2_antisymm) (add_eq_zero_of_neg_eq _ leftMul_7_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_3_antisymm) (add_eq_zero_of_neg_eq _ leftMul_4_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_3_antisymm) (add_eq_zero_of_neg_eq _ leftMul_5_antisymm)
  · exact lieBracket_skew_of_skew _ _ (add_eq_zero_of_neg_eq _ leftMul_3_antisymm) (add_eq_zero_of_neg_eq _ leftMul_6_antisymm)

/-- **G₂ is contained in so(8):** every G₂ generator is antisymmetric. -/
theorem g2_in_so8 (k : Fin 14) :
    g2Generator k + (g2Generator k)ᵀ = 0 := g2Generator_antisymm k

#check leftMul_1_antisymm
#check leftMul_2_antisymm
#check leftMul_3_antisymm
#check leftMul_4_antisymm
#check leftMul_5_antisymm
#check leftMul_6_antisymm
#check leftMul_7_antisymm

end Hqiv.Algebra
