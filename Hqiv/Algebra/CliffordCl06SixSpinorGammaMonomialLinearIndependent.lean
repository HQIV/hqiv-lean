import Hqiv.Algebra.CliffordCl06SixSpinorMonomialMatrixData
import Hqiv.Algebra.CliffordCl06SixStandardSpinorMatLiftSurjective
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Linear independence of the `64` spinor `γ` monomial matrices over `ℝ`

The family `spinorGammaMonomialMat` is linearly independent: row-major flattening identifies each
matrix with a column of a `64 × 64` coordinate matrix `V`, whose Gram matrix `VᵀV` agrees
(entrywise) with `(8 : ℝ) • W` for the normalized Frobenius Gram `W = spinorMonomialGramColumns`
cast to `ℝ`.  Since `det W ≠ 0` over `ℤ`, the cast has nonzero determinant over `ℝ`, hence
`det (VᵀV) ≠ 0`, so `det V ≠ 0` and `V` is invertible.  Injectivity of `mulVec V` then matches the
`GeneratorsLieClosure` / `so8CoordMatrix` pattern.
-/

namespace Hqiv.Algebra

open Equiv Finset Fintype Matrix
open scoped BigOperators

/-- Row-major identification `Fin 8 × Fin 8 ≃ Fin 64` (consistent with `finProdFinEquiv`). -/
noncomputable def spinorRowMajorEquiv : Fin 8 × Fin 8 ≃ Fin 64 :=
  (finProdFinEquiv (m := 8) (n := 8)).trans (finCongr (by norm_num : 8 * 8 = 64))

/-- Coordinate matrix: column `j` is the row-major flattening of `spinorGammaMonomialMat j`. -/
noncomputable def spinorMonomialCoordMatrix : Matrix (Fin 64) (Fin 64) ℝ :=
  fun k j =>
    spinorGammaMonomialMat j (spinorRowMajorEquiv.symm k).1 (spinorRowMajorEquiv.symm k).2

noncomputable abbrev spinorMonomialGramColumnsR : Matrix (Fin 64) (Fin 64) ℝ :=
  (algebraMap ℤ ℝ).mapMatrix spinorMonomialGramColumns

theorem spinorMonomialGramColumnsR_eq_map_intCast :
    spinorMonomialGramColumnsR = spinorMonomialGramColumns.map ((↑) : ℤ → ℝ) := by
  ext i j
  simp [spinorMonomialGramColumnsR, RingHom.mapMatrix_apply]

theorem spinorMonomialGramColumnsR_det_ne_zero : spinorMonomialGramColumnsR.det ≠ 0 := by
  rw [spinorMonomialGramColumnsR_eq_map_intCast, ← Int.cast_det (R := ℝ)]
  exact_mod_cast spinorMonomialGramColumns_det_ne_zero

theorem algebraMap_spinorGammaMonomialMatZ (m : Fin 64) (a b : Fin 8) :
    algebraMap ℤ ℝ (spinorGammaMonomialMatZ m a b) = spinorGammaMonomialMat m a b := by
  simpa using congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M a b) (spinorGammaMonomialMatZ_map m)

theorem spinorMonomialGramFrobSum_algebraMap (i j : Fin 64) :
    algebraMap ℤ ℝ (spinorMonomialGramFrobSum i j) =
      ∑ a : Fin 8, ∑ b : Fin 8,
        spinorGammaMonomialMat i a b * spinorGammaMonomialMat j a b := by
  simp_rw [spinorMonomialGramFrobSum, map_sum, map_mul, algebraMap_spinorGammaMonomialMatZ]

theorem spinorMonomial_coordGram_entries_eq_smul (i j : Fin 64) :
    (spinorMonomialCoordMatrix.transpose * spinorMonomialCoordMatrix) i j =
      (8 : ℝ) * spinorMonomialGramColumnsR i j := by
  have hfrob :
      ∑ a : Fin 8, ∑ b : Fin 8,
          spinorGammaMonomialMat i a b * spinorGammaMonomialMat j a b =
        algebraMap ℤ ℝ (spinorMonomialGramFrobSum i j) :=
      (spinorMonomialGramFrobSum_algebraMap i j).symm
  have h8 :
      algebraMap ℤ ℝ (spinorMonomialGramFrobSum i j) =
        (8 : ℝ) * spinorMonomialGramColumnsR i j := by
    simpa [spinorMonomialGramColumnsR, map_mul] using
      congrArg (algebraMap ℤ ℝ) (spinorMonomialGramFrobSum_eq_mul_spinorMonomialGramColumns i j)
  -- rewrite Gram entry as a single sum over `k`, then reindex `Fin 64 ≃ Fin 8 × Fin 8`
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, spinorMonomialCoordMatrix]
  calc
    (∑ k : Fin 64,
        spinorGammaMonomialMat i (spinorRowMajorEquiv.symm k).1
            (spinorRowMajorEquiv.symm k).2 *
          spinorGammaMonomialMat j (spinorRowMajorEquiv.symm k).1
            (spinorRowMajorEquiv.symm k).2) =
        ∑ p : Fin 8 × Fin 8,
          spinorGammaMonomialMat i p.1 p.2 * spinorGammaMonomialMat j p.1 p.2 := by
      simpa using
        (Equiv.sum_comp spinorRowMajorEquiv (g := fun kk : Fin 64 =>
            spinorGammaMonomialMat i (spinorRowMajorEquiv.symm kk).1
                (spinorRowMajorEquiv.symm kk).2 *
              spinorGammaMonomialMat j (spinorRowMajorEquiv.symm kk).1
                (spinorRowMajorEquiv.symm kk).2)).symm
    _ = ∑ a : Fin 8, ∑ b : Fin 8, spinorGammaMonomialMat i a b * spinorGammaMonomialMat j a b := by
      rw [Fintype.sum_prod_type]
    _ = _ := by rw [hfrob, h8]

theorem spinorMonomial_coordGram_eq_smul :
    spinorMonomialCoordMatrix.transpose * spinorMonomialCoordMatrix =
      (8 : ℝ) • spinorMonomialGramColumnsR := by
  ext i j
  simpa [Matrix.smul_apply] using spinorMonomial_coordGram_entries_eq_smul i j

theorem spinorMonomial_coordGram_det_ne_zero :
    (spinorMonomialCoordMatrix.transpose * spinorMonomialCoordMatrix).det ≠ 0 := by
  have hW : spinorMonomialGramColumnsR.det ≠ 0 := spinorMonomialGramColumnsR_det_ne_zero
  have h8pow : (8 : ℝ) ^ Fintype.card (Fin 64) ≠ 0 := by norm_num
  rw [spinorMonomial_coordGram_eq_smul, Matrix.det_smul]
  exact mul_ne_zero h8pow hW

theorem spinorMonomialCoordMatrix_det_ne_zero : spinorMonomialCoordMatrix.det ≠ 0 := by
  intro hV
  have hgram := spinorMonomial_coordGram_det_ne_zero
  rw [Matrix.det_mul, Matrix.det_transpose, hV, zero_mul] at hgram
  exact hgram rfl

theorem spinorMonomialCoordMatrix_mulVec_eq_zero_imp_eq_zero (c : Fin 64 → ℝ)
    (h : spinorMonomialCoordMatrix.mulVec c = 0) : c = 0 := by
  have hdet : spinorMonomialCoordMatrix.det ≠ 0 := spinorMonomialCoordMatrix_det_ne_zero
  haveI : Invertible spinorMonomialCoordMatrix.det :=
    (isUnit_iff_ne_zero.mpr hdet).invertible
  haveI : Invertible spinorMonomialCoordMatrix := Matrix.invertibleOfDetInvertible _
  have key :=
    inv_mulVec_eq_vec (A := spinorMonomialCoordMatrix) (u := (0 : Fin 64 → ℝ)) (v := c) h.symm
  rw [mulVec_zero] at key
  exact key.symm

theorem spinorMonomialCoordMatrix_sum_smul_col_eq_mulVec (c : Fin 64 → ℝ) (k : Fin 64) :
    (∑ j : Fin 64, c j • (spinorMonomialCoordMatrix.col j)) k =
      spinorMonomialCoordMatrix.mulVec c k := by
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Matrix.transpose_apply]
  ring

theorem spinorGammaMonomialMat_flatten_linearCombination (c : Fin 64 → ℝ) (k : Fin 64) :
    (∑ j : Fin 64, c j • spinorGammaMonomialMat j) (spinorRowMajorEquiv.symm k).1
        (spinorRowMajorEquiv.symm k).2 =
      spinorMonomialCoordMatrix.mulVec c k := by
  have hLHS :
      (∑ j : Fin 64, c j • spinorGammaMonomialMat j) (spinorRowMajorEquiv.symm k).1
          (spinorRowMajorEquiv.symm k).2 =
        ∑ j : Fin 64,
          c j * spinorGammaMonomialMat j (spinorRowMajorEquiv.symm k).1
            (spinorRowMajorEquiv.symm k).2 := by
    classical
    -- `Matrix` is a nested `Pi`; pull out the two indices with `Fintype.sum_apply` twice.
    rw [Fintype.sum_apply (a := (spinorRowMajorEquiv.symm k).1),
      Fintype.sum_apply (a := (spinorRowMajorEquiv.symm k).2)]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [smul_eq_mul]
  rw [hLHS, ← spinorMonomialCoordMatrix_sum_smul_col_eq_mulVec c k]
  classical
  rw [Fintype.sum_apply (a := k)]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [Pi.smul_apply, smul_eq_mul, Matrix.col_apply, spinorMonomialCoordMatrix]

/-- The `64` ordered `γ` monomial matrices are `ℝ`-linearly independent. -/
theorem spinorGammaMonomialMat_linearIndependent :
    LinearIndependent ℝ spinorGammaMonomialMat := by
  classical
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg i
  have hdiff :
      (∑ j : Fin 64, (f j - g j) • spinorGammaMonomialMat j) = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, hfg, sub_self]
  have hcoord : spinorMonomialCoordMatrix.mulVec (fun j => f j - g j) = 0 := by
    ext k
    have := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ =>
        M (spinorRowMajorEquiv.symm k).1 (spinorRowMajorEquiv.symm k).2) hdiff
    simpa [Matrix.zero_apply, Pi.zero_apply, spinorGammaMonomialMat_flatten_linearCombination] using
      this
  have hzero := spinorMonomialCoordMatrix_mulVec_eq_zero_imp_eq_zero (fun j => f j - g j) hcoord
  exact sub_eq_zero.mp (congr_fun hzero i)

end Hqiv.Algebra
