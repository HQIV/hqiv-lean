import Hqiv.Algebra.CliffordCl06SixDimension
import Hqiv.Algebra.CliffordCl06SixSpinorGammaMatInt
import Hqiv.Algebra.CliffordCl06SixStandardSpinorRho
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Surjectivity of the standard spinor matrix lift (conditional layer)

The ordered-product **γ** monomials (bitmask column order matching
`cl06SpinorGammaMaskFinset` in `CliffordCl06SixSpinorGammaMatInt`) generate the matrix subalgebra
once they are `ℝ`-linearly independent as `8×8` matrices.

`Mathlib` already gives `CliffordAlgebra.range_lift`, so surjectivity of
`cl06StandardSpinorMatLift` is equivalent to `Algebra.adjoin ℝ (Set.range cl06SpinorMatLin) = ⊤`.

The **linear independence** of the `64` monomial matrices is proved in
`CliffordCl06SixSpinorGammaMonomialLinearIndependent` (Gram / row-major `ℝ^64` coordinate matrix).
The integral Gram `W` in `CliffordCl06SixSpinorMonomialMatrixData` supplies `det W ≠ 0` via the
mod-`101` axiom; `spinorGammaMonomialMatZ_map` identifies the `ℝ` monomials with
`Matrix.map (algebraMap ℤ ℝ)` of the integral model.
-/

namespace Hqiv.Algebra

open Finset List Matrix Module Submodule

/-- Ordered γ-product for bitmask `m` (increasing `i` among set bits), times identity if empty. -/
noncomputable def spinorGammaMonomialMat (m : Fin 64) : Matrix (Fin 8) (Fin 8) ℝ :=
  (cl06SpinorGammaMaskFinset m).sort (· ≤ ·)|>.foldl
    (fun A i => A * cl06SpinorGammaMat i) (1 : Matrix (Fin 8) (Fin 8) ℝ)

theorem spinorGammaMonomialMatZ_map (m : Fin 64) :
    (spinorGammaMonomialMatZ m).map (algebraMap ℤ ℝ) = spinorGammaMonomialMat m := by
  classical
  let g : RingHom ℤ ℝ := algebraMap ℤ ℝ
  rw [spinorGammaMonomialMat, spinorGammaMonomialMatZ]
  generalize (cl06SpinorGammaMaskFinset m).sort (· ≤ ·) = L
  suffices ∀ (A0 : Matrix (Fin 8) (Fin 8) ℤ),
      (L.foldl (fun A i => A * cl06SpinorGammaMatZ i) A0).map g =
        L.foldl (fun A i => A * cl06SpinorGammaMat i) (A0.map g) by
    simpa [Matrix.map_one] using this (1 : Matrix (Fin 8) (Fin 8) ℤ)
  intro A0
  induction L generalizing A0 with
  | nil =>
      rfl
  | cons a L ih =>
      simp only [List.foldl_cons]
      rw [ih (A0 * cl06SpinorGammaMatZ a)]
      rw [Matrix.map_mul, cl06SpinorGammaMatZ_map]

theorem cl06SpinorGammaMat_mem_adjoin (j : Fin 6) :
    cl06SpinorGammaMat j ∈ Algebra.adjoin ℝ (Set.range cl06SpinorMatLin) := by
  classical
  have hγ : cl06SpinorGammaMat j = cl06SpinorMatLin (Pi.single j (1 : ℝ)) := by
    simp [cl06SpinorMatLin, Fintype.linearCombination_apply, Pi.single_apply, cl06SpinorGammaMat]
  rw [hγ]
  exact Algebra.subset_adjoin (Set.mem_range_self _)

theorem spinorGammaMonomialList_foldl_mem_adjoin' (L : List (Fin 6))
    (A0 : Matrix (Fin 8) (Fin 8) ℝ)
    (hA0 : A0 ∈ Algebra.adjoin ℝ (Set.range cl06SpinorMatLin)) :
    L.foldl (fun A i => A * cl06SpinorGammaMat i) A0 ∈
      Algebra.adjoin ℝ (Set.range cl06SpinorMatLin) := by
  induction L generalizing A0 with
  | nil =>
      simpa using hA0
  | cons a L ih =>
      simp only [List.foldl_cons]
      exact ih _ (Subalgebra.mul_mem _ hA0 (cl06SpinorGammaMat_mem_adjoin a))

theorem spinorGammaMonomialList_foldl_mem_adjoin (L : List (Fin 6)) :
    L.foldl (fun A i => A * cl06SpinorGammaMat i) (1 : Matrix (Fin 8) (Fin 8) ℝ) ∈
      Algebra.adjoin ℝ (Set.range cl06SpinorMatLin) :=
  spinorGammaMonomialList_foldl_mem_adjoin' L 1 (Subalgebra.one_mem _)

theorem spinorGammaMonomialMat_mem_adjoin (m : Fin 64) :
    spinorGammaMonomialMat m ∈ Algebra.adjoin ℝ (Set.range cl06SpinorMatLin) := by
  classical
  simpa [spinorGammaMonomialMat] using
    spinorGammaMonomialList_foldl_mem_adjoin ((cl06SpinorGammaMaskFinset m).sort (· ≤ ·))

theorem spinorGammaMonomial_range_subset_adjoin :
    Set.range spinorGammaMonomialMat ⊆
      (Algebra.adjoin ℝ (Set.range cl06SpinorMatLin) :
        Set (Matrix (Fin 8) (Fin 8) ℝ)) := by
  rintro _ ⟨m, rfl⟩
  exact SetLike.mem_coe.2 (spinorGammaMonomialMat_mem_adjoin m)

theorem span_spinorGammaMonomial_le_adjoin :
    span ℝ (Set.range spinorGammaMonomialMat) ≤
      (Algebra.adjoin ℝ (Set.range cl06SpinorMatLin)).toSubmodule := by
  rw [span_le]
  exact spinorGammaMonomial_range_subset_adjoin

theorem matrix_finrank_eq_64 : Module.finrank ℝ (Matrix (Fin 8) (Fin 8) ℝ) = 64 := by
  classical
  simp only [Matrix]
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Module.finrank_pi, Fintype.card_fin]
  simp [smul_eq_mul]

theorem algebra_adjoin_cl06SpinorMatLin_eq_top_of_linearIndependent
    (hLI : LinearIndependent ℝ spinorGammaMonomialMat) :
    Algebra.adjoin ℝ (Set.range cl06SpinorMatLin) = ⊤ := by
  classical
  have hcard : Fintype.card (Fin 64) = Module.finrank ℝ (Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [Fintype.card_fin, matrix_finrank_eq_64]
  have hspan := LinearIndependent.span_eq_top_of_card_eq_finrank' hLI hcard
  refine (_root_.Algebra.eq_top_iff).mpr fun M => ?_
  have hle : (⊤ : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℝ)) ≤
      (Algebra.adjoin ℝ (Set.range cl06SpinorMatLin)).toSubmodule := by
    rw [← hspan]
    exact span_spinorGammaMonomial_le_adjoin
  exact hle (Submodule.mem_top : M ∈ (⊤ : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℝ)))

theorem cl06StandardSpinorMatLift_range_eq_top_of_linearIndependent
    (hLI : LinearIndependent ℝ spinorGammaMonomialMat) :
    (cl06StandardSpinorMatLift).range = ⊤ := by
  rw [cl06StandardSpinorMatLift, CliffordAlgebra.range_lift,
    algebra_adjoin_cl06SpinorMatLin_eq_top_of_linearIndependent hLI]

theorem cl06StandardSpinorMatLift_surjective_of_linearIndependent
    (hLI : LinearIndependent ℝ spinorGammaMonomialMat) :
    Function.Surjective cl06StandardSpinorMatLift :=
  (AlgHom.range_eq_top (f := cl06StandardSpinorMatLift)).mp
    (cl06StandardSpinorMatLift_range_eq_top_of_linearIndependent hLI)

theorem cl06StandardSpinorMatLift_injective_of_surjective
    (hsurj : Function.Surjective cl06StandardSpinorMatLift) :
    Function.Injective cl06StandardSpinorMatLift := by
  classical
  haveI : FiniteDimensional ℝ CliffordCl06Six :=
    FiniteDimensional.of_finrank_pos (K := ℝ) (V := CliffordCl06Six) (by
      rw [cliffordCl06Six_finrank]; decide)
  let f := cl06StandardSpinorMatLift.toLinearMap
  have hr : f.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := matrix_finrank_eq_64
  have hdom := cliffordCl06Six_finrank
  have hker : Module.finrank ℝ (LinearMap.ker f) = 0 := by
    have key := LinearMap.finrank_range_add_finrank_ker (f := f)
    rw [hr, finrank_top, hdim, hdom] at key
    omega
  have hbot : LinearMap.ker f = ⊥ :=
    (Submodule.finrank_eq_zero (R := ℝ) (M := CliffordCl06Six) (S := LinearMap.ker f)).1
      (by convert hker)
  exact (LinearMap.ker_eq_bot (f := f)).mp hbot

theorem cl06StandardSpinorMatLift_bijective_of_linearIndependent
    (hLI : LinearIndependent ℝ spinorGammaMonomialMat) :
    Function.Bijective cl06StandardSpinorMatLift :=
  ⟨cl06StandardSpinorMatLift_injective_of_surjective
      (cl06StandardSpinorMatLift_surjective_of_linearIndependent hLI),
    cl06StandardSpinorMatLift_surjective_of_linearIndependent hLI⟩

end Hqiv.Algebra
