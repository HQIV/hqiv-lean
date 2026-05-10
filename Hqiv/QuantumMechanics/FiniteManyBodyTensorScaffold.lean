import Mathlib.Data.PNat.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Logic.Equiv.Fin.Basic
import Hqiv.QuantumMechanics.FiniteDimVonNeumann

/-!
# Finite many-body tensor bookkeeping (Kronecker sum scaffold)

This module is **numerical-bridge** material: it packages the standard
`H₁ ⊗ I + I ⊗ H₂` construction on `Fin n × Fin m` and reindexes to
`Fin (n * m)` in the same order used by `numpy.kron` row-major flattening.

It extends `FiniteDimVonNeumann` without new physics axioms: only finite-dimensional
complex linear algebra.

## Python alignment

`scripts/qm_finite_tensor_toy.py` builds the same Kronecker sum and reports
spectra / small time traces for regression-style experiments.
-/

namespace Hqiv.QM

open scoped Kronecker
open Matrix Complex

/-- Row-major `Fin n × Fin m ≃ Fin (n * m)` (matches `numpy.reshape(..., order="C")`
after swapping axes to `(m, n)` vs our `prodComm` + `finProdFinEquiv` chain). -/
noncomputable def finTensorIndexEquiv (n m : ℕ+) : (Fin n.1 × Fin m.1) ≃ Fin (n * m).1 :=
  Equiv.prodComm _ _ |>.trans finProdFinEquiv |>.trans
    (Equiv.cast (congrArg Fin (show m.1 * n.1 = (n * m).1 by
      have h : (n * m).1 = n.1 * m.1 := rfl
      rw [h, mul_comm])))

theorem finTensorIndexEquiv_card (n m : ℕ+) :
    Fintype.card (Fin n.1 × Fin m.1) = Fintype.card (Fin (n * m).1) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact (PNat.mul_coe n m).symm

noncomputable section

/-- Non-interacting sum on the product computational basis (`H₁ ⊗ I + I ⊗ H₂`). -/
def tensorKroneckerSumAux (n m : ℕ+) (A : Matrix (Fin n.1) (Fin n.1) ℂ)
    (B : Matrix (Fin m.1) (Fin m.1) ℂ) :
    Matrix (Fin n.1 × Fin m.1) (Fin n.1 × Fin m.1) ℂ :=
  A ⊗ₖ (1 : Matrix (Fin m.1) (Fin m.1) ℂ) + (1 : Matrix (Fin n.1) (Fin n.1) ℂ) ⊗ₖ B

private lemma kronecker_mul_one_isHermitian (n m : ℕ+)
    {A : Matrix (Fin n.1) (Fin n.1) ℂ} (hA : A.IsHermitian) :
    (A ⊗ₖ (1 : Matrix (Fin m.1) (Fin m.1) ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_kronecker, hA, Matrix.conjTranspose_one]

private lemma one_mul_kronecker_isHermitian (n m : ℕ+)
    {B : Matrix (Fin m.1) (Fin m.1) ℂ} (hB : B.IsHermitian) :
    ((1 : Matrix (Fin n.1) (Fin n.1) ℂ) ⊗ₖ B).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_kronecker, Matrix.conjTranspose_one, hB]

theorem tensorKroneckerSumAux_isHermitian (n m : ℕ+) (A : Matrix (Fin n.1) (Fin n.1) ℂ)
    (B : Matrix (Fin m.1) (Fin m.1) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (tensorKroneckerSumAux n m A B).IsHermitian :=
  (kronecker_mul_one_isHermitian n m hA).add (one_mul_kronecker_isHermitian n m hB)

/-- Same operator on `Fin (n * m)` after reindexing rows/cols. -/
def tensorKroneckerSumMatrix (n m : ℕ+) (A : Matrix (Fin n.1) (Fin n.1) ℂ)
    (B : Matrix (Fin m.1) (Fin m.1) ℂ) :
    Matrix (Fin (n * m).1) (Fin (n * m).1) ℂ :=
  (tensorKroneckerSumAux n m A B).submatrix (finTensorIndexEquiv n m).symm
    (finTensorIndexEquiv n m).symm

theorem tensorKroneckerSumMatrix_isHermitian (n m : ℕ+) (A : Matrix (Fin n.1) (Fin n.1) ℂ)
    (B : Matrix (Fin m.1) (Fin m.1) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (tensorKroneckerSumMatrix n m A B).IsHermitian :=
  (tensorKroneckerSumAux_isHermitian n m A B hA hB).submatrix _

/-- Bundle as an `Observable` on the composite Hilbert space `ℂ^(nm)`. -/
noncomputable def observableTensorKroneckerSum (n m : ℕ+) (A : Matrix (Fin n.1) (Fin n.1) ℂ)
    (B : Matrix (Fin m.1) (Fin m.1) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Observable (n * m).1 where
  A := tensorKroneckerSumMatrix n m A B
  isHerm := tensorKroneckerSumMatrix_isHermitian n m A B hA hB

end

end Hqiv.QM
