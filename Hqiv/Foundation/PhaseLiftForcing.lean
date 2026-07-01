import Hqiv.Foundation.SevenImaginaryIncidence
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Basic

/-!
# PhaseLiftForcing — the abstract phase-lift generator on a distinguished 2-plane

The HQIV cumulative phase readout `ℛ` produces an infinitesimal rotation `Δ` on one
distinguished 2-plane of the carrier. Here we package that generator **abstractly** as
a skew-symmetric `planeGenerator i j` on the 8-channel carrier, with no reference to
the concrete octonion matrices. We prove the two structural facts the closure step
needs:

* `planeGenerator i j` is skew-symmetric (its transpose is its negation);
* it is nonzero whenever `i ≠ j` (it genuinely lifts a 2-plane).

The HQIV distinguished plane is `(e₁, e₇)`; `foundationDelta := planeGenerator 1 7`
is the abstract analogue of the concrete `Hqiv.GeneratorsFromAxioms.phaseLiftDelta`,
to which it is shown equal in the witness layer.
-/

namespace Hqiv.Foundation

open Matrix

/-- **Abstract phase-lift generator** on the carrier: the skew-symmetric matrix with
`+1` at `(j, i)` and `−1` at `(i, j)` (the infinitesimal rotation of the `(i, j)`-plane). -/
def planeGenerator (i j : Fin 8) : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.single j i 1 - Matrix.single i j 1

/-- Transpose of `single` (proved inline; Mathlib has no direct lemma in this version). -/
private theorem single_transpose (i j : Fin 8) (c : ℝ) :
    (Matrix.single i j c)ᵀ = Matrix.single j i c := by
  ext a b
  simp only [Matrix.transpose_apply, Matrix.single_apply]
  by_cases h : i = b ∧ j = a
  · obtain ⟨hi, hj⟩ := h; subst hi; subst hj; simp
  · rw [if_neg h, if_neg]
    tauto

/-- **Skew-symmetry:** `(planeGenerator i j)ᵀ = − planeGenerator i j`. -/
theorem planeGenerator_transpose (i j : Fin 8) :
    (planeGenerator i j)ᵀ = - planeGenerator i j := by
  unfold planeGenerator
  rw [Matrix.transpose_sub, single_transpose, single_transpose]
  abel

/-- **Antisymmetry entrywise:** `planeGenerator i j a b + planeGenerator i j b a = 0`. -/
theorem planeGenerator_antisymm (i j a b : Fin 8) :
    planeGenerator i j a b + planeGenerator i j b a = 0 := by
  have h := congrFun (congrFun (planeGenerator_transpose i j) b) a
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  linarith [h]

/-- **The generator is nonzero off the diagonal:** its `(j, i)` entry is `1`. -/
theorem planeGenerator_apply_swap (i j : Fin 8) (hij : i ≠ j) :
    planeGenerator i j j i = 1 := by
  unfold planeGenerator
  simp [Matrix.sub_apply, hij]

theorem planeGenerator_ne_zero (i j : Fin 8) (hij : i ≠ j) :
    planeGenerator i j ≠ 0 := by
  intro h
  have : planeGenerator i j j i = 0 := by rw [h]; rfl
  rw [planeGenerator_apply_swap i j hij] at this
  exact one_ne_zero this

/-- **HQIV distinguished plane index `i`** = the EM/electromagnetic axis `e₁`. -/
def phaseLiftPlaneI : Fin 8 := 1

/-- **HQIV distinguished plane index `j`** = the colour-preferred axis `e₇`. -/
def phaseLiftPlaneJ : Fin 8 := 7

/-- **The abstract HQIV phase-lift `Δ`** on the `(e₁, e₇)` plane.

This is the foundation-side, table-free generator; the concrete
`Hqiv.GeneratorsFromAxioms.phaseLiftDelta` is shown equal to it in the witness layer. -/
def foundationDelta : Matrix (Fin 8) (Fin 8) ℝ :=
  planeGenerator phaseLiftPlaneI phaseLiftPlaneJ

theorem foundationDelta_transpose :
    (foundationDelta)ᵀ = - foundationDelta :=
  planeGenerator_transpose _ _

theorem foundationDelta_ne_zero : foundationDelta ≠ 0 :=
  planeGenerator_ne_zero _ _ (by decide)

end Hqiv.Foundation
