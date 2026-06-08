import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Hqiv.QuantumMechanics.HorizonFreeFieldScaffold

/-!
# Patch Hilbert space ↔ Dojo carrier bridge

The HQIV patch layer uses `LatticeHilbert 4 = EuclideanSpace ℂ (Fin 4)` with **ℂ-linear**
endomorphisms `LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4`. The Lean Dojo `QuantumYangMillsTheory`
carrier `H` is a **real** inner product space with bounded operators `H →L[ℝ] H` (= `LinearOperator H`).

This module packages the standard Hilbert-space link: fix a bounded ℝ-linear embedding
`incl : LatticeHilbert 4 →L[ℝ] H` and send a patch operator `A` to the **sandwich**
`incl ∘ Aℝ ∘ incl†`, where `Aℝ` is `A` viewed as an ℝ-linear map and `†` is the Hilbert adjoint.

On the ℂ side we use `InnerProductSpace.complexToReal` (mathlib’s real restriction of the
canonical ℂ-inner product) so that `ContinuousLinearMap.adjoint` is available over `ℝ`.
-/

namespace Hqiv.Story

open Hqiv.QM

/-- Data linking the finite-dimensional patch Hilbert space to a Dojo-style real Hilbert carrier. -/
structure HilbertPatchBridge (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] where
  /-- ℝ-linear, bounded embedding of the `Fin 4` patch carrier into the QFT Hilbert space. -/
  incl : LatticeHilbert 4 →L[ℝ] H

namespace HilbertPatchBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (br : HilbertPatchBridge H)

/-- ℝ-inner product on the patch space induced from the standard ℂ-inner product. -/
noncomputable local instance : InnerProductSpace ℝ (LatticeHilbert 4) :=
  InnerProductSpace.complexToReal

/-- A ℂ-linear patch operator, viewed as a continuous ℝ-linear endomorphism (finite-dimensional). -/
noncomputable def latticeOpAsRealContinuous (A : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4) :
    LatticeHilbert 4 →L[ℝ] LatticeHilbert 4 :=
  LinearMap.toContinuousLinearMap (A.restrictScalars ℝ)

/-- Promote a patch endomorphism to a bounded operator on the full carrier via `incl A incl†`. -/
noncomputable def patchOpAsLinearOperator (A : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4) :
    H →L[ℝ] H :=
  br.incl.comp ((latticeOpAsRealContinuous A).comp (ContinuousLinearMap.adjoint br.incl))

@[simp]
theorem patchOpAsLinearOperator_zero :
    br.patchOpAsLinearOperator (0 : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4) = 0 := by
  simp [patchOpAsLinearOperator, latticeOpAsRealContinuous]

/-- Identity bridge when the Dojo carrier is **definitionally** `LatticeHilbert 4`. -/
noncomputable def latticeIdentityBridge : HilbertPatchBridge (LatticeHilbert 4) where
  incl := ContinuousLinearMap.id ℝ (LatticeHilbert 4)

@[simp]
theorem latticeIdentityBridge_patchOpAsLinearOperator (A : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4) :
    latticeIdentityBridge.patchOpAsLinearOperator A = latticeOpAsRealContinuous A := by
  simp [patchOpAsLinearOperator, latticeOpAsRealContinuous, latticeIdentityBridge,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

end HilbertPatchBridge

end Hqiv.Story
