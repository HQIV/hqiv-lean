import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Hqiv.GeneratorsFromAxioms
import Hqiv.Geometry.AuxiliaryField

/-!
# Horizon phase-lift generator Δ

The phase-lift operator Δ is the generator of rotation in the (e₁, e₇) plane, forced
by the geometric (informational-energy) route: the time angle δθ′ couples to this
direction. In the matrix realization, Δ is the antisymmetric 8×8 matrix with
Δ₁₇ = -1, Δ₇₁ = 1 (0-based indices), zero elsewhere — i.e. the rotation generator
in the plane spanned by e₁ and e₇.

**Informational-energy link:** The scalar φ = 2/Θ_local (from AuxiliaryField) satisfies
φ = 2c²/Θ_local in the axiom; the phase-lift coefficient φ/6 appears in the
full derivation-style formula Δ(x) = (φ/6) ∑_{i=1}^7 (e_i·x - x·e_i). The matrix
`phaseLiftDelta` below is the unit generator; the φ/6 factor is applied when
coupling to the auxiliary field at a given shell.

**Reference:** HQIV preprint v2, Zenodo 10.5281/zenodo.18899939, Section 4.2–4.3;
Hqiv.Geometry.AuxiliaryField for φ.
-/

open Matrix

namespace Hqiv.Algebra

/-- **Phase-lift generator Δ** (matrix): rotation in the (e₁, e₇) plane.
Re-exported from Hqiv.GeneratorsFromAxioms; matches HQVM/matrices.py `_build_Delta()`. -/
def phaseLiftDeltaMatrix : Matrix (Fin 8) (Fin 8) ℝ := Hqiv.phaseLiftDelta

/-- **Δ is antisymmetric:** Δᵀ = -Δ. -/
theorem phaseLiftDelta_antisymm :
    phaseLiftDeltaMatrix + phaseLiftDeltaMatrixᵀ = 0 := by
  ext i j
  rw [add_apply, transpose_apply, zero_apply, phaseLiftDeltaMatrix]
  exact Hqiv.phaseLiftDelta_antisymm i j

/-- **Phase coefficient φ/6** at shell m (from AuxiliaryField). Used in the
informational-energy axiom: Δ_φ(x) = (φ(m)/6) · (matrix action of Δ on x). -/
noncomputable def phaseLiftCoeff (m : Nat) : ℝ := Hqiv.phi_of_shell m / 6

/-- **φ(m)/6 is positive** for all shells. -/
theorem phaseLiftCoeff_pos (m : Nat) : 0 < phaseLiftCoeff m := by
  unfold phaseLiftCoeff
  have h := Hqiv.phi_of_shell_pos m
  positivity

end Hqiv.Algebra
