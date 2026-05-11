import Hqiv.Algebra.CliffordCl06SixIdeal
import Hqiv.Algebra.OctonionSpinorCarrier
import Hqiv.Algebra.Triality

/-!
# Abstract `Cl(0,6)` ideals → octonion spinor carrier (representation-conditional)

The obstruction in `Hqiv.Algebra.OctonionLeftMulCliffordObstruction` shows that **naive**
octonion **left** matrices on `e₁,…,e₆` cannot realize the universal `CliffordAlgebra.lift` for the
standard `Cl(0,6)` quadratic form.  The correct HQIV packaging is therefore:

1. work in the **abstract** algebra `CliffordCl06Six` for ideal/idempotent statements; then
2. choose (separately) an `ℝ`-algebra map `ρ : CliffordCl06Six →ₐ[ℝ] (Module.End ℝ W)` into
   endomorphisms of some real spinor module `W` (for HQIV: `W = OctonionSpinorCarrier`); a concrete
   Mathlib-backed choice is `Hqiv.Algebra.cl06StandardSpinorRho` (Kronecker `γ` matrices, **not**
   naive octonion left multiplication); and
3. transport ideals along `ρ` by composing `ρ` with submodule inclusion.

Triality (`Hqiv.Algebra.Triality`) permutes the three `8`-dimensional `Spin(8)` slots at the **Lie /
representation** layer.  **Equivariance** of a bridge map under triality is an extra hypothesis on
`ρ` (commutation with the concrete triality-induced operators on `End ℝ W`), not something forced
by the Clifford algebra alone.
-/

namespace Hqiv.Algebra

open Submodule

/-- Fix a spinor seed `v₀` and read off `x ↦ (ρ x) v₀` on a left ideal `I`. -/
noncomputable def cliffordIdealToSpinorVec
    (ρ : CliffordCl06Six →ₐ[ℝ] Module.End ℝ OctonionSpinorCarrier) (I : CliffordLeftIdeal)
    (v₀ : OctonionSpinorCarrier) : I →ₗ[ℝ] OctonionSpinorCarrier where
  toFun x := ρ x v₀
  map_add' x y := by simp [map_add]
  map_smul' r x := by
    rw [Submodule.coe_smul_of_tower (S := ℝ) r x, Algebra.smul_def, map_mul, AlgHom.commutes]
    simp

theorem cliffordIdealToSpinorVec_apply
    (ρ : CliffordCl06Six →ₐ[ℝ] Module.End ℝ OctonionSpinorCarrier) (I : CliffordLeftIdeal)
    (v₀ : OctonionSpinorCarrier) (x : I) :
    cliffordIdealToSpinorVec ρ I v₀ x = ρ (x : CliffordCl06Six) v₀ :=
  rfl

end Hqiv.Algebra
