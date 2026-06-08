import Hqiv.Algebra.OctonionSpinorCarrier
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Star.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Complexified octonion spinor carrier (Furey Stage 1)

`AGENTS/FUREY_PROOF_ROADMAP.md` Stage 1 asks for a concrete `ℂ`-module model of the
single-generation complexified carrier and its `finrank` over `ℂ`.

This file keeps the same **coordinate** pattern as `OctonionSpinorCarrier` (`Fin 8 → _`),
so downstream bridges can align with the electroweak layer’s coefficient vectors without
pulling `PiLp` / Hermitian structure.

**Base change.** `Mathlib.LinearAlgebra.TensorProduct.Pi` gives the standard `ℂ`-linear
identification `ℂ ⊗[ℝ] (Fin 8 → ℝ) ≃ₗ[ℂ] (Fin 8 → ℂ)` (`complexOctonionSpinorTensorEquiv`), compatible
with slotwise `ofReal` (`complexOctonionSpinorTensorEquiv_apply_tmul_one`).

**Star / conjugation.** Pointwise complex conjugation on `Fin 8 → ℂ` is a `StarAddMonoid` / `StarRing`
instance from `Mathlib.Algebra.Star.Pi`; `StarModule ℝ` follows from `StarModule ℝ ℂ`
(`Mathlib.LinearAlgebra.Complex.Module`). `StarModule ℂ` is recorded as the same `inferInstance`
certificate when needed for conjugate-linear algebra over `ℂ`.

**Not claimed here:** `Cl(6)` minimal-ideal classification beyond the repo’s abstract `Cl(0,6)`
ideal packaging, or number-operator charge quantization — see `CliffordCl06SixIdeal` /
`CliffordMinimalIdeal` and `AGENTS/FUREY_PROOF_ROADMAP.md` Stage 3.
-/

open scoped TensorProduct

namespace Hqiv.Algebra

/-- **Complexified 8s carrier:** `ℂ⁸` with slotwise `ℂ`-action (Furey-style one-generation model). -/
abbrev ComplexOctonionSpinorCarrier := Fin 8 → ℂ

instance : AddCommGroup ComplexOctonionSpinorCarrier := Pi.addCommGroup
instance : Module ℂ ComplexOctonionSpinorCarrier := Pi.module _ _ _
instance : Module ℝ ComplexOctonionSpinorCarrier := Pi.module _ _ _

/-- Embed real spinor coefficients into the complexified carrier (slotwise `ℝ → ℂ`). -/
noncomputable def octonionSpinorRealToComplex :
    OctonionSpinorCarrier →ₗ[ℝ] ComplexOctonionSpinorCarrier where
  toFun v i := (v i : ℂ)
  map_add' v w := by ext i; simp
  map_smul' r v := by ext i; simp [Pi.smul_apply, Algebra.smul_def]

/-!
### Base change `ℂ ⊗[ℝ] ℝ⁸ ≃ ℂ⁸`
-/

/-- Canonical `ℂ`-linear identification `ℂ ⊗[ℝ] (Fin 8 → ℝ) ≃ₗ[ℂ] (Fin 8 → ℂ)`. -/
noncomputable abbrev complexOctonionSpinorTensorEquiv :
    (ℂ ⊗[ℝ] OctonionSpinorCarrier) ≃ₗ[ℂ] ComplexOctonionSpinorCarrier :=
  TensorProduct.piScalarRight ℝ ℂ ℂ (Fin 8)

theorem complexOctonionSpinorTensorEquiv_apply_tmul_one (v : OctonionSpinorCarrier) :
    complexOctonionSpinorTensorEquiv (1 ⊗ₜ v) = octonionSpinorRealToComplex v := by
  ext i
  simp only [octonionSpinorRealToComplex, LinearMap.coe_mk, AddHom.coe_mk,
    complexOctonionSpinorTensorEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, Algebra.smul_def, mul_one, Complex.coe_algebraMap]

/-!
### `StarModule` bookkeeping (conjugation)
-/

/-- Conjugation is slotwise: `(star f) i = star (f i)`. -/
theorem complexOctonionSpinor_star_apply (f : ComplexOctonionSpinorCarrier) (i : Fin 8) :
    (star f) i = star (f i) :=
  rfl

instance complexOctonionSpinorCarrier_starModuleReal : StarModule ℝ ComplexOctonionSpinorCarrier :=
  inferInstance

instance complexOctonionSpinorCarrier_starModuleComplex : StarModule ℂ ComplexOctonionSpinorCarrier :=
  inferInstance

theorem complexOctonionSpinor_star_smul_real (r : ℝ) (f : ComplexOctonionSpinorCarrier) :
    star (r • f) = r • star f :=
  star_smul r f

theorem complexOctonionSpinor_star_smul_complex (c : ℂ) (f : ComplexOctonionSpinorCarrier) :
    star (c • f) = star c • star f :=
  star_smul c f

/-- **Dimension over `ℂ`:** `finrank ℂ (Fin 8 → ℂ) = 8`. -/
theorem complexOctonionSpinorCarrier_finrank_complex :
    Module.finrank ℂ ComplexOctonionSpinorCarrier = 8 := by
  rw [Module.finrank_pi (R := ℂ) (ι := Fin 8)]
  exact Fintype.card_fin _

/-- **Dimension over `ℝ`:** `16 = 8 × [ℂ : ℝ]` via `finrank_real_of_complex`. -/
theorem complexOctonionSpinorCarrier_finrank_real :
    Module.finrank ℝ ComplexOctonionSpinorCarrier = 16 := by
  rw [finrank_real_of_complex, complexOctonionSpinorCarrier_finrank_complex]

theorem octonionSpinorRealToComplex_injective :
    Function.Injective octonionSpinorRealToComplex := by
  intro v w h
  ext i
  exact Complex.ofReal_injective (congr_fun h i)

end Hqiv.Algebra
