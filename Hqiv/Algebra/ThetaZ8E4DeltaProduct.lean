import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Basic

import Hqiv.Algebra.ThetaZ8DeltaProductScaffold
import Hqiv.Algebra.ThetaZ8EisensteinQCoeff

/-!
# `E₄ × δ` as a concrete weight-`16` modular form

`thetaZ8_times_delta_weight16` turns a weight-`4` and a weight-`12` level-one form into weight
`16`. Instantiating the weight-`4` slot with **`E₄`** (`eisensteinE4`) yields a fully explicit
`ModularForm Γ(1) 16` as soon as a weight-`12` placeholder `δ` is supplied.

`ModularForm.qExpansion_mul` identifies the `q`-expansion with the **Cauchy product** of the two
`PowerSeries`; combined with `eisensteinE4_qExpansion_coeff_eq_sigma3`, coefficients are concrete
linear combinations of **`240 · σ₃`** and the chosen `δ` coefficients.

This is **not** the classical `θ_{ℤ⁸} ⊗ Δ` (no proved `θ = r₈`, no Mathlib `Δ` here).
-/

namespace Hqiv.Algebra

open Complex Finset UpperHalfPlane Matrix.SpecialLinearGroup ModularForm ModularFormClass
  CongruenceSubgroup
open scoped CongruenceSubgroup

noncomputable section

variable (hk : 3 ≤ (4 : ℕ))

/-- Weight-`16` form `E₄ · δ` built from the Eisenstein witness and any weight-`12` input. -/
noncomputable def thetaZ8E4TimesDeltaPlaceholder (δ : ModularForm Γ(1) 12) : ModularForm Γ(1) 16 :=
  thetaZ8_times_delta_weight16 (eisensteinE4 hk) δ

private lemma coe_mcast_modularForm {a b : ℤ} (hab : a = b) (f : ModularForm Γ(1) a) :
    (ModularForm.mcast hab f : ℍ → ℂ) = (f : ℍ → ℂ) := by
  ext z
  rfl

private lemma qExpansion_mcast_eq {a b : ℤ} (hab : a = b) (f : ModularForm Γ(1) a) :
    qExpansion 1 (ModularForm.mcast hab f : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) := by
  rw [coe_mcast_modularForm hab f]

/-- `q`-expansion of the product is the product of `q`-expansions (`Mathlib` Cauchy convolution). -/
theorem thetaZ8E4TimesDeltaPlaceholder_qExpansion_mul (δ : ModularForm Γ(1) 12) :
    qExpansion 1 (thetaZ8E4TimesDeltaPlaceholder hk δ : ℍ → ℂ) =
      qExpansion 1 (eisensteinE4 hk : ℍ → ℂ) * qExpansion 1 (δ : ℍ → ℂ) := by
  dsimp [thetaZ8E4TimesDeltaPlaceholder, thetaZ8_times_delta_weight16]
  rw [qExpansion_mcast_eq (by norm_num : (4 : ℤ) + 12 = 16) (ModularForm.mul (eisensteinE4 hk) δ)]
  exact ModularForm.qExpansion_mul (hh := zero_lt_one) (hΓ := by simp) (eisensteinE4 hk) δ

/-- Coefficient `n` is the Cauchy convolution of the `E₄` and `δ` coefficient sequences. -/
theorem thetaZ8E4TimesDeltaPlaceholder_coeff (δ : ModularForm Γ(1) 12) (n : ℕ) :
    (qExpansion 1 (thetaZ8E4TimesDeltaPlaceholder hk δ : ℍ → ℂ)).coeff n =
      ∑ p ∈ antidiagonal n,
        (qExpansion 1 (eisensteinE4 hk : ℍ → ℂ)).coeff p.1 * (qExpansion 1 (δ : ℍ → ℂ)).coeff p.2 := by
  rw [thetaZ8E4TimesDeltaPlaceholder_qExpansion_mul hk, PowerSeries.coeff_mul]

/-- Same convolution with **`E₄` coefficients** spelt as `eisensteinE4_qCoeff` (hence `σ₃`). -/
theorem thetaZ8E4TimesDeltaPlaceholder_coeff_eisenstein (δ : ModularForm Γ(1) 12) (n : ℕ) :
    (qExpansion 1 (thetaZ8E4TimesDeltaPlaceholder hk δ : ℍ → ℂ)).coeff n =
      ∑ p ∈ antidiagonal n,
        eisensteinE4_qCoeff hk p.1 * (qExpansion 1 (δ : ℍ → ℂ)).coeff p.2 := by
  rw [thetaZ8E4TimesDeltaPlaceholder_coeff hk δ n]
  refine sum_congr rfl fun p _hp => ?_
  congr 1
  rw [eisensteinE4_qExpansion_coeff_eq_sigma3 hk]

/-- Degenerate but well-typed experiment: the zero weight-`12` form gives the zero weight-`16`
product (all `q`-coefficients `0`). -/
theorem thetaZ8E4TimesDelta_zero_coeff (n : ℕ) :
    (qExpansion 1 (thetaZ8E4TimesDeltaPlaceholder hk (0 : ModularForm Γ(1) 12) : ℍ → ℂ)).coeff n = 0 := by
  rw [thetaZ8E4TimesDeltaPlaceholder_qExpansion_mul hk (0 : ModularForm Γ(1) 12)]
  have hδ0 :
      qExpansion 1 ((0 : ModularForm Γ(1) 12) : ℍ → ℂ) = 0 := by
    rw [show ((0 : ModularForm Γ(1) 12) : ℍ → ℂ) = (0 : ℍ → ℂ) from ModularForm.coe_zero]
    exact qExpansion_zero (1 : ℝ)
  rw [hδ0, mul_zero]
  simp

end

end Hqiv.Algebra
