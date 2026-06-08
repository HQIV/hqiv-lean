import Mathlib.Data.Complex.Basic

import Hqiv.Algebra.IntegerLatticeShellCount8

/-!
# Modular / theta **coefficient bridge** (M1 on the modular ladder)

The classical generating series attached to shell counts on `ℤ⁸` has the form
`∑_{m ≥ 0} r₈(m) q^m`. The arithmetic coefficient at `q^m` is **`r₈(m)`**, already defined in
`IntegerLatticeShellCount8` as `r8`.

This module exposes that stream under the name `thetaZ8FormalCoeff` and packages optional
**hypotheses** (`CoeffsAgreeWithR8`) for later comparison with Mathlib’s modular-form API.

**Not here:** `ModularForm`, Hecke operators, Jacobi product formula for `r₈(m)`, or tensor products
with `Δ`. See `AGENTS/MODULAR_THETA_ACTION_PLAN.md` and `AGENTS/MODULAR_THETA_CURVATURE_BRIDGE.md`.
-/

namespace Hqiv.Algebra

/-- Coefficient of `q^m` in the formal series `∑ r₈(m) q^m` (definitionally `r8 m`). -/
def thetaZ8FormalCoeff (m : ℕ) : ℕ :=
  r8 m

@[simp]
theorem thetaZ8FormalCoeff_eq_r8 (m : ℕ) : thetaZ8FormalCoeff m = r8 m :=
  rfl

/-- Hypothesis: a complex coefficient stream agrees with embedded shell counts `r8`. -/
structure CoeffsAgreeWithR8 (a : ℕ → ℂ) : Prop where
  eq : ∀ m : ℕ, a m = (r8 m : ℂ)

theorem coeffsAgreeWithR8_of (a : ℕ → ℂ) (h : ∀ m : ℕ, a m = (r8 m : ℂ)) : CoeffsAgreeWithR8 a :=
  ⟨h⟩

/-- Coerced shell counts as a canonical `ℕ → ℂ` stream (always satisfies `CoeffsAgreeWithR8`). -/
noncomputable def thetaZ8FormalCoeffComplex (m : ℕ) : ℂ :=
  (r8 m : ℂ)

theorem coeffsAgree_thetaZ8FormalCoeffComplex : CoeffsAgreeWithR8 thetaZ8FormalCoeffComplex :=
  coeffsAgreeWithR8_of _ fun _ => rfl

end Hqiv.Algebra
