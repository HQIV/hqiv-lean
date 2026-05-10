import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Tao–Rodgers / de Bruijn–Newman: sharp equivalence (proved) vs analytic inputs (external)

## What is **proved in this file** (pure real order theory)

Given **any** real `Λ` and the two assumptions

1. `RiemannHypothesis ↔ Λ ≤ 0` (de Bruijn–Newman bridge in some fixed normalization), and  
2. `0 ≤ Λ` (Rodgers–Tao 2018: Newman’s conjecture),

we **prove** the sharp equivalence `RiemannHypothesis ↔ Λ = 0`.

This is `sharp_equivalence_of_nonpos_bridge` below. No axioms, no `sorry`.

## What is **not** proved here

* Constructing the physical **de Bruijn–Newman constant** `Λ` from the heat flow / `H(λ,z)`.
* The analytic theorem `RiemannHypothesis ↔ Λ ≤ 0` for that constructed `Λ`.
* The Rodgers–Tao theorem `0 ≤ Λ` for that `Λ`.

Formalizing those is a large Mathlib-scale project; this module only locks in the **logical closure**
once those statements are available as hypotheses.

## References

* B. Rodgers, T. Tao, *The De Bruijn–Newman constant is non-negative* (2018).
* Standard sources on **RH ↔ Λ ≤ 0** in the de Bruijn–Newman formalism.
-/

namespace Hqiv.Physics

/-- **Core lemma (fully proved):** sharp `RH ↔ Λ = 0` from the nonpositive bridge and `Λ ≥ 0`.

This is exactly the argument: RH ⇒ `Λ ≤ 0` and `Λ ≥ 0` ⇒ `Λ = 0`; conversely `Λ = 0` ⇒ `Λ ≤ 0` ⇒ RH.
-/
theorem sharp_equivalence_of_nonpos_bridge {Λ : ℝ} (h_bridge : RiemannHypothesis ↔ Λ ≤ 0) (hΛ : 0 ≤ Λ) :
    RiemannHypothesis ↔ Λ = 0 := by
  constructor
  · intro hrh
    have hle : Λ ≤ 0 := h_bridge.mp hrh
    exact le_antisymm hle hΛ
  · intro hΛ0
    refine h_bridge.mpr ?_
    simp [hΛ0]

theorem RiemannHypothesis_of_lambda_eq_zero {Λ : ℝ} (h_bridge : RiemannHypothesis ↔ Λ ≤ 0) (hΛ : 0 ≤ Λ) :
    Λ = 0 → RiemannHypothesis :=
  (sharp_equivalence_of_nonpos_bridge h_bridge hΛ).mpr

theorem lambda_eq_zero_of_RiemannHypothesis {Λ : ℝ} (h_bridge : RiemannHypothesis ↔ Λ ≤ 0) (hΛ : 0 ≤ Λ) :
    RiemannHypothesis → Λ = 0 :=
  (sharp_equivalence_of_nonpos_bridge h_bridge hΛ).mp

/-- Data + analytic hypotheses for packaging the Rodgers–Tao story. -/
structure TaoRodgersHypotheses where
  Λ : ℝ
  rh_iff_lambda_nonpos : RiemannHypothesis ↔ Λ ≤ 0
  lambda_nonneg : 0 ≤ Λ

/-- The **sharp equivalence** for a bundled hypothesis record (definitionally the bridge lemma). -/
theorem RiemannHypothesis_iff_lambda_eq_zero (H : TaoRodgersHypotheses) :
    RiemannHypothesis ↔ H.Λ = 0 :=
  sharp_equivalence_of_nonpos_bridge H.rh_iff_lambda_nonpos H.lambda_nonneg

theorem lambda_eq_zero_iff_RiemannHypothesis (H : TaoRodgersHypotheses) :
    H.Λ = 0 ↔ RiemannHypothesis :=
  (RiemannHypothesis_iff_lambda_eq_zero H).symm

def TaoRodgersSharpEquivalence (H : TaoRodgersHypotheses) : Prop :=
  RiemannHypothesis ↔ H.Λ = 0

@[simp]
theorem taoRodgersSharpEquivalence_iff (H : TaoRodgersHypotheses) :
    TaoRodgersSharpEquivalence H ↔ (RiemannHypothesis ↔ H.Λ = 0) :=
  Iff.rfl

theorem taoRodgersSharpEquivalence_of_hyp (H : TaoRodgersHypotheses) :
    TaoRodgersSharpEquivalence H :=
  RiemannHypothesis_iff_lambda_eq_zero H

structure TaoRodgersPackage where
  hyp : TaoRodgersHypotheses
  rh_iff_lambda_eq_zero : RiemannHypothesis ↔ hyp.Λ = 0 :=
    RiemannHypothesis_iff_lambda_eq_zero hyp

def TaoRodgersHypotheses.toPackage (H : TaoRodgersHypotheses) : TaoRodgersPackage where
  hyp := H

end Hqiv.Physics
