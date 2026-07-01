import HqivSpine.Physics.MandelstamInvariants

/-!
# `HqivSpine.Physics.DalitzPlot` — three-body phase space and the Dalitz sum rule

The three-body sequel to `MandelstamInvariants`. For a decay `M → 1 2 3` the three pairwise invariant
masses `s_{ij} = (pᵢ+pⱼ)²` are the Dalitz coordinates, and they obey the exact three-body analogue of
the Mandelstam `s+t+u` rule.

* **Dalitz sum rule.** Unconditionally on four-momenta,
  `s₁₂ + s₁₃ + s₂₃ = (p₁+p₂+p₃)² + p₁² + p₂² + p₃²` (`dalitz_sum`); on-shell with parent mass `M`
  this is `s₁₂ + s₁₃ + s₂₃ = M² + m₁² + m₂² + m₃²` (`dalitz_sum_onShell`).
* **One coordinate is dependent.** The third invariant is fixed by the other two (`dalitz_constraint`),
  so the Dalitz density lives on a 2D region — the defining feature of the Dalitz plot.

Bundled in `DalitzClosure` / `dalitz_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.DalitzPlot

open HqivSpine.Physics HqivSpine.Physics.MandelstamInvariants

/-- **Pairwise invariant mass squared** `s_{ij} = (pᵢ+pⱼ)²`. -/
def invMassSq (pi pj : Fin 4 → ℝ) : ℝ := mink4 (pi + pj)

/-- **The Dalitz sum rule (unconditional):** the three pairwise invariants sum to the parent invariant
plus the three daughter invariants. The three-body analogue of `s+t+u = ∑mᵢ²`. -/
theorem dalitz_sum (p1 p2 p3 : Fin 4 → ℝ) :
    invMassSq p1 p2 + invMassSq p1 p3 + invMassSq p2 p3
      = mink4 (p1 + p2 + p3) + mink4 p1 + mink4 p2 + mink4 p3 := by
  simp only [invMassSq, mink4, Pi.add_apply]; ring

/-- **Dalitz sum rule on-shell:** with parent mass `M` and daughters on their mass shells,
`s₁₂ + s₁₃ + s₂₃ = M² + m₁² + m₂² + m₃²`. -/
theorem dalitz_sum_onShell {p1 p2 p3 : Fin 4 → ℝ} {M m1 m2 m3 : ℝ}
    (hM : OnShell (p1 + p2 + p3) M) (h1 : OnShell p1 m1) (h2 : OnShell p2 m2) (h3 : OnShell p3 m3) :
    invMassSq p1 p2 + invMassSq p1 p3 + invMassSq p2 p3 = M ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 := by
  rw [dalitz_sum p1 p2 p3]
  rw [show mink4 (p1 + p2 + p3) = M ^ 2 from hM, show mink4 p1 = m1 ^ 2 from h1,
    show mink4 p2 = m2 ^ 2 from h2, show mink4 p3 = m3 ^ 2 from h3]

/-- **The third Dalitz coordinate is determined by the other two** — the Dalitz plot is two-dimensional. -/
theorem dalitz_constraint {p1 p2 p3 : Fin 4 → ℝ} {M m1 m2 m3 : ℝ}
    (hM : OnShell (p1 + p2 + p3) M) (h1 : OnShell p1 m1) (h2 : OnShell p2 m2) (h3 : OnShell p3 m3) :
    invMassSq p2 p3 = M ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 - invMassSq p1 p2 - invMassSq p1 p3 := by
  have h := dalitz_sum_onShell hM h1 h2 h3
  linarith

/-! ## Closure -/

/-- **Dalitz discharge bundle.** -/
structure DalitzClosure : Prop where
  sum_rule : ∀ p1 p2 p3 : Fin 4 → ℝ,
    invMassSq p1 p2 + invMassSq p1 p3 + invMassSq p2 p3
      = mink4 (p1 + p2 + p3) + mink4 p1 + mink4 p2 + mink4 p3
  sum_rule_onShell : ∀ {p1 p2 p3 : Fin 4 → ℝ} {M m1 m2 m3 : ℝ},
    OnShell (p1 + p2 + p3) M → OnShell p1 m1 → OnShell p2 m2 → OnShell p3 m3 →
    invMassSq p1 p2 + invMassSq p1 p3 + invMassSq p2 p3 = M ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2
  dependent_coordinate : ∀ {p1 p2 p3 : Fin 4 → ℝ} {M m1 m2 m3 : ℝ},
    OnShell (p1 + p2 + p3) M → OnShell p1 m1 → OnShell p2 m2 → OnShell p3 m3 →
    invMassSq p2 p3 = M ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 - invMassSq p1 p2 - invMassSq p1 p3

/-- **The Dalitz story is discharged:** the three pairwise invariants obey the three-body sum rule, and
the plot is genuinely two-dimensional — PDG-free. -/
theorem dalitz_closure : DalitzClosure where
  sum_rule := dalitz_sum
  sum_rule_onShell := dalitz_sum_onShell
  dependent_coordinate := dalitz_constraint

end HqivSpine.Physics.DalitzPlot
