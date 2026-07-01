import HqivSpine.Physics.StellarStructure

/-!
# `HqivSpine.Physics.StellarCollapse` — the finite support budget (Chandrasekhar-style bound)

`StellarStructure` showed every shell is held up by a positive pressure drop `w(m) > 0`. But the
**total** support a star can muster is *finite*: the per-shell drops telescope, and because the
pressure profile decays to zero the integrated support is bounded by the central pressure `K`.

* **Telescoping budget.** The support of the inner `N` shells sums to `K·(1 − shellShape N)`
  (`support_partialSum_eq`), strictly increasing in `N` (`support_partialSum_strictMono`) and always
  strictly below the central pressure `K` (`support_partialSum_lt_central`).
* **The collapse threshold.** A gravitational demand `D ≥ K` exceeds the entire support budget, so it
  can **never** be met at any finite shell count (`collapse_above_budget`): a star whose binding
  demand exceeds its central-pressure budget `K` has no hydrostatic equilibrium and must collapse.
  The central pressure `K` plays the role of the Chandrasekhar ceiling.

Bundled in `CollapseClosure` / `stellar_collapse_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.StellarCollapse

open HqivSpine.Physics HqivSpine.Physics.StellarStructure

/-- **Telescoping:** the support of the inner `N` shells is the central-to-`N` pressure drop. -/
theorem support_partialSum (K : ℝ) (N : ℕ) :
    ∑ m ∈ Finset.range N, hydrostaticSupport K m = stellarPressure K 0 - stellarPressure K N := by
  simp only [hydrostaticSupport]
  exact Finset.sum_range_sub' (fun m => stellarPressure K m) N

/-- The integrated support budget over the inner `N` shells is `K·(1 − shellShape N)`. -/
theorem support_partialSum_eq (K : ℝ) (N : ℕ) :
    ∑ m ∈ Finset.range N, hydrostaticSupport K m = K * (1 - shellShape N) := by
  rw [support_partialSum, stellarPressure_center, stellarPressure]; ring

/-- The budget **strictly increases** with shell count (more shells, more total support). -/
theorem support_partialSum_strictMono {K : ℝ} (hK : 0 < K) :
    StrictMono (fun N => ∑ m ∈ Finset.range N, hydrostaticSupport K m) := by
  apply strictMono_nat_of_lt_succ
  intro N
  rw [Finset.sum_range_succ]
  have := hydrostaticSupport_pos hK N
  linarith

/-- The support budget is **always strictly below the central pressure** `K` — a finite ceiling. -/
theorem support_partialSum_lt_central {K : ℝ} (hK : 0 < K) (N : ℕ) :
    ∑ m ∈ Finset.range N, hydrostaticSupport K m < K := by
  rw [support_partialSum_eq]
  have hs := shellShape_pos N
  nlinarith [mul_pos hK hs]

/-- **The collapse threshold.** A gravitational demand `D ≥ K` exceeds the entire support budget and
can never be met at any finite shell count: no hydrostatic equilibrium exists, so the star collapses.
The central pressure `K` is the Chandrasekhar-style ceiling. -/
theorem collapse_above_budget {K D : ℝ} (hK : 0 < K) (hD : K ≤ D) (N : ℕ) :
    ∑ m ∈ Finset.range N, hydrostaticSupport K m < D :=
  lt_of_lt_of_le (support_partialSum_lt_central hK N) hD

/-! ## Closure -/

/-- **Stellar-collapse discharge bundle.** -/
structure CollapseClosure : Prop where
  budget : ∀ (K : ℝ) (N : ℕ),
    ∑ m ∈ Finset.range N, hydrostaticSupport K m = K * (1 - shellShape N)
  budget_bounded : ∀ {K : ℝ}, 0 < K → ∀ N : ℕ,
    ∑ m ∈ Finset.range N, hydrostaticSupport K m < K
  collapse : ∀ {K D : ℝ}, 0 < K → K ≤ D → ∀ N : ℕ,
    ∑ m ∈ Finset.range N, hydrostaticSupport K m < D

/-- **Stellar collapse is discharged:** the integrated hydrostatic support is a finite budget capped
by the central pressure `K`, so a binding demand above `K` admits no equilibrium and forces collapse. -/
theorem stellar_collapse_closure : CollapseClosure where
  budget := support_partialSum_eq
  budget_bounded := support_partialSum_lt_central
  collapse := collapse_above_budget

end HqivSpine.Physics.StellarCollapse
