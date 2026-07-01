import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.NBodyPhaseSpace` — the n-body phase-space recursion skeleton

The invariant `n`-body phase space `Rₙ` is built recursively by peeling off one particle and treating
the rest as an effective subsystem: `Rₙ = R₂ ⊗ R_{n−1}`. The integral that dresses this recursion needs
measure theory, but its two *kinematic* skeletons are pure algebra and are what fix when a channel is
open and how many independent variables it has.

* **Threshold recursion.** The production threshold is the mass sum `∑mᵢ`
  (`threshold_succ`: adding particle `n+1` raises it by `m_{n+1}`), so an open `n`-body channel always
  contains its `(n−1)`-body subsystem (`allowed_subsystem`) — the recursion `Rₙ = R₂ ⊗ R_{n−1}` at the
  level of thresholds.
* **Invariant-count recursion.** The number of independent kinematic invariants is `3n − 7`
  (`numInvariants`), rising by `3` per added particle (`numInvariants_succ`); at `n=3` it is `2`
  (`numInvariants_three`), exactly the dimension of the Dalitz plot.

Bundled in `NBodyClosure` / `nbody_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.NBodyPhaseSpace

/-- **Production threshold** of an `n`-body final state: the sum of the daughter masses. -/
def threshold {n : ℕ} (m : Fin n → ℝ) : ℝ := ∑ i, m i

/-- **Threshold recursion:** the `(n+1)`-body threshold is the `n`-body threshold of the first `n`
daughters plus the mass of the peeled-off particle — the skeleton of `Rₙ₊₁ = R₂ ⊗ Rₙ`. -/
theorem threshold_succ {n : ℕ} (m : Fin (n + 1) → ℝ) :
    threshold m = threshold (Fin.init m) + m (Fin.last n) := by
  simp only [threshold, Fin.sum_univ_castSucc, Fin.init]

theorem threshold_nonneg {n : ℕ} {m : Fin n → ℝ} (hm : ∀ i, 0 ≤ m i) : 0 ≤ threshold m :=
  Finset.sum_nonneg (fun i _ => hm i)

/-- A decay `M → (daughters)` is **threshold-allowed** when the parent mass clears the mass sum. -/
def Allowed {n : ℕ} (M : ℝ) (m : Fin n → ℝ) : Prop := threshold m ≤ M

/-- **An open `(n+1)`-body channel contains its `n`-body subsystem:** the recursion guarantees the
peeled subsystem is itself producible. -/
theorem allowed_subsystem {n : ℕ} {M : ℝ} {m : Fin (n + 1) → ℝ}
    (hlast : 0 ≤ m (Fin.last n)) (h : Allowed M m) : Allowed M (Fin.init m) := by
  unfold Allowed at h ⊢
  rw [threshold_succ] at h
  linarith

/-- **Two-body threshold** `m₀ + m₁` — the base case of the recursion. -/
theorem threshold_two (m : Fin 2 → ℝ) : threshold m = m 0 + m 1 := by
  simp [threshold, Fin.sum_univ_two]

/-! ## Counting independent kinematic invariants -/

/-- **Number of independent Lorentz-invariant kinematic variables** of an `n`-body final state,
`3n − 7` (valid for `n ≥ 2`). -/
def numInvariants (n : ℕ) : ℤ := 3 * (n : ℤ) - 7

/-- **Each additional particle adds three invariants.** -/
theorem numInvariants_succ (n : ℕ) : numInvariants (n + 1) = numInvariants n + 3 := by
  unfold numInvariants; push_cast; ring

/-- **At `n = 3` there are two invariants** — the dimension of the Dalitz plot. -/
theorem numInvariants_three : numInvariants 3 = 2 := by unfold numInvariants; norm_num

/-- **At `n = 4` there are five invariants.** -/
theorem numInvariants_four : numInvariants 4 = 5 := by unfold numInvariants; norm_num

/-! ## Closure -/

/-- **n-body phase-space discharge bundle.** -/
structure NBodyClosure : Prop where
  threshold_recursion : ∀ {n : ℕ} (m : Fin (n + 1) → ℝ),
    threshold m = threshold (Fin.init m) + m (Fin.last n)
  threshold_base : ∀ m : Fin 2 → ℝ, threshold m = m 0 + m 1
  subsystem_open : ∀ {n : ℕ} {M : ℝ} {m : Fin (n + 1) → ℝ},
    0 ≤ m (Fin.last n) → Allowed M m → Allowed M (Fin.init m)
  invariants_recursion : ∀ n, numInvariants (n + 1) = numInvariants n + 3
  invariants_dalitz : numInvariants 3 = 2

/-- **The n-body recursion is discharged:** thresholds peel one particle at a time down to the two-body
base, an open channel always contains its subsystem, and the invariant count grows by three per
particle with the Dalitz value `2` at `n=3` — PDG-free. -/
theorem nbody_closure : NBodyClosure where
  threshold_recursion := threshold_succ
  threshold_base := threshold_two
  subsystem_open := allowed_subsystem
  invariants_recursion := numInvariants_succ
  invariants_dalitz := numInvariants_three

end HqivSpine.Physics.NBodyPhaseSpace
