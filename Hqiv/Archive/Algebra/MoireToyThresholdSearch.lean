import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Bounds.Basic

import Hqiv.Archive.Algebra.MoireCuspBracket

/-!
# Toy threshold search (aligned with `hqiv_geometric_3sat_demo.py`)

The Python script builds a monotone sequence `cum[j]` (cumulative `|ΔS|` on the patch), chooses a
threshold `T ∈ [0, cum_total]` (`variation_threshold`), and runs binary search for:

* the **smallest** `j` with `cum[j] ≥ T` (`binary_search_smallest_true` on `pred_ge`);
* the **largest** `j` with `cum[j] < T` (`binary_search_largest_true` on `pred_lt`).

**This file does not relate `cum` or `T` to SAT.** It only pins down the **order-theoretic** meaning of
“first crossing” / “best `j`” for the score pipeline:

1. `moireCumulativeAbsVariation` is **monotone** in the patch index (`moireCumulativeAbsVariation_mono`).
2. Therefore the predicate `j ↦ (T ≤ moireCumulativeAbsVariation S j)` is **upward closed** on `Fin n`.
3. If there is at least one index above threshold, there is a **unique least** such index in `Fin n`
   order — exactly what the left binary search is designed to return under the usual monotonicity
   hypotheses on `pred`.
4. A **one-step** first crossing is already characterized as `IsLeast` / `IsGreatest` in
   `MoireCuspBracket` (`moire_first_ge_threshold_eq_succ`, `moire_last_below_threshold_eq_pred`).

Use empirical tests (Python) to falsify any **stronger** bridge; use Lean for this discrete search logic.
-/

noncomputable section

open scoped BigOperators
open Finset Set

namespace Hqiv.Algebra

variable {n : ℕ} (S : MoirePatchScore n) (T : ℝ)

/-- Predicate “cumulative variation has reached `T` at `j`” — matches `cum[j] ≥ T` in the demo. -/
def moireCumGeThreshold (j : Fin n) : Prop :=
  T ≤ moireCumulativeAbsVariation S j

theorem moire_cum_ge_upward_closed {i j : Fin n} (hij : i ≤ j) (hi : moireCumGeThreshold S T i) :
    moireCumGeThreshold S T j := by
  dsimp [moireCumGeThreshold] at hi ⊢
  exact le_trans hi (moireCumulativeAbsVariation_mono S (Fin.le_iff_val_le_val.mp hij))

theorem moire_cum_lt_downward_closed {i j : Fin n} (hij : i ≤ j)
    (hj : moireCumulativeAbsVariation S j < T) :
    moireCumulativeAbsVariation S i < T := by
  have mono := moireCumulativeAbsVariation_mono S (j := i) (k := j) (Fin.le_iff_val_le_val.mp hij)
  linarith [mono]

/-- If some patch index is above threshold, there is a **least** such index (Fin order). -/
theorem exists_isLeast_moire_cum_ge (_hn : 0 < n)
    (hex : ∃ j : Fin n, moireCumGeThreshold S T j) :
    ∃ j : Fin n, IsLeast { j : Fin n | moireCumGeThreshold S T j } j := by
  classical
  obtain ⟨j0, hj0⟩ := hex
  let pred : Fin n → Prop := fun j => moireCumGeThreshold S T j
  haveI (j : Fin n) : Decidable (pred j) := Classical.propDecidable _
  let s := Finset.univ.filter pred
  have hj0' : j0 ∈ s := Finset.mem_filter.mpr ⟨mem_univ _, hj0⟩
  have hne : s.Nonempty := ⟨j0, hj0'⟩
  refine ⟨s.min' hne, ?_⟩
  convert isLeast_min' s hne using 1
  ext j
  simp [pred, moireCumGeThreshold, s]

/-- If some index is still strictly below threshold, there is a **greatest** such index. -/
theorem exists_isGreatest_moire_cum_lt (_hn : 0 < n)
    (hex : ∃ j : Fin n, moireCumulativeAbsVariation S j < T) :
    ∃ j : Fin n, IsGreatest { j : Fin n | moireCumulativeAbsVariation S j < T } j := by
  classical
  obtain ⟨j0, hj0⟩ := hex
  let pred : Fin n → Prop := fun j => moireCumulativeAbsVariation S j < T
  haveI (j : Fin n) : Decidable (pred j) := Classical.propDecidable _
  let s := Finset.univ.filter pred
  have hj0' : j0 ∈ s := Finset.mem_filter.mpr ⟨mem_univ _, hj0⟩
  have hne : s.Nonempty := ⟨j0, hj0'⟩
  refine ⟨s.max' hne, ?_⟩
  convert isGreatest_max' s hne using 1
  ext j
  simp [pred, s]

/-!
### Relation to the one-step lemmas in `MoireCuspBracket`

If the first time `T` is crossed is a **single** index step (`j₀` below, `j₀+1` at or above), then
`moire_first_ge_threshold_eq_succ` already identifies that `j₀+1` as `IsLeast` for `moireCumGeThreshold`,
and `moire_last_below_threshold_eq_pred` identifies `j₀` as `IsGreatest` for the strict-below set.
-/

end Hqiv.Algebra

end
