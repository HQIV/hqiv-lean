import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hqiv.Geometry

open scoped BigOperators

noncomputable section

/-- Kept channel set for Bool-indexed truncation masks. -/
def keptIdx (keep : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => keep i)

/-- Dropped channel set for Bool-indexed truncation masks. -/
def droppedIdx (keep : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => !(keep i))

/-- Full weighted edge-priority contribution across all channels. -/
def weightedPriority (amp weight : Fin n → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin n => amp i * weight i)

/-- Truncated weighted contribution, retaining only kept channels. -/
def weightedPriorityKept (amp weight : Fin n → ℝ) (keep : Fin n → Bool) : ℝ :=
  Finset.sum (keptIdx keep) (fun i : Fin n => amp i * weight i)

/-- Weighted contribution of dropped channels only. -/
def weightedPriorityDropped (amp weight : Fin n → ℝ) (keep : Fin n → Bool) : ℝ :=
  Finset.sum (droppedIdx keep) (fun i : Fin n => amp i * weight i)

/-- Residual mass tracked by Phase-2 truncation telemetry. -/
def droppedWeightMass (weight : Fin n → ℝ) (keep : Fin n → Bool) : ℝ :=
  Finset.sum (droppedIdx keep) (fun i : Fin n => |weight i|)

/--
Exact split: full weighted priority equals kept plus dropped channel contributions.
-/
theorem weightedPriority_split
    (amp weight : Fin n → ℝ)
    (keep : Fin n → Bool) :
    weightedPriority amp weight
      = weightedPriorityKept amp weight keep + weightedPriorityDropped amp weight keep := by
  unfold weightedPriority weightedPriorityKept weightedPriorityDropped keptIdx droppedIdx
  simpa using
    (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun i : Fin n => keep i) (f := fun i => amp i * weight i)).symm

/--
Exact truncation error identity: dropped contribution is the full-minus-kept gap.
-/
theorem weightedPriority_error_eq_dropped
    (amp weight : Fin n → ℝ)
    (keep : Fin n → Bool) :
    weightedPriority amp weight - weightedPriorityKept amp weight keep
      = weightedPriorityDropped amp weight keep := by
  have hsplit := weightedPriority_split amp weight keep
  linarith

/--
Absolute truncation error is bounded by dropped absolute contribution.
-/
theorem abs_weightedPriority_error_le_dropped_abs
    (amp weight : Fin n → ℝ)
    (keep : Fin n → Bool) :
    |weightedPriority amp weight - weightedPriorityKept amp weight keep|
      ≤ Finset.sum (droppedIdx keep) (fun i : Fin n => |amp i * weight i|) := by
  rw [weightedPriority_error_eq_dropped amp weight keep]
  simpa [weightedPriorityDropped] using
    (Finset.abs_sum_le_sum_abs (s := droppedIdx keep) (f := fun i : Fin n => amp i * weight i))

/--
Phase-2 proof channel:
if each local amplitude satisfies `|amp i| ≤ 1`, truncation error from dropping
channels is bounded by dropped weight mass.
-/
theorem abs_weightedPriority_error_le_droppedWeightMass_of_unit_amp
    (amp weight : Fin n → ℝ)
    (keep : Fin n → Bool)
    (hUnit : ∀ i : Fin n, |amp i| ≤ 1) :
    |weightedPriority amp weight - weightedPriorityKept amp weight keep|
      ≤ droppedWeightMass weight keep := by
  refine le_trans (abs_weightedPriority_error_le_dropped_abs amp weight keep) ?_
  unfold droppedWeightMass
  refine Finset.sum_le_sum ?_
  intro i hi
  have hwi : 0 ≤ |weight i| := abs_nonneg (weight i)
  have hmul : |amp i| * |weight i| ≤ 1 * |weight i| :=
    mul_le_mul_of_nonneg_right (hUnit i) hwi
  calc
    |amp i * weight i| = |amp i| * |weight i| := by simp [abs_mul]
    _ ≤ 1 * |weight i| := hmul
    _ = |weight i| := by ring

/--
Gate form of the Phase-2 truncation certificate:
if dropped mass is below a gate threshold and amplitudes are unit-bounded,
then truncation error is also below that gate.
-/
theorem abs_weightedPriority_error_le_gate_of_unit_amp_of_droppedWeightMass_le
    (amp weight : Fin n → ℝ)
    (keep : Fin n → Bool)
    (gate : ℝ)
    (hUnit : ∀ i : Fin n, |amp i| ≤ 1)
    (hMassGate : droppedWeightMass weight keep ≤ gate) :
    |weightedPriority amp weight - weightedPriorityKept amp weight keep| ≤ gate := by
  exact le_trans
    (abs_weightedPriority_error_le_droppedWeightMass_of_unit_amp amp weight keep hUnit)
    hMassGate

end

end Hqiv.Geometry

