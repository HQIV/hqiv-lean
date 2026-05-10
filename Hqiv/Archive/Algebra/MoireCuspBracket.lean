import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

import Hqiv.Algebra.OctonionSphereFourierPatch

/-!
# Cusp moiré strategy (discrete patch)

This packages the **logic** behind the Python demo’s score-driven search on `Fin n`:

* **Cumulative absolute variation** — same object as the running sum of `|S(i+1)−S(i)|` in
  `scripts/hqiv_geometric_3sat_demo.py`. It is **monotone** in the patch index.

* **Triangle inequality on slope steps** — `|Δ²S| ≤ |ΔS_{j+1}| + |ΔS_j|` (Gaussian lens step).

“Cusp” means the **discrete threshold crossing** of monotone cumulative variation, not a modular cusp.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Hqiv.Algebra

variable {n : ℕ}

lemma succ_lt_n_of_lt {j : Fin n} {i : ℕ} (hi : i < j.val) : i + 1 < n :=
  Nat.lt_of_le_of_lt (Nat.succ_le_iff.mpr hi) j.is_lt

lemma lt_n_of_lt {j : Fin n} {i : ℕ} (hi : i < j.val) : i < n :=
  Nat.lt_trans hi j.is_lt

lemma succ_lt_n_of_mem_Ico {j k : Fin n} {i : ℕ} (hi : i ∈ Finset.Ico j.val k.val) : i + 1 < n := by
  have hik := (Finset.mem_Ico.mp hi).2
  exact Nat.lt_of_le_of_lt (Nat.succ_le_iff.mpr hik) k.is_lt

lemma lt_n_of_mem_Ico {j k : Fin n} {i : ℕ} (hi : i ∈ Finset.Ico j.val k.val) : i < n :=
  Nat.lt_trans (Finset.mem_Ico.mp hi).2 k.is_lt

/-- Absolute edge increment at `i` relative to an upper bound `j` (`i < j`). -/
noncomputable def moireEdgeAbs (S : MoirePatchScore n) (j : Fin n) {i : ℕ} (hi : i < j.val) : ℝ :=
  |S ⟨i + 1, succ_lt_n_of_lt hi⟩ - S ⟨i, lt_n_of_lt hi⟩|

/-- Cumulative total variation along indices `0 … j−1` (empty at `j = 0`). -/
noncomputable def moireCumulativeAbsVariation (S : MoirePatchScore n) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.range j.val,
    if hi : i < j.val then
      |S ⟨i + 1, succ_lt_n_of_lt hi⟩ - S ⟨i, lt_n_of_lt hi⟩|
    else 0

/-- Pointwise kernel for `moireCumulativeAbsVariation` at a chosen cutoff `t`. -/
noncomputable def moireAbsDiffKernel (S : MoirePatchScore n) (t : Fin n) (i : ℕ) : ℝ :=
  if hi : i < t.val then
    |S ⟨i + 1, succ_lt_n_of_lt hi⟩ - S ⟨i, lt_n_of_lt hi⟩|
  else 0

lemma moireCumulativeAbsVariation_eq_kernel (S : MoirePatchScore n) (j : Fin n) :
    moireCumulativeAbsVariation S j = ∑ i ∈ Finset.range j.val, moireAbsDiffKernel S j i := rfl

lemma range_eq_union_Ico {j k : ℕ} (hjk : j ≤ k) :
    Finset.range k = Finset.range j ∪ Finset.Ico j k := by
  ext i
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  omega

lemma disjoint_range_Ico (j k : ℕ) (_hjk : j ≤ k) :
    Disjoint (Finset.range j) (Finset.Ico j k) := by
  classical
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  simp only [Finset.mem_range, Finset.mem_Ico] at ha hb
  subst hab
  omega

lemma moireAbsDiffKernel_eq_on_initial {S : MoirePatchScore n} {j k : Fin n}
    (hjk : j.val ≤ k.val) {i : ℕ} (hi : i ∈ Finset.range j.val) :
    moireAbsDiffKernel S j i = moireAbsDiffKernel S k i := by
  have hij : i < j.val := Finset.mem_range.mp hi
  have hik : i < k.val := Nat.lt_of_lt_of_le hij hjk
  simp [moireAbsDiffKernel, hij, hik]

lemma moireAbsDiffKernel_Ico {S : MoirePatchScore n} {j k : Fin n} {i : ℕ}
    (hi : i ∈ Finset.Ico j.val k.val) :
    moireAbsDiffKernel S k i =
      |S ⟨i + 1, succ_lt_n_of_mem_Ico hi⟩ - S ⟨i, lt_n_of_mem_Ico hi⟩| := by
  have hik : i < k.val := (Finset.mem_Ico.mp hi).2
  simp [moireAbsDiffKernel, hik]

/-- Split of cumulative variation along `range k = range j ⊔ Ico j k` (for `j ≤ k`). -/
lemma moireCumulativeAbsVariation_split (S : MoirePatchScore n) {j k : Fin n} (hjk : j.val ≤ k.val) :
    moireCumulativeAbsVariation S k =
      moireCumulativeAbsVariation S j +
        ∑ i ∈ Finset.Ico j.val k.val,
          (if hi : i ∈ Finset.Ico j.val k.val then
            |S ⟨i + 1, succ_lt_n_of_mem_Ico hi⟩ - S ⟨i, lt_n_of_mem_Ico hi⟩|
          else 0) := by
  classical
  have hrange : Finset.range k.val = Finset.range j.val ∪ Finset.Ico j.val k.val :=
    range_eq_union_Ico hjk
  have hdisj : Disjoint (Finset.range j.val) (Finset.Ico j.val k.val) :=
    disjoint_range_Ico j.val k.val hjk
  have hsum :
      (∑ i ∈ Finset.range k.val, moireAbsDiffKernel S k i) =
        (∑ i ∈ Finset.range j.val, moireAbsDiffKernel S k i) +
          ∑ i ∈ Finset.Ico j.val k.val, moireAbsDiffKernel S k i := by
    calc
      ∑ i ∈ Finset.range k.val, moireAbsDiffKernel S k i
          = ∑ i ∈ Finset.range j.val ∪ Finset.Ico j.val k.val, moireAbsDiffKernel S k i := by
              rw [hrange]
      _ = ∑ i ∈ Finset.range j.val, moireAbsDiffKernel S k i +
            ∑ i ∈ Finset.Ico j.val k.val, moireAbsDiffKernel S k i :=
            Finset.sum_union hdisj
  have hleft :
      ∑ i ∈ Finset.range j.val, moireAbsDiffKernel S k i =
        ∑ i ∈ Finset.range j.val, moireAbsDiffKernel S j i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact (moireAbsDiffKernel_eq_on_initial (S := S) hjk hi).symm
  have hright :
      ∑ i ∈ Finset.Ico j.val k.val, moireAbsDiffKernel S k i =
        ∑ i ∈ Finset.Ico j.val k.val,
          (if hi : i ∈ Finset.Ico j.val k.val then
            |S ⟨i + 1, succ_lt_n_of_mem_Ico hi⟩ - S ⟨i, lt_n_of_mem_Ico hi⟩|
          else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [moireAbsDiffKernel_Ico (S := S) hi]
    rw [dif_pos hi]
  rw [moireCumulativeAbsVariation_eq_kernel, hsum, hleft, hright]
  simp [moireCumulativeAbsVariation_eq_kernel]

lemma moireCumulativeAbsVariation_nonneg (S : MoirePatchScore n) (j : Fin n) :
    0 ≤ moireCumulativeAbsVariation S j := by
  classical
  dsimp [moireCumulativeAbsVariation]
  refine Finset.sum_nonneg ?_
  intro i _
  split_ifs
  · exact abs_nonneg _
  · rfl

lemma moireCumulativeAbsVariation_mono (S : MoirePatchScore n) {j k : Fin n}
    (hjk : j.val ≤ k.val) :
    moireCumulativeAbsVariation S j ≤ moireCumulativeAbsVariation S k := by
  classical
  have hEq :
      ∑ i ∈ Finset.range j.val, moireAbsDiffKernel S j i =
        ∑ i ∈ Finset.range j.val, moireAbsDiffKernel S k i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact moireAbsDiffKernel_eq_on_initial (S := S) hjk hi
  have hsub : Finset.range j.val ⊆ Finset.range k.val :=
    Finset.range_subset_range.mpr hjk
  have hle :
      ∑ i ∈ Finset.range j.val, moireAbsDiffKernel S k i ≤
        ∑ i ∈ Finset.range k.val, moireAbsDiffKernel S k i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i hi hi'
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_range, not_lt] at hi'
    have hik : i < k.val := hi
    simp [moireAbsDiffKernel, hik]
  rw [moireCumulativeAbsVariation_eq_kernel, moireCumulativeAbsVariation_eq_kernel, hEq]
  exact hle

/-!
### Triangle inequality: second difference (slope step) controlled by adjacent slopes
-/

theorem abs_moirePatchSlopeStep_le_add_adjacent_slopes {n : ℕ} (hn : 2 < n) (S : MoirePatchScore n)
    (j : Fin (n - 2)) :
    |moirePatchSlopeStep hn S j|
      ≤ |S ⟨j.val + 2, by omega⟩ - S ⟨j.val + 1, by omega⟩| +
        |S ⟨j.val + 1, by omega⟩ - S ⟨j.val, by omega⟩| := by
  have hn1 : 1 < n := by omega
  have hsplit :
      moirePatchSlopeStep hn S j =
        (S ⟨j.val + 2, by omega⟩ - S ⟨j.val + 1, by omega⟩) -
          (S ⟨j.val + 1, by omega⟩ - S ⟨j.val, by omega⟩) := by
    simp [moirePatchSlopeStep, moirePatchScoreSlope]
  rw [hsplit]
  let a := S ⟨j.val + 2, by omega⟩ - S ⟨j.val + 1, by omega⟩
  let b := S ⟨j.val + 1, by omega⟩ - S ⟨j.val, by omega⟩
  calc
    |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

/-!
### Cusp bracket at a strict one-step crossing
-/

theorem moire_below_threshold_on_initial_segment {S : MoirePatchScore n} {T : ℝ} {j₀ : Fin n}
    (hjn : j₀.val + 1 < n) (hlt : moireCumulativeAbsVariation S j₀ < T)
    (_hge : T ≤ moireCumulativeAbsVariation S ⟨j₀.val + 1, hjn⟩)
    (k : Fin n) (hk : k.val ≤ j₀.val) :
    moireCumulativeAbsVariation S k < T := by
  have hk2 : moireCumulativeAbsVariation S k ≤ moireCumulativeAbsVariation S j₀ :=
    moireCumulativeAbsVariation_mono S hk
  linarith

theorem moire_first_ge_threshold_eq_succ {S : MoirePatchScore n} {T : ℝ} {j₀ : Fin n}
    (hjn : j₀.val + 1 < n)
    (hlt : moireCumulativeAbsVariation S j₀ < T)
    (hge : T ≤ moireCumulativeAbsVariation S ⟨j₀.val + 1, hjn⟩) :
    IsLeast { j : Fin n | T ≤ moireCumulativeAbsVariation S j } ⟨j₀.val + 1, hjn⟩ := by
  constructor
  · exact hge
  · intro j hj
    simp only [Set.mem_setOf] at hj
    by_cases h : j.val ≤ j₀.val
    · have hltj := moire_below_threshold_on_initial_segment (S := S) (T := T) (j₀ := j₀) hjn hlt hge j h
      linarith [hj, hltj]
    · push_neg at h
      have hlt : j₀.val < j.val := h
      exact Fin.le_iff_val_le_val.mpr (Nat.succ_le_iff.mpr hlt)

theorem moire_last_below_threshold_eq_pred {S : MoirePatchScore n} {T : ℝ} {j₀ : Fin n}
    (hjn : j₀.val + 1 < n)
    (hlt : moireCumulativeAbsVariation S j₀ < T)
    (hge : T ≤ moireCumulativeAbsVariation S ⟨j₀.val + 1, hjn⟩) :
    IsGreatest { j : Fin n | moireCumulativeAbsVariation S j < T } j₀ := by
  constructor
  · exact hlt
  · intro k hk
    simp only [Set.mem_setOf] at hk
    by_cases h : k.val ≤ j₀.val
    · exact Fin.le_iff_val_le_val.mpr h
    · push_neg at h
      have hk'' : j₀.val + 1 ≤ k.val := Nat.succ_le_iff.mpr h
      have mono :=
        moireCumulativeAbsVariation_mono (S := S)
          (j := ⟨j₀.val + 1, hjn⟩) (k := k) hk''
      have Tlek : T ≤ moireCumulativeAbsVariation S k := le_trans hge mono
      exact absurd hk (not_lt_of_ge Tlek)

end Hqiv.Algebra

end
