import Hqiv.Story.S3GoldbachAnnulusCircle
import Hqiv.Story.S3CumulativeHarmonicPhase

/-!
# Goldbach pair multiplicity on the π-normalized annulus

Multiple Goldbach pairs at one midpoint are **distinct left slots** on the same
`2N`-slot Hopf circle (not independent circles).  This module records the
machine-checked budget:

* pair count ≤ scan-slot capacity (`goldbachMidpointCount_le_scan_slots`);
* each survivor sits at angle `π · p / N` on the annulus;
* partner sweep angles sum to one full revolution `2π`;
* annulus arc width × slot count = `2π`;
* twiddle axis at `π`;
* certified counts at `N = 5` (`{3,5}`) and `N = 10` (`{3,7}`);
* named link to the harmonic leading scale `π (log N)²` (asymptotic slot).

The Hardy–Littlewood growth `~ n/(log n)²` is not proved here; the π-budget is
the **angular** and **harmonic-arc** normalization the stack already carries.
-/

namespace Hqiv.Story

open Hqiv.Geometry Real
open scoped BigOperators

noncomputable section

/-! ## Pair count vs scan capacity -/

theorem dual_midpoint_survivor_mem_scan_slots {N p : ℕ}
    (h : dualMidpointSurvivor N p) :
    p ∈ midpointScanSlots N := by
  rcases h with ⟨hp, _, hpN, _⟩
  exact (mem_midpointScanSlots_iff (N := N) (p := p)).mpr ⟨hp.two_le, hpN⟩

theorem mem_goldbach_midpoint_candidates_mem_scan_slots {N p : ℕ}
    (hp : p ∈ goldbachMidpointCandidates N) :
    p ∈ midpointScanSlots N :=
  dual_midpoint_survivor_mem_scan_slots
    ((mem_goldbachMidpointCandidates_iff (N := N) (p := p)).mp hp)

theorem dualMidpointLeftCandidates_subset_scan_slots (N : ℕ) :
    dualMidpointLeftCandidates N ⊆ midpointScanSlots N := by
  intro p hp
  exact dual_midpoint_survivor_mem_scan_slots
    ((mem_dualMidpointLeftCandidates_iff (N := N) (p := p)).mp hp)

theorem goldbachMidpointCount_le_scan_slot_count (N : ℕ) :
    goldbachMidpointCount N ≤ (midpointScanSlots N).card := by
  rw [goldbachMidpointCount_eq_leftCount]
  exact Finset.card_le_card (dualMidpointLeftCandidates_subset_scan_slots N)

theorem midpointScanSlots_card_le (N : ℕ) (hN : 2 ≤ N) :
    (midpointScanSlots N).card ≤ N - 1 := by
  simp only [midpointScanSlots]
  rw [Nat.card_Icc]
  omega

theorem goldbachMidpointCount_le_pred (N : ℕ) (hN : 2 ≤ N) :
    goldbachMidpointCount N ≤ N - 1 :=
  (goldbachMidpointCount_le_scan_slot_count N).trans (midpointScanSlots_card_le N hN)

theorem dualMidpointLeftCandidates_subset_range (N : ℕ) :
    dualMidpointLeftCandidates N ⊆ Finset.range (N + 1) := by
  intro p hp
  simp only [dualMidpointLeftCandidates, Finset.mem_filter, Finset.mem_range] at hp
  exact Finset.mem_range.mpr hp.1

theorem goldbachMidpointCount_le_succ (N : ℕ) :
    goldbachMidpointCount N ≤ N + 1 := by
  rw [goldbachMidpointCount_eq_leftCount]
  calc
    (dualMidpointLeftCandidates N).card ≤ (Finset.range (N + 1)).card :=
      Finset.card_le_card (dualMidpointLeftCandidates_subset_range N)
    _ = N + 1 := by simp

/-! ## π-normalized slot angles -/

theorem goldbach_left_arm_angle_eq_pi_mul_slot_over_N
    {N p : ℕ} (hN : 0 < N) (hp : p < goldbachAnnulusCircumference N) :
    goldbachLeftArmAngle N p hN hp =
      Real.pi * (p : ℝ) / (N : ℝ) := by
  have h := goldbach_left_arm_angle_eq N p hN hp
  dsimp [goldbachLeftArmAngle, goldbachAnnulusCircumference, shellSweepAngle] at h ⊢
  field_simp at h ⊢
  linarith

theorem goldbach_midpoint_pair_sweep_angles_sum_two_pi
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q)
    (hp : p < goldbachAnnulusCircumference N)
    (hq : q < goldbachAnnulusCircumference N) :
    shellSweepAngle (goldbach_shell_depth_pos hN) ⟨p, hp⟩ +
        shellSweepAngle (goldbach_shell_depth_pos hN) ⟨q, hq⟩ =
      2 * Real.pi := by
  dsimp [goldbachAnnulusCircumference, shellSweepAngle]
  rcases h with ⟨_, _, _, _, hsum⟩
  field_simp
  rw [← Nat.cast_add, hsum]

/-! ## One annulus = one `2π` arc budget -/

theorem goldbach_annulus_arc_width (N : ℕ) (hN : 0 < N) :
    shellArcWidth (goldbachAnnulusCircumference N) =
      Real.pi / (N : ℝ) := by
  unfold shellArcWidth goldbachAnnulusCircumference
  push_cast
  field_simp [show (N : ℝ) ≠ 0 from by positivity]

theorem goldbach_annulus_slots_times_width_eq_two_pi (N : ℕ) (hN : 0 < N) :
    (goldbachAnnulusCircumference N : ℝ) * shellArcWidth (goldbachAnnulusCircumference N) =
      2 * Real.pi := by
  unfold shellArcWidth goldbachAnnulusCircumference
  push_cast
  field_simp [show (N : ℝ) ≠ 0 from by positivity]

/-! ## Certified small-midpoint pair counts -/

theorem dualMidpointLeftCandidates_five :
    dualMidpointLeftCandidates 5 = ({3, 5} : Finset ℕ) := by decide

theorem dualMidpointLeftCandidates_ten :
    dualMidpointLeftCandidates 10 = ({3, 7} : Finset ℕ) := by decide

theorem goldbachMidpointCount_five :
    goldbachMidpointCount 5 = 2 := by
  rw [goldbachMidpointCount_eq_leftCount, dualMidpointLeftCandidates_five]
  decide

theorem goldbachMidpointCount_ten :
    goldbachMidpointCount 10 = 2 := by
  rw [goldbachMidpointCount_eq_leftCount, dualMidpointLeftCandidates_ten]
  decide

/-! ## Packaging: π circle budget + harmonic scale name -/

/--
**π-normalized annulus budget** at midpoint `N`: pair count capped by scan slots,
axis at `π`, and one `2π` arc partition for the `2N` Hopf slots.
-/
structure GoldbachAnnulusPiCircleBudget (N : ℕ) where
  hN : 0 < N
  pair_count_le_scan : goldbachMidpointCount N ≤ (midpointScanSlots N).card
  pair_count_le_succ : goldbachMidpointCount N ≤ N + 1
  axis_at_pi :
    shellSweepAngle (goldbach_shell_depth_pos hN)
        ⟨goldbachTwiddleAxis N, goldbach_twiddle_axis_lt_circumference hN⟩ = Real.pi
  annulus_two_pi :
    (goldbachAnnulusCircumference N : ℝ) *
        shellArcWidth (goldbachAnnulusCircumference N) = 2 * Real.pi

theorem goldbach_annulus_pi_circle_budget (N : ℕ) (hN : 0 < N) :
    GoldbachAnnulusPiCircleBudget N :=
  { hN := hN
    pair_count_le_scan := goldbachMidpointCount_le_scan_slot_count N
    pair_count_le_succ := goldbachMidpointCount_le_succ N
    axis_at_pi := goldbach_axis_angle_eq_pi hN
    annulus_two_pi := goldbach_annulus_slots_times_width_eq_two_pi N hN }

/--
**Harmonic π-scale name** for cumulative shell depth `N`: the leading arc–harmonic
weight `π (log N)²` (`S3CumulativeHarmonicPhase`) names the logarithmic cap on
additive phase load as shells stack — complementary to the per-midpoint finite
pair count above.
-/
structure GoldbachAnnulusHarmonicPiScale (N : ℕ) where
  circle_budget : GoldbachAnnulusPiCircleBudget N
  harmonic_leading : ℝ := totalArcHarmonicWeightLeadingApprox N
  harmonic_leading_eq : harmonic_leading = Real.pi * asymptoticLog N ^ 2

def goldbach_annulus_harmonic_pi_scale (N : ℕ) (hN : 0 < N) :
    GoldbachAnnulusHarmonicPiScale N :=
  { circle_budget := goldbach_annulus_pi_circle_budget N hN
    harmonic_leading_eq := rfl }

end

end Hqiv.Story
