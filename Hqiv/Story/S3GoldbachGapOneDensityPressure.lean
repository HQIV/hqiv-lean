import Hqiv.Story.S3GoldbachGapOneActivationBudget
import Hqiv.Story.S3GoldbachSlotPhaseCouplingBridge
import Hqiv.Story.S3SquareOrbitGapOneBridge

/-!
# Gap-one activation pressure, square-ladder density, cap–coupling integration

Packages the **density / pressure** layer requested after the anchor discharge at
`N = 4`:

* **Twin activation pressure** — infinitely often along the midpoint ladder,
  `goldbachGapOneActivationMass > 0` with each spike bounded by the per-`N` cap.
* **Square-ladder gap-one symmetric pressure** — existence along `m²` (certified
  only at `m = 2` today; infinite density is open and ≠ twin density).
* **Cap-respecting on-line zeros** — slot-phase budget ⇒ coupling + square-root
  weights without needing obstruction at every `m`.
-/

namespace Hqiv.Story

open Hqiv.Geometry Real Complex
open scoped BigOperators

noncomputable section

/-! ## Twin activation pressure (midpoint ladder) -/

/--
**Gap-one activation pressure.**  Along the midpoint index, twin / gap-one activation
mass is strictly positive infinitely often.
-/
def GoldbachGapOneActivationPressure : Prop :=
  ∀ N₀, ∃ N, N ≥ N₀ ∧ 0 < goldbachGapOneActivationMass N

theorem goldbach_dyadic_gap_one_sweep_pressure_forces_activation_pressure
    (h : GoldbachDyadicGapOneSweepPressure) :
    GoldbachGapOneActivationPressure := by
  intro N₀
  rcases h N₀ with ⟨N, hNle, htwin⟩
  exact ⟨N, hNle, goldbach_gap_one_activation_mass_pos_of_twin_support htwin⟩

theorem goldbach_parity_and_infinitely_many_twins_forces_activation_pressure
    (_hG : GoldbachParity)
    (hTwins : ∀ p, ∃ q > p, TwinPrimePair q) :
    GoldbachGapOneActivationPressure :=
  goldbach_dyadic_gap_one_sweep_pressure_forces_activation_pressure
    (goldbach_dyadic_gap_one_sweep_pressure_of_infinitely_many_twins hTwins)

/--
Each positive twin activation spike is a **controlled sub-budget** of the per-midpoint
associator cap — the global convergent series bounds the ladder contribution.
-/
theorem gap_one_activation_positive_bounded_by_cap {N : ℕ}
    (h : goldbachMidpointSupportsTwinPrime N) :
    0 < goldbachGapOneActivationMass N ∧
      goldbachGapOneActivationMass N ≤ goldbachAnnulusAssociatorCapTerm N := by
  refine ⟨goldbach_gap_one_activation_mass_pos_of_twin_support h, ?_⟩
  have hN : 2 ≤ N := h.1
  exact goldbach_gap_one_activation_mass_le_cap_term hN

theorem goldbach_gap_one_activation_pressure_with_cap_bound
    (hPress : GoldbachGapOneActivationPressure) (N₀ : ℕ) :
    ∃ N, N ≥ N₀ ∧
      0 < goldbachGapOneActivationMass N ∧
        goldbachGapOneActivationMass N ≤ goldbachAnnulusAssociatorCapTerm N := by
  rcases hPress N₀ with ⟨N, hNle, hpos⟩
  have hsup : goldbachMidpointSupportsTwinPrime N := by
    dsimp [goldbachGapOneActivationMass] at hpos
    split_ifs at hpos with htwin
    · exact htwin
    · simp at hpos
  rcases gap_one_activation_positive_bounded_by_cap hsup with ⟨_, hle⟩
  exact ⟨N, hNle, hpos, hle⟩

/-! ## Square-ladder gap-one symmetric pressure (honest split) -/

/--
**Square-ladder gap-one symmetric pressure:** infinitely often some `m²` hosts a
symmetric Ng-square pair at **gap `g = 1`** (twin channel on the square ladder).
-/
def SquareLadderGapOneSymmetricPressure : Prop :=
  ∀ M₀, ∃ m, m ≥ M₀ ∧
    symmetricPrimeReflectionAtGap (m * m) 1 ∧ MidpointGapNgSquare (m * m) 1

theorem square_ladder_gap_one_symmetric_occurs :
    ∃ m, 0 < m ∧
      symmetricPrimeReflectionAtGap (m * m) 1 ∧ MidpointGapNgSquare (m * m) 1 :=
  ⟨2, by decide, square_midpoint_twin_at_four.1, square_midpoint_twin_at_four.2.1⟩

/--
**Open (documented).**  `GoldbachParity` alone does not locate infinitely many
square midpoints with `g = 1` — twin primes at `N = p + 1` rarely land on `m²`.
-/
def GoldbachParityForcesSquareLadderGapOneSymmetricPressure : Prop :=
  GoldbachParity → SquareLadderGapOneSymmetricPressure

theorem not_square_ladder_gap_one_symmetric_pressure :
    ¬ SquareLadderGapOneSymmetricPressure := by
  intro h
  rcases h 3 with ⟨m, hm, hsym, _⟩
  have hm2 : m = 2 := square_ladder_gap_one_symmetric_unique_at_m_two m (by omega) hsym
  omega

theorem goldbach_parity_forces_square_ladder_gap_one_symmetric_pressure_false
    (_hG : GoldbachParity) :
    ¬ SquareLadderGapOneSymmetricPressure :=
  not_square_ladder_gap_one_symmetric_pressure

theorem dyadic_gap_one_activation_pressure_not_square_ladder_gap_one
    (h : GoldbachDyadicGapOneSweepPressure) :
    GoldbachGapOneActivationPressure ∧
      ¬ SquareLadderGapOneSymmetricPressure :=
  ⟨goldbach_dyadic_gap_one_sweep_pressure_forces_activation_pressure h,
    not_square_ladder_gap_one_symmetric_pressure⟩

/-! ## Square vs non-square midpoint split (negative identity exploitation) -/

/-- Midpoint index `N` is a perfect square `m²`. -/
def GoldbachMidpointIsPerfectSquare (N : ℕ) : Prop :=
  ∃ m, N = m * m

/-- Midpoint index is not a perfect square (on the certified ladder `N ≥ 2`). -/
def GoldbachMidpointIsNonSquare (N : ℕ) : Prop :=
  2 ≤ N ∧ ¬ GoldbachMidpointIsPerfectSquare N

instance decidableGoldbachMidpointIsPerfectSquare (N : ℕ) :
    Decidable (GoldbachMidpointIsPerfectSquare N) :=
  Classical.propDecidable _

theorem goldbach_midpoint_perfect_square_iff {N : ℕ} :
    GoldbachMidpointIsPerfectSquare N ↔ ∃ m, N = m * m :=
  Iff.rfl

theorem goldbach_midpoint_twin_on_square_only_at_four {N : ℕ}
    (htwin : goldbachMidpointSupportsTwinPrime N) :
    GoldbachMidpointIsPerfectSquare N → N = 4 := by
  intro hSq
  exact goldbach_midpoint_is_square_twin_index_eq_four hSq htwin

theorem goldbach_midpoint_twin_implies_non_square {N : ℕ} (hN : 5 ≤ N)
    (htwin : goldbachMidpointSupportsTwinPrime N) :
    GoldbachMidpointIsNonSquare N := by
  refine ⟨by omega, ?_⟩
  intro hSq
  have := goldbach_midpoint_twin_on_square_only_at_four htwin hSq
  omega

/--
Dyadic twin pressure at `N₀ ≥ 5` is witnessed on a **non-square** midpoint — the
square subladder cannot carry twins beyond the anchor `N = 4`.
-/
theorem goldbach_dyadic_pressure_from_non_square_midpoint
    (h : GoldbachDyadicGapOneSweepPressure) (N₀ : ℕ) (hN₀ : 5 ≤ N₀) :
    ∃ N, N ≥ N₀ ∧ goldbachMidpointSupportsTwinPrime N ∧
      GoldbachMidpointIsNonSquare N := by
  rcases h N₀ with ⟨N, hNle, htwin⟩
  refine ⟨N, hNle, htwin, ?_⟩
  exact goldbach_midpoint_twin_implies_non_square (by omega) htwin

theorem goldbach_dyadic_pressure_not_carried_by_square_subladder
    (h : GoldbachDyadicGapOneSweepPressure) (N₀ : ℕ) (hN₀ : 5 ≤ N₀) :
    ∃ N, N ≥ N₀ ∧ goldbachMidpointSupportsTwinPrime N ∧
      ∀ m, N ≠ m * m := by
  rcases goldbach_dyadic_pressure_from_non_square_midpoint h N₀ hN₀ with
    ⟨N, hNle, htwin, hNonSq⟩
  refine ⟨N, hNle, htwin, ?_⟩
  intro m hm
  exact hNonSq.2 ⟨m, hm⟩

/--
**Non-square twin sweep pressure.**  Infinitely often a **non-square** midpoint hosts
twins — the recurring twin channel cannot rely on the square subladder beyond `N = 4`.
-/
def GoldbachNonSquareTwinSweepPressure : Prop :=
  ∀ N₀, ∃ N, N ≥ N₀ ∧ N ≥ 5 ∧
    goldbachMidpointSupportsTwinPrime N ∧
      GoldbachMidpointIsNonSquare N

/--
**Non-square gap-one activation pressure.**  Positive activation mass occurs infinitely
often on non-square midpoints (`N ≥ 5`).
-/
def GoldbachNonSquareGapOneActivationPressure : Prop :=
  ∀ N₀, ∃ N, N ≥ N₀ ∧ N ≥ 5 ∧
    GoldbachMidpointIsNonSquare N ∧
      0 < goldbachGapOneActivationMass N

theorem goldbach_dyadic_pressure_forces_non_square_twin_sweep
    (h : GoldbachDyadicGapOneSweepPressure) (N₀ : ℕ) :
    ∃ N, N ≥ N₀ ∧ N ≥ 5 ∧
      goldbachMidpointSupportsTwinPrime N ∧
        GoldbachMidpointIsNonSquare N := by
  rcases h (max N₀ 5) with ⟨N, hNle, htwin⟩
  refine ⟨N, ?_, ?_, htwin, ?_⟩
  · omega
  · omega
  · exact goldbach_midpoint_twin_implies_non_square (by omega) htwin

theorem goldbach_dyadic_pressure_forces_non_square_activation
    (h : GoldbachDyadicGapOneSweepPressure) (N₀ : ℕ) :
    ∃ N, N ≥ N₀ ∧ N ≥ 5 ∧
      GoldbachMidpointIsNonSquare N ∧
        0 < goldbachGapOneActivationMass N := by
  rcases goldbach_dyadic_pressure_forces_non_square_twin_sweep h N₀ with
    ⟨N, hNle, hN5, htwin, hNonSq⟩
  refine ⟨N, hNle, hN5, hNonSq, ?_⟩
  exact goldbach_gap_one_activation_mass_pos_of_twin_support htwin

theorem goldbach_dyadic_gap_one_sweep_forces_non_square_twin_pressure
    (h : GoldbachDyadicGapOneSweepPressure) :
    GoldbachNonSquareTwinSweepPressure := by
  intro N₀
  exact goldbach_dyadic_pressure_forces_non_square_twin_sweep h N₀

theorem goldbach_dyadic_gap_one_sweep_forces_non_square_activation_pressure
    (h : GoldbachDyadicGapOneSweepPressure) :
    GoldbachNonSquareGapOneActivationPressure := by
  intro N₀
  exact goldbach_dyadic_pressure_forces_non_square_activation h N₀

theorem dyadic_gap_one_pressure_splits_square_anchor_from_non_square_tail
    (h : GoldbachDyadicGapOneSweepPressure) (N₀ : ℕ) :
    (∃ N, N ≥ N₀ ∧ N = 4 ∧ goldbachMidpointSupportsTwinPrime N) ∨
      (∃ N, N ≥ N₀ ∧ N ≥ 5 ∧
        goldbachMidpointSupportsTwinPrime N ∧
          GoldbachMidpointIsNonSquare N) := by
  rcases h N₀ with ⟨N, hNle, htwin⟩
  by_cases h4 : N = 4
  · left
    exact ⟨N, hNle, h4, htwin⟩
  · right
    have h5 : 5 ≤ N := by
      rcases Nat.lt_or_ge N 5 with hlt5 | hge5
      · exfalso
        have hNle4 : N ≤ 4 := (Nat.lt_succ_iff).mp hlt5
        interval_cases N
        · rcases htwin with ⟨hN2, _⟩; omega
        · rcases htwin with ⟨hN2, _⟩; omega
        · rcases htwin with ⟨_, hp⟩
          dsimp [TwinPrimePair] at hp
          norm_num at hp
        · rcases htwin with ⟨_, hp⟩
          dsimp [TwinPrimePair] at hp
          norm_num at hp
        · exact h4 rfl
      · exact hge5
    exact ⟨N, hNle, h5, htwin, goldbach_midpoint_twin_implies_non_square h5 htwin⟩

/-! ## Finite square subladder contribution to gap-one mass -/

theorem goldbach_gap_one_activation_pos_on_square_midpoint {m : ℕ}
    (hpos : 0 < goldbachGapOneActivationMass (m * m)) :
    m = 2 := by
  dsimp [goldbachGapOneActivationMass] at hpos
  split_ifs at hpos with htwin
  · exact goldbach_midpoint_twin_on_square_forces_m_two htwin
  · simp at hpos

theorem goldbach_gap_one_activation_mass_zero_on_square_for_m_gt_two {m : ℕ}
    (hm : m > 2) :
    goldbachGapOneActivationMass (m * m) = 0 := by
  dsimp [goldbachGapOneActivationMass]
  split_ifs with htwin
  · rcases htwin with ⟨hN, htwinPair⟩
    exfalso
    have h3 : 3 ≤ m * m := by
      have hm3 : 3 ≤ m := by omega
      nlinarith
    exact no_twin_on_square_midpoint_for_m_gt_two hm
      (symmetric_gap_one_iff_twin.mpr ⟨h3, htwinPair⟩)
  · rfl

theorem goldbach_gap_one_square_anchor_is_unique :
    (∀ m, 2 < m → goldbachGapOneActivationMass (m * m) = 0) ∧
      0 < goldbachGapOneActivationMass 4 :=
  ⟨fun m hm => goldbach_gap_one_activation_mass_zero_on_square_for_m_gt_two hm,
    square_midpoint_twin_at_four.2.2.1⟩

/--
Sum of gap-one activation over square midpoints `N = (m+2)²` equals the single
anchor term at `N = 4` — the square subladder is a negligible constant in the global cap.
-/
noncomputable def goldbachGapOneSquareSubladderMass : ℝ :=
  ∑' m : ℕ, goldbachGapOneActivationMass ((m + 2) * (m + 2))

theorem goldbach_gap_one_square_subladder_mass_eq_anchor :
    goldbachGapOneSquareSubladderMass = goldbachGapOneActivationMass 4 := by
  unfold goldbachGapOneSquareSubladderMass
  have htail : ∀ n, 1 ≤ n →
      goldbachGapOneActivationMass ((n + 2) * (n + 2)) = 0 := by
    intro n hn
    exact goldbach_gap_one_activation_mass_zero_on_square_for_m_gt_two (by omega)
  have hsplit :
      (fun m : ℕ => goldbachGapOneActivationMass ((m + 2) * (m + 2))) =
        fun m : ℕ => if m = 0 then goldbachGapOneActivationMass 4 else 0 := by
    funext m
    match m with
    | 0 => simp
    | n + 1 => simp [htail (n + 1) (by omega)]
  rw [hsplit]
  simp

theorem goldbach_gap_one_square_subladder_le_gap_one_series :
    goldbachGapOneSquareSubladderMass ≤
      ∑' n : ℕ, goldbachGapOneActivationMass (n + 2) := by
  rw [goldbach_gap_one_square_subladder_mass_eq_anchor]
  have hfin :
      Finset.sum ({2} : Finset ℕ) (fun n => goldbachGapOneActivationMass (n + 2)) =
        goldbachGapOneActivationMass 4 := by simp
  calc goldbachGapOneActivationMass 4
      = Finset.sum ({2} : Finset ℕ) (fun n => goldbachGapOneActivationMass (n + 2)) := hfin.symm
    _ ≤ ∑' n, goldbachGapOneActivationMass (n + 2) :=
        Summable.sum_le_tsum ({2} : Finset ℕ)
          (fun n _ => goldbach_gap_one_activation_mass_nonneg (n + 2))
          goldbach_gap_one_activation_subseries_summable

theorem goldbach_annulus_cap_term_four_le_cap_series :
    goldbachAnnulusAssociatorCapTerm 4 ≤ goldbachAnnulusAssociatorCapSeries := by
  unfold goldbachAnnulusAssociatorCapSeries
  have hfin :
      Finset.sum ({2} : Finset ℕ) (fun n => goldbachAnnulusAssociatorCapTerm (n + 2)) =
        goldbachAnnulusAssociatorCapTerm 4 := by simp
  calc goldbachAnnulusAssociatorCapTerm 4
      = Finset.sum ({2} : Finset ℕ) (fun n => goldbachAnnulusAssociatorCapTerm (n + 2)) := hfin.symm
    _ ≤ ∑' n, goldbachAnnulusAssociatorCapTerm (n + 2) :=
        Summable.sum_le_tsum ({2} : Finset ℕ)
          (fun n _ => goldbach_annulus_cap_term_nonneg (n + 2))
          summable_goldbach_annulus_associator_cap_series

theorem goldbach_gap_one_square_subladder_mass_le_cap_anchor :
    goldbachGapOneSquareSubladderMass ≤ goldbachAnnulusAssociatorCapTerm 4 := by
  rw [goldbach_gap_one_square_subladder_mass_eq_anchor]
  exact goldbach_gap_one_activation_mass_le_cap_term (by omega)

theorem goldbach_gap_one_square_subladder_absorbed_by_global_cap :
    goldbachGapOneSquareSubladderMass ≤ goldbachAnnulusAssociatorCapSeries := by
  calc goldbachGapOneSquareSubladderMass
      ≤ goldbachAnnulusAssociatorCapTerm 4 :=
        goldbach_gap_one_square_subladder_mass_le_cap_anchor
    _ ≤ goldbachAnnulusAssociatorCapSeries :=
        goldbach_annulus_cap_term_four_le_cap_series

/-! ## Cap split: square anchor + non-square tail -/

/-- Gap-one activation on perfect-square midpoints (zero otherwise). -/
noncomputable def goldbachGapOneActivationMassSquareOnly (N : ℕ) : ℝ :=
  if GoldbachMidpointIsPerfectSquare N then goldbachGapOneActivationMass N else 0

/-- Gap-one activation attributed to non-square midpoints (zero on perfect squares). -/
noncomputable def goldbachGapOneActivationMassNonSquare (N : ℕ) : ℝ :=
  if GoldbachMidpointIsPerfectSquare N then 0 else goldbachGapOneActivationMass N

theorem goldbach_gap_one_activation_mass_split {N : ℕ} :
    goldbachGapOneActivationMass N =
      goldbachGapOneActivationMassSquareOnly N + goldbachGapOneActivationMassNonSquare N := by
  unfold goldbachGapOneActivationMassSquareOnly goldbachGapOneActivationMassNonSquare
  split_ifs <;> ring

theorem goldbach_gap_one_activation_mass_square_only_eq_zero {N : ℕ}
    (hSq : ¬ GoldbachMidpointIsPerfectSquare N) :
    goldbachGapOneActivationMassSquareOnly N = 0 := by
  unfold goldbachGapOneActivationMassSquareOnly
  simp [hSq]

theorem goldbach_gap_one_activation_mass_square_only_nonneg {N : ℕ} :
    0 ≤ goldbachGapOneActivationMassSquareOnly N := by
  unfold goldbachGapOneActivationMassSquareOnly
  split_ifs with h
  · exact goldbach_gap_one_activation_mass_nonneg N
  · simp

theorem goldbach_gap_one_activation_mass_square_only_le_mass {N : ℕ} :
    goldbachGapOneActivationMassSquareOnly N ≤ goldbachGapOneActivationMass N := by
  unfold goldbachGapOneActivationMassSquareOnly
  split_ifs with h
  · exact le_rfl
  · simpa using goldbach_gap_one_activation_mass_nonneg N

noncomputable def goldbachGapOneNonSquareSubladderMass : ℝ :=
  ∑' n : ℕ, goldbachGapOneActivationMassNonSquare (n + 2)

theorem goldbach_gap_one_non_square_subladder_mass_nonneg (n : ℕ) :
    0 ≤ goldbachGapOneActivationMassNonSquare (n + 2) := by
  dsimp [goldbachGapOneActivationMassNonSquare]
  split_ifs with h
  · exact le_rfl
  · exact goldbach_gap_one_activation_mass_nonneg (n + 2)

theorem goldbach_gap_one_non_square_subladder_summable :
    Summable (fun n : ℕ => goldbachGapOneActivationMassNonSquare (n + 2)) :=
  Summable.of_nonneg_of_le
    (fun n => goldbach_gap_one_non_square_subladder_mass_nonneg n)
    (fun n => by
      dsimp [goldbachGapOneActivationMassNonSquare]
      split_ifs with hSq
      · simpa using goldbach_gap_one_activation_mass_nonneg (n + 2)
      · rfl)
    goldbach_gap_one_activation_subseries_summable

theorem goldbach_gap_one_non_square_mass_zero_on_square {N : ℕ}
    (hSq : GoldbachMidpointIsPerfectSquare N) :
    goldbachGapOneActivationMassNonSquare N = 0 := by
  dsimp [goldbachGapOneActivationMassNonSquare]
  simp [hSq]

theorem goldbach_midpoint_not_perfect_square_two : ¬ GoldbachMidpointIsPerfectSquare 2 := by
  rintro ⟨m, hm⟩
  have hmle : m ≤ 1 := by nlinarith [sq_nonneg m, hm]
  interval_cases m <;> norm_num at hm

theorem goldbach_midpoint_not_perfect_square_three : ¬ GoldbachMidpointIsPerfectSquare 3 := by
  rintro ⟨m, hm⟩
  have hmle : m ≤ 1 := by nlinarith [sq_nonneg m, hm]
  interval_cases m <;> norm_num at hm

theorem goldbach_midpoint_perfect_square_four :
    GoldbachMidpointIsPerfectSquare 4 := ⟨2, rfl⟩

theorem goldbach_midpoint_perfect_square_implies_m_ge_three {N m : ℕ}
    (hm : N = m * m) (hN : 9 ≤ N) : 3 ≤ m := by
  nlinarith [sq_nonneg m, hm]

theorem goldbach_gap_one_square_part_mass_eq_anchor_term :
    (∑' n : ℕ, goldbachGapOneActivationMassSquareOnly (n + 2)) =
      goldbachGapOneActivationMass 4 := by
  have htail : ∀ k, 3 ≤ k → goldbachGapOneActivationMassSquareOnly (k + 2) = 0 := by
    intro k hk
    unfold goldbachGapOneActivationMassSquareOnly
    split_ifs with hSq
    · rcases hSq with ⟨m, hm⟩
      have hpos : GoldbachMidpointIsPerfectSquare (k + 2) := ⟨m, hm⟩
      have hm3 : 3 ≤ m := by nlinarith [sq_nonneg m, hm, show 5 ≤ k + 2 from by omega]
      have hmgt : m > 2 := Nat.lt_of_succ_le hm3
      have hzero := goldbach_gap_one_activation_mass_zero_on_square_for_m_gt_two hmgt
      have hmass : goldbachGapOneActivationMass (k + 2) = 0 := by
        simpa [hm] using hzero
      simp [goldbachGapOneActivationMassSquareOnly, if_pos hpos, hmass]
    · rfl
  have hfn :
      (fun n : ℕ => goldbachGapOneActivationMassSquareOnly (n + 2)) =
        fun n : ℕ => if n = 2 then goldbachGapOneActivationMass 4 else 0 := by
    funext n
    match n with
    | 0 =>
      simp [goldbachGapOneActivationMassSquareOnly, goldbach_midpoint_not_perfect_square_two]
    | 1 =>
      simp [goldbachGapOneActivationMassSquareOnly, goldbach_midpoint_not_perfect_square_three]
    | 2 =>
      simp [goldbachGapOneActivationMassSquareOnly, goldbach_midpoint_perfect_square_four]
    | n + 3 =>
      exact htail (n + 3) (by omega)
  rw [hfn]
  simp

theorem goldbach_gap_one_series_eq_anchor_plus_non_square :
    (∑' n : ℕ, goldbachGapOneActivationMass (n + 2)) =
      goldbachGapOneActivationMass 4 + goldbachGapOneNonSquareSubladderMass := by
  have hsplit' :
      (fun n : ℕ => goldbachGapOneActivationMass (n + 2)) =
        fun n : ℕ =>
          goldbachGapOneActivationMassSquareOnly (n + 2) +
            goldbachGapOneActivationMassNonSquare (n + 2) := by
    funext n
    exact goldbach_gap_one_activation_mass_split (N := n + 2)
  rw [hsplit']
  have hsumm₁ :
      Summable (fun n : ℕ => goldbachGapOneActivationMassSquareOnly (n + 2)) :=
    Summable.of_nonneg_of_le
      (fun n => goldbach_gap_one_activation_mass_square_only_nonneg (N := n + 2))
      (fun n => goldbach_gap_one_activation_mass_square_only_le_mass (N := n + 2))
      goldbach_gap_one_activation_subseries_summable
  rw [Summable.tsum_add hsumm₁ goldbach_gap_one_non_square_subladder_summable]
  rw [goldbach_gap_one_square_part_mass_eq_anchor_term]
  simp [goldbachGapOneNonSquareSubladderMass]

theorem goldbach_gap_one_series_eq_square_subladder_plus_non_square :
    (∑' n : ℕ, goldbachGapOneActivationMass (n + 2)) =
      goldbachGapOneSquareSubladderMass + goldbachGapOneNonSquareSubladderMass := by
  rw [goldbach_gap_one_series_eq_anchor_plus_non_square,
    goldbach_gap_one_square_subladder_mass_eq_anchor]

theorem goldbach_gap_one_non_square_subladder_le_gap_one_series :
    goldbachGapOneNonSquareSubladderMass ≤
      ∑' n : ℕ, goldbachGapOneActivationMass (n + 2) := by
  rw [goldbach_gap_one_series_eq_anchor_plus_non_square]
  linarith [goldbach_gap_one_activation_mass_nonneg 4]

theorem goldbach_gap_one_non_square_subladder_le_cap_series :
    goldbachGapOneNonSquareSubladderMass ≤ goldbachAnnulusAssociatorCapSeries := by
  calc goldbachGapOneNonSquareSubladderMass
      ≤ ∑' n : ℕ, goldbachGapOneActivationMass (n + 2) :=
        goldbach_gap_one_non_square_subladder_le_gap_one_series
    _ ≤ goldbachAnnulusAssociatorCapSeries :=
        tsum_goldbach_gap_one_activation_le_cap_series

/-! ## Symmetric pairs on square ladder (wider than gap-one) -/

/--
Some square midpoint admits a symmetric prime gap (not necessarily `g = 1`).
Certified at `m = 2` (`g = 1`) and `m = 3` (`g = 2` at `N = 9`).
-/
def SquareLadderSymmetricPairOccurs : Prop :=
  ∃ m, 0 < m ∧ ∃ g, symmetricPrimeReflectionAtGap (m * m) g

theorem square_ladder_symmetric_pair_at_m_two :
    ∃ g, symmetricPrimeReflectionAtGap 4 g :=
  ⟨1, symmetricPrimeReflectionAtGap_four_one⟩

theorem square_ladder_symmetric_pair_at_m_three :
    ∃ g, symmetricPrimeReflectionAtGap 9 g :=
  ⟨2, symmetricPrimeReflectionAtGap_nine_two⟩

theorem square_ladder_symmetric_pair_certified_anchors :
    (∃ g, symmetricPrimeReflectionAtGap 4 g) ∧
      (∃ g, symmetricPrimeReflectionAtGap 9 g) :=
  ⟨square_ladder_symmetric_pair_at_m_two, square_ladder_symmetric_pair_at_m_three⟩

/-! ## Cap-respecting on-line zeros ⇒ coupling + square-root (no per-`m` forcing) -/

/--
Any on-line zero carrying the **slot-phase budget** (per-midpoint cap + global
floor series bound) satisfies `SigmaTPhaseCouplingAt` and square-root spectral
weights — without assuming Δ-orbit obstruction at every square `m`.
-/
theorem on_line_zero_with_slot_budget_coupling_and_square_root
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    SigmaTPhaseCouplingAt ρ ∧ SquareRootSpectralWeightsAt ρ :=
  ⟨goldbach_slot_phase_budget_implies_sigma_t_coupling hBudget,
    goldbach_slot_budget_implies_square_root_weights hBudget⟩

theorem on_line_zero_with_slot_budget_respects_global_cap
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    ∑' n : ℕ, goldbachAnnulusAssociatorFloorMass (n + 2) ≤
      goldbachAnnulusAssociatorCapSeries :=
  hBudget.floor_mass_le_cap_series

/--
**Parity package.**  On-line nontrivial zeros inherit budget, coupling, square-root
weights, and global cap compliance from `GoldbachParity` alone.
-/
theorem goldbach_parity_on_line_zero_cap_coupling_square_root_package
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) (hσ : ρ.re = (1 / 2 : ℝ)) :
    GoldbachSlotPhasePinBudgetAt ρ ∧
      SigmaTPhaseCouplingAt ρ ∧
      SquareRootSpectralWeightsAt ρ ∧
      ∑' n : ℕ, goldbachAnnulusAssociatorFloorMass (n + 2) ≤
        goldbachAnnulusAssociatorCapSeries :=
  let hb := goldbach_slot_phase_pin_budget_at_of_parity hG h hσ
  ⟨hb, goldbach_slot_phase_budget_implies_sigma_t_coupling hb,
    goldbach_slot_budget_implies_square_root_weights hb, hb.floor_mass_le_cap_series⟩

/--
Gap-one activation spikes (when they occur) sit inside the same per-midpoint cap
that the slot-phase budget uses at every certified `N`.
-/
theorem twin_activation_mass_respects_slot_budget_cap {N : ℕ}
    (hN : 2 ≤ N) (_htwin : goldbachMidpointSupportsTwinPrime N) :
    goldbachGapOneActivationMass N ≤ goldbachAnnulusAssociatorCapTerm N ∧
      goldbachAnnulusAssociatorFloorMass N ≤ goldbachAnnulusAssociatorCapTerm N :=
  ⟨goldbach_gap_one_activation_mass_le_cap_term hN,
    goldbach_annulus_floor_mass_le_cap_term N hN⟩

end

end Hqiv.Story
