import Hqiv.Story.S3GoldbachAnnulusTwinPrimeSweep
import Hqiv.Story.S3GoldbachAnnulusAssociatorGlobalBudget
import Hqiv.Story.S3MidpointEulerSoeBridge

/-!
# Gap-one (twin) activation mass on the π-annulus ladder

Packages the audit slice: twin primes are **gap-one annulus sweeps**, their
activation mass is a **summable sub-budget** of the global associator cap series,
and each twin midpoint carries the **`ln 2` dyadic ladder step**.

This does **not** prove infinitely many twins or a density law — it isolates the
minimal sweep channel inside the existing finite global budget.
-/

namespace Hqiv.Story

open Hqiv.Geometry Real Complex
open scoped BigOperators

noncomputable section

/-! ## Gap-one count and activation mass -/

/-- Midpoint `N` hosts a twin-prime pair `(N−1, N+1)`. -/
def goldbachMidpointSupportsTwinPrime (N : ℕ) : Prop :=
  2 ≤ N ∧ TwinPrimePair (N - 1)

instance decidableGoldbachMidpointSupportsTwinPrime (N : ℕ) :
    Decidable (goldbachMidpointSupportsTwinPrime N) :=
  Classical.propDecidable _

/-- Indicator: `1` when midpoint `N` supports twins, else `0`. -/
noncomputable def goldbachGapOneMidpointCount (N : ℕ) : ℕ :=
  if goldbachMidpointSupportsTwinPrime N then 1 else 0

/-- Associator activation mass attributed to a twin / gap-one sweep at `N`. -/
noncomputable def goldbachGapOneActivationMass (N : ℕ) : ℝ :=
  if goldbachMidpointSupportsTwinPrime N then 1 / ((N ^ 3 : ℕ) : ℝ) else 0

/-- Wide-gap survivor count: total Goldbach slots minus the twin indicator. -/
noncomputable def goldbachWideGapMidpointCount (N : ℕ) : ℕ :=
  goldbachMidpointCount N - goldbachGapOneMidpointCount N

theorem goldbach_gap_one_activation_mass_nonneg (N : ℕ) :
    0 ≤ goldbachGapOneActivationMass N := by
  dsimp [goldbachGapOneActivationMass]
  split_ifs <;> positivity

/-! ## Twin ⇒ survivor ⇒ positive pair count -/

theorem twin_prime_midpoint_in_left_candidates {N : ℕ}
    (hN : 2 ≤ N) (htwin : TwinPrimePair (N - 1)) :
    N - 1 ∈ dualMidpointLeftCandidates N := by
  have hpair : GoldbachMidpointPair N (N - 1) (N + 1) := by
    have hle : 1 ≤ N := by omega
    have hpart : N - 1 + 2 = N + 1 := by omega
    simpa [Nat.sub_add_cancel hle, hpart] using goldbach_gap_one_midpoint_pair htwin
  exact (mem_dualMidpointLeftCandidates_iff N (N - 1)).mpr
    (goldbachMidpointPair_to_dual_survivor hpair)

theorem twin_prime_implies_midpoint_count_pos {N : ℕ}
    (hN : 2 ≤ N) (htwin : TwinPrimePair (N - 1)) :
    0 < goldbachMidpointCount N := by
  rw [goldbachMidpointCount_eq_leftCount]
  refine Finset.card_pos.mpr ⟨N - 1, ?_⟩
  exact twin_prime_midpoint_in_left_candidates hN htwin

theorem goldbach_gap_one_count_le_midpoint_count (N : ℕ) :
    goldbachGapOneMidpointCount N ≤ goldbachMidpointCount N := by
  dsimp [goldbachGapOneMidpointCount, goldbachWideGapMidpointCount]
  split_ifs with h
  · rcases h with ⟨hN, htwin⟩
    have hpos := twin_prime_implies_midpoint_count_pos hN htwin
    omega
  · omega

theorem goldbach_midpoint_count_eq_gap_one_plus_wide (N : ℕ) :
    goldbachMidpointCount N =
      goldbachGapOneMidpointCount N + goldbachWideGapMidpointCount N := by
  dsimp [goldbachWideGapMidpointCount]
  have := goldbach_gap_one_count_le_midpoint_count N
  omega

theorem goldbachMidpointSupportsTwinPrime_iff (N : ℕ) :
    goldbachMidpointSupportsTwinPrime N ↔ 2 ≤ N ∧ TwinPrimePair (N - 1) :=
  Iff.rfl

theorem goldbach_gap_one_count_eq_one_of_twin {N : ℕ}
    (hN : 2 ≤ N) (htwin : TwinPrimePair (N - 1)) :
    goldbachGapOneMidpointCount N = 1 := by
  dsimp [goldbachGapOneMidpointCount, goldbachMidpointSupportsTwinPrime]
  simp [hN, htwin]

theorem goldbach_gap_one_activation_mass_eq_inv_cube {N : ℕ}
    (hN : 2 ≤ N) (htwin : TwinPrimePair (N - 1)) :
    goldbachGapOneActivationMass N = 1 / ((N ^ 3 : ℕ) : ℝ) := by
  dsimp [goldbachGapOneActivationMass, goldbachMidpointSupportsTwinPrime]
  simp [hN, htwin]

/-! ## Twin sweep + `ln 2` ladder package -/

theorem twin_prime_left_slot_lt_circumference {p : ℕ} (_h : TwinPrimePair p) :
    p < goldbachAnnulusCircumference (p + 1) := by
  dsimp [goldbachAnnulusCircumference]
  omega

theorem twin_prime_partner_slot_lt_circumference {p : ℕ} (h : TwinPrimePair p) :
    p + 2 < goldbachAnnulusCircumference (p + 1) := by
  dsimp [goldbachAnnulusCircumference]
  have hp : 2 ≤ p := Nat.Prime.two_le h.1
  omega

theorem twin_prime_midpoint_pos {p : ℕ} (_h : TwinPrimePair p) : 0 < p + 1 :=
  Nat.succ_pos p

theorem twin_prime_gap_one_sweeps_full_circle {p : ℕ} (h : TwinPrimePair p) :
    shellSweepAngle (goldbach_shell_depth_pos (twin_prime_midpoint_pos h))
        ⟨p, twin_prime_left_slot_lt_circumference h⟩ +
        shellSweepAngle (goldbach_shell_depth_pos (twin_prime_midpoint_pos h))
          ⟨p + 2, twin_prime_partner_slot_lt_circumference h⟩ =
      2 * Real.pi :=
  goldbach_pair_sweeps_full_circle (twin_prime_midpoint_pos h)
    (goldbach_gap_one_midpoint_pair h)
    (twin_prime_left_slot_lt_circumference h)
    (twin_prime_partner_slot_lt_circumference h)

/--
**Twin vantage package:** gap-one midpoint pair, full `2π` sweep, and `ln 2` ladder
step at `N = p + 1`.
-/
structure GoldbachTwinGapOneSweepPackage (p : ℕ) (h : TwinPrimePair p) where
  midpoint_pair : GoldbachMidpointPair (p + 1) p (p + 2)
  ladder : GoldbachAnnulusLogTwoLadderStep (p + 1)
  sweeps_two_pi :
    shellSweepAngle (goldbach_shell_depth_pos (twin_prime_midpoint_pos h))
        ⟨p, twin_prime_left_slot_lt_circumference h⟩ +
        shellSweepAngle (goldbach_shell_depth_pos (twin_prime_midpoint_pos h))
          ⟨p + 2, twin_prime_partner_slot_lt_circumference h⟩ =
      2 * Real.pi

theorem goldbach_twin_gap_one_sweep_package (p : ℕ) (h : TwinPrimePair p) :
    GoldbachTwinGapOneSweepPackage p h :=
  { midpoint_pair := goldbach_gap_one_midpoint_pair h
    ladder := goldbach_annulus_log_two_ladder_step (p + 1) (twin_prime_midpoint_pos h)
    sweeps_two_pi := twin_prime_gap_one_sweeps_full_circle h }

theorem twin_prime_log_two_ladder_package (p : ℕ) (h : TwinPrimePair p) :
    GoldbachTwinGapOneSweepPackage p h :=
  goldbach_twin_gap_one_sweep_package p h

/-! ## Activation mass inside associator cap -/

theorem goldbach_gap_one_activation_mass_le_cap_term {N : ℕ} (hN : 2 ≤ N) :
    goldbachGapOneActivationMass N ≤ goldbachAnnulusAssociatorCapTerm N := by
  by_cases htwin : goldbachMidpointSupportsTwinPrime N
  · dsimp [goldbachGapOneActivationMass]
    rw [if_pos htwin]
    have hcast : ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; ring
    rw [hcast]
    exact goldbach_annulus_cap_term_ge_one_div_cube N hN
  · dsimp [goldbachGapOneActivationMass]
    simp [htwin]
    exact goldbach_annulus_cap_term_nonneg N

theorem goldbach_gap_one_activation_mass_le_floor_mass {N : ℕ}
    (hN : 2 ≤ N) (htwin : TwinPrimePair (N - 1)) :
    goldbachGapOneActivationMass N ≤ goldbachAnnulusAssociatorFloorMass N := by
  have hpos := twin_prime_implies_midpoint_count_pos hN htwin
  rw [goldbach_gap_one_activation_mass_eq_inv_cube hN htwin,
    goldbach_annulus_floor_mass_eq N hN]
  have hcount : (goldbachMidpointCount N : ℝ) ≥ 1 := by exact_mod_cast hpos
  have hden : 0 < ((N ^ 3 : ℕ) : ℝ) := by positivity
  field_simp
  nlinarith

theorem goldbach_gap_one_activation_subseries_summable :
    Summable (fun n : ℕ => goldbachGapOneActivationMass (n + 2)) := by
  refine Summable.of_nonneg_of_le
    (fun n => goldbach_gap_one_activation_mass_nonneg (n + 2))
    (fun n => goldbach_gap_one_activation_mass_le_cap_term (N := n + 2) (by omega))
    summable_goldbach_annulus_associator_cap_series

theorem tsum_goldbach_gap_one_activation_le_cap_series :
    ∑' n : ℕ, goldbachGapOneActivationMass (n + 2) ≤
      goldbachAnnulusAssociatorCapSeries := by
  refine Summable.tsum_mono goldbach_gap_one_activation_subseries_summable
    summable_goldbach_annulus_associator_cap_series ?_
  intro n
  exact goldbach_gap_one_activation_mass_le_cap_term (N := n + 2) (by omega)

/-! ## Twin geometric weight on the Perron aggregate -/

theorem twin_gap_one_geometric_mean_eq_sqrt_square_minus_one {N : ℕ}
    (hN : 2 ≤ N) (_htwin : TwinPrimePair (N - 1)) :
    Real.sqrt (((N - 1) * (N + 1) : ℕ) : ℝ) =
      Real.sqrt ((N : ℝ) ^ 2 - 1) := by
  congr 1
  push_cast
  have hone : (1 : ℕ) ≤ N := by omega
  rw [Nat.cast_sub hone]
  ring

/-! ## Dyadic `ln 2` normalization (proved spine) -/

/--
Every positive midpoint index carries the proved `ln 2` ladder step (arc width
halves, log increment positive and ≤ `log 2`).
-/
def GoldbachDyadicSweepLnTwoNormalization : Prop :=
  ∀ N, 0 < N → GoldbachAnnulusLogTwoLadderStep N

theorem goldbach_dyadic_sweep_ln_two_normalization :
    GoldbachDyadicSweepLnTwoNormalization :=
  fun N hN => goldbach_annulus_log_two_ladder_step N hN

/--
**Named sweep pressure (future analytic input).**  Closing twin frequency would
require showing gap-one activation cannot vanish along dyadic shells while
maintaining full `2π` sweep coverage — not proved here.
-/
def GoldbachDyadicGapOneSweepPressure : Prop :=
  ∀ N₀, ∃ N ≥ N₀, goldbachMidpointSupportsTwinPrime N

theorem goldbach_dyadic_gap_one_sweep_pressure_of_infinitely_many_twins
    (h : ∀ p, ∃ q > p, TwinPrimePair q) :
    GoldbachDyadicGapOneSweepPressure := by
  intro N₀
  rcases h N₀ with ⟨q, _, htwin⟩
  refine ⟨q + 1, ?_, ?_⟩
  · omega
  · exact ⟨by omega, htwin⟩

/-! ## Prime `2` ghost lattice anchors gap-one channel -/

theorem prime_two_line_phase_eq_iff_int {t₁ t₂ : ℝ}
    (h : linePhase 2 t₁ = linePhase 2 t₂) :
    ∃ k : ℤ, (t₂ - t₁) * Real.log 2 = 2 * Real.pi * (k : ℝ) := by
  rcases linePhase_eq_iff_int h with ⟨k, hk⟩
  exact ⟨k, by simpa using hk⟩

end

end Hqiv.Story
