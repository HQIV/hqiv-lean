import Hqiv.Story.S3GoldbachAnnulusPairCountPiBudget
import Hqiv.Story.S3LogPhaseAssociatorCoupling
import Hqiv.Story.S3LogPhaseGoldbachHalfSlopeComparison

/-!
# Annulus π-budget caps associator activation per midpoint

Combines the finite slot budget (`S3GoldbachAnnulusPairCountPiBudget`) with the
on-line associator floor (`GoldbachTripletLogAssociatorInvariant`) and angular
separation of left-arm slots.

**Honesty.** This is geometric bookkeeping: a uniform bound on how much
associator floor mass one midpoint can contribute, not a discharge of off-line
zeros.  The cap is deliberately loose (`≤ (N-1)/N³`) but machine-checked and
ready for cardinality arguments against total activation mass.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Per-midpoint associator floor mass cap -/

theorem goldbach_annulus_budget_caps_associator_activation
    {N : ℕ} (hN : 2 ≤ N) :
    (goldbachMidpointCount N : ℝ) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤
      ((N - 1 : ℕ) : ℝ) / ((N ^ 3 : ℕ) : ℝ) := by
  have hle : (goldbachMidpointCount N : ℝ) ≤ ((N - 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (goldbachMidpointCount_le_pred N hN)
  have hden : 0 < (N : ℝ) ^ 3 := by positivity
  calc
    (goldbachMidpointCount N : ℝ) * (1 / ((N ^ 3 : ℕ) : ℝ))
        = (goldbachMidpointCount N : ℝ) / (N : ℝ) ^ 3 := by push_cast; field_simp
    _ ≤ ((N - 1 : ℕ) : ℝ) / (N : ℝ) ^ 3 := div_le_div_of_nonneg_right hle (le_of_lt hden)
    _ = ((N - 1 : ℕ) : ℝ) / ((N ^ 3 : ℕ) : ℝ) := by push_cast; field_simp

theorem goldbach_annulus_associator_floor_per_pair_on_line
    {N p q : ℕ} (hNpos : 0 < N) (hPair : GoldbachMidpointPair N p q)
    {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) :
    1 / ((N ^ 3 : ℕ) : ℝ) ≤
      octAssociatorChannel p q (2 * N) s :=
  midpoint_triple_channel_floor hNpos hPair hs

theorem goldbach_annulus_total_floor_mass_le_budget
    {N : ℕ} (hN : 2 ≤ N) :
    (goldbachMidpointCount N : ℝ) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤
      ((N - 1 : ℕ) : ℝ) / ((N ^ 3 : ℕ) : ℝ) :=
  goldbach_annulus_budget_caps_associator_activation hN

/-! ## Angular separation of distinct left slots -/

theorem goldbach_distinct_slots_distinct_arm_angles
    {N p₁ p₂ : ℕ} (hN : 0 < N) (hne : p₁ ≠ p₂) :
    Real.pi * (p₁ : ℝ) / (N : ℝ) ≠ Real.pi * (p₂ : ℝ) / (N : ℝ) := by
  intro h
  have hNne : (N : ℝ) ≠ 0 := by positivity
  field_simp [hNne] at h
  exact hne (Nat.cast_injective h)

theorem goldbach_distinct_survivor_slots_distinct_angles
    {N p₁ p₂ : ℕ} (hN : 0 < N) (hp1 : p₁ < goldbachAnnulusCircumference N)
    (hp2 : p₂ < goldbachAnnulusCircumference N) (hne : p₁ ≠ p₂) :
    goldbachLeftArmAngle N p₁ hN hp1 ≠ goldbachLeftArmAngle N p₂ hN hp2 := by
  intro hangle
  have hratne := goldbach_distinct_slots_distinct_arm_angles hN hne
  rw [goldbach_left_arm_angle_eq_pi_mul_slot_over_N hN hp1,
    goldbach_left_arm_angle_eq_pi_mul_slot_over_N hN hp2] at hangle
  exact hratne hangle

/-! ## Half-slope saturation: at most one diagonal slot per midpoint -/

theorem goldbach_off_diagonal_pair_strict_phase_cap
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q) (hnd : p ≠ N) :
    Real.log ((p * q : ℕ) : ℝ) < 2 * Real.log N := by
  have hle := (pair_phase_speed_max hN h).1
  have heq := (midpoint_phase_speed_saturated_iff_diagonal hN h).mp
  by_contra hge
  push_neg at hge
  have hsat : Real.log ((p * q : ℕ) : ℝ) = 2 * Real.log N := le_antisymm hle hge
  obtain ⟨hpN, _⟩ := heq hsat
  exact hnd hpN

theorem goldbach_at_most_one_saturation_slot_per_midpoint
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q)
    (hsat : Real.log ((p * q : ℕ) : ℝ) = 2 * Real.log N) :
    p = N ∧ q = N :=
  (midpoint_phase_speed_saturated_iff_diagonal hN h).mp hsat

/-! ## Packaging: activation cap at a midpoint -/

/--
**Associator activation cap** at midpoint `N`: the π-annulus budget limits how many
distinct survivor slots (hence associator floors `≥ 1/N³`) can activate at one
midpoint, and records the uniform total-floor bound.
-/
structure GoldbachAnnulusAssociatorActivationCap (N : ℕ) where
  hN : 2 ≤ N
  pi_budget : GoldbachAnnulusPiCircleBudget N
  pair_count_le_pred : goldbachMidpointCount N ≤ N - 1
  total_floor_mass_le :
    (goldbachMidpointCount N : ℝ) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤
      ((N - 1 : ℕ) : ℝ) / ((N ^ 3 : ℕ) : ℝ)

theorem goldbach_annulus_associator_activation_cap (N : ℕ) (hN : 2 ≤ N) :
    GoldbachAnnulusAssociatorActivationCap N :=
  { hN := hN
    pi_budget := goldbach_annulus_pi_circle_budget N (by omega)
    pair_count_le_pred := goldbachMidpointCount_le_pred N hN
    total_floor_mass_le := goldbach_annulus_budget_caps_associator_activation hN }

/--
At a nontrivial zero on the line, `GoldbachParity` supplies a triplet invariant at
every midpoint together with the associator activation cap — additive activation
mass per `N` is uniformly bounded.
-/
theorem goldbach_triplet_activation_cap_under_parity_on_line
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    (hσ : ρ.re = (1 / 2 : ℝ)) {N : ℕ} (hN : 2 ≤ N) :
    Nonempty (GoldbachTripletLogAssociatorInvariant ρ N) ∧
      (goldbachMidpointCount N : ℝ) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤
        ((N - 1 : ℕ) : ℝ) / ((N ^ 3 : ℕ) : ℝ) := by
  refine ⟨goldbach_triplet_invariant_under_parity_on_line hG h hσ hN, ?_⟩
  exact goldbach_annulus_budget_caps_associator_activation hN

theorem goldbach_triplet_invariant_floor_from_cap
    {ρ : ℂ} {N : ℕ} (_hN : 2 ≤ N)
    (G : GoldbachTripletLogAssociatorInvariant ρ N) :
    1 / ((N ^ 3 : ℕ) : ℝ) ≤
      octAssociatorChannel G.p G.q (2 * N) (Complex.mk (1 / 2 : ℝ) ρ.im) :=
  G.associator_floor

/-! ## Certified small-midpoint total floor mass -/

theorem goldbach_annulus_total_floor_mass_five :
    (goldbachMidpointCount 5 : ℝ) * (1 / ((5 ^ 3 : ℕ) : ℝ)) ≤
      ((4 : ℝ)) / ((5 ^ 3 : ℕ) : ℝ) := by
  simpa [goldbachMidpointCount_five, Nat.cast_sub (show 1 ≤ 5 by norm_num)] using
    goldbach_annulus_budget_caps_associator_activation (show 2 ≤ 5 by norm_num)

theorem goldbach_annulus_total_floor_mass_ten :
    (goldbachMidpointCount 10 : ℝ) * (1 / ((10 ^ 3 : ℕ) : ℝ)) ≤
      ((9 : ℝ)) / ((10 ^ 3 : ℕ) : ℝ) := by
  simpa [goldbachMidpointCount_ten, Nat.cast_sub (show 1 ≤ 10 by norm_num)] using
    goldbach_annulus_budget_caps_associator_activation (show 2 ≤ 10 by norm_num)

/--
At most `N - 1` distinct left-arm angles (hence independent angular slots) can
carry survivor pairs at midpoint `N`.
-/
theorem goldbach_annulus_at_most_pred_independent_slots
    {N : ℕ} (hN : 2 ≤ N) :
    goldbachMidpointCount N ≤ N - 1 :=
  goldbachMidpointCount_le_pred N hN

end

end Hqiv.Story
