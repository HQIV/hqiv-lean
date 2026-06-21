import Hqiv.Story.S3GoldbachAnnulusAssociatorGlobalBudget
import Hqiv.Story.S3GoldbachAnnulusPhasePinning

/-!
# Per-slot phase pinning with πp/N angular data and global budget

Each survivor left slot at midpoint `N` carries:

* left-arm angle `π · p / N` on the `2N`-slot annulus;
* a two-prime height pin via `linePhase p` and `linePhase (2N − p)`;
* a share of the per-midpoint associator cap `(N−1)/N³` inside the global series budget.

**Honesty.** Angular separation is the proved π-normalized slot data; distinct slots
use distinct left primes and distinct arm angles.  Two-prime pinning is inherited
from the certified probe layer.  Global mass is capped by
`goldbachAnnulusAssociatorCapSeries`, not a discharge of off-line zeros.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Distinct left slots -/

/--
Two distinct survivor **left slots** at the same midpoint `N`.
-/
def goldbachMidpointSlotDistinct (N p₁ p₂ : ℕ) : Prop :=
  p₁ ∈ dualMidpointLeftCandidates N ∧
    p₂ ∈ dualMidpointLeftCandidates N ∧
    p₁ ≠ p₂

theorem goldbach_midpoint_slot_distinct_left_primes_ne
    {N p₁ p₂ : ℕ} (hSlot : goldbachMidpointSlotDistinct N p₁ p₂) :
    p₁ ≠ p₂ :=
  hSlot.2.2

theorem dualMidpointLeft_lt_circumference {N p : ℕ}
    (hp : p ∈ dualMidpointLeftCandidates N) :
    p < goldbachAnnulusCircumference N := by
  have hscan := dualMidpointLeftCandidates_subset_scan_slots N hp
  have hN : 0 < N := by
    rcases (mem_dualMidpointLeftCandidates_iff N p).mp hp with ⟨hpPrime, _, _, _⟩
    have := Nat.Prime.two_le hpPrime
    omega
  exact goldbach_scan_slot_lt_circumference hN hscan

theorem goldbach_midpoint_slot_has_pair {N p : ℕ}
    (hp : p ∈ dualMidpointLeftCandidates N) :
    GoldbachMidpointPair N p (2 * N - p) :=
  dual_midpoint_survivor_gives_pair ((mem_dualMidpointLeftCandidates_iff N p).mp hp)

/-! ## Angular separation (πp/N) -/

/--
**Distinct-slot angular separation.**  Distinct survivor slots carry distinct
left-arm angles `π · p / N` — the π-normalized budget slot coordinate.
-/
theorem distinct_slot_phase_pinning
    {N p₁ p₂ : ℕ} (hN : 0 < N) (hSlot : goldbachMidpointSlotDistinct N p₁ p₂) :
    Real.pi * (p₁ : ℝ) / (N : ℝ) ≠ Real.pi * (p₂ : ℝ) / (N : ℝ) :=
  goldbach_distinct_slots_distinct_arm_angles hN hSlot.2.2

theorem distinct_slot_left_arm_angles_ne
    {N p₁ p₂ : ℕ} (hN : 0 < N) (hSlot : goldbachMidpointSlotDistinct N p₁ p₂) :
    goldbachLeftArmAngle N p₁ hN (dualMidpointLeft_lt_circumference hSlot.1) ≠
      goldbachLeftArmAngle N p₂ hN (dualMidpointLeft_lt_circumference hSlot.2.1) := by
  have hne := goldbach_midpoint_slot_distinct_left_primes_ne hSlot
  exact goldbach_distinct_survivor_slots_distinct_angles hN
    (dualMidpointLeft_lt_circumference hSlot.1)
    (dualMidpointLeft_lt_circumference hSlot.2.1) hne

theorem goldbach_slot_left_arm_angle_eq_pi_mul_slot_over_N
    {N p : ℕ} (hN : 0 < N) (hp : p ∈ dualMidpointLeftCandidates N) :
    goldbachLeftArmAngle N p hN (dualMidpointLeft_lt_circumference hp) =
      Real.pi * (p : ℝ) / (N : ℝ) :=
  goldbach_left_arm_angle_eq_pi_mul_slot_over_N hN (dualMidpointLeft_lt_circumference hp)

/-! ## Per-slot two-prime height pinning -/

theorem goldbach_left_slot_two_prime_pin_height
    {N p : ℕ} (hp_slot : p ∈ dualMidpointLeftCandidates N) (hpLt : p < N)
    {t₁ t₂ : ℝ}
    (hpin : linePhase p t₁ = linePhase p t₂)
    (hqpin : linePhase (2 * N - p) t₁ = linePhase (2 * N - p) t₂) :
    t₁ = t₂ := by
  obtain ⟨hp, hq, _, _⟩ := (mem_dualMidpointLeftCandidates_iff N p).mp hp_slot
  have hne : p ≠ 2 * N - p := by omega
  exact two_prime_phases_pin_height hp hq hne hpin hqpin

theorem goldbach_left_slot_pin_check_sound
    {N p : ℕ} (hp_slot : p ∈ dualMidpointLeftCandidates N) (hpLt : p < N)
    {t₁ t₂ : ℝ} :
    linePhase p t₁ = linePhase p t₂ ∧
      linePhase (2 * N - p) t₁ = linePhase (2 * N - p) t₂ →
      t₁ = t₂ := by
  intro hph
  exact goldbach_left_slot_two_prime_pin_height hp_slot hpLt hph.1 hph.2

theorem distinct_slot_height_not_both_prime_phases_match
    {N p : ℕ} (hp_slot : p ∈ dualMidpointLeftCandidates N) (hpLt : p < N)
    {t₁ t₂ : ℝ} (hne_t : t₁ ≠ t₂) :
    linePhase p t₁ ≠ linePhase p t₂ ∨
      linePhase (2 * N - p) t₁ ≠ linePhase (2 * N - p) t₂ := by
  by_contra hall
  push_neg at hall
  exact hne_t (goldbach_left_slot_two_prime_pin_height hp_slot hpLt hall.1 hall.2)

/-! ## Budget per midpoint and globally -/

theorem goldbach_slot_floor_mass_le_cap
    {N : ℕ} (hN : 2 ≤ N) :
    goldbachAnnulusAssociatorFloorMass N ≤ goldbachAnnulusAssociatorCapTerm N :=
  goldbach_annulus_floor_mass_le_cap_term N hN

theorem goldbach_slot_global_floor_mass_le_cap_series :
    goldbachAnnulusAssociatorFloorMassSeries ≤ goldbachAnnulusAssociatorCapSeries :=
  tsum_goldbach_annulus_floor_mass_le_cap_series

/--
Per-midpoint associator activation cap together with the slot-count budget.
-/
structure GoldbachAnnulusSlotActivationCap (N : ℕ) where
  activation_cap : GoldbachAnnulusAssociatorActivationCap N
  floor_mass_le_cap :
    goldbachAnnulusAssociatorFloorMass N ≤ goldbachAnnulusAssociatorCapTerm N

theorem goldbach_annulus_slot_activation_cap (N : ℕ) (hN : 2 ≤ N) :
    GoldbachAnnulusSlotActivationCap N :=
  { activation_cap := goldbach_annulus_associator_activation_cap N hN
    floor_mass_le_cap := goldbach_annulus_floor_mass_le_cap_term N hN }

/--
**Global slot phase-pin budget** at a zero on the line: per-midpoint caps, convergent
global series, and parity-supplied triplet data at every `N ≥ 2`.
-/
structure GoldbachSlotPhasePinBudgetAt (ρ : ℂ) where
  hσ : ρ.re = (1 / 2 : ℝ)
  hζ : IsNontrivialZetaZero ρ
  global_budget : GoldbachAnnulusAssociatorGlobalBudget
  floor_mass_le_cap_series :
    goldbachAnnulusAssociatorFloorMassSeries ≤ goldbachAnnulusAssociatorCapSeries
  midpoint_floor_mass_le_cap :
    ∀ N, 2 ≤ N →
      goldbachAnnulusAssociatorFloorMass N ≤ goldbachAnnulusAssociatorCapTerm N
  triplet :
    ∀ N, 2 ≤ N → Nonempty (GoldbachTripletLogAssociatorInvariant ρ N)

theorem goldbach_slot_phase_pin_budget_at_global :
    GoldbachAnnulusAssociatorGlobalBudget :=
  goldbach_annulus_associator_global_budget

theorem goldbach_slot_phase_pin_budget_at_of_parity
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) (hσ : ρ.re = (1 / 2 : ℝ)) :
    GoldbachSlotPhasePinBudgetAt ρ :=
  { hσ := hσ
    hζ := h
    global_budget := goldbach_annulus_associator_global_budget
    floor_mass_le_cap_series := tsum_goldbach_annulus_floor_mass_le_cap_series
    midpoint_floor_mass_le_cap := fun N hN =>
      goldbach_annulus_floor_mass_le_cap_term N hN
    triplet := fun N hN =>
      @goldbach_triplet_invariant_under_parity_on_line hG ρ h hσ N hN }

/--
**Certified probe + budget.**  Each left slot contributes an independent two-prime
pinning condition (soundness from `S3LogPhaseProbeCertified`) while total countable
floor mass across midpoints respects the global cap series.
-/
theorem goldbach_slot_pin_check_sound_with_budget
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) (hσ : ρ.re = (1 / 2 : ℝ))
    {N p : ℕ} (hN : 2 ≤ N) (hp_slot : p ∈ dualMidpointLeftCandidates N) (hpLt : p < N) :
    goldbachAnnulusAssociatorFloorMass N ≤ goldbachAnnulusAssociatorCapTerm N ∧
      goldbachAnnulusAssociatorFloorMassSeries ≤ goldbachAnnulusAssociatorCapSeries ∧
      (∀ {t₁ t₂ : ℝ},
        linePhase p t₁ = linePhase p t₂ ∧
          linePhase (2 * N - p) t₁ = linePhase (2 * N - p) t₂ →
          t₁ = t₂) ∧
      Nonempty (GoldbachTripletLogAssociatorInvariant ρ N) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact goldbach_annulus_floor_mass_le_cap_term N hN
  · exact tsum_goldbach_annulus_floor_mass_le_cap_series
  · intro t₁ t₂ hph
    exact goldbach_left_slot_two_prime_pin_height hp_slot hpLt hph.1 hph.2
  · exact goldbach_triplet_invariant_under_parity_on_line hG h hσ hN

/-! ## Certified small midpoints: distinct slots + angles -/

theorem goldbach_midpoint_slot_distinct_five_three_five :
    goldbachMidpointSlotDistinct 5 3 5 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [dualMidpointLeftCandidates_five]; simp
  · rw [dualMidpointLeftCandidates_five]; simp
  · decide

theorem distinct_slot_phase_pinning_five_three_five :
    Real.pi * (3 : ℝ) / 5 ≠ Real.pi * (5 : ℝ) / 5 :=
  distinct_slot_phase_pinning (by norm_num : 0 < 5) goldbach_midpoint_slot_distinct_five_three_five

theorem goldbach_midpoint_slot_distinct_ten_three_seven :
    goldbachMidpointSlotDistinct 10 3 7 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [dualMidpointLeftCandidates_ten]; simp
  · rw [dualMidpointLeftCandidates_ten]; simp
  · decide

theorem distinct_slot_phase_pinning_ten_three_seven :
    Real.pi * (3 : ℝ) / 10 ≠ Real.pi * (7 : ℝ) / 10 :=
  distinct_slot_phase_pinning (by norm_num : 0 < 10) goldbach_midpoint_slot_distinct_ten_three_seven

end

end Hqiv.Story
