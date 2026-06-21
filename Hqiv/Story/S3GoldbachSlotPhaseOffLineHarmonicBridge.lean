import Hqiv.Story.S3GoldbachSlotPhaseCouplingBridge
import Hqiv.Story.S3GoldbachAnnulusPairCountPiBudget
import Hqiv.Story.S3OrbitVsPointwiseGap

/-!
# Off-line zeros vs slot budget; harmonic π-scale comparison

**Off-line contradiction (honest).** `GoldbachSlotPhasePinBudgetAt` *requires* `ρ.re = 1/2`
by definition, so an off-line zero cannot carry that budget — the named
`goldbach_slot_budget_off_line_contradiction` is immediate bookkeeping, not a discharge
of off-line ζ zeros from mass ceilings.

**Coupling vs on-line.** `SigmaTPhaseCouplingAt` holds at *every* nontrivial zero
unconditionally (`sigma_t_coupling_at_every_nontrivial_zero`). Forcing the critical
line from coupling is the global predicate `SigmaTPhaseCouplingForcesCriticalLine`,
which is RH-equivalent — not a per-zero implication.

**Harmonic bridge (#3).** Per-midpoint associator caps and floor masses sit below the
leading harmonic scale `π (log N)²` from `S3CumulativeHarmonicPhase`, while the
*global* cap series converges and the midpoint harmonic leading series diverges.

**Twin primes / sweep geometry.**  Twin pairs `(p,p+2)` are gap-one Goldbach annulus
sweeps on the `2N`-circle (`S3GoldbachAnnulusTwinPrimeSweep`); doubling the midpoint
ladder has a positive harmonic log increment bounded by `log 2` while halving arc
width. That is the `ln 2` frequency normalisation — not a proof that every
consecutive gap is `2`.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry
open scoped BigOperators

noncomputable section

/-! ## Off-line vs `GoldbachSlotPhasePinBudgetAt` -/

/--
An off-line point cannot satisfy the slot-phase budget: the structure field
`hσ : ρ.re = 1/2` is part of the definition.
-/
theorem not_goldbach_slot_phase_pin_budget_at_off_line
    {ρ : ℂ} (hOff : ρ.re ≠ (1 / 2 : ℝ)) :
    ¬ GoldbachSlotPhasePinBudgetAt ρ :=
  fun h => hOff h.hσ

/--
Named off-line contradiction for the slot-phase budget. Uses only that the budget
packages on-line data (`hBudget.hσ`), not coupling or global mass ceilings.
-/
theorem goldbach_slot_budget_off_line_contradiction
    {ρ : ℂ} (_hζ : IsNontrivialZetaZero ρ) (hOff : ρ.re ≠ (1 / 2 : ℝ))
    (hBudget : GoldbachSlotPhasePinBudgetAt ρ) : False :=
  not_goldbach_slot_phase_pin_budget_at_off_line hOff hBudget

theorem off_line_zero_cannot_carry_slot_phase_budget
    {ρ : ℂ} (hOff : ρ.re ≠ (1 / 2 : ℝ)) :
    ¬ GoldbachSlotPhasePinBudgetAt ρ :=
  not_goldbach_slot_phase_pin_budget_at_off_line hOff

theorem slot_phase_budget_requires_critical_line
    {ρ : ℂ} (h : GoldbachSlotPhasePinBudgetAt ρ) :
    ρ.re = (1 / 2 : ℝ) :=
  h.hσ

/--
Under `GoldbachParity`, the slot budget at a nontrivial zero is equivalent to
being on the critical line — parity supplies the budget on the line only.
-/
theorem goldbach_parity_slot_budget_iff_on_line
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) :
    GoldbachSlotPhasePinBudgetAt ρ ↔ ρ.re = (1 / 2 : ℝ) :=
  ⟨fun hb => hb.hσ, fun hσ => goldbach_slot_phase_pin_budget_at_of_parity hG h hσ⟩

/--
Hypothetical **off-line activation budget**: same global mass bookkeeping as the
on-line budget but without `ρ.re = 1/2`. No Lean discharge connects this to ζ zeros
off the line; closing that gap would require new hypotheses tying activation mass
to zero heights.
-/
structure GoldbachHypotheticalSlotActivationBudgetAt (ρ : ℂ) where
  hζ : IsNontrivialZetaZero ρ
  global_budget : GoldbachAnnulusAssociatorGlobalBudget
  floor_mass_le_cap_series :
    goldbachAnnulusAssociatorFloorMassSeries ≤ goldbachAnnulusAssociatorCapSeries
  midpoint_floor_mass_le_cap :
    ∀ N, 2 ≤ N →
      goldbachAnnulusAssociatorFloorMass N ≤ goldbachAnnulusAssociatorCapTerm N
  triplet :
    ∀ N, 2 ≤ N → Nonempty (GoldbachTripletLogAssociatorInvariant ρ N)

theorem goldbach_slot_phase_pin_budget_at_implies_hypothetical
    {ρ : ℂ} (h : GoldbachSlotPhasePinBudgetAt ρ) :
    GoldbachHypotheticalSlotActivationBudgetAt ρ :=
  { hζ := h.hζ
    global_budget := h.global_budget
    floor_mass_le_cap_series := h.floor_mass_le_cap_series
    midpoint_floor_mass_le_cap := h.midpoint_floor_mass_le_cap
    triplet := h.triplet }

theorem hypothetical_slot_activation_budget_on_line_of_parity
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) (hσ : ρ.re = (1 / 2 : ℝ)) :
    GoldbachHypotheticalSlotActivationBudgetAt ρ :=
  goldbach_slot_phase_pin_budget_at_implies_hypothetical
    (goldbach_slot_phase_pin_budget_at_of_parity hG h hσ)

/-! ## Coupling is per-zero but does not localize the line without RH -/

theorem exists_off_line_nontrivial_zero_of_not_all_on_line
    (h : ¬ AllNontrivialZerosOnLine) :
    ∃ ρ : ℂ, IsNontrivialZetaZero ρ ∧ ρ.re ≠ (1 / 2 : ℝ) := by
  unfold AllNontrivialZerosOnLine at h
  push_neg at h
  obtain ⟨ρ, hζ, hOff⟩ := h
  exact ⟨ρ, hζ, hOff⟩

/--
If some nontrivial zero is off the line, it still carries `SigmaTPhaseCouplingAt`
from the unconditional frontier lemma — coupling alone does not exclude it.
-/
theorem sigma_t_coupling_at_some_off_line_zero_of_not_all_on_line
    (h : ¬ AllNontrivialZerosOnLine) :
    ∃ ρ : ℂ, IsNontrivialZetaZero ρ ∧ ρ.re ≠ (1 / 2 : ℝ) ∧ SigmaTPhaseCouplingAt ρ := by
  rcases exists_off_line_nontrivial_zero_of_not_all_on_line h with ⟨ρ, hζ, hOff⟩
  exact ⟨ρ, hζ, hOff, sigma_t_coupling_at_every_nontrivial_zero hζ⟩

theorem sigma_t_coupling_holds_whenever_slot_budget_holds
    {ρ : ℂ} (h : GoldbachSlotPhasePinBudgetAt ρ) :
    SigmaTPhaseCouplingAt ρ :=
  goldbach_slot_phase_budget_implies_sigma_t_coupling h

theorem sigma_t_coupling_forces_line_iff_RH :
    SigmaTPhaseCouplingForcesCriticalLine ↔ RiemannHypothesis :=
  sigma_t_coupling_forces_critical_line_iff_RH

/-! ## Harmonic π-scale vs per-midpoint associator caps -/

theorem one_le_pi_asymptoticLog_sq (N : ℕ) (hN : 2 ≤ N) :
    (1 : ℝ) ≤ Real.pi * asymptoticLog N ^ 2 := by
  have h3le : (3 : ℕ) ≤ N + 1 := by omega
  have hcast : (3 : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast h3le
  have hge : Real.log 3 ≤ Real.log (N + 1) := Real.log_le_log (by norm_num) hcast
  have h13 : (1 : ℝ) < Real.log 3 := by
    have h : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) h
    simpa [Real.log_exp] using this
  have hlog : (1 : ℝ) < asymptoticLog N := by
    dsimp [asymptoticLog]
    linarith
  nlinarith [Real.pi_gt_three, sq_pos_of_pos (by linarith : (0 : ℝ) < asymptoticLog N)]

theorem goldbach_annulus_cap_term_le_one
    {N : ℕ} (hN : 2 ≤ N) :
    goldbachAnnulusAssociatorCapTerm N ≤ (1 : ℝ) := by
  have := goldbach_annulus_cap_term_le_one_div_sq N hN
  have hone : 1 / (N : ℝ) ^ 2 ≤ (1 : ℝ) := by
    have hsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith
    rw [one_div_le (by positivity) (by positivity)]
    linarith
  exact le_trans this hone

/--
Per-midpoint cap `(N−1)/N³` is dominated by the harmonic leading scale `π (log N)²`.
-/
theorem goldbach_annulus_cap_term_le_harmonic_pi_scale
    {N : ℕ} (hN : 2 ≤ N) :
    goldbachAnnulusAssociatorCapTerm N ≤ totalArcHarmonicWeightLeadingApprox N := by
  dsimp [totalArcHarmonicWeightLeadingApprox]
  exact le_trans (goldbach_annulus_cap_term_le_one hN) (one_le_pi_asymptoticLog_sq N hN)

theorem goldbach_annulus_floor_mass_le_harmonic_pi_scale
    {N : ℕ} (hN : 2 ≤ N) :
    goldbachAnnulusAssociatorFloorMass N ≤ totalArcHarmonicWeightLeadingApprox N :=
  le_trans (goldbach_annulus_floor_mass_le_cap_term N hN)
    (goldbach_annulus_cap_term_le_harmonic_pi_scale hN)

theorem goldbach_associator_cap_subsumed_by_harmonic_pi_scale
    {N : ℕ} (hN : 2 ≤ N) :
    goldbachAnnulusAssociatorCapTerm N ≤
      (goldbach_annulus_harmonic_pi_scale N (by omega)).harmonic_leading := by
  rw [(goldbach_annulus_harmonic_pi_scale N (by omega)).harmonic_leading_eq]
  exact goldbach_annulus_cap_term_le_harmonic_pi_scale hN

theorem harmonic_leading_midpoint_term_ge_one (n : ℕ) :
    (1 : ℝ) ≤ totalArcHarmonicWeightLeadingApprox (n + 2) :=
  one_le_pi_asymptoticLog_sq (n + 2) (by omega)

/--
Per-midpoint harmonic leading weights stay ≥ `1` along the midpoint ladder, so they
cannot decay to zero — contrast with the summable global associator cap series.
-/
theorem harmonic_leading_midpoint_grows_without_summable_decay :
    ∀ n₀, ∃ n ≥ n₀, (1 : ℝ) ≤ totalArcHarmonicWeightLeadingApprox (n + 2) :=
  fun n₀ => ⟨n₀, le_rfl, harmonic_leading_midpoint_term_ge_one n₀⟩

/--
**Harmonic vs cap bookkeeping.** Finite global associator cap series, while harmonic
leading weights do not tend to zero along midpoints.
-/
theorem goldbach_cap_series_summable_harmonic_leading_not_vanishing :
    Summable (fun n : ℕ => goldbachAnnulusAssociatorCapTerm (n + 2)) ∧
      ∀ᶠ n in Filter.atTop, (1 : ℝ) ≤ totalArcHarmonicWeightLeadingApprox (n + 2) :=
  ⟨summable_goldbach_annulus_associator_cap_series,
    Filter.eventually_atTop.mpr ⟨0, fun n _ => harmonic_leading_midpoint_term_ge_one n⟩⟩

/-! ## Twin primes: not a consequence of annulus geometry -/

/--
The π-annulus counts Goldbach pairs at midpoint `N` (`p + q = 2N`) in at most
`N − 1` angular slots. Consecutive-prime gaps are a different statistic; even full
`GoldbachParity` does not bound gaps between successive primes.
-/
theorem goldbach_annulus_pair_count_not_consecutive_gap_bound
    (N : ℕ) (hN : 2 ≤ N) :
    goldbachMidpointCount N ≤ N - 1 :=
  goldbachMidpointCount_le_pred N hN

end

end Hqiv.Story
