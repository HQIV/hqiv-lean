import Hqiv.Story.S3GoldbachAnnulusSlotPhaseProbe
import Hqiv.Story.S3LogPhaseZetaCouplingFrontier
import Hqiv.Story.S3LogPhaseGoldbachCouplingParity
import Hqiv.Story.S3SpectralResonanceChanneling

/-!
# Slot-phase budget ⇒ σ–t coupling on the critical line

Compares the additive slot-phase budget (`GoldbachSlotPhasePinBudgetAt`) against the
named coupling predicate `SigmaTPhaseCouplingAt` from the log-edge frontier.

**What is proved.**

* Every on-line budget packages a **log–Goldbach coupling witness** at every
  midpoint `N ≥ 2` via the triplet invariant field (not only the minimal `2+2`
  shell).
* **σ–t coupling** (`SigmaTPhaseCouplingAt`) follows: witness + unconditional
  global two-prime height pinning (`two_prime_phases_pin_height`).
* Under `GoldbachParity`, constructing the budget is explicit and yields the same
  coupling route into `sigma_t_coupling_forces_critical_line_iff_RH`.
* On the line, budget + coupling align with **square-root spectral weights**
  (`SquareRootSpectralWeightsAt`) — the zeta channel of `RH_iff_zero_spectral_weights`.

**Honesty.** The global two-prime pin is not *derived* from the finite slot budget;
it is the certified probe layer already shared with `S3LogPhaseProbeCertified`.
The budget supplies **additive geometry** (per-slot πp/N data, associator mass
ceiling, parity midpoint packages).  Diagonal saturation `p = q = N` is the
machine-checked square-root joint-weight locus (`midpoint_phase_speed_saturated_iff_diagonal`).
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Coupling witness from triplet budget -/

theorem goldbach_slot_phase_budget_coupling_witness
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    LogPhaseGoldbachZetaCouplingAt ρ := by
  rcases hBudget.triplet 2 (by norm_num : 2 ≤ 2) with ⟨inv⟩
  exact ⟨inv.coupling⟩

theorem goldbach_slot_phase_budget_coupling_at_midpoint
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) {N : ℕ} (hN : 2 ≤ N) :
    Nonempty (LogPhaseGoldbachCouplingWitness ρ) := by
  rcases hBudget.triplet N hN with ⟨inv⟩
  exact ⟨inv.coupling⟩

theorem goldbach_slot_phase_budget_half_slope_package
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ p q : ℕ, GoldbachMidpointPair N p q ∧
      HalfSlopeLogPhaseSpectralPackage N p q := by
  rcases hBudget.triplet N hN with ⟨inv⟩
  exact ⟨inv.p, inv.q, inv.pair, inv.package⟩

/-! ## σ–t coupling -/

theorem goldbach_slot_phase_budget_global_two_prime_pin :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      ∀ t₁ t₂ : ℝ,
        linePhase p t₁ = linePhase p t₂ → linePhase q t₁ = linePhase q t₂ → t₁ = t₂ := by
  intro p q hp hq hne t₁ t₂ h_p h_q
  exact two_prime_phases_pin_height hp hq hne h_p h_q

/--
**Slot-phase budget ⇒ σ–t coupling.**  Triplet data supplies the log–Goldbach
witness; the certified probe layer supplies global two-prime height pinning.
-/
theorem goldbach_slot_phase_budget_implies_sigma_t_coupling
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    SigmaTPhaseCouplingAt ρ :=
  ⟨goldbach_slot_phase_budget_coupling_witness hBudget,
    goldbach_slot_phase_budget_global_two_prime_pin⟩

theorem goldbach_slot_phase_budget_implies_coupling_on_line
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    SigmaTPhaseCouplingAt ρ ∧ ρ.re = (1 / 2 : ℝ) :=
  ⟨goldbach_slot_phase_budget_implies_sigma_t_coupling hBudget, hBudget.hσ⟩

/-! ## Square-root spectral weights (per-zero predicate) -/

/--
At a zero `ρ`, every spectral line `n ≥ 2` carries square-root weight
`‖n^{−ρ}‖² = 1/n` — the per-zero form of `RH_iff_zero_spectral_weights`.
-/
def SquareRootSpectralWeightsAt (ρ : ℂ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ‖so4SpectralLine n ρ‖ ^ 2 = (n : ℝ)⁻¹

theorem square_root_spectral_weights_at_of_on_line
    {ρ : ℂ} (hσ : ρ.re = (1 / 2 : ℝ)) :
    SquareRootSpectralWeightsAt ρ := by
  intro n hn
  exact (so4SpectralLine_sq_weight hn).mpr hσ

/-! ## Parity route -/

theorem goldbach_parity_slot_budget_sigma_t_coupling
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    (hσ : ρ.re = (1 / 2 : ℝ)) :
    SigmaTPhaseCouplingAt ρ :=
  goldbach_slot_phase_budget_implies_sigma_t_coupling
    (goldbach_slot_phase_pin_budget_at_of_parity hG h hσ)

theorem goldbach_parity_slot_budget_coupling_at_every_midpoint
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    (hσ : ρ.re = (1 / 2 : ℝ)) {N : ℕ} (hN : 2 ≤ N) :
    Nonempty (LogPhaseGoldbachCouplingWitness ρ) :=
  goldbach_slot_phase_budget_coupling_at_midpoint
    (goldbach_slot_phase_pin_budget_at_of_parity hG h hσ) hN

/--
**Strengthened probe + budget + coupling.**  Per-slot pinning, global mass ceiling,
triplet invariant, and named `SigmaTPhaseCouplingAt` at the zero height.
-/
theorem goldbach_slot_pin_check_sound_with_budget_and_coupling
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) (hσ : ρ.re = (1 / 2 : ℝ))
    {N p : ℕ} (hN : 2 ≤ N) (hp_slot : p ∈ dualMidpointLeftCandidates N) (hpLt : p < N) :
    goldbachAnnulusAssociatorFloorMass N ≤ goldbachAnnulusAssociatorCapTerm N ∧
      goldbachAnnulusAssociatorFloorMassSeries ≤ goldbachAnnulusAssociatorCapSeries ∧
      (∀ {t₁ t₂ : ℝ},
        linePhase p t₁ = linePhase p t₂ ∧
          linePhase (2 * N - p) t₁ = linePhase (2 * N - p) t₂ →
          t₁ = t₂) ∧
      Nonempty (GoldbachTripletLogAssociatorInvariant ρ N) ∧
      SigmaTPhaseCouplingAt ρ ∧
      SquareRootSpectralWeightsAt ρ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact goldbach_annulus_floor_mass_le_cap_term N hN
  · exact tsum_goldbach_annulus_floor_mass_le_cap_series
  · intro t₁ t₂ hph
    exact goldbach_left_slot_two_prime_pin_height hp_slot hpLt hph.1 hph.2
  · exact goldbach_triplet_invariant_under_parity_on_line hG h hσ hN
  · exact goldbach_parity_slot_budget_sigma_t_coupling hG h hσ
  · exact square_root_spectral_weights_at_of_on_line hσ

/-! ## Link to RH-equivalent coupling discharge -/

theorem goldbach_slot_sigma_t_coupling_forces_critical_line_iff_RH :
    SigmaTPhaseCouplingForcesCriticalLine ↔ RiemannHypothesis :=
  sigma_t_coupling_forces_critical_line_iff_RH

/--
Conditional RH route: any zero carrying the slot-phase budget on the line already
satisfies `SigmaTPhaseCouplingAt`; discharge of off-line zeros is still the global
`SigmaTPhaseCouplingForcesCriticalLine` ↔ RH equivalence.
-/
theorem goldbach_slot_budget_zeros_on_line_have_sigma_t_coupling
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) (hσ : ρ.re = (1 / 2 : ℝ)) :
    GoldbachSlotPhasePinBudgetAt ρ ∧ SigmaTPhaseCouplingAt ρ :=
  ⟨goldbach_slot_phase_pin_budget_at_of_parity hG h hσ,
    goldbach_parity_slot_budget_sigma_t_coupling hG h hσ⟩

/-! ## Square-root spectral floor from triplet (on-line additive channel) -/

theorem goldbach_slot_budget_associator_floor_at_midpoint
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ p q : ℕ,
      1 / ((N ^ 3 : ℕ) : ℝ) ≤
        octAssociatorChannel p q (2 * N) (Complex.mk (1 / 2 : ℝ) ρ.im) := by
  rcases hBudget.triplet N hN with ⟨inv⟩
  refine ⟨inv.p, inv.q, inv.associator_floor⟩

/--
Diagonal saturation (`p = q = N`) is the additive square-root joint-weight locus
on the Goldbach circle — the prime-square phase-speed match.
-/
theorem goldbach_slot_diagonal_saturation_is_square_root_locus
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q)
    (hsat : Real.log ((p * q : ℕ) : ℝ) = 2 * Real.log N) :
    p = N ∧ q = N :=
  goldbach_at_most_one_saturation_slot_per_midpoint hN h hsat

/-! ## Square-root spectral weights on the line -/

theorem square_root_spectral_weights_at_iff_on_line
    {ρ : ℂ} (h : IsNontrivialZetaZero ρ) :
    SquareRootSpectralWeightsAt ρ ↔ ρ.re = (1 / 2 : ℝ) :=
  (zero_line_characterizations ρ h).2.2.symm

/--
**Budget + coupling ⇒ square-root weights.**  On the line (`hBudget.hσ`), the
existing `so4SpectralLine_sq_weight` locator applies at every `n ≥ 2`.
Coupling is recorded for the three-way package; square-root weights follow from
`Re ρ = 1/2`, not from σ–t pin alone.
-/
theorem goldbach_slot_budget_coupling_implies_square_root_weights
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ)
    (_hCouple : SigmaTPhaseCouplingAt ρ) :
    SquareRootSpectralWeightsAt ρ :=
  square_root_spectral_weights_at_of_on_line hBudget.hσ

theorem goldbach_slot_budget_implies_square_root_weights
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    SquareRootSpectralWeightsAt ρ :=
  square_root_spectral_weights_at_of_on_line hBudget.hσ

theorem goldbach_slot_budget_on_line_sq_weight
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) {n : ℕ} (hn : 2 ≤ n) :
    ‖so4SpectralLine n ρ‖ ^ 2 = (n : ℝ)⁻¹ :=
  (so4SpectralLine_sq_weight hn).mpr hBudget.hσ

/--
**Three-way package on the line:** annulus slot-phase budget, σ–t coupling, and
square-root spectral weights all hold at `ρ`.
-/
theorem goldbach_slot_budget_coupling_square_root_on_line
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    GoldbachSlotPhasePinBudgetAt ρ ∧
      SigmaTPhaseCouplingAt ρ ∧
      SquareRootSpectralWeightsAt ρ ∧
      ρ.re = (1 / 2 : ℝ) :=
  ⟨hBudget,
    goldbach_slot_phase_budget_implies_sigma_t_coupling hBudget,
    goldbach_slot_budget_implies_square_root_weights hBudget,
    hBudget.hσ⟩

theorem goldbach_parity_slot_budget_square_root_weights
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    (hσ : ρ.re = (1 / 2 : ℝ)) :
    SquareRootSpectralWeightsAt ρ :=
  goldbach_slot_budget_implies_square_root_weights
    (goldbach_slot_phase_pin_budget_at_of_parity hG h hσ)

theorem goldbach_parity_slot_budget_coupling_square_root_package
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    (hσ : ρ.re = (1 / 2 : ℝ)) :
    GoldbachSlotPhasePinBudgetAt ρ ∧
      SigmaTPhaseCouplingAt ρ ∧
      SquareRootSpectralWeightsAt ρ :=
  let hb := goldbach_slot_phase_pin_budget_at_of_parity hG h hσ
  ⟨hb, goldbach_slot_phase_budget_implies_sigma_t_coupling hb,
    goldbach_slot_budget_implies_square_root_weights hb⟩

/--
Parity zeros on the line sit in the same square-root characterization used by
`bridge_iff_spectral_weights_and_parity` / `RH_iff_zero_spectral_weights`.
-/
theorem goldbach_parity_on_line_zero_has_square_root_weights
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    (hσ : ρ.re = (1 / 2 : ℝ)) {n : ℕ} (hn : 2 ≤ n) :
    ‖so4SpectralLine n ρ‖ ^ 2 = (n : ℝ)⁻¹ :=
  goldbach_slot_budget_on_line_sq_weight
    (goldbach_slot_phase_pin_budget_at_of_parity hG h hσ) hn

/--
**Cap-respecting on-line zeros.**  Slot-phase budget (per-midpoint cap + global floor
series) already forces σ–t coupling and square-root weights; no Δ-orbit input per `m`.
Re-exported for the density/pressure layer (`S3GoldbachGapOneDensityPressure`).
-/
theorem slot_phase_budget_on_line_implies_coupling_and_square_root
    {ρ : ℂ} (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    SigmaTPhaseCouplingAt ρ ∧ SquareRootSpectralWeightsAt ρ ∧
      ∑' n : ℕ, goldbachAnnulusAssociatorFloorMass (n + 2) ≤
        goldbachAnnulusAssociatorCapSeries :=
  ⟨goldbach_slot_phase_budget_implies_sigma_t_coupling hBudget,
    goldbach_slot_budget_implies_square_root_weights hBudget,
    hBudget.floor_mass_le_cap_series⟩

end

end Hqiv.Story
