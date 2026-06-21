import Hqiv.Story.S3OnLineZeroHeightPhaseCouplingBridge
import Hqiv.Story.S3OnLineCascadeTripletHeightPhaseBridge
import Hqiv.Story.S3GoldbachGapOneDensityPressure
import Hqiv.Story.S3ZetaGoldbachTailBandCrossChannelBridge

/-!
# On-line height-phase lock from slot budget — attack decomposition

**Last on-line pin** for `NontrivialZeroForcesPerturbedHolonomyAdjoint`.

At a nontrivial zero with `GoldbachSlotPhasePinBudgetAt ρ`, the remaining content is
the **geometric discharge**

`OnLineHeightPhaseLockAt ρ.im`

(equivalently `star (linePhase 30 ρ.im) = -linePhase 30 ρ.im` / the discrete ladder
`2 t log 30 = π + 2kπ`).

Everything else on the on-line half is already proved upstream:

* ladder equivalence (`on_line_spectral_product_opposed_iff_height_phase`);
* weight opposite / defect / perturbed adjoint from height lock;
* slot budget ⇒ σ–t coupling under parity;
* coupling route ↔ slot-budget route under parity;
* cascade `(6,5,11)` channel positivity and tail-band reflection at zero height.

This module **names the finest open target**, bundles the proved attack ingredients,
and packages **`on_line_half_complete`** — the on-line sub-target of
`NontrivialZeroForcesPerturbedHolonomyAdjoint` once the pin closes.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Equivalent formulations of the open pin -/

/--
**Unit-circle form** of the height-phase lock at a slot-budget zero — the direct
`linePhase 30` target behind the proved `(6,5)` spectral-product factorization.
-/
def OnLineZeroLinePhaseThirtyOpposedFromSlotBudget : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → GoldbachSlotPhasePinBudgetAt ρ →
    star (linePhase 30 ρ.im) = -linePhase 30 ρ.im

/--
**Finest named geometric discharge.**  Triplet data at cascade midpoint `N = 6`,
the `(6,5,11)` associator positivity, and tail-band conjugation at `ρ.im` should
force `linePhase 30` opposition — the additive/spectral bridge not yet derived from
the slot budget fields alone.
-/
def OnLineZeroTripletTailBandDischargesLinePhaseThirty : Prop :=
  OnLineZeroLinePhaseThirtyOpposedFromSlotBudget

theorem on_line_zero_line_phase_thirty_opposed_iff_height_lock :
    OnLineZeroLinePhaseThirtyOpposedFromSlotBudget ↔
      OnLineZeroHeightPhaseLockFromSlotBudget := by
  constructor
  · intro h ρ hζ hBudget
    exact (on_line_height_phase_lock_iff_linePhase_thirty_opposed ρ.im).mpr
      (h hζ hBudget)
  · intro h ρ hζ hBudget
    exact (on_line_height_phase_lock_iff_linePhase_thirty_opposed ρ.im).mp
      (h hζ hBudget)

theorem on_line_zero_triplet_tail_band_discharge_iff_height_lock :
    OnLineZeroTripletTailBandDischargesLinePhaseThirty ↔
      OnLineZeroHeightPhaseLockFromSlotBudget :=
  on_line_zero_line_phase_thirty_opposed_iff_height_lock

theorem on_line_zero_height_phase_lock_from_line_phase_thirty
    (h : OnLineZeroLinePhaseThirtyOpposedFromSlotBudget) :
    OnLineZeroHeightPhaseLockFromSlotBudget :=
  on_line_zero_line_phase_thirty_opposed_iff_height_lock.mp h

theorem on_line_zero_line_phase_thirty_from_height_lock
    (h : OnLineZeroHeightPhaseLockFromSlotBudget) :
    OnLineZeroLinePhaseThirtyOpposedFromSlotBudget :=
  on_line_zero_line_phase_thirty_opposed_iff_height_lock.mpr h

/-! ## Cascade weight + shared slot-5 bridge (proved reformulations) -/

theorem on_line_zero_cascade_weight_opposite_iff_triplet_discharge :
    OnLineZeroCascadeWeightOppositeFromSlotBudget ↔
      OnLineZeroTripletTailBandDischargesLinePhaseThirty :=
  on_line_zero_cascade_weight_opposite_iff_height_lock.trans
    on_line_zero_line_phase_thirty_opposed_iff_height_lock.symm

theorem on_line_zero_cascade_weight_opposite_iff_line_phase_thirty :
    OnLineZeroCascadeWeightOppositeFromSlotBudget ↔
      OnLineZeroLinePhaseThirtyOpposedFromSlotBudget :=
  on_line_zero_cascade_weight_opposite_iff_triplet_discharge

theorem on_line_slot_budget_zero_shared_slot_five_anchor
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    OnLineCascadeTripletSharedSlotFive ρ :=
  on_line_cascade_triplet_shared_slot_five hζ hBudget

/-! ## Proved attack ingredients at slot-budget zeros -/

structure OnLineSlotBudgetHeightPhaseAttackData where
  ladder : OnLineSpectralProductOpposedIffHeightPhase
  tail_reflection : ∀ t : ℝ,
    star (tailBandCriticalLinePhase t) = tailBandCriticalLinePhase (-t)
  cascade_channel_pos :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → 0 < octAssociatorChannel 6 5 11 ρ
  slot_budget_coupling :
    ∀ {ρ : ℂ}, GoldbachSlotPhasePinBudgetAt ρ → SigmaTPhaseCouplingAt ρ
  slot_budget_square_root :
    ∀ {ρ : ℂ}, GoldbachSlotPhasePinBudgetAt ρ → SquareRootSpectralWeightsAt ρ
  triplet_at_six :
    ∀ {ρ : ℂ}, GoldbachSlotPhasePinBudgetAt ρ →
      Nonempty (GoldbachTripletLogAssociatorInvariant ρ 6)
  global_cap_respected :
    ∀ {ρ : ℂ}, GoldbachSlotPhasePinBudgetAt ρ →
      ∑' n : ℕ, goldbachAnnulusAssociatorFloorMass (n + 2) ≤
        goldbachAnnulusAssociatorCapSeries

def on_line_slot_budget_height_phase_attack_data :
    OnLineSlotBudgetHeightPhaseAttackData where
  ladder := on_line_spectral_product_opposed_iff_height_phase
  tail_reflection := tailBandCriticalLinePhase_conj
  cascade_channel_pos := fun hζ => zero_cascade_associator_channel_pos hζ
  slot_budget_coupling := goldbach_slot_phase_budget_implies_sigma_t_coupling
  slot_budget_square_root := goldbach_slot_budget_implies_square_root_weights
  triplet_at_six := fun hBudget => hBudget.triplet 6 (by decide)
  global_cap_respected := fun hBudget => hBudget.floor_mass_le_cap_series

structure OnLineSlotBudgetZeroCascadeAnchor (ρ : ℂ) where
  budget : GoldbachSlotPhasePinBudgetAt ρ
  triplet_six : Nonempty (GoldbachTripletLogAssociatorInvariant ρ 6)
  channel_pos : 0 < octAssociatorChannel 6 5 11 ρ
  tail_reflect :
    star (tailBandCriticalLinePhase ρ.im) = tailBandCriticalLinePhase (-ρ.im)
  coupling : SigmaTPhaseCouplingAt ρ
  square_root : SquareRootSpectralWeightsAt ρ

def on_line_slot_budget_zero_cascade_anchor
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    OnLineSlotBudgetZeroCascadeAnchor ρ :=
  { budget := hBudget
    triplet_six := hBudget.triplet 6 (by decide)
    channel_pos := zero_cascade_associator_channel_pos hζ
    tail_reflect := tailBandCriticalLinePhase_conj ρ.im
    coupling := goldbach_slot_phase_budget_implies_sigma_t_coupling hBudget
    square_root := goldbach_slot_budget_implies_square_root_weights hBudget }

def on_line_slot_budget_zero_cascade_anchor_under_parity
    (hG : GoldbachParity) {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ)) :
    OnLineSlotBudgetZeroCascadeAnchor ρ :=
  on_line_slot_budget_zero_cascade_anchor hζ
    (goldbach_slot_phase_pin_budget_at_of_parity hG hζ hs)

theorem on_line_slot_budget_zero_respects_zeta_tail_band
    (hG : GoldbachParity) (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ)) :
    goldbachAnnulusAssociatorCapSeries - goldbachAnnulusInverseCubeTail ≤
      goldbachAnnulusZetaTailBandWidth :=
  (on_line_slot_budget_respects_zeta_tail_band hG hζ hs).2

/-! ## Open pin ⇒ spectral / weight / defect / adjoint (proved mod carrier) -/

theorem on_line_zero_height_phase_lock_from_slot_budget_attack
    (hDischarge : OnLineZeroTripletTailBandDischargesLinePhaseThirty) :
    OnLineZeroHeightPhaseLockFromSlotBudget :=
  on_line_zero_height_phase_lock_from_line_phase_thirty hDischarge

theorem on_line_zero_spectral_opposed_from_slot_budget_attack
    (hDischarge : OnLineZeroTripletTailBandDischargesLinePhaseThirty) :
    OnLineZeroSpectralProductOpposedFromSlotBudget :=
  on_line_zero_spectral_product_opposed_from_slot_budget_of_height_carrier
    (on_line_zero_height_phase_lock_from_slot_budget_attack hDischarge)

theorem on_line_zero_coupling_height_lock_from_slot_budget_attack
    (hG : GoldbachParity) (hDischarge : OnLineZeroTripletTailBandDischargesLinePhaseThirty) :
    OnLineZeroHeightPhaseLockFromCoupling :=
  on_line_zero_height_phase_lock_from_coupling_of_parity hG
    (on_line_zero_height_phase_lock_from_slot_budget_attack hDischarge)

/-! ## On-line half complete (fires once the pin closes) -/

/--
**On-line half complete.**  Under `GoldbachParity`, closing the slot-budget height
discharge yields the on-line sub-target
`OnLineZeroAssociatorDefectVanishesFromCoupling` for
`NontrivialZeroForcesPerturbedHolonomyAdjoint_of_subtargets`.
-/
theorem on_line_half_complete
    (hG : GoldbachParity) (hDischarge : OnLineZeroTripletTailBandDischargesLinePhaseThirty) :
    OnLineZeroAssociatorDefectVanishesFromCoupling :=
  goldbach_parity_on_line_zero_defect_from_height_carrier hG
    (on_line_zero_height_phase_lock_from_slot_budget_attack hDischarge)

theorem on_line_half_complete_from_height_lock
    (hG : GoldbachParity) (hHeight : OnLineZeroHeightPhaseLockFromSlotBudget) :
    OnLineZeroAssociatorDefectVanishesFromCoupling :=
  goldbach_parity_on_line_zero_defect_from_height_carrier hG hHeight

theorem on_line_half_complete_perturbed_adjoint
    (hG : GoldbachParity) (hDischarge : OnLineZeroTripletTailBandDischargesLinePhaseThirty)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hNon : associatorPerturbNonNormalityWitnessAt ρ) :
    perturbedHolonomyFullAdjointAt 3 (by decide) ρ :=
  goldbach_parity_on_line_zero_perturbed_adjoint_from_height_carrier hG
    (on_line_zero_height_phase_lock_from_slot_budget_attack hDischarge) hζ hs hNon

theorem on_line_half_complete_weight_opposite
    (hG : GoldbachParity) (hDischarge : OnLineZeroTripletTailBandDischargesLinePhaseThirty) :
    OnLineZeroAssociatorWeightOppositeFromCoupling :=
  on_line_zero_associator_weight_opposite_from_coupling
    (on_line_zero_coupling_height_lock_from_slot_budget_attack hG hDischarge)

/-! ## Clean attack structure -/

structure OnLineAssociatorAdjointAttackHalf where
  attack_data : OnLineSlotBudgetHeightPhaseAttackData
  discharge : OnLineZeroTripletTailBandDischargesLinePhaseThirty
  on_line_defect : OnLineZeroAssociatorDefectVanishesFromCoupling
  on_line_weight : OnLineZeroAssociatorWeightOppositeFromCoupling
  on_line_coupling_lock : OnLineZeroHeightPhaseLockFromCoupling

def on_line_associator_adjoint_attack_half
    (hG : GoldbachParity) (hDischarge : OnLineZeroTripletTailBandDischargesLinePhaseThirty) :
    OnLineAssociatorAdjointAttackHalf where
  attack_data := on_line_slot_budget_height_phase_attack_data
  discharge := hDischarge
  on_line_defect := on_line_half_complete hG hDischarge
  on_line_weight := on_line_half_complete_weight_opposite hG hDischarge
  on_line_coupling_lock :=
    on_line_zero_coupling_height_lock_from_slot_budget_attack hG hDischarge

/--
Once the on-line half is complete, the full millennium target reduces to the
off-line exclusion sub-target alone.
-/
theorem nontrivial_zero_forces_perturbed_adjoint_of_on_line_half_and_off_line
    (hOnLine : OnLineZeroAssociatorDefectVanishesFromCoupling)
    (hOffLine : OffLineZeroExcludedByCouplingAndNonNormality) :
    NontrivialZeroForcesPerturbedHolonomyAdjoint :=
  NontrivialZeroForcesPerturbedHolonomyAdjoint_of_subtargets hOnLine hOffLine

theorem nontrivial_zero_forces_perturbed_adjoint_of_slot_budget_discharge_and_off_line
    (hG : GoldbachParity) (hDischarge : OnLineZeroTripletTailBandDischargesLinePhaseThirty)
    (hOffLine : OffLineZeroExcludedByCouplingAndNonNormality) :
    NontrivialZeroForcesPerturbedHolonomyAdjoint :=
  nontrivial_zero_forces_perturbed_adjoint_of_on_line_half_and_off_line
    (on_line_half_complete hG hDischarge) hOffLine

end

end Hqiv.Story
