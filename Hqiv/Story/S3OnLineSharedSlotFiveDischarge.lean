import Hqiv.Story.S3OnLineCascadeTripletHeightPhaseBridge
import Hqiv.Story.S3OnLineZeroHeightPhaseSlotBudgetAttack
import Hqiv.Story.S3HarmonicHolonomyCriticalLineFrontier

/-!
# Shared slot-5 discharge — finest on-line sub-target

The polar bridge (`S3OnLineCascadeTripletHeightPhaseBridge`) proves that at any
slot-budget zero the cascade `(6,5)` and triplet gap `(5,7)` readouts share
`linePhase 5` and factor as

* `d₆ d₅ = |30|^{-1/2} · linePhase 30`
* `gap₆,₁ = d₅ d₇ = |35|^{-1/2} · linePhase 35`

**Proved here.**

* `OnLineCascadeTripletSharedSlotFive ρ` is built unconditionally from budget.
* Cascade weight oppositeness ↔ `linePhase 30` opposition at shared-slot zeros
  (via the existing height-lock / weight iff chain).
* `OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite` is equivalent to every
  earlier on-line pin name (`TripletTailBand`, height lock, cascade weight).

**Open pin (single content).**  `OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed`:
the zero-level identification that triplet `(5,7,12)` + budget geometry forces
`star (linePhase 30 ρ.im) = -linePhase 30 ρ.im`.  Closing it immediately fires
`on_line_half_complete` and full perturbed adjoint on the line.

**Three-step decomposition** (same content, finer attack surface):

1. **Gap from triplet** — `OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet`
2. **Shared slot-5 transfer** — `OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty`
3. **Cascade weight** — equivalent to step 2 via the proved polar / height-lock chain
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Named finest on-line sub-target -/

/--
**Unit-circle form** of the shared slot-5 discharge at a zero carrying the polar
anchor bundle.
-/
def OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → OnLineCascadeTripletSharedSlotFive ρ →
    star (linePhase 30 ρ.im) = -linePhase 30 ρ.im

/--
**Weight form** — the `(0,1)` sheet content for associator defect cancellation.
This is the user's suggested primary target shape.
-/
def OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → OnLineCascadeTripletSharedSlotFive ρ →
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ

/--
Triplet-at-six packaging of the same open content (budget supplies shared slot-5).
-/
def OnLineZeroTripletAtSixIdentifiesCascadePhase : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → GoldbachSlotPhasePinBudgetAt ρ →
    star (linePhase 30 ρ.im) = -linePhase 30 ρ.im

/-! ## Three-step decomposition of the open pin -/

/--
**Step 1 — gap opposition from triplet data.**

At a slot-budget zero carrying `OnLineCascadeTripletSharedSlotFive`, the `N = 6`
triplet gap sheet `(5,7)` should force unit-circle opposition on `linePhase 35`.
The content lives in `triplet_six : Nonempty (GoldbachTripletLogAssociatorInvariant ρ 6)`.
-/
def OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → OnLineCascadeTripletSharedSlotFive ρ →
    star (linePhase 35 ρ.im) = -linePhase 35 ρ.im

/--
**Step 2 — shared slot-5 transfer.**

Given gap `(5,7)` opposition, tail-band reflection, cascade channel positivity,
and the shared `linePhase 5` factorization should force cascade `linePhase 30`
opposition.
-/
def OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → OnLineCascadeTripletSharedSlotFive ρ →
    star (linePhase 35 ρ.im) = -linePhase 35 ρ.im →
      star (linePhase 30 ρ.im) = -linePhase 30 ρ.im

/- Step 3 — cascade weight opposition is `OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite`,
  equivalent to step 2 via `shared_slot_five_cascade_weight_opposite_iff_linePhase_thirty_opposed`. -/

/-! ## Proved: algebraic setup for the transfer attack -/

theorem shared_slot_five_gap_opposed_gives_five_seven_product_opposed
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ)
    (hGap : star (linePhase 35 ρ.im) = -linePhase 35 ρ.im) :
    star (linePhase 5 ρ.im) * star (linePhase 7 ρ.im) =
      -(linePhase 5 ρ.im * linePhase 7 ρ.im) := by
  calc
    star (linePhase 5 ρ.im) * star (linePhase 7 ρ.im) =
        star (linePhase 7 ρ.im * linePhase 5 ρ.im) := (star_mul _ _).symm
    _ = star (linePhase 5 ρ.im * linePhase 7 ρ.im) := by rw [mul_comm]
    _ = star (linePhase 35 ρ.im) := by rw [hShared.shared_phase.2]
    _ = -linePhase 35 ρ.im := hGap
    _ = -(linePhase 5 ρ.im * linePhase 7 ρ.im) := by rw [hShared.shared_phase.2]

theorem shared_slot_five_linePhase_thirty_opposed_iff_six_five_product_opposed
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    star (linePhase 30 ρ.im) = -linePhase 30 ρ.im ↔
      star (linePhase 6 ρ.im) * star (linePhase 5 ρ.im) =
        -(linePhase 6 ρ.im * linePhase 5 ρ.im) := by
  have hstar :
      star (linePhase 6 ρ.im) * star (linePhase 5 ρ.im) = star (linePhase 30 ρ.im) := by
    calc
      star (linePhase 6 ρ.im) * star (linePhase 5 ρ.im) =
          star (linePhase 5 ρ.im * linePhase 6 ρ.im) := (star_mul _ _).symm
      _ = star (linePhase 6 ρ.im * linePhase 5 ρ.im) := by rw [mul_comm]
      _ = star (linePhase 30 ρ.im) := by rw [hShared.shared_phase.1]
  constructor
  · intro h
    calc
      star (linePhase 6 ρ.im) * star (linePhase 5 ρ.im) = star (linePhase 30 ρ.im) := hstar
      _ = -linePhase 30 ρ.im := h
      _ = -(linePhase 6 ρ.im * linePhase 5 ρ.im) := by rw [hShared.shared_phase.1]
  · intro h
    calc
      star (linePhase 30 ρ.im) = star (linePhase 6 ρ.im * linePhase 5 ρ.im) := by
        rw [hShared.shared_phase.1]
      _ = star (linePhase 6 ρ.im) * star (linePhase 5 ρ.im) := by
        rw [← star_mul, mul_comm (linePhase 5 ρ.im) (linePhase 6 ρ.im)]
      _ = -(linePhase 6 ρ.im * linePhase 5 ρ.im) := h
      _ = -linePhase 30 ρ.im := by rw [hShared.shared_phase.1]

/-! ## Step 1 carriers and budget packaging -/

theorem on_line_zero_gap_linePhase_thirty_five_opposed_from_triplet
    (hTriplet : OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (_hs : ρ.re = (1 / 2 : ℝ))
    (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    star (linePhase 35 ρ.im) = -linePhase 35 ρ.im :=
  hTriplet hζ hShared

theorem on_line_zero_gap_linePhase_thirty_five_opposed_from_triplet_of_budget
    (hTriplet : OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    star (linePhase 35 ρ.im) = -linePhase 35 ρ.im :=
  hTriplet hζ (on_line_cascade_triplet_shared_slot_five hζ hBudget)

theorem on_line_zero_gap_thirty_five_opposed_from_triplet_iff_slot_budget :
    OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet ↔
      OnLineZeroGapLinePhaseThirtyFiveOpposedFromSlotBudget where
  mp hTriplet := fun {ρ} hζ hBudget =>
    hTriplet hζ (on_line_cascade_triplet_shared_slot_five hζ hBudget)
  mpr hBudget := fun {ρ} hζ hShared =>
    hBudget hζ hShared.budget

theorem on_line_zero_shared_slot_five_transfers_gap_to_linePhase_thirty
    (hTransfer : OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hShared : OnLineCascadeTripletSharedSlotFive ρ)
    (hGap : star (linePhase 35 ρ.im) = -linePhase 35 ρ.im) :
    star (linePhase 30 ρ.im) = -linePhase 30 ρ.im :=
  hTransfer hζ hShared hGap

/-! ## Proved: polar bridge ⇒ weight ↔ linePhase 30 at shared-slot zeros -/

theorem shared_slot_five_cascade_weight_opposite_iff_linePhase_thirty_opposed
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ ↔
      star (linePhase 30 ρ.im) = -linePhase 30 ρ.im :=
  (on_line_zero_height_lock_iff_cascade_weight_opposite hζ hShared.budget.hσ).symm.trans
    (on_line_height_phase_lock_iff_linePhase_thirty_opposed ρ.im)

theorem shared_slot_five_linePhase_thirty_opposed_iff_spectral_product_opposed
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    star (linePhase 30 ρ.im) = -linePhase 30 ρ.im ↔
      star (so4SpectralLine 6 ρ) * star (so4SpectralLine 5 ρ) =
        -(so4SpectralLine 6 ρ * so4SpectralLine 5 ρ) := by
  have hs := hShared.budget.hσ
  constructor
  · intro hPhase
    have hLock := (on_line_height_phase_lock_iff_linePhase_thirty_opposed ρ.im).mpr hPhase
    exact on_line_zero_spectral_product_opposed_of_height_phase hs hLock
  · intro hspec
    exact (on_line_height_phase_lock_iff_linePhase_thirty_opposed ρ.im).mp
      (on_line_point_eq_critical_height hs ▸ hspec)

theorem shared_slot_five_gap_linePhase_thirty_five_opposed_iff_gap_spectral_opposed
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    star (linePhase 35 ρ.im) = -linePhase 35 ρ.im ↔
      star (gapSpectralChannel 6 (goldbachMidpointGap 6 5) ρ) =
        -gapSpectralChannel 6 (goldbachMidpointGap 6 5) ρ := by
  have hpos : 0 < criticalLineModulus 35 := critical_line_modulus_pos (n := 35) (by decide)
  have hne : ((criticalLineModulus 35 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hcast :
      star ((criticalLineModulus 35 : ℂ) * linePhase 35 ρ.im) =
        ((criticalLineModulus 35 : ℝ) : ℂ) * star (linePhase 35 ρ.im) := by
    apply Complex.ext <;> simp [star, Complex.ofReal_mul]
  constructor
  · intro h
    rw [hShared.gap_polar, hcast, h]
    simp [neg_mul]
  · intro h
    rw [hShared.gap_polar] at h
    rw [hcast] at h
    exact mul_left_cancel₀ hne (by simpa [neg_mul] using h)

theorem shared_slot_five_gap_opposed_iff_gap_spectral_at_zero
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    star (linePhase 35 ρ.im) = -linePhase 35 ρ.im ↔
      star (gapSpectralChannel 6 (goldbachMidpointGap 6 5) ρ) =
        -gapSpectralChannel 6 (goldbachMidpointGap 6 5) ρ :=
  shared_slot_five_gap_linePhase_thirty_five_opposed_iff_gap_spectral_opposed hShared

/-! ## Step 2 transfer attack ingredients + decomposition closure -/

structure SharedSlotFiveGapToCascadeTransferAttackData where
  gap_spectral :
    ∀ {ρ : ℂ}, OnLineCascadeTripletSharedSlotFive ρ →
      (star (linePhase 35 ρ.im) = -linePhase 35 ρ.im ↔
        star (gapSpectralChannel 6 (goldbachMidpointGap 6 5) ρ) =
          -gapSpectralChannel 6 (goldbachMidpointGap 6 5) ρ)
  gap_product :
    ∀ {ρ : ℂ}, (hShared : OnLineCascadeTripletSharedSlotFive ρ) →
      ∀ (hGap : star (linePhase 35 ρ.im) = -linePhase 35 ρ.im),
        star (linePhase 5 ρ.im) * star (linePhase 7 ρ.im) =
          -(linePhase 5 ρ.im * linePhase 7 ρ.im)
  cascade_product :
    ∀ {ρ : ℂ}, (hShared : OnLineCascadeTripletSharedSlotFive ρ) →
      (star (linePhase 30 ρ.im) = -linePhase 30 ρ.im ↔
        star (linePhase 6 ρ.im) * star (linePhase 5 ρ.im) =
          -(linePhase 6 ρ.im * linePhase 5 ρ.im))
  tail_reflect_at_zero :
    ∀ {ρ : ℂ}, OnLineCascadeTripletSharedSlotFive ρ →
      star (tailBandCriticalLinePhase ρ.im) = tailBandCriticalLinePhase (-ρ.im)
  cascade_channel_pos :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → 0 < octAssociatorChannel 6 5 11 ρ
  coupling :
    ∀ {ρ : ℂ}, OnLineCascadeTripletSharedSlotFive ρ → SigmaTPhaseCouplingAt ρ

def shared_slot_five_gap_to_cascade_transfer_attack_data :
    SharedSlotFiveGapToCascadeTransferAttackData where
  gap_spectral := @shared_slot_five_gap_opposed_iff_gap_spectral_at_zero
  gap_product := @shared_slot_five_gap_opposed_gives_five_seven_product_opposed
  cascade_product := @shared_slot_five_linePhase_thirty_opposed_iff_six_five_product_opposed
  tail_reflect_at_zero := fun {ρ} _hShared => tailBandCriticalLinePhase_conj ρ.im
  cascade_channel_pos := zero_cascade_associator_channel_pos
  coupling := fun hShared => goldbach_slot_phase_budget_implies_sigma_t_coupling hShared.budget

theorem on_line_zero_shared_slot_five_discharge_from_decomposition
    (hGap : OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet)
    (hTransfer : OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty) :
    OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed :=
  fun hζ hShared => hTransfer hζ hShared (hGap hζ hShared)

theorem on_line_zero_shared_slot_five_cascade_weight_from_decomposition
    (hGap : OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet)
    (hTransfer : OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty) :
    OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite :=
  fun hζ hShared =>
    (shared_slot_five_cascade_weight_opposite_iff_linePhase_thirty_opposed hζ hShared).mpr
      (on_line_zero_shared_slot_five_discharge_from_decomposition hGap hTransfer hζ hShared)

theorem on_line_zero_shared_slot_five_transfer_from_discharge
    (hDischarge : OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed) :
    OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty :=
  fun _hζ _hShared _hGap => hDischarge _hζ _hShared

/-! ## Equivalence of named targets -/

theorem on_line_zero_shared_slot_five_forces_linePhase_thirty_opposed_iff_weight
    :
    OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed ↔
      OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite where
  mp hLine := fun {ρ} hζ hShared =>
    (shared_slot_five_cascade_weight_opposite_iff_linePhase_thirty_opposed hζ hShared).mpr
      (hLine hζ hShared)
  mpr hWeight := fun {ρ} hζ hShared =>
    (shared_slot_five_cascade_weight_opposite_iff_linePhase_thirty_opposed hζ hShared).mp
      (hWeight hζ hShared)

theorem on_line_zero_shared_slot_five_forces_cascade_weight_opposite_iff_triplet_at_six
    :
    OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite ↔
      OnLineZeroTripletAtSixIdentifiesCascadePhase where
  mp hWeight := fun {ρ} hζ hBudget =>
    (shared_slot_five_cascade_weight_opposite_iff_linePhase_thirty_opposed hζ
      (on_line_cascade_triplet_shared_slot_five hζ hBudget)).mp
      (hWeight hζ (on_line_cascade_triplet_shared_slot_five hζ hBudget))
  mpr hTriplet := fun {ρ} hζ hShared =>
    (shared_slot_five_cascade_weight_opposite_iff_linePhase_thirty_opposed hζ hShared).mpr
      (hTriplet hζ hShared.budget)

theorem on_line_zero_shared_slot_five_discharge_iff_cascade_weight_from_slot_budget :
    OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite ↔
      OnLineZeroCascadeWeightOppositeFromSlotBudget where
  mp hShared := fun {ρ} hζ hBudget =>
    hShared hζ (on_line_cascade_triplet_shared_slot_five hζ hBudget)
  mpr hCascade := fun {ρ} hζ hAnchor => hCascade hζ hAnchor.budget

theorem on_line_zero_shared_slot_five_discharge_iff_triplet_tail_band :
    OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed ↔
      OnLineZeroTripletTailBandDischargesLinePhaseThirty :=
  (on_line_zero_shared_slot_five_forces_linePhase_thirty_opposed_iff_weight.trans
    on_line_zero_shared_slot_five_discharge_iff_cascade_weight_from_slot_budget).trans
    on_line_zero_cascade_weight_opposite_iff_triplet_discharge

/-! ## Carrier lemmas (apply the open pin) -/

theorem on_line_zero_shared_slot_five_forces_cascade_weight_opposite
    (hDischarge : OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (_hs : ρ.re = (1 / 2 : ℝ))
    (_hBudget : GoldbachSlotPhasePinBudgetAt ρ)
    (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ :=
  hDischarge hζ hShared

theorem on_line_zero_shared_slot_five_forces_cascade_weight_opposite_of_budget
    (hDischarge : OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ :=
  hDischarge hζ (on_line_cascade_triplet_shared_slot_five hζ hBudget)

theorem on_line_zero_shared_slot_five_forces_linePhase_thirty_opposed_of_budget
    (hDischarge : OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    star (linePhase 30 ρ.im) = -linePhase 30 ρ.im :=
  hDischarge hζ (on_line_cascade_triplet_shared_slot_five hζ hBudget)

/-! ## On-line half fires from shared slot-5 discharge -/

theorem on_line_half_complete_from_shared_slot_five_discharge
    (hG : GoldbachParity) (hDischarge : OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite) :
    OnLineZeroAssociatorDefectVanishesFromCoupling :=
  on_line_half_complete hG
    (on_line_zero_shared_slot_five_discharge_iff_triplet_tail_band.mp
      (on_line_zero_shared_slot_five_forces_linePhase_thirty_opposed_iff_weight.mpr hDischarge))

theorem on_line_zero_perturbed_adjoint_from_shared_slot_five_discharge
    (hG : GoldbachParity) (hDischarge : OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite)
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ))
    (hNon : associatorPerturbNonNormalityWitnessAt ρ) :
    perturbedHolonomyFullAdjointAt 3 (by decide) ρ :=
  on_line_half_complete_perturbed_adjoint hG
    (on_line_zero_shared_slot_five_discharge_iff_triplet_tail_band.mp
      (on_line_zero_shared_slot_five_forces_linePhase_thirty_opposed_iff_weight.mpr hDischarge))
    hζ hs hNon

/-! ## Attack bundle -/

structure SharedSlotFiveDischargeAttackData where
  shared_anchor :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → GoldbachSlotPhasePinBudgetAt ρ →
      OnLineCascadeTripletSharedSlotFive ρ
  weight_linePhase :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → OnLineCascadeTripletSharedSlotFive ρ →
      (cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ ↔
        star (linePhase 30 ρ.im) = -linePhase 30 ρ.im)
  spectral_linePhase :
    ∀ {ρ : ℂ}, OnLineCascadeTripletSharedSlotFive ρ →
      (star (linePhase 30 ρ.im) = -linePhase 30 ρ.im ↔
        star (so4SpectralLine 6 ρ) * star (so4SpectralLine 5 ρ) =
          -(so4SpectralLine 6 ρ * so4SpectralLine 5 ρ))
  tail_reflection :
    ∀ t : ℝ, star (tailBandCriticalLinePhase t) = tailBandCriticalLinePhase (-t)

def shared_slot_five_discharge_attack_data : SharedSlotFiveDischargeAttackData where
  shared_anchor := @on_line_cascade_triplet_shared_slot_five
  weight_linePhase := @shared_slot_five_cascade_weight_opposite_iff_linePhase_thirty_opposed
  spectral_linePhase := @shared_slot_five_linePhase_thirty_opposed_iff_spectral_product_opposed
  tail_reflection := tailBandCriticalLinePhase_conj

structure SharedSlotFiveDischargeAttackHalf where
  attack_data : SharedSlotFiveDischargeAttackData
  discharge : OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite
  on_line_defect : OnLineZeroAssociatorDefectVanishesFromCoupling

def shared_slot_five_discharge_attack_half
    (hG : GoldbachParity) (hDischarge : OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite) :
    SharedSlotFiveDischargeAttackHalf where
  attack_data := shared_slot_five_discharge_attack_data
  discharge := hDischarge
  on_line_defect := on_line_half_complete_from_shared_slot_five_discharge hG hDischarge

theorem on_line_half_complete_from_shared_slot_five_decomposition
    (hG : GoldbachParity)
    (hGap : OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet)
    (hTransfer : OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty) :
    OnLineZeroAssociatorDefectVanishesFromCoupling :=
  on_line_half_complete_from_shared_slot_five_discharge hG
    (on_line_zero_shared_slot_five_cascade_weight_from_decomposition hGap hTransfer)

structure SharedSlotFiveDischargeDecomposition where
  gap_from_triplet : OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet
  gap_to_cascade : OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty
  transfer_data : SharedSlotFiveGapToCascadeTransferAttackData
  discharge : OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed
  cascade_weight : OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite
  on_line_defect : OnLineZeroAssociatorDefectVanishesFromCoupling

def shared_slot_five_discharge_decomposition
    (hG : GoldbachParity)
    (hGap : OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet)
    (hTransfer : OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty) :
    SharedSlotFiveDischargeDecomposition where
  gap_from_triplet := hGap
  gap_to_cascade := hTransfer
  transfer_data := shared_slot_five_gap_to_cascade_transfer_attack_data
  discharge := on_line_zero_shared_slot_five_discharge_from_decomposition hGap hTransfer
  cascade_weight := on_line_zero_shared_slot_five_cascade_weight_from_decomposition hGap hTransfer
  on_line_defect := on_line_half_complete_from_shared_slot_five_decomposition hG hGap hTransfer

end

end Hqiv.Story
