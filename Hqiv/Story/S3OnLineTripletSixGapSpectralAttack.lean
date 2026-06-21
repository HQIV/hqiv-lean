import Hqiv.Story.S3OnLineSharedSlotFiveDischarge
import Hqiv.Story.S3LogPhaseAssociatorCoupling
import Hqiv.Story.S3OnLineZeroHeightPhaseCouplingBridge
import Hqiv.Story.S3ExplicitFormulaPrimePhaseCoincidence
import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3MidpointConstructiveSpectralSlope

/-!
# Step 1 attack — `N = 6` triplet ⇒ gap `(5,7)` spectral opposition

Decomposes `OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet` (Step 1 of the
shared slot-5 discharge) into gap-spectral sub-pins at the certified cascade
midpoint `N = 6`, pair `(5,7)`.

**Proved packaging.**

* `OnLineTripletSixGapAttackIngredients ρ` — polar bridge, tail-band reflection,
  gap nonvanishing, cascade channel positivity, and triplet existence.
* **Sub-pin 1b** is unconditional via the polar factorization
  `gap = |35|^{-1/2} · linePhase 35`.

**Open sub-pins (Step 1 content).**

* **1a** — `OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed`
* **1a-i** — `OnLineZeroTripletSixAssociatorPhaseIdentifiesGapSpectral`
* **1a-ii** — `OnLineZeroTripletSixTailBandDischargesGapSpectralOpposed`
* **Rolling route (named, open)** — `OnLineZeroTripletSixGapSpectralFromRollingIdentification`

Closing 1a + the proved 1b yields Step 1 and feeds the shared slot-5 cascade chain.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Gap `(5,7)` readout at `N = 6` -/

/-- Certified gap channel at the cascade midpoint `N = 6`, left arm `(5,7)`. -/
def gapFiveSevenSpectralChannel (ρ : ℂ) : ℂ :=
  gapSpectralChannel 6 (goldbachMidpointGap 6 5) ρ

def OnLineZeroGapFiveSevenSpectralOpposedAt (ρ : ℂ) : Prop :=
  star (gapFiveSevenSpectralChannel ρ) = -gapFiveSevenSpectralChannel ρ

theorem gap_five_seven_spectral_opposed_iff_linePhase_thirty_five
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    OnLineZeroGapFiveSevenSpectralOpposedAt ρ ↔
      star (linePhase 35 ρ.im) = -linePhase 35 ρ.im := by
  dsimp [OnLineZeroGapFiveSevenSpectralOpposedAt, gapFiveSevenSpectralChannel]
  exact (shared_slot_five_gap_opposed_iff_gap_spectral_at_zero hShared).symm

theorem gap_five_seven_channel_ne_zero {ρ : ℂ} :
    gapFiveSevenSpectralChannel ρ ≠ 0 :=
  gapSpectralChannel_ne_zero (N := 6) (g := goldbachMidpointGap 6 5) (by decide) (by decide) ρ

/-! ## Sub-pin 1a — triplet ⇒ gap spectral opposed -/

/--
**Sub-pin 1a.**  The `N = 6` triplet invariant at a shared-slot zero forces
opposition on the gap `(5,7)` spectral product.
-/
def OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → OnLineCascadeTripletSharedSlotFive ρ →
    OnLineZeroGapFiveSevenSpectralOpposedAt ρ

/--
**Sub-pin 1b (transfer inside the gap sheet).**  Gap spectral opposition implies
`linePhase 35` unit-circle opposition via the polar bridge.
-/
def OnLineZeroGapFiveSevenSpectralOpposedTransfersToLinePhaseThirtyFive : Prop :=
  ∀ {ρ : ℂ}, OnLineCascadeTripletSharedSlotFive ρ →
    OnLineZeroGapFiveSevenSpectralOpposedAt ρ →
      star (linePhase 35 ρ.im) = -linePhase 35 ρ.im

theorem on_line_zero_gap_five_seven_spectral_opposed_transfers_to_linePhase_thirty_five
    {ρ : ℂ} (hShared : OnLineCascadeTripletSharedSlotFive ρ)
    (hGap : OnLineZeroGapFiveSevenSpectralOpposedAt ρ) :
    star (linePhase 35 ρ.im) = -linePhase 35 ρ.im :=
  (gap_five_seven_spectral_opposed_iff_linePhase_thirty_five hShared).mp hGap

theorem on_line_zero_gap_five_seven_spectral_transfer_unconditional :
    OnLineZeroGapFiveSevenSpectralOpposedTransfersToLinePhaseThirtyFive :=
  fun _hShared hSpectral =>
    on_line_zero_gap_five_seven_spectral_opposed_transfers_to_linePhase_thirty_five
      _hShared hSpectral

/-! ## Finer 1a decomposition -/

/--
**1a-i (phase identification).**  At zero height, triplet `(5,7,12)` associator
data identifies the gap `(5,7)` spectral readout on the unit-circle sheet.
Expected proof route: explicit-formula prime phase / rolling identification.
-/
def OnLineZeroTripletSixAssociatorPhaseIdentifiesGapSpectral : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → OnLineCascadeTripletSharedSlotFive ρ →
    OnLineZeroGapFiveSevenSpectralOpposedAt ρ

/--
**1a-ii (tail-band discharge).**  Given phase identification, tail-band reflection
at `ρ.im` discharges gap spectral opposition.  The tail input itself is already
proved; the open content is the zero-level link from triplet data to opposition.
-/
def OnLineZeroTripletSixTailBandDischargesGapSpectralOpposed : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → OnLineCascadeTripletSharedSlotFive ρ →
    OnLineZeroTripletSixAssociatorPhaseIdentifiesGapSpectral →
      OnLineZeroGapFiveSevenSpectralOpposedAt ρ

/--
**Rolling-identification packaging** of 1a-i — closure of
`OnLineZeroTripletSixRollingAssociatorIdentifiesGapSpectralPhase` over
`RollingZetaIdentificationAtCriticalLine` (see
`S3OnLineTripletSixRollingGapSpectralBridge`).
-/
def OnLineZeroTripletSixGapSpectralFromRollingIdentification : Prop :=
  ∀ (hRoll : RollingZetaIdentificationAtCriticalLine),
    OnLineZeroTripletSixAssociatorPhaseIdentifiesGapSpectral

/--
Triplet at `N = 6` uses the certified `(5,7)` arms matching the cascade gap sheet.
-/
def OnLineTripletSixUsesFiveSevenArms : Prop :=
  ∀ {ρ : ℂ}, ∀ (G : GoldbachTripletLogAssociatorInvariant ρ 6), G.p = 5 ∧ G.q = 7

theorem goldbach_triplet_six_gap_eq_pair_at_five_seven
    {ρ : ℂ} (G : GoldbachTripletLogAssociatorInvariant ρ 6) (hp : G.p = 5) :
    gapFiveSevenSpectralChannel ρ =
      so4SpectralLine G.p ρ * so4SpectralLine G.q ρ := by
  dsimp [gapFiveSevenSpectralChannel]
  rw [← G.package.gap_eq_pair ρ]
  congr 1
  rw [hp, goldbachMidpointGap_eq]

theorem on_line_zero_triplet_six_forces_gap_spectral_of_subpins
    (hPhase : OnLineZeroTripletSixAssociatorPhaseIdentifiesGapSpectral)
    (hTail : OnLineZeroTripletSixTailBandDischargesGapSpectralOpposed) :
    OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed :=
  fun hζ hShared => hTail hζ hShared hPhase

theorem on_line_zero_triplet_six_associator_phase_implies_gap_spectral
    (hPhase : OnLineZeroTripletSixAssociatorPhaseIdentifiesGapSpectral) :
    OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed :=
  hPhase

/-! ## Step 1 closes from 1a + proved 1b -/

theorem on_line_zero_gap_linePhase_thirty_five_opposed_from_triplet_spectral
    (hTripletGap : OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed) :
    OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet :=
  fun hζ hShared =>
    on_line_zero_gap_five_seven_spectral_opposed_transfers_to_linePhase_thirty_five hShared
      (hTripletGap hζ hShared)

theorem on_line_zero_gap_linePhase_thirty_five_from_triplet_spectral_subpins
    (h1a : OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed)
    (_h1b : OnLineZeroGapFiveSevenSpectralOpposedTransfersToLinePhaseThirtyFive) :
    OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet :=
  on_line_zero_gap_linePhase_thirty_five_opposed_from_triplet_spectral h1a

theorem on_line_zero_shared_slot_five_step_one_from_triplet_spectral
    (h1a : OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed)
    (hTransfer : OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty) :
    OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed :=
  on_line_zero_shared_slot_five_discharge_from_decomposition
    (on_line_zero_gap_linePhase_thirty_five_opposed_from_triplet_spectral h1a)
    hTransfer

/-! ## Proved attack ingredients at shared-slot zeros -/

structure OnLineTripletSixGapAttackIngredients (ρ : ℂ) where
  shared : OnLineCascadeTripletSharedSlotFive ρ
  gap_polar :
    gapFiveSevenSpectralChannel ρ =
      (criticalLineModulus 35 : ℂ) * linePhase 35 ρ.im
  shared_phase :
    linePhase 30 ρ.im = linePhase 6 ρ.im * linePhase 5 ρ.im ∧
      linePhase 35 ρ.im = linePhase 5 ρ.im * linePhase 7 ρ.im
  gap_ne : gapFiveSevenSpectralChannel ρ ≠ 0
  tail_reflect :
    star (tailBandCriticalLinePhase ρ.im) = tailBandCriticalLinePhase (-ρ.im)
  cascade_channel_pos : 0 < octAssociatorChannel 6 5 11 ρ
  coupling : SigmaTPhaseCouplingAt ρ
  triplet_six : Nonempty (GoldbachTripletLogAssociatorInvariant ρ 6)

def on_line_triplet_six_gap_attack_ingredients
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hShared : OnLineCascadeTripletSharedSlotFive ρ) :
    OnLineTripletSixGapAttackIngredients ρ :=
  { shared := hShared
    gap_polar := hShared.gap_polar
    shared_phase := hShared.shared_phase
    gap_ne := gap_five_seven_channel_ne_zero
    tail_reflect := tailBandCriticalLinePhase_conj ρ.im
    cascade_channel_pos := zero_cascade_associator_channel_pos hζ
    coupling := goldbach_slot_phase_budget_implies_sigma_t_coupling hShared.budget
    triplet_six := hShared.triplet_six }

structure TripletSixGapSpectralAttackData where
  gap_spectral_transfer :
    OnLineZeroGapFiveSevenSpectralOpposedTransfersToLinePhaseThirtyFive
  gap_polar :
    ∀ {ρ : ℂ}, OnLineCascadeTripletSharedSlotFive ρ →
      gapFiveSevenSpectralChannel ρ =
        (criticalLineModulus 35 : ℂ) * linePhase 35 ρ.im
  gap_spectral_iff_linePhase :
    ∀ {ρ : ℂ}, OnLineCascadeTripletSharedSlotFive ρ →
      (OnLineZeroGapFiveSevenSpectralOpposedAt ρ ↔
        star (linePhase 35 ρ.im) = -linePhase 35 ρ.im)
  gap_pair_at_five_seven :
    ∀ {ρ : ℂ}, (G : GoldbachTripletLogAssociatorInvariant ρ 6) →
      G.p = 5 →
        gapFiveSevenSpectralChannel ρ =
          so4SpectralLine G.p ρ * so4SpectralLine G.q ρ
  gap_ne : ∀ {ρ : ℂ}, gapFiveSevenSpectralChannel ρ ≠ 0
  tail_reflect :
    ∀ t : ℝ, star (tailBandCriticalLinePhase t) = tailBandCriticalLinePhase (-t)
  cascade_channel_pos :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → 0 < octAssociatorChannel 6 5 11 ρ
  ingredients :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → OnLineCascadeTripletSharedSlotFive ρ →
      OnLineTripletSixGapAttackIngredients ρ

def triplet_six_gap_spectral_attack_data : TripletSixGapSpectralAttackData where
  gap_spectral_transfer := on_line_zero_gap_five_seven_spectral_transfer_unconditional
  gap_polar := fun hShared => hShared.gap_polar
  gap_spectral_iff_linePhase := gap_five_seven_spectral_opposed_iff_linePhase_thirty_five
  gap_pair_at_five_seven := goldbach_triplet_six_gap_eq_pair_at_five_seven
  gap_ne := fun {ρ} => gap_five_seven_channel_ne_zero (ρ := ρ)
  tail_reflect := tailBandCriticalLinePhase_conj
  cascade_channel_pos := zero_cascade_associator_channel_pos
  ingredients := on_line_triplet_six_gap_attack_ingredients

structure TripletSixGapSpectralAttackHalf where
  attack_data : TripletSixGapSpectralAttackData
  triplet_gap_spectral : OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed
  step_one : OnLineZeroGapLinePhaseThirtyFiveOpposedFromTriplet

def triplet_six_gap_spectral_attack_half
    (h1a : OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed) :
    TripletSixGapSpectralAttackHalf where
  attack_data := triplet_six_gap_spectral_attack_data
  triplet_gap_spectral := h1a
  step_one := on_line_zero_gap_linePhase_thirty_five_opposed_from_triplet_spectral h1a

structure TripletSixGapSpectralAttackFull where
  half : TripletSixGapSpectralAttackHalf
  shared_slot_transfer : OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty
  shared_slot_discharge : OnLineZeroSharedSlotFiveForcesLinePhaseThirtyOpposed
  cascade_weight : OnLineZeroSharedSlotFiveForcesCascadeWeightOpposite

def triplet_six_gap_spectral_attack_full
    (h1a : OnLineZeroTripletSixForcesGapFiveSevenSpectralOpposed)
    (hTransfer : OnLineZeroSharedSlotFiveTransfersGapToLinePhaseThirty) :
    TripletSixGapSpectralAttackFull where
  half := triplet_six_gap_spectral_attack_half h1a
  shared_slot_transfer := hTransfer
  shared_slot_discharge :=
    on_line_zero_shared_slot_five_step_one_from_triplet_spectral h1a hTransfer
  cascade_weight :=
    on_line_zero_shared_slot_five_cascade_weight_from_decomposition
      (on_line_zero_gap_linePhase_thirty_five_opposed_from_triplet_spectral h1a)
      hTransfer

end

end Hqiv.Story
