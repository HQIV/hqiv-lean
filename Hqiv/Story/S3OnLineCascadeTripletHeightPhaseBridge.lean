import Hqiv.Story.S3OnLineSpectralProductHeightPhaseLadder
import Hqiv.Story.S3LogPhaseGoldbachHalfSlopeComparison
import Hqiv.Story.S3LogPhaseAssociatorCoupling
import Hqiv.Geometry.GoldbachG2Parity

/-!
# Cascade `(6,5)` ↔ triplet `N = 6` gap channel — polar bridge

The slot-budget height discharge sits at the intersection of two on-line spectral
readouts that **share slot `5`**:

| Readout | Pair / slots | Unit phase |
|---------|----------------|------------|
| Cascade holonomy weight | `(6,5)` | `linePhase 30 = linePhase 6 · linePhase 5` |
| Goldbach triplet gap at `N = 6` | `(5,7)` | `linePhase 35 = linePhase 5 · linePhase 7` |

**Proved here:** critical-line polar factorizations for both channels and the
equivalence of the open height lock with cascade weight oppositeness at zeros.

The remaining open pin (`OnLineZeroTripletTailBandDischargesLinePhaseThirty`) is
the zero-level identification tying the triplet/gap sheet to cascade weight
oppositeness through the shared `linePhase 5` anchor.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Critical-line polar factorizations -/

private theorem criticalLineModulus_mul_cast {a b : ℕ} (_ha : 0 < a) (_hb : 0 < b) :
    ((criticalLineModulus a : ℂ) * (criticalLineModulus b : ℂ)) =
      (criticalLineModulus (a * b) : ℂ) := by
  norm_cast
  dsimp [criticalLineModulus]
  push_cast
  rw [← Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b) (z := -(1 / 2))]

theorem critical_line_gap_channel_six_five_seven (t : ℝ) :
    gapSpectralChannel 6 (goldbachMidpointGap 6 5) (criticalLinePointAtHeight t) =
      (criticalLineModulus 35 : ℂ) * linePhase 35 t := by
  set ρ := criticalLinePointAtHeight t
  have hPair := goldbach_midpoint_pair_six_five_seven
  rw [gapSpectralChannel_eq_midpoint_pair_lines hPair]
  have h5 := critical_line_prime_power_polar (n := 5) (by decide) t
  have h7 := critical_line_prime_power_polar (n := 7) (by decide) t
  have hmul := linePhase_mul (p := 5) (q := 7) (by decide) (by decide) t
  have hcm := criticalLineModulus_mul_cast (by decide : 0 < 5) (by decide : 0 < 7)
  calc
    so4SpectralLine 5 ρ * so4SpectralLine 7 ρ =
        ((criticalLineModulus 5 : ℂ) * linePhase 5 t) *
          ((criticalLineModulus 7 : ℂ) * linePhase 7 t) := by rw [h5, h7]
    _ = ((criticalLineModulus 5 : ℂ) * (criticalLineModulus 7 : ℂ)) *
          (linePhase 5 t * linePhase 7 t) := by ring
    _ = (criticalLineModulus 35 : ℂ) * linePhase 35 t := by rw [hcm, hmul]

theorem critical_line_cascade_and_gap_share_linePhase_five (t : ℝ) :
    linePhase 30 t = linePhase 6 t * linePhase 5 t ∧
      linePhase 35 t = linePhase 5 t * linePhase 7 t :=
  ⟨linePhase_mul (p := 6) (q := 5) (by decide) (by decide) t,
    linePhase_mul (p := 5) (q := 7) (by decide) (by decide) t⟩

theorem critical_line_cascade_spectral_line_five (t : ℝ) :
    so4SpectralLine 5 (criticalLinePointAtHeight t) =
      (criticalLineModulus 5 : ℂ) * linePhase 5 t :=
  critical_line_prime_power_polar (n := 5) (by decide) t

/-! ## Height lock ↔ cascade weight opposite (on-line, no slot budget) -/

theorem on_line_height_lock_iff_cascade_weight_opposite {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) (hch : 0 < octAssociatorChannel 6 5 11 ρ) :
    OnLineHeightPhaseLockAt ρ.im ↔
      cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ := by
  constructor
  · intro hLock
    exact on_line_zero_weight_opposite_of_height_phase hs hch hLock
  · intro hWeight
    have hspec := (cascade_weight_opposite_iff_star_spectral_opposed hs hch).mp hWeight
    dsimp [OnLineHeightPhaseLockAt]
    rw [show criticalLinePointAtHeight ρ.im = ρ from (on_line_point_eq_critical_height hs).symm]
    exact hspec

theorem on_line_zero_height_lock_iff_cascade_weight_opposite {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hs : ρ.re = (1 / 2 : ℝ)) :
    OnLineHeightPhaseLockAt ρ.im ↔
      cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ :=
  on_line_height_lock_iff_cascade_weight_opposite hs (zero_cascade_associator_channel_pos hζ)

/-! ## Slot-budget reformulation of the open pin -/

/--
**Weight form** of the slot-budget height discharge — the `(0,1)` sheet content
needed for associator defect cancellation.
-/
def OnLineZeroCascadeWeightOppositeFromSlotBudget : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → GoldbachSlotPhasePinBudgetAt ρ →
    cascadeAssociatorHolonomyWeight (1 - ρ) = -cascadeAssociatorHolonomyWeight ρ

/--
**Gap-channel unit-circle form** at the certified `N = 6` triplet `(5,7)`.
-/
def OnLineZeroGapLinePhaseThirtyFiveOpposedFromSlotBudget : Prop :=
  ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → GoldbachSlotPhasePinBudgetAt ρ →
    star (linePhase 35 ρ.im) = -linePhase 35 ρ.im

theorem on_line_zero_cascade_weight_opposite_iff_height_lock :
    OnLineZeroCascadeWeightOppositeFromSlotBudget ↔
      OnLineZeroHeightPhaseLockFromSlotBudget := by
  constructor
  · intro h ρ hζ hBudget
    exact (on_line_zero_height_lock_iff_cascade_weight_opposite hζ hBudget.hσ).mpr
      (h hζ hBudget)
  · intro h ρ hζ hBudget
    exact (on_line_zero_height_lock_iff_cascade_weight_opposite hζ hBudget.hσ).mp
      (h hζ hBudget)

/--
At a slot-budget zero, the `N = 6` triplet packages gap = pair lines and the
`(6,5,11)` associator floor — the shared `linePhase 5` anchor between cascade
and gap readouts.
-/
structure OnLineCascadeTripletSharedSlotFive (ρ : ℂ) where
  budget : GoldbachSlotPhasePinBudgetAt ρ
  cascade_polar :
    so4SpectralLine 6 ρ * so4SpectralLine 5 ρ =
      (criticalLineModulus 30 : ℂ) * linePhase 30 ρ.im
  gap_polar :
    gapSpectralChannel 6 (goldbachMidpointGap 6 5) ρ =
      (criticalLineModulus 35 : ℂ) * linePhase 35 ρ.im
  shared_phase :
    linePhase 30 ρ.im = linePhase 6 ρ.im * linePhase 5 ρ.im ∧
      linePhase 35 ρ.im = linePhase 5 ρ.im * linePhase 7 ρ.im
  triplet_six : Nonempty (GoldbachTripletLogAssociatorInvariant ρ 6)

def on_line_cascade_triplet_shared_slot_five
    {ρ : ℂ} (_hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    OnLineCascadeTripletSharedSlotFive ρ :=
  { budget := hBudget
    cascade_polar := by
      rw [on_line_point_eq_critical_height hBudget.hσ]
      exact critical_line_spectral_product_six_five ρ.im
    gap_polar := by
      rw [on_line_point_eq_critical_height hBudget.hσ]
      exact critical_line_gap_channel_six_five_seven ρ.im
    shared_phase := critical_line_cascade_and_gap_share_linePhase_five ρ.im
    triplet_six := hBudget.triplet 6 (by decide) }

end

end Hqiv.Story
