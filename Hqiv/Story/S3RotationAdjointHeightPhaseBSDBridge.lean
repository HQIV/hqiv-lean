import Hqiv.Story.S3HarmonicHolonomyAssociatorAdjointAttack
import Hqiv.Story.S3MulModBSDRotationDualCapstone
import Hqiv.Story.S3FortyFiveProjection
import Hqiv.Story.S3RotationRigidity

open LSeries

/-!
# Rotation ladder ↔ holonomy adjoint ↔ height-phase attack ↔ BSD convergence

Now that RH and BSD tracks share `rotFree θ` on the functional-equation pair,
this module makes the **cross-track links proved** and names the **open RH pin**
`OnLineZeroHeightPhaseLockFromSlotBudget` in rotation language.

## Proved cross-track

| Rotation | Vanishing / sign | RH anchor | BSD anchor |
|----------|------------------|-----------|------------|
| 45° | `rot45Free = 0` ⟺ `σ = 1/2` | cascade holonomy adjoint | — |
| 90° | `rot90Free > 0` ⟺ `σ > 1` | — | `mulModBSDLSeries` domain |

## Open RH focus (highest leverage)

`OnLineZeroHeightPhaseLockFromSlotBudget`: slot budget at a zero should force
`OnLineHeightPhaseLockAt ρ.im` (spectral product opposition for cascade slots
`(6,5)`).  Individual entry adjoint at `n = 6, 5` is **already free** on the
line; the open content is the **pair** height-phase lock, equivalent to the
discrete ladder `exp(2 i t log 30) = -1` (`OnLineSpectralProductOpposedIffHeightPhase`).
-/

namespace Hqiv.Story

open Hqiv.Algebra Complex Real Matrix

noncomputable section

/-! ## 45° ⟷ holonomy adjoint (proved) -/

/--
Cascade holonomy FE-adjoint is exactly the 45° equator on the real part:
same locus as `criticalLineDeviation = 0`.
-/
theorem cascade_holonomy_adjoint_iff_rot45_equator {N : ℕ} (hN : 2 ≤ N) {s : ℂ} :
    harmonicCascadeHolonomyTransformer N hN (1 - s) =
      (harmonicCascadeHolonomyTransformer N hN s)ᴴ ↔
        rot45Free (functionalPair s.re) = 0 := by
  rw [harmonic_cascade_holonomy_transformer_adjoint_iff hN,
    rot45Free_functionalPair_eq_zero_iff]

theorem cascade_holonomy_adjoint_iff_fortyfive_rotFree {N : ℕ} (hN : 2 ≤ N) {s : ℂ} :
    harmonicCascadeHolonomyTransformer N hN (1 - s) =
      (harmonicCascadeHolonomyTransformer N hN s)ᴴ ↔
        rotFree (Real.pi / 4) (functionalPair s.re) = 0 := by
  rw [cascade_holonomy_adjoint_iff_rot45_equator hN, rotFree_pi_div_four]

theorem holonomy_entry_adjoint_iff_rot45_equator {n : ℕ} (hn : 2 ≤ n) {s : ℂ} :
    so4SpectralLine n (1 - s) = starRingEnd ℂ (so4SpectralLine n s) ↔
      rot45Free (functionalPair s.re) = 0 := by
  rw [transformer_entry_adjoint_iff hn, rot45Free_functionalPair_eq_zero_iff]

/-! ## On-line: entry adjoint is free; height-phase lock is the pair target -/

theorem on_line_cascade_slots_six_five_entry_adjoint {ρ : ℂ} (hs : ρ.re = (1 / 2 : ℝ)) :
    so4SpectralLine 6 (1 - ρ) = starRingEnd ℂ (so4SpectralLine 6 ρ) ∧
      so4SpectralLine 5 (1 - ρ) = starRingEnd ℂ (so4SpectralLine 5 ρ) := by
  constructor
  · exact (transformer_entry_adjoint_iff (by decide : 2 ≤ 6)).mpr hs
  · exact (transformer_entry_adjoint_iff (by decide : 2 ≤ 5)).mpr hs

/--
On the line, cascade slots `6` and `5` already satisfy entry-level FE adjoint
(`transformer_entry_adjoint_iff`).  `OnLineHeightPhaseLockAt` is the **pair**
spectral-product opposition — the content of `OnLineZeroHeightPhaseLockFromSlotBudget`.
-/
theorem on_line_height_phase_lock_implies_entry_adjoint {ρ : ℂ}
    (hs : ρ.re = (1 / 2 : ℝ)) (_hLock : OnLineHeightPhaseLockAt ρ.im) :
    so4SpectralLine 6 (1 - ρ) = starRingEnd ℂ (so4SpectralLine 6 ρ) :=
  (transformer_entry_adjoint_iff (by decide : 2 ≤ 6)).mpr hs

/-! ## 90° ⟷ BSD L-series domain (proved) -/

/--
The mul-mod L-series half-plane `{Re s > 1}` is exactly the region where the
90° free coordinate is **positive** on `σ = Re s` — the convergence side of the
rotation wall `σ = 1`.
-/
theorem mulModBSD_lseries_half_plane_iff_rot90_positive (s : ℂ) :
    (1 : ℝ) < s.re ↔ 0 < rot90Free (functionalPair s.re) := by
  simp [rot90Free_functionalPair]

theorem mulModBSD_lseries_summable_on_rot90_positive {s : ℂ}
    (hs : 0 < rot90Free (functionalPair s.re)) :
    LSeriesSummable mulModBSDLocalCoeff s := by
  have hre : (1 : ℝ) < s.re :=
    (mulModBSD_lseries_half_plane_iff_rot90_positive s).mpr hs
  exact mulModBSDLSeries_summable hre

/-! ## Unified cross-track capstone -/

structure RotationAdjointHeightPhaseBSDBridge where
  dual_capstone : MulModBSDRotationDualCapstone
  holonomy_adjoint_rot45 :
    ∀ {N : ℕ} (hN : 2 ≤ N) {s : ℂ},
      harmonicCascadeHolonomyTransformer N hN (1 - s) =
          (harmonicCascadeHolonomyTransformer N hN s)ᴴ ↔
        rot45Free (functionalPair s.re) = 0
  lseries_rot90 :
    ∀ s : ℂ, (1 : ℝ) < s.re ↔ 0 < rot90Free (functionalPair s.re)
  height_phase_open :
    OnLineZeroHeightPhaseLockFromSlotBudget →
      OnLineZeroSpectralProductOpposedFromSlotBudget

noncomputable def rotation_adjoint_height_phase_bsd_bridge :
    RotationAdjointHeightPhaseBSDBridge where
  dual_capstone := mulMod_bsd_rotation_dual_capstone
  holonomy_adjoint_rot45 := fun {N} (hN : 2 ≤ N) {_s : ℂ} =>
    cascade_holonomy_adjoint_iff_rot45_equator (N := N) hN
  lseries_rot90 := mulModBSD_lseries_half_plane_iff_rot90_positive
  height_phase_open := on_line_zero_spectral_product_opposed_from_slot_budget_of_height_carrier

def RotationAdjointHeightPhaseBSDBridgeInhabited : Prop :=
  Nonempty RotationAdjointHeightPhaseBSDBridge

theorem rotation_adjoint_height_phase_bsd_bridge_inhabited :
    RotationAdjointHeightPhaseBSDBridgeInhabited :=
  ⟨rotation_adjoint_height_phase_bsd_bridge⟩

/--
**RH attack chain (conditional on the open height pin).**  Once
`OnLineZeroHeightPhaseLockFromSlotBudget` holds, slot-budget zeros yield full
perturbed holonomy adjoint on the `(6,5,11)` associator sheet.
-/
theorem on_line_zero_perturbed_adjoint_from_rotation_open_pin
    (hHeight : OnLineZeroHeightPhaseLockFromSlotBudget) {ρ : ℂ}
    (hζ : IsNontrivialZetaZero ρ) (hBudget : GoldbachSlotPhasePinBudgetAt ρ)
    (hNon : associatorPerturbNonNormalityWitnessAt ρ) :
    perturbedHolonomyFullAdjointAt 3 (by decide) ρ :=
  on_line_zero_perturbed_adjoint_from_slot_budget_of_height_carrier hHeight hζ hBudget hNon

end

end Hqiv.Story
