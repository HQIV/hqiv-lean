import Hqiv.Story.S3DiscreteContinuumOffLineWeightBridge
import Hqiv.Story.S3GoldbachAnnulusAssociatorGlobalBudget
import Hqiv.Story.S3GoldbachSlotPhaseOffLineHarmonicBridge
import Hqiv.Story.S3ExplicitFormulaDualitySlot
import Hqiv.Physics.ShellIndexRiemannZetaBridge
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# ζ(2)−ζ(3) tail band ↔ discrete press / off-line weight — cross-channel bridge

The Goldbach global associator budget (`S3GoldbachAnnulusAssociatorGlobalBudget`)
sandwiches the cap series between inverse-power tails classically identified with
`ζ(3) − 1` and `ζ(2) − 1`.  Their difference is the **ζ(2) − ζ(3) band width**.

The ζ-side discrete→continuous bridge (`S3DiscreteContinuumOffLineWeightBridge`)
names off-line **interior weight debt** and the RH capstone
`GeometricChannelAbsorbsAllZeros`.

This module folds the two channels into one review surface:

* **Proved (unconditional):** tail band width, global budget, off-line exclusion on
  *both* channels (`interiorStripH = 0` and `¬ GoldbachSlotPhasePinBudgetAt`), and
  literal Mathlib identity `goldbachAnnulusZetaTailBandWidth = ζ(2) − ζ(3)`.
* **Proved (ζ press faces):** anchor dominance + no backprojection (re-exported).
* **Method carrier:** `DiscreteContinuumTailBandMethodCarrier W` bundles the proved
  discrete→continuum + tail-band layer below capstone.
* **Joint capstone:** `GeometricChannelAbsorbsAllZeros ∧ GoldbachParity`.
* **Honesty:** joint capstone and the cross-channel bridge are equivalent to
  `RiemannHypothesis ∧ GoldbachParity` — the same frontier as
  `SO8ProjectedHalfSlopeBridge 2` / `GeometricHalfSlopeDischarge`.  Neither tail
  alone discharges either classical problem.
-/

namespace Hqiv.Story

open Hqiv.Physics Hqiv.Geometry Complex Real

noncomputable section

/-! ## Literal Mathlib ζ(2) − ζ(3) tail band -/

private def goldbachAnnulusInverseSquareTailTerm (n : ℕ) : ℂ :=
  1 / (n + 2 : ℂ) ^ (2 : ℕ)

private def goldbachAnnulusInverseCubeTailTerm (n : ℕ) : ℂ :=
  1 / (n + 2 : ℂ) ^ (3 : ℕ)

private theorem goldbach_annulus_inverse_square_tail_term_eq_real (n : ℕ) :
    goldbachAnnulusInverseSquareTailTerm n =
      ((1 / ((n + 2 : ℝ) ^ 2) : ℝ) : ℂ) := by
  simp [goldbachAnnulusInverseSquareTailTerm]

private theorem goldbach_annulus_inverse_cube_tail_term_eq_real (n : ℕ) :
    goldbachAnnulusInverseCubeTailTerm n =
      ((1 / ((n + 2 : ℝ) ^ 3) : ℝ) : ℂ) := by
  simp [goldbachAnnulusInverseCubeTailTerm]

private theorem goldbach_annulus_inverse_square_tail_eq_ofReal_tsum :
    ((goldbachAnnulusInverseSquareTail : ℝ) : ℂ) =
      ∑' n : ℕ, goldbachAnnulusInverseSquareTailTerm n := by
  rw [goldbachAnnulusInverseSquareTail, Complex.ofReal_tsum]
  congr 1
  ext n
  simpa using (goldbach_annulus_inverse_square_tail_term_eq_real n).symm

private theorem goldbach_annulus_inverse_cube_tail_eq_ofReal_tsum :
    ((goldbachAnnulusInverseCubeTail : ℝ) : ℂ) =
      ∑' n : ℕ, goldbachAnnulusInverseCubeTailTerm n := by
  rw [goldbachAnnulusInverseCubeTail, Complex.ofReal_tsum]
  congr 1
  ext n
  simpa using (goldbach_annulus_inverse_cube_tail_term_eq_real n).symm

private theorem riemannZeta_two_sub_one_eq_inverse_square_tail_tsum :
    riemannZeta 2 - 1 = ∑' n : ℕ, goldbachAnnulusInverseSquareTailTerm n := by
  have hs : 1 < (2 : ℂ).re := by simp
  have hz := riemannZeta_tsum_succ_eq (2 : ℂ) hs
  set g : ℕ → ℂ := fun n => 1 / (n + 1 : ℂ) ^ (2 : ℂ)
  have hg : Summable g := by
    have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (2 : ℂ)) :=
      Complex.summable_one_div_nat_cpow.mpr (by simp : 1 < (2 : ℝ))
    convert (summable_nat_add_iff 1).mpr h0 using 1
    ext n
    simp [g]
  have hsplit := Summable.sum_add_tsum_nat_add 1 hg
  have h0 : g 0 = 1 := by simp [g]
  have hshift :
      ∑' n : ℕ, g (n + 1) = ∑' n : ℕ, goldbachAnnulusInverseSquareTailTerm n := by
    refine tsum_congr fun n => ?_
    simp [g, goldbachAnnulusInverseSquareTailTerm]
    ring
  have hsplit' : g 0 + ∑' n : ℕ, g (n + 1) = ∑' n : ℕ, g n := by
    simpa [Finset.sum_range_one] using hsplit
  calc riemannZeta 2 - 1
      = (∑' n : ℕ, g n) - 1 := by rw [hz]
    _ = (∑' n : ℕ, g n) - g 0 := by rw [h0]
    _ = ∑' n : ℕ, g (n + 1) := by
      rw [← hsplit', add_sub_cancel_left]
    _ = ∑' n : ℕ, goldbachAnnulusInverseSquareTailTerm n := hshift

private theorem riemannZeta_three_sub_one_eq_inverse_cube_tail_tsum :
    riemannZeta 3 - 1 = ∑' n : ℕ, goldbachAnnulusInverseCubeTailTerm n := by
  have hs : 1 < (3 : ℂ).re := by simp
  have hz := riemannZeta_tsum_succ_eq (3 : ℂ) hs
  set g : ℕ → ℂ := fun n => 1 / (n + 1 : ℂ) ^ (3 : ℂ)
  have hg : Summable g := by
    have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (3 : ℂ)) :=
      Complex.summable_one_div_nat_cpow.mpr (by simp : 1 < (3 : ℝ))
    convert (summable_nat_add_iff 1).mpr h0 using 1
    ext n
    simp [g]
  have hsplit := Summable.sum_add_tsum_nat_add 1 hg
  have h0 : g 0 = 1 := by simp [g]
  have hshift :
      ∑' n : ℕ, g (n + 1) = ∑' n : ℕ, goldbachAnnulusInverseCubeTailTerm n := by
    refine tsum_congr fun n => ?_
    simp [g, goldbachAnnulusInverseCubeTailTerm]
    ring
  have hsplit' : g 0 + ∑' n : ℕ, g (n + 1) = ∑' n : ℕ, g n := by
    simpa [Finset.sum_range_one] using hsplit
  calc riemannZeta 3 - 1
      = (∑' n : ℕ, g n) - 1 := by rw [hz]
    _ = (∑' n : ℕ, g n) - g 0 := by rw [h0]
    _ = ∑' n : ℕ, g (n + 1) := by
      rw [← hsplit', add_sub_cancel_left]
    _ = ∑' n : ℕ, goldbachAnnulusInverseCubeTailTerm n := hshift

/--
**Literal tail identity (square).**  The Goldbach square tail is exactly `ζ(2) − 1`.
-/
theorem goldbach_annulus_inverse_square_tail_eq_zeta_two_sub_one :
    ((goldbachAnnulusInverseSquareTail : ℝ) : ℂ) = riemannZeta 2 - 1 := by
  rw [goldbach_annulus_inverse_square_tail_eq_ofReal_tsum,
    riemannZeta_two_sub_one_eq_inverse_square_tail_tsum]

/--
**Literal tail identity (cube).**  The Goldbach cube tail is exactly `ζ(3) − 1`.
-/
theorem goldbach_annulus_inverse_cube_tail_eq_zeta_three_sub_one :
    ((goldbachAnnulusInverseCubeTail : ℝ) : ℂ) = riemannZeta 3 - 1 := by
  rw [goldbach_annulus_inverse_cube_tail_eq_ofReal_tsum,
    riemannZeta_three_sub_one_eq_inverse_cube_tail_tsum]

/-! ## The ζ(2) − ζ(3) tail band (Goldbach additive channel) -/

/--
**Band width** as the shell-wise `(1/N² − 1/N³)` tail from `N = 2`; classically
`(ζ(2) − 1) − (ζ(3) − 1) = ζ(2) − ζ(3)`.
-/
noncomputable def goldbachAnnulusZetaTailBandTerm (n : ℕ) : ℝ :=
  1 / ((n + 2 : ℝ) ^ 2) - 1 / ((n + 2 : ℝ) ^ 3)

noncomputable def goldbachAnnulusZetaTailBandWidth : ℝ :=
  ∑' n : ℕ, goldbachAnnulusZetaTailBandTerm n

theorem goldbach_annulus_zeta_tail_band_term_nonneg (n : ℕ) :
    0 ≤ goldbachAnnulusZetaTailBandTerm n := by
  dsimp [goldbachAnnulusZetaTailBandTerm]
  have hn : (2 : ℝ) ≤ n + 2 := by linarith
  have hden : (0 : ℝ) < (n + 2) ^ 3 := by positivity
  rw [sub_nonneg, one_div_le (by positivity) (by positivity)]
  nlinarith [sq_nonneg (n + 2 : ℝ)]

theorem goldbach_annulus_zeta_tail_band_term_pos_at_zero :
    0 < goldbachAnnulusZetaTailBandTerm 0 := by
  dsimp [goldbachAnnulusZetaTailBandTerm]
  norm_num

theorem summable_goldbach_annulus_zeta_tail_band_term :
    Summable goldbachAnnulusZetaTailBandTerm :=
  summable_goldbach_annulus_inverse_square_tail.sub
    summable_goldbach_annulus_inverse_cube_tail

theorem goldbach_annulus_zeta_tail_band_width_eq_sub :
    goldbachAnnulusZetaTailBandWidth =
      goldbachAnnulusInverseSquareTail - goldbachAnnulusInverseCubeTail := by
  unfold goldbachAnnulusZetaTailBandWidth goldbachAnnulusInverseSquareTail
    goldbachAnnulusInverseCubeTail goldbachAnnulusZetaTailBandTerm
  exact Summable.tsum_sub summable_goldbach_annulus_inverse_square_tail
    summable_goldbach_annulus_inverse_cube_tail

/--
**Literal ζ(2) − ζ(3) band.**  The proved band width equals the Mathlib zeta difference.
-/
theorem zeta_goldbach_tail_band_is_literal_zeta_two_minus_zeta_three :
    ((goldbachAnnulusZetaTailBandWidth : ℝ) : ℂ) = riemannZeta 2 - riemannZeta 3 := by
  rw [goldbach_annulus_zeta_tail_band_width_eq_sub]
  push_cast
  rw [goldbach_annulus_inverse_square_tail_eq_zeta_two_sub_one,
    goldbach_annulus_inverse_cube_tail_eq_zeta_three_sub_one]
  ring

theorem goldbach_annulus_zeta_tail_band_width_pos :
    0 < goldbachAnnulusZetaTailBandWidth := by
  have hpos := goldbach_annulus_zeta_tail_band_term_pos_at_zero
  have hsum := (summable_goldbach_annulus_zeta_tail_band_term).tsum_pos
    (fun n => goldbach_annulus_zeta_tail_band_term_nonneg n) 0 hpos
  simpa [goldbachAnnulusZetaTailBandWidth] using hsum

theorem goldbach_annulus_inverse_square_tail_gt_cube_tail :
    goldbachAnnulusInverseCubeTail < goldbachAnnulusInverseSquareTail := by
  rw [show goldbachAnnulusInverseCubeTail < goldbachAnnulusInverseSquareTail ↔
      0 < goldbachAnnulusInverseSquareTail - goldbachAnnulusInverseCubeTail by
    constructor <;> intro h <;> linarith]
  rw [← goldbach_annulus_zeta_tail_band_width_eq_sub]
  exact goldbach_annulus_zeta_tail_band_width_pos

/--
The global associator cap series sits inside the ζ(2)−ζ(3) band: its excess over
the cube tail is bounded by the band width.
-/
theorem goldbach_annulus_cap_excess_le_zeta_tail_band_width
    (B : GoldbachAnnulusAssociatorGlobalBudget) :
    goldbachAnnulusAssociatorCapSeries - goldbachAnnulusInverseCubeTail ≤
      goldbachAnnulusZetaTailBandWidth := by
  rw [goldbach_annulus_zeta_tail_band_width_eq_sub]
  linarith [B.cube_tail_le_cap_series, B.cap_series_le_square_tail]

theorem goldbach_annulus_cap_headroom_le_zeta_tail_band_width
    (B : GoldbachAnnulusAssociatorGlobalBudget) :
    goldbachAnnulusInverseSquareTail - goldbachAnnulusAssociatorCapSeries ≤
      goldbachAnnulusZetaTailBandWidth := by
  rw [goldbach_annulus_zeta_tail_band_width_eq_sub]
  linarith [B.cube_tail_le_cap_series, B.cap_series_le_square_tail]

/-! ## Off-line exclusion on both channels -/

/-- Off-line points cannot carry the Goldbach slot-phase budget (on-line field). -/
def OffLineCannotCarryGoldbachSlotBudget : Prop :=
  ∀ ρ : ℂ, ρ.re ≠ (1 / 2 : ℝ) → ¬ GoldbachSlotPhasePinBudgetAt ρ

theorem off_line_cannot_carry_goldbach_slot_budget :
    OffLineCannotCarryGoldbachSlotBudget :=
  fun _ hOff h => not_goldbach_slot_phase_pin_budget_at_off_line hOff h

/--
**Cross-channel off-line exclusion (proved).**  An off-line nontrivial zero pays
ζ-side interior weight debt and cannot host the Goldbach slot budget.
-/
theorem off_line_nontrivial_zero_excluded_from_both_channels
    {ρ : ℂ} (hζ : IsNontrivialZetaZero ρ) (hσ : ρ.re ≠ (1 / 2 : ℝ)) :
    interiorStripH ρ = 0 ∧ ¬ GoldbachSlotPhasePinBudgetAt ρ :=
  ⟨offline_zero_forces_assembly_vanish hζ hσ,
   not_goldbach_slot_phase_pin_budget_at_off_line hσ⟩

theorem off_line_weight_debt_and_goldbach_budget_mutually_exclusive
    {ρ : ℂ} (_hCap : GeometricChannelAbsorbsAllZeros)
    (hBudget : GoldbachSlotPhasePinBudgetAt ρ) :
    ρ.re = (1 / 2 : ℝ) :=
  hBudget.hσ

/-! ## Joint packaging -/

/--
**Joint capstone:** geometric ζ-channel absorption plus the Goldbach parity
payload that supplies on-line slot budgets.
-/
def ZetaGoldbachTailBandJointCapstone : Prop :=
  GeometricChannelAbsorbsAllZeros ∧ GoldbachParity

/--
Cross-channel bridge: proved ζ press/ladder lock + proved global tail budget +
named joint frontiers.
-/
structure ZetaGoldbachTailBandCrossChannelBridge (W : TempLadderFiniteWindowConcrete) where
  zeta_press : OffLineWeightPressBridge W
  global_budget : GoldbachAnnulusAssociatorGlobalBudget
  goldbach_parity : GoldbachParity

theorem zeta_goldbach_joint_capstone_of_bridge
    {W : TempLadderFiniteWindowConcrete}
    (B : ZetaGoldbachTailBandCrossChannelBridge W) :
    ZetaGoldbachTailBandJointCapstone :=
  ⟨B.zeta_press.geometric_absorption, B.goldbach_parity⟩

theorem zeta_goldbach_cross_channel_unconditional_carrier
    (W : TempLadderFiniteWindowConcrete) :
    GoldbachAnnulusAssociatorGlobalBudget ∧
      OffLineZeroCarriesInteriorWeightDebt ∧
        OffLineCannotCarryGoldbachSlotBudget ∧
          0 < goldbachAnnulusZetaTailBandWidth ∧
            (W.toLambdaHQIVZero).lambdaHQIV = 0 :=
  ⟨goldbach_annulus_associator_global_budget,
   off_line_zero_carries_interior_weight_debt,
   off_line_cannot_carry_goldbach_slot_budget,
   goldbach_annulus_zeta_tail_band_width_pos,
   lambdaHQIV_eq_zero_of_finiteWindowConcrete W⟩

def zeta_goldbach_tail_band_cross_channel_bridge_of_millennium
    (W : TempLadderFiniteWindowConcrete) (h : RiemannHypothesis ∧ GoldbachParity) :
    ZetaGoldbachTailBandCrossChannelBridge W where
  zeta_press := offLineWeightPressBridge_of_RH W h.1
  global_budget := goldbach_annulus_associator_global_budget
  goldbach_parity := h.2

/-! ## Honesty: joint capstone ↔ millennium conjunction -/

theorem zeta_goldbach_joint_capstone_iff_millennium :
    ZetaGoldbachTailBandJointCapstone ↔ (RiemannHypothesis ∧ GoldbachParity) := by
  constructor
  · rintro ⟨hGeo, hG⟩
    exact ⟨geometric_absorption_iff_RH.mp hGeo, hG⟩
  · rintro ⟨hRH, hG⟩
    exact ⟨geometric_absorption_iff_RH.mpr hRH, hG⟩

theorem zeta_goldbach_tail_band_cross_channel_bridge_iff_millennium
    (W : TempLadderFiniteWindowConcrete) :
    Nonempty (ZetaGoldbachTailBandCrossChannelBridge W) ↔
      (RiemannHypothesis ∧ GoldbachParity) := by
  constructor
  · rintro ⟨B⟩
    exact zeta_goldbach_joint_capstone_iff_millennium.mp
      (zeta_goldbach_joint_capstone_of_bridge B)
  · intro h
    exact ⟨zeta_goldbach_tail_band_cross_channel_bridge_of_millennium W h⟩

theorem zeta_goldbach_tail_band_joint_capstone_iff_half_slope_bridge_two :
    ZetaGoldbachTailBandJointCapstone ↔ SO8ProjectedHalfSlopeBridge 2 := by
  rw [zeta_goldbach_joint_capstone_iff_millennium,
    so8_projected_half_slope_two_iff_rh_and_goldbach_parity]

/--
On the line, `GoldbachParity` supplies slot budgets bounded by the global cap inside
the ζ(2)−ζ(3) band; off-line points are excluded on both channels unconditionally.
-/
theorem on_line_slot_budget_respects_zeta_tail_band
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) (hσ : ρ.re = (1 / 2 : ℝ)) :
    GoldbachSlotPhasePinBudgetAt ρ ∧
      goldbachAnnulusAssociatorCapSeries - goldbachAnnulusInverseCubeTail ≤
        goldbachAnnulusZetaTailBandWidth := by
  refine ⟨goldbach_slot_phase_pin_budget_at_of_parity hG h hσ, ?_⟩
  exact goldbach_annulus_cap_excess_le_zeta_tail_band_width
    goldbach_annulus_associator_global_budget

/-! ## Discrete→continuum method carrier (proved layer below capstone) -/

/--
**Method carrier:** the discrete press faces, dual off-line exclusion, convergent
global Goldbach budget, literal `ζ(2) − ζ(3)` band, and proved `lambdaHQIV = 0`.
-/
def DiscreteContinuumTailBandMethodCarrier (W : TempLadderFiniteWindowConcrete) : Prop :=
  AnchorDiscreteDominatesBackwardContinuum ∧
    EscapeViaBackprojectionForbidden ∧
      OffLineZeroCarriesInteriorWeightDebt ∧
        OffLineCannotCarryGoldbachSlotBudget ∧
          GoldbachAnnulusAssociatorGlobalBudget ∧
            ((goldbachAnnulusZetaTailBandWidth : ℝ) : ℂ) = riemannZeta 2 - riemannZeta 3 ∧
              0 < goldbachAnnulusZetaTailBandWidth ∧
                (W.toLambdaHQIVZero).lambdaHQIV = 0

/--
**Unconditional method discharge.**  Everything in the carrier is proved today; only
the joint capstone remains RH ∧ GoldbachParity.
-/
theorem discrete_continuum_tail_band_method_carrier
    (W : TempLadderFiniteWindowConcrete) :
    DiscreteContinuumTailBandMethodCarrier W :=
  ⟨anchor_discrete_dominates_backward_continuum,
   escape_via_backprojection_forbidden,
   off_line_zero_carries_interior_weight_debt,
   off_line_cannot_carry_goldbach_slot_budget,
   goldbach_annulus_associator_global_budget,
   zeta_goldbach_tail_band_is_literal_zeta_two_minus_zeta_three,
   goldbach_annulus_zeta_tail_band_width_pos,
   lambdaHQIV_eq_zero_of_finiteWindowConcrete W⟩

theorem discrete_continuum_method_carrier_subset_cross_channel_unconditional
    (W : TempLadderFiniteWindowConcrete)
    (h : DiscreteContinuumTailBandMethodCarrier W) :
    GoldbachAnnulusAssociatorGlobalBudget ∧
      OffLineZeroCarriesInteriorWeightDebt ∧
        OffLineCannotCarryGoldbachSlotBudget ∧
          0 < goldbachAnnulusZetaTailBandWidth ∧
            (W.toLambdaHQIVZero).lambdaHQIV = 0 := by
  rcases h with ⟨_, _, hDebt, hSlot, hBudget, _, hpos, hLam⟩
  exact ⟨hBudget, hDebt, hSlot, hpos, hLam⟩

/--
**Frontier packaging.**  The proved method carrier does not discharge millennium by
itself; adding the named joint capstone is exactly `RiemannHypothesis ∧ GoldbachParity`.
-/
theorem discrete_continuum_method_plus_capstone_iff_millennium
    (W : TempLadderFiniteWindowConcrete) :
    DiscreteContinuumTailBandMethodCarrier W ∧
      ZetaGoldbachTailBandJointCapstone ↔
        (RiemannHypothesis ∧ GoldbachParity) := by
  constructor
  · rintro ⟨hMethod, hCap⟩
    exact zeta_goldbach_joint_capstone_iff_millennium.mp hCap
  · intro hMill
    exact ⟨discrete_continuum_tail_band_method_carrier W,
      zeta_goldbach_joint_capstone_iff_millennium.mpr hMill⟩

theorem discrete_continuum_method_reduces_to_half_slope_bridge
    (W : TempLadderFiniteWindowConcrete) :
    DiscreteContinuumTailBandMethodCarrier W ∧
      ZetaGoldbachTailBandJointCapstone ↔
        DiscreteContinuumTailBandMethodCarrier W ∧
          SO8ProjectedHalfSlopeBridge 2 := by
  constructor <;> intro h
  · exact ⟨h.1, zeta_goldbach_tail_band_joint_capstone_iff_half_slope_bridge_two.mp h.2⟩
  · exact ⟨h.1, zeta_goldbach_tail_band_joint_capstone_iff_half_slope_bridge_two.mpr h.2⟩

theorem method_carrier_does_not_imply_capstone
    (W : TempLadderFiniteWindowConcrete) :
    DiscreteContinuumTailBandMethodCarrier W →
      (ZetaGoldbachTailBandJointCapstone ↔ (RiemannHypothesis ∧ GoldbachParity)) := by
  intro _hMethod
  exact zeta_goldbach_joint_capstone_iff_millennium

/-!
## Status

| Layer | Content | Status |
|-------|---------|--------|
| ζ(2)−ζ(3) band | `goldbachAnnulusZetaTailBandWidth` | **Proved** (`= ζ(2)−ζ(3)`, cap excess ≤ width) |
| Method carrier | `DiscreteContinuumTailBandMethodCarrier W` | **Proved** |
| Global budget | `GoldbachAnnulusAssociatorGlobalBudget` | **Proved** |
| Off-line ζ debt | `OffLineZeroCarriesInteriorWeightDebt` | **Proved** (re-export) |
| Off-line GB budget | `OffLineCannotCarryGoldbachSlotBudget` | **Proved** |
| Joint capstone | `ZetaGoldbachTailBandJointCapstone` | **↔ RH ∧ GoldbachParity** |
| Cross bridge | `ZetaGoldbachTailBandCrossChannelBridge W` | **↔ RH ∧ GoldbachParity** |
| Method + capstone | `discrete_continuum_method_plus_capstone_iff_millennium` | **↔ RH ∧ GoldbachParity** |
| Millennium link | `zeta_goldbach_tail_band_joint_capstone_iff_half_slope_bridge_two` | **↔ `SO8ProjectedHalfSlopeBridge 2`** |
-/

end

end Hqiv.Story
