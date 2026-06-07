import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Basic
import Hqiv.Physics.ComptonHorizonPhase
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.MetaHorizonTrappedPlanckMass

namespace Hqiv.Physics

open scoped BigOperators
open Hqiv
open ContinuousXiPath

/-!
# Continuous shell-chart readout: Compton phase deficit on the trapped-Planck mass ladder

Integer shells `m ∈ ℕ` are readout samples.  The carrier need not sit exactly on
those labels: the continuous horizon coordinate `ξ = m + 1`
(`ContinuousXiPath.xiOfShell`) records motion between samples and supplies the
phase-corrected readout coordinate.

When a carrier is **in motion** on the null lattice, each excitation quantum borrows a
fraction `1/(4ξ_j)` of a shell index — the quarter-turn Compton budget
(`horizonQuarterPeriod / twoPi = 1/4`) per unit `ξ`.

The **phase-corrected** trapped-Planck readout evaluates the inside ratio at
`m_eff = totalModeShell n ℓ − metaHorizonComptonPhaseDeficit n ℓ` (linear
interpolation between integer shell samples).

Python mirror: `scripts/hqiv_continuous_shell_mass.py` (`ContinuousReadout.PHASE`).
-/

/-! ## Compton quarter-leak per excitation step -/

/-- Compton quarter-leak at excitation step `j ≥ 1` on the lock-in ladder:
`1/(4 ξ)` with `ξ = xiOfShell (referenceM + j)`. -/
noncomputable def comptonQuarterLeakAtStep (j : ℕ) : ℝ :=
  1 / (4 * xiOfShell (referenceM + j))

private theorem xiOfShell_referenceM_add_pos (j : ℕ) :
    0 < xiOfShell (referenceM + j) := by
  unfold xiOfShell
  positivity

theorem comptonQuarterLeakAtStep_pos {j : ℕ} :
    0 < comptonQuarterLeakAtStep j := by
  unfold comptonQuarterLeakAtStep
  exact div_pos one_pos (mul_pos (by norm_num : (0 : ℝ) < 4) (xiOfShell_referenceM_add_pos j))

theorem comptonQuarterLeakAtStep_eq_horizonQuarter_over_twoPi_xi (j : ℕ) :
    comptonQuarterLeakAtStep j =
      Hqiv.horizonQuarterPeriod / (Hqiv.twoPi * xiOfShell (referenceM + j)) := by
  unfold comptonQuarterLeakAtStep Hqiv.horizonQuarterPeriod Hqiv.twoPi
  field_simp [xiOfShell_ne_zero (referenceM + j)]

/-- Cumulative shell-index pull-back for `n + ℓ` excitation quanta. -/
noncomputable def metaHorizonComptonPhaseDeficit (n ℓ : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n + ℓ), comptonQuarterLeakAtStep j

theorem metaHorizonComptonPhaseDeficit_zero :
    metaHorizonComptonPhaseDeficit 0 0 = 0 := by
  unfold metaHorizonComptonPhaseDeficit comptonQuarterLeakAtStep
  simp

theorem metaHorizonComptonPhaseDeficit_nonneg (n ℓ : ℕ) :
    0 ≤ metaHorizonComptonPhaseDeficit n ℓ := by
  unfold metaHorizonComptonPhaseDeficit
  refine Finset.sum_nonneg ?_
  intro j _
  exact le_of_lt comptonQuarterLeakAtStep_pos

theorem metaHorizonComptonPhaseDeficit_pos {n ℓ : ℕ} (h : 0 < n + ℓ) :
    0 < metaHorizonComptonPhaseDeficit n ℓ := by
  unfold metaHorizonComptonPhaseDeficit
  have hmem : 1 ∈ Finset.Icc 1 (n + ℓ) := by
    simp [Finset.mem_Icc]
    omega
  have hne : (Finset.Icc 1 (n + ℓ)).Nonempty := ⟨1, hmem⟩
  refine Finset.sum_pos (fun j _ => ?_) hne
  exact comptonQuarterLeakAtStep_pos

/-! ## Effective continuous shell coordinate -/

/-- Phase-corrected shell readout coordinate (ℝ chart, not necessarily integer). -/
noncomputable def metaHorizonEffectiveShellPhase (n ℓ : ℕ) : ℝ :=
  (totalModeShell n ℓ : ℝ) - metaHorizonComptonPhaseDeficit n ℓ

theorem metaHorizonEffectiveShellPhase_ground :
    metaHorizonEffectiveShellPhase 0 0 = referenceM := by
  unfold metaHorizonEffectiveShellPhase metaHorizonComptonPhaseDeficit totalModeShell
  simp [referenceM_eq_four]

theorem metaHorizonEffectiveShellPhase_lt_total_of_excited {n ℓ : ℕ} (h : 0 < n + ℓ) :
    metaHorizonEffectiveShellPhase n ℓ < (totalModeShell n ℓ : ℝ) := by
  unfold metaHorizonEffectiveShellPhase
  exact sub_lt_self _ (metaHorizonComptonPhaseDeficit_pos h)

/-! ## Linear interpolation of trapped inside ratio -/

/-- Piecewise-linear extension of `metaHorizonTrappedInsideRatio` in the shell index. -/
noncomputable def metaHorizonTrappedInsideRatioInterp (m_exc : ℝ) (m_ref : ℕ) : ℝ :=
  let mFloor := Int.floor m_exc
  let mLo := Int.toNat mFloor
  let t := m_exc - mFloor
  let mHi := mLo + 1
  (1 - t) * metaHorizonTrappedInsideRatio mLo m_ref +
    t * metaHorizonTrappedInsideRatio mHi m_ref

theorem metaHorizonTrappedInsideRatioInterp_nat (m : ℕ) :
    metaHorizonTrappedInsideRatioInterp m referenceM =
      metaHorizonTrappedInsideRatio m referenceM := by
  unfold metaHorizonTrappedInsideRatioInterp
  simp [Int.floor_natCast, sub_self, zero_mul, add_zero, one_mul]

theorem metaHorizonTrappedInsideRatioInterp_referenceM_ground :
    metaHorizonTrappedInsideRatioInterp referenceM referenceM = 1 := by
  rw [metaHorizonTrappedInsideRatioInterp_nat referenceM]
  exact metaHorizonTrappedInsideRatio_referenceM_ground

/-! ## Phase-corrected trapped-Planck mass readout -/

/--
**Phase-corrected trapped-Planck mass readout** at lock-in.

Evaluates the trapped inside ratio at the Compton-deficit effective shell
`metaHorizonEffectiveShellPhase n ℓ` (continuous chart, not integer tag).
-/
noncomputable def metaHorizonTrappedPlanckMassPhaseReadout (n ℓ : ℕ) : ℝ :=
  derivedProtonMass *
    metaHorizonTrappedInsideRatioInterp
      (metaHorizonEffectiveShellPhase n ℓ) referenceM

theorem metaHorizonTrappedPlanckMassPhaseReadout_ground :
    metaHorizonTrappedPlanckMassPhaseReadout 0 0 = derivedProtonMass := by
  unfold metaHorizonTrappedPlanckMassPhaseReadout
  rw [metaHorizonEffectiveShellPhase_ground]
  simp [metaHorizonTrappedInsideRatioInterp_referenceM_ground]

private theorem metaHorizonEffectiveShellPhase_one_zero :
    metaHorizonEffectiveShellPhase 1 0 = (5 : ℝ) - 1 / 24 := by
  unfold metaHorizonEffectiveShellPhase metaHorizonComptonPhaseDeficit comptonQuarterLeakAtStep xiOfShell
    totalModeShell
  simp only [Nat.add_zero, Nat.add_one, referenceM_eq_four]
  norm_num

private theorem metaHorizonTrappedInsideRatioInterp_one_zero :
    metaHorizonTrappedInsideRatioInterp ((5 : ℝ) - 1 / 24) referenceM =
      (1 / 24) * metaHorizonTrappedInsideRatio 4 referenceM +
        (23 / 24) * metaHorizonTrappedInsideRatio 5 referenceM := by
  unfold metaHorizonTrappedInsideRatioInterp
  have hf : Int.floor ((5 : ℝ) - 1 / 24) = 4 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  simp only [hf]
  norm_num
  simp only [Nat.add_one, referenceM_eq_four]
  rfl

theorem metaHorizonTrappedPlanckMassPhaseReadout_one_zero_lt_discrete :
    metaHorizonTrappedPlanckMassPhaseReadout 1 0 <
      metaHorizonTrappedPlanckMassReadout 1 0 := by
  unfold metaHorizonTrappedPlanckMassPhaseReadout metaHorizonTrappedPlanckMassReadout
  rw [metaHorizonEffectiveShellPhase_one_zero, metaHorizonTrappedInsideRatioInterp_one_zero]
  simp only [totalModeShell, referenceM_eq_four, Nat.add_zero, Nat.add_one]
  have hr4 : metaHorizonTrappedInsideRatio 4 referenceM = 1 := by
    rw [show referenceM = 4 from referenceM_eq_four]
    exact metaHorizonTrappedInsideRatio_referenceM_ground
  have hr5 : metaHorizonTrappedInsideRatio 4 referenceM <
      metaHorizonTrappedInsideRatio 5 referenceM := by
    rw [hr4]
    exact metaHorizonTrappedInsideRatio_gt_one_of_shell_gt (by decide : referenceM < 5)
  have hproton : 0 < derivedProtonMass := derivedProtonMass_pos
  have hblend :
      (1 / 24) * metaHorizonTrappedInsideRatio 4 referenceM +
        (23 / 24) * metaHorizonTrappedInsideRatio 5 referenceM <
      metaHorizonTrappedInsideRatio 5 referenceM := by
    rw [hr4]
    nlinarith [hr5]
  exact mul_lt_mul_of_pos_left hblend hproton

theorem metaHorizonTrappedPlanckMassPhaseReadout_one_zero_gt_ground :
    derivedProtonMass < metaHorizonTrappedPlanckMassPhaseReadout 1 0 := by
  unfold metaHorizonTrappedPlanckMassPhaseReadout
  rw [metaHorizonEffectiveShellPhase_one_zero, metaHorizonTrappedInsideRatioInterp_one_zero]
  have hr4 : metaHorizonTrappedInsideRatio 4 referenceM = 1 := by
    rw [show referenceM = 4 from referenceM_eq_four]
    exact metaHorizonTrappedInsideRatio_referenceM_ground
  have hr5 : 1 < metaHorizonTrappedInsideRatio 5 referenceM :=
    metaHorizonTrappedInsideRatio_gt_one_of_shell_gt (by decide : referenceM < 5)
  have hproton : 0 < derivedProtonMass := derivedProtonMass_pos
  have hblend :
      1 < (1 / 24) * metaHorizonTrappedInsideRatio 4 referenceM +
        (23 / 24) * metaHorizonTrappedInsideRatio 5 referenceM := by
    rw [hr4]
    nlinarith [hr5]
  rw [mul_comm derivedProtonMass]
  apply lt_mul_of_one_lt_left hproton hblend

structure MetaHorizonContinuousShellWitness where
  phase_ground :
    metaHorizonTrappedPlanckMassPhaseReadout 0 0 = derivedProtonMass
  phase_deficit_zero :
    metaHorizonComptonPhaseDeficit 0 0 = 0
  effective_shell_ground :
    metaHorizonEffectiveShellPhase 0 0 = referenceM
  compton_leak_horizon_bridge :
    comptonQuarterLeakAtStep 1 =
      Hqiv.horizonQuarterPeriod / (Hqiv.twoPi * xiOfShell (referenceM + 1))
  delta_one_zero_closer_than_discrete :
    metaHorizonTrappedPlanckMassPhaseReadout 1 0 <
      metaHorizonTrappedPlanckMassReadout 1 0
  phase_one_zero_gt_ground :
    derivedProtonMass < metaHorizonTrappedPlanckMassPhaseReadout 1 0

theorem metaHorizonContinuousShellWitness_default : MetaHorizonContinuousShellWitness where
  phase_ground := metaHorizonTrappedPlanckMassPhaseReadout_ground
  phase_deficit_zero := metaHorizonComptonPhaseDeficit_zero
  effective_shell_ground := metaHorizonEffectiveShellPhase_ground
  compton_leak_horizon_bridge := comptonQuarterLeakAtStep_eq_horizonQuarter_over_twoPi_xi 1
  delta_one_zero_closer_than_discrete := metaHorizonTrappedPlanckMassPhaseReadout_one_zero_lt_discrete
  phase_one_zero_gt_ground := metaHorizonTrappedPlanckMassPhaseReadout_one_zero_gt_ground

end Hqiv.Physics
