import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.HopfShellBeltramiMassBridge

namespace Hqiv.Physics

/-!
# Half-step ξ chart ↔ TUFT Beltrami ratios ↔ discrete shell steps

**Proved alignment (lock-in neighborhood).** TUFT minimal Beltrami ratio for fiber windings
`3 → 2` is `4/3`. On the HQIV discrete shell ladder, with chart `m = n + 1` for winding `n`,

`geometricResonanceStep (n_from+1) (n_to+1) = tuftBeltramiResonanceRatio n_from n_to`

at `(n_from,n_to) = (3,2)` — i.e. `geometricResonanceStep 4 3 = 4/3`.

**Half-step / overconstrained system.** The Python `hqiv_coupling_linear_system.py` normalization
objective samples `ξ_G = 7/2` (`xiHalfStep`), strictly between integer shells `m = 2` and `m = 3`
(`ξ = 3` and `ξ = 4`). That point is **off** the integer shell chart; it is not a third
`geometricResonanceStep` ratio.

**Beltrami `3/2` (windings `2 → 1`).** On integer shells, `geometricResonanceStep 3 2 = 35/24`.
The same `3/2` **does** appear as the holonomy-row budget ratio `holonomyRowRhs(v=2)/holonomyRowRhs(v=1)`
from the Fano `1,2,3` vertex weights (`ContinuousXiCoupling`). At the brace half-step `ξ_G = 7/2`,
the Python scan pins `1/α ≈ 137.036` with `c₀ ≈ 1` (`halfStepXiWitness`).

**Do not confuse charts:** lepton mass ratios (`175/76`, `4484/2499`) use distant shells `15,33,58`;
lock-in step `4/3` is the shell below `referenceM = 4`; holonomy `3/2` is the middle generation
slot in the overconstrained system.
-/

/-! ## Hopf winding ↔ shell index chart -/

/-- Weak-sector bookkeeping: TUFT fiber winding `n` ↔ discrete shell `m = n + 1`. -/
def hopfWindingToShellIndex (n : ℕ) : ℕ :=
  n + 1

theorem hopfWindingToShellIndex_succ (n : ℕ) :
    hopfWindingToShellIndex n = Nat.succ n := rfl

theorem hopfWindingToShellIndex_three : hopfWindingToShellIndex 3 = 4 := rfl
theorem hopfWindingToShellIndex_two : hopfWindingToShellIndex 2 = 3 := rfl
theorem hopfWindingToShellIndex_one : hopfWindingToShellIndex 1 = 2 := rfl

/-- Beltrami winding ratio packaged as a geometric resonance step on the shell chart. -/
noncomputable def geometricResonanceStepFromHopfWinding (n_from n_to : ℕ) : ℝ :=
  geometricResonanceStep (hopfWindingToShellIndex n_from) (hopfWindingToShellIndex n_to)

/-! ## `4/3` at lock-in neighbor shells `m = 4` and `m = 3` -/

theorem geometricResonanceStep_four_three_eq_four_thirds :
    geometricResonanceStep 4 3 = (4 : ℝ) / 3 := by
  unfold geometricResonanceStep detunedShellSurface shellSurface rindlerDetuningShared c_rindler_shared
  rw [gamma_eq_2_5]
  norm_num

theorem tuftBeltrami_tau_mu_eq_geometricResonance_lockin_neighbor :
    tuftBeltramiResonanceRatio 3 2 = geometricResonanceStep 4 3 := by
  rw [tuftBeltramiResonanceRatio_tau_mu, geometricResonanceStep_four_three_eq_four_thirds]

theorem tuftBeltrami_tau_mu_eq_geometricResonanceFromHopf_three_two :
    tuftBeltramiResonanceRatio 3 2 = geometricResonanceStepFromHopfWinding 3 2 := by
  rw [geometricResonanceStepFromHopfWinding, hopfWindingToShellIndex_three,
    hopfWindingToShellIndex_two, tuftBeltrami_tau_mu_eq_geometricResonance_lockin_neighbor]

/-! ## `3/2` Beltrami label ≠ integer-shell geometric step at `(3,2)` -/

theorem geometricResonanceStep_three_two_eq_thirtyFive_twentyFour :
    geometricResonanceStep 3 2 = (35 : ℝ) / 24 := by
  unfold geometricResonanceStep detunedShellSurface shellSurface rindlerDetuningShared c_rindler_shared
  rw [gamma_eq_2_5]
  norm_num

theorem tuftBeltrami_mu_e_ne_geometricResonanceStep_three_two :
    tuftBeltramiResonanceRatio 2 1 ≠ geometricResonanceStep 3 2 := by
  rw [tuftBeltramiResonanceRatio_mu_e, geometricResonanceStep_three_two_eq_thirtyFive_twentyFour]
  norm_num

/-! ## `3/2` in the overconstrained holonomy rows (Fano `1,2,3` pattern) -/

theorem tuftBeltrami_mu_e_eq_fanoHolonomyWeight_ratio :
    tuftBeltramiResonanceRatio 2 1 = (3 : ℝ) / 2 ∧
      ((3 : ℝ) / fanoWeightSum) / ((2 : ℝ) / fanoWeightSum) = (3 : ℝ) / 2 := by
  constructor
  · exact tuftBeltramiResonanceRatio_mu_e
  · exact fanoHolonomyWeight_ratio_three_halves

theorem tuftBeltrami_mu_e_eq_holonomyRowRhs_vertices :
    tuftBeltramiResonanceRatio 2 1 =
      holonomyRowRhs fanoVertexHeavyGen / holonomyRowRhs fanoVertexMiddle := by
  rw [tuftBeltramiResonanceRatio_mu_e, holonomyRowRhs_middle_heavy_ratio]

theorem tuftBeltrami_tau_mu_eq_shifted_holonomy_weight_ratio :
    tuftBeltramiResonanceRatio 3 2 = (4 : ℝ) / 3 ∧
      ((3 : ℝ) + 1) / ((2 : ℝ) + 1) = (4 : ℝ) / 3 := by
  constructor
  · exact tuftBeltramiResonanceRatio_tau_mu
  · exact fanoShiftedHolonomyWeight_ratio_four_thirds

theorem halfStepXiWitness_brace_pins_codata :
    halfStepXiWitness.bracedInvAlpha = 137.035999177 := by
  unfold halfStepXiWitness
  rfl

theorem halfStepXiWitness_c0_near_unity :
    |(halfStepXiWitness.c0 - 1)| < (1 / 100 : ℝ) := by
  unfold halfStepXiWitness
  norm_num

/-! ## Real-shell extension and half-step midpoint -/

/-- Affine detuned surface on a real shell coordinate (extends `detunedShellSurface`). -/
noncomputable def detunedShellSurfaceReal (x : ℝ) : ℝ :=
  (x + 1) * (x + 2) / rindlerDetuningShared x

theorem detunedShellSurfaceReal_eq_at_nat (m : ℕ) :
    detunedShellSurfaceReal (m : ℝ) = detunedShellSurface m := by
  unfold detunedShellSurfaceReal detunedShellSurface shellSurface rindlerDetuningShared
  rfl

/-- Midpoint of horizon coordinates between two integer shells. -/
noncomputable def xiMidpointBetween (m_lo m_hi : ℕ) : ℝ :=
  (xiOfShell m_lo + xiOfShell m_hi) / 2

/-- Real shell index at the midpoint: `ξ - 1`. -/
noncomputable def shellHalfStepBetween (m_lo m_hi : ℕ) : ℝ :=
  xiMidpointBetween m_lo m_hi - 1

theorem xiMidpointBetween_eq_average (m_lo m_hi : ℕ) :
    xiMidpointBetween m_lo m_hi = ((m_lo : ℝ) + (m_hi : ℝ) + 2) / 2 := by
  unfold xiMidpointBetween xiOfShell
  ring

theorem shellHalfStepBetween_two_three : shellHalfStepBetween 2 3 = (5 : ℝ) / 2 := by
  unfold shellHalfStepBetween xiMidpointBetween xiOfShell
  norm_num

theorem xiHalfStep_eq_midpoint_shells_two_three :
    xiHalfStep = xiMidpointBetween 2 3 := by
  rw [xiHalfStep_eq_three_point_five, xiMidpointBetween_eq_average]
  norm_num

theorem xiHalfStep_strictly_between_shells_two_three :
    xiOfShell 2 < xiHalfStep ∧ xiHalfStep < xiOfShell 3 := by
  constructor <;> norm_num [xiHalfStep_eq_three_point_five, xiOfShell]

theorem shellHalfStepBetween_two_three_eq_xiHalfStep_minus_one :
    shellHalfStepBetween 2 3 = xiHalfStep - 1 := by
  rw [shellHalfStepBetween_two_three, xiHalfStep_eq_three_point_five]
  norm_num

/-- Geometric step on the real shell chart. -/
noncomputable def geometricResonanceStepReal (x_from x_to : ℝ) : ℝ :=
  detunedShellSurfaceReal x_from / detunedShellSurfaceReal x_to

theorem geometricResonanceStepReal_eq_at_nat (m_from m_to : ℕ) :
    geometricResonanceStepReal (m_from : ℝ) (m_to : ℝ) = geometricResonanceStep m_from m_to := by
  unfold geometricResonanceStepReal geometricResonanceStep
  rw [detunedShellSurfaceReal_eq_at_nat, detunedShellSurfaceReal_eq_at_nat]

/-! ## Bundled witness -/

/-- Lock-in-adjacent shell step matches TUFT `4/3`; half-step sits between `m=2` and `m=3`. -/
structure HalfStepBeltramiShellWitness where
  beltrami_four_thirds : tuftBeltramiResonanceRatio 3 2 = (4 : ℝ) / 3
  geometric_four_thirds : geometricResonanceStep 4 3 = (4 : ℝ) / 3
  beltrami_eq_geometric_lockin_neighbor :
    tuftBeltramiResonanceRatio 3 2 = geometricResonanceStep 4 3
  beltrami_three_halves : tuftBeltramiResonanceRatio 2 1 = (3 : ℝ) / 2
  beltrami_three_halves_eq_holonomy :
    tuftBeltramiResonanceRatio 2 1 =
      holonomyRowRhs fanoVertexHeavyGen / holonomyRowRhs fanoVertexMiddle
  structural_residual_below_halfStep :
    structureXiWitness.residualNorm < halfStepXiWitness.residualNorm
  beltrami_three_halves_ne_geometric_three_two :
    tuftBeltramiResonanceRatio 2 1 ≠ geometricResonanceStep 3 2
  xi_half_between_two_three : xiOfShell 2 < xiHalfStep ∧ xiHalfStep < xiOfShell 3
  half_step_brace_alpha : halfStepXiWitness.bracedInvAlpha = 137.035999177

theorem halfStepBeltramiShellWitness_default : HalfStepBeltramiShellWitness where
  beltrami_four_thirds := tuftBeltramiResonanceRatio_tau_mu
  geometric_four_thirds := geometricResonanceStep_four_three_eq_four_thirds
  beltrami_eq_geometric_lockin_neighbor := tuftBeltrami_tau_mu_eq_geometricResonance_lockin_neighbor
  beltrami_three_halves := tuftBeltramiResonanceRatio_mu_e
  beltrami_three_halves_eq_holonomy := tuftBeltrami_mu_e_eq_holonomyRowRhs_vertices
  beltrami_three_halves_ne_geometric_three_two := tuftBeltrami_mu_e_ne_geometricResonanceStep_three_two
  xi_half_between_two_three := xiHalfStep_strictly_between_shells_two_three
  half_step_brace_alpha := halfStepXiWitness_brace_pins_codata
  structural_residual_below_halfStep := structure_residual_lt_halfStep

end Hqiv.Physics
