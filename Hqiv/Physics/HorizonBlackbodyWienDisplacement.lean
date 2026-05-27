import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.HorizonBlackbodySpectrum
import Hqiv.Physics.HorizonBlackbodyLadder
import Hqiv.Physics.HorizonBlackbodyStefan

/-!
# HQIV Wien displacement law: the transition shell

For the truncated blackbody spectrum on the HQIV null lattice, the standard
Wien displacement constant `ω_peak / T ≈ 2.821` is replaced by a clean
**transition-shell theorem**: the largest shell whose mode frequency
`ω_m = T_Pl/(m+1)` is still at least the bath temperature `T`.

Define
  `transitionShellIndex T := ⌊1/T⌋ - 1` (Nat-truncated).

We prove (for `0 < T ≤ 1`, i.e., below the Planck scale):

* `transitionShell_RJ_side : T ≤ ω_{m*}` — the transition shell is still
  Rayleigh–Jeans-side (or exactly at the crossover).
* `transitionShell_Wien_side : ω_{m*+1} < T` — the next shell is strictly
  Wien-side.
* `wienDisplacement_lowerBound : 1 ≤ ω_{m*} / T` — Wien displacement ratio
  is at least 1 (Planck-unit form of the HQIV crossover).
* `wienDisplacement_upperBound : ω_{m*} / T < 1 + ω_{m*}` — and bounded
  above by `1 + ω_{m*}`, so as `T → 0`, `ω_{m*} → 0` and the ratio → 1.

**HQIV Wien displacement constant** = 1 (exact, in natural Planck units).
The residue `ω_{m*}/T - 1 < ω_{m*}` vanishes in the cold limit.

Zero `sorry`; no new axioms.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-! ## Transition shell definition -/

/-- The **HQIV transition shell index** `m*(T) = ⌊1/T⌋ - 1` (Nat-truncated).
This is the largest shell whose mode frequency `ω_m` is at least `T`
(when `0 < T ≤ T_Pl = 1`). -/
noncomputable def transitionShellIndex (T : ℝ) : ℕ :=
  Nat.floor (1 / T) - 1

/-- In the cold regime `0 < T ≤ 1`, `m*(T) + 1 = ⌊1/T⌋`. -/
theorem transitionShellIndex_succ_eq_floor (T : ℝ)
    (hT : 0 < T) (hT_le : T ≤ 1) :
    transitionShellIndex T + 1 = Nat.floor (1 / T : ℝ) := by
  unfold transitionShellIndex
  have h1T_ge_one : (1 : ℝ) ≤ 1 / T := by
    rw [le_div_iff₀ hT]; linarith
  have hfloor_pos : 1 ≤ Nat.floor (1 / T : ℝ) := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro h
    have hh : (1 / T : ℝ) < 1 := Nat.floor_eq_zero.mp h
    linarith
  omega

/-! ## Crossover bounds -/

/-- **RJ side:** the transition shell still satisfies `T ≤ ω_{m*}`. -/
theorem transitionShell_RJ_side (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    T ≤ shellOmega (transitionShellIndex T) := by
  rw [shellOmega_eq]
  have key := transitionShellIndex_succ_eq_floor T hT hT_le
  have hcast : ((transitionShellIndex T : ℕ) : ℝ) + 1 =
      (Nat.floor (1 / T : ℝ) : ℝ) := by
    have : ((transitionShellIndex T + 1 : ℕ) : ℝ) =
        (Nat.floor (1 / T : ℝ) : ℝ) := by exact_mod_cast key
    push_cast at this; linarith
  rw [hcast]
  have hfloor_pos : 1 ≤ Nat.floor (1 / T : ℝ) := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro h
    have hh : (1 / T : ℝ) < 1 := Nat.floor_eq_zero.mp h
    have : (1 : ℝ) ≤ 1 / T := by rw [le_div_iff₀ hT]; linarith
    linarith
  have hfloor_pos_real : (0 : ℝ) < (Nat.floor (1 / T : ℝ) : ℝ) := by
    have : (1 : ℝ) ≤ (Nat.floor (1 / T : ℝ) : ℝ) := by exact_mod_cast hfloor_pos
    linarith
  have hfloor_le : (Nat.floor (1 / T : ℝ) : ℝ) ≤ 1 / T := by
    apply Nat.floor_le; positivity
  rw [le_div_iff₀ hfloor_pos_real]
  calc T * (Nat.floor (1 / T : ℝ) : ℝ) ≤ T * (1 / T) :=
        mul_le_mul_of_nonneg_left hfloor_le hT.le
    _ = 1 := by field_simp

/-- **Wien side:** the next shell strictly satisfies `ω_{m*+1} < T`. -/
theorem transitionShell_Wien_side (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    shellOmega (transitionShellIndex T + 1) < T := by
  rw [shellOmega_eq]
  have key := transitionShellIndex_succ_eq_floor T hT hT_le
  have hcast : ((transitionShellIndex T + 1 : ℕ) : ℝ) + 1 =
      (Nat.floor (1 / T : ℝ) : ℝ) + 1 := by
    have : ((transitionShellIndex T + 1 : ℕ) : ℝ) =
        (Nat.floor (1 / T : ℝ) : ℝ) := by exact_mod_cast key
    linarith
  rw [hcast]
  have hbound : (1 / T : ℝ) < (Nat.floor (1 / T : ℝ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloor_plus_one_pos : (0 : ℝ) < (Nat.floor (1 / T : ℝ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (Nat.floor (1 / T : ℝ) : ℝ) := by exact_mod_cast Nat.zero_le _
    linarith
  rw [div_lt_iff₀ hfloor_plus_one_pos]
  have h1 : T * (1 / T) < T * ((Nat.floor (1 / T : ℝ) : ℝ) + 1) :=
    mul_lt_mul_of_pos_left hbound hT
  have h2 : T * (1 / T) = 1 := by field_simp
  linarith

/-! ## Wien displacement law: `ω_{m*} / T ≈ 1` -/

/-- **Lower bound on the Wien displacement ratio:** `ω_{m*} / T ≥ 1`. -/
theorem wienDisplacement_lowerBound (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    1 ≤ shellOmega (transitionShellIndex T) / T := by
  rw [le_div_iff₀ hT, one_mul]
  exact transitionShell_RJ_side T hT hT_le

/-- **HQIV Wien displacement law (tight upper bound):**
`ω_{m*} / T < 1 + ω_{m*}`.  Since `ω_{m*} → 0` as `T → 0`, the ratio
`ω_{m*}/T → 1`.  The HQIV Wien displacement constant is **exactly 1** in
natural Planck units. -/
theorem wienDisplacement_upperBound (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    shellOmega (transitionShellIndex T) / T <
      1 + shellOmega (transitionShellIndex T) := by
  set m := transitionShellIndex T with hm_def
  have hWien : shellOmega (m + 1) < T := transitionShell_Wien_side T hT hT_le
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm2_pos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hWien_eq : shellOmega (m + 1) = 1 / ((m : ℝ) + 2) := by
    rw [shellOmega_eq (m + 1)]
    push_cast; ring
  rw [hWien_eq] at hWien
  have h1lt : (1 : ℝ) < T * ((m : ℝ) + 2) := by
    rw [div_lt_iff₀ hm2_pos] at hWien; linarith
  rw [shellOmega_eq m]
  rw [div_div, div_lt_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * T)]
  have hne : ((m : ℝ) + 1) ≠ 0 := ne_of_gt hm1_pos
  field_simp
  nlinarith [h1lt, hm1_pos, hT]

/-- **Symmetric Wien displacement law:** for any `0 < T ≤ 1`,
`1 ≤ ω_{m*} / T < 1 + ω_{m*}`.  Asymptotic ratio: `ω_{m*}/T → 1` as `T → 0`. -/
theorem wienDisplacement_bracket (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    1 ≤ shellOmega (transitionShellIndex T) / T ∧
      shellOmega (transitionShellIndex T) / T <
        1 + shellOmega (transitionShellIndex T) :=
  ⟨wienDisplacement_lowerBound T hT hT_le,
   wienDisplacement_upperBound T hT hT_le⟩

/-- **Wien residue bound:** the deviation `ω_{m*}/T - 1` is bounded
by the (small) mode frequency `ω_{m*}` itself. -/
theorem wienDisplacement_residue_bound (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    shellOmega (transitionShellIndex T) / T - 1 <
      shellOmega (transitionShellIndex T) := by
  have h := wienDisplacement_upperBound T hT hT_le
  linarith

/-- **Numerical witness at the lock-in window** for `T = 1/(referenceM+1)`:
the transition shell is exactly `referenceM = 4`. -/
theorem transitionShellIndex_at_referenceM :
    transitionShellIndex (1 / ((Hqiv.referenceM : ℝ) + 1)) = Hqiv.referenceM := by
  have hr : Hqiv.referenceM = 4 := by
    unfold Hqiv.referenceM Hqiv.qcdShell Hqiv.stepsFromQCDToLockin
      Hqiv.latticeStepCount
    norm_num
  rw [hr]
  unfold transitionShellIndex
  have hsimp : (1 : ℝ) / (1 / (((4 : ℕ) : ℝ) + 1)) = 5 := by push_cast; norm_num
  rw [hsimp]
  have h5 : Nat.floor (5 : ℝ) = 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) from by norm_num]
    exact Nat.floor_natCast 5
  rw [h5]

end

end Hqiv.Physics
