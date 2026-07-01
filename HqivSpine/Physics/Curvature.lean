import HqivSpine.Physics.Shell
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `HqivSpine.Physics.Curvature` — the curvature imprint `δ_E(m)`

The discrete curvature imprint, derived entirely from foundation integers:

* the imprint weight `1/(m+1)` (load-bearing: it strictly decays, and a continuum
  `m → ∞` limit destroys it);
* the per-shell shape `shellShape m = (1/(m+1)) · (1 + α·ln(m+1))` with `α = 3/5`;
* the combinatorial curvature norm `N₆₇ = 6⁷·√3`, where every piece is a foundation
  number: base `6 = signsPerAxis · transverseDim`, exponent `7 = imaginaryDim`,
  and `√3 = √transverseDim`;
* the imprint `δ_E(m) = N₆₇ · shellShape m`.

The true spatial curvature `Ω_k` is carried separately by the now slice.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-- The discrete imprint weight `1/(m+1)`. -/
noncomputable def imprintWeight (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

theorem imprintWeight_pos (m : ℕ) : 0 < imprintWeight m := by
  unfold imprintWeight; positivity

/-- **The imprint weight strictly decays in the shell index** — the discrete index
is load-bearing; a continuum `m → ∞` limit sends it to `0`. -/
theorem imprintWeight_strictAnti (m : ℕ) : imprintWeight (m + 1) < imprintWeight m := by
  unfold imprintWeight
  have h0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h1 : ((m : ℝ) + 1) < ((m : ℝ) + 1 + 1) := by linarith
  have := one_div_lt_one_div_of_lt h0 h1
  simpa [push_cast, add_assoc] using this

/-- **Per-shell curvature shape** `(1/(m+1)) · (1 + α·ln(m+1))`. -/
noncomputable def shellShape (m : ℕ) : ℝ :=
  imprintWeight m * (1 + alphaEM * Real.log ((m : ℝ) + 1))

/-- At the innermost shell `shellShape 0 = 1` (`ln 1 = 0`, `1/(0+1) = 1`). -/
theorem shellShape_zero : shellShape 0 = 1 := by
  simp [shellShape, imprintWeight]

/-- `shellShape m > 0` for every shell. -/
theorem shellShape_pos (m : ℕ) : 0 < shellShape m := by
  unfold shellShape
  have hw := imprintWeight_pos m
  have hx : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hlog : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg hx
  have hα : (0 : ℝ) ≤ alphaEM := by rw [alphaEM_eq]; norm_num
  have hfac : 0 < 1 + alphaEM * Real.log ((m : ℝ) + 1) := by
    have : 0 ≤ alphaEM * Real.log ((m : ℝ) + 1) := mul_nonneg hα hlog
    linarith
  exact mul_pos hw hfac

/-! ## The curvature shape is strictly antitone — one value per shell

The `1/(m+1)` decay beats the `1 + α·ln(m+1)` growth at `α = 3/5`: the per-shell
shape strictly decreases, so the imprint is **injective** in the shell index. A
given closed-curvature value is realised on *exactly one* shell. The single
analytic input is `log(1+x) ≤ x` (`Real.log_le_sub_one_of_pos`). -/

/-- **Per-shell step decay** `shellShape (m+1) < shellShape m`: the load-bearing
monotonicity. The cross-multiplied claim reduces to
`α·[(m+1)ln(m+2) − (m+2)ln(m+1)] < 1`, and the bracket is `≤ 1` because
`(m+1)·ln((m+2)/(m+1)) ≤ 1` while `ln(m+1) ≥ 0`; then `α = 3/5 < 1` closes it. -/
theorem shellShape_succ_lt (m : ℕ) : shellShape (m + 1) < shellShape m := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have ha1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have ha2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  simp only [shellShape, imprintWeight]
  have e1 : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
  rw [e1]
  rw [show (1 : ℝ) / ((m : ℝ) + 2) * (1 + alphaEM * Real.log ((m : ℝ) + 2)) =
        (1 + alphaEM * Real.log ((m : ℝ) + 2)) / ((m : ℝ) + 2) from by ring,
      show (1 : ℝ) / ((m : ℝ) + 1) * (1 + alphaEM * Real.log ((m : ℝ) + 1)) =
        (1 + alphaEM * Real.log ((m : ℝ) + 1)) / ((m : ℝ) + 1) from by ring,
      div_lt_div_iff₀ ha2 ha1]
  set L1 : ℝ := Real.log ((m : ℝ) + 1) with hL1
  set L2 : ℝ := Real.log ((m : ℝ) + 2) with hL2
  -- log((m+2)/(m+1)) = L2 - L1 ≤ 1/(m+1)
  have hlog_div : Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) = L2 - L1 := by
    rw [Real.log_div (ne_of_gt ha2) (ne_of_gt ha1)]
  have hle : L2 - L1 ≤ 1 / ((m : ℝ) + 1) := by
    have hr : (0 : ℝ) < ((m : ℝ) + 2) / ((m : ℝ) + 1) := by positivity
    have hstep := Real.log_le_sub_one_of_pos hr
    have hsub : ((m : ℝ) + 2) / ((m : ℝ) + 1) - 1 = 1 / ((m : ℝ) + 1) := by
      field_simp; ring
    rw [hlog_div] at hstep; linarith
  have hL1nn : 0 ≤ L1 := Real.log_nonneg (by linarith)
  -- bracket = (m+1)L2 − (m+2)L1 = (m+1)(L2−L1) − L1 ≤ 1 − 0
  have hbr : ((m : ℝ) + 1) * L2 - ((m : ℝ) + 2) * L1 ≤ 1 := by
    have h1 : ((m : ℝ) + 1) * (L2 - L1) ≤ ((m : ℝ) + 1) * (1 / ((m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hle (le_of_lt ha1)
    have h2 : ((m : ℝ) + 1) * (1 / ((m : ℝ) + 1)) = 1 := by field_simp
    nlinarith [h1, h2, hL1nn]
  rw [alphaEM_eq]
  nlinarith [hbr]

/-- **The curvature shape is strictly antitone in the shell index.** -/
theorem shellShape_strictAnti : StrictAnti shellShape :=
  strictAnti_nat_of_succ_lt shellShape_succ_lt

/-- **Injectivity:** distinct shells carry distinct curvature shapes. -/
theorem shellShape_injective : Function.Injective shellShape :=
  shellShape_strictAnti.injective

/-! ## The combinatorial curvature norm `N₆₇` -/

/-- Cube directions `= signsPerAxis · transverseDim = 2 · 3 = 6`. -/
def cubeDirections : ℕ := signsPerAxis * transverseDim

theorem cubeDirections_eq : cubeDirections = 6 := by decide

/-- **The combinatorial curvature norm** `N₆₇ = 6⁷·√3`, every factor derived:
base `cubeDirections = 6`, exponent `imaginaryDim = 7`, radicand `transverseDim = 3`. -/
noncomputable def curvatureNorm : ℝ :=
  (cubeDirections : ℝ) ^ imaginaryDim * Real.sqrt (transverseDim : ℝ)

theorem curvatureNorm_eq : curvatureNorm = (6 : ℝ) ^ 7 * Real.sqrt 3 := by
  unfold curvatureNorm
  rw [cubeDirections_eq, imaginaryDim_eq_seven]
  norm_num [transverseDim]

theorem curvatureNorm_pos : 0 < curvatureNorm := by
  rw [curvatureNorm_eq]
  have h1 : (0 : ℝ) < (6 : ℝ) ^ 7 := by positivity
  have h2 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  exact mul_pos h1 h2

/-- **The combinatorial curvature imprint** `δ_E(m) = N₆₇ · shellShape m`. -/
noncomputable def deltaE (m : ℕ) : ℝ := curvatureNorm * shellShape m

theorem deltaE_pos (m : ℕ) : 0 < deltaE m :=
  mul_pos curvatureNorm_pos (shellShape_pos m)

theorem deltaE_zero : deltaE 0 = curvatureNorm := by
  rw [deltaE, shellShape_zero, mul_one]

/-! ## Closed-curvature shell selection

`δ_E` inherits the strict antitonicity of `shellShape` (the positive constant
`N₆₇` cannot break monotonicity), so the imprint is injective: a closed-curvature
value lives on **exactly one** shell. This is the kinematical companion of the
emission-resonance fixed point in `Blackbody` — together they answer "why does
information live on shell `m`": a scale `ω_m` *lights up* shell `m` (Wien
resonance) and a closed curvature *pins* a unique shell (this injectivity). -/

/-- **The imprint `δ_E` is strictly antitone.** -/
theorem deltaE_strictAnti : StrictAnti deltaE := by
  intro a b hab
  rw [deltaE, deltaE]
  exact mul_lt_mul_of_pos_left (shellShape_strictAnti hab) curvatureNorm_pos

/-- **The imprint is injective in the shell index.** -/
theorem deltaE_injective : Function.Injective deltaE :=
  deltaE_strictAnti.injective

/-- **Closed-curvature uniqueness:** a curvature-imprint value is realised on at
most one shell — equal imprints force equal shell indices, so content carrying a
given closed curvature localises on a unique `m`. -/
theorem curvature_pins_unique_shell {m₁ m₂ : ℕ} (h : deltaE m₁ = deltaE m₂) :
    m₁ = m₂ :=
  deltaE_injective h

end HqivSpine.Physics
