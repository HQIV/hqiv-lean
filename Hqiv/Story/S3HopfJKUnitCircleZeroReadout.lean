import Hqiv.Story.S3StripRollingProjection
import Hqiv.Story.S3ZetaAxisRotationProjection
import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3HopfShellHolonomy
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Critical-line zeros on the Hopf `j`–`k` unit circle

The critical line `Re s = ½` lifts into `ℍ` as a **unit circle** in the `j`/`k`
plane (`stripRollingMap`, `hopfFiberCoords`).  In `ℂ` one writes phases as
`exp(i θ)`; in the quaternion chart the imaginary unit is carried by the
**`j`–`k` plane** (`zetaSinSlot` / `zetaCosSlot` are the FE rotation slots).

This module rearranges ζ-zeros on the line in that projection:

* **coordinates** — `(j, k) = (cos t, sin t)` on `S¹` (`hopfJKCirclePoint`);
* **phase** — `exp(π · j · k · i)` (`hopfJKUnitCirclePhase`): the `j*k` product
  mediates the complex exponential (quaternion convention `j*k = i`);
* **amplitude** — 45° projection `j/√2 + k/√2` (`hopfJKCriticalAmplitude`);
* **zero** — amplitude vanishes ⟺ `j + k = 0` on the circle.

The strip height `t` is only the cover parameter; the **compact** object is the
`j`–`k` circle point and its phase–amplitude pair.

**Honesty.**  `ζ(s) = 0` on the line as this readout still requires
`RollingZetaIdentificationAtCriticalLine`.  The circle geometry and balance
locus are unconditional.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## Unit circle in the `j`–`k` plane -/

/-- Point on the Hopf unit circle: `(j, k) = (cos t, sin t)`. -/
noncomputable def hopfJKCirclePoint (t : ℝ) : ℝ × ℝ :=
  (hopfFiberCoords t 0, hopfFiberCoords t 1)

theorem hopf_jk_circle_on_unit (t : ℝ) :
    (hopfJKCirclePoint t).1 ^ 2 + (hopfJKCirclePoint t).2 ^ 2 = 1 := by
  dsimp [hopfJKCirclePoint]
  simpa using hopf_fiber_on_unit_circle t

theorem hopf_jk_circle_eq_base_proj (t : ℝ) :
    hopfJKCirclePoint t =
      (hopfBaseProj (stripRollingMap t) 0, hopfBaseProj (stripRollingMap t) 1) := by
  simp [hopfJKCirclePoint, hopfBaseProj, hopfFiberCoords, stripRollingMap,
    hopf_base_proj_strip_rolling]

/-- Bilinear `j·k` coefficient on the circle. -/
noncomputable def hopfJKProduct (t : ℝ) : ℝ :=
  (hopfJKCirclePoint t).1 * (hopfJKCirclePoint t).2

theorem hopf_jk_product_eq (t : ℝ) :
    hopfJKProduct t = Real.cos t * Real.sin t := by
  dsimp [hopfJKProduct, hopfJKCirclePoint, hopfFiberCoords]

theorem hopf_jk_product_period (t : ℝ) (n : ℤ) :
    hopfJKProduct (t + 2 * Real.pi * (n : ℝ)) = hopfJKProduct t := by
  rw [hopf_jk_product_eq, hopf_jk_product_eq]
  rw [show t + 2 * Real.pi * (n : ℝ) = t + (n : ℝ) * (2 * Real.pi) by ring]
  simp [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-! ## `exp(π · j · k · i)` — phase readout replacing bare `exp(i t)` -/

/--
Unit-circle phase driven by the `j`–`k` product.

Classically `exp(π i) = −1`; here the generator is the **coordinate product**
`j·k` on the Hopf circle, embedded into `ℂ` via `j*k ↦ i`.
-/
noncomputable def hopfJKUnitCirclePhase (t : ℝ) : ℂ :=
  exp (I * (Real.pi * hopfJKProduct t))

theorem hopf_jk_unit_circle_phase_on_circle (t : ℝ) :
    ‖hopfJKUnitCirclePhase t‖ = 1 := by
  simpa [hopfJKUnitCirclePhase] using
    norm_exp_I_mul_ofReal (Real.pi * hopfJKProduct t)

/-! ## 45° amplitude on the `j`–`k` circle -/

/-- 45°-projected amplitude from `j` and `k` coordinates on the rolled line. -/
noncomputable def hopfJKCriticalAmplitude (t : ℝ) : ℝ :=
  jAxisProj (stripRollingMap t) + kAxisProj (stripRollingMap t)

theorem hopf_jk_amplitude_eq_critical_proj (t : ℝ) :
    hopfJKCriticalAmplitude t = criticalProj (stripRollingMap t) := by
  dsimp [hopfJKCriticalAmplitude, jAxisProj, kAxisProj, criticalProj, imagSum,
    stripRollingMap]
  ring

theorem hopf_jk_amplitude_eq_coord_sum_scaled (t : ℝ) :
    hopfJKCriticalAmplitude t =
      ((hopfJKCirclePoint t).1 + (hopfJKCirclePoint t).2) / Real.sqrt 2 := by
  dsimp [hopfJKCriticalAmplitude, jAxisProj, kAxisProj, hopfJKCirclePoint,
    hopfFiberCoords, stripRollingMap]
  ring

theorem hopf_jk_amplitude_eq_cos_sub_pi_four (t : ℝ) :
    hopfJKCriticalAmplitude t = Real.cos (t - Real.pi / 4) := by
  rw [hopf_jk_amplitude_eq_critical_proj, strip_rolling_critical_proj_eq_cos_sub_pi_four]

theorem hopf_jk_amplitude_eq_zero_iff (t : ℝ) :
    hopfJKCriticalAmplitude t = 0 ↔
      ∃ n : ℤ, t = (3 * Real.pi / 4) + (n : ℝ) * Real.pi := by
  rw [hopf_jk_amplitude_eq_critical_proj, strip_rolling_critical_proj_eq_zero_iff]

theorem hopf_jk_amplitude_zero_iff_coord_sum (t : ℝ) :
    hopfJKCriticalAmplitude t = 0 ↔
      (hopfJKCirclePoint t).1 + (hopfJKCirclePoint t).2 = 0 := by
  rw [hopf_jk_amplitude_eq_coord_sum_scaled]
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hsum | hden
    · exact hsum
    · have hsqrt : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
      exact absurd hden hsqrt
  · intro hsum
    rw [hsum, zero_div]

/-! ## Twiddle readout: phase × amplitude -/

/--
Full `j`–`k` twiddle readout: `exp(π·j·k·i)` against the 45° amplitude.

This is the rearranged critical-line dictionary: phase from the `j`–`k` product,
vanishing from amplitude balance on `S¹`.
-/
noncomputable def hopfJKTwiddleReadout (t : ℝ) : ℂ :=
  hopfJKUnitCirclePhase t * (hopfJKCriticalAmplitude t : ℂ)

theorem hopf_jk_twiddle_vanishes_iff_amplitude (t : ℝ) :
    hopfJKTwiddleReadout t = 0 ↔ hopfJKCriticalAmplitude t = 0 := by
  dsimp [hopfJKTwiddleReadout]
  constructor
  · intro h
    rw [mul_eq_zero] at h
    rcases h with hPhase | hAmp
    · exact False.elim (Complex.exp_ne_zero _ hPhase)
    · exact Complex.ofReal_eq_zero.mp hAmp
  · intro hAmp
    simp [hopfJKTwiddleReadout, hAmp]

theorem hopf_jk_twiddle_vanishes_iff_cos_sin (t : ℝ) :
    hopfJKTwiddleReadout t = 0 ↔ Real.cos t + Real.sin t = 0 := by
  rw [hopf_jk_twiddle_vanishes_iff_amplitude, hopf_jk_amplitude_eq_critical_proj,
    strip_rolling_cancellation_iff]

/-! ## ζ-zeros rearranged through the `H` lift (conditional) -/

theorem zeta_zero_iff_hopf_jk_amplitude
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    riemannZeta (criticalLinePointAtHeight t) = 0 ↔
      hopfJKCriticalAmplitude t = 0 := by
  have hLine : (criticalLinePointAtHeight t).re = (1 / 2 : ℝ) := by
    simp [criticalLinePointAtHeight]
  simpa [← hopf_jk_amplitude_eq_critical_proj] using
    zeta_zero_iff_rolling_cancellation_of_match
      (rolling_matches_critical_height_rolledSample hLine) (hId t)

theorem zeta_zero_iff_hopf_jk_twiddle
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    riemannZeta (criticalLinePointAtHeight t) = 0 ↔
      hopfJKTwiddleReadout t = 0 := by
  rw [zeta_zero_iff_hopf_jk_amplitude hId, hopf_jk_twiddle_vanishes_iff_amplitude]

theorem zeta_zero_iff_hopf_jk_circle_balance
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    riemannZeta (criticalLinePointAtHeight t) = 0 ↔
      (hopfJKCirclePoint t).1 + (hopfJKCirclePoint t).2 = 0 := by
  simpa using
    (zeta_zero_iff_hopf_jk_amplitude hId t).trans (hopf_jk_amplitude_zero_iff_coord_sum t)

/--
Bundle: critical line → `j`–`k` unit circle → `exp(π·j·k·i)` phase × amplitude;
ζ-zeros (conditional) are amplitude balance on `S¹`.
-/
structure HopfJKUnitCircleZeroBundle where
  on_unit_circle : ∀ t, (hopfJKCirclePoint t).1 ^ 2 + (hopfJKCirclePoint t).2 ^ 2 = 1
  phase_on_circle : ∀ t, ‖hopfJKUnitCirclePhase t‖ = 1
  twiddle_vanishes_iff_amplitude :
    ∀ t, hopfJKTwiddleReadout t = 0 ↔ hopfJKCriticalAmplitude t = 0
  balance_iff_cos_sin :
    ∀ t, hopfJKCriticalAmplitude t = 0 ↔ Real.cos t + Real.sin t = 0

noncomputable def hopfJKUnitCircleZeroBundle : HopfJKUnitCircleZeroBundle where
  on_unit_circle := hopf_jk_circle_on_unit
  phase_on_circle := hopf_jk_unit_circle_phase_on_circle
  twiddle_vanishes_iff_amplitude := hopf_jk_twiddle_vanishes_iff_amplitude
  balance_iff_cos_sin := fun t => by
    rw [hopf_jk_amplitude_eq_critical_proj, strip_rolling_cancellation_iff]

/-!
## Status

* **Unconditional:** `j`–`k` unit circle; `exp(π·j·k·i)` phase; amplitude =
  `j/√2 + k/√2`; twiddle vanishes ⟺ `j + k = 0` ⟺ `cos t + sin t = 0`.
* **Conditional:** `ζ(½+it)=0` ⟺ amplitude/twiddle vanishes under
  `RollingZetaIdentificationAtCriticalLine`.
-/

end

end Hqiv.Story
