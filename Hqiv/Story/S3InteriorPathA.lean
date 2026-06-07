import Hqiv.Story.S3InteriorStripHClosedForm
import Hqiv.Story.S3ZetaClosedForm
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Pathway A: functional equation for `interiorStripH`

The open-strip multiplier in Mathlib packaging is

`χ(s) = 2 · (2π)^{-(1-s)} · Γ(1-s) · cos(π(1-s)/2)`,

so `ζ(s) = χ(s) · ζ(1-s)` (`riemannZeta_open_strip_fe_closed_form`).

Because `so4CriticalFactor (1-s) = -so4CriticalFactor s`, the interior assembly
`h(s) := interiorStripH s = ζ(s) / so4CriticalFactor(s)` satisfies the **flipped**
reflection law

`h(s) = -χ(s) · h(1-s)`,

and the completed assembly `h(s) · so4CriticalFactor(s) = ζ(s)` satisfies the
standard `ζ(s) = χ(s) · ζ(1-s)` identity.

**Honesty.** This does **not** discharge the capstone: if `ζ(s) = 0` off the line
then `h(s) = 0` as well (`interiorStripH_eq_zero_iff_zeta_eq_zero_on_strip`).
Pathway A supplies the symmetry identity needed to study a completed interior
function; proving `h ≠ 0` at nontrivial zeros off the line remains RH-equivalent.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## FE multiplier χ(s) -/

/-- Open-strip functional-equation multiplier: `ζ(s) = χ(s) · ζ(1-s)`. -/
noncomputable def interiorStripFEMultiplier (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Gamma (1 - s) * zetaSinCosFactor (1 - s)

theorem interiorStripFEMultiplier_eq_odd_channel_ratio
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hζ1 : riemannZeta (1 - s) ≠ 0) :
    interiorStripFEMultiplier s = oddStripChannel s / riemannZeta (1 - s) := by
  unfold interiorStripFEMultiplier oddStripChannel zetaSinCosFactor
  field_simp [hζ1]

theorem riemannZeta_eq_interiorStripFEMultiplier_mul
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta s = interiorStripFEMultiplier s * riemannZeta (1 - s) := by
  unfold interiorStripFEMultiplier
  exact riemannZeta_open_strip_fe_closed_form s h0 h1

/-! ## Reflection aliases -/

theorem so4CriticalFactor_reflection (s : ℂ) :
    so4CriticalFactor (1 - s) = -so4CriticalFactor s :=
  so4CriticalFactor_one_sub s

/-! ## Functional equation for `h` -/

/--
**Interior `h` functional equation (pathway A).**

Off `σ = 1/2` and `(1-σ) = 1/2`, the normalized assembly satisfies
`h(s) = -χ(s) · h(1-s)`.
-/
theorem interiorStripH_functional_equation
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s = -interiorStripFEMultiplier s * interiorStripH (1 - s) := by
  have hσ' := one_sub_re_ne_half hσ
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  have hcf' : so4CriticalFactor (1 - s) ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ'
  have hs := interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ
  have h1s := interiorStripH_eq_zeta_div_critical_on_strip
    (one_sub_re_pos h1) (one_sub_re_lt_one h0) hσ'
  have hζ := riemannZeta_eq_interiorStripFEMultiplier_mul h0 h1
  rw [hs, hζ, h1s, so4CriticalFactor_reflection]
  field_simp [hcf, hcf']

theorem interiorStripH_eq_zero_iff_zeta_eq_zero_on_strip
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s = 0 ↔ riemannZeta s = 0 := by
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  rw [interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ]
  constructor
  · intro h
    rcases (div_eq_zero_iff).1 h with hz | hf
    · exact hz
    · exact absurd hf hcf
  · intro h
    simp [h, zero_div]

/-! ## Completed interior assembly -/

/--
Completed interior readout: multiply `h` by the equator factor to recover `ζ`.
This is the natural "completion" removing the explicit `/ (2σ-1)` denominator.
-/
noncomputable def completedInteriorH (s : ℂ) : ℂ :=
  completedInteriorFromH s

theorem completedInteriorH_eq_zeta_on_strip
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    completedInteriorH s = riemannZeta s :=
  completedInteriorFromH_eq_zeta_on_strip h0 h1 hσ

/--
**Standard ζ functional equation on the completed assembly** (no extra factor needed):
`ζ(s) = χ(s) · ζ(1-s)`.
-/
theorem completedInteriorH_functional_equation
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    completedInteriorH s = interiorStripFEMultiplier s * completedInteriorH (1 - s) := by
  have hσ' := one_sub_re_ne_half hσ
  simp only [completedInteriorH]
  rw [completedInteriorFromH_eq_zeta_on_strip h0 h1 hσ,
    completedInteriorFromH_eq_zeta_on_strip (one_sub_re_pos h1) (one_sub_re_lt_one h0) hσ']
  exact riemannZeta_eq_interiorStripFEMultiplier_mul h0 h1

/--
Assembly form: `h(s)·f(s) = χ(s)·h(1-s)·f(1-s)` with `f = so4CriticalFactor`.
-/
theorem interiorStripH_times_critical_eq_multiplier_mul_reflection
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s * so4CriticalFactor s =
      interiorStripFEMultiplier s * (interiorStripH (1 - s) * so4CriticalFactor (1 - s)) := by
  simpa [completedInteriorH, completedInteriorFromH] using
    completedInteriorH_functional_equation h0 h1 hσ

/--
Relating the two levels: `h(s)·f(s) = χ(s)·h(1-s)·f(1-s)` is equivalent to
`h(s) = -χ(s)·h(1-s)` because `f(1-s) = -f(s)`.
-/
theorem interior_pathA_reflection_links_multiplier_and_h
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s = -interiorStripFEMultiplier s * interiorStripH (1 - s) ∧
      completedInteriorH s = interiorStripFEMultiplier s * completedInteriorH (1 - s) := by
  refine ⟨interiorStripH_functional_equation h0 h1 hσ, ?_⟩
  exact completedInteriorH_functional_equation h0 h1 hσ

/-- Pathway A target: a completed `h`-level object with controlled poles (future). -/
def InteriorPathACompletedHGoal : Prop :=
  ∃ g : ℂ → ℂ,
    (∀ s, 0 < s.re → s.re < 1 → s.re ≠ (1 / 2 : ℝ) →
      g s = interiorStripH s * so4CriticalFactor s) ∧
    (∀ s, 0 < s.re → s.re < 1 → s.re ≠ (1 / 2 : ℝ) →
      g s = interiorStripFEMultiplier s * g (1 - s))

theorem interior_pathA_completed_goal_holds :
    InteriorPathACompletedHGoal :=
  ⟨completedInteriorH,
    fun _s _h0 _h1 _hσ => rfl,
    fun _s h0 h1 hσ => completedInteriorH_functional_equation h0 h1 hσ⟩

end

end Hqiv.Story
