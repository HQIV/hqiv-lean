import Hqiv.Story.S3SO4InteriorWitness
import Hqiv.Story.S3ZetaAxisRotationProjection

/-!
# Explicit `interiorStripH` on the open strip

The RH capstone asks for nonvanishing of

`interiorStripH s = (evenStripChannel s + oddStripChannel s) / so4CriticalFactor s`

at nontrivial zeros off `Re s = 1/2`.  On the open strip the even channel is still
the degenerate placeholder, so the assembly collapses to the explicit quotient

`h(s) = ζ(s) / so4CriticalFactor(s) = ζ(s) · √2 / (2σ − 1)`.

The functional-equation reflection `s ↦ 1 − s` flips the critical factor:
`so4CriticalFactor (1 − s) = −so4CriticalFactor s`.  Substituting the proved
sin/cos–Γ–π strip closed form yields the full FE expression for `h` before the
quotient — the regional "weird" poles and zeros are then visible in `h` itself,
and the capstone is exactly the statement that those singularities do not produce
off-line zeros of `ζ`.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## Critical factor symmetry under `s ↦ 1 − s` -/

theorem functionalPair_one_sub_re (s : ℂ) :
    functionalPair (1 - s).re = (1 - s.re, s.re) := by
  simp [functionalPair, sub_re, one_re]

theorem so4CriticalFactor_one_sub (s : ℂ) :
    so4CriticalFactor (1 - s) = -so4CriticalFactor s := by
  simp only [so4CriticalFactor, exactTwiddleReadout, rot45Free_functionalPair, sub_re, one_re]
  push_cast
  ring

/-! ## Explicit quotient on the open strip -/

theorem interiorStripH_eq_zeta_div_critical_on_strip
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s = riemannZeta s / so4CriticalFactor s :=
  interiorStripH_eq_zeta_div_critical_off_line h0 h1 hσ evenOddSO4Assembly_of_odd_channel

theorem interiorStripH_eq_zeta_times_sqrt2_div_equator
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s =
      riemannZeta s * ((Real.sqrt 2 / (2 * s.re - 1)) : ℂ) := by
  have hdiv := interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  rw [hdiv]
  simp [so4CriticalFactor, exactTwiddleReadout, rot45Free_functionalPair]
  field_simp [hcf]

/-- Odd-channel numerator before normalizing by the equator factor. -/
theorem interiorStripH_eq_odd_channel_div_critical
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s = oddStripChannel s / so4CriticalFactor s := by
  have hnum : evenStripChannel s + oddStripChannel s = oddStripChannel s := by
    simpa [evenStripChannel, oddStripChannel_eq_zeta h0 h1] using
      (evenOddSO4Assembly_of_odd_channel s h0 h1 hσ).symm
  unfold interiorStripH
  rw [hnum]

/--
**Full strip closed form for `h`.**  Expand `oddStripChannel` via the functional
equation assembly; the Γ-poles and sin/cos zeros appear explicitly in the
numerator before division by `(2σ−1)/√2`.
-/
theorem interiorStripH_fe_closed_form
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s =
      (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Gamma (1 - s) * zetaSinCosFactor (1 - s) *
          riemannZeta (1 - s)) / so4CriticalFactor s := by
  rw [interiorStripH_eq_odd_channel_div_critical h0 h1 hσ, oddStripChannel]

/-! ## Reflection product (pathway A seed) -/

theorem one_sub_re_lt_one {s : ℂ} (h0 : 0 < s.re) : (1 - s).re < 1 := by
  simp [sub_re, one_re]
  linarith

theorem one_sub_re_pos {s : ℂ} (h1 : s.re < 1) : 0 < (1 - s).re := by
  simp [sub_re, one_re]
  linarith

theorem one_sub_re_ne_half {s : ℂ} (hσ : s.re ≠ (1 / 2 : ℝ)) : (1 - s).re ≠ (1 / 2 : ℝ) := by
  simp [sub_re, one_re]
  intro h
  apply hσ
  linarith

theorem interiorStripH_mul_at_reflection
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s * interiorStripH (1 - s) =
      -riemannZeta s * riemannZeta (1 - s) / (so4CriticalFactor s ^ 2) := by
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  have hs := interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ
  have h1s := interiorStripH_eq_zeta_div_critical_on_strip
    (one_sub_re_pos h1) (one_sub_re_lt_one h0) (one_sub_re_ne_half hσ)
  rw [hs, h1s, so4CriticalFactor_one_sub]
  field_simp [hcf]

/-! ## Capstone packaging (RH-equivalent) -/

/-- The interior capstone named explicitly for `interiorStripH`. -/
abbrev InteriorStripHNonvanishingCapstone : Prop :=
  InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH

theorem interior_capstone_iff_RiemannHypothesis :
    InteriorStripHNonvanishingCapstone ↔ RiemannHypothesis :=
  ⟨RiemannHypothesis_of_SO4_interior_witness,
    fun hRH s _hzz hσ =>
      absurd (hRH s _hzz.1 _hzz.2.1 _hzz.2.2) hσ⟩

/--
**Candidate completed interior readout** (packaging for pathway A).

Multiply `h` by the equator factor to recover `ζ` on the strip; the completion
inserts the diagonal `1/√2` slot as the even carrier.
-/
noncomputable def completedInteriorFromH (s : ℂ) : ℂ :=
  interiorStripH s * so4CriticalFactor s

theorem completedInteriorFromH_eq_zeta_on_strip
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    completedInteriorFromH s = riemannZeta s := by
  unfold completedInteriorFromH
  rw [interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ]
  field_simp [so4CriticalFactor_ne_zero_off_line hσ]

end

end Hqiv.Story
