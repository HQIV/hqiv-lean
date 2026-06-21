import Hqiv.Story.S3InteriorStripHClosedForm
import Hqiv.Story.S3InteriorPathA
import Hqiv.Story.S3InteriorPathE
import Hqiv.Story.S3SpectralResonanceChanneling
import Hqiv.Story.S3RHZeroSetBridge
import Hqiv.Story.S3TangentOrbitCriticalLine
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Capstone nonvanishing attack: FE numerator audit and zero reduction

The off-line factorization `ζ = h · (2σ−1)/√2` is proved; the open capstone
`InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH` remains RH-equivalent.

This module expands `h = interiorStripH` through the functional-equation assembly,
audits the elementary nonzero factors in the FE multiplier `χ(s)`, and proves the
sharp zero reduction

`h(s) = 0 ↔ ζ(1−s) = 0`

on the open strip off `σ = 1/2` whenever `χ(s) ≠ 0`.  Combined with the quotient
law `h(s) = 0 ↔ ζ(s) = 0`, off-line nontrivial zeros force **FE-paired**
cancellation `ζ(1−ρ) = 0` unconditionally.

**Honesty.** This does not discharge RH: it isolates the exact analytic payload
and packages the capstone as exclusion of off-line nontrivial zeros / FE-paired
collective cancellation.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## FE power base and multiplier audit -/

/-- Positive real base `2 · (2π)` used in the open-strip FE assembly. -/
noncomputable def interiorStripFEPowerBase : ℂ :=
  2 * (2 * (Real.pi : ℂ))

theorem interiorStripFEPowerBase_ne_zero : interiorStripFEPowerBase ≠ 0 := by
  norm_num [interiorStripFEPowerBase]

theorem interiorStripFEPowerBase_eq_def (s : ℂ) :
    interiorStripFEPowerBase ^ (-(1 - s)) =
      (2 * (2 * (Real.pi : ℂ))) ^ (-(1 - s)) := rfl

theorem interiorStrip_fe_power_ne_zero (s : ℂ) :
    interiorStripFEPowerBase ^ (-(1 - s)) ≠ 0 := by
  rw [Complex.cpow_ne_zero_iff]
  exact Or.inl interiorStripFEPowerBase_ne_zero

theorem zetaSinCosFactor_one_sub_eq_proj_cos (s : ℂ) :
    zetaSinCosFactor (1 - s) = cos (Real.pi * (1 - s) / 2) := by
  simp only [zetaSinCosFactor]

theorem zetaSinCosFactor_one_sub_ne_zero_of_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zetaSinCosFactor (1 - s) ≠ 0 := by
  rw [zetaSinCosFactor_one_sub_eq_proj_cos]
  exact proj_cos_ne_zero_of_strip (one_sub_re_pos h1) (one_sub_re_lt_one h0)

theorem Gamma_one_sub_ne_zero_of_strip {s : ℂ} (_h0 : 0 < s.re) (h1 : s.re < 1) :
    Gamma (1 - s) ≠ 0 := by
  refine Complex.Gamma_ne_zero_of_re_pos ?_
  simp [sub_re, one_re]
  linarith

theorem interiorStripFEMultiplier_ne_zero_of_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    interiorStripFEMultiplier s ≠ 0 := by
  unfold interiorStripFEMultiplier
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · rw [Complex.cpow_ne_zero_iff]
        left
        norm_num
    · exact Gamma_one_sub_ne_zero_of_strip h0 h1
  · exact zetaSinCosFactor_one_sub_ne_zero_of_strip h0 h1

/-! ## FE numerator packaging -/

/-- Odd-channel numerator before normalizing by the equator factor. -/
noncomputable def interiorStripOddNumerator (s : ℂ) : ℂ :=
  oddStripChannel s

theorem interiorStripOddNumerator_eq_fe_multiplier_mul_zeta_one_sub
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    interiorStripOddNumerator s = interiorStripFEMultiplier s * riemannZeta (1 - s) := by
  unfold interiorStripOddNumerator
  rw [oddStripChannel_eq_zeta h0 h1]
  exact riemannZeta_eq_interiorStripFEMultiplier_mul h0 h1

theorem interiorStripOddNumerator_eq_h_mul_critical
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripOddNumerator s = interiorStripH s * so4CriticalFactor s := by
  unfold interiorStripOddNumerator
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  rw [interiorStripH_eq_odd_channel_div_critical h0 h1 hσ]
  field_simp [hcf]

theorem interiorStripH_eq_odd_numerator_div_critical
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s = interiorStripOddNumerator s / so4CriticalFactor s := by
  unfold interiorStripOddNumerator
  exact interiorStripH_eq_odd_channel_div_critical h0 h1 hσ

/-! ## Main zero reduction: `h = 0 ↔ ζ(1−s) = 0` -/

theorem interiorStripH_eq_zero_iff_zeta_one_sub_eq_zero_on_strip
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s = 0 ↔ riemannZeta (1 - s) = 0 := by
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  have hχ : interiorStripFEMultiplier s ≠ 0 := interiorStripFEMultiplier_ne_zero_of_strip h0 h1
  rw [interiorStripH_eq_odd_numerator_div_critical h0 h1 hσ,
    interiorStripOddNumerator_eq_fe_multiplier_mul_zeta_one_sub h0 h1]
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hnum | hf
    · rcases mul_eq_zero.mp hnum with hχ0 | hζ1
      · exact absurd hχ0 hχ
      · exact hζ1
    · exact absurd hf hcf
  · intro hζ1
    rw [hζ1, mul_zero, zero_div]

theorem interiorStripH_eq_zero_iff_zeta_eq_zero_and_one_sub
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH s = 0 ↔ riemannZeta s = 0 ∧ riemannZeta (1 - s) = 0 := by
  constructor
  · intro h
    exact ⟨(interiorStripH_eq_zero_iff_zeta_eq_zero_on_strip h0 h1 hσ).mp h,
      (interiorStripH_eq_zero_iff_zeta_one_sub_eq_zero_on_strip h0 h1 hσ).mp h⟩
  · intro ⟨hζ, _⟩
    exact (interiorStripH_eq_zero_iff_zeta_eq_zero_on_strip h0 h1 hσ).mpr hζ

/-! ## Nontrivial-zero corollaries: FE-paired cancellation -/

theorem nontrivial_offline_zero_forces_zeta_one_sub_zero
    {ρ : ℂ} (h : IsNontrivialZetaZero ρ) (hσ : ρ.re ≠ (1 / 2 : ℝ)) :
    riemannZeta (1 - ρ) = 0 := by
  obtain ⟨h0, h1⟩ := nontrivial_zero_open_strip ρ h
  have hz0 := offline_zero_forces_assembly_vanish h hσ
  exact (interiorStripH_eq_zero_iff_zeta_one_sub_eq_zero_on_strip h0 h1 hσ).mp hz0

theorem nontrivial_offline_zero_forces_fe_paired_cancellation
    {ρ : ℂ} (h : IsNontrivialZetaZero ρ) (hσ : ρ.re ≠ (1 / 2 : ℝ)) :
    riemannZeta ρ = 0 ∧ riemannZeta (1 - ρ) = 0 :=
  ⟨h.1, nontrivial_offline_zero_forces_zeta_one_sub_zero h hσ⟩

/-- Off-line nontrivial zeros force FE-paired collective cancellation when `χ ≠ 0`. -/
def OfflineNontrivialZeroForcesFEPairedCancellation : Prop :=
  ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ρ.re ≠ (1 / 2 : ℝ) →
    riemannZeta ρ = 0 ∧ riemannZeta (1 - ρ) = 0

theorem offline_nontrivial_zero_forces_fe_paired_cancellation :
    OfflineNontrivialZeroForcesFEPairedCancellation :=
  fun _ρ h hσ => nontrivial_offline_zero_forces_fe_paired_cancellation h hσ

/-- Capstone as exclusion of off-line FE-paired cancellation at nontrivial zeros. -/
def NoOfflineNontrivialFEPairedCancellation : Prop :=
  ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ρ.re ≠ (1 / 2 : ℝ) → riemannZeta (1 - ρ) ≠ 0

theorem interior_capstone_iff_no_offline_fe_partner_zero :
    InteriorStripHNonvanishingCapstone ↔ NoOfflineNontrivialFEPairedCancellation := by
  constructor
  · intro hCap ρ hzz hσ hζ1
    exact absurd ((interiorStripH_eq_zero_iff_zeta_one_sub_eq_zero_on_strip
      (nontrivial_zero_open_strip ρ hzz).1 (nontrivial_zero_open_strip ρ hzz).2 hσ).mpr hζ1)
      (hCap ρ hzz hσ)
  · intro hNo ρ hzz hσ hh
    exact absurd ((interiorStripH_eq_zero_iff_zeta_one_sub_eq_zero_on_strip
      (nontrivial_zero_open_strip ρ hzz).1 (nontrivial_zero_open_strip ρ hzz).2 hσ).mp hh)
      (hNo ρ hzz hσ)

theorem interior_capstone_iff_no_offline_nontrivial_zeros :
    InteriorStripHNonvanishingCapstone ↔
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ρ.re ≠ (1 / 2 : ℝ) → riemannZeta ρ ≠ 0 := by
  constructor
  · intro hCap ρ hzz hσ hζ
    exact absurd (offline_zero_forces_assembly_vanish hzz hσ) (hCap ρ hzz hσ)
  · intro hNo ρ hzz hσ hh
    exact absurd hzz.1 (hNo ρ hzz hσ)

/-! ## Path E: nondegenerate even channel enriches but does not discharge -/

theorem pathE_even_nonzero_at_every_strip_point
    {s : ℂ} (h0 : 0 < s.re) :
    evenStripChannelPathE s ≠ 0 :=
  evenStripChannelPathE_ne_zero h0

theorem pathE_at_zeta_zero_odd_residual_neg_even
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hζ : riemannZeta s = 0) :
    oddStripChannelPathE s = -evenStripChannelPathE s ∧
      evenStripChannelPathE s ≠ 0 :=
  ⟨pathE_channels_cancel_at_zeta_zero h0 h1 hζ,
    evenStripChannelPathE_ne_zero h0⟩

theorem pathE_numerator_zero_at_zeta_zero
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hζ : riemannZeta s = 0) :
    evenStripChannelPathE s + oddStripChannelPathE s = 0 :=
  (pathE_numerator_zero_iff_zeta_zero h0 h1).mpr hζ

theorem pathE_capstone_iff_original_capstone_attack :
    InteriorStripHPathENonvanishingCapstone ↔ InteriorStripHNonvanishingCapstone :=
  interior_pathE_capstone_iff_original_capstone

theorem pathE_does_not_close_capstone_from_even_positivity
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ))
    (hζ : riemannZeta s = 0) :
    evenStripChannelPathE s ≠ 0 ∧
      interiorStripH_PathE s = 0 ∧
      interiorStripH s = 0 := by
  refine ⟨evenStripChannelPathE_ne_zero h0, ?_, ?_⟩
  · rw [interiorStripH_PathE_eq_zeta_div_critical_on_strip h0 h1 hσ, hζ, zero_div]
  · rw [interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ, hζ, zero_div]

/-!
## Status

* FE multiplier `χ(s)` is **nonzero on the entire open strip** (`interiorStripFEMultiplier_ne_zero_of_strip`).
* Off `σ ≠ 1/2`: `h(s) = 0 ↔ ζ(1−s) = 0` and `h(s) = 0 ↔ ζ(s) = 0`.
* Off-line nontrivial zeros force `ζ(1−ρ) = 0` unconditionally.
* Capstone ↔ no off-line FE partner zeros ↔ no off-line nontrivial zeros ↔ RH.
* Path E even sector is nonzero at every strip point but the numerator still vanishes at `ζ`-zeros.
-/

end

end Hqiv.Story
