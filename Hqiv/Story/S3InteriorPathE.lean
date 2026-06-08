import Hqiv.Story.S3InteriorPathA
import Hqiv.Story.S3HarmonicDeltaEvenOrbit
import Hqiv.Story.S3SO4InteriorWitness
import Hqiv.Story.S3InteriorStripHClosedForm
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Pathway E: non-degenerate even channel (harmonic–Δ split)

The degenerate witness keeps `evenStripChannel := 0` because the proved open-strip
FE already packages all of `ζ` in `oddStripChannel`.

Pathway E **rebalances** the assembly without changing the quotient value:

* **even** — harmonic–Δ multiplier `1 + α/3 = 6/5` against the `π⁴/6` Bernoulli
  sphere slot (`evenBernoulliSector`);
* **odd residual** — `oddStripChannel − even`, so `even + odd_residual = ζ` exactly.

Then `interiorStripH_PathE = (even + odd_residual) / so4CriticalFactor = ζ / factor`,
matching the original `interiorStripH` off `σ ≠ 1/2` while exposing a **nonzero**
even contribution for geometric capstone work.

**Honesty.** Even positivity does not prove the RH capstone: when `ζ(s) = 0` the
residual odd channel is `-even`, so the numerator still vanishes. The capstone
remains `InteriorAssemblyNonzeroAtNontrivialZerosOffLine`; Path E only enriches the
decomposition.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## Harmonic–Δ multiplier -/

/-- Strip readout of HQIV curvature imprint `α` (constant `3/5` from the spine). -/
noncomputable def hqivAlphaStrip (_s : ℂ) : ℝ :=
  Hqiv.alpha

theorem hqivAlphaStrip_eq_three_fifths (s : ℂ) :
    hqivAlphaStrip s = 3 / 5 := by
  unfold hqivAlphaStrip
  exact Hqiv.alpha_eq_3_5

/--
**Harmonic–Δ multiplier** on the third-orbit slot: `1 + α/3 = 6/5`.
Re-exported as a complex strip function for the even channel.
-/
noncomputable def harmonicDeltaMultiplier (_s : ℂ) : ℂ :=
  (harmonicEvenOrbitMultiplier : ℂ)

theorem harmonicDeltaMultiplier_eq_six_fifths (s : ℂ) :
    harmonicDeltaMultiplier s = 6 / 5 := by
  simp [harmonicDeltaMultiplier, harmonicEvenOrbitMultiplier_eq_six_fifths]

theorem harmonicDeltaMultiplier_eq_one_plus_alpha_third (s : ℂ) :
    harmonicDeltaMultiplier s = (1 + hqivAlphaStrip s / 3 : ℂ) := by
  rw [harmonicDeltaMultiplier_eq_six_fifths, hqivAlphaStrip_eq_three_fifths s]
  norm_num

theorem harmonicDeltaMultiplier_ne_zero (s : ℂ) : harmonicDeltaMultiplier s ≠ 0 := by
  rw [harmonicDeltaMultiplier_eq_six_fifths s]
  norm_num

/-! ## Even Bernoulli / π⁴/6 sector -/

/--
Even-sector carrier normalized to the `π⁴/6` equator-half slot
(`so4EquatorHalfArea_eq_pi_four_sixths`).  The `s`-dependence enters through the
external `π^s` factor in `evenStripChannelPathE`.
-/
noncomputable def evenBernoulliSector (_s : ℂ) : ℂ :=
  (so4EquatorHalfArea / (Real.pi ^ 4 / 6) : ℝ)

theorem evenBernoulliSector_eq_one (s : ℂ) :
    evenBernoulliSector s = 1 := by
  simp [evenBernoulliSector, so4EquatorHalfArea_eq_pi_four_sixths]

theorem evenBernoulliSector_ne_zero (s : ℂ) : evenBernoulliSector s ≠ 0 := by
  rw [evenBernoulliSector_eq_one s]
  norm_num

theorem pi_cpow_strip_ne_zero (s : ℂ) :
    (Real.pi : ℂ) ^ s ≠ 0 := by
  rw [Complex.cpow_ne_zero_iff]
  exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)

/-! ## Path E channels -/

/-- Non-degenerate even channel on the open strip. -/
noncomputable def evenStripChannelPathE (s : ℂ) : ℂ :=
  harmonicDeltaMultiplier s * (Real.pi : ℂ) ^ s * evenBernoulliSector s

/--
Odd channel **residual**: proved FE assembly minus the explicit even contribution.
Tautologically arranged so `even + odd_residual = ζ` on the strip.
-/
noncomputable def oddStripChannelPathE (s : ℂ) : ℂ :=
  oddStripChannel s - evenStripChannelPathE s

theorem even_odd_pathE_assembles_to_zeta
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    evenStripChannelPathE s + oddStripChannelPathE s = riemannZeta s := by
  simp [evenStripChannelPathE, oddStripChannelPathE, oddStripChannel_eq_zeta h0 h1]

theorem oddStripChannelPathE_eq_zeta_minus_even
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    oddStripChannelPathE s = riemannZeta s - evenStripChannelPathE s := by
  unfold oddStripChannelPathE
  rw [oddStripChannel_eq_zeta h0 h1]

/-- Full interior `h` with Path E channel split. -/
noncomputable def interiorStripH_PathE (s : ℂ) : ℂ :=
  (evenStripChannelPathE s + oddStripChannelPathE s) / so4CriticalFactor s

theorem interiorStripH_PathE_eq_interiorStripH (s : ℂ) :
    interiorStripH_PathE s = interiorStripH s := by
  unfold interiorStripH_PathE interiorStripH oddStripChannelPathE
  simp [evenStripChannel, add_sub_cancel]

theorem interiorStripH_PathE_eq_zeta_div_critical_on_strip
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripH_PathE s = riemannZeta s / so4CriticalFactor s := by
  rw [interiorStripH_PathE_eq_interiorStripH, interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ]

/-- **Factorization** (same value as the degenerate witness). -/
theorem interiorStripH_PathE_factorization
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    riemannZeta s = interiorStripH_PathE s * so4CriticalFactor s := by
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  rw [interiorStripH_PathE_eq_zeta_div_critical_on_strip h0 h1 hσ]
  field_simp [hcf]

noncomputable def completedInteriorFromH_PathE (s : ℂ) : ℂ :=
  interiorStripH_PathE s * so4CriticalFactor s

theorem completedInteriorFromH_PathE_eq_zeta_on_strip
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    completedInteriorFromH_PathE s = riemannZeta s := by
  unfold completedInteriorFromH_PathE
  rw [interiorStripH_PathE_eq_zeta_div_critical_on_strip h0 h1 hσ]
  field_simp [so4CriticalFactor_ne_zero_off_line hσ]

/-! ## Even-channel non-degeneracy -/

theorem evenStripChannelPathE_ne_zero
    {s : ℂ} (_h0 : 0 < s.re) :
    evenStripChannelPathE s ≠ 0 := by
  unfold evenStripChannelPathE
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact harmonicDeltaMultiplier_ne_zero s
    · exact pi_cpow_strip_ne_zero s
  · exact evenBernoulliSector_ne_zero s

theorem evenStripChannelPathE_eq_six_fifths_pi_pow (s : ℂ) :
    evenStripChannelPathE s = (6 / 5 : ℂ) * (Real.pi : ℂ) ^ s := by
  simp [evenStripChannelPathE, harmonicDeltaMultiplier_eq_six_fifths,
    evenBernoulliSector_eq_one]

/-! ## Capstone equivalence (decomposition only) -/

abbrev InteriorStripHPathENonvanishingCapstone : Prop :=
  InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH_PathE

theorem interior_pathE_capstone_iff_original_capstone :
    InteriorStripHPathENonvanishingCapstone ↔ InteriorStripHNonvanishingCapstone := by
  constructor
  · intro hCap s hZ hσ
    simpa [interiorStripH_PathE_eq_interiorStripH s] using hCap s hZ hσ
  · intro hCap s hZ hσ
    simpa [← interiorStripH_PathE_eq_interiorStripH s] using hCap s hZ hσ

/--
Trivial but honest: off `σ = 1/2`, nonzero `ζ` forces nonzero `h_PathE`
(because `h_PathE = ζ / factor` and `factor ≠ 0`).
-/
theorem interiorStripH_PathE_nonzero_of_zeta_nonzero
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ))
    (hζ : riemannZeta s ≠ 0) :
    interiorStripH_PathE s ≠ 0 := by
  intro h
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  have hdiv := interiorStripH_PathE_eq_zeta_div_critical_on_strip h0 h1 hσ
  rw [hdiv] at h
  rcases (div_eq_zero_iff).1 h with hz | hf
  · exact hζ hz
  · exact absurd hf hcf

/--
At a `ζ`-zero the even and odd Path E channels cancel each other in the numerator:
`odd_residual = −even`.
-/
theorem pathE_channels_cancel_at_zeta_zero
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hζ : riemannZeta s = 0) :
    oddStripChannelPathE s = -evenStripChannelPathE s := by
  calc oddStripChannelPathE s
      = oddStripChannel s - evenStripChannelPathE s := rfl
    _ = riemannZeta s - evenStripChannelPathE s := by rw [oddStripChannel_eq_zeta h0 h1]
    _ = -evenStripChannelPathE s := by rw [hζ, zero_sub]

theorem pathE_numerator_zero_iff_zeta_zero
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    evenStripChannelPathE s + oddStripChannelPathE s = 0 ↔ riemannZeta s = 0 := by
  constructor
  · intro h
    have hAsm := even_odd_pathE_assembles_to_zeta h0 h1
    simpa [hAsm] using h
  · intro hζ
    simpa [hζ] using even_odd_pathE_assembles_to_zeta h0 h1

/-!
## Pathway E status

* Even channel: **non-degenerate** via `6/5 · π^s` (Bernoulli sector normalized).
* `interiorStripH_PathE` **equals** `interiorStripH` on the strip — factorization unchanged.
* Capstone: **RH-equivalent**, unchanged by Path E (`interior_pathE_capstone_iff_original_capstone`).
* New attack surface: even positivity + explicit `-even` odd residual at zeros
  (`pathE_channels_cancel_at_zeta_zero`).
-/

end

end Hqiv.Story
