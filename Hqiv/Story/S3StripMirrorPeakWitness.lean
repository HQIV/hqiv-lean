import Hqiv.Story.S3HigherTwiddleFactorizationProbe
import Hqiv.Story.S3InteriorPathA
import Hqiv.Story.S3MirroredTwiddlePair

/-!
# Strip mirror-peaking witnesses and probe false-peak law

This module packages the **OSH ↔ FE/twiddle** mirror-peaking analogy on the strip:

* **Strip mirror peak** — pivot `σ`, FE partner `1-σ`, and a discriminating rotation
  readout (`rotFree θ` vs `rotFree (π/2-θ)`), matching the shape of
  `LogicMirrorPeak` / `peakSupportPair` in `CarrierPeaking`.
* **Probe false peaks** — at a shared Dirichlet numerator, a probe frame assembly
  vanishes exactly when the **probe geometric factor** vanishes, not when `ζ` vanishes.
  Only the main equator-normalized channel tracks `ζ` off `σ = 1/2`.

## Proved here

* `twiddleInteriorFrameAssembly_eq_zero_iff_sum_zero` off the probe locus.
* `probe_frame_zero_iff_geometric_factor_zero` when the frame numerator is nonzero.
* Full-strip analogue for `twiddleInteriorAssembly` with `ζ ≠ 0`.
* Contrast with main capstone: `interiorStripHFrame_eq_zero_iff_sum_zero` and
  `interiorStripH_eq_zero_iff_zeta_eq_zero_on_strip`.
* `StripMirrorPeakWitness`: FE orbit cancellation + optional discriminating flip.
* Plastic probe instance of the false-peak law.

RH discharge remains on the main `interiorStripH` capstone.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## Frame assembly zero characterizations -/

theorem twiddleInteriorFrameAssembly_eq_zero_iff_sum_zero
    (N : ℕ) (ch : TwiddleChannel) (s : ℂ)
    (hloc : onTwiddleProbeOffLocus ch s) (hc : 2 * ch.c - 1 ≠ 0) :
    twiddleInteriorFrameAssembly N ch s = 0 ↔ finiteSpectralFrameSum N s = 0 := by
  unfold twiddleInteriorFrameAssembly
  have hgeo := twiddleGeometricFactor_ne_zero_of_off_locus hloc hc
  constructor
  · intro h0
    rcases (div_eq_zero_iff).1 h0 with hsum | hgeo'
    · exact hsum
    · exact absurd hgeo' hgeo
  · intro hsum
    simp [hsum, zero_div]

theorem interiorStripHFrame_eq_zero_iff_sum_zero
    (N : ℕ) (s : ℂ) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    interiorStripHFrame N s = 0 ↔ finiteSpectralFrameSum N s = 0 := by
  unfold interiorStripHFrame
  have hcf := so4CriticalFactor_ne_zero_off_line hσ
  constructor
  · intro h0
    rcases (div_eq_zero_iff).1 h0 with hsum | hcf'
    · exact hsum
    · exact absurd hcf' hcf
  · intro hsum
    simp [hsum, zero_div]

/--
**Probe false-peak law (frame level).**  With a nonzero shared Dirichlet numerator,
probe assembly vanishes iff the probe geometric factor vanishes — not iff `ζ` vanishes.
-/
theorem probe_frame_zero_iff_geometric_factor_zero
    (N : ℕ) (ch : TwiddleChannel) {s : ℂ} (hnum : finiteSpectralFrameSum N s ≠ 0) :
    twiddleInteriorFrameAssembly N ch s = 0 ↔ twiddleGeometricFactor ch s = 0 := by
  unfold twiddleInteriorFrameAssembly
  constructor
  · intro h0
    by_contra hgeo
    rcases (div_eq_zero_iff).1 h0 with hsum | hgeo'
    · exact hnum hsum
    · exact hgeo hgeo'
  · intro hgeo
    simp [hgeo]

theorem twiddleInteriorAssembly_eq_zero_iff_zeta_zero
    (ch : TwiddleChannel) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ))
    (hloc : onTwiddleProbeOffLocus ch s) (hc : 2 * ch.c - 1 ≠ 0) :
    twiddleInteriorAssembly ch s = 0 ↔ riemannZeta s = 0 := by
  unfold twiddleInteriorAssembly
  have hgeo := twiddleGeometricFactor_ne_zero_of_off_locus hloc hc
  constructor
  · intro h0
    rcases (div_eq_zero_iff).1 h0 with hζ | hgeo'
    · exact hζ
    · exact absurd hgeo' hgeo
  · intro hζ
    simp [hζ, zero_div]

/--
**Probe false-peak law (full strip).**  With `ζ ≠ 0`, probe interior assembly vanishes
iff the probe geometric factor vanishes.
-/
theorem probe_interiorAssembly_zero_iff_geometric_factor_zero
    (ch : TwiddleChannel) {s : ℂ} (hζ : riemannZeta s ≠ 0) :
    twiddleInteriorAssembly ch s = 0 ↔ twiddleGeometricFactor ch s = 0 := by
  unfold twiddleInteriorAssembly
  constructor
  · intro h0
    by_contra hgeo
    rcases (div_eq_zero_iff).1 h0 with hζ' | hgeo'
    · exact hζ hζ'
    · exact hgeo hgeo'
  · intro hgeo
    simp [hgeo]

/--
Probe frame zeros are **not** main-capstone zeros: with a nonzero shared numerator,
the main interior assembly cannot vanish (even when the probe assembly does).
-/
theorem probe_frame_zero_not_main_capstone_zero
    (N : ℕ) (ch : TwiddleChannel) {s : ℂ}
    (hnum : finiteSpectralFrameSum N s ≠ 0) (hσ : s.re ≠ (1 / 2 : ℝ))
    (_hprobe : twiddleInteriorFrameAssembly N ch s = 0) :
    interiorStripHFrame N s ≠ 0 := by
  intro hmain
  exact hnum ((interiorStripHFrame_eq_zero_iff_sum_zero N s hσ).mp hmain)

theorem probe_frame_zero_forces_geometric_factor_zero
    (N : ℕ) (ch : TwiddleChannel) {s : ℂ}
    (hnum : finiteSpectralFrameSum N s ≠ 0)
    (hprobe : twiddleInteriorFrameAssembly N ch s = 0) :
    twiddleGeometricFactor ch s = 0 :=
  (probe_frame_zero_iff_geometric_factor_zero N ch hnum).mp hprobe

/-- Plastic probe instance of the false-peak law. -/
theorem plastic_probe_frame_zero_iff_geometric_factor_zero
    (N : ℕ) {s : ℂ} (hnum : finiteSpectralFrameSum N s ≠ 0) :
    plasticInteriorFrameAssembly N s = 0 ↔ (so4PlasticCubicFree s : ℂ) = 0 := by
  simpa [plasticInteriorFrameAssembly, plasticCubicTwiddle, twiddleGeometricFactor,
    so4PlasticCubicFree] using
    probe_frame_zero_iff_geometric_factor_zero N plasticCubicTwiddle hnum

/-! ## Strip mirror peak (FE orbit readout) -/

/--
Strip-side mirror peak: rotation angle `θ`, pivot `σ`, and whether the mirror pair
**discriminates** at that pivot (`cos θ ≠ sin θ`).
-/
structure StripMirrorPeak where
  θ : ℝ
  σ : ℝ
  flipsDiscriminator : Prop

def stripMirrorPeak (θ σ : ℝ) : StripMirrorPeak :=
  { θ := θ, σ := σ, flipsDiscriminator := Real.cos θ ≠ Real.sin θ }

/-- Mirror-pair difference at the pivot (constant in `σ`; vanishes only at `θ = π/4`). -/
def stripMirrorPeakDiscriminator (peak : StripMirrorPeak) : ℝ :=
  rotFree peak.θ (functionalPair peak.σ) -
    rotFree (Real.pi / 2 - peak.θ) (functionalPair peak.σ)

theorem stripMirrorPeakDiscriminator_eq (peak : StripMirrorPeak) :
    stripMirrorPeakDiscriminator peak = Real.cos peak.θ - Real.sin peak.θ := by
  simpa [stripMirrorPeakDiscriminator] using rotFree_mirror_pair_diff peak.θ peak.σ

def stripMirrorPeakFlips (peak : StripMirrorPeak) : Bool :=
  stripMirrorPeakDiscriminator peak ≠ 0

theorem stripMirrorPeakFlips_iff_discriminator (peak : StripMirrorPeak) :
    stripMirrorPeakFlips peak = true ↔ stripMirrorPeakDiscriminator peak ≠ 0 := by
  unfold stripMirrorPeakFlips
  exact decide_eq_true_iff

theorem stripMirrorPeak_flips_iff_angle (θ σ : ℝ) :
    stripMirrorPeakFlips (stripMirrorPeak θ σ) = true ↔ Real.cos θ ≠ Real.sin θ := by
  simp [stripMirrorPeak, stripMirrorPeakFlips_iff_discriminator,
    stripMirrorPeakDiscriminator_eq, sub_ne_zero, rotFree_mirror_pair_diff_zero_iff]

theorem stripMirrorPeak_flips_of_angle (θ σ : ℝ) (h : Real.cos θ ≠ Real.sin θ) :
    stripMirrorPeakFlips (stripMirrorPeak θ σ) = true := by
  rwa [stripMirrorPeak_flips_iff_angle]

/-- Decidable strip mirror witness (analogue of `peakQubitFlipWitness`). -/
def stripMirrorPeakWitness (peak : StripMirrorPeak) : Option ℝ :=
  if stripMirrorPeakFlips peak then
    some (stripMirrorPeakDiscriminator peak)
  else
    none

theorem stripMirrorPeakWitness_some_iff (peak : StripMirrorPeak) :
    (stripMirrorPeakWitness peak).isSome ↔ stripMirrorPeakFlips peak = true := by
  unfold stripMirrorPeakWitness stripMirrorPeakFlips
  by_cases h : stripMirrorPeakDiscriminator peak ≠ 0 <;> simp [h]

theorem stripMirrorPeakWitness_some_iff_discriminator
    (peak : StripMirrorPeak) :
    (stripMirrorPeakWitness peak).isSome ↔ stripMirrorPeakDiscriminator peak ≠ 0 := by
  rw [stripMirrorPeakWitness_some_iff, stripMirrorPeakFlips_iff_discriminator]

/--
Certified strip mirror witness: FE orbit cancellation holds, and the pair
discriminates at the pivot.
-/
structure StripMirrorPeakWitness extends StripMirrorPeak where
  hflip : stripMirrorPeakDiscriminator toStripMirrorPeak ≠ 0
  hcancel :
    rotFree θ (functionalPair σ) +
      rotFree (Real.pi / 2 - θ) (functionalPair (1 - σ)) = 0

def StripMirrorPeakWitness.ofAngle (θ σ : ℝ) (h : Real.cos θ ≠ Real.sin θ) :
    StripMirrorPeakWitness :=
  { toStripMirrorPeak := stripMirrorPeak θ σ
    , hflip := by
        rw [stripMirrorPeakDiscriminator_eq]
        exact sub_ne_zero.mpr h
    , hcancel := rotFree_mirror_pair_sum θ σ }

theorem StripMirrorPeakWitness.witness_some (w : StripMirrorPeakWitness) :
    (stripMirrorPeakWitness w.toStripMirrorPeak).isSome := by
  rw [stripMirrorPeakWitness_some_iff_discriminator]
  exact w.hflip

theorem StripMirrorPeakWitness.discriminator_ne_zero (w : StripMirrorPeakWitness) :
    stripMirrorPeakDiscriminator w.toStripMirrorPeak ≠ 0 :=
  w.hflip

/--
On the critical line the paired sum collapses; off-line discrimination is carried
by `stripMirrorPeakDiscriminator` (vanishes only at `θ = π/4`).
-/
theorem stripMirrorPeak_sum_at_half (peak : StripMirrorPeak) :
    rotFree peak.θ (functionalPair (1 / 2)) +
      rotFree (Real.pi / 2 - peak.θ) (functionalPair (1 / 2)) = 0 := by
  rw [rotFree_mirror_pair_sum_same_pair peak.θ (1 / 2)]
  ring

/-! ## Packaging -/

/--
**False-peak law:** probe assemblies detect probe geometric-factor zeros; main
assemblies track `ζ` off the equator.
-/
structure ProbeFalsePeakLaw (N : ℕ) (ch : TwiddleChannel) : Prop where
  zero_iff_geometric :
    ∀ {s}, finiteSpectralFrameSum N s ≠ 0 →
      (twiddleInteriorFrameAssembly N ch s = 0 ↔ twiddleGeometricFactor ch s = 0)
  not_main_capstone :
    ∀ {s}, finiteSpectralFrameSum N s ≠ 0 → s.re ≠ (1 / 2 : ℝ) →
      twiddleInteriorFrameAssembly N ch s = 0 → interiorStripHFrame N s ≠ 0
  main_tracks_zeta :
    ∀ {s}, 0 < s.re → s.re < 1 → s.re ≠ (1 / 2 : ℝ) →
      (interiorStripHFrame N s = 0 ↔ finiteSpectralFrameSum N s = 0)

theorem probe_false_peak_law (N : ℕ) (ch : TwiddleChannel) : ProbeFalsePeakLaw N ch where
  zero_iff_geometric := fun {s} hnum =>
    probe_frame_zero_iff_geometric_factor_zero N ch hnum
  not_main_capstone :=
    fun {s} hnum hσ hprobe => probe_frame_zero_not_main_capstone_zero N ch hnum hσ hprobe
  main_tracks_zeta := fun {s} _ _ hσ => interiorStripHFrame_eq_zero_iff_sum_zero N s hσ

structure StripMirrorPeakFormalizationStatus : Prop where
  fe_orbit_cancellation :
    ∀ (θ σ : ℝ),
      rotFree θ (functionalPair σ) +
        rotFree (Real.pi / 2 - θ) (functionalPair (1 - σ)) = 0
  witness_some :
    ∀ (w : StripMirrorPeakWitness), (stripMirrorPeakWitness w.toStripMirrorPeak).isSome
  plastic_false_peak :
    ∀ (N : ℕ) {s}, finiteSpectralFrameSum N s ≠ 0 →
      (plasticInteriorFrameAssembly N s = 0 ↔ (so4PlasticCubicFree s : ℂ) = 0)

theorem strip_mirror_peak_formalization_status : StripMirrorPeakFormalizationStatus where
  fe_orbit_cancellation := fun θ σ => rotFree_mirror_pair_sum θ σ
  witness_some := fun w => StripMirrorPeakWitness.witness_some w
  plastic_false_peak := fun N {s} hnum =>
    plastic_probe_frame_zero_iff_geometric_factor_zero N hnum

end

end Hqiv.Story
