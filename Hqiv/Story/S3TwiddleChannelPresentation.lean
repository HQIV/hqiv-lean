import Hqiv.Story.S3HigherTwiddleFactorizationProbe
import Hqiv.Story.S3InteriorStripHClosedForm
import Hqiv.Story.S3SpectralResonanceChanneling
import Hqiv.Story.S3StripMirrorPeakWitness
import Hqiv.Story.S3MirroredTwiddlePair
import Hqiv.Story.S3TwiddleFrameCrossTalkLaw

/-!
# Twiddle channels as a factorization presentation family

Each readout channel packages the same **factorization engine**

`ζ(s) = interior(s) · geometric(s)`,

with a different geometric factor.  The main `45°` equator channel and every
higher-twiddle probe are instances of one schema — the categorical analogue of
choosing different `(P, β_c)` on the same presentation.

## What this module adds

* **`ZetaFactorizationChannel`** — abstract channel (geometric factor, interior
  assembly, off-locus predicate, factorization proof).
* **`mainZetaChannel`** and **`twiddleZetaChannel ch`** — canonical instances.
* **Generic zero dichotomy** — at a zero off locus, either the geometric or the
  interior slot vanishes.
* **`FrameFactorizationChannel`** — finite-frame level `N` with shared Dirichlet
  numerator `∑_{n≤N} n^{−s}`.
* **`TwiddleChannelRegistry`** — main baseline + probe, cross-talk bundle, and
  the frame ratio law in presentation language.
* **Mirrored linear probes** — `c` and `1-c` as paired channels sharing FE
  swap laws.

## Honest scope

Probe channels are **not** zero locators: with `ζ ≠ 0`, probe assembly vanishes
iff the probe geometric factor vanishes (`probe_false_peak`).  RH discharge
remains on the main `interiorStripH` capstone only.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## Off-locus predicates -/

/-- Open strip away from the main critical line. -/
def mainChannelOffLocus (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1 ∧ s.re ≠ (1 / 2 : ℝ)

theorem mainChannelOffLocus_of_twiddle {ch : TwiddleChannel} {s : ℂ}
    (h : onTwiddleProbeOffLocus ch s) : mainChannelOffLocus s := by
  rcases h with ⟨h0, h1, hσ, _, _⟩
  exact ⟨h0, h1, hσ⟩

/-! ## Full-strip ζ factorization channel -/

/-- One channel of the ζ factorization engine. -/
structure ZetaFactorizationChannel where
  geo : ℂ → ℂ
  interior : ℂ → ℂ
  offLocus : ℂ → Prop
  geo_ne_zero : ∀ {s}, offLocus s → geo s ≠ 0
  factorizes : ∀ {s}, offLocus s → riemannZeta s = interior s * geo s

namespace ZetaFactorizationChannel

/-- At an off-locus point, a ζ zero forces one slot to vanish. -/
theorem zero_dichotomy (ch : ZetaFactorizationChannel) {s : ℂ}
    (hloc : ch.offLocus s) (hζ : riemannZeta s = 0) :
    ch.interior s = 0 ∨ ch.geo s = 0 := by
  rw [ch.factorizes hloc] at hζ
  rw [mul_eq_zero] at hζ
  exact hζ

/-- Interior vanishes whenever the geometric slot is nonzero and ζ vanishes. -/
theorem interior_eq_zero_of_geo_ne_zero (ch : ZetaFactorizationChannel) {s : ℂ}
    (hloc : ch.offLocus s) (hgeo : ch.geo s ≠ 0) (hζ : riemannZeta s = 0) :
    ch.interior s = 0 := by
  rcases zero_dichotomy ch hloc hζ with hint | hgeo0
  · exact hint
  · exact absurd hgeo0 hgeo

/-- Geometric slot vanishes whenever interior is nonzero and ζ vanishes. -/
theorem geo_eq_zero_of_interior_ne_zero (ch : ZetaFactorizationChannel) {s : ℂ}
    (hloc : ch.offLocus s) (hint : ch.interior s ≠ 0) (hζ : riemannZeta s = 0) :
    ch.geo s = 0 := by
  rcases zero_dichotomy ch hloc hζ with hint0 | hgeo
  · exact absurd hint0 hint
  · exact hgeo

end ZetaFactorizationChannel

/-! ## Main 45° channel instance -/

/-- Main equator-normalized channel: `ζ = interiorStripH · so4CriticalFactor`. -/
noncomputable def mainZetaChannel : ZetaFactorizationChannel where
  geo := so4CriticalFactor
  interior := interiorStripH
  offLocus := mainChannelOffLocus
  geo_ne_zero := fun hσ => so4CriticalFactor_ne_zero_off_line hσ.2.2
  factorizes := fun hσ =>
    main_channel_factorization_off_line hσ.1 hσ.2.1 hσ.2.2

/-! ## Twiddle probe channel instance -/

/-- Higher-twiddle probe channel: `ζ = twiddleInteriorAssembly ch · free_ch`. -/
noncomputable def twiddleZetaChannel (ch : TwiddleChannel) (hc : 2 * ch.c - 1 ≠ 0) :
    ZetaFactorizationChannel where
  geo := twiddleGeometricFactor ch
  interior := twiddleInteriorAssembly ch
  offLocus := onTwiddleProbeOffLocus ch
  geo_ne_zero := fun hloc => twiddleGeometricFactor_ne_zero_of_off_locus hloc hc
  factorizes := fun {s} (_hloc : onTwiddleProbeOffLocus ch s) =>
    twiddleInteriorAssembly_factorizes ch hc s _hloc

/-- Plastic probe packaged as a `ZetaFactorizationChannel`. -/
noncomputable def plasticZetaChannel : ZetaFactorizationChannel :=
  twiddleZetaChannel plasticCubicTwiddle plasticTwiddle_two_c_minus_one_ne_zero

theorem mainZetaChannel_interior (s : ℂ) : mainZetaChannel.interior s = interiorStripH s := rfl

theorem mainZetaChannel_geo_eq (s : ℂ) : mainZetaChannel.geo s = so4CriticalFactor s := rfl

theorem twiddleZetaChannel_geo (ch : TwiddleChannel) (hc : 2 * ch.c - 1 ≠ 0) (s : ℂ) :
    (twiddleZetaChannel ch hc).geo s = twiddleGeometricFactor ch s := rfl

theorem twiddleZetaChannel_interior (ch : TwiddleChannel) (hc : 2 * ch.c - 1 ≠ 0) (s : ℂ) :
    (twiddleZetaChannel ch hc).interior s = twiddleInteriorAssembly ch s := rfl

/-! ## Frame-level channel (shared Dirichlet numerator) -/

structure FrameFactorizationChannel (N : ℕ) where
  geo : ℂ → ℂ
  interior : ℂ → ℂ
  offLocus : ℂ → Prop
  geo_ne_zero : ∀ {s}, offLocus s → geo s ≠ 0
  factorizes : ∀ {s}, offLocus s → finiteSpectralFrameSum N s = interior s * geo s

namespace FrameFactorizationChannel

theorem zero_dichotomy {N : ℕ} (ch : FrameFactorizationChannel N) {s : ℂ}
    (hloc : ch.offLocus s) (hsum : finiteSpectralFrameSum N s = 0) :
    ch.interior s = 0 ∨ ch.geo s = 0 := by
  rw [ch.factorizes hloc] at hsum
  rw [mul_eq_zero] at hsum
  exact hsum

end FrameFactorizationChannel

noncomputable def mainFrameChannel (N : ℕ) : FrameFactorizationChannel N where
  geo := so4CriticalFactor
  interior := interiorStripHFrame N
  offLocus := mainChannelOffLocus
  geo_ne_zero := fun hσ => so4CriticalFactor_ne_zero_off_line hσ.2.2
  factorizes := fun {s} hσ =>
    main_channel_finite_frame_factorization_off_line N hσ.1 hσ.2.1 hσ.2.2

noncomputable def twiddleFrameChannel (N : ℕ) (ch : TwiddleChannel) (hc : 2 * ch.c - 1 ≠ 0) :
    FrameFactorizationChannel N where
  geo := twiddleGeometricFactor ch
  interior := twiddleInteriorFrameAssembly N ch
  offLocus := onTwiddleProbeOffLocus ch
  geo_ne_zero := fun hloc => twiddleGeometricFactor_ne_zero_of_off_locus hloc hc
  factorizes := fun {s} hloc => twiddleInteriorFrameAssembly_factorizes N ch hc s hloc

/-! ## Channel registry: baseline + probe + cross-talk -/

/--
A **twiddle laboratory** at frame level `N`: main channel, one probe channel,
and optional semiprime-mediated cross-talk data.
-/
structure TwiddleChannelRegistry (N : ℕ) where
  probeCh : TwiddleChannel
  hc : 2 * probeCh.c - 1 ≠ 0
  crossTalk : Option HigherTwiddleCrossTalk

namespace TwiddleChannelRegistry

noncomputable def mainFrame (N : ℕ) : FrameFactorizationChannel N :=
  mainFrameChannel N

noncomputable def probeFrame (reg : TwiddleChannelRegistry N) : FrameFactorizationChannel N :=
  twiddleFrameChannel N reg.probeCh reg.hc

noncomputable def mainZeta : ZetaFactorizationChannel :=
  mainZetaChannel

noncomputable def probeZeta (reg : TwiddleChannelRegistry N) : ZetaFactorizationChannel :=
  twiddleZetaChannel reg.probeCh reg.hc

/-- Frame ratio law in registry language: `h_probe / h_main = geo_main / geo_probe`. -/
theorem frame_interior_ratio (reg : TwiddleChannelRegistry N) {s : ℂ}
    (hσ : s.re ≠ (1 / 2 : ℝ)) (hsum : finiteSpectralFrameSum N s ≠ 0)
    (hloc : onTwiddleProbeOffLocus reg.probeCh s) :
    (probeFrame reg).interior s / (mainFrame N).interior s =
      ((mainFrame N).geo s : ℂ) / (probeFrame reg).geo s := by
  dsimp [mainFrame, probeFrame, mainFrameChannel, twiddleFrameChannel]
  exact twiddleInteriorFrameAssembly_div_interiorStripHFrame N reg.probeCh hσ hsum hloc reg.hc

/-- Full-strip ratio law in registry language. -/
theorem zeta_interior_ratio (reg : TwiddleChannelRegistry N) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) (hζ : riemannZeta s ≠ 0)
    (hloc : onTwiddleProbeOffLocus reg.probeCh s) :
    (probeZeta reg).interior s / mainZeta.interior s =
      (mainZeta.geo s : ℂ) / (probeZeta reg).geo s := by
  dsimp [probeZeta, mainZeta, twiddleZetaChannel, mainZetaChannel]
  exact twiddleInteriorAssembly_div_interiorStripH reg.probeCh h0 h1 hσ hζ hloc reg.hc

/-- **Probe false peak (presentation form).**  With `ζ ≠ 0`, probe interior vanishes
iff probe geometric factor vanishes — not iff `ζ` vanishes. -/
theorem probe_false_peak (reg : TwiddleChannelRegistry N) {s : ℂ}
    (_h0 : 0 < s.re) (_h1 : s.re < 1) (_hσ : s.re ≠ (1 / 2 : ℝ)) (hζ : riemannZeta s ≠ 0)
    (_hloc : onTwiddleProbeOffLocus reg.probeCh s) :
    (probeZeta reg).interior s = 0 ↔ (probeZeta reg).geo s = 0 := by
  dsimp [probeZeta, twiddleZetaChannel]
  exact probe_interiorAssembly_zero_iff_geometric_factor_zero reg.probeCh hζ

theorem probe_false_peak_frame (reg : TwiddleChannelRegistry N) {s : ℂ}
    (hnum : finiteSpectralFrameSum N s ≠ 0) :
    (probeFrame reg).interior s = 0 ↔ (probeFrame reg).geo s = 0 := by
  dsimp [probeFrame, twiddleFrameChannel]
  exact probe_frame_zero_iff_geometric_factor_zero N reg.probeCh hnum

/-- Cross-talk bundle carried by the registry, when present. -/
def crossTalkData (reg : TwiddleChannelRegistry N) (h : reg.crossTalk.isSome) :
    HigherTwiddleCrossTalk :=
  reg.crossTalk.get h

/-- Finite-frame cross-talk term at registry level. -/
noncomputable def registryCrossTalk (reg : TwiddleChannelRegistry N)
    (h : reg.crossTalk.isSome) (s : ℂ) : ℂ :=
  twiddleMainProbeCrossTalk N (crossTalkData reg h) s

theorem registryCrossTalk_eq_main_probe (reg : TwiddleChannelRegistry N)
    (h : reg.crossTalk.isSome) (s : ℂ) :
    registryCrossTalk reg h s =
      twiddleMainProbeCrossTalk N (crossTalkData reg h) s :=
  rfl

theorem registry_crossTalk_support (reg : TwiddleChannelRegistry N)
    (h : reg.crossTalk.isSome) (hmed : (crossTalkData reg h).semiprimeMediated) :
    SemiprimeCrossTalkSupportLaw N (crossTalkData reg h) :=
  semiprimeCrossTalkSupportLaw N (crossTalkData reg h) hmed

/-- Main channel tracks ζ zeros off the critical line (capstone-facing). -/
theorem main_interior_zero_iff_zeta_zero {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    mainZetaChannel.interior s = 0 ↔ riemannZeta s = 0 := by
  rw [mainZetaChannel_interior]
  constructor
  · intro h0int
    have hf := main_channel_factorization_off_line h0 h1 hσ
    rw [h0int, zero_mul] at hf
    exact hf
  · intro hζ
    rw [interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ, hζ, zero_div]

end TwiddleChannelRegistry

/-! ## Semiprime cross-talk carrier and plastic laboratory -/

/-- Unit weight on semiprimes only (zero on primes and higher composites). -/
noncomputable def semiprimeIndicatorWeight : ℕ → ℂ :=
  fun n => if isSemiprime n then 1 else 0

theorem semiprimeIndicatorWeight_supported : SemiprimeSupportedWeight semiprimeIndicatorWeight := by
  intro n hnot
  simp [semiprimeIndicatorWeight, hnot]

/-- Plastic probe with the canonical semiprime indicator cross-talk carrier. -/
noncomputable def plasticSemiprimeCrossTalk : HigherTwiddleCrossTalk where
  probe := plasticCubicTwiddle
  weight := semiprimeIndicatorWeight

theorem plasticSemiprimeCrossTalk_mediated :
    plasticSemiprimeCrossTalk.semiprimeMediated :=
  semiprimeIndicatorWeight_supported

noncomputable def plasticChannelRegistry (N : ℕ) : TwiddleChannelRegistry N where
  probeCh := plasticCubicTwiddle
  hc := plasticTwiddle_two_c_minus_one_ne_zero
  crossTalk := some plasticSemiprimeCrossTalk

theorem plasticChannelRegistry_has_crossTalk (N : ℕ) :
    (plasticChannelRegistry N).crossTalk.isSome := by
  simp [plasticChannelRegistry]

theorem plasticChannelRegistry_crossTalk_support (N : ℕ) :
    SemiprimeCrossTalkSupportLaw N plasticSemiprimeCrossTalk :=
  semiprimeCrossTalkSupportLaw N plasticSemiprimeCrossTalk plasticSemiprimeCrossTalk_mediated

theorem plastic_registry_crossTalk_support (N : ℕ) :
    SemiprimeCrossTalkSupportLaw N
      (TwiddleChannelRegistry.crossTalkData (plasticChannelRegistry N)
        (plasticChannelRegistry_has_crossTalk N)) :=
  TwiddleChannelRegistry.registry_crossTalk_support (plasticChannelRegistry N)
    (plasticChannelRegistry_has_crossTalk N) plasticSemiprimeCrossTalk_mediated

theorem plastic_registry_probe_geo (N : ℕ) (s : ℂ) :
    (TwiddleChannelRegistry.probeZeta (plasticChannelRegistry N)).geo s =
      twiddleGeometricFactor plasticCubicTwiddle s := by
  rfl

/-! ## Mirrored linear pair as two probe channels -/

/-- Linear coefficient channel with normalization `norm`. -/
noncomputable def linearCoefficientChannel (c : ℝ) (_hn : 0 < linearTwiddleNorm c) :
    TwiddleChannel :=
  { c := c, norm := linearTwiddleNorm c }

/-- Mirror partner channel under FE reflection `c ↦ 1-c`. -/
noncomputable def linearMirrorChannel (c : ℝ) (_hn : 0 < linearTwiddleNorm c)
    (_hn' : 0 < linearTwiddleNorm (1 - c)) : TwiddleChannel :=
  linearCoefficientChannel (1 - c) _hn'

theorem linearMirror_zero_locus {c : ℝ} (hc : 2 * c - 1 ≠ 0) (hc' : 2 * (1 - c) - 1 ≠ 0) :
    linearTwiddleZero (1 - c) = 1 - linearTwiddleZero c :=
  linearTwiddleZero_mirror hc hc'

/--
**Presentation naturality (FE swap).**  Mirror channels have zero loci symmetric
about `σ = 1/2`; this is the probe-level avatar of the `α_c` naturality relation.
-/
theorem linear_probe_zero_mirror {c : ℝ} (hc : 2 * c - 1 ≠ 0) (hc' : 2 * (1 - c) - 1 ≠ 0)
    (hn : 0 < linearTwiddleNorm c) (hn' : 0 < linearTwiddleNorm (1 - c)) :
    linearTwiddleZero (linearMirrorChannel c hn hn').c =
      1 - linearTwiddleZero (linearCoefficientChannel c hn).c := by
  dsimp [linearMirrorChannel, linearCoefficientChannel]
  exact linearMirror_zero_locus hc hc'

/-!
A mirrored FE pair `(c, 1-c)` as two probe channels on the same factorization
presentation.  The registry uses the primary coefficient; the mirror partner
is accessed separately.
-/
structure MirrorTwiddleChannelPair where
  c : ℝ
  hc : 2 * c - 1 ≠ 0
  hc' : 2 * (1 - c) - 1 ≠ 0
  hn : 0 < linearTwiddleNorm c
  hn' : 0 < linearTwiddleNorm (1 - c)

namespace MirrorTwiddleChannelPair

noncomputable def primary (pair : MirrorTwiddleChannelPair) : TwiddleChannel :=
  linearCoefficientChannel pair.c pair.hn

noncomputable def mirror (pair : MirrorTwiddleChannelPair) : TwiddleChannel :=
  linearMirrorChannel pair.c pair.hn pair.hn'

theorem primary_c (pair : MirrorTwiddleChannelPair) : pair.primary.c = pair.c := rfl

theorem mirror_c (pair : MirrorTwiddleChannelPair) :
    pair.mirror.c = 1 - pair.c := rfl

theorem zero_loci_mirror (pair : MirrorTwiddleChannelPair) :
    linearTwiddleZero pair.mirror.c = 1 - linearTwiddleZero pair.c :=
  linearMirror_zero_locus pair.hc pair.hc'

noncomputable def primaryZeta (pair : MirrorTwiddleChannelPair) : ZetaFactorizationChannel :=
  twiddleZetaChannel pair.primary pair.hc

noncomputable def mirrorZeta (pair : MirrorTwiddleChannelPair) : ZetaFactorizationChannel :=
  twiddleZetaChannel pair.mirror pair.hc'

end MirrorTwiddleChannelPair

/-- Build a registry from coefficient `c`, using the primary channel as probe. -/
noncomputable def twiddleChannelRegistry_from_mirror_pair
    (pair : MirrorTwiddleChannelPair) (N : ℕ) : TwiddleChannelRegistry N where
  probeCh := pair.primary
  hc := pair.hc
  crossTalk := none

/-- Same, with an explicit semiprime cross-talk weight. -/
noncomputable def twiddleChannelRegistry_from_mirror_pair_with_crossTalk
    (pair : MirrorTwiddleChannelPair) (N : ℕ) (w : ℕ → ℂ)
    (_hw : SemiprimeSupportedWeight w) : TwiddleChannelRegistry N where
  probeCh := pair.primary
  hc := pair.hc
  crossTalk := some { probe := pair.primary, weight := w }

theorem mirror_pair_registry_primary (pair : MirrorTwiddleChannelPair) (N : ℕ) :
    (twiddleChannelRegistry_from_mirror_pair pair N).probeCh = pair.primary := rfl

theorem mirror_pair_registry_with_crossTalk_mediated
    (pair : MirrorTwiddleChannelPair) (N : ℕ) (w : ℕ → ℂ) (hw : SemiprimeSupportedWeight w) :
    (twiddleChannelRegistry_from_mirror_pair_with_crossTalk pair N w hw).crossTalk.isSome := by
  simp [twiddleChannelRegistry_from_mirror_pair_with_crossTalk]

/-- Convenience builder from raw coefficient data. -/
noncomputable def mirrorPair (c : ℝ) (hc : 2 * c - 1 ≠ 0) (hc' : 2 * (1 - c) - 1 ≠ 0)
    (hn : 0 < linearTwiddleNorm c) (hn' : 0 < linearTwiddleNorm (1 - c)) :
    MirrorTwiddleChannelPair :=
  { c := c, hc := hc, hc' := hc', hn := hn, hn' := hn' }

noncomputable def twiddleChannelRegistry_from_coefficient
    (c : ℝ) (hc : 2 * c - 1 ≠ 0) (hc' : 2 * (1 - c) - 1 ≠ 0)
    (hn : 0 < linearTwiddleNorm c) (hn' : 0 < linearTwiddleNorm (1 - c)) (N : ℕ) :
    TwiddleChannelRegistry N :=
  twiddleChannelRegistry_from_mirror_pair (mirrorPair c hc hc' hn hn') N

/-! ## Main-channel zero dichotomy re-exported -/

theorem main_channel_offline_zero_forces_interior
    (_reg : TwiddleChannelRegistry N) {ρ : ℂ}
    (h : IsNontrivialZetaZero ρ) (hσ : ρ.re ≠ (1 / 2 : ℝ)) :
    mainZetaChannel.interior ρ = 0 :=
  offline_zero_forces_assembly_vanish h hσ

theorem twiddle_probe_offline_zero_forces_interior {ch : TwiddleChannel}
    (hc : 2 * ch.c - 1 ≠ 0) {ρ : ℂ}
    (h : IsNontrivialZetaZero ρ) (hσ : ρ.re ≠ (1 / 2 : ℝ))
    (hprobe : ρ.re ≠ linearTwiddleZero ch.c) (hn : ch.norm ≠ 0) :
    (twiddleZetaChannel ch hc).interior ρ = 0 := by
  obtain ⟨h0, h1⟩ := nontrivial_zero_open_strip ρ h
  have hloc : onTwiddleProbeOffLocus ch ρ :=
    ⟨h0, h1, hσ, hprobe, hn⟩
  exact ZetaFactorizationChannel.interior_eq_zero_of_geo_ne_zero (twiddleZetaChannel ch hc) hloc
    (twiddleGeometricFactor_ne_zero_of_off_locus hloc hc) h.1

end

end Hqiv.Story
