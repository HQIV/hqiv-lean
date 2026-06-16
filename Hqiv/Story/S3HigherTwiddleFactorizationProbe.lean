import Hqiv.Story.S3CubicPlasticTwiddle
import Hqiv.Story.S3InteriorStripHClosedForm
import Hqiv.Story.S3SpectralResonanceChanneling
import Hqiv.Story.S3TuftNestedFrameTower

/-!
# Higher-twiddle factorization probes

Higher linear/cubic twiddles are **not** zero locators: they form a multi-channel
laboratory for the factorization engine
`ζ(s) = h(s) · geometricReadout(s)`.

This module scaffolds:

* **Per-channel interior assemblies** `twiddleInteriorAssembly` (quotient by a
  twiddle readout, parallel to `interiorStripH`).
* **Patch factorization** off the main critical line and off each probe's
  vertical zero locus.
* **Semiprime-supported spectral cross-talk** between the main `45°` channel and
  higher-twiddle probes (finite frame truncations).
* **Finite-frame interior assemblies** `h_c^{(N)}` and patch factorization at level `N`.
* **Frame visibility** heuristics tying probe loci to the TUFT radius ladder.

## Honest scope

Cross-talk is typed and semiprime support is proved for weights; explicit-formula
mediation and the frame ratio/cross-talk law are in
`S3SemiprimeExplicitFormulaMediation` and `S3TwiddleFrameCrossTalkLaw`.
Probe false peaks and strip mirror witnesses are in `S3StripMirrorPeakWitness`.
No theorem yet forces physical cross-talk to be semiprime-only, and probe channels
do not pin `ζ` zeros.  RH discharge remains on the main `interiorStripH` capstone.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real Finset Hqiv.Geometry

/-! ## Semiprime spectral support -/

/-- Square-free semiprime: product of two primes (allowing `p = q`). -/
def isSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p * q = n

instance (n : ℕ) : Decidable (isSemiprime n) := by
  classical
  dsimp [isSemiprime]
  infer_instance

theorem not_isSemiprime_of_prime {p : ℕ} (hp : Nat.Prime p) : ¬isSemiprime p := by
  rintro ⟨q, r, hq, hr, heq⟩
  by_cases hq1 : q = 1
  · exact Nat.Prime.ne_one hq hq1
  by_cases hr1 : r = 1
  · rw [hr1] at hr
    exact Nat.not_prime_one hr
  · exact (Nat.not_prime_of_mul_eq heq hq1 hr1) hp

/-- Weight is nonzero only on semiprime indices (cross-talk carrier). -/
def SemiprimeSupportedWeight (w : ℕ → ℂ) : Prop :=
  ∀ n, ¬isSemiprime n → w n = 0

theorem semiprime_supported_weight_zero_on_prime {w : ℕ → ℂ}
    (h : SemiprimeSupportedWeight w) {p : ℕ} (hp : Nat.Prime p) :
    w p = 0 :=
  h p (not_isSemiprime_of_prime hp)

/-! ## Twiddle channel = normalized linear readout -/

abbrev TwiddleChannel := CubicTwiddle

/-- Complex lift of a normalized twiddle readout (depends only on `Re s`). -/
noncomputable def twiddleGeometricFactor (ch : TwiddleChannel) (s : ℂ) : ℂ :=
  (so4CubicFree ch s : ℂ)

/-- Interior assembly relative to channel `ch`: `ζ / free_ch`. -/
noncomputable def twiddleInteriorAssembly (ch : TwiddleChannel) (s : ℂ) : ℂ :=
  riemannZeta s / twiddleGeometricFactor ch s

/-- Open strip, away from `σ = 1/2` and away from the probe's vertical zero. -/
def onTwiddleProbeOffLocus (ch : TwiddleChannel) (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1 ∧ s.re ≠ (1 / 2 : ℝ) ∧
    s.re ≠ linearTwiddleZero ch.c ∧ ch.norm ≠ 0

theorem twiddleGeometricFactor_ne_zero_of_off_locus
    {ch : TwiddleChannel} {s : ℂ} (h : onTwiddleProbeOffLocus ch s)
    (hc : 2 * ch.c - 1 ≠ 0) :
    twiddleGeometricFactor ch s ≠ 0 := by
  rcases h with ⟨h0, h1, hσ, hprobe, hn⟩
  intro h0cast
  unfold twiddleGeometricFactor at h0cast
  have hfree : so4CubicFree ch s = 0 := by
    simpa using h0cast
  exact hprobe ((so4CubicFree_zero_iff hc hn).mp hfree)

/-! ## Patch factorization per channel -/

/-- Pointwise factorization `ζ = h · geometricFactor` off the probe locus. -/
def TwiddleChannelFactorizationOffLocus (ch : TwiddleChannel) (h : ℂ → ℂ) : Prop :=
  ∀ s, onTwiddleProbeOffLocus ch s →
    riemannZeta s = h s * twiddleGeometricFactor ch s

theorem twiddleInteriorAssembly_factorizes (ch : TwiddleChannel)
    (hc : 2 * ch.c - 1 ≠ 0) :
    TwiddleChannelFactorizationOffLocus ch (twiddleInteriorAssembly ch) := by
  intro s hloc
  unfold twiddleInteriorAssembly twiddleGeometricFactor
  have hgeo := twiddleGeometricFactor_ne_zero_of_off_locus hloc hc
  calc
    riemannZeta s =
        riemannZeta s / twiddleGeometricFactor ch s * twiddleGeometricFactor ch s := by
      field_simp [hgeo, mul_comm]
    _ = twiddleInteriorAssembly ch s * twiddleGeometricFactor ch s := by
      unfold twiddleInteriorAssembly
      ring_nf

theorem twiddle_channel_factorization_exists (ch : TwiddleChannel)
    (hc : 2 * ch.c - 1 ≠ 0) :
    ∃ h : ℂ → ℂ, TwiddleChannelFactorizationOffLocus ch h :=
  ⟨twiddleInteriorAssembly ch, twiddleInteriorAssembly_factorizes ch hc⟩

/-- Main `45°` channel packaged as the canonical twiddle laboratory baseline. -/
theorem main_channel_factorization_off_line
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    riemannZeta s = interiorStripH s * so4CriticalFactor s := by
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  have hdiv := interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ
  calc
    riemannZeta s = riemannZeta s / so4CriticalFactor s * so4CriticalFactor s := by
      field_simp [hcf]
    _ = interiorStripH s * so4CriticalFactor s := by rw [hdiv, mul_comm]

/-! ## Plastic probe instance -/

noncomputable def plasticInteriorAssembly (s : ℂ) : ℂ :=
  twiddleInteriorAssembly plasticCubicTwiddle s

theorem plasticInteriorAssembly_def (s : ℂ) :
    plasticInteriorAssembly s =
      riemannZeta s / (so4PlasticCubicFree s : ℂ) := by
  unfold plasticInteriorAssembly plasticCubicTwiddle twiddleInteriorAssembly
    twiddleGeometricFactor so4PlasticCubicFree
  rfl

theorem plastic_patch_factorization_off_locus
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ))
    (hprobe : s.re ≠ plasticTwiddleZero) :
    riemannZeta s =
      plasticInteriorAssembly s * (so4PlasticCubicFree s : ℂ) := by
  have hc := plasticTwiddle_two_c_minus_one_ne_zero
  have hloc : onTwiddleProbeOffLocus plasticCubicTwiddle s := by
    refine ⟨h0, h1, hσ, ?_, ne_of_gt plasticTwiddleNorm_pos⟩
    simpa [plasticTwiddleZero] using hprobe
  exact twiddleInteriorAssembly_factorizes plasticCubicTwiddle hc s hloc

/-! ## Finite-frame semiprime cross-talk -/

/-- Finite spectral cross-talk term at frame level `N`. -/
noncomputable def finiteSpectralCrossTalk (N : ℕ) (w : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, w n * so4SpectralLine n s

theorem semiprime_weight_kills_prime_spectral_line
    {w : ℕ → ℂ} (h : SemiprimeSupportedWeight w) (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    w p * so4SpectralLine p s = 0 := by
  rw [semiprime_supported_weight_zero_on_prime h hp, zero_mul]

structure HigherTwiddleCrossTalk where
  probe : TwiddleChannel
  weight : ℕ → ℂ

def HigherTwiddleCrossTalk.semiprimeMediated (ct : HigherTwiddleCrossTalk) : Prop :=
  SemiprimeSupportedWeight ct.weight

noncomputable def HigherTwiddleCrossTalk.finiteLeakage
    (ct : HigherTwiddleCrossTalk) (N : ℕ) (s : ℂ) : ℂ :=
  finiteSpectralCrossTalk N ct.weight s

/-- On the critical line, main geometric factor vanishes; cross-talk stays in the
spectral sum (no division by `so4CriticalFactor`). -/
noncomputable def criticalLineFiniteLeakage (w : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  finiteSpectralCrossTalk N w s

theorem critical_line_leakage_prime_term_zero
    {w : ℕ → ℂ} (h : SemiprimeSupportedWeight w) (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    w p * so4SpectralLine p s = 0 :=
  semiprime_weight_kills_prime_spectral_line h p hp s

/-! ## Frame visibility (probe locus vs harmonic ladder) -/

/-- Probe index is visible in frame `N` when the tower radius equals `H_N`
(only possible on the critical line — `frame_radius_eq_harmonic_iff`). -/
def twiddleProbeOnFrameHarmonicRadius (N : ℕ) (σ_probe : ℝ) (s : ℂ) : Prop :=
  s.re = σ_probe ∧ spectralFrameNormSq N s = harmonicPartialSum N

theorem twiddle_probe_not_on_harmonic_radius_off_critical_line
    {N : ℕ} (hN : 2 ≤ N) (σ_probe : ℝ) {s : ℂ}
    (hvis : twiddleProbeOnFrameHarmonicRadius N σ_probe s)
    (hprobe : σ_probe ≠ (1 / 2 : ℝ)) :
    False := by
  rcases hvis with ⟨hσ, hradius⟩
  have hcrit := (frame_radius_eq_harmonic_iff hN).mp hradius
  have heqσ : σ_probe = (1 / 2 : ℝ) := by linarith [hσ, hcrit]
  exact hprobe heqσ

/-- Semiprime-mediated plastic cross-talk bundle (hypothesis layer). -/
def PlasticSemiprimeCrossTalk (w : ℕ → ℂ) : Prop :=
  SemiprimeSupportedWeight w ∧
    HigherTwiddleCrossTalk.semiprimeMediated
      { probe := plasticCubicTwiddle, weight := w }

/-! ## Finite-frame interior assemblies `h_c^{(N)}` -/

/-- Level-`N` Dirichlet frame partial sum `∑_{n≤N} n^{−s}`. -/
noncomputable def finiteSpectralFrameSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, so4SpectralLine n s

/-- Main-channel finite-frame interior assembly `h^{(N)}`. -/
noncomputable def interiorStripHFrame (N : ℕ) (s : ℂ) : ℂ :=
  finiteSpectralFrameSum N s / (so4CriticalFactor s : ℂ)

/-- Twiddle-channel finite-frame interior assembly `h_c^{(N)}`. -/
noncomputable def twiddleInteriorFrameAssembly (N : ℕ) (ch : TwiddleChannel) (s : ℂ) : ℂ :=
  finiteSpectralFrameSum N s / twiddleGeometricFactor ch s

/-- Plastic probe finite-frame assembly `h_ρ^{(N)}`. -/
noncomputable def plasticInteriorFrameAssembly (N : ℕ) (s : ℂ) : ℂ :=
  twiddleInteriorFrameAssembly N plasticCubicTwiddle s

theorem plasticInteriorFrameAssembly_def (N : ℕ) (s : ℂ) :
    plasticInteriorFrameAssembly N s =
      finiteSpectralFrameSum N s / (so4PlasticCubicFree s : ℂ) := by
  unfold plasticInteriorFrameAssembly plasticCubicTwiddle twiddleInteriorFrameAssembly
    twiddleGeometricFactor so4PlasticCubicFree
  rfl

/-- Patch factorization at frame level `N`: `∑_{n≤N} n^{−s} = h_c^{(N)} · free_c`. -/
def TwiddleChannelFrameFactorizationOffLocus (N : ℕ) (ch : TwiddleChannel) (h : ℂ → ℂ) : Prop :=
  ∀ s, onTwiddleProbeOffLocus ch s →
    finiteSpectralFrameSum N s = h s * twiddleGeometricFactor ch s

theorem twiddleInteriorFrameAssembly_factorizes (N : ℕ) (ch : TwiddleChannel)
    (hc : 2 * ch.c - 1 ≠ 0) :
    TwiddleChannelFrameFactorizationOffLocus N ch (twiddleInteriorFrameAssembly N ch) := by
  intro s hloc
  unfold twiddleInteriorFrameAssembly twiddleGeometricFactor
  have hgeo := twiddleGeometricFactor_ne_zero_of_off_locus hloc hc
  calc
    finiteSpectralFrameSum N s =
        finiteSpectralFrameSum N s / twiddleGeometricFactor ch s * twiddleGeometricFactor ch s := by
      field_simp [hgeo, mul_comm]
    _ = twiddleInteriorFrameAssembly N ch s * twiddleGeometricFactor ch s := by
      unfold twiddleInteriorFrameAssembly
      ring_nf

theorem twiddle_frame_factorization_exists (N : ℕ) (ch : TwiddleChannel)
    (hc : 2 * ch.c - 1 ≠ 0) :
    ∃ h : ℂ → ℂ, TwiddleChannelFrameFactorizationOffLocus N ch h :=
  ⟨twiddleInteriorFrameAssembly N ch, twiddleInteriorFrameAssembly_factorizes N ch hc⟩

theorem main_channel_finite_frame_factorization_off_line
    (N : ℕ) {s : ℂ} (_h0 : 0 < s.re) (_h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    finiteSpectralFrameSum N s =
      interiorStripHFrame N s * (so4CriticalFactor s : ℂ) := by
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  unfold interiorStripHFrame
  field_simp [hcf, mul_comm]

theorem plastic_finite_frame_factorization_off_locus
    (N : ℕ) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ))
    (hprobe : s.re ≠ plasticTwiddleZero) :
    finiteSpectralFrameSum N s =
      plasticInteriorFrameAssembly N s * (so4PlasticCubicFree s : ℂ) := by
  have hc := plasticTwiddle_two_c_minus_one_ne_zero
  have hloc : onTwiddleProbeOffLocus plasticCubicTwiddle s := by
    refine ⟨h0, h1, hσ, ?_, ne_of_gt plasticTwiddleNorm_pos⟩
    simpa [plasticTwiddleZero] using hprobe
  exact twiddleInteriorFrameAssembly_factorizes N plasticCubicTwiddle hc s hloc

/-- Frame-level semiprime leakage stays in the spectral sum (no division by `free_c`). -/
theorem critical_line_finite_leakage_eq_cross_talk
    (w : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    criticalLineFiniteLeakage w N s = finiteSpectralCrossTalk N w s :=
  rfl

theorem finiteSpectralCrossTalk_eq_semiprime_sum
    {w : ℕ → ℂ} (h : SemiprimeSupportedWeight w) (N : ℕ) (s : ℂ) :
    finiteSpectralCrossTalk N w s =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => isSemiprime n),
        w n * so4SpectralLine n s := by
  unfold finiteSpectralCrossTalk
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro n hn hnot
  have hsemi : ¬isSemiprime n := by
    intro hsemi
    exact hnot (Finset.mem_filter.mpr ⟨hn, hsemi⟩)
  rw [h n hsemi, zero_mul]

/-! ## Frame interior ratio law -/

/-- Shared Dirichlet numerator for every channel at level `N`. -/
theorem frame_assemblies_share_numerator (N : ℕ) (ch : TwiddleChannel) (s : ℂ)
    (hσ : s.re ≠ (1 / 2 : ℝ)) (hloc : onTwiddleProbeOffLocus ch s) (hc : 2 * ch.c - 1 ≠ 0) :
    twiddleInteriorFrameAssembly N ch s * twiddleGeometricFactor ch s =
      interiorStripHFrame N s * (so4CriticalFactor s : ℂ) := by
  unfold twiddleInteriorFrameAssembly interiorStripHFrame
  have hcf := so4CriticalFactor_ne_zero_off_line hσ
  have hgeo := twiddleGeometricFactor_ne_zero_of_off_locus hloc hc
  field_simp [hcf, hgeo]

/--
**Frame ratio law.**  At any level `N`, whenever the shared Dirichlet partial sum is
nonzero, probe and main interior assemblies differ by the geometric-factor ratio:
`h_probe^{(N)} / h_main^{(N)} = so4CriticalFactor / free_probe`.
-/
theorem twiddleInteriorFrameAssembly_div_interiorStripHFrame
    (N : ℕ) (ch : TwiddleChannel) {s : ℂ}
    (hσ : s.re ≠ (1 / 2 : ℝ)) (hsum : finiteSpectralFrameSum N s ≠ 0)
    (hloc : onTwiddleProbeOffLocus ch s) (hc : 2 * ch.c - 1 ≠ 0) :
    twiddleInteriorFrameAssembly N ch s / interiorStripHFrame N s =
      (so4CriticalFactor s : ℂ) / twiddleGeometricFactor ch s := by
  have hcf := so4CriticalFactor_ne_zero_off_line hσ
  have hgeo := twiddleGeometricFactor_ne_zero_of_off_locus hloc hc
  unfold twiddleInteriorFrameAssembly interiorStripHFrame
  field_simp [hsum, hcf, hgeo]

/--
Full-strip ratio law: `h_probe / h_main = so4CriticalFactor / free_probe` off both
loci (same algebraic identity as the frame version, with `ζ`-level assemblies).
-/
theorem twiddleInteriorAssembly_div_interiorStripH
    (ch : TwiddleChannel) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) (hζ : riemannZeta s ≠ 0)
    (hloc : onTwiddleProbeOffLocus ch s) (hc : 2 * ch.c - 1 ≠ 0) :
    twiddleInteriorAssembly ch s / interiorStripH s =
      (so4CriticalFactor s : ℂ) / twiddleGeometricFactor ch s := by
  have hcf := so4CriticalFactor_ne_zero_off_line hσ
  have hgeo := twiddleGeometricFactor_ne_zero_of_off_locus hloc hc
  unfold twiddleInteriorAssembly
  rw [interiorStripH_eq_zeta_div_critical_on_strip h0 h1 hσ]
  field_simp [hζ, hcf, hgeo]

theorem plasticInteriorFrameAssembly_div_interiorStripHFrame
    (N : ℕ) {s : ℂ} (hσ : s.re ≠ (1 / 2 : ℝ)) (hsum : finiteSpectralFrameSum N s ≠ 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hprobe : s.re ≠ plasticTwiddleZero) :
    plasticInteriorFrameAssembly N s / interiorStripHFrame N s =
      (so4CriticalFactor s : ℂ) / (so4PlasticCubicFree s : ℂ) := by
  have hc := plasticTwiddle_two_c_minus_one_ne_zero
  have hloc : onTwiddleProbeOffLocus plasticCubicTwiddle s := by
    refine ⟨h0, h1, hσ, ?_, ne_of_gt plasticTwiddleNorm_pos⟩
    simpa [plasticTwiddleZero] using hprobe
  simpa [plasticInteriorFrameAssembly, plasticCubicTwiddle, twiddleGeometricFactor,
    so4PlasticCubicFree] using
    twiddleInteriorFrameAssembly_div_interiorStripHFrame N plasticCubicTwiddle hσ hsum hloc hc

end

end Hqiv.Story
