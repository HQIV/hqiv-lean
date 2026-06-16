import Hqiv.Geometry.ReverseShorClassicalOSHPeriodSelector
import Hqiv.QuantumComputing.CarrierPeaking
import Hqiv.QuantumComputing.SemiprimeOrthogonalDiagonalQuantum
import Hqiv.Story.S3SemiprimeExplicitFormulaMediation
import Hqiv.Story.S3StripMirrorPeakWitness

/-!
# Semiprime-typed carrier scaffold (QC ↔ explicit-formula mediation)

This module packages the hybrid architecture discussed for certified sparse simulation:

* evolve on an explicit `SuperpositionCarrier` (support list, not full `(L+1)²`);
* type readout weights to **semiprime** indices (spectral leg);
* run **Λ-side canaries** on **prime squares only** (explicit-formula leg);
* accept **mirror peaks** only when pivot and mirror labels both lie in support.

The prime-side collapse (`explicitFormulaWeightPair_eq_prime_square_sum`) is imported
from `S3SemiprimeExplicitFormulaMediation`; local mass canaries come from
`CarrierPeaking`.  Mirror peaking links to `ReverseShorClassicalOSHPeriodSelector`.

## Honest scope

This scaffold does **not** replace an `n`-qubit `2^n` Hilbert-space embedding for
general circuits.  It formalizes the **certified carrier path**: sparse support,
semiprime-typed weights, prime-square Λ canaries, and logic-mirror witnesses.
Dense `applyGateSparse` rebuild remains the reference oracle off the certified class.
-/

namespace Hqiv.QuantumComputing

open Hqiv.Story
open Hqiv.Geometry.ReverseShorClassicalOSHPeriodSelector
open Hqiv.QuantumComputing.SemiprimeOrthogonalDiagonalQuantum
open ArithmeticFunction

noncomputable section

/-! ## Frame levels -/

/-- Harmonic flat frame: `(L+1)²` slots (`sparseBasisCard`). -/
def carrierHarmonicFrameLevel (L : ℕ) : ℕ :=
  sparseBasisCard L

theorem carrierHarmonicFrameLevel_eq (L : ℕ) :
    carrierHarmonicFrameLevel L = (L + 1) * (L + 1) := by
  simp [carrierHarmonicFrameLevel, sparseBasisCard, pow_two]

theorem carrierHarmonicFrameLevel_pos (L : ℕ) : 0 < carrierHarmonicFrameLevel L := by
  simp [carrierHarmonicFrameLevel, sparseBasisCard]

/--
Lineal-basis embedding proxy from the carrier benchmarks: cutoff `L ≈ ⌊√(2^n)⌋`
while support may remain tiny (e.g. two kets for the Shor micro-oracle).
-/
def embeddedLinealCutoff (n : ℕ) : ℕ :=
  Nat.sqrt (2 ^ n)

theorem embeddedLinealCutoff_le_frame (n : ℕ) :
    embeddedLinealCutoff n ≤ carrierHarmonicFrameLevel (embeddedLinealCutoff n) := by
  dsimp only [embeddedLinealCutoff, carrierHarmonicFrameLevel, sparseBasisCard]
  have hle : ∀ L : ℕ, L ≤ (L + 1) ^ 2 := fun L => by
    rw [pow_two]
    nlinarith [Nat.le_add_left L (L + 1), Nat.le_add_right L 1, Nat.le_add_right 1 L]
  exact hle (Nat.sqrt (2 ^ n))

/-- Default arithmetic truncation for typed carriers: harmonic frame `(L+1)²`. -/
def carrierDefaultFrameLevel (L : ℕ) : ℕ :=
  carrierHarmonicFrameLevel L

theorem carrierDefaultFrameLevel_eq_harmonic (L : ℕ) :
    carrierDefaultFrameLevel L = carrierHarmonicFrameLevel L := rfl

theorem carrierDefaultFrameLevel_eq (L : ℕ) :
    carrierDefaultFrameLevel L = (L + 1) * (L + 1) := by
  simp [carrierDefaultFrameLevel, carrierHarmonicFrameLevel_eq]

/-! ## Typed carrier bundle -/

/--
A **semiprime-typed carrier**: explicit harmonic support plus a real readout weight
vanishing off semiprime indices (spectral typing).
-/
structure SemiprimeTypedCarrier (L : ℕ) where
  carrier : SuperpositionCarrier L
  weight : ℕ → ℝ
  typed : SemiprimeSupportedRealWeight weight

/-- Real part of a semiprime-typed complex spectral cross-talk weight. -/
def crossTalkWeightRe (w : ℕ → ℂ) : ℕ → ℝ :=
  fun n => (w n).re

theorem crossTalkWeightRe_typed {w : ℕ → ℂ} (h : SemiprimeSupportedWeight w) :
    SemiprimeSupportedRealWeight (crossTalkWeightRe w) := by
  intro n hnot
  simp [crossTalkWeightRe, h n hnot]

theorem SemiprimeTypedCarrier.complex_weight_supported {L : ℕ} (st : SemiprimeTypedCarrier L) :
    SemiprimeSupportedWeight (fun n => (st.weight n : ℂ)) :=
  (semiprime_supported_real_iff_complex).mp st.typed

/-- Build a typed carrier from an explicit carrier plus semiprime spectral weights. -/
def SemiprimeTypedCarrier.ofCarrier {L : ℕ} (c : SuperpositionCarrier L) (w : ℕ → ℂ)
    (h : SemiprimeSupportedWeight w) : SemiprimeTypedCarrier L :=
  { carrier := c, weight := crossTalkWeightRe w, typed := crossTalkWeightRe_typed h }

/-- Fold a `SparseRegister` through `carrierOfSparse` with induced semiprime weights. -/
def SemiprimeTypedCarrier.ofSparseRegister {L : ℕ} (r : SparseRegister L) (w : ℕ → ℂ)
    (h : SemiprimeSupportedWeight w) : SemiprimeTypedCarrier L :=
  SemiprimeTypedCarrier.ofCarrier (carrierOfSparse r) w h

theorem SemiprimeTypedCarrier.ofSparseRegister_carrier
    {L : ℕ} (r : SparseRegister L) (w : ℕ → ℂ) (h : SemiprimeSupportedWeight w) :
    (SemiprimeTypedCarrier.ofSparseRegister r w h).carrier = carrierOfSparse r := rfl

/-- Spectral cross-talk readout at the default harmonic frame (real part). -/
noncomputable def carrierSpectralCrossTalkAtHarmonicFrame {L : ℕ} (st : SemiprimeTypedCarrier L)
    (s : ℂ) : ℝ :=
  (finiteSpectralCrossTalk (carrierDefaultFrameLevel L)
    (fun n => (st.weight n : ℂ)) s).re

theorem carrierSpectralCrossTalkAtHarmonicFrame_eq_semiprime_sum
    {L : ℕ} (st : SemiprimeTypedCarrier L) (s : ℂ) :
    carrierSpectralCrossTalkAtHarmonicFrame st s =
      (∑ n ∈ (Finset.Icc 1 (carrierDefaultFrameLevel L)).filter (fun n => isSemiprime n),
        (st.weight n : ℂ) * so4SpectralLine n s).re := by
  unfold carrierSpectralCrossTalkAtHarmonicFrame
  rw [finiteSpectralCrossTalk_eq_semiprime_sum (SemiprimeTypedCarrier.complex_weight_supported st)
    (carrierDefaultFrameLevel L) s]

/-- Flat harmonic index for a typed weight slot. -/
def typedWeightAt (L : ℕ) (st : SemiprimeTypedCarrier L) (flat : ℕ) : ℝ :=
  st.weight (wrapIdx L flat)

/-- Λ-side canary: explicit-formula truncation against the typed weight. -/
noncomputable def carrierExplicitCanary {L : ℕ} (N : ℕ) (st : SemiprimeTypedCarrier L) : ℝ :=
  explicitFormulaWeightPair N st.weight

/-- Λ-canary at the default harmonic frame `N = (L+1)²`. -/
noncomputable def carrierExplicitCanaryAtHarmonicFrame {L : ℕ} (st : SemiprimeTypedCarrier L) : ℝ :=
  carrierExplicitCanary (carrierDefaultFrameLevel L) st

theorem carrierExplicitCanaryAtHarmonicFrame_eq
    {L : ℕ} (st : SemiprimeTypedCarrier L) :
    carrierExplicitCanaryAtHarmonicFrame st =
      carrierExplicitCanary (carrierDefaultFrameLevel L) st := rfl

/-- Local mass canary at one flat slot (carrier norm leg, not Λ). -/
def carrierLocalMass (L : ℕ) (st : SemiprimeTypedCarrier L) (flat : ℕ) : ℝ :=
  carrierKetMass st.carrier flat

/-- Logic-mirror peak on the typed carrier support. -/
def typedCarrierMirrorPeak (L : ℕ) (st : SemiprimeTypedCarrier L) (peak : LogicMirrorPeak) : Prop :=
  peakSupportPair st.carrier peak = true

/-! ## Two-tier support law (spectral vs Λ) -/

/--
**Λ-leg collapse.**  Under semiprime typing, the explicit canary sees only prime
squares inside the truncation `N`.
-/
theorem carrierExplicitCanary_eq_prime_square_sum
    {L : ℕ} (N : ℕ) (st : SemiprimeTypedCarrier L) :
    carrierExplicitCanary N st =
      ∑ n ∈ primeSquareIndicesInFrame N, vonMangoldt n * st.weight n := by
  unfold carrierExplicitCanary
  exact explicitFormulaWeightPair_eq_prime_square_sum st.typed N

theorem carrierExplicitCanaryAtHarmonicFrame_eq_prime_square_sum
    {L : ℕ} (st : SemiprimeTypedCarrier L) :
    carrierExplicitCanaryAtHarmonicFrame st =
      ∑ n ∈ primeSquareIndicesInFrame (carrierDefaultFrameLevel L),
        vonMangoldt n * st.weight n :=
  carrierExplicitCanary_eq_prime_square_sum (carrierDefaultFrameLevel L) st

theorem carrierExplicitCanary_eq_zero_of_no_prime_squares
    {L : ℕ} (N : ℕ) (st : SemiprimeTypedCarrier L)
    (hempty : primeSquareIndicesInFrame N = ∅) :
    carrierExplicitCanary N st = 0 := by
  rw [carrierExplicitCanary_eq_prime_square_sum N st, hempty, Finset.sum_empty]

/--
**Quantitative Λ-canary bound** (frame rate `(log N)/√N` after averaging).
-/
theorem carrierExplicitCanary_abs_le
    {L : ℕ} (N : ℕ) (st : SemiprimeTypedCarrier L) (hN1 : 1 ≤ N) (C : ℝ)
    (hC : ∀ n ∈ Finset.Icc 1 N, |st.weight n| ≤ C) (hC0 : 0 ≤ C) :
    |carrierExplicitCanary N st| ≤
      C * (primeSquareIndicesInFrame N).card * Real.log N := by
  unfold carrierExplicitCanary
  exact explicitFormulaWeightPair_abs_le st.typed hN1 C hC hC0

theorem carrierFrameAverageExplicitCanary_abs_le
    {L : ℕ} (st : SemiprimeTypedCarrier L) {N : ℕ} (hN : 2 ≤ N) (C : ℝ)
    (hC : ∀ n ∈ Finset.Icc 1 N, |st.weight n| ≤ C) (hC0 : 0 ≤ C) :
    |carrierExplicitCanary N st / N| ≤
      C * (Nat.sqrt N + 1 : ℝ) * Real.log N / N := by
  unfold carrierExplicitCanary
  simpa using frameAverageExplicitPair_abs_le st.typed hN C hC hC0

/--
Prime and square-free semiprime slots carry no Λ-canary weight (spectral-only on
those indices).
-/
theorem carrierExplicitCanary_kills_prime
    {L : ℕ} (st : SemiprimeTypedCarrier L) {p : ℕ} (hp : Nat.Prime p) :
    vonMangoldt p * st.weight p = 0 :=
  semiprime_mediation_kills_prime_explicit_weight st.typed hp

theorem carrierExplicitCanary_kills_squarefree
    {L : ℕ} (st : SemiprimeTypedCarrier L) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    vonMangoldt (p * q) * st.weight (p * q) = 0 :=
  semiprime_mediation_kills_squarefree_explicit_weight hp hq hne

theorem carrier_prime_square_count_le_sqrt (N : ℕ) :
    (primeSquareIndicesInFrame N).card ≤ Nat.sqrt N + 1 :=
  primeSquareIndicesInFrame_card_le_sqrt N

/-! ## Mirror peak leg -/

/--
Typed carrier with a certified logic-mirror peak (pivot + mirror on support).
-/
structure SemiprimeTypedMirrorCarrier (L : ℕ) extends SemiprimeTypedCarrier L where
  peak : LogicMirrorPeak
  hpeak : peakSupportPair carrier peak = true

theorem SemiprimeTypedMirrorCarrier.peak_witness_some
    {L : ℕ} (st : SemiprimeTypedMirrorCarrier L) :
    (peakQubitFlipWitness st.carrier st.peak).isSome := by
  exact (peakQubitFlipWitness_some_iff st.carrier st.peak).mpr st.hpeak

theorem SemiprimeTypedMirrorCarrier.typed_peak
    {L : ℕ} (st : SemiprimeTypedMirrorCarrier L) :
    typedCarrierMirrorPeak L st.toSemiprimeTypedCarrier st.peak := by
  simpa [typedCarrierMirrorPeak] using st.hpeak

/-- Build a typed mirror carrier from an OSH period/mirror witness plus a typed weight. -/
def SemiprimeTypedMirrorCarrier.ofPeriodWitness
    {L odd : ℕ} (w : PeriodMirrorSupportWitness L odd)
    (weight : ℕ → ℝ) (typed : SemiprimeSupportedRealWeight weight) :
    SemiprimeTypedMirrorCarrier L :=
  { toSemiprimeTypedCarrier := { carrier := w.carrier, weight := weight, typed := typed }
    , peak := w.peak
    , hpeak := w.hpeak }

theorem SemiprimeTypedMirrorCarrier.ofPeriodWitness_peak_witness
    {L odd : ℕ} (w : PeriodMirrorSupportWitness L odd)
    (weight : ℕ → ℝ) (typed : SemiprimeSupportedRealWeight weight) :
    (peakQubitFlipWitness w.carrier w.peak).isSome :=
  SemiprimeTypedMirrorCarrier.peak_witness_some (SemiprimeTypedMirrorCarrier.ofPeriodWitness w weight typed)

/-! ## Certified carrier steps -/

/--
Λ-canaries depend only on the typed weight, not on carrier amplitudes: π-phase
carrier steps leave the explicit canary unchanged.
-/
theorem carrierExplicitCanary_invariant_under_phase
    {L : ℕ} (N : ℕ) (st : SemiprimeTypedCarrier L) (flat : ℕ) :
    carrierExplicitCanary N
        { carrier := applyPhaseCarrier st.carrier flat, weight := st.weight, typed := st.typed } =
      carrierExplicitCanary N st := by
  rfl

/--
Local mass canaries are preserved under certified π-phase (existing `CarrierPeaking`).
-/
theorem carrierLocalMass_invariant_under_phase
    {L : ℕ} (st : SemiprimeTypedCarrier L) (flat phaseFlat : ℕ) :
    carrierLocalMass L
        { carrier := applyPhaseCarrier st.carrier phaseFlat, weight := st.weight, typed := st.typed }
        flat =
      carrierLocalMass L st flat := by
  simp [carrierLocalMass, applyPhaseCarrier_preserves_carrierKetMass]

theorem canarySuite_invariant_under_phase
    {L : ℕ} (st : SemiprimeTypedCarrier L) (probes : List CanaryProbe) (phaseFlat : ℕ)
    (h : carrierCanaryPasses probes st.carrier) :
    carrierCanaryPasses probes (applyPhaseCarrier st.carrier phaseFlat) := by
  intro p hp
  exact (applyPhaseCarrier_preserves_canaryPass st.carrier phaseFlat p).mpr (h p hp)

/--
Apply a certified sparse permutation step; typed weights are unchanged (spectral typing
is index-based, not amplitude-based).
-/
def SemiprimeTypedCarrier.applyPermutation {L : ℕ} (st : SemiprimeTypedCarrier L) (perm : ℕ → ℕ) :
    SemiprimeTypedCarrier L :=
  { carrier := applyPermutationCarrier st.carrier perm, weight := st.weight, typed := st.typed }

theorem carrierExplicitCanary_invariant_under_perm
    {L : ℕ} (N : ℕ) (st : SemiprimeTypedCarrier L) (perm : ℕ → ℕ) :
    carrierExplicitCanary N (st.applyPermutation perm) = carrierExplicitCanary N st := rfl

theorem carrierExplicitCanaryAtHarmonicFrame_invariant_under_perm
    {L : ℕ} (st : SemiprimeTypedCarrier L) (perm : ℕ → ℕ) :
    carrierExplicitCanaryAtHarmonicFrame (st.applyPermutation perm) =
      carrierExplicitCanaryAtHarmonicFrame st :=
  carrierExplicitCanary_invariant_under_perm (carrierDefaultFrameLevel L) st perm

theorem carrierLocalMass_invariant_under_perm
    {L : ℕ} (st : SemiprimeTypedCarrier L) (perm : ℕ → ℕ) (flat : ℕ)
    (hnodup : st.carrier.support.Nodup)
    (hinj : ∀ k₁ k₂, k₁ ∈ st.carrier.support → k₂ ∈ st.carrier.support →
      wrapIdx L (perm k₁) = wrapIdx L (perm k₂) → k₁ = k₂)
    (hk : wrapIdx L flat ∈ st.carrier.support) (hfix : permFixesWrappedFlat L perm flat) :
    carrierLocalMass L (st.applyPermutation perm) flat = carrierLocalMass L st flat := by
  simp [SemiprimeTypedCarrier.applyPermutation, carrierLocalMass]
  exact applyPermutationCarrier_preserves_carrierKetMass st.carrier perm flat hnodup hinj hk hfix

theorem canarySuite_invariant_under_perm
    {L : ℕ} (st : SemiprimeTypedCarrier L) (perm : ℕ → ℕ) (probes : List CanaryProbe)
    (hnodup : st.carrier.support.Nodup)
    (hinj : ∀ k₁ k₂, k₁ ∈ st.carrier.support → k₂ ∈ st.carrier.support →
      wrapIdx L (perm k₁) = wrapIdx L (perm k₂) → k₁ = k₂)
    (hprobe : ∀ p ∈ probes, wrapIdx L p.flat ∈ st.carrier.support)
    (hfix : permutationPreservesCanarySuite L perm probes)
    (h : carrierCanaryPasses probes st.carrier) :
    carrierCanaryPasses probes (st.applyPermutation perm).carrier := by
  exact (applyPermutationCarrier_preserves_carrierCanaryPasses st.carrier perm probes hnodup hinj
    hprobe hfix).mpr h

noncomputable def applyPermutationTypedCarrierSparseStep {L : ℕ} (st : SemiprimeTypedCarrier L)
    (perm : ℕ → ℕ) : SemiprimeTypedCarrier L :=
  st.applyPermutation perm

noncomputable def applyPermutationTypedCarrierSparseStepReg {L : ℕ} (st : SemiprimeTypedCarrier L)
    (perm : ℕ → ℕ) : SparseRegister L :=
  applyPermutationCarrierSparseStepReg perm (sparseOfCarrier st.carrier)

/-! ## Orthogonal-diagonal Shor bridge -/

namespace SemiprimeOrthogonalDiagonalTypedCarrier

/-- Lineal cutoff shared by embedded Shor bookkeeping and typed carriers. -/
def linealHarmonicLevel (n : ℕ) : ℕ :=
  embeddedLinealCutoff n

theorem linealHarmonicLevel_le_frame (n : ℕ) :
    linealHarmonicLevel n ≤ carrierHarmonicFrameLevel (linealHarmonicLevel n) :=
  embeddedLinealCutoff_le_frame n

/--
Orthogonal-diagonal pivot + mirror + work qubit budget identity (bookkeeping layer).
-/
theorem typed_spec_qubit_budget (n : ℕ) :
    orthogonalDiagonalQubitBudget n =
      pivotFlatQubits n + mirrorFlatQubits n + workRegisterQubits n := rfl

theorem pivot_mirror_flats_eq_2L (n : ℕ) :
    pivotFlatQubits n + mirrorFlatQubits n = 2 * shorBitLength n := by
  unfold pivotFlatQubits mirrorFlatQubits shorBitLength
  ring

/--
Bundle: OSH period/mirror witness at the lineal cutoff plus semiprime-typed readout weights.
-/
structure OrthogonalDiagonalTypedSpec (n odd : ℕ) where
  witness : PeriodMirrorSupportWitness (embeddedLinealCutoff n) odd
  weight : ℕ → ℝ
  typed : SemiprimeSupportedRealWeight weight

def toMirrorCarrier {n odd : ℕ} (spec : OrthogonalDiagonalTypedSpec n odd) :
    SemiprimeTypedMirrorCarrier (embeddedLinealCutoff n) :=
  SemiprimeTypedMirrorCarrier.ofPeriodWitness spec.witness spec.weight spec.typed

theorem toMirrorCarrier_peak_witness {n odd : ℕ} (spec : OrthogonalDiagonalTypedSpec n odd) :
    (peakQubitFlipWitness spec.witness.carrier spec.witness.peak).isSome :=
  SemiprimeTypedMirrorCarrier.ofPeriodWitness_peak_witness spec.witness spec.weight spec.typed

theorem toMirrorCarrier_explicit_canary_at_harmonic
    {n odd : ℕ} (spec : OrthogonalDiagonalTypedSpec n odd) :
    carrierExplicitCanaryAtHarmonicFrame (toMirrorCarrier spec).toSemiprimeTypedCarrier =
      carrierExplicitCanary (carrierDefaultFrameLevel (embeddedLinealCutoff n))
        (toMirrorCarrier spec).toSemiprimeTypedCarrier := rfl

end SemiprimeOrthogonalDiagonalTypedCarrier

/-! ## Strip mirror peak bridge (Story ↔ QC bookkeeping) -/

/--
Both mirror-peaking layers use the same witness shape: a decidable `Option` that is
nonempty exactly when a discriminating flip is present — pivot+mirror on carrier
support (QC), or a nonzero rotation mirror discriminant (strip).
-/
theorem carrier_mirror_peak_witness_some_iff {L : ℕ}
    (c : SuperpositionCarrier L) (peak : LogicMirrorPeak) :
    (peakQubitFlipWitness c peak).isSome ↔ peakSupportPair c peak = true :=
  peakQubitFlipWitness_some_iff c peak

theorem strip_mirror_peak_witness_some_iff (peak : StripMirrorPeak) :
    (stripMirrorPeakWitness peak).isSome ↔ stripMirrorPeakDiscriminator peak ≠ 0 :=
  stripMirrorPeakWitness_some_iff_discriminator peak

/-! ## Packaging -/

/--
Two-tier support law for semiprime-typed carriers: Λ-leg on prime squares, mirror
peak on explicit carrier support.
-/
structure SemiprimeTypedCarrierSupportLaw (L N : ℕ) (st : SemiprimeTypedCarrier L) where
  explicit_prime_square :
    carrierExplicitCanary N st =
      ∑ n ∈ primeSquareIndicesInFrame N, vonMangoldt n * st.weight n
  mirror_peak (peak : LogicMirrorPeak) :
    typedCarrierMirrorPeak L st peak ↔ peakSupportPair st.carrier peak = true

theorem semiprimeTypedCarrierSupportLaw (L N : ℕ) (st : SemiprimeTypedCarrier L) :
    SemiprimeTypedCarrierSupportLaw L N st where
  explicit_prime_square := carrierExplicitCanary_eq_prime_square_sum N st
  mirror_peak := fun _ => Iff.rfl

/--
Checklist: which hybrid slots are formally discharged in this scaffold.
-/
structure SemiprimeTypedCarrierFormalizationStatus : Prop where
  explicit_prime_square :
    ∀ (L N : ℕ) (st : SemiprimeTypedCarrier L),
      carrierExplicitCanary N st =
        ∑ n ∈ primeSquareIndicesInFrame N, vonMangoldt n * st.weight n
  harmonic_frame_default :
    ∀ (L : ℕ) (st : SemiprimeTypedCarrier L),
      carrierExplicitCanaryAtHarmonicFrame st =
        ∑ n ∈ primeSquareIndicesInFrame (carrierDefaultFrameLevel L),
          vonMangoldt n * st.weight n
  sparse_register_fold :
    ∀ (L : ℕ) (r : SparseRegister L) (w : ℕ → ℂ) (h : SemiprimeSupportedWeight w),
      (SemiprimeTypedCarrier.ofSparseRegister r w h).carrier = carrierOfSparse r
  lambda_kills_prime :
    ∀ (L : ℕ) (st : SemiprimeTypedCarrier L) (p : ℕ),
      Nat.Prime p → vonMangoldt p * st.weight p = 0
  phase_preserves_local_canary :
    ∀ (L : ℕ) (st : SemiprimeTypedCarrier L) (probes : List CanaryProbe) (phaseFlat : ℕ),
      carrierCanaryPasses probes st.carrier →
        carrierCanaryPasses probes (applyPhaseCarrier st.carrier phaseFlat)
  perm_preserves_local_canary :
    ∀ (L : ℕ) (st : SemiprimeTypedCarrier L) (perm : ℕ → ℕ) (probes : List CanaryProbe),
      st.carrier.support.Nodup →
        (∀ k₁ k₂, k₁ ∈ st.carrier.support → k₂ ∈ st.carrier.support →
          wrapIdx L (perm k₁) = wrapIdx L (perm k₂) → k₁ = k₂) →
        (∀ p ∈ probes, wrapIdx L p.flat ∈ st.carrier.support) →
        permutationPreservesCanarySuite L perm probes →
        carrierCanaryPasses probes st.carrier →
          carrierCanaryPasses probes (st.applyPermutation perm).carrier
  mirror_witness :
    ∀ (L : ℕ) (st : SemiprimeTypedMirrorCarrier L),
      (peakQubitFlipWitness st.carrier st.peak).isSome
  orthogonal_diagonal_budget :
    ∀ n, orthogonalDiagonalQubitBudget n =
      pivotFlatQubits n + mirrorFlatQubits n + workRegisterQubits n
  prime_square_count :
    ∀ N, (primeSquareIndicesInFrame N).card ≤ Nat.sqrt N + 1

theorem semiprime_typed_carrier_formalization_status :
    SemiprimeTypedCarrierFormalizationStatus where
  explicit_prime_square := fun _ _ st => carrierExplicitCanary_eq_prime_square_sum _ st
  harmonic_frame_default := fun _ st => carrierExplicitCanaryAtHarmonicFrame_eq_prime_square_sum st
  sparse_register_fold := fun _ r w h => SemiprimeTypedCarrier.ofSparseRegister_carrier r w h
  lambda_kills_prime := fun L st _p hp => carrierExplicitCanary_kills_prime (L := L) st hp
  phase_preserves_local_canary := fun _ st probes phaseFlat h =>
    canarySuite_invariant_under_phase st probes phaseFlat h
  perm_preserves_local_canary := fun _ st perm probes hnodup hinj hprobe hfix h =>
    canarySuite_invariant_under_perm st perm probes hnodup hinj hprobe hfix h
  mirror_witness := fun _ st => SemiprimeTypedMirrorCarrier.peak_witness_some st
  orthogonal_diagonal_budget := fun n => SemiprimeOrthogonalDiagonalTypedCarrier.typed_spec_qubit_budget n
  prime_square_count := fun N => carrier_prime_square_count_le_sqrt N

end

end Hqiv.QuantumComputing
