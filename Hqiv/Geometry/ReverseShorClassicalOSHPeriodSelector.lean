import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Hqiv.Geometry.HQIVOSHIntegratedFactorDriver
import Hqiv.QuantumComputing.CarrierPeaking

/-!
# Reverse Shor / Classical OSH Period Selector

This module states the bounded Lean target for the "work Shor backwards" interpretation.

Instead of claiming a universal classical replacement for Shor, the OSH selector starts with a
patch-local carrier/support geometry that is intended to expose the same period or mirror peaks a
quantum circuit would have made visible. Deterministic flip/prune/peaking bookkeeping then nominates
divisor candidates, and the only theorem-level factoring claim is the sound certificate already used
by the integrated driver: once a nominated candidate, or its `gcd` channel, is a nontrivial divisor of
the odd core, the odd core splits.

So the supported fast class remains the certified structured regime: diagonal, permutation,
local-mix, mirror-oracle, sparse period micro-schedules. Full Shor with arbitrary modular
exponentiation, measurement/reset, controlled swaps, and support densification is deliberately outside
the proved statement here.
-/

open Hqiv.QuantumComputing
open Hqiv.Geometry.HQIVOSHIntegratedFactorDriver

namespace Hqiv.Geometry.ReverseShorClassicalOSHPeriodSelector

/--
A patch-local period/mirror witness: the carrier support contains both a pivot and its mirror, and
the mirror flips the selected target bit. The two candidate fields record the deterministic
angle/ket fallback readouts used by `HQIVOSHIntegratedFactorDriver`.
-/
structure PeriodMirrorSupportWitness (L odd : ℕ) where
  carrier : SuperpositionCarrier L
  peak : LogicMirrorPeak
  pivotCandidate : ℕ
  mirrorCandidate : ℕ
  hpeak : peakSupportPair carrier peak = true
  hpivot : pivotCandidate = ketLinearFallbackCandidate L odd peak.pivot
  hmirror : mirrorCandidate = ketLinearFallbackCandidate L odd (peak.mirror peak.pivot)

/--
The finite candidate channels extracted from an exposed period/mirror witness:
direct pivot, direct mirror, and the corresponding `gcd` readouts against the odd core.
-/
def periodSelectorCandidates {L odd : ℕ} (w : PeriodMirrorSupportWitness L odd) : List ℕ :=
  [w.pivotCandidate, w.mirrorCandidate, Nat.gcd w.pivotCandidate odd, Nat.gcd w.mirrorCandidate odd]

/-- Membership predicate for deterministic reverse-Shor candidate channels. -/
def IsPeriodSelectorCandidate {L odd : ℕ} (w : PeriodMirrorSupportWitness L odd) (d : ℕ) : Prop :=
  d ∈ periodSelectorCandidates w

/-- The exposed support really gives a nonempty carrier peaking witness. -/
theorem periodMirrorSupportWitness_peak_isSome {L odd : ℕ}
    (w : PeriodMirrorSupportWitness L odd) :
    (peakQubitFlipWitness w.carrier w.peak).isSome := by
  exact (peakQubitFlipWitness_some_iff w.carrier w.peak).mpr w.hpeak

/-- Direct pivot readout is one of the deterministic selector candidates. -/
theorem pivotCandidate_is_selector_candidate {L odd : ℕ}
    (w : PeriodMirrorSupportWitness L odd) :
    IsPeriodSelectorCandidate w w.pivotCandidate := by
  simp [IsPeriodSelectorCandidate, periodSelectorCandidates]

/-- Direct mirror readout is one of the deterministic selector candidates. -/
theorem mirrorCandidate_is_selector_candidate {L odd : ℕ}
    (w : PeriodMirrorSupportWitness L odd) :
    IsPeriodSelectorCandidate w w.mirrorCandidate := by
  simp [IsPeriodSelectorCandidate, periodSelectorCandidates]

/-- Pivot `gcd` readout is one of the deterministic selector candidates. -/
theorem pivotGcdCandidate_is_selector_candidate {L odd : ℕ}
    (w : PeriodMirrorSupportWitness L odd) :
    IsPeriodSelectorCandidate w (Nat.gcd w.pivotCandidate odd) := by
  simp [IsPeriodSelectorCandidate, periodSelectorCandidates]

/-- Mirror `gcd` readout is one of the deterministic selector candidates. -/
theorem mirrorGcdCandidate_is_selector_candidate {L odd : ℕ}
    (w : PeriodMirrorSupportWitness L odd) :
    IsPeriodSelectorCandidate w (Nat.gcd w.mirrorCandidate odd) := by
  simp [IsPeriodSelectorCandidate, periodSelectorCandidates]

/--
Bounded theorem target: candidate extraction is sound when the constructed support exposes a
period/mirror witness and the selected deterministic channel is certified as a nontrivial divisor.

The proof intentionally stops at divisibility soundness. It does not assert a universal period-finding
runtime, dense-circuit simulation bound, or arbitrary modular-exponentiation fast path.
-/
theorem reverseShor_candidate_extraction_sound {L odd d : ℕ}
    (w : PeriodMirrorSupportWitness L odd)
    (_hsel : IsPeriodSelectorCandidate w d)
    (h₁ : 1 < d) (h₂ : d < odd) (hdiv : d ∣ odd) :
    ∃ cert : OddCoreFactorWitness odd, cert.d = d ∧ cert.d * (odd / cert.d) = odd := by
  let cert : OddCoreFactorWitness odd := oddCoreWitness_of_hit odd d h₁ h₂ hdiv
  refine ⟨cert, rfl, ?_⟩
  exact cert.reconstructs

/--
GCD-channel specialization: if the pivot candidate has a nontrivial `gcd` with the odd core, that
`gcd` is a sound extracted factor.
-/
theorem reverseShor_pivot_gcd_extraction_sound {L odd : ℕ}
    (w : PeriodMirrorSupportWitness L odd)
    (h₁ : 1 < Nat.gcd w.pivotCandidate odd)
    (h₂ : Nat.gcd w.pivotCandidate odd < odd) :
    ∃ cert : OddCoreFactorWitness odd,
      cert.d = Nat.gcd w.pivotCandidate odd ∧ cert.d * (odd / cert.d) = odd := by
  exact reverseShor_candidate_extraction_sound w
    (pivotGcdCandidate_is_selector_candidate w) h₁ h₂ (Nat.gcd_dvd_right _ _)

/--
GCD-channel specialization for the mirror branch.
-/
theorem reverseShor_mirror_gcd_extraction_sound {L odd : ℕ}
    (w : PeriodMirrorSupportWitness L odd)
    (h₁ : 1 < Nat.gcd w.mirrorCandidate odd)
    (h₂ : Nat.gcd w.mirrorCandidate odd < odd) :
    ∃ cert : OddCoreFactorWitness odd,
      cert.d = Nat.gcd w.mirrorCandidate odd ∧ cert.d * (odd / cert.d) = odd := by
  exact reverseShor_candidate_extraction_sound w
    (mirrorGcdCandidate_is_selector_candidate w) h₁ h₂ (Nat.gcd_dvd_right _ _)

#check PeriodMirrorSupportWitness
#check periodSelectorCandidates
#check periodMirrorSupportWitness_peak_isSome
#check reverseShor_candidate_extraction_sound
#check reverseShor_pivot_gcd_extraction_sound
#check reverseShor_mirror_gcd_extraction_sound

end Hqiv.Geometry.ReverseShorClassicalOSHPeriodSelector
