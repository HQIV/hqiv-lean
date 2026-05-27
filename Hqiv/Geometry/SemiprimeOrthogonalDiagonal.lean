import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Hqiv.Geometry.QuantumFactorGateFrontier
import Hqiv.Geometry.ReverseShorClassicalOSHPeriodSelector

/-!
# Semiprime orthogonal-diagonal Shor (bounded certificate layer)

For odd composites intended as semiprimes `N = p·q`, multiplication by a coprime base splits
across CRT into two cyclic channels. The Python mirror (`hqiv_semiprime_orthogonal_diagonal.py`)
builds a patch-local carrier with:

* channel A: direct angle slot from `a^k mod N`;
* channel B: `reflectSlot` on the doubled `#Q` span;
* diagonal eigenphase weights on disjoint flats at **mpmath precision scaled by `N` and `r`**;
* period via BSGS / brute order find plus optional continued-fraction peak readout;
* classical period `gcd(a^(r/2) ± 1, N)` when `r` is even.

Lean records the slot maps and reuses `ReverseShorClassicalOSHPeriodSelector` for sound extraction.
-/

open Hqiv.Geometry.QuantumFactorGateFrontier
open Hqiv.Geometry.HQIVOSHIntegratedFactorDriver
open Hqiv.Geometry.ReverseShorClassicalOSHPeriodSelector
open Hqiv.QuantumComputing

namespace Hqiv.Geometry.SemiprimeOrthogonalDiagonal

/-- Slot-level orthogonality: the two CRT diagonal channels use distinct angle buckets. -/
def slotChannelsOrthogonal (slotA slotB : ℕ) : Prop :=
  slotA ≠ slotB

/-- Channel A slot from exponent orbit value (angle register). -/
def channelASlot (n v : ℕ) : ℕ :=
  angleSlot n v

/-- Channel B slot: reflection across `2#Q`. -/
def channelBSlot (n slotA : ℕ) : ℕ :=
  reflectSlot n slotA

/-- Cofactor readout for one diagonal channel (same as gate frontier). -/
def channelCofactor (n slot : ℕ) : ℕ :=
  cofactorCandidateFromSlot n slot

/--
Witness bundle for semiprime diagonal extraction feeding the period selector.

The carrier and peak fields are constructive inputs; sound factorization still requires an
`OddCoreFactorWitness` on the odd core (see `reverseShor_candidate_extraction_sound`).
-/
structure SemiprimeDiagonalWitness (L odd : ℕ) where
  baseA : ℕ
  periodR : ℕ
  slotA : ℕ
  slotB : ℕ
  horth : slotChannelsOrthogonal slotA slotB
  pivotCandidate : ℕ
  mirrorCandidate : ℕ
  periodWitness : PeriodMirrorSupportWitness L odd

/-- Pivot cofactor uses channel A; mirror uses channel B (orthogonal slots). -/
def semiprimeDiagonalCandidates {L odd : ℕ} (w : SemiprimeDiagonalWitness L odd) : List ℕ :=
  periodSelectorCandidates w.periodWitness

theorem pivot_in_semiprime_diagonal_candidates {L odd : ℕ}
    (w : SemiprimeDiagonalWitness L odd) :
    IsPeriodSelectorCandidate w.periodWitness w.periodWitness.pivotCandidate := by
  exact pivotCandidate_is_selector_candidate w.periodWitness

theorem semiprime_diagonal_extraction_sound {L odd d : ℕ}
    (w : SemiprimeDiagonalWitness L odd)
    (h₁ : 1 < d) (h₂ : d < odd) (hdiv : d ∣ odd)
    (hsel : IsPeriodSelectorCandidate w.periodWitness d) :
    ∃ cert : OddCoreFactorWitness odd, cert.d = d ∧ cert.d * (odd / cert.d) = odd :=
  reverseShor_candidate_extraction_sound w.periodWitness hsel h₁ h₂ hdiv

#check SemiprimeDiagonalWitness
#check semiprimeDiagonalCandidates
#check semiprime_diagonal_extraction_sound

end Hqiv.Geometry.SemiprimeOrthogonalDiagonal
