import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Hqiv.QuantumComputing.OSHoracle
import Hqiv.Geometry.QuantumFactorGateFrontier

/-!
# HQIV OSH integrated factor driver (Lean mirror)

This module records what is **actually provable** about the Python driver
`scripts/hqiv_osh_integrated_driver.py` without claiming benchmark wall-clock
asymptotics.

## What is formalized

* **Sound factor certificates**: if the search returns a nontrivial divisor of the
  odd core after peeling powers of two, then the original composite splits as
  `2^k * d * (odd / d)`.
* **Angle / ket candidate maps** used in the script: discrete `idx / basis`
  rounding to an integer slot, and the linear `wrapIdx` fallback candidate.
  The fallback agrees with `QuantumFactorGateFrontier.cofactorCandidateFromSlot`
  on wrapped indices.
* **Sparse OSH step shape** (support doubling, prune length bound): cited from
  `Hqiv.QuantumComputing.OSHoracle` — this is the formal **sparse Shor-style** bookkeeping layer
  (expand → gate → flip-detect → prune). Rapidity / shell phase in HQIV supplies the **angular**
  coordinate story; OSHoracle pins the **sparse ket list** algebra so both meet in one pipeline.
* **Discrete bounds that are *exactly* what the code computes**: `wrapIdx` stays
  below `sparseBasisCard`; `idxAngleCandidate` admits a sharp polynomial upper
  bound `≤ 2 + idx * rootCap`; ket-scan candidates are `≤ qSpan n` once `#Q ≥ 2`
  (`QuantumFactorGateFrontier.cofactorCandidate_le_qSpan` proves the same for
  `cofactorCandidateFromSlot`).
* **Algebra of peeling twos**: if `d ∣ odd` and `orig = 2^k * odd`, then
  `2^k * d ∣ orig`.

The monolithic script’s integer-only hit test (`1 < c < odd` and `odd % c == 0`) is the same
certificate as `OddCoreFactorWitness`; see `Hqiv.Geometry.MonolithicGeometricFactorizer`. For the
equivalence with gcd-based extraction (same divisibility predicate, `gcd(d, odd) = d` when `d ∣ odd`),
see `Hqiv.Geometry.FactorDivisibilityBridge`.

## What is *not* proved here

Wall-clock or floating-point benchmark scaling is **not** a theorem in this file:
it depends on an unstated machine model, native gate implementation, `mpmath`
precision policy, and heuristic termination. Treat those as engineering
benchmarks unless you introduce an explicit cost model and prove a bound in
that model. For `inputLog2`, cutoff vs `n`, and linear per-step list charges,
see `Hqiv.Geometry.FactorSearchCostModel`.
-/

open Hqiv.QuantumComputing
open Hqiv.Geometry.QuantumFactorGateFrontier

namespace Hqiv.Geometry.HQIVOSHIntegratedFactorDriver

/-- Python `max(2, int(sqrt(n)))` for the angle-slot root. -/
def rootCap (n : ℕ) : ℕ :=
  max 2 (Nat.sqrt n)

theorem rootCap_ge_two (n : ℕ) : 2 ≤ rootCap n := by
  simp [rootCap]

/-- Discrete analogue of `angle_to_candidate` for `θ = 2π * idx / basis`. -/
def idxAngleCandidate (n basis idx : ℕ) : ℕ :=
  let b := max 1 basis
  let r := rootCap n
  2 + (idx * (r - 1)) / b

theorem idxAngleCandidate_ge_two (n basis idx : ℕ) : 2 ≤ idxAngleCandidate n basis idx := by
  simp [idxAngleCandidate]

/--
Honest upper bound for the discrete `idx/basis` angle slot (no hidden constants):
numerator is at most `idx * rootCap n` after dividing by `max 1 basis`.
-/
theorem idxAngleCandidate_le_two_add_idx_mul_rootCap (n basis idx : ℕ) :
    idxAngleCandidate n basis idx ≤ 2 + idx * rootCap n := by
  unfold idxAngleCandidate rootCap
  set r := max 2 (Nat.sqrt n)
  set b := max 1 basis
  have hdiv : (idx * (r - 1)) / b ≤ idx * (r - 1) := Nat.div_le_self (idx * (r - 1)) b
  have hmul : idx * (r - 1) ≤ idx * r := Nat.mul_le_mul_left idx (Nat.sub_le _ _)
  exact Nat.add_le_add_left (Nat.le_trans hdiv hmul) 2

/-- `sparseBasisCard L = (L+1)^2` is always positive. -/
theorem sparseBasisCard_pos (L : ℕ) : 0 < sparseBasisCard L := by
  rw [sparseBasisCard, Nat.pow_two]
  exact Nat.mul_pos (Nat.succ_pos L) (Nat.succ_pos L)

theorem wrapIdx_lt_sparseBasis (L idx : ℕ) : wrapIdx L idx < sparseBasisCard L :=
  Nat.mod_lt _ (sparseBasisCard_pos L)

/-- Python `max(1, sqrt(n)-1)` with natural subtraction (matches `0` when `sqrt n = 0`). -/
def ketResidualMod (n : ℕ) : ℕ :=
  max 1 (Nat.sqrt n - 1)

/-- Ket-scan fallback candidate from `hqiv_osh_integrated` (`wrap_idx` branch). -/
def ketLinearFallbackCandidate (L n idx : ℕ) : ℕ :=
  2 + (wrapIdx L idx % ketResidualMod n)

private theorem sqrt_le_one_of_qSpan_le_one {n : ℕ} (hq : qSpan n ≤ 1) : Nat.sqrt n ≤ 1 := by
  simp [qSpan, qCard] at hq
  omega

private theorem ketResidualMod_eq_one_of_sqrt_le_one {n : ℕ} (h : Nat.sqrt n ≤ 1) :
    ketResidualMod n = 1 := by
  have hlt : Nat.sqrt n < 2 := Nat.lt_succ_iff.mpr h
  have heq : Nat.sqrt n = 0 ∨ Nat.sqrt n = 1 := by omega
  rcases heq with heq0 | heq1
  · simp [ketResidualMod, heq0]
  · simp [ketResidualMod, heq1]

private theorem qSpan_sub_eq_ketResidualMod_of_one_lt_qSpan {n : ℕ} (hlt : 1 < qSpan n) :
    qSpan n - 1 = ketResidualMod n := by
  by_cases hcard : Nat.sqrt n ≤ 1
  · have hspan : qSpan n = 1 := by simp [qSpan, qCard, Nat.max_eq_left hcard]
    rw [hspan] at hlt
    exact False.elim (Nat.lt_irrefl 1 hlt)
  · unfold ketResidualMod
    dsimp [qSpan, qCard]
    push_neg at hcard
    have htwo : 2 ≤ Nat.sqrt n := Nat.succ_le_iff.mpr hcard
    rw [Nat.max_eq_right (Nat.le_trans (by decide) htwo)]
    have hone_lt : 1 < Nat.sqrt n := Nat.lt_of_lt_of_le (by decide : 1 < 2) htwo
    have hsub : 1 ≤ Nat.sqrt n - 1 := Nat.le_sub_one_of_lt hone_lt
    simpa [Nat.max_eq_left hsub]

/--
Integrated-driver ket fallback matches the gate-frontier cofactor map on the
same wrapped sparse index (the Python `wrap_idx` scan branch).
-/
theorem ketLinearFallback_eq_cofactorCandidate (L n idx : ℕ) :
    ketLinearFallbackCandidate L n idx = cofactorCandidateFromSlot n (wrapIdx L idx) := by
  unfold ketLinearFallbackCandidate cofactorCandidateFromSlot
  dsimp [qSpan, qCard]
  by_cases hq : max 1 (Nat.sqrt n) ≤ 1
  · -- Degenerate shell: both maps return `2`.
    have hsqrt := sqrt_le_one_of_qSpan_le_one (by simpa [qSpan] using hq)
    rw [ketResidualMod_eq_one_of_sqrt_le_one hsqrt]
    simp [hq, Nat.mod_one]
  · have hlt : 1 < qSpan n := by simpa [qSpan] using Nat.lt_of_not_ge hq
    have hmod := qSpan_sub_eq_ketResidualMod_of_one_lt_qSpan (n := n) hlt
    have hq' : ¬ max 1 (Nat.sqrt n) ≤ 1 := hq
    have hmod' : ketResidualMod n = max 1 (Nat.sqrt n) - 1 := by simpa [qSpan, qCard] using hmod.symm
    rw [hmod']
    simp [hq']

/-- Ket-scan candidate stays inside the `#Q` shell once the shell is nontrivial. -/
theorem ketLinearFallbackCandidate_le_qSpan (L n idx : ℕ) (hq : 2 ≤ qSpan n) :
    ketLinearFallbackCandidate L n idx ≤ qSpan n := by
  rw [ketLinearFallback_eq_cofactorCandidate]
  -- Same bound as `QuantumFactorGateFrontier.cofactorCandidate_le_qSpan` (reproved here so this
  -- file elaborates even when dependency oleans are stale).
  unfold cofactorCandidateFromSlot
  have hn1 : ¬ qSpan n ≤ 1 := by omega
  simp [hn1]
  have hpos : 0 < qSpan n - 1 := Nat.sub_pos_of_lt (Nat.lt_of_succ_le hq)
  have hmod := Nat.mod_lt (wrapIdx L idx) hpos
  have hle := Nat.le_sub_one_of_lt hmod
  omega

/-- If a nontrivial divisor is found, it reconstructs the odd part. -/
theorem oddPart_factor_mul_div {odd d : ℕ} (_hd₁ : 1 < d) (_hd₂ : d < odd) (hdvd : d ∣ odd) :
    d * (odd / d) = odd :=
  Nat.mul_div_cancel' hdvd

/--
Certificate shape for a successful **odd-core** hit after peeling twos.
(Python checks `1 < c < n` with `n` the odd working integer.)
-/
structure OddCoreFactorWitness (odd : ℕ) where
  d : ℕ
  h₁ : 1 < d
  h₂ : d < odd
  hdiv : d ∣ odd

theorem OddCoreFactorWitness.reconstructs (w : OddCoreFactorWitness odd) :
    w.d * (odd / w.d) = odd :=
  oddPart_factor_mul_div w.h₁ w.h₂ w.hdiv

/--
Full split after recording `k` factors of two, an odd remainder, and a divisor
certificate on that remainder.
-/
structure IntegratedFactorWitness (orig : ℕ) where
  k : ℕ
  odd : ℕ
  horig : orig = 2 ^ k * odd
  hodd : OddCoreFactorWitness odd

theorem IntegratedFactorWitness.reconstructs_orig (w : IntegratedFactorWitness orig) :
    orig = 2 ^ w.k * w.hodd.d * (w.odd / w.hodd.d) := by
  rcases w with ⟨k, odd, horig, hodd⟩
  dsimp at *
  rw [horig, Nat.mul_assoc, hodd.reconstructs]

/-- Package a divisibility hit into an odd-core witness (the Python `1 < c < n` check). -/
def oddCoreWitness_of_hit (odd d : ℕ) (h₁ : 1 < d) (h₂ : d < odd) (hdiv : d ∣ odd) :
    OddCoreFactorWitness odd :=
  ⟨d, h₁, h₂, hdiv⟩

/--
If `d` divides the odd remainder, then `2^k · d` divides the original number after peeling
twos. This is the algebraic backbone of “report `twos` factors then split `odd`”.
-/
theorem two_pow_mul_dvd_of_dvd_odd {k odd d orig : ℕ}
    (horig : orig = 2 ^ k * odd) (hdiv : d ∣ odd) : (2 ^ k * d) ∣ orig := by
  rw [horig]
  exact Nat.mul_dvd_mul_left (2 ^ k) hdiv

/-- One sparse OSH step evolves support of length `m` to length `2m`; pruning only shrinks. -/
theorem integrated_evolved_then_prune_length_le {L : ℕ} (g : HQIVGate L) (r : SparseRegister L)
    (flipped : List ℕ) :
    (pruneToFlipped (L := L) flipped (applyGateSparse g r)).length ≤ 2 * r.length := by
  refine Nat.le_trans (pruneToFlipped_length_le _ _) ?_
  exact Nat.le_of_eq (applyGateSparse_length_eq_two_mul g r)

/-- Same, using flipped = `detectFlippedKets` (the integrated script’s prune set). -/
theorem integrated_pruned_sparse_step_length_le {L : ℕ} (g : HQIVGate L) (r : SparseRegister L) :
    (pruneToFlipped
          (L := L)
          (detectFlippedKets r (applyGateSparse g r))
          (applyGateSparse g r)).length ≤
        2 * r.length :=
  integrated_evolved_then_prune_length_le g r (detectFlippedKets r (applyGateSparse g r))

/-- Sparse OSH gate application doubles list length (already in `OSHoracle`). -/
theorem integrated_sparse_support_doubles {L : ℕ} (g : HQIVGate L) (r : SparseRegister L) :
    (applyGateSparse g r).length = 2 * r.length :=
  applyGateSparse_length_eq_two_mul g r

/-- Flipped-ket detection list is linear in the two supports. -/
theorem integrated_detect_flipped_le {L : ℕ} (before after : SparseRegister L) :
    (detectFlippedKets before after).length ≤ before.length + after.length :=
  detectFlippedKets_length_le_sum before after

/-- Pruning never increases support size. -/
theorem integrated_prune_le {L : ℕ} (flipped : List ℕ) (r : SparseRegister L) :
    (pruneToFlipped flipped r).length ≤ r.length :=
  pruneToFlipped_length_le flipped r

end Hqiv.Geometry.HQIVOSHIntegratedFactorDriver
