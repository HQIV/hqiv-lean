import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Geometry.FactorSearchCostModel
import Hqiv.Geometry.FactorDivisibilityBridge
import Hqiv.Geometry.HQIVOSHIntegratedFactorDriver

/-!
# Monolithic geometric factorizer (Lean mirror of `monolithic_geometric_factorizer.py`)

Discrete counterparts of the Python bookkeeping:

* **Dynamic precision** `get_dynamic_precision`: `bitlength + max(1, ⌊log₂ bitlength⌋) + 8`.
* **Angle → candidate** from a rational turn `a / n` (initial pairs use `θ = 2π · a / n`).
* **Multiplication gate strength** `1 / (min(bitlen(c1), bitlen(c2)) + 2)` (`strengthInvLowestRegister`);
  `strengthInvPair` remains in Lean as the legacy pair-difference denominator.
* **Pruning**: `threshold = abs(candidate - n).bit_length + 1` (factors sit in bit-length splits of
  the target; schedule matches Python); drop when `age > threshold` and more than four registers remain.

**Asymptotics.** With register cap `min(128, ⌊∛n⌋)` (after peeling twos, odd core `n`), the cap tracks
the complementary **k**-ladder at cube-root scale. Per-step work stays **O(1)** under the `128` clamp.
Initialization still walks odd `k` until `max_k` or the cap. Precision digits are **O(inputLog2 n)**
(see `dynamicPrecisionDigits_le_two_mul_inputLog_add_eleven`).

`mpmath` real semantics are not modeled in the discrete lemmas below; see **Real turn fraction** for the
ℝ template (`FracDriftAdequateResources`: **target bits** + **max steps** + **age bound × register cap**).
**Composite factors** (e.g. `3³ · 257`) need not be prime: registers carrying `27` and `257` suffice for
the gate to see the product; **sound** factor hits do not require primality.

## Sparse OSH / “sparse Shor” alignment (same spine as the integrated driver)

**Integrated path (formal ↔ code).** The Python driver mirrored in
`HQIVOSHIntegratedFactorDriver` uses the sparse OSH step shape proved in `Hqiv.QuantumComputing.OSHoracle`:
support doubles on `applyGateSparse`, then `detectFlippedKets` + `pruneToFlipped` with explicit length
bounds (`integrated_pruned_sparse_step_length_le`, etc.). That is the **sparse-simulation** reading of
superposition bookkeeping — not a separate ad hoc list hack.

**Rapidity.** In HQIV, rapidity and shell phase (`SpatialSliceRapidityScaffold`, Ω-weighted channels) are
the geometric **bookkeeping** for “how far along the horizon / which angular slot”; they pair with
`wrapIdx` and harmonic indices exactly as the **angle** side of the same story. The OSH file fixes the
**support-list** side; together they are the discrete analogue of carrying phase while tracking only
sparse kets.

**This monolithic script.** Here, periodicity is carried by **`phase_velocity`** and `extract_period` in
Python (not modeled). The Lean content is the **discrete** shadow: `phaseAdvanceRat`, pruning via
`pruneAgeThreshold`, and sound integer hits (`monolithicAcceptsDivisor`). Age-based pruning is *not*
`pruneToFlipped` — different policy — but both are “track candidates under a budget.” A completeness
theorem tying **steps → period peak → divisor** would glue this file’s dynamics to the OSH lemmas the
same way Shor glues QFT sampling to modular arithmetic; that bridge is **not** proved here.

## Soundness vs search (what Lean isolates)

* **Verified divisor hits are not heuristic.** The Python loop only promotes an integer `d` after
  `1 < d < odd` and `odd % d == 0` — no floats. That predicate is `monolithicAcceptsDivisor`; it is
  equivalent to `OddCoreFactorWitness` and implies compositeness of the odd core
  (`not_prime_of_monolithicAccepts`). GCD-based recovery is the **same** certificate (`d ∣ odd`): see
  `Hqiv.Geometry.FactorDivisibilityBridge` (`dvd_iff_mul_div`, `oddCoreWitness_of_gcd`,
  `gcd_eq_left_of_dvd`).
* **Everything else tunes discovery**, not truth of a hit: dynamic precision, multiplication strength,
  pruning ages, and `max_registers` may cause a **miss**; they cannot turn a failing modular test into a
  success. The Python driver terminates by register exhaustion (including a final single-register
  age-out); there is no separate step cap.
* **Full `prime_factors` output** still depends on Python’s `is_probable_prime` and recursion; Lean
  treats that list as **engine output**, not a theorem, unless you replace MR with proofs or certificates.
  The algebraic glue after peeling twos is already in `HQIVOSHIntegratedFactorDriver`.
-/

namespace Hqiv.Geometry.MonolithicGeometricFactorizer

open Classical
open Finset
open Hqiv.Geometry.FactorSearchCostModel
open Hqiv.Geometry.HQIVOSHIntegratedFactorDriver

/-- If `k³ ≤ n` then `k ≤ n` (else `k ≥ n+1` would force `(n+1)³ ≤ k³ ≤ n`). -/
theorem le_of_cube_le (k n : ℕ) (h : k ^ 3 ≤ n) : k ≤ n := by
  by_contra hk
  push_neg at hk
  have hk' : n + 1 ≤ k := Nat.lt_iff_add_one_le.mp hk
  have hpow : (n + 1) ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left hk' 3
  have hsucc : (n + 1) ^ 3 > n := by
    cases n <;> simp [pow_succ, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.mul_assoc]; omega
  have hle : (n + 1) ^ 3 ≤ n := Nat.le_trans hpow h
  omega

/-! ## Integer cube root (⌊∛n⌋) — register cap aligned with odd-k ladder after 2-peel -/

/-- Greatest `r` with `r³ ≤ n` (matches `floor_cbrt` in `monolithic_geometric_factorizer.py`). -/
def floorCbrt (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun r => r ^ 3 ≤ n)).max' (by
    use 0
    simp [mem_filter, mem_range])

theorem mem_range_floorCbrt (n : ℕ) : floorCbrt n ∈ Finset.range (n + 1) := by
  have h := Finset.max'_mem ((Finset.range (n + 1)).filter (fun r => r ^ 3 ≤ n)) (by
    use 0
    simp [mem_filter, mem_range])
  simpa [floorCbrt] using (Finset.mem_filter.1 h).1

theorem floorCbrt_le (n : ℕ) : floorCbrt n ≤ n := by
  have h := mem_range_floorCbrt n
  rwa [mem_range, Nat.lt_succ_iff] at h

theorem floorCbrt_cube_le (n : ℕ) : floorCbrt n ^ 3 ≤ n :=
  (Finset.mem_filter.1 <|
      Finset.max'_mem ((Finset.range (n + 1)).filter (fun r => r ^ 3 ≤ n)) (by
        use 0
        simp [mem_filter, mem_range])).2

theorem floorCbrt_lt_succ_cube (n : ℕ) : n < (Nat.succ (floorCbrt n)) ^ 3 := by
  let S := (Finset.range (n + 1)).filter (fun r => r ^ 3 ≤ n)
  by_contra hnot
  push_neg at hnot
  have hcube : (Nat.succ (floorCbrt n)) ^ 3 ≤ n := hnot
  have hk : Nat.succ (floorCbrt n) ≤ n := le_of_cube_le _ _ hcube
  have hmem : Nat.succ (floorCbrt n) ∈ S := by
    simp [S, mem_filter, mem_range, hk, hcube]
  have hle : Nat.succ (floorCbrt n) ≤ floorCbrt n := S.le_max' (Nat.succ (floorCbrt n)) hmem
  exact Nat.not_succ_le_self (floorCbrt n) hle

/-- Python `n.bit_length()` for natural `n` (`0` maps to `0`). -/
def natBitLength (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.log 2 n + 1

theorem natBitLength_pos {n : ℕ} (hn : 0 < n) : 0 < natBitLength n := by
  simp [natBitLength, Nat.pos_iff_ne_zero.mp hn]

theorem natBitLength_le_succ_inputLog2 (n : ℕ) : natBitLength n ≤ inputLog2 n + 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [natBitLength, inputLog2]
  · have hn0 : n ≠ 0 := hn.ne'
    simp [natBitLength, hn0, inputLog2]
    exact Nat.log_mono_right (Nat.le_succ n)

/-! ## Dynamic precision digits -/

/-- Inner `log_bits = max(1, ⌊log₂ bits⌋)` with `bits = natBitLength n`. -/
def logBitsForBitLength (bits : ℕ) : ℕ :=
  max 1 (Nat.log 2 bits)

/-- Matches `get_dynamic_precision`: `bits + log_bits + 8`. -/
def dynamicPrecisionDigits (n : ℕ) : ℕ :=
  let bits := natBitLength n
  bits + logBitsForBitLength bits + 8

theorem logBitsForBitLength_le_succ (bits : ℕ) : logBitsForBitLength bits ≤ bits + 1 := by
  unfold logBitsForBitLength
  have hlog : Nat.log 2 bits ≤ bits := Nat.log_le_self 2 bits
  omega

theorem dynamicPrecisionDigits_le_two_mul_inputLog_add_eleven (n : ℕ) :
    dynamicPrecisionDigits n ≤ 2 * inputLog2 n + 11 := by
  unfold dynamicPrecisionDigits
  set bits := natBitLength n
  have hb : bits ≤ inputLog2 n + 1 := natBitLength_le_succ_inputLog2 n
  have hlog : logBitsForBitLength bits ≤ bits + 1 := logBitsForBitLength_le_succ bits
  have hsum : bits + logBitsForBitLength bits + 8 ≤ 2 * inputLog2 n + 11 := by
    omega
  simpa [two_mul, Nat.add_assoc] using hsum

/-! ## Angle slot and discrete candidate (fraction `a / n` of a full turn) -/

/-- Python `max(2, int(sqrt(n)))` — same as `HQIVOSHIntegratedFactorDriver.rootCap`. -/
def monolithicRootCap (n : ℕ) : ℕ :=
  max 2 (Nat.sqrt n)

theorem monolithicRootCap_ge_two (n : ℕ) : 2 ≤ monolithicRootCap n := by
  simp [monolithicRootCap]

/--
Discrete `angle_to_candidate` when the turn fraction is exactly `a / n`
(`θ = 2π · a / n`, so `θ/(2π) = a/n`):
`2 + ⌊(a · (root-1)) / n⌋`.
-/
def angleToCandidateMonolithic (n a : ℕ) : ℕ :=
  let r := monolithicRootCap n
  2 + (a * (r - 1)) / n

theorem angleToCandidateMonolithic_ge_two (n a : ℕ) : 2 ≤ angleToCandidateMonolithic n a := by
  simp [angleToCandidateMonolithic]

theorem angleToCandidateMonolithic_le_two_add_a (n a : ℕ) (hn : 0 < n) :
    angleToCandidateMonolithic n a ≤ 2 + a := by
  unfold angleToCandidateMonolithic monolithicRootCap
  have hr1 : max 2 (Nat.sqrt n) - 1 ≤ n := by
    have hsqrt : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
    cases Nat.le_total 2 (Nat.sqrt n) with
    | inl h2 =>
      rw [Nat.max_eq_right h2]
      exact Nat.le_trans (Nat.sub_le _ _) hsqrt
    | inr h2 =>
      rw [Nat.max_eq_left h2]
      exact Nat.lt_iff_add_one_le.mp hn
  have hmul : a * (max 2 (Nat.sqrt n) - 1) ≤ a * n :=
    Nat.mul_le_mul_left _ hr1
  have hdiv : (a * (max 2 (Nat.sqrt n) - 1)) / n ≤ a := by
    have hn0 : n ≠ 0 := hn.ne'
    have h2 : (a * (max 2 (Nat.sqrt n) - 1)) / n ≤ (a * n) / n :=
      @Nat.div_le_div_right _ _ n hmul
    have hcancel : (a * n) / n = a := by
      rw [← Nat.mul_comm n a]
      simpa using Nat.mul_div_cancel_left a (Nat.pos_of_ne_zero hn0)
    rwa [hcancel] at h2
  simpa [angleToCandidateMonolithic, monolithicRootCap] using Nat.add_le_add_left hdiv 2

/-! ## Real turn fraction and precision adequacy (bridge for `mpmath` vs discrete slots)

Python uses `frac = θ / (2π)` in `[0,1)` and `2 + ⌊frac · (root-1)⌋`. On ℝ, uniqueness of that
`floor` step holds if the **floating error in `frac`** stays below **half** a slice width.

**Resources:** the cumulative drift budget is a function of (i) **target bit length** `targetBitLength n`
(`natBitLength`, same as Python `n.bit_length()` on the odd core), (ii) **max main-loop steps**,
(iii) **per-register age bound** (prune horizon), and (iv) **register cap** — each aged register can
accumulate error independently, so scale by `registerCap` (e.g. `monolithicMaxRegisters n`). Relate
per-step `ε_step` to decimal precision (`dynamicPrecisionDigits` is `O(targetBitLength)`).
-/

/-- Odd-core target size in bits (Python `n.bit_length()`). -/
def targetBitLength (n : ℕ) : ℕ :=
  natBitLength n

/-- Normalized turn fraction `a/n` as a real (`0 < n`). -/
noncomputable def turnFractionReal (a n : ℕ) (_hn : 0 < n) : ℝ :=
  (a : ℝ) / (n : ℝ)

/-- Iteration resources: step cap, worst-case age before prune, and how many registers carry drift. -/
structure MonolithicFracResources where
  maxSteps : ℕ
  maxAgeBound : ℕ
  registerCap : ℕ

/--
Proxy for how many `frac` updates can fire: main-loop steps plus registers × age (each register line
can drift between prunes).
-/
noncomputable def fracOperationCount (r : MonolithicFracResources) : ℝ :=
  (r.maxSteps : ℝ) + (r.maxAgeBound : ℝ) * (r.registerCap : ℝ)

theorem fracOperationCount_nonneg (r : MonolithicFracResources) : 0 ≤ fracOperationCount r := by
  unfold fracOperationCount
  have hs : 0 ≤ (r.maxSteps : ℝ) := Nat.cast_nonneg _
  have ha : 0 ≤ (r.maxAgeBound : ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (r.registerCap : ℝ) := Nat.cast_nonneg _
  have hmul : 0 ≤ (r.maxAgeBound : ℝ) * (r.registerCap : ℝ) := mul_nonneg ha hc
  exact add_nonneg hs hmul

/-- Number of equal `frac` slices: `rootCap n - 1` (≥ 1 since `rootCap n ≥ 2`). -/
def monolithicSliceCount (n : ℕ) : ℕ :=
  monolithicRootCap n - 1

theorem monolithicSliceCount_pos (n : ℕ) : 0 < monolithicSliceCount n := by
  have h2 : 2 ≤ monolithicRootCap n := monolithicRootCap_ge_two n
  have hone_lt : 1 < monolithicRootCap n := Nat.lt_of_lt_of_le (by decide : 1 < 2) h2
  exact Nat.sub_pos_of_lt hone_lt

/-- Width of one `frac` slot in `[0,1)` before scaling by `(root-1)` in `angle_to_candidate`. -/
noncomputable def fracSlotWidth (n : ℕ) : ℝ :=
  (1 : ℝ) / (monolithicSliceCount n : ℝ)

theorem fracSlotWidth_pos (n : ℕ) : 0 < fracSlotWidth n := by
  have hsc : 0 < (monolithicSliceCount n : ℝ) := by
    exact_mod_cast monolithicSliceCount_pos n
  simpa [fracSlotWidth] using one_div_pos.mpr hsc

/-- Half a slice: if total `frac` error is `<` this, `floor` cannot straddle a boundary spuriously. -/
noncomputable def maxFracUncertainty (n : ℕ) : ℝ :=
  fracSlotWidth n / 2

theorem maxFracUncertainty_pos (n : ℕ) : 0 < maxFracUncertainty n := by
  have h := fracSlotWidth_pos n
  dsimp [maxFracUncertainty]
  exact half_pos h

/--
**Precision adequacy (real):** floating / `mpmath` error in normalized `frac` is dominated by half a
discrete slice — then the computer’s `angle_to_candidate` matches the rational discrete map at each
refresh. (Relate `ε` to `10^{-dps}` and multiply by step budget for cumulative drift.)
-/
def FracErrorAdequate (n : ℕ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ε < maxFracUncertainty n

/--
**Cumulative** bound (steps only): `steps · ε_step < maxFracUncertainty n`.
-/
def FracDriftAdequate (n steps : ℕ) (ε_step : ℝ) : Prop :=
  0 ≤ ε_step ∧ (steps : ℝ) * ε_step < maxFracUncertainty n

/--
Full resource bundle: `targetBits` must match `targetBitLength n`; total drift
`fracOperationCount r · ε_step` stays under half a slice. Instantiate `r.registerCap` with
`monolithicMaxRegisters n` and `r.maxAgeBound` with a bound from `pruneAgeThreshold` when certifying a
Python run.
-/
def FracDriftAdequateResources (n : ℕ) (r : MonolithicFracResources) (targetBits : ℕ) (ε_step : ℝ) : Prop :=
  targetBits = targetBitLength n ∧
  0 ≤ ε_step ∧ fracOperationCount r * ε_step < maxFracUncertainty n

/-! ## Pair-difference bit length and multiplication strength -/

/--
Python `abs(c1 - c2).bit_length()`:
`0` if equal, else `⌊log₂ |c1-c2|⌋ + 1`.
-/
def absDiffBitLength (c1 c2 : ℕ) : ℕ :=
  let d := Nat.dist c1 c2
  if d = 0 then 0 else Nat.log 2 d + 1

/-- Denominator of inverse strength: `bit_diff + 2`. -/
def strengthInvPair (c1 c2 : ℕ) : ℕ :=
  absDiffBitLength c1 c2 + 2

theorem strengthInvPair_ge_two (c1 c2 : ℕ) : 2 ≤ strengthInvPair c1 c2 := by
  simp [strengthInvPair, absDiffBitLength]

theorem absDiffBitLength_le_succ_log_max (c1 c2 : ℕ) :
    absDiffBitLength c1 c2 ≤ Nat.log 2 (max c1 c2 + 1) + 2 := by
  have hdist : Nat.dist c1 c2 ≤ max c1 c2 := by
    rw [Nat.dist_eq_max_sub_min]
    omega
  rcases Nat.eq_zero_or_pos (Nat.dist c1 c2) with hd0 | hdpos
  · simp [absDiffBitLength, hd0]
  · have hdne : Nat.dist c1 c2 ≠ 0 := hdpos.ne'
    simp [absDiffBitLength, hdne]
    have hlog : Nat.log 2 (Nat.dist c1 c2) ≤ Nat.log 2 (max c1 c2) :=
      Nat.log_mono_right hdist
    have hmx : Nat.log 2 (max c1 c2) ≤ Nat.log 2 (max c1 c2 + 1) :=
      Nat.log_mono_right (Nat.le_succ _)
    omega

/-! ## Closeness and rational phase advance (multiplication gate) -/

/-- Python `abs(c1*c2 - n) / n` as a rational. Can exceed `1` when the product is far from `n`. -/
def closenessRat (c1 c2 n : ℕ) (_hn : 0 < n) : ℚ :=
  (Nat.dist (c1 * c2) n : ℚ) / n

theorem closenessRat_nonneg (c1 c2 n : ℕ) (hn : 0 < n) : 0 ≤ closenessRat c1 c2 n hn := by
  simp [closenessRat]
  refine div_nonneg (Nat.cast_nonneg _) ?_
  exact_mod_cast hn.le

theorem closenessRat_le_one_of_dist_le (c1 c2 n : ℕ) (hn : 0 < n)
    (h : Nat.dist (c1 * c2) n ≤ n) : closenessRat c1 c2 n hn ≤ 1 := by
  simp [closenessRat]
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  rw [div_le_one hnq]
  exact_mod_cast h

/--
Scaled phase advance `(1 - closeness) / strengthInv` when closeness ≤ 1 so the numerator is
nonnegative (hypothesis `hcl`).
-/
def phaseAdvanceRat (c1 c2 n : ℕ) (hn : 0 < n) (_hcl : Nat.dist (c1 * c2) n ≤ n) : ℚ :=
  ((1 : ℚ) - closenessRat c1 c2 n hn) * (1 / (strengthInvPair c1 c2 : ℚ))

theorem phaseAdvanceRat_nonneg (c1 c2 n : ℕ) (hn : 0 < n) (hcl : Nat.dist (c1 * c2) n ≤ n) :
    0 ≤ phaseAdvanceRat c1 c2 n hn hcl := by
  unfold phaseAdvanceRat
  have hc : closenessRat c1 c2 n hn ≤ 1 := closenessRat_le_one_of_dist_le _ _ _ hn hcl
  have h1 : (0 : ℚ) ≤ 1 - closenessRat c1 c2 n hn := sub_nonneg.mpr hc
  have h2 : 0 ≤ (1 / (strengthInvPair c1 c2 : ℚ)) := by
    have hpos : 0 < strengthInvPair c1 c2 :=
      Nat.lt_of_lt_of_le (by decide : 0 < 2) (strengthInvPair_ge_two c1 c2)
    have hs : 0 < (strengthInvPair c1 c2 : ℚ) := Nat.cast_pos.mpr hpos
    exact (one_div_pos.mpr hs).le
  exact mul_nonneg h1 h2

theorem phaseAdvanceRat_le_one_div_two (c1 c2 n : ℕ) (hn : 0 < n)
    (hcl : Nat.dist (c1 * c2) n ≤ n) :
    phaseAdvanceRat c1 c2 n hn hcl ≤ 1 / 2 := by
  unfold phaseAdvanceRat
  have hc : closenessRat c1 c2 n hn ≤ 1 := closenessRat_le_one_of_dist_le _ _ _ hn hcl
  have h1 : (1 - closenessRat c1 c2 n hn) ≤ 1 := by linarith [closenessRat_nonneg c1 c2 n hn, hc]
  have hs : (2 : ℚ) ≤ (strengthInvPair c1 c2 : ℚ) := by exact_mod_cast strengthInvPair_ge_two c1 c2
  have h2pos : (0 : ℚ) < 2 := by norm_num
  have hinv : (1 / (strengthInvPair c1 c2 : ℚ)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le h2pos hs
  have hinv_nn : 0 ≤ (1 / (strengthInvPair c1 c2 : ℚ)) := by
    have hpos : 0 < strengthInvPair c1 c2 :=
      Nat.lt_of_lt_of_le (by decide : 0 < 2) (strengthInvPair_ge_two c1 c2)
    have hs : 0 < (strengthInvPair c1 c2 : ℚ) := Nat.cast_pos.mpr hpos
    exact (one_div_pos.mpr hs).le
  calc
    (1 - closenessRat c1 c2 n hn) * (1 / (strengthInvPair c1 c2 : ℚ))
        ≤ 1 * (1 / (strengthInvPair c1 c2 : ℚ)) := mul_le_mul_of_nonneg_right h1 hinv_nn
    _ = 1 / (strengthInvPair c1 c2 : ℚ) := one_mul _
    _ ≤ 1 / 2 := hinv

/-! ## Pruning policy (Python `age > threshold` with `threshold = bitlength + 1`) -/

/-- `abs(candidate - n).bit_length + 1` in Python; we use `absDiffBitLength`. -/
def pruneAgeThreshold (n c : ℕ) : ℕ :=
  absDiffBitLength c n + 1

/--
If the script removes a line, Python requires `age > pruneAgeThreshold n c`, hence
`pruneAgeThreshold n c + 1 ≤ age`.
-/
theorem prune_requires_age (n c age : ℕ) (h : pruneAgeThreshold n c < age) :
    pruneAgeThreshold n c + 1 ≤ age :=
  Nat.succ_le_of_lt h

theorem pruneAgeThreshold_le_inputLog_add_three (n c : ℕ) (hc : c ≤ n) :
    pruneAgeThreshold n c ≤ inputLog2 n + 3 := by
  have hdist : Nat.dist c n = n - c :=
    Nat.dist_eq_sub_of_le hc
  have hbd : Nat.dist c n ≤ n := by
    rw [hdist]
    exact Nat.sub_le _ _
  rcases Nat.eq_zero_or_pos (Nat.dist c n) with hd0 | hdpos
  · simp [pruneAgeThreshold, absDiffBitLength, hd0]
  · have hdne : Nat.dist c n ≠ 0 := hdpos.ne'
    simp [pruneAgeThreshold, absDiffBitLength, hdne]
    have hlog : Nat.log 2 (Nat.dist c n) ≤ Nat.log 2 n :=
      Nat.log_mono_right hbd
    have hn1 : Nat.log 2 n ≤ inputLog2 n := by
      simp [inputLog2]
      exact Nat.log_mono_right (Nat.le_succ _)
    omega

/-! ## Dynamic strength (lowest register) and mod-periodicity certificates for age pruning

**Python:** multiplication strength uses `strengthInvLowestRegister` (`min` bit-length + 2). Lean still
records `strengthInvPair` (`abs(c1-c2)` bit-length) for comparison with older analyses.

**Certified prune:** if the map `t ↦ f t % m` has exhibited **global** period `p` (`f (t+p) ≡ f t`),
then residues depend only on `t % p`; ages beyond that carry **no new mod-`m` information**, which is
the discrete certificate behind “safe to drop stale trajectories” *for that observable* — not a
guarantee that the true divisor is absent (completeness is separate).
-/

/-- Bit-size proxy for one register (`natBitLength`, same convention as dynamic precision). -/
def registerBitSize (c : ℕ) : ℕ :=
  natBitLength c

/-- Minimum of the two paired registers’ bit-sizes — “lowest sized register” for tuning. -/
def minRegisterBitSize (c1 c2 : ℕ) : ℕ :=
  min (registerBitSize c1) (registerBitSize c2)

/--
Inverse-strength denominator keyed off the **minimum** register size (`+ 2` keeps the same slack as
`strengthInvPair`). Compare with pair-difference `strengthInvPair` used in current Python.
-/
def strengthInvLowestRegister (c1 c2 : ℕ) : ℕ :=
  minRegisterBitSize c1 c2 + 2

theorem strengthInvLowestRegister_ge_two (c1 c2 : ℕ) : 2 ≤ strengthInvLowestRegister c1 c2 := by
  unfold strengthInvLowestRegister minRegisterBitSize registerBitSize natBitLength
  split_ifs <;> omega

/-- Rational phase advance using `strengthInvLowestRegister` instead of `strengthInvPair`. -/
def phaseAdvanceRatLowest (c1 c2 n : ℕ) (hn : 0 < n) (_hcl : Nat.dist (c1 * c2) n ≤ n) : ℚ :=
  ((1 : ℚ) - closenessRat c1 c2 n hn) * (1 / (strengthInvLowestRegister c1 c2 : ℚ))

theorem phaseAdvanceRatLowest_nonneg (c1 c2 n : ℕ) (hn : 0 < n) (hcl : Nat.dist (c1 * c2) n ≤ n) :
    0 ≤ phaseAdvanceRatLowest c1 c2 n hn hcl := by
  unfold phaseAdvanceRatLowest
  have hc : closenessRat c1 c2 n hn ≤ 1 := closenessRat_le_one_of_dist_le _ _ _ hn hcl
  have h1 : (0 : ℚ) ≤ 1 - closenessRat c1 c2 n hn := sub_nonneg.mpr hc
  have hpos : 0 < strengthInvLowestRegister c1 c2 :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2) (strengthInvLowestRegister_ge_two c1 c2)
  have h2 : 0 ≤ (1 / (strengthInvLowestRegister c1 c2 : ℚ)) := by
    have hs : 0 < (strengthInvLowestRegister c1 c2 : ℚ) := Nat.cast_pos.mpr hpos
    exact (one_div_pos.mpr hs).le
  exact mul_nonneg h1 h2

/-! ### Mod-`m` periodicity and redundant age (certificate for prune) -/

/-- Residue of `f t` modulo `m` (`m > 0`). -/
def modResidue (f : ℕ → ℕ) (m : ℕ) (t : ℕ) (_hm : 0 < m) : ℕ :=
  f t % m

/-- Global period: shifting by `p` preserves residues mod `m` at every step. -/
def modGlobalPeriod (f : ℕ → ℕ) (m p : ℕ) : Prop :=
  0 < m ∧ 0 < p ∧ ∀ t, f (t + p) % m = f t % m

theorem mod_residue_iter_period (f : ℕ → ℕ) (m p k : ℕ) (_hm : 0 < m) (_hp : 0 < p)
    (hper : ∀ t, f (t + p) % m = f t % m) : f (k * p) % m = f 0 % m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul]
    exact (hper (k * p)).trans ih

/--
If `f` is globally `p`-periodic mod `m`, every age has the same residue class as the remainder of
`age` mod `p` — **no further mod-`m` information** from counting age beyond multiples of `p`.
This is the discrete backbone for certifying “stale” trajectories when a period has been detected.
-/
theorem mod_residue_eq_mod_age (f : ℕ → ℕ) (m p age : ℕ) (_hm : 0 < m) (hp : 0 < p)
    (hper : ∀ t, f (t + p) % m = f t % m) : f age % m = f (age % p) % m := by
  refine Nat.strong_induction_on age ?_
  intro a ih
  rcases Nat.lt_or_ge a p with hlt | hge
  · have ha : a % p = a := Nat.mod_eq_of_lt hlt
    simp [ha]
  · have hage : f a % m = f (a - p) % m := by
      have h := hper (a - p)
      have hs : a - p + p = a := Nat.sub_add_cancel hge
      simpa [hs] using h
    have hlt' : a - p < a := Nat.sub_lt (Nat.lt_of_lt_of_le hp hge) hp
    have hmod : (a - p) % p = a % p := by
      conv_rhs => rw [← Nat.sub_add_cancel hge]
      rw [Nat.add_mod_right]
    rw [hage, ih (a - p) hlt']
    exact congr_arg (fun t => f t % m) hmod

/--
**Certified age threshold (mod-`m` view):** once `age ≥ p` and global period `p` is known for the
observed map, the residue at `age` is already determined by `age % p`; increasing `age` further does
not refine the mod-`m` observable.
-/
theorem age_redundant_mod_obs_of_global_period (f : ℕ → ℕ) (m p age₁ age₂ : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hper : ∀ t, f (t + p) % m = f t % m) (h₁ : age₁ % p = age₂ % p) :
    f age₁ % m = f age₂ % m := by
  calc
    f age₁ % m = f (age₁ % p) % m := mod_residue_eq_mod_age f m p age₁ hm hp hper
    _ = f (age₂ % p) % m := by rw [h₁]
    _ = f age₂ % m := (mod_residue_eq_mod_age f m p age₂ hm hp hper).symm

/-- Finite-window observation: residues repeat with period `p` on indices `< len` (prefix certificate). -/
def modPeriodObservedPrefix (f : ℕ → ℕ) (m p len : ℕ) : Prop :=
  0 < m ∧ 0 < p ∧ ∀ i, i + p < len → f (i + p) % m = f i % m

/-! ## Register cap and initialization length (read `O(·)` from explicit `≤`) -/

/-- Python `max(12, min(128, floor_cbrt(n)))` — cube-root scale matches odd-`k` ladder after 2-peel. -/
def monolithicMaxRegisters (n : ℕ) : ℕ :=
  max 12 (min 128 (floorCbrt n))

theorem monolithicMaxRegisters_le_128 (n : ℕ) : monolithicMaxRegisters n ≤ 128 := by
  simp [monolithicMaxRegisters]

/-- Odd-index walk bound `min(n // 4, 2 * ⌊√n⌋)` from Python before the register cap stops early. -/
def monolithicOddKUpper (n : ℕ) : ℕ :=
  min (n / 4) (2 * Nat.sqrt n)

theorem monolithicOddKUpper_le_two_mul_sqrt (n : ℕ) :
    monolithicOddKUpper n ≤ 2 * Nat.sqrt n := by
  simp [monolithicOddKUpper]

/-! ## Soundness of integer divisor checks (vs heuristic search knobs) -/

/--
Integer acceptance test used in `monolithic_geometric_factorizer.py` when recording `best_factor`
(or the fallback `best_reg`): **no** floating-point predicate — only bounds and `%`.
-/
def monolithicAcceptsDivisor (n d : ℕ) : Prop :=
  1 < d ∧ d < n ∧ n % d = 0

theorem monolithicAcceptsDivisor_iff_dvd_and_bounds (n d : ℕ) :
    monolithicAcceptsDivisor n d ↔ (1 < d ∧ d < n ∧ d ∣ n) := by
  constructor
  · rintro ⟨h₁, h₂, hmod⟩
    exact ⟨h₁, h₂, Nat.dvd_of_mod_eq_zero hmod⟩
  · rintro ⟨h₁, h₂, hdvd⟩
    exact ⟨h₁, h₂, Nat.mod_eq_zero_of_dvd hdvd⟩

/-- Pack a passing acceptance test as the same `OddCoreFactorWitness` shape as the integrated driver. -/
def oddCoreWitness_of_monolithicAccept {n d : ℕ} (h : monolithicAcceptsDivisor n d) :
    OddCoreFactorWitness n :=
  ⟨d, h.1, h.2.1, Nat.dvd_of_mod_eq_zero h.2.2⟩

theorem oddCoreWitness_of_monolithicAccept_reconstructs {n d : ℕ} (h : monolithicAcceptsDivisor n d) :
    n = (oddCoreWitness_of_monolithicAccept h).d * (n / (oddCoreWitness_of_monolithicAccept h).d) := by
  simpa [oddCoreWitness_of_monolithicAccept] using (oddCoreWitness_of_monolithicAccept h).reconstructs.symm

/--
A reported divisor witness means the odd part cannot be prime (so the “geometric search” did not
need to guess primality to certify **compositeness**).
-/
theorem not_prime_of_monolithicAccepts {n d : ℕ} (_hn : 1 < n) (h : monolithicAcceptsDivisor n d) :
    ¬Nat.Prime n := by
  rcases h with ⟨h₁, h₂, hmod⟩
  have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
  have h2 : 2 ≤ d := Nat.succ_le_iff.mpr h₁
  exact Nat.not_prime_of_dvd_of_lt hdvd h2 h₂

/--
After peeling `orig = 2^k * odd`, any monolithic acceptance on `odd` splits `orig` exactly
(`HQIVOSHIntegratedFactorDriver.IntegratedFactorWitness.reconstructs_orig` is the bundled witness).
-/
theorem factor_orig_of_peel_and_monolithic_hit (orig k odd d : ℕ)
    (hpeel : orig = 2 ^ k * odd) (h : monolithicAcceptsDivisor odd d) :
    orig = 2 ^ k * d * (odd / d) := by
  rw [hpeel]
  have hr : d * (odd / d) = odd := by
    simpa [oddCoreWitness_of_monolithicAccept] using (oddCoreWitness_of_monolithicAccept h).reconstructs
  conv_lhs => rw [← hr]
  exact (Nat.mul_assoc (2 ^ k) d (odd / d)).symm

theorem two_pow_dvd_orig_of_monolithic_hit (orig k odd d : ℕ)
    (hpeel : orig = 2 ^ k * odd) (h : monolithicAcceptsDivisor odd d) :
    2 ^ k * d ∣ orig :=
  two_pow_mul_dvd_of_dvd_odd hpeel (oddCoreWitness_of_monolithicAccept h).hdiv

/-! ## Counterexamples (boundary ⇒ different bookkeeping)

**Prune age.** `pruneAgeThreshold` is `absDiffBitLength |c - n| + 1`. When `Nat.dist c n` crosses from `7`
to `8`, the bit-length of the distance steps up, so the **same** target `n` but **adjacent** candidates
sit in different prune bands — a literal change of age budget on that line (as soon as you hit the
boundary, you are past the previous threshold scale).

**Lowest-register strength.** `strengthInvLowestRegister` uses `min (natBitLength c1) (natBitLength c2)`;
moving a coordinate from `7` to `8` crosses a bit-length stair-step, so the inverse-strength denominator
jumps when that side is the minimum.

**GCD probe.** `gcd(2,15) = 1` while `3 ∣ 15`: one gcd sample need not meet any nontrivial factor — this
is the counterexample side of “gcd and division are the same *once you hold the right certificate*”
vs “any fixed probe succeeds.” See also `Hqiv.Geometry.FactorDivisibilityBridge`.
-/

theorem dist_to_n_boundary_seven_vs_eight : Nat.dist 993 1000 = 7 ∧ Nat.dist 992 1000 = 8 := by
  native_decide

theorem pruneAgeThreshold_jumps_across_dist_boundary :
    pruneAgeThreshold 1000 993 = 4 ∧ pruneAgeThreshold 1000 992 = 5 := by
  native_decide

theorem registerBitSize_jumps_at_eight : registerBitSize 7 ≠ registerBitSize 8 := by
  native_decide

theorem strengthInvLowestRegister_jumps_when_low_coordinate_crosses_eight :
    strengthInvLowestRegister 7 100 ≠ strengthInvLowestRegister 8 100 := by
  native_decide

theorem gcd_probe_can_miss_nontrivial_factor :
    Nat.gcd 2 15 = 1 ∧ 3 ∣ 15 ∧ 1 < 3 ∧ 3 < 15 := by
  native_decide

/-! Lean-identified gaps (tuning / completeness, not soundness of modular hits):

- If the true divisor sits on a pruned register or beyond `max_registers`, you get a miss; raise the
  cap or relax prune policy. The acceptance test is unchanged.

- If `angle_to_candidate` or gate dynamics never land an integer divisor, increase precision or
  adjust strength; only discovery is affected.

- Full `prime_factors` output remains probable until primes are certified (AKS, Pratt, proofs in Lean).
-/

end Hqiv.Geometry.MonolithicGeometricFactorizer
