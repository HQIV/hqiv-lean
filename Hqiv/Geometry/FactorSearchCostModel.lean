import Mathlib.Data.Nat.Log
import Hqiv.QuantumComputing.OSHoracle

/-!
# Cost-model scaffolding for factor / gate-frontier search

This file does **not** assert **completeness** (“every composite yields a factor”) for any script.
**Sound** divisor checks and **peel + recursive** split are algebraic; turning that into a proved
**prime list** needs certified primality (or recursion to atoms). **Big-`O` runtime** is the main
remaining certification layer: the **integrated** sparse pipeline below has a concrete **polynomial in
`inputLog2 n + 1`** total-work bound (`total_integrated_work_le_twelve_mul_inputLogDim_pow_six`); the
**monolithic** geometric factorizer’s wall-clock asymptotic is still a **roadmap** (combine
`MonolithicGeometricFactorizer` caps/precision with per-step costs).

Instead of a single `O((log n)^α)` slogan for all drivers, this file isolates **exact** combinatorial
quantities that any complexity proof must relate:

* a standard **bit-scale** parameter `inputLog2 n`;
* the **harmonic cutoff** `L` used in the sparse layer (matching the integrated
  driver’s default `max 4 √n` when `L` is auto);
* **per-step list traffic** in the sparse OSH step: lengths of `before`, evolved,
  and flipped-index lists are linear in the pre-step support size.

A future `poly (inputLog2 n)` bound would combine (i) a policy tying `L` and fuel
to `n`, (ii) a proved or assumed **support cap** `r.length ≤ B(L, n)`, and (iii)
the linear per-step bounds below to sum over `fuel` iterations.

This file also defines `integratedStepListCost`, `fuelPolyLogSq`, `SearchPipelineHypothesis`,
and a template inequality `naive_total_le_poly_template` bounding total naive list
charge when fuel is capped by `fuelPolyLogSq` and per-step charge by `6 * (5+√n)²`.

**Support caps** `seedPointCap` / `postPruneSupportCap` match the integrated driver’s
`seed_points = min(64, sparse_basis_card(L))` and the proved bound
`prune.length ≤ 2 * before.length`.

**Phase-channel** costs abstract `_registers_from_sparse_state`, pair multiplication,
history append, and a conservative `O(h²)` charge for `extract_period` when history
length is `h`.

**`integratedCombinedPerStepCap`** + `total_integrated_work_le_twelve_mul_inputLogDim_pow_six`
give a concrete polynomial bound in **`inputLog2 n + 1`** (degree `6` in the
combined theorem statement).

See also `Hqiv.Geometry.HQIVOSHIntegratedFactorDriver` for certificates and
candidate maps, `Hqiv.Geometry.MonolithicGeometricFactorizer` for the monolithic
Python factorizer’s precision / pruning / strength policy, and
`Hqiv.QuantumComputing.OSHoracle` for sparse support lemmas.
-/

namespace Hqiv.Geometry.FactorSearchCostModel

open Hqiv.QuantumComputing

/-- Floor log₂ of `n + 1` (avoids base-2 log of `0`). Convenient input-size proxy. -/
def inputLog2 (n : ℕ) : ℕ :=
  Nat.log 2 (n + 1)

/-- Integrated-driver style default cutoff when `L` is chosen automatically: `max 4 √n`. -/
def defaultHarmonicCutoff (n : ℕ) : ℕ :=
  max 4 (Nat.sqrt n)

theorem defaultHarmonicCutoff_le_four_add_sqrt (n : ℕ) :
    defaultHarmonicCutoff n ≤ 4 + Nat.sqrt n := by
  simp [defaultHarmonicCutoff]

theorem defaultHarmonicCutoff_le_four_add_n (n : ℕ) : defaultHarmonicCutoff n ≤ 4 + n := by
  have hs : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  calc
    defaultHarmonicCutoff n ≤ 4 + Nat.sqrt n := defaultHarmonicCutoff_le_four_add_sqrt n
    _ ≤ 4 + n := Nat.add_le_add_left hs _

theorem inputLog2_le_succ (n : ℕ) : inputLog2 n ≤ n + 1 := by
  simpa [inputLog2] using Nat.log_le_self 2 (n + 1)

/-- Convenient ring variable `d := inputLog2 n + 1` for polynomial bounds. -/
def inputLogDim (n : ℕ) : ℕ :=
  inputLog2 n + 1

/-- Sparse harmonic basis size `(L+1)²` from `sparseBasisCard`. -/
abbrev basisCard (L : ℕ) : ℕ :=
  sparseBasisCard L

theorem basisCard_eq (L : ℕ) : basisCard L = (L + 1) ^ 2 := by
  simp [basisCard, sparseBasisCard]

theorem basisCard_quad_in_L (L : ℕ) : basisCard L ≤ (L + 2) ^ 2 := by
  rw [basisCard_eq]
  have : (L + 1) ^ 2 ≤ (L + 2) ^ 2 := by
    exact Nat.pow_le_pow_left (Nat.le_succ _) 2
  exact this

theorem basisCard_mono {L L' : ℕ} (h : L ≤ L') : basisCard L ≤ basisCard L' := by
  simp [basisCard_eq]
  exact Nat.pow_le_pow_left (Nat.add_le_add_right h _) 2

/-! ## Support invariant (integrated driver: seed + prune)

Python uses `seed_points = min(64, sparse_basis_card(L))` and
`build_seed_register(L, n_points)` so the **initial** sparse list has length
`≤ min(64, basisCard L)`. After `apply_gate_sparse` and `prune_to_flipped`, Lean
proves `prune.length ≤ evolved.length = 2 * before.length`.
-/

/-- Matches `min(64, sparse_basis_card(L))` in `hqiv_osh_integrated_driver.py`. -/
def seedPointCap (_n L : ℕ) : ℕ :=
  min 64 (basisCard L)

/-- Worst-case support after one evolve+prune from a seed-bounded `before`. -/
def postPruneSupportCap (n L : ℕ) : ℕ :=
  2 * seedPointCap n L

theorem seedPointCap_le_basisCard (n L : ℕ) : seedPointCap n L ≤ basisCard L := by
  simp [seedPointCap]

theorem seedPointCap_le_sixty_four (n L : ℕ) : seedPointCap n L ≤ 64 := by
  simp [seedPointCap]

/--
After `pruneToFlipped flipped (applyGateSparse g r)`, the active sparse list is
no longer than `2 * r.length` (evolve doubles, then prune only removes).
-/
theorem prune_after_sparse_le_two_mul_before (L : ℕ) (g : HQIVGate L) (r : SparseRegister L)
    (flipped : List ℕ) :
    (pruneToFlipped flipped (applyGateSparse g r)).length ≤ 2 * r.length := by
  refine Nat.le_trans (pruneToFlipped_length_le _ _) ?_
  rw [applyGateSparse_length_eq_two_mul g r]

/--
If `before.length` is bounded by the seed cap, the pruned register is bounded by
`postPruneSupportCap` (the integrated driver’s worst-case one-step blow-up).
-/
theorem prune_length_le_postPruneSupportCap (n L : ℕ) (g : HQIVGate L) (r : SparseRegister L)
    (flipped : List ℕ) (h : r.length ≤ seedPointCap n L) :
    (pruneToFlipped flipped (applyGateSparse g r)).length ≤ postPruneSupportCap n L := by
  unfold postPruneSupportCap seedPointCap
  exact (prune_after_sparse_le_two_mul_before L g r flipped).trans (Nat.mul_le_mul_left 2 h)

/-- Predicate: sparse state lies in the one-step post-prune envelope from a seed-bounded row. -/
def postPruneLengthLeCap (n L : ℕ) (r : SparseRegister L) : Prop :=
  r.length ≤ postPruneSupportCap n L

/--
One sparse gate step: sum of list lengths for `before`, evolved sparse register,
and flipped-index list is at most `6` times the **pre-step** support length.

This is a crude **worst-case** charging scheme (each cell touched once); it is
exactly the kind of bound that multiplies by `fuel` when you assume a per-step
support cap.
-/
theorem sparse_step_list_sum_le_six_mul (L : ℕ) (g : HQIVGate L) (r : SparseRegister L) :
    r.length + (applyGateSparse g r).length +
        (detectFlippedKets r (applyGateSparse g r)).length ≤
      6 * r.length := by
  set e := applyGateSparse g r
  set f := detectFlippedKets r e
  have hel : e.length = 2 * r.length := applyGateSparse_length_eq_two_mul g r
  have hfle : f.length ≤ r.length + e.length := detectFlippedKets_length_le_sum r e
  rw [hel] at hfle
  omega

/--
If the pre-step register has support at most `B`, the same triple-sum is `≤ 6 * B`.
-/
theorem sparse_step_list_sum_le_six_mul_cap (L : ℕ) (g : HQIVGate L) (r : SparseRegister L)
    (B : ℕ) (hB : r.length ≤ B) :
    r.length + (applyGateSparse g r).length +
        (detectFlippedKets r (applyGateSparse g r)).length ≤
      6 * B :=
  (sparse_step_list_sum_le_six_mul L g r).trans (Nat.mul_le_mul_left 6 hB)

/--
Explicit list-charge for one integrated sparse step (before + evolved + flipped indices).

`noncomputable` because `applyGateSparse` is classical in `OSHoracle`.
-/
noncomputable def integratedStepListCost (L : ℕ) (g : HQIVGate L) (r : SparseRegister L) : ℕ :=
  r.length + (applyGateSparse g r).length + (detectFlippedKets r (applyGateSparse g r)).length

theorem integratedStepListCost_eq (L : ℕ) (g : HQIVGate L) (r : SparseRegister L) :
    integratedStepListCost L g r =
      r.length + (applyGateSparse g r).length +
        (detectFlippedKets r (applyGateSparse g r)).length :=
  rfl

theorem integratedStepListCost_le_six_mul (L : ℕ) (g : HQIVGate L) (r : SparseRegister L) :
    integratedStepListCost L g r ≤ 6 * r.length :=
  sparse_step_list_sum_le_six_mul L g r

theorem integratedStepListCost_le_six_mul_cap (L : ℕ) (g : HQIVGate L) (r : SparseRegister L)
    (B : ℕ) (hB : r.length ≤ B) : integratedStepListCost L g r ≤ 6 * B :=
  sparse_step_list_sum_le_six_mul_cap L g r B hB

/-- Naive total work proxy: `fuel` identical steps each charged at most `W` units. -/
def fuelTotalWork (fuel W : ℕ) : ℕ :=
  fuel * W

/--
Under a uniform per-step work cap `W`, total charged work is `fuel * W`.

To specialize toward `poly (inputLog2 n)`, supply `W` from
`sparse_step_list_sum_le_six_mul_cap` with a `B` derived from your support-bound
hypothesis, and bound `fuel` using your loop termination policy.
-/
theorem fuelTotalWork_le (fuel W W' : ℕ) (h : W ≤ W') : fuelTotalWork fuel W ≤ fuelTotalWork fuel W' :=
  Nat.mul_le_mul_left fuel h

theorem fuelTotalWork_six_mul_cap (fuel B : ℕ) : fuelTotalWork fuel (6 * B) = fuel * 6 * B := by
  simp [fuelTotalWork, Nat.mul_assoc]

theorem fuelTotalWork_le_of_fuel_bound (fuel fuel' W : ℕ) (hf : fuel ≤ fuel') :
    fuelTotalWork fuel W ≤ fuelTotalWork fuel' W := by
  simp [fuelTotalWork]
  exact Nat.mul_le_mul hf le_rfl

/-- `L + 1 ≤ 5 + √n` for the default cutoff `max 4 √n`. -/
theorem defaultHarmonicCutoff_add_one_le_five_add_sqrt (n : ℕ) :
    defaultHarmonicCutoff n + 1 ≤ 5 + Nat.sqrt n := by
  simp [defaultHarmonicCutoff]
  omega

theorem basisCard_default_cutoff_le_sq_five_add_sqrt (n : ℕ) :
    basisCard (defaultHarmonicCutoff n) ≤ (5 + Nat.sqrt n) ^ 2 := by
  rw [basisCard_eq]
  exact Nat.pow_le_pow_left (defaultHarmonicCutoff_add_one_le_five_add_sqrt n) 2

theorem six_mul_basisCard_default_le (n : ℕ) :
    6 * basisCard (defaultHarmonicCutoff n) ≤ 6 * (5 + Nat.sqrt n) ^ 2 :=
  Nat.mul_le_mul_left _ (basisCard_default_cutoff_le_sq_five_add_sqrt n)

/--
Charging each step at `W = 6 * basisCard L` with `L = defaultHarmonicCutoff n` yields a
per-step charge `≤ 6 * (5 + √n)²`. (This is **not** the same as a tight sparse support
bound; it is the angular basis size, used as a coarse universal cap.)
-/
theorem fuelTotalWork_six_basisCard_default_le (fuel n : ℕ) :
    fuelTotalWork fuel (6 * basisCard (defaultHarmonicCutoff n)) ≤
      fuel * 6 * (5 + Nat.sqrt n) ^ 2 := by
  simpa [fuelTotalWork, Nat.mul_assoc] using Nat.mul_le_mul_left fuel (six_mul_basisCard_default_le n)

/-- Polylog-style iteration budget template: `(inputLog2 n + 1)²`. -/
def fuelPolyLogSq (n : ℕ) : ℕ :=
  (inputLog2 n + 1) ^ 2

theorem fuelPolyLogSq_le_sq_succ (n : ℕ) : fuelPolyLogSq n ≤ (n + 2) ^ 2 := by
  have h1 : inputLog2 n + 1 ≤ n + 2 := by
    exact Nat.succ_le_succ (inputLog2_le_succ n)
  simp [fuelPolyLogSq]
  exact Nat.pow_le_pow_left h1 2

theorem fuelPolyLogSq_eq_inputLogDim_sq (n : ℕ) : fuelPolyLogSq n = (inputLogDim n) ^ 2 := by
  simp [fuelPolyLogSq, inputLogDim]

/-! ## Phase-channel cost (integrated driver)

Charges: building angle registers from sparse support (`≤ 2 * sparseLen` kets with
reflection), pair `multiplication_gate` passes (`≤ sparseLen` pairs when
`regs ≈ 2 * sparseLen`), one history append, and `extract_period` with naive
`O(h²)` for history length `h` (bounded by `fuel`).
-/

def phaseRegisterBuildCost (sparseLen : ℕ) : ℕ :=
  2 * sparseLen

def phasePairCost (sparseLen : ℕ) : ℕ :=
  sparseLen

def phaseHistoryAppendCost : ℕ :=
  1

/-- Naive `O(h²)` upper bound for `extract_period` (Python double loop over lag `p`). -/
def phaseExtractCost (histLen : ℕ) : ℕ :=
  histLen * histLen

def phaseHistoryLenBound (fuel : ℕ) : ℕ :=
  fuel

def phaseChannelPerStepCap (sparseSupport fuel : ℕ) : ℕ :=
  phaseRegisterBuildCost sparseSupport + phasePairCost sparseSupport + phaseHistoryAppendCost +
    phaseExtractCost (phaseHistoryLenBound fuel)

/-- Sparse list work cap expressed in `inputLogDim` (hypothesis-grade substitute for `√n` basis). -/
def integratedSparsePerStepCapInputLog (n : ℕ) : ℕ :=
  6 * (inputLogDim n) ^ 3

/--
Phase cost with `sparseSupport = (inputLogDim n)³` and history bound `(inputLogDim n)²`
matching `fuelPolyLogSq` (extract cost `(fuel)² = (inputLogDim n)⁴`).
-/
def integratedPhaseChannelPerStepCap (n : ℕ) : ℕ :=
  let d := inputLogDim n
  phaseChannelPerStepCap (d ^ 3) (d ^ 2)

def integratedCombinedPerStepCap (n : ℕ) : ℕ :=
  integratedSparsePerStepCapInputLog n + integratedPhaseChannelPerStepCap n

theorem integratedCombinedPerStepCap_le_twelve_mul_inputLogDim_pow_four (n : ℕ) :
    integratedCombinedPerStepCap n ≤ 12 * (inputLogDim n) ^ 4 := by
  simp only [integratedCombinedPerStepCap, integratedSparsePerStepCapInputLog, integratedPhaseChannelPerStepCap,
    phaseChannelPerStepCap, phaseRegisterBuildCost, phasePairCost, phaseHistoryAppendCost, phaseExtractCost,
    phaseHistoryLenBound, inputLogDim]
  set d := inputLog2 n + 1 with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact Nat.succ_pos _
  have hsq : d ^ 2 * d ^ 2 = d ^ 4 := by
    simpa using (Nat.pow_add d 2 2).symm
  have hpoly : 9 * d ^ 3 + d ^ 4 + 1 ≤ 12 * d ^ 4 := by
    have hd1 : 1 ≤ d := Nat.succ_le_of_lt hdpos
    have h9 : 9 * d ^ 3 ≤ 9 * d ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hd1 (by decide : 3 ≤ 4))
    have hsum : 9 * d ^ 3 + d ^ 4 ≤ 9 * d ^ 4 + d ^ 4 := Nat.add_le_add_right h9 _
    have h10 : 9 * d ^ 4 + d ^ 4 = 10 * d ^ 4 := (Nat.succ_mul 9 (d ^ 4)).symm
    have h10le : 10 * d ^ 4 + 1 ≤ 12 * d ^ 4 := by
      have hone : 1 ≤ 2 * d ^ 4 := by
        have h1 : 1 ≤ d ^ 4 := by
          simpa [Nat.one_pow] using Nat.pow_le_pow_left (Nat.succ_le_of_lt hdpos) 4
        have h2 : d ^ 4 ≤ 2 * d ^ 4 := by
          simpa [Nat.one_mul] using Nat.mul_le_mul_right (d ^ 4) (by decide : 1 ≤ 2)
        exact Nat.le_trans h1 h2
      calc
        10 * d ^ 4 + 1 ≤ 10 * d ^ 4 + 2 * d ^ 4 := Nat.add_le_add_left hone _
        _ = 12 * d ^ 4 := by rw [← Nat.add_mul 10 2 (d ^ 4)]
    calc
      9 * d ^ 3 + d ^ 4 + 1 ≤ 9 * d ^ 4 + d ^ 4 + 1 := Nat.add_le_add_right hsum 1
      _ = 10 * d ^ 4 + 1 := by rw [h10]
      _ ≤ 12 * d ^ 4 := h10le
  have hleft :
      6 * d ^ 3 + (2 * d ^ 3 + d ^ 3 + 1 + d ^ 2 * d ^ 2) = 9 * d ^ 3 + d ^ 4 + 1 := by
    rw [hsq]
    have hflat :
        6 * d ^ 3 + (2 * d ^ 3 + d ^ 3 + 1 + d ^ 4) =
          6 * d ^ 3 + 2 * d ^ 3 + d ^ 3 + 1 + d ^ 4 := by
      simp [Nat.add_assoc]
    rw [hflat]
    have hcoef : 6 * d ^ 3 + 2 * d ^ 3 + d ^ 3 = 9 * d ^ 3 := by
      rw [← Nat.add_mul 6 2 (d ^ 3)]
      rw [show (6 + 2 : ℕ) = 8 by rfl]
      exact (Nat.succ_mul 8 (d ^ 3)).symm
    calc
      6 * d ^ 3 + 2 * d ^ 3 + d ^ 3 + 1 + d ^ 4
          = 9 * d ^ 3 + 1 + d ^ 4 := by rw [hcoef]
      _ = 9 * d ^ 3 + d ^ 4 + 1 := by simp [Nat.add_assoc, Nat.add_comm]
  have hle :
      6 * d ^ 3 + (2 * d ^ 3 + d ^ 3 + 1 + d ^ 2 * d ^ 2) ≤ 12 * d ^ 4 := by
    rw [hleft]
    exact hpoly
  simpa [hd] using hle

/--
Total naive work under `fuel ≤ fuelPolyLogSq n` and the combined sparse + phase per-step cap.

Bound: **`12 * (inputLog2 n + 1)⁶`**, i.e. a polynomial in **`inputLog2 n + 1`** of degree `6`.
-/
theorem total_integrated_work_le_twelve_mul_inputLogDim_pow_six (n fuel : ℕ)
    (hf : fuel ≤ fuelPolyLogSq n) :
    fuelTotalWork fuel (integratedCombinedPerStepCap n) ≤ 12 * (inputLogDim n) ^ 6 := by
  calc
    fuelTotalWork fuel (integratedCombinedPerStepCap n)
        ≤ fuelPolyLogSq n * integratedCombinedPerStepCap n := fuelTotalWork_le_of_fuel_bound _ _ _ hf
    _ = (inputLogDim n) ^ 2 * integratedCombinedPerStepCap n := by rw [fuelPolyLogSq_eq_inputLogDim_sq]
    _ ≤ (inputLogDim n) ^ 2 * (12 * (inputLogDim n) ^ 4) :=
        Nat.mul_le_mul_left _ (integratedCombinedPerStepCap_le_twelve_mul_inputLogDim_pow_four n)
    _ = 12 * (inputLogDim n) ^ 6 := by
      let d := inputLogDim n
      calc
        d ^ 2 * (12 * d ^ 4) = d ^ 2 * 12 * d ^ 4 := by rw [Nat.mul_assoc]
        _ = 12 * d ^ 2 * d ^ 4 := by rw [Nat.mul_comm (d ^ 2) 12]
        _ = 12 * (d ^ 2 * d ^ 4) := by rw [Nat.mul_assoc]
        _ = 12 * d ^ (2 + 4) := by rw [← Nat.pow_add]
        _ = 12 * d ^ 6 := rfl

theorem naive_total_le_poly_template (n fuel : ℕ)
    (hf : fuel ≤ fuelPolyLogSq n) :
    fuelTotalWork fuel (6 * (5 + Nat.sqrt n) ^ 2) ≤ (n + 2) ^ 2 * 6 * (5 + Nat.sqrt n) ^ 2 := by
  calc
    fuelTotalWork fuel (6 * (5 + Nat.sqrt n) ^ 2)
        ≤ fuelPolyLogSq n * (6 * (5 + Nat.sqrt n) ^ 2) := fuelTotalWork_le_of_fuel_bound _ _ _ hf
    _ ≤ (n + 2) ^ 2 * (6 * (5 + Nat.sqrt n) ^ 2) := Nat.mul_le_mul_right _ (fuelPolyLogSq_le_sq_succ n)
    _ = (n + 2) ^ 2 * 6 * (5 + Nat.sqrt n) ^ 2 := by rw [Nat.mul_assoc]

/--
Hypothesis bundle for a later `poly (inputLog2 n)` refinement: default cutoff and a
polylog-squared fuel budget. A separate **support invariant** `∀ step, r.length ≤ B`
should be added when you formalize the sparse trace.
-/
structure SearchPipelineHypothesis (n fuel L : ℕ) : Prop where
  cutoff_eq : L = defaultHarmonicCutoff n
  fuel_le : fuel ≤ fuelPolyLogSq n

/-!
### Roadmap (informal)

A **theorem-level** complexity statement needs, in addition to the linear per-step
bounds above, explicit hypotheses such as:

1. **Cutoff policy**: e.g. `L = defaultHarmonicCutoff n`, so `L = O(√n)` and
   `basisCard L = O(n)` in terms of `n`.
2. **Support invariant**: a finite bound `r.length ≤ B(n,L)` after each prune; any
   `poly (inputLog2 n)` claim requires such a `B` of polynomial growth in `inputLog2 n`
   (not proved here for the HQIV native gate).
3. **Fuel**: `fuel` bounded by a function of `n` (e.g. the script’s `max_steps`).

Then `total work ≤ fuel(n) * 6 * B(n, L(n))` is a **rigorous** inequality in this
model; converting it to big-O in `inputLog2 n` is pure algebra on `fuel` and `B`.

### Monolithic factorizer (`monolithic_geometric_factorizer.py`) — Big-`O` packaging

Discrete mirrors live in `Hqiv.Geometry.MonolithicGeometricFactorizer`. Ingredients already isolated:

* `dynamicPrecisionDigits n` is `O(inputLog2 n)`;
* register cap `monolithicMaxRegisters n` is `≤ 128` and `≤ floorCbrt n` in value;
* prune threshold `pruneAgeThreshold` is `O(inputLog2 n)` on candidates `≤ n`;
* real-layer `FracDriftAdequateResources` ties **target bits**, **max steps**, **age × register cap**,
  and `maxFracUncertainty` for float/discrete alignment.

A **theorem-level** runtime bound would sum per-step work (gate, prune, gcd checks) over the main loop
and recursive cofactors after peel, then big-`O` in `inputLogDim n` — **not** closed here. This is the
same “list charges × iterations” pattern as `fuelTotalWork` above.
-/

end Hqiv.Geometry.FactorSearchCostModel
