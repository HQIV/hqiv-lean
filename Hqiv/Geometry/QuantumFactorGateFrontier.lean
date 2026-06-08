import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Quantum-style gate frontier scaffold for factor candidates

This module formalizes a Lean-side scaffold matching the current Python exploration:

1. Build `#Q := floor(sqrt n)` and doubled span `2#Q` across a reflection point.
2. Represent qbit-sim registers whose codes map to angle slots of possible cofactors.
3. Apply deterministic gate-like transforms on register arrays (phase + reflection + paired phase).
4. Iterate shell steps up to `sqrt n`.

The intent is *structural verification* of the search pipeline shape before any claim of
physical or quantum speedup.
-/

namespace Hqiv.Geometry
namespace QuantumFactorGateFrontier

/-- Primary shell-cardinality proxy `#Q`: floor square root of the target shell. -/
def qCard (n : ℕ) : ℕ := Nat.sqrt n

/-- Guarded nonempty span used by angle slot logic. -/
def qSpan (n : ℕ) : ℕ := max 1 (qCard n)

/-- Reflected doubled span `2#Q` used for counterpart tracking. -/
def doubleQSpan (n : ℕ) : ℕ := 2 * qSpan n

/-- Modulus used for reflection arithmetic (always positive). -/
def reflectionMod (n : ℕ) : ℕ := max 1 (doubleQSpan n)

theorem reflectionMod_pos (n : ℕ) : 0 < reflectionMod n := by
  simp [reflectionMod]

/-- Reflection across the midpoint of the doubled span (computed modulo the span). -/
def reflectSlot (n s : ℕ) : ℕ :=
  let m := reflectionMod n
  (m - 1 - (s % m)) % m

/-- Angle slot picked from the primary `#Q` interval. -/
def angleSlot (n code : ℕ) : ℕ :=
  code % qSpan n

/--
Candidate cofactor map from angle slot.

Values are in `[2, #Q]` when `#Q > 1`; degenerate shells map to `2`.
-/
def cofactorCandidateFromSlot (n slot : ℕ) : ℕ :=
  let q := qSpan n
  if _hq : q ≤ 1 then
    2
  else
    2 + (slot % (q - 1))

/--
Cofactor candidates never exceed the primary shell span once `#Q ≥ 2`
(the degenerate case `qSpan n = 1` is excluded by `2 ≤ qSpan n`).
-/
theorem cofactorCandidate_le_qSpan (n slot : ℕ) (hq : 2 ≤ qSpan n) :
    cofactorCandidateFromSlot n slot ≤ qSpan n := by
  unfold cofactorCandidateFromSlot
  have hn1 : ¬ qSpan n ≤ 1 := by omega
  simp [hn1]
  have hpos : 0 < qSpan n - 1 := Nat.sub_pos_of_lt (Nat.lt_of_succ_le hq)
  have hmod := Nat.mod_lt slot hpos
  have hle := Nat.le_sub_one_of_lt hmod
  omega

/-- Classical qbit-sim register: bit width plus integer code. -/
structure QBitRegister where
  qBits : ℕ
  code : ℕ
deriving Repr, DecidableEq

/-- Width modulus for a register. -/
def registerMod (r : QBitRegister) : ℕ := 2 ^ r.qBits

theorem registerMod_pos (r : QBitRegister) : 0 < registerMod r := by
  simp [registerMod]

/-- Normalized code in `[0, 2^qBits)`. -/
def normalizeCode (r : QBitRegister) : ℕ :=
  r.code % registerMod r

theorem normalizeCode_lt_modulus (r : QBitRegister) :
    normalizeCode r < registerMod r := by
  exact Nat.mod_lt _ (registerMod_pos r)

/-- Register-induced angle slot in the doubled reflected span. -/
def registerAngleSlot (n : ℕ) (r : QBitRegister) : ℕ :=
  normalizeCode r % reflectionMod n

/-- Coupled counterpart angle slot across the reflection point. -/
def counterpartAngleSlot (n : ℕ) (r : QBitRegister) : ℕ :=
  reflectSlot n (registerAngleSlot n r)

/-- Gate 1: phase shift (mod `2^qBits`). -/
def gatePhase (shift : ℕ) (r : QBitRegister) : QBitRegister where
  qBits := r.qBits
  code := (normalizeCode r + shift) % registerMod r

/-- Gate 2: reflection in register code-space. -/
def gateReflect (r : QBitRegister) : QBitRegister where
  qBits := r.qBits
  code := (registerMod r - 1 - normalizeCode r) % registerMod r

/--
Three-gate bundle respecting paired counterparts:
phase, reflection, then phase on the reflected branch.
-/
def gateBundle (step : ℕ) (r : QBitRegister) : List QBitRegister :=
  [gatePhase step r, gateReflect r, gatePhase (step + 1) (gateReflect r)]

/-- One shell step over a frontier of registers. -/
def stepRegisters (step : ℕ) (regs : List QBitRegister) : List QBitRegister :=
  ((regs.foldr (fun r acc => gateBundle step r ++ acc) [])).eraseDups

/--
Simulation loop with explicit shell index.

`simulateFrom n fuel step regs` performs `fuel` updates starting at shell `step`.
-/
def simulateFrom : ℕ → ℕ → ℕ → List QBitRegister → List (List QBitRegister)
  | _n, 0, _step, regs => [regs]
  | n, fuel + 1, step, regs =>
      let next := stepRegisters step regs
      regs :: simulateFrom n fuel (step + 1) next

/-- Shell iteration budget: run updates up to `sqrt n`. -/
def stepBudget (n : ℕ) : ℕ := Nat.sqrt n

/-- Full gate simulation trace up to `sqrt n`. -/
def runGateSimulation (n : ℕ) (init : List QBitRegister) : List (List QBitRegister) :=
  simulateFrom n (stepBudget n) 0 init

theorem simulateFrom_length (n fuel step : ℕ) (regs : List QBitRegister) :
    (simulateFrom n fuel step regs).length = fuel + 1 := by
  induction fuel generalizing step regs with
  | zero =>
      simp [simulateFrom]
  | succ fuel ih =>
      simp [simulateFrom, ih]

theorem runGateSimulation_length (n : ℕ) (init : List QBitRegister) :
    (runGateSimulation n init).length = stepBudget n + 1 := by
  simpa [runGateSimulation] using simulateFrom_length n (stepBudget n) 0 init

/-- Candidate list extracted from current register frontier via angle slots. -/
def candidateList (n : ℕ) (regs : List QBitRegister) : List ℕ :=
  regs.map (fun r => cofactorCandidateFromSlot n (registerAngleSlot n r))

/-
Priority theorem bundle for the current gate-frontier interpretation.
-/

/-- Divisor-pair reflection law on shell `n`: whenever `d ∣ n`, its reflected pair is `n / d`. -/
theorem divisorPair_reflection (n d : ℕ) (hd : d ∣ n) :
    d * (n / d) = n := by
  exact Nat.mul_div_cancel' hd

/-- The reflection branch is always generated by the gate bundle. -/
theorem reflectionRegister_generated (step : ℕ) (r : QBitRegister) :
    gateReflect r ∈ gateBundle step r := by
  simp [gateBundle]

/--
If the slot-level reflection model aligns with `gateReflect`, then the counterpart slot is
explicitly generated by one bundle step.
-/
theorem counterpartAngle_generated_if_aligned
    (n step : ℕ) (r : QBitRegister)
    (hAlign : registerAngleSlot n (gateReflect r) = counterpartAngleSlot n r) :
    ∃ r' ∈ gateBundle step r, registerAngleSlot n r' = counterpartAngleSlot n r := by
  refine ⟨gateReflect r, ?_, ?_⟩
  · exact reflectionRegister_generated step r
  · simp [hAlign]

/-- Inside the strict primary slot window, cofactor candidates cover `2 + slot` exactly. -/
theorem cofactorCandidate_slot_exact
    (n slot : ℕ)
    (hq : 2 ≤ qSpan n)
    (hslot : slot < qSpan n - 1) :
    cofactorCandidateFromSlot n slot = slot + 2 := by
  have hq_not_le1 : ¬ qSpan n ≤ 1 := by omega
  have hmod : slot % (qSpan n - 1) = slot := Nat.mod_eq_of_lt hslot
  simp [cofactorCandidateFromSlot, hq_not_le1, hmod, Nat.add_comm]

/--
Arity coverage on the `#Q` shell:
every candidate size `k` in `[2, qSpan n]` is represented by some angle slot.
-/
theorem arityCoverage_exists_slot
    (n k : ℕ)
    (hk2 : 2 ≤ k)
    (hkQ : k ≤ qSpan n) :
    ∃ slot, cofactorCandidateFromSlot n slot = k := by
  by_cases hq : qSpan n ≤ 1
  · have : False := by omega
    exact False.elim this
  · let slot := k - 2
    refine ⟨slot, ?_⟩
    have hq2 : 2 ≤ qSpan n := by omega
    have hslot : slot < qSpan n - 1 := by
      dsimp [slot]
      omega
    have hexact := cofactorCandidate_slot_exact n slot hq2 hslot
    dsimp [slot] at hexact
    calc
      cofactorCandidateFromSlot n (k - 2) = (k - 2) + 2 := hexact
      _ = k := Nat.sub_add_cancel hk2

/-- Reflection gate preserves register width and therefore stays in the same shell state-space. -/
theorem gateReflect_preserves_qBits (r : QBitRegister) :
    (gateReflect r).qBits = r.qBits := by
  simp [gateReflect]

/--
Periodicity witness for gate-frontier bundle shape:
bundle cardinality is shell-step invariant, giving an explicit detectable lag-1 pattern.
-/
theorem gateBundle_periodicity_lag1 (step : ℕ) (r : QBitRegister) :
    (gateBundle (step + 1) r).length = (gateBundle step r).length := by
  simp [gateBundle]

/--
Abstract advantage contract:
if a reflection-aware hit-rate lower bound strictly exceeds uniform hit-rate, the method
has measurable advantage over uniform sampling.
-/
theorem reflectionAdvantage_of_bounds
    (uniformHitRate reflectedHitRate : ℚ)
    (hAdv : uniformHitRate < reflectedHitRate) :
    reflectedHitRate - uniformHitRate > 0 := by
  linarith

end QuantumFactorGateFrontier
end Hqiv.Geometry

