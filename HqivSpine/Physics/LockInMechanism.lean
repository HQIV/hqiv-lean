import HqivSpine.Physics.LockIn
import HqivSpine.Physics.Exclusion
import HqivSpine.Physics.Blackbody
import HqivSpine.Physics.Monogamy
import HqivSpine.Physics.Gravity
import HqivSpine.Algebra.Triality

/-!
# `HqivSpine.Physics.LockInMechanism` — why `referenceM = 4` and what keeps the proton there

This module **bundles** the three proved layers that together explain lock-in at shell `4`:

1. **Selector (gauge-closure balance).** `Physics.LockIn`: unlocked modes `N(m) = 8(m+1)`
   meet sector capacity `C = dim 𝔰𝔬(8) + carrier + base = 40` **only** at `m = 4`. The signed
   `modeDeficit(m) = C − N(m)` is a discrete **restoring drive**: positive below lock-in
   (outward pull to unlock modes), negative above (inward pull to shed surplus), zero at `4`.
   This is the discrete face of `Physics.Gravity`'s horizon ⇄ Planck-pole tug of war.

2. **Inward wall (informational monogamy).** `Physics.Exclusion` / `SpinStatistics`: Pauli
   injectivity and pair conservation forbid collapse to the Planck pole. This earns a
   **degeneracy floor** but does **not** by itself select shell `4` — the chiral content
   (`48` Weyl slots) already fits the cumulative Pauli budget by shell `2`.

3. **Stability (blackbody resonance).** `Physics.Blackbody`: once at `4`, the proton is a
   self-resonant standing mode (`proton_lockin_stable`) — emission fills the horizon, and
   inward collapse to shell `3` is gapped by `ω₃ − ω₄ = 1/20`.

At lock-in the CKW monogamy weight `η_mode(4) = 1/3` (`Physics.Monogamy.etaMode_referenceM`)
is the democratic third carried into mixing readouts.

**Honest scope:** dynamic inner/outer Casimir emergence of `ξ_lock = 5` is discharged in
`Physics.CasimirClosureAction` (`referenceMCasimirClosureAction`). Scalar coupled shell+ξ
slow-manifold closure is in `Physics.JointClosureAction` (`referenceMJointClosureAction`).
Full fast octonion `(v, ξ)` dynamics on `S⁷` remain exploratory (Python probes).

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics

open HqivSpine.Algebra HqivSpine.Foundation

/-! ## Discrete restoring drive -/

/-- Direction of the mode-budget tug of war at shell `m`. -/
inductive LockInDrive
  | outward
  | neutral
  | inward
  deriving DecidableEq, Repr

/-- **Restoring drive** from the signed mode deficit. -/
def lockInDrive (m : ℕ) : LockInDrive :=
  if 0 < modeDeficit m then .outward
  else if modeDeficit m < 0 then .inward
  else .neutral

theorem lockInDrive_eq_outward {m : ℕ} (h : m < referenceM) :
    lockInDrive m = .outward := by
  unfold lockInDrive
  simp only [(modeDeficit_pos_iff m).mpr h, ite_true]

theorem lockInDrive_eq_inward {m : ℕ} (h : referenceM < m) :
    lockInDrive m = .inward := by
  unfold lockInDrive
  split_ifs with hpos hneg
  · linarith [(modeDeficit_pos_iff m).mp hpos, (modeDeficit_neg_iff m).mpr h]
  · rfl
  · have h0 : modeDeficit m = 0 := by linarith
    linarith [(modeDeficit_eq_zero_iff m).mp h0, (modeDeficit_neg_iff m).mpr h]

theorem lockInDrive_eq_neutral {m : ℕ} (h : m = referenceM) :
    lockInDrive m = .neutral := by
  subst h
  unfold lockInDrive
  simp [modeDeficit_referenceM]

theorem lockInDrive_outward_iff (m : ℕ) :
    lockInDrive m = .outward ↔ m < referenceM := by
  constructor
  · intro hdrive
    by_cases h : m < referenceM
    · exact h
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt h) with heq | hgt
      · rw [lockInDrive_eq_neutral heq.symm] at hdrive
        cases hdrive
      · rw [lockInDrive_eq_inward hgt] at hdrive
        cases hdrive
  · intro h
    exact lockInDrive_eq_outward h

theorem lockInDrive_inward_iff (m : ℕ) :
    lockInDrive m = .inward ↔ referenceM < m := by
  constructor
  · intro hdrive
    by_cases h : referenceM < m
    · exact h
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt h) with heq | hlt
      · rw [lockInDrive_eq_neutral heq] at hdrive
        cases hdrive
      · rw [lockInDrive_eq_outward hlt] at hdrive
        cases hdrive
  · intro h
    exact lockInDrive_eq_inward h

theorem lockInDrive_neutral_iff (m : ℕ) :
    lockInDrive m = .neutral ↔ m = referenceM := by
  constructor
  · intro hdrive
    by_cases h : m = referenceM
    · exact h
    · rcases Nat.lt_or_gt_of_ne h with hlt | hgt
      · rw [lockInDrive_eq_outward hlt] at hdrive
        cases hdrive
      · rw [lockInDrive_eq_inward hgt] at hdrive
        cases hdrive
  · intro h
    exact lockInDrive_eq_neutral h

/-- Below lock-in, one outward shell step strictly reduces the deficit. -/
theorem modeDeficit_restores_outward {m : ℕ} (h : m < referenceM) :
    modeDeficit (m + 1) < modeDeficit m :=
  modeDeficit_succ_lt_of_below h

/-- Strictly below lock-in, the deficit stays positive. -/
theorem modeDeficit_pos_of_strictly_below {m : ℕ} (h : m + 1 < referenceM) :
    0 < modeDeficit (m + 1) :=
  (modeDeficit_pos_iff (m + 1)).mpr h

/-- Above lock-in, one inward shell step moves the deficit toward balance. -/
theorem modeDeficit_restores_inward {m : ℕ} (h : referenceM < m) :
    modeDeficit m < modeDeficit (m - 1) ∧ modeDeficit (m - 1) ≤ 0 := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have hsucc : modeDeficit m = modeDeficit (m - 1 + 1) := by
    rw [Nat.sub_add_cancel (Nat.one_le_of_lt hm)]
  rw [hsucc, modeDeficit_succ]
  constructor
  · linarith
  · by_cases heq : m = referenceM + 1
    · rw [show m - 1 = referenceM from by omega, modeDeficit_referenceM]
    · have hgt : referenceM + 1 < m := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt h) (Ne.symm heq)
      have hneg : modeDeficit (m - 1) < 0 := (modeDeficit_neg_iff (m - 1)).mpr (by omega)
      linarith

/-! ## Monogamy floor vs. sector-closure selector -/

/-- The chiral fermion content exactly fills the cumulative budget at shell `2`. -/
theorem cumulativeModes_chiral_at_shell_two :
    cumulativeModes 2 = chiralSlotCount := by
  rw [cumulativeModes_eq, chiralSlotCount_eq_48]

/-- **Pauli floor for chiral content:** enough cumulative slots exist from shell `2` upward. -/
theorem cumulativeModes_ge_chiral_iff (m : ℕ) :
    chiralSlotCount ≤ cumulativeModes m ↔ 2 ≤ m := by
  constructor
  · intro h
    match m with
    | 0 =>
      rw [cumulativeModes_zero, chiralSlotCount_eq_48, carrierMultiplicity_eq_eight] at h
      norm_num at h
    | 1 =>
      rw [cumulativeModes_eq, chiralSlotCount_eq_48] at h
      norm_num at h
    | m + 2 =>
      simp
  · intro hm
    calc
      chiralSlotCount
      _ = cumulativeModes 2 := cumulativeModes_chiral_at_shell_two.symm
      _ ≤ cumulativeModes m := cumulativeModes_strictMono.monotone hm

/-- **Monogamy does not select shell `4`.** The Pauli floor is met two shells earlier than
sector closure; only the per-shell mode balance pins `referenceM`. -/
theorem monogamy_floor_below_lockin :
    chiralSlotCount ≤ cumulativeModes 2 ∧
      newModes 2 < sectorClosureCapacity ∧
      2 < referenceM := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← cumulativeModes_chiral_at_shell_two]
  · rw [newModes_eq, sectorClosureCapacity_eq_forty]; norm_num
  · decide

/-! ## Capstone: the three-layer lock-in mechanism -/

/-- The proved lock-in mechanism at `referenceM = 4`: selector, inward wall, stability,
and the monogamy-weight witness at lock-in. -/
structure ReferenceMLockInMechanism where
  /-- Unique two-sided sector-closure balance (`N(m) = C` only at `m = 4`). -/
  balance :
    (∀ m : ℕ, m < referenceM → newModes m < sectorClosureCapacity) ∧
      newModes referenceM = sectorClosureCapacity ∧
      (∀ m : ℕ, referenceM < m → sectorClosureCapacity < newModes m)
  /-- Informational monogamy forbids Planck-pole collapse. -/
  inward_wall :
    (∀ f : Fin chiralSlotCount → Fin (cumulativeModes 0), ¬ Monogamous f) ∧
      (∀ (c : Charges), netCharge c ≠ 0 → ∀ qs : List ℤ, applyPairs c qs ≠ [])
  /-- Blackbody resonance stability of the proton shell. -/
  stability :
    transitionShellIndex (shellOmega referenceM) = referenceM ∧
      Nat.floor (1 / shellOmega referenceM) = 5 ∧
      0 < shellOmega 3 - shellOmega referenceM
  /-- CKW monogamy mode weight at lock-in is the democratic third. -/
  eta_third : etaMode referenceM = 1 / 3
  /-- Monogamy supplies a Pauli floor by shell `2`, strictly below lock-in. -/
  monogamy_not_selector :
    chiralSlotCount ≤ cumulativeModes 2 ∧
      newModes 2 < sectorClosureCapacity ∧
      2 < referenceM

/-- **The lock-in mechanism is fully discharged** on the spine. -/
def referenceMLockInMechanism : ReferenceMLockInMechanism where
  balance := referenceM_lockin_balance
  inward_wall := spin_statistics_no_collapse
  stability := proton_lockin_stable
  eta_third := etaMode_referenceM
  monogamy_not_selector := monogamy_floor_below_lockin

/-- **Continuous ⇄ discrete bridge (scope record).** Interior curvature `0 < φ < 1` feels
both pulls (`tug_of_war_interior`); the discrete lattice balances them at the unique shell
where `modeDeficit = 0`. -/
theorem lockin_continuous_discrete_parallel {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    expansionFlow φ < φ ∧ φ < gEff φ :=
  tug_of_war_interior hφ0 hφ1

end HqivSpine.Physics
