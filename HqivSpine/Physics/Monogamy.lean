import HqivSpine.Physics.Exclusion

/-!
# `HqivSpine.Physics.Monogamy` — monogamy of entanglement (CKW) on the shell mode budget

The HQIV second axiom is **informational monogamy**. `Physics.Exclusion` / `SpinStatistics`
read it as Pauli exclusion (no shared carrier state). This module reads it the other way —
as **monogamy of entanglement**: the Coffman–Kundu–Wootters (CKW) three-party tangle
inequality `τ(A:B) + τ(A:C) ≤ τ(A:BC)`, the statement that `A`'s entanglement cannot be
freely shared between two partners.

HQIV weights tangles by a **shell mode-count factor** built from the spine's own derived
budget (`Physics.Exclusion`/`LockIn`):

  `etaMode m = newModes m / cumulativeModes referenceM = 8(m+1) / 120`,

the modes unlocked at shell `m` as a fraction of the lock-in cumulative budget. At the
lock-in shell itself `etaMode referenceM = 40/120 = 1/3` (`etaMode_referenceM`). The
mode weighting preserves CKW (`corrected_monogamy_of_ckw`) and, when the factor is `≤ 1`,
**tightens** the pairwise budget (`corrected_pair_sum_le_uncorrected`) — monogamy made
stricter by the discrete budget.

A φ-augmented factor `etaModePhi m = etaMode m / φ(m)` (with the shell occupation
`φ(m) = 2(m+1)`, `Shell.phi`) gives a **decoherence proxy** that is non-increasing across a
shell step whenever the factor is (`coherenceProxy_step_nonincreasing`): less accessible
coherent pairwise entanglement farther out.

Disentangled onto spine definitions only — Mathlib + spine, no legacy `Hqiv.*`, no `sorry`,
no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-! ## Standard CKW monogamy and the HQIV mode weight -/

/-- **Three-party tangle monogamy (CKW form):** `A`'s pairwise entanglements cannot exceed
its entanglement with the rest, `τ(A:B) + τ(A:C) ≤ τ(A:BC)`. -/
def ckwMonogamy (tauAB tauAC tauA_BC : ℝ) : Prop :=
  tauAB + tauAC ≤ tauA_BC

/-- The lock-in cumulative budget `cumulativeModes referenceM = 120` is positive. -/
theorem cumulativeModes_referenceM_pos : 0 < (cumulativeModes referenceM : ℝ) := by
  have : 0 < cumulativeModes referenceM := by rw [cumulativeModes_eq]; positivity
  exact_mod_cast this

/-- **HQIV mode-count weight** from shell `m` to the lock-in reference shell:
`etaMode m = newModes m / cumulativeModes referenceM`. -/
noncomputable def etaMode (m : ℕ) : ℝ :=
  (newModes m : ℝ) / (cumulativeModes referenceM : ℝ)

theorem etaMode_nonneg (m : ℕ) : 0 ≤ etaMode m :=
  div_nonneg (by positivity) (le_of_lt cumulativeModes_referenceM_pos)

/-- **At the lock-in shell the mode fraction is `1/3`:** `etaMode 4 = 40/120`. -/
theorem etaMode_referenceM : etaMode referenceM = 1 / 3 := by
  unfold etaMode
  rw [show (newModes referenceM : ℝ) = 40 by rw [newModes_eq]; norm_num [show referenceM = 4 from rfl],
      show (cumulativeModes referenceM : ℝ) = 120 by rw [cumulativeModes_eq]; norm_num [show referenceM = 4 from rfl]]
  norm_num

/-- The mode factor is `≤ 1` exactly when the modes unlocked at `m` fit the lock-in budget. -/
theorem etaMode_le_one {m : ℕ} (h : newModes m ≤ cumulativeModes referenceM) :
    etaMode m ≤ 1 := by
  unfold etaMode
  rw [div_le_one cumulativeModes_referenceM_pos]
  exact_mod_cast h

/-! ## Mode-corrected monogamy -/

/-- Mode-corrected pair tangle at shell `m`. -/
noncomputable def correctedPairTangle (m : ℕ) (tau : ℝ) : ℝ :=
  etaMode m * tau

/-- Mode-corrected CKW inequality at shell `m`. -/
def correctedCkwMonogamy (m : ℕ) (tauAB tauAC tauA_BC : ℝ) : Prop :=
  correctedPairTangle m tauAB + correctedPairTangle m tauAC ≤ correctedPairTangle m tauA_BC

/-- **Mode weighting preserves CKW monogamy:** if standard CKW holds, the shell-weighted
inequality holds with the same tangle inputs. -/
theorem corrected_monogamy_of_ckw (m : ℕ) {tauAB tauAC tauA_BC : ℝ}
    (hckw : ckwMonogamy tauAB tauAC tauA_BC) :
    correctedCkwMonogamy m tauAB tauAC tauA_BC := by
  unfold correctedCkwMonogamy correctedPairTangle ckwMonogamy at *
  nlinarith [hckw, etaMode_nonneg m]

/-- **The mode correction tightens the pairwise budget** when the factor is `≤ 1`: the
shell-weighted pairwise tangle sum cannot exceed the uncorrected one. -/
theorem corrected_pair_sum_le_uncorrected (m : ℕ) {tauAB tauAC : ℝ}
    (htau : 0 ≤ tauAB + tauAC) (heta : etaMode m ≤ 1) :
    correctedPairTangle m tauAB + correctedPairTangle m tauAC ≤ tauAB + tauAC := by
  unfold correctedPairTangle
  nlinarith [etaMode_nonneg m, htau, heta]

/-! ## φ-augmented factor and the decoherence proxy -/

/-- The shell occupation `φ(m) = 2(m+1)` is positive (real cast). -/
theorem phi_pos (m : ℕ) : 0 < (phi m : ℝ) := by
  have : 0 < phi m := by unfold phi; omega
  exact_mod_cast this

/-- **φ-augmented shell factor:** the mode weight divided by the shell occupation `φ(m)`. -/
noncomputable def etaModePhi (m : ℕ) : ℝ :=
  etaMode m / (phi m : ℝ)

theorem etaModePhi_nonneg (m : ℕ) : 0 ≤ etaModePhi m :=
  div_nonneg (etaMode_nonneg m) (le_of_lt (phi_pos m))

/-- φ-augmented corrected pair tangle. -/
noncomputable def correctedPairTanglePhi (m : ℕ) (tau : ℝ) : ℝ :=
  etaModePhi m * tau

/-- φ-augmented corrected CKW inequality. -/
def correctedCkwMonogamyPhi (m : ℕ) (tauAB tauAC tauA_BC : ℝ) : Prop :=
  correctedPairTanglePhi m tauAB + correctedPairTanglePhi m tauAC ≤
    correctedPairTanglePhi m tauA_BC

/-- **The φ-augmented weighting also preserves CKW monogamy.** -/
theorem corrected_monogamy_of_ckw_phi (m : ℕ) {tauAB tauAC tauA_BC : ℝ}
    (hckw : ckwMonogamy tauAB tauAC tauA_BC) :
    correctedCkwMonogamyPhi m tauAB tauAC tauA_BC := by
  unfold correctedCkwMonogamyPhi correctedPairTanglePhi ckwMonogamy at *
  nlinarith [hckw, etaModePhi_nonneg m]

/-- **Decoherence proxy** from the φ-augmented budget: accessible coherent pairwise
entanglement at shell `m` for an intrinsic pairwise tangle. -/
noncomputable def coherenceProxy (m : ℕ) (tauPair : ℝ) : ℝ :=
  etaModePhi m * tauPair

/-- **Decoherence monotonicity:** if the φ-augmented factor is non-increasing across a
shell step and the intrinsic pairwise tangle is nonnegative, the coherence proxy is
non-increasing across that step. -/
theorem coherenceProxy_step_nonincreasing (m : ℕ) {tauPair : ℝ}
    (htau : 0 ≤ tauPair) (hstep : etaModePhi (m + 1) ≤ etaModePhi m) :
    coherenceProxy (m + 1) tauPair ≤ coherenceProxy m tauPair := by
  unfold coherenceProxy
  nlinarith [etaModePhi_nonneg m, etaModePhi_nonneg (m + 1), htau, hstep]

end HqivSpine.Physics
