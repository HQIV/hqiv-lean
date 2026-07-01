import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.ForceCarrier` — the S2 force-carrier amplitude envelope

A force carrier emitted at a source site propagates an **allowed translation amplitude** over the
normalized chain distance `d ∈ [0,1]`. The S2 (great-circle) profile

`A(d) = sin(½π(1 − d))^k`

is the carrier envelope: full amplitude at the source (`d = 0 ⇒ A = 1`), vanishing at the causal
edge (`d = 1 ⇒ A = 0`), and bounded in `[0,1]` everywhere. With an optional exponential range
attenuation `e^{−d/span}` this is the carrier amplitude, and the forward/back/net split is the
emission–absorption decomposition.

Golfed from the physics core of `Hqiv.Physics.ForceCarrierWhip` (the solver-side whip/objective
optimization scaffolding is left in the legacy tree). Mathlib-only; no legacy `Hqiv.*`, no `sorry`,
no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.ForceCarrier

open Real

/-- Raw normalized chain distance before clipping. -/
noncomputable def dNormRaw (n i j : ℕ) : ℝ :=
  (Int.natAbs (Int.ofNat i - Int.ofNat j) : ℝ) / max (1 : ℝ) (n - 1 : ℝ)

/-- Normalized chain distance in `[0,1]` via clipping. -/
noncomputable def dNorm (n i j : ℕ) : ℝ := min 1 (dNormRaw n i j)

theorem dNorm_nonneg (n i j : ℕ) : 0 ≤ dNorm n i j :=
  le_min (by norm_num) (div_nonneg (by positivity) (by positivity))

theorem dNorm_le_one (n i j : ℕ) : dNorm n i j ≤ 1 := min_le_left _ _

theorem dNorm_eq_zero_self (n i : ℕ) : dNorm n i i = 0 := by
  unfold dNorm dNormRaw; simp

/-- Carrier phase `φ = ½π(1 − d)` — full at the source, zero at the causal edge. -/
noncomputable def carrierPhase (n i j : ℕ) : ℝ := (Real.pi / 2) * (1 - dNorm n i j)

theorem carrierPhase_nonneg (n i j : ℕ) : 0 ≤ carrierPhase n i j := by
  unfold carrierPhase; nlinarith [Real.pi_pos, dNorm_le_one n i j]

theorem carrierPhase_le_pi (n i j : ℕ) : carrierPhase n i j ≤ Real.pi := by
  unfold carrierPhase; nlinarith [Real.pi_pos, dNorm_nonneg n i j]

theorem sin_carrierPhase_nonneg (n i j : ℕ) : 0 ≤ Real.sin (carrierPhase n i j) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (carrierPhase_nonneg n i j) (carrierPhase_le_pi n i j)

/-- Integer envelope order from a real tuning parameter (`≥ 1`). -/
noncomputable def envelopeOrder (p : ℝ) : ℕ := max 1 (Int.toNat ⌊p⌋)

theorem envelopeOrder_pos (p : ℝ) : 0 < envelopeOrder p :=
  Nat.succ_le_iff.mp (le_max_left 1 (Int.toNat ⌊p⌋))

/-- **S2 carrier envelope** `sin(½π(1 − d))^k` over the clipped normalized distance. -/
noncomputable def s2Envelope (p : ℝ) (n i j : ℕ) : ℝ :=
  (Real.sin (carrierPhase n i j)) ^ (envelopeOrder p)

theorem s2Envelope_nonneg (p : ℝ) (n i j : ℕ) : 0 ≤ s2Envelope p n i j :=
  pow_nonneg (sin_carrierPhase_nonneg n i j) _

theorem s2Envelope_le_one (p : ℝ) (n i j : ℕ) : s2Envelope p n i j ≤ 1 :=
  pow_le_one₀ (sin_carrierPhase_nonneg n i j) (Real.sin_le_one _)

/-- **Full amplitude at the source:** `A(0) = 1`. -/
theorem s2Envelope_at_source (p : ℝ) (n src : ℕ) : s2Envelope p n src src = 1 := by
  unfold s2Envelope carrierPhase; rw [dNorm_eq_zero_self]; simp

/-- **Vanishes at the causal edge:** `d = 1 ⇒ A = 0`. -/
theorem s2Envelope_at_far_end (p : ℝ) (n i j : ℕ) (hd : dNorm n i j = 1) :
    s2Envelope p n i j = 0 := by
  unfold s2Envelope carrierPhase
  rw [hd]; simp [Nat.ne_of_gt (envelopeOrder_pos p)]

/-- Carrier amplitude with optional exponential range attenuation `e^{−d/span}`. -/
noncomputable def carrierAmplitude (step span p : ℝ) (n src j : ℕ) : ℝ :=
  step * Real.exp (-(dNorm n src j) / span) * s2Envelope p n src j

theorem carrierAmplitude_nonneg (step span p : ℝ) (n src j : ℕ) (hstep : 0 ≤ step) :
    0 ≤ carrierAmplitude step span p n src j :=
  mul_nonneg (mul_nonneg hstep (Real.exp_pos _).le) (s2Envelope_nonneg p n src j)

/-! ## Forward / back / net carrier decomposition -/

/-- Forward (emission) amplitude. -/
noncomputable def ampForward (step span p : ℝ) (n src j : ℕ) : ℝ :=
  carrierAmplitude step span p n src j

/-- Back (absorption) amplitude, scaled by `β`. -/
noncomputable def ampBackward (step span p β : ℝ) (n src j : ℕ) : ℝ :=
  β * carrierAmplitude step span p n src j

/-- Net chain perturbation amplitude `forward − backward`. -/
noncomputable def ampNet (step span p β : ℝ) (n src j : ℕ) : ℝ :=
  ampForward step span p n src j - ampBackward step span p β n src j

theorem ampNet_abs_le_sum (step span p β : ℝ) (n src j : ℕ) :
    |ampNet step span p β n src j| ≤
      |ampForward step span p n src j| + |ampBackward step span p β n src j| :=
  abs_sub _ _

/-- With no back-reaction (`β = 0`) the net amplitude is the pure forward emission. -/
theorem ampNet_beta_zero (step span p : ℝ) (n src j : ℕ) :
    ampNet step span p 0 n src j = ampForward step span p n src j := by
  unfold ampNet ampBackward; ring

end HqivSpine.Physics.ForceCarrier
