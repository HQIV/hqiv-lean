import HqivSpine.Physics.Shell
import HqivSpine.Physics.Curvature
import HqivSpine.Foundation.Carrier
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `HqivSpine.Physics.ContinuousHorizon` — the continuous horizon coordinate `ξ`

Integer shell index `m` is a **chart sample** on the continuous horizon coordinate

\[
  ξ = m + 1 = φ/2,
\]

while the physics (coupling curves, holonomy phase budget, lock-in identification) lives on
`ξ ∈ ℝ₊`. Mined from legacy `ContinuousXiCoupling` / `ContinuousXiPath`, disentangled to
foundation-anchored spine constants only.

Honest scope: the **symbolic** continuous chart and its link to discrete shells — not a numerical
scan or CODATA fit. Comparison decimals stay in `Frontiers`.
-/

namespace HqivSpine.Physics.ContinuousHorizon

open HqivSpine.Foundation
open HqivSpine.Physics

/-- Continuous horizon coordinate attached to discrete shell `m`. -/
noncomputable def xiOfShell (m : ℕ) : ℝ := (m + 1 : ℝ)

theorem xiOfShell_referenceM : xiOfShell referenceM = 5 := by
  unfold xiOfShell referenceM; norm_num

/-- Continuous auxiliary-field slot: `φ = 2ξ`. -/
noncomputable def phiOfXi (ξ : ℝ) : ℝ := 2 * ξ

theorem phiOfXi_xiOfShell (m : ℕ) : phiOfXi (xiOfShell m) = (phi m : ℝ) := by
  unfold phiOfXi xiOfShell phi
  push_cast
  ring

/-- **Per-shell curvature shape** on the continuous coordinate:
`(1/ξ)(1 + α·log ξ)` with `α = 3/5`. -/
noncomputable def sigmaXi (ξ : ℝ) : ℝ := (1 / ξ) * (1 + alphaEM * Real.log ξ)

theorem sigmaXi_xiOfShell (m : ℕ) : sigmaXi (xiOfShell m) = shellShape m := by
  simp only [sigmaXi, xiOfShell, shellShape, imprintWeight]

/-- O-Maxwell logarithmic running slot on the continuous coordinate. -/
noncomputable def logPhiXi (ξ : ℝ) : ℝ := alphaEM * Real.log (phiOfXi ξ + 1)

/-- Bare GUT inverse coupling `42 = 6·7`, foundation-anchored. -/
noncomputable def invAlphaGUT : ℝ := oneOverAlphaBare

theorem invAlphaGUT_eq : invAlphaGUT = 42 := by
  unfold invAlphaGUT oneOverAlphaBare; norm_num

/-- Continuous high-scale inverse coupling at horizon coordinate `ξ`. -/
noncomputable def oneOverAlphaEffXi (ξ c : ℝ) : ℝ :=
  invAlphaGUT * (1 + c * logPhiXi ξ)

/-- Shape ratio in the Gauss→EW brace. -/
noncomputable def sigmaRatio (ξG ξEW : ℝ) : ℝ := sigmaXi ξG / sigmaXi ξEW

/-- Continuous brace readout `1/α(ξG) · σ(ξG)/σ(ξEW)`. -/
noncomputable def continuousBraceInvAlpha (c ξG ξEW : ℝ) : ℝ :=
  oneOverAlphaEffXi ξG c * sigmaRatio ξG ξEW

/-- Analytic primitive of the curvature density on `ξ > 0`:
`∫ (1/ξ)(1 + α log ξ) dξ = log ξ + (α/2)(log ξ)²`. -/
noncomputable def continuousCurvaturePrimitive (ξ : ℝ) : ℝ :=
  Real.log ξ + (alphaEM / 2) * (Real.log ξ) ^ 2

theorem continuousCurvaturePrimitive_one : continuousCurvaturePrimitive 1 = 0 := by
  simp [continuousCurvaturePrimitive]

/-- Continuous `Ω_k` ratio against a lock-in horizon coordinate. -/
noncomputable def omegaKContinuous (ξ ξLock : ℝ) : ℝ :=
  if continuousCurvaturePrimitive ξLock = 0 then 1
  else continuousCurvaturePrimitive ξ / continuousCurvaturePrimitive ξLock

theorem omegaKContinuous_self (ξ : ℝ) : omegaKContinuous ξ ξ = 1 := by
  unfold omegaKContinuous
  by_cases h : continuousCurvaturePrimitive ξ = 0
  · simp [h]
  · simp [h]

/-- Lock-in coordinate `ξ_lock = referenceM + 1 = 5`. -/
noncomputable def xiLockin : ℝ := xiOfShell referenceM

theorem xiLockin_eq_five : xiLockin = 5 := xiOfShell_referenceM

theorem omegaKContinuous_lockin : omegaKContinuous xiLockin xiLockin = 1 :=
  omegaKContinuous_self xiLockin

theorem continuousCurvaturePrimitive_pos_for_gt_one (ξ : ℝ) (h : 1 < ξ) :
    0 < continuousCurvaturePrimitive ξ := by
  unfold continuousCurvaturePrimitive
  have hlog : 0 < Real.log ξ := Real.log_pos h
  have hα : 0 < alphaEM := by rw [alphaEM_eq]; norm_num
  nlinarith [mul_pos hα (pow_pos hlog 2)]

theorem continuousCurvaturePrimitive_strictMono_gt_one (ξ1 ξ2 : ℝ)
    (h1 : 1 < ξ1) (h2 : ξ1 < ξ2) :
    continuousCurvaturePrimitive ξ1 < continuousCurvaturePrimitive ξ2 := by
  unfold continuousCurvaturePrimitive
  have hξ1_pos : 0 < ξ1 := by linarith
  set y1 : ℝ := Real.log ξ1
  set y2 : ℝ := Real.log ξ2
  set a : ℝ := alphaEM / 2
  have hy1_pos : 0 < y1 := by simpa [y1] using Real.log_pos h1
  have hy12 : y1 < y2 := by simpa [y1, y2] using Real.log_lt_log hξ1_pos h2
  have ha_pos : 0 < a := by subst a; rw [alphaEM_eq]; norm_num
  have hfactor_pos : 0 < (y2 - y1) * (1 + a * (y1 + y2)) := by
    have hdiff_pos : 0 < y2 - y1 := sub_pos.mpr hy12
    have hsum_pos : 0 < 1 + a * (y1 + y2) := by nlinarith
    exact mul_pos hdiff_pos hsum_pos
  have hfactor_eq :
      y2 + a * y2 ^ 2 - (y1 + a * y1 ^ 2) = (y2 - y1) * (1 + a * (y1 + y2)) := by ring
  have hdiff_pos : 0 < y2 + a * y2 ^ 2 - (y1 + a * y1 ^ 2) := by rwa [hfactor_eq]
  have hmain : y1 + a * y1 ^ 2 < y2 + a * y2 ^ 2 := sub_pos.mp hdiff_pos
  simpa [y1, y2, a] using hmain

/-- Preferred half-step on the continuous axis (`7/2`): early-closed-shell anchor. -/
noncomputable def xiHalfStep : ℝ := (imaginaryDim : ℝ) / 2

theorem xiHalfStep_eq : xiHalfStep = 7 / 2 := by
  unfold xiHalfStep
  rw [imaginaryDim_eq_seven]
  norm_num

end HqivSpine.Physics.ContinuousHorizon
