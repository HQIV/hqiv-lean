import HqivSpine.Physics.Shell
import HqivSpine.Physics.NucleonLadder

/-!
# `HqivSpine.Physics.RindlerDetuning` — δ-corrected Rindler surfaces

The operational detuning denominator `1 + (γ/2)m` (with `γ/2 = 1/5` foundation-anchored) already
appears in `NucleonLadder`. This module adds the **global shift** layer mined from legacy
`GlobalDetuning`: a shell-independent correction `δ` linked to the now-slice lapse increment
`Φ + φ·t`, and the corrected effective surface used on every resonance ladder.

Honest scope: the **algebra** of detuned surfaces and geometric steps — not a fitted PDG ratio.
-/

namespace HqivSpine.Physics.RindlerDetuning

open HqivSpine.Physics
open HqivSpine.Physics.NucleonLadder

/-- Shared Rindler slope `c = γ/2 = 1/5`. -/
noncomputable def cRindler : ℝ := gammaHQIV / 2

theorem cRindler_eq_one_fifth : cRindler = 1 / 5 := by
  unfold cRindler; rw [gammaHQIV_eq]; norm_num

/-- **Shell surface** `(m+1)(m+2) = latticeSimplexCount m`. -/
noncomputable def shellSurface (m : ℕ) : ℝ := (latticeSimplexCount m : ℝ)

theorem shellSurface_pos (m : ℕ) : 0 < shellSurface m := by
  unfold shellSurface
  exact_mod_cast latticeSimplexCount_pos m

/-- δ-corrected Rindler denominator `1 + c·m + δ`. -/
noncomputable def rindlerDenWithDelta (δ : ℝ) (m : ℕ) : ℝ :=
  1 + cRindler * (m : ℝ) + δ

theorem rindlerDenWithDelta_zero (m : ℕ) :
    rindlerDenWithDelta 0 m = rindlerDetuning m := by
  unfold rindlerDenWithDelta rindlerDetuning cRindler
  simp

def rindlerDenPos (δ : ℝ) (m : ℕ) : Prop := 0 < rindlerDenWithDelta δ m

/-- **δ-corrected effective surface** `S(m) / (1 + c·m + δ)`. -/
noncomputable def effCorrected (δ : ℝ) (m : ℕ) : ℝ :=
  shellSurface m / rindlerDenWithDelta δ m

theorem effCorrected_zero_eq_detuned (m : ℕ) :
    effCorrected 0 m = detunedSurface m := by
  unfold effCorrected detunedSurface shellSurface
  rw [rindlerDenWithDelta_zero]

theorem effCorrected_pos (δ : ℝ) (m : ℕ) (h : rindlerDenPos δ m) : 0 < effCorrected δ m := by
  unfold effCorrected rindlerDenPos at *
  exact div_pos (shellSurface_pos m) h

theorem rindlerDenPos_zero (m : ℕ) : rindlerDenPos 0 m := by
  unfold rindlerDenPos rindlerDenWithDelta cRindler
  rw [gammaHQIV_eq]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

theorem effCorrected_zero_pos (m : ℕ) : 0 < effCorrected 0 m :=
  effCorrected_pos 0 m (rindlerDenPos_zero m)

/-- Geometric resonance step on corrected surfaces. -/
noncomputable def geometricStepCorrected (δ : ℝ) (m_from m_to : ℕ) : ℝ :=
  effCorrected δ m_from / effCorrected δ m_to

theorem geometricStepCorrected_zero (m_from m_to : ℕ) :
    geometricStepCorrected 0 m_from m_to =
      detunedSurface m_from / detunedSurface m_to := by
  unfold geometricStepCorrected
  rw [effCorrected_zero_eq_detuned, effCorrected_zero_eq_detuned]

/-- **Geometric resonance step** on δ = 0 detuned surfaces (legacy `geometricResonanceStep`). -/
noncomputable def geometricResonanceStep (m_from m_to : ℕ) : ℝ :=
  geometricStepCorrected 0 m_from m_to

theorem geometricResonanceStep_eq_detuned_ratio (m_from m_to : ℕ) :
    geometricResonanceStep m_from m_to =
      detunedSurface m_from / detunedSurface m_to :=
  geometricStepCorrected_zero m_from m_to

/-- Global detuning hypothesis: one scalar observer datum times a coefficient. -/
structure GlobalDetuningHypothesis where
  lambda : ℝ
  obs : ℝ

noncomputable def deltaGlobal (h : GlobalDetuningHypothesis) : ℝ := h.lambda * h.obs

/-- Link to the now-slice lapse increment `Φ + φ·t` (the increment of `N = 1 + Φ + φ·t` above 1). -/
def globalDetuningFromNowSlice (lambda bigPhi phi t : ℝ) : GlobalDetuningHypothesis :=
  { lambda := lambda, obs := bigPhi + phi * t }

theorem deltaGlobal_fromNowSlice (lambda bigPhi phi t : ℝ) :
    deltaGlobal (globalDetuningFromNowSlice lambda bigPhi phi t) = lambda * (bigPhi + phi * t) := rfl

/-- Unified effective surface with global shift. -/
noncomputable def effCorrectedGlobal (h : GlobalDetuningHypothesis) (m : ℕ) : ℝ :=
  effCorrected (deltaGlobal h) m

end HqivSpine.Physics.RindlerDetuning
