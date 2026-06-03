import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Hqiv.Physics.ComptonHorizonPhase
import Hqiv.Physics.GlobalDetuning

/-!
# Compton phase IR window (`0 < x < θ`)

This module isolates the phase-window statement:

* `θ := horizonQuarterPeriod = π/2`,
* `x := ω * t`,
* `t_IR := θ / ω` (for `ω > 0`).

Then `0 < t < t_IR` implies `0 < x < θ`.

This is the derivation-first hook requested for chemistry/QC participation windows
without fixing geometric binding angles directly.
-/

namespace Hqiv.Physics

noncomputable section

/-- Phase cap `θ` used by the quarter-turn window. -/
noncomputable def phaseTheta : ℝ := Hqiv.horizonQuarterPeriod

/-- Phase variable `x = ω t`. -/
noncomputable def phaseX (ω t : ℝ) : ℝ := ω * t

/-- Frequency-implied IR time window `t_IR = θ / ω` (`ω > 0`). -/
noncomputable def tIR (ω : ℝ) (_hω : 0 < ω) : ℝ := phaseTheta / ω

theorem phaseTheta_eq_pi_div_two : phaseTheta = Real.pi / 2 := by
  unfold phaseTheta
  simpa using horizonQuarterPeriod_eq_pi_div_two

theorem phaseTheta_pos : 0 < phaseTheta := by
  rw [phaseTheta_eq_pi_div_two]
  positivity

theorem phase_window_of_time_window (ω t : ℝ) (hω : 0 < ω) (ht : 0 < t) (htIR : t < tIR ω hω) :
    0 < phaseX ω t ∧ phaseX ω t < phaseTheta := by
  constructor
  · unfold phaseX
    exact mul_pos hω ht
  · unfold phaseX tIR at *
    have hmul' : t * ω < (phaseTheta / ω) * ω := mul_lt_mul_of_pos_right htIR hω
    have hdiv : (phaseTheta / ω) * ω = phaseTheta := by
      field_simp [ne_of_gt hω]
    have hmul : ω * t < phaseTheta := by
      nlinarith [hmul', hdiv]
    simpa [mul_comm] using hmul

/-- Compton-specialized phase variable `x = ω_compton * t`. -/
noncomputable def comptonPhaseX (E ħ t : ℝ) (hħ : ħ ≠ 0) : ℝ :=
  phaseX (omegaCompton E ħ hħ) t

/-- Compton-specialized IR cutoff `t_IR = θ / ω_compton`. -/
noncomputable def comptonTIR (E ħ : ℝ) (hE : 0 < E) (hħ : 0 < ħ) : ℝ :=
  tIR (omegaCompton E ħ (ne_of_gt hħ)) (omegaCompton_pos E ħ hE hħ)

theorem compton_phase_window (E ħ t : ℝ) (hE : 0 < E) (hħ : 0 < ħ) (ht : 0 < t)
    (htIR : t < comptonTIR E ħ hE hħ) :
    0 < comptonPhaseX E ħ t (ne_of_gt hħ) ∧
      comptonPhaseX E ħ t (ne_of_gt hħ) < phaseTheta := by
  simpa [comptonPhaseX, comptonTIR] using
    phase_window_of_time_window (omegaCompton E ħ (ne_of_gt hħ)) t
      (omegaCompton_pos E ħ hE hħ) ht htIR

/-- A bounded participation coordinate from the phase window: `η = x/θ`. -/
noncomputable def phaseParticipationEta (x : ℝ) : ℝ := x / phaseTheta

theorem phaseParticipationEta_mem_unit (x : ℝ) (hx0 : 0 < x) (hxθ : x < phaseTheta) :
    0 < phaseParticipationEta x ∧ phaseParticipationEta x < 1 := by
  have hθ : 0 < phaseTheta := phaseTheta_pos
  constructor
  · unfold phaseParticipationEta
    exact div_pos hx0 hθ
  · unfold phaseParticipationEta
    exact (div_lt_one hθ).2 hxθ

/-- Lapse-time variant: use `timeAngle φ t = φ t` as the phase proxy `x`. -/
theorem phase_window_of_timeAngle (φ t : ℝ) (hφ : 0 < φ) (ht : 0 < t) (hcap : timeAngle φ t < phaseTheta) :
    0 < timeAngle φ t ∧ timeAngle φ t < phaseTheta := by
  constructor
  · simp [timeAngle]
    exact mul_pos hφ ht
  · exact hcap

end
end Hqiv.Physics

