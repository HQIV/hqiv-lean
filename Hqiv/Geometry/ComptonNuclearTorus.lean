import Hqiv.Geometry.NuclearTorusPerturbation
import Hqiv.Physics.ComptonIRWindow

/-!
# Compton/IR-window sourced nuclear torus angles

Build `NuclearTorusConfig` directly from Compton phase coordinates `x_i = ω_i t_i`,
with per-channel constraints `0 < t_i < t_IR,i`, and prove each linking angle lies in
the HQIV phase window `0 < x_i < θ` (`θ = horizonQuarterPeriod`).
-/

namespace Hqiv.Geometry

open Hqiv

/-- Per-channel Compton-sourced angle `x = ω_compton(E,ħ) * t`. -/
noncomputable def comptonLinkedAngle (E ħ t : ℝ) (hħ : 0 < ħ) : ℝ :=
  Hqiv.Physics.comptonPhaseX E ħ t (ne_of_gt hħ)

/-- Build a `NuclearTorusConfig` from three Compton-sourced phase angles. -/
noncomputable def comptonLinkedNuclearTorusConfig
    (E : Fin 3 → ℝ) (ħ : ℝ) (hħ : 0 < ħ) (t : Fin 3 → ℝ) : NuclearTorusConfig where
  linkingAngles := fun i => comptonLinkedAngle (E i) ħ (t i) hħ

theorem comptonLinkedAngle_mem_window
    (E ħ t : ℝ) (hE : 0 < E) (hħ : 0 < ħ) (ht : 0 < t)
    (htIR : t < Hqiv.Physics.comptonTIR E ħ hE hħ) :
    0 < comptonLinkedAngle E ħ t hħ ∧
      comptonLinkedAngle E ħ t hħ < Hqiv.Physics.phaseTheta := by
  unfold comptonLinkedAngle
  simpa using Hqiv.Physics.compton_phase_window E ħ t hE hħ ht htIR

theorem comptonLinkedNuclearTorusConfig_angle_mem_window
    (E : Fin 3 → ℝ) (ħ : ℝ) (hħ : 0 < ħ) (t : Fin 3 → ℝ)
    (hE : ∀ i : Fin 3, 0 < E i)
    (ht : ∀ i : Fin 3, 0 < t i)
    (htIR : ∀ i : Fin 3, t i < Hqiv.Physics.comptonTIR (E i) ħ (hE i) hħ)
    (i : Fin 3) :
    0 < (comptonLinkedNuclearTorusConfig E ħ hħ t).linkingAngles i ∧
      (comptonLinkedNuclearTorusConfig E ħ hħ t).linkingAngles i < Hqiv.Physics.phaseTheta := by
  simpa [comptonLinkedNuclearTorusConfig] using
    comptonLinkedAngle_mem_window (E i) ħ (t i) (hE i) hħ (ht i) (htIR i)

theorem comptonLinkedNuclearTorusConfig_angles_pos
    (E : Fin 3 → ℝ) (ħ : ℝ) (hħ : 0 < ħ) (t : Fin 3 → ℝ)
    (hE : ∀ i : Fin 3, 0 < E i)
    (ht : ∀ i : Fin 3, 0 < t i)
    (htIR : ∀ i : Fin 3, t i < Hqiv.Physics.comptonTIR (E i) ħ (hE i) hħ) :
    ∀ i : Fin 3, 0 < (comptonLinkedNuclearTorusConfig E ħ hħ t).linkingAngles i := by
  intro i
  exact (comptonLinkedNuclearTorusConfig_angle_mem_window E ħ hħ t hE ht htIR i).1

theorem comptonLinkedNuclearTorusConfig_angles_lt_phaseTheta
    (E : Fin 3 → ℝ) (ħ : ℝ) (hħ : 0 < ħ) (t : Fin 3 → ℝ)
    (hE : ∀ i : Fin 3, 0 < E i)
    (ht : ∀ i : Fin 3, 0 < t i)
    (htIR : ∀ i : Fin 3, t i < Hqiv.Physics.comptonTIR (E i) ħ (hE i) hħ) :
    ∀ i : Fin 3, (comptonLinkedNuclearTorusConfig E ħ hħ t).linkingAngles i < Hqiv.Physics.phaseTheta := by
  intro i
  exact (comptonLinkedNuclearTorusConfig_angle_mem_window E ħ hħ t hE ht htIR i).2

end Hqiv.Geometry

