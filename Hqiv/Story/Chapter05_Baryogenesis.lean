import Hqiv.Story.Chapter04_MassLadder
import Hqiv.Physics.BaryogenesisCore

/-!
# Story — Chapter 5: baryogenesis geometry (shells, no paper η)

`m_QCD`, `m_lockin`, temperature ladder, `δ_E` at QCD, and Ω_k lock-in — the discrete section where
baryon-asymmetry *readouts* (e.g. `rapidityCPBias` elsewhere) attach.

Downstream: `Chapter06_Fluid` (effective fluid / plasma–fluid vocabulary).

## Mass-gap narrative

**Input:** `MassGap.step04_harmonicLadderSpectralAnchor` (narrative pin). **Output:**
`MassGap.step05_referenceShellGapWitness` — positive curvature imprint on the lock-in shell and the
Ω_k / temperature identities from `Hqiv.Physics.BaryogenesisCore`.
-/

namespace Hqiv.Story.MassGap

open Hqiv

/-- **Ch 5 → 6.** Lock-in shell imprint is positive; Ω_k calibration and ladder temperatures (`BaryogenesisCore`). -/
def step05_referenceShellGapWitness : Prop :=
  0 < shell_shape_abs m_lockin ∧
    omega_k_at_horizon m_lockin m_lockin = 1 ∧
      T_QCD = T m_QCD ∧ T_lockin = T m_lockin

theorem step05_referenceShellGapWitness_holds : step05_referenceShellGapWitness := by
  refine ⟨shell_shape_abs_pos m_lockin, ?_, T_QCD_eq_ladder, T_lockin_eq_ladder⟩
  exact omega_k_lockin_calibration curvature_integral_m_lockin_pos

theorem step05_of_step04 (_ : step04_harmonicLadderSpectralAnchor) : step05_referenceShellGapWitness :=
  step05_referenceShellGapWitness_holds

end Hqiv.Story.MassGap
