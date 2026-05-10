import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Hqiv

open BigOperators

/-!
# Baryogenesis geometry (curvature + ladder; no paper η)

Discrete shells **m_QCD**, **m_lockin**, the temperature ladder **T_QCD** / **T_lockin**,
**δE** at the QCD shell, and **Ω_k** lock-in calibration are **independent** of the paper
`eta_paper` constant. That value is quarantined in `Hqiv.Physics.BaryogenesisEtaPaper`.
η-at-horizon definitions that multiply curvature ratios by `eta_paper` are in
`Hqiv.Physics.BaryogenesisWitness`.

**Definitions (pure math, no paper η):**
- **m_QCD**, **m_lockin**: shell indices from the discrete ladder.
- **T_QCD**, **T_lockin**: T(m) = 1/(m+1) in natural units.
- **Baryogenesis shells**: the discrete step range used in the paper chain.
- **Lock-in Ω_k:** `omega_k_at_horizon m_lockin m_lockin = 1` at positive curvature integral.
-/

/-- **QCD transition shell index** (lattice-derived). T_QCD = T(m_QCD). -/
def m_QCD : Nat := qcdShell

/-- **Lockin shell index** (lattice-derived). referenceM = qcdShell + stepsFromQCDToLockin;
    T_lockin = T(m_lockin); the η witness (in `BaryogenesisWitness`) locks in at this shell. -/
def m_lockin : Nat := referenceM

/-- **Lockin is a few discrete steps after QCD.** -/
theorem m_lockin_eq_m_QCD_add_steps : m_lockin = m_QCD + stepsFromQCDToLockin := by
  unfold m_lockin m_QCD referenceM; rfl

/-- **Baryogenesis shells:** discrete steps from m_QCD through lockin and a few steps after.
    Shells m with m_QCD ≤ m ≤ m_lockin + stepsAfterLockin. -/
def baryogenesisShells : Finset Nat :=
  Finset.Icc m_QCD (m_lockin + stepsAfterLockin)

/-- **T_QCD:** QCD transition temperature on the lattice ladder. T_QCD = T(m_QCD) = 1/(m_QCD+1). -/
noncomputable def T_QCD : ℝ := T m_QCD

/-- **T_lockin:** Lockin temperature on the lattice ladder. T_lockin = T(m_lockin) = 1/(m_lockin+1). -/
noncomputable def T_lockin : ℝ := T m_lockin

/-- **T_QCD is on the temperature ladder.** -/
theorem T_QCD_eq_ladder : T_QCD = T m_QCD := rfl

/-- **T_lockin is on the temperature ladder.** -/
theorem T_lockin_eq_ladder : T_lockin = T m_lockin := rfl

/-- **T_QCD in closed form:** T_QCD = 1/(m_QCD+1). -/
theorem T_QCD_closed : T_QCD = 1 / (m_QCD + 1 : ℝ) := T_eq m_QCD

/-- **T_lockin in closed form:** T_lockin = 1/(m_lockin+1). -/
theorem T_lockin_closed : T_lockin = 1 / (m_lockin + 1 : ℝ) := T_eq m_lockin

/-- **Both temperatures are positive** (on the ladder). -/
theorem T_QCD_pos : 0 < T_QCD := T_pos m_QCD
theorem T_lockin_pos : 0 < T_lockin := T_pos m_lockin

/-- **δE at QCD shell:** the curvature imprint at the QCD transition sets the scale for the
    normalization shared with Ω_k and (in the witness module) η. -/
theorem deltaE_at_QCD_shell : deltaE m_QCD = curvature_norm_combinatorial * shell_shape m_QCD := rfl

/-- **m_lockin equals referenceM** (paper-derived: lockin at the reference horizon). -/
theorem m_lockin_eq_referenceM : m_lockin = referenceM := rfl

/-- **Lockin shell has positive curvature integral.** -/
theorem curvature_integral_m_lockin_pos : 0 < curvature_integral m_lockin := by
  rw [m_lockin_eq_referenceM]; exact curvature_integral_ref_pos

/-- **Vital (geometry):** Ω_k at the lockin horizon equals 1 (first-principles ratio). -/
theorem omega_k_lockin_calibration (h_lockin : 0 < curvature_integral m_lockin) :
    omega_k_at_horizon m_lockin m_lockin = 1 :=
  omega_k_at_horizon_self m_lockin h_lockin

/-- Ω_k lock-in at `m_lockin` plus ladder temperature IDs (hypothesis type for wiring lemmas). -/
def baryogenesis_vital_readout : Prop :=
  omega_k_at_horizon m_lockin m_lockin = 1 ∧ T_QCD = T m_QCD ∧ T_lockin = T m_lockin

/-- **QCD/lockin temperatures + Ω_k lock-in** without any paper-η line. -/
theorem baryogenesis_vital_omega_T_no_eta : baryogenesis_vital_readout := by
  refine ⟨omega_k_lockin_calibration curvature_integral_m_lockin_pos,
    T_QCD_eq_ladder, T_lockin_eq_ladder⟩

end Hqiv
