import Hqiv.Physics.TuftElectroweakBosonReadout
import Hqiv.Physics.WeakHiggsFromOMaxwellScaffold
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Algebra.AnomalyCancellation

/-!
# Higgs self-coupling and κ modifier readout

Discrete-action coefficients for λ₃ (trilinear), λ₄ (quartic), and
Higgs coupling modifiers κ_W, κ_Z, κ_γ, κ_b, κ_τ from the TUFT closure.
-/

namespace Hqiv.Physics

open Hqiv.Algebra

/-! ## Higgs potential coefficients -/

/-- Quartic λ from scalar closure: `m_H² / (2 v²)` at lock-in. -/
noncomputable def higgsQuarticLambda : ℝ :=
  m_H_derived ^ 2 / (2 * vacuumExpectationValueScalar ^ 2)

/-- Trilinear λ₃ slot: `2 m_H / v` (discrete portal normalization). -/
noncomputable def higgsTrilinearLambda3 : ℝ :=
  2 * m_H_derived / vacuumExpectationValueScalar

theorem higgsTrilinearLambda3_eq_two_mH_over_v :
    higgsTrilinearLambda3 = 2 * m_H_derived / vacuumExpectationValueScalar := rfl

/-! ## Coupling modifiers -/

/-- κ_W: W–Higgs coupling modifier from geometric sin²θ_W. -/
noncomputable def kappaW : ℝ :=
  Real.sqrt sin2ThetaWGeometricLockin

/-- κ_Z: Z–Higgs coupling modifier. -/
noncomputable def kappaZ : ℝ :=
  Real.sqrt (1 - sin2ThetaWGeometricLockin)

/-- κ_γ: photon–Higgs effective coupling (discrete EM trace). -/
noncomputable def kappaGamma : ℝ :=
  1 + gamma_HQIV / 8

/-- κ_b: bottom Yukawa modifier from down-type quark ladder. -/
noncomputable def kappaB : ℝ :=
  1 + gamma_HQIV / (4 * 5)

/-- κ_τ: tau Yukawa modifier from lepton resonance step. -/
noncomputable def kappaTau : ℝ :=
  1 + gamma_HQIV / (4 * 3)

theorem kappaGamma_eq_twentyone_twentieths :
    kappaGamma = (21 : ℝ) / 20 := by
  simp [kappaGamma, gamma_eq_2_5]
  norm_num

/-! ## Ward identity / anomaly embedding -/

structure HiggsCouplingCertificate where
  anomaly_free : smAnomalyFreeOneGeneration
  three_gen_sum : ∑ g : Fin 3, anomalyCoeff g = 0
  lambda3_pos : 0 < higgsTrilinearLambda3

def higgsCouplingCertificate_holds : HiggsCouplingCertificate where
  anomaly_free := sm_anomaly_free_one_generation
  three_gen_sum := anomaly_coeff_sum_three_generations
  lambda3_pos := by
    unfold higgsTrilinearLambda3
    rw [boson_witness_m_H]
    have hT : 0 < T m_lockin := T_pos m_lockin
    unfold vacuumExpectationValueScalar ewScalarSectorQuantumLift vacuumExpectationValue
      bosonClosureShell outerClosureMonogamyLift gammaDerived outerHorizonSurface
      chargedLeptonSmDoubletCount trialityOrder referenceM qcdShell stepsFromQCDToLockin
      latticeStepCount alpha
    positivity

end Hqiv.Physics
