import Hqiv.Physics.HQIVGravityReadoutScalars
import Hqiv.Physics.HQIVPerturbationScaffold
import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.BaryogenesisEtaPaper
import Hqiv.Geometry.OctonionicLightCone

/-!
# Cosmological perturbation readout

Discrete Friedmann and perturbation witness records from the HQIV gravity action
with shell-wise curvature imprint. Tensor modes and non-Gaussianity slots included.
-/

namespace Hqiv.Physics

open Hqiv

/-- Hubble parameter slot from effective G_eff power law at scale factor a. -/
noncomputable def cosmologicalHubbleSlot (a H0 : ℝ) : ℝ :=
  H0 * a ^ (-alpha / 2)

theorem cosmologicalHubbleSlot_a_one (H0 : ℝ) :
    cosmologicalHubbleSlot 1 H0 = H0 := by
  simp [cosmologicalHubbleSlot, alpha_eq_3_5]

/-- Curvature perturbation amplitude from shell_shape at lock-in. -/
noncomputable def curvaturePerturbationAmplitude (m : ℕ) : ℝ :=
  shell_shape m / shell_shape referenceM

theorem curvaturePerturbationAmplitude_referenceM :
    curvaturePerturbationAmplitude referenceM = 1 := by
  unfold curvaturePerturbationAmplitude
  have hpos : 0 < curvatureDensity (referenceM + 1) :=
    curvatureDensity_pos_succ referenceM
  rw [shell_shape_eq_density_succ, div_self (ne_of_gt hpos)]

/-- Tensor-to-scalar ratio slot from horizon monogamy. -/
noncomputable def tensorToScalarRatio : ℝ := gamma_HQIV / 10

theorem tensorToScalarRatio_eq_one_twentyfifth :
    tensorToScalarRatio = (1 : ℝ) / 25 := by
  simp [tensorToScalarRatio, gamma_eq_2_5]
  norm_num

/-- Non-Gaussianity f_NL slot from baryogenesis amplitude (comparison-scale log ratio). -/
noncomputable def nonGaussianityFNL : ℝ :=
  Real.log (eta_paper / 6.10e-10)

structure CosmologicalPerturbationCertificate where
  hubble_a_one : ∀ H0, cosmologicalHubbleSlot 1 H0 = H0
  tensor_ratio : tensorToScalarRatio = (1 : ℝ) / 25
  curvature_at_lockin : curvaturePerturbationAmplitude referenceM = 1

theorem cosmologicalPerturbationCertificate_holds : CosmologicalPerturbationCertificate where
  hubble_a_one := cosmologicalHubbleSlot_a_one
  tensor_ratio := tensorToScalarRatio_eq_one_twentyfifth
  curvature_at_lockin := curvaturePerturbationAmplitude_referenceM

end Hqiv.Physics
