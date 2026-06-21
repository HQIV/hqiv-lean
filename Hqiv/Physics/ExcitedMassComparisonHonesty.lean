import Hqiv.Physics.HadronMassReadout
import Hqiv.Physics.HepDecayReadout
import Hqiv.Physics.FanoResonance

/-!
# Excited-state comparison honesty (quarantine layer)

Formalizes when PDG listed mass uncertainties support a meaningful $n_\\sigma$ pull
versus when scale-free $|\\Delta|/M$ is the honest metric at discrete readout granularity.
-/

namespace Hqiv.Physics

/-- Readout-resolution floor on comparison $\\sigma$: $1\\%$ of mass matches TUFT chart granularity. -/
noncomputable def comparisonSigmaReadoutFloor : ℝ := 1 / 100

theorem comparisonSigmaReadoutFloor_eq_one_hundredth :
    comparisonSigmaReadoutFloor = (1 : ℝ) / 100 := rfl

/-- Listed PDG $\\sigma$ is narrower than readout resolution — $n_\\sigma$ is ill-posed. -/
def listedSigmaBelowReadoutResolution (sigmaMeV massMeV : ℝ) : Prop :=
  0 < sigmaMeV ∧ sigmaMeV < comparisonSigmaReadoutFloor * massMeV

/-- Effective comparison band uses $\\max(\\sigma,\\,0.01M)$; not a claim about experimental precision. -/
noncomputable def comparisonSigmaEffective (sigmaMeV massMeV : ℝ) : ℝ :=
  max sigmaMeV (comparisonSigmaReadoutFloor * massMeV)

theorem comparisonSigmaEffective_ge_floor (sigmaMeV massMeV : ℝ) :
    comparisonSigmaReadoutFloor * massMeV ≤ comparisonSigmaEffective sigmaMeV massMeV := by
  unfold comparisonSigmaEffective
  exact le_max_right _ _

theorem comparisonSigmaEffective_eq_sigma_when_generous
    (sigmaMeV massMeV : ℝ) (h : comparisonSigmaReadoutFloor * massMeV ≤ sigmaMeV) :
    comparisonSigmaEffective sigmaMeV massMeV = sigmaMeV := by
  simp [comparisonSigmaEffective, max_eq_left h]

/-- Light isoscalar vector content weight exceeds isovector ($\\rho$): structural $\\omega$--$\\rho$ split. -/
theorem tuftIsoscalarVectorExceedsIsovectorWeight :
    tuftMesonLightExcitationWeight < tuftMesonIsoscalarExcitationWeight := by
  rw [tuftMesonIsoscalarExcitationWeight_eq]
  have hw : (0 : ℝ) < tuftMesonLightExcitationWeight := by
    rw [tuftMesonLightExcitationWeight_eq_eight_twenty_sevenths]
    norm_num
  nlinarith [gamma_eq_2_5, hw]

/-- Pure orbital baryon excitation at $\\ell=2$ carries unit coupling — $N(1440)$ granularity is chart-native. -/
theorem tuftExcitationCouplingWeight_zero_two_positive_eq_one :
    tuftExcitationCouplingWeight 0 2 false = 1 := by
  simp [tuftExcitationCouplingWeight]

#check comparisonSigmaReadoutFloor
#check listedSigmaBelowReadoutResolution
#check tuftIsoscalarVectorExceedsIsovectorWeight

end Hqiv.Physics
