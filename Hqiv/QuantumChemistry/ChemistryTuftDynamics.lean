import Hqiv.QuantumChemistry.DynamicBindingChart
import Hqiv.QuantumChemistry.ElectronicValenceFromTuftChart
import Hqiv.QuantumChemistry.CentreGeometryFromTuft
import Hqiv.QuantumChemistry.H2O
import Hqiv.QuantumChemistry.TorqueTreeEquilibrium

/-!
# Chemistry TUFT dynamics (unified export)

Packages the post-TUFT dynamic spine for the GMTKN55 / curvature-contact
Python chart:

* electronic Compton slots from `TuftShellChart`,
* site energy = trapped Casimir,
* `dynamicBindingCurvatureFeedbackAtXi` and `dynamicComptonEtaSecondOrder`,
* dynamic centre angles and surplus dress without fitted κ_bind.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics

/-- Mean contact ξ on the heavy-hydride Compton triplet. -/
noncomputable def dynamicContactXiHeavyHydride : ℝ :=
  dynamicComptonXiMean dynamicComptonTripletHeavyHydride

theorem dynamicContactXiHeavyHydride_eq_mean :
    dynamicContactXiHeavyHydride =
      (xiOfShell electronicComptonCentreS + xiOfShell electronicComptonCentreP +
          xiOfShell electronicComptonHydrogenS) / 3 := by
  unfold dynamicContactXiHeavyHydride dynamicComptonXiMean dynamicComptonTripletHeavyHydride
  simp [DynamicComptonTriplet.xiAt, DynamicComptonTriplet.shellAt,
    electronicComptonCentreS, electronicComptonCentreP, electronicComptonHydrogenS, xiOfShell]

/-- Dynamic binding feedback at the chemistry contact ξ. -/
noncomputable def dynamicBindingFeedbackAtChemistryContact : ℝ :=
  dynamicBindingCurvatureFeedbackAtXi dynamicContactXiHeavyHydride

/-- Full second-order binding core factor (η₂ × feedback) at chemistry contact. -/
noncomputable def dynamicBindingParticipationAtContact (η_p : ℝ) : ℝ :=
  dynamicComptonEtaSecondOrder η_p (dynamicComptonPShellActive dynamicComptonTripletHeavyHydride) *
    dynamicBindingFeedbackAtChemistryContact

theorem dynamicComptonTripletHeavyHydride_p_active :
    dynamicComptonPShellActive dynamicComptonTripletHeavyHydride = true := by
  native_decide

end Hqiv.QuantumChemistry
