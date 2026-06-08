import Hqiv.Physics.Action
import Hqiv.Physics.ActionHolonomyGlue
import Hqiv.Physics.NonAbelianHolonomyMeasureScaffold
import Hqiv.Geometry.RapidityLorentzClosure
import Hqiv.Geometry.SpatialRotationLorentzClosure

/-!
# Strong-interacting discrete action ↔ Poincaré (next discharge layer)

**Discharged:** abelian Wilson–kinetic equivalence; boost-neutral fiber Wilson packaged in
`NonAbelianHolonomyMeasureProgram`; scalar-φ `action_O_Maxwell` rule; partial measure alignment
(Wilson–kinetic + rotated readout).

**Open (named targets):** general flat HQVM kinetic invariance under full `boostDiscretePotential41`;
Haar measure on rotated charts; continuum Wightman Poincaré.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Geometry
open Matrix
open scoped Matrix

noncomputable section

def discretePotentialVec (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) : Fin 4 → ℝ :=
  fun ν => A a ν

def boostDiscretePotential41 (η : ℝ) (A : Fin 8 → Fin 4 → ℝ) : Fin 8 → Fin 4 → ℝ :=
  fun a ν => (boostMatrix41 η *ᵥ discretePotentialVec A a) ν

def isDiscretePotential01Supported (A : Fin 8 → Fin 4 → ℝ) : Prop :=
  ∀ (a : Fin 8), A a 2 = 0 ∧ A a 3 = 0

theorem L_O_phi_coupling_invariant_phi_scalar_boost (η : ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ : ℝ) :
    L_O_phi_coupling A (phiLorentzScalarBoost η φ) = L_O_phi_coupling A φ := by
  simp [L_O_phi_coupling, phiLorentzScalarBoost]

theorem action_O_Maxwell_invariant_phi_scalar_boost (η : ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ : ℝ) :
    action_O_Maxwell A (phiLorentzScalarBoost η φ) = action_O_Maxwell A φ := by
  simp [action_O_Maxwell, action_O_Maxwell_general, L_O_Maxwell, L_O_Maxwell_general,
    L_O_phi_coupling_invariant_phi_scalar_boost η A φ, phiLorentzScalarBoost]

/-- Fiber matrix Wilson + abelian readout already discharged in `NonAbelianHolonomyMeasureProgram`. -/
def BoostCovariantNonabelianWilsonDischarged : Prop :=
  Nonempty NonAbelianHolonomyMeasureProgram

theorem boostCovariantNonabelianWilson_discharged : BoostCovariantNonabelianWilsonDischarged :=
  ⟨nonAbelianHolonomyMeasureProgram_default⟩

/-- **Target (open):** flat HQVM kinetic invariance under `boostDiscretePotential41` (full `Fin 4`). -/
def GeneralFlatHQVMKineticBoostDischarged : Prop := False

theorem generalFlatHQVMKineticBoost_not_discharged : ¬ GeneralFlatHQVMKineticBoostDischarged := id

/-- **Target (open):** embedded `(t,x¹)` kinetic invariance (sub-target of general boost). -/
def Flat01HQVMKineticBoostDischarged : Prop := False

theorem flat01HQVMKineticBoost_not_discharged : ¬ Flat01HQVMKineticBoostDischarged := id

structure DiscreteActionFlatHQVMPoincareDischarged : Prop where
  wilson_kinetic : WilsonKineticPlaquetteEquivalenceDischarged
  boost_wilson : BoostCovariantNonabelianWilsonDischarged
  action_phi_scalar :
    ∀ (η : ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ : ℝ),
      action_O_Maxwell A (phiLorentzScalarBoost η φ) = action_O_Maxwell A φ
  zeta_phase_scalar :
    ∀ (η φ t : ℝ) (m : ℕ),
      polarAngleFromRapidity (phiLorentzScalarBoost η φ) t m = polarAngleFromRapidity φ t m

theorem discreteActionFlatHQVMPoincare_discharged : DiscreteActionFlatHQVMPoincareDischarged where
  wilson_kinetic := wilsonKineticPlaquetteEquivalence_discharged
  boost_wilson := boostCovariantNonabelianWilson_discharged
  action_phi_scalar := action_O_Maxwell_invariant_phi_scalar_boost
  zeta_phase_scalar := polarAngleFromRapidity_invariant_under_phi_scalar_boost

structure FullActionStrongPoincareDischarged : Prop where
  flat_slice : DiscreteActionFlatHQVMPoincareDischarged
  rotated_readout : RotatedFrameReadoutDischarged
  flat01_kinetic_boost : ¬ Flat01HQVMKineticBoostDischarged
  general_kinetic_boost : ¬ GeneralFlatHQVMKineticBoostDischarged

theorem fullActionStrongPoincare_discharged : FullActionStrongPoincareDischarged where
  flat_slice := discreteActionFlatHQVMPoincare_discharged
  rotated_readout := rotatedFrameReadoutDischarged_holds
  flat01_kinetic_boost := flat01HQVMKineticBoost_not_discharged
  general_kinetic_boost := generalFlatHQVMKineticBoost_not_discharged

def MeasureHolonomyAlignmentDischarged : Prop := False

theorem measureHolonomyAlignment_not_discharged : ¬ MeasureHolonomyAlignmentDischarged := id

structure MeasureHolonomyPartialAlignmentDischarged : Prop where
  wilson_kinetic : WilsonKineticPlaquetteEquivalenceDischarged
  rotated_readout : RotatedFrameReadoutDischarged

theorem measureHolonomyPartialAlignment_discharged : MeasureHolonomyPartialAlignmentDischarged where
  wilson_kinetic := wilsonKineticPlaquetteEquivalence_discharged
  rotated_readout := rotatedFrameReadoutDischarged_holds

end

end Hqiv.Physics
