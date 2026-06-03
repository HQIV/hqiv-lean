import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Physics.NuclearOutsideTemperatureDynamics

/-!
# Dynamic proton / neutron readout

This module builds the first `nucleon(p,n)` layer after the nuclear outside-temperature
dynamics are locked down.

The construction is intentionally thin:

* `NucleonFlavor` chooses the already-derived constituent channel (`uud` or `udd`).
* `NucleonEnvironment` carries the common shell, ξ, nuclear well depth, and bonded/free flag.
* The same ξ-dependent own-binding and well contribution are subtracted from both flavors.

Therefore the absolute proton/neutron masses can move with outside curvature and the nuclear
well, but the p–n splitting is still the derived constituent/isospin split until an explicit
flavor-dependent weak or EM tipping layer is added.
-/

namespace Hqiv.Physics

noncomputable section

/-- Proton/neutron flavor tag for the dynamic nucleon function. -/
inductive NucleonFlavor
  | proton
  | neutron
  deriving DecidableEq, Repr

/-- Environment shared by a proton/neutron readout. -/
structure NucleonEnvironment where
  /-- Binding shell for the nucleon's own composite trace. -/
  shell : ℕ := referenceM
  /-- Continuous horizon coordinate. `xiLockin = 5` is the calibrated lock-in point. -/
  ξ : ℝ := xiLockin
  /-- Nuclear well depth supplied by the caustic stack / embedding. -/
  wellDepth : ℝ := 0
  /-- If true, the well depth participates; if false this is a free branch. -/
  bonded : Bool := false

/-- Constituent channel selected by flavor. -/
noncomputable def nucleonConstituentEnergy : NucleonFlavor → ℝ
  | .proton => protonConstituentEnergy
  | .neutron => neutronConstituentEnergy

/-- Common own-binding at ξ from the outside-curvature temperature module. -/
noncomputable def nucleonOwnBindingInEnvironment
    (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  nucleonOwnBindingAtXi env.shell env.ξ c

/-- Nuclear well contribution: bonded branches subtract the positive well slot. -/
noncomputable def nucleonWellContribution (env : NucleonEnvironment) : ℝ :=
  if env.bonded then max 0 env.wellDepth else 0

/--
Dynamic proton/neutron mass readout.

This is the first `nucleon(p,n)` function: constituent energy minus the common
temperature-modulated own-binding and the common bonded well contribution.
-/
noncomputable def nucleonMassAtXi
    (flavor : NucleonFlavor) (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  nucleonConstituentEnergy flavor -
    nucleonOwnBindingInEnvironment env c -
      nucleonWellContribution env

/-- Convenience aliases for the dynamic p/n readouts. -/
noncomputable def protonMassAtXi (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  nucleonMassAtXi .proton env c

noncomputable def neutronMassAtXi (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  nucleonMassAtXi .neutron env c

theorem protonMassAtXi_eq (env : NucleonEnvironment) (c : ℝ) :
    protonMassAtXi env c =
      protonConstituentEnergy -
        nucleonOwnBindingInEnvironment env c -
          nucleonWellContribution env := rfl

theorem neutronMassAtXi_eq (env : NucleonEnvironment) (c : ℝ) :
    neutronMassAtXi env c =
      neutronConstituentEnergy -
        nucleonOwnBindingInEnvironment env c -
          nucleonWellContribution env := rfl

/--
The dynamic environment does not split p from n by itself.

The p–n gap remains the derived constituent/isospin split because own-binding and
well-depth are shared. β± and weak widths are separate slots.
-/
theorem neutron_proton_gap_preserved_at_xi
    (env : NucleonEnvironment) (c : ℝ) :
    neutronMassAtXi env c - protonMassAtXi env c = derivedDeltaM := by
  unfold neutronMassAtXi protonMassAtXi nucleonMassAtXi nucleonConstituentEnergy
  rw [constituent_isospin_splitting]
  ring

/-- Free lock-in environment: no nuclear well, shell `referenceM`, ξ = lock-in. -/
def freeLockinNucleonEnvironment : NucleonEnvironment where
  shell := referenceM
  ξ := xiLockin
  wellDepth := 0
  bonded := false

/-- Bonded environment builder with a supplied caustic well depth. -/
def bondedNucleonEnvironmentAtXi (shell : ℕ) (ξ wellDepth : ℝ) : NucleonEnvironment where
  shell := shell
  ξ := ξ
  wellDepth := wellDepth
  bonded := true

/-- β− overlap slot for a dynamic environment. -/
noncomputable def betaMinusOverlapForEnvironment (env : NucleonEnvironment) : ℝ :=
  betaMinusOverlapAtXi env.ξ

/-- β+ structural mirror slot. Weak widths remain outside this mass readout. -/
noncomputable def betaPlusOverlapForEnvironment (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  nucleonOwnBindingInEnvironment env c

theorem betaMinusOverlapForEnvironment_eq (env : NucleonEnvironment) :
    betaMinusOverlapForEnvironment env = betaMinusOverlapAtXi env.ξ := rfl

end

end Hqiv.Physics
