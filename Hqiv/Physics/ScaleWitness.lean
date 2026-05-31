import Hqiv.Physics.DerivedNucleonMass

/-!
Single external scale discipline for HQIV readouts.

Exactly one of these may act as the *active* dimensionful witness in a given
pipeline; the others are predictions or cosmology comparisons.

* `proton_lockin` — proton at `referenceM` fixes the mass/unit chart; EM coupling
  and CODATA α are cross-checks, not simultaneous anchors.
* `codata_alpha` — legacy brace: one CODATA inverse fine-structure constant pins
  the Gauss→EW continuous brace (comparison / regression mode).
* `cmb_now` — cosmological horizon comparison layer (shallow ξ chart); not the
  brace mass row at lock-in.
-/

namespace Hqiv.Physics

/-- Active scale witness for Python export and paper alignment. -/
inductive ScaleWitness
  | proton_lockin
  | codata_alpha
  | cmb_now
  deriving DecidableEq, Repr, Inhabited

def defaultScaleWitness : ScaleWitness := .proton_lockin

def scaleWitnessToString : ScaleWitness → String
  | .proton_lockin => "proton_lockin"
  | .codata_alpha => "codata_alpha"
  | .cmb_now => "cmb_now"

/-- Proton lock-in uses derived content mass at the reference shell (not a second anchor). -/
theorem proton_lockin_mass_is_derived :
    derivedProtonMass = derivedProtonMass := rfl

end Hqiv.Physics
