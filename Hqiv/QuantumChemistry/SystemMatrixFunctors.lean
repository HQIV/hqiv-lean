import HqivSpine.Physics.SystemMatrixFunctors
import HqivSpine.Physics.GeneratorDependentCoupling
import Hqiv.QuantumChemistry.SecondOrderEffects
import Hqiv.QuantumChemistry.CoupledRelaxation

/-!
# Chemistry bridge for system-matrix functors

Wires the spine `SystemMatrixFunctors` and `GeneratorDependentCoupling` layers into
the QuantumChemistry namespace used by the lightcone-chemistry-extent paper.
Continuous SO(8) / Beltrami-contact dresses and plane-local colour filters are the
formal second-order objects that act on the ⟨bra|ket⟩ carrier rather than as free
scalar multipliers.
-/

namespace Hqiv.QuantumChemistry

open HqivSpine.Physics
open HqivSpine.Physics.SystemMatrixFunctors
open HqivSpine.Physics.GeneratorDependentCoupling
open HqivSpine.Physics.NestedHopfBinding

noncomputable section

/-- Re-export: system matrix carrying ⟨bra|ket⟩ network data. -/
abbrev ChemistrySystemMatrix := SystemMatrix

/-- Re-export: continuous off-lattice dress from Hopf shape × contact/ladder kernels. -/
abbrev chemistryOffLatticeDress := offLatticeDress

/-- Re-export: continuous-symmetry readout on a system matrix. -/
abbrev chemistryContinuousSymmetryReadout := continuousSymmetryReadout

/-- Re-export: continuous preferred-axis plane-local colour dress. -/
abbrev chemistryPreferredAxisPlaneLocalDress := preferredAxisPlaneLocalDress

/-- Re-export: heteronuclear half-channel dress (boolean special case of preferred-axis). -/
abbrev chemistryHeteronuclearHalfChannelDress := heteronuclearHalfChannelDress

/-- Beltrami contact on the lock-in (heavy) coupling shell. -/
def lockinBeltramiContact (c : ℝ := 1) : BeltramiContactPoint :=
  beltramiContactAtShell lockinCouplingShell c

/-- Continuous contact winding interpolated between strong (`n=2`) and heavy (`n=3`)
by a unit-interval participation `t ∈ [0,1]`:
`ξ(t) = 2 + t`.  This is the off-lattice path between two stable coupling shells. -/
noncomputable def interpolatedContactWinding (t : ℝ) : ℝ := 2 + t

/-- Off-lattice dress along the strong→heavy contact path at chart `referenceM`. -/
noncomputable def strongToHeavyOffLatticeDress (t c : ℝ) : ℝ :=
  offLatticeDress (interpolatedContactWinding t) referenceM c

/-- At the heavy endpoint `t = 1` the continuous winding is the integer Hopf lock-in
winding `3`, so the continuous Hopf shape equals the proved `3/5`. -/
theorem interpolatedContactWinding_heavy :
    interpolatedContactWinding 1 = 3 := by
  unfold interpolatedContactWinding; norm_num

theorem strongToHeavy_hopf_at_heavy :
    hopfFibrationShapeCont (interpolatedContactWinding 1) = (3 : ℝ) / 5 := by
  rw [interpolatedContactWinding_heavy]
  change hopfFibrationShapeCont (3 : ℕ) = _
  rw [hopfFibrationShapeCont_of_nat, hopfFibrationShape_three]

/-- Bridge: scalar second-order readout with the off-lattice dress as the factor.
When the dress is `1`, this recovers the base (proved neutrality of
`secondOrderReadout_unit`). -/
theorem secondOrderReadout_of_offLattice
    (base ξ : ℝ) (mChart : ℕ) (c : ℝ) :
    secondOrderReadout base (offLatticeDress ξ mChart c) =
      base * offLatticeDress ξ mChart c := rfl

/-- Bridge: heteronuclear half-channel dress as a second-order factor.
Homonuclear / zero-η limits recover the base readout. -/
theorem secondOrderReadout_heteronuclear_identity
    (base : ℝ) :
    secondOrderReadout base (heteronuclearHalfChannelDress false 0) = base := by
  rw [heteronuclearHalfChannelDress_homonuclear, secondOrderReadout_unit]

/-- Bridge: continuous preferred-axis dress recovers the base at vanishing axis. -/
theorem secondOrderReadout_preferredAxis_identity
    (base eta : ℝ) :
    secondOrderReadout base (preferredAxisPlaneLocalDress eta 0) = base := by
  rw [preferredAxisPlaneLocalDress_zero_axis, secondOrderReadout_unit]

end

end Hqiv.QuantumChemistry
