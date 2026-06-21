import Hqiv.Physics.ElectroweakMassObservation

/-!
# Accelerator outside dressing (hadron spectroscopy ledger)

Extends the Earth-surface gravity/kinetic closure (`K_mass_chart` from
`NuclearOutsideTemperatureDynamics`) with **per-facility** kinematic dressing:
magnetic-field curvature density, comoving beam/stream fraction, and (for $e^+e^-$
factories) the line-shape radiative stack.

The **pole / chart mass** from TUFT discharge is unchanged; apparent mass at a
facility is
`m_apparent = m_pole × K_gravity × K_facility` when a species route assigns a
non-trivial facility chart.

Python mirror: `scripts/hqiv_accelerator_outside_dressing.py`.
Witness bundle: `data/accelerator_outside_dressing.json`.
-/

namespace Hqiv.Physics

noncomputable section

/-! ## Facility routes for spectroscopy comparison -/

/-- Which outside environment dresses an apparent mass readout. -/
inductive HadronMassFacilityRoute
  | earthSurface
  | cmsLhc
  | atlasLhc
  | lhcb
  | besCharmonium
  | lepLineShape
  deriving DecidableEq

def hadronMassFacilityRouteToSetup : HadronMassFacilityRoute → ElectroweakFacilitySetup
  | .earthSurface => lepLineShapeFacility
  | .cmsLhc => cmsLhcFacility
  | .atlasLhc => atlasLhcFacility
  | .lhcb => cmsLhcFacility
  | .besCharmonium => lepLineShapeFacility
  | .lepLineShape => lepLineShapeFacility

/-- Earth tabulation uses unity facility dressing; collider routes use the EW facility factor. -/
noncomputable def spectroscopyAcceleratorDressingFactor (route : HadronMassFacilityRoute) : ℝ :=
  match route with
  | .earthSurface => 1
  | r => facilityMassDressingFactor (hadronMassFacilityRouteToSetup r)

theorem spectroscopyAcceleratorDressingFactor_earth_eq_one :
    spectroscopyAcceleratorDressingFactor .earthSurface = 1 := rfl

theorem spectroscopyAcceleratorDressingFactor_cmsLhc_eq_facility_factor :
    spectroscopyAcceleratorDressingFactor .cmsLhc =
      facilityMassDressingFactor cmsLhcFacility := rfl

/-! ## Apparent mass at facility -/

/-- Apparent mass after gravity chart increment and optional accelerator dressing. -/
noncomputable def apparentHadronMassMeV
    (mPoleMeV kGravityChart kFacility : ℝ) : ℝ :=
  mPoleMeV * kGravityChart * kFacility

theorem apparentHadronMassMeV_earth_chart (mPoleMeV kGravityChart : ℝ) :
    apparentHadronMassMeV mPoleMeV kGravityChart 1 = mPoleMeV * kGravityChart := by
  simp [apparentHadronMassMeV]

theorem apparentHadronMassMeV_facility_increment (mPoleMeV kFacility : ℝ) :
    apparentHadronMassMeV mPoleMeV 1 kFacility = mPoleMeV * kFacility := by
  simp [apparentHadronMassMeV]

/-- Increment from accelerator dressing alone: $m_{\mathrm{pole}}(K_{\mathrm{facility}}-1)$. -/
noncomputable def acceleratorDressingIncrementMeV (mPoleMeV kFacility : ℝ) : ℝ :=
  mPoleMeV * (kFacility - 1)

theorem acceleratorDressingIncrementMeV_earth (mPoleMeV : ℝ) :
    acceleratorDressingIncrementMeV mPoleMeV 1 = 0 := by
  simp [acceleratorDressingIncrementMeV]

end

end Hqiv.Physics
