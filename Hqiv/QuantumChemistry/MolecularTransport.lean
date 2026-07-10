import Hqiv.QuantumChemistry.PhaseMaterialResponse
import HqivSpine.Physics.DiscreteDiffusion

/-!
# Molecular transport from phase geometry and discrete diffusion

This module is the chemistry-facing bridge opened by
`HqivSpine.Physics.DiscreteDiffusion` and `PhaseGeometryDensity`.

The proved spine object is still finite-patch diffusion on `C_n`: a continuum is not
required.  The chemistry layer below only repackages those discrete readouts into
structural slots used by material response:

* concentration from unit-cell number density;
* Fick-style contact flux and diffusion-limited contact rate;
* Nernst-Einstein-style ionic conductivity with carrier density supplied explicitly.

Avogadro's number appears only in the molar readout; the structural number-density
identity reduces it back to `Z / V_cell`.
-/

namespace Hqiv.QuantumChemistry

open HqivSpine.Physics.Thermodynamics
open HqivSpine.Physics.DiscreteDiffusion

noncomputable section

/-! ## Concentration readouts -/

/-- Molar concentration [mol/cm^3] from molecular number density. -/
noncomputable def molarConcentrationMolPerCm3 (cell : PhaseUnitCell) : ℝ :=
  molecularNumberDensityPerCm3 cell / avogadroNumber

/-- The molar readout is exactly `ρ_mass / molecularWeight`; `N_A` cancels. -/
theorem molarConcentration_eq_massDensity_div_mw (cell : PhaseUnitCell) :
    molarConcentrationMolPerCm3 cell =
      massDensityGPerCm3 cell / cell.molecularWeightAmu := by
  unfold molarConcentrationMolPerCm3 molecularNumberDensityPerCm3
  field_simp [ne_of_gt avogadroNumber_pos]

/-- With positive molecular weight, concentration is also `Z/(V_cell N_A)`. -/
theorem molarConcentration_eq_numberDensity_div_avogadro
    (cell : PhaseUnitCell) (hM : 0 < cell.molecularWeightAmu) :
    molarConcentrationMolPerCm3 cell =
      numberDensityFromUnitCell cell / avogadroNumber := by
  unfold molarConcentrationMolPerCm3
  rw [molecularNumberDensity_eq_numberDensityFromUnitCell cell hM]

/-- Positive phase geometry gives positive molar concentration. -/
theorem molarConcentration_pos_of_pos_lattice (cell : PhaseUnitCell)
    (hZ : 0 < cell.moleculesPerCell) (hM : 0 < cell.molecularWeightAmu)
    (ha : 0 < cell.aAngstrom) (hb : 0 < cell.bAngstrom) (hc : 0 < cell.cAngstrom) :
    0 < molarConcentrationMolPerCm3 cell := by
  unfold molarConcentrationMolPerCm3
  exact div_pos (molecularNumberDensityPerCm3_pos_of_pos_lattice cell hZ hM ha hb hc)
    avogadroNumber_pos

/--
Number density read directly from the Einstein/Brownian MSD slot.

The numerator is the discrete Brownian count readout; the denominator is the phase
cell volume.  When the MSD count is identified with the unit-cell occupancy, this is
exactly the structural number density `Z/V_cell`.
-/
noncomputable def einsteinBrownianNumberDensityPerCm3
    (cell : PhaseUnitCell) (D t : ℝ) : ℝ :=
  einsteinMsdReadout D t / unitCellVolumeCm3 cell

theorem einsteinBrownianNumberDensity_eq_numberDensityFromUnitCell
    (cell : PhaseUnitCell) (D t : ℝ)
    (hcount : einsteinMsdReadout D t = (cell.moleculesPerCell : ℝ)) :
    einsteinBrownianNumberDensityPerCm3 cell D t =
      numberDensityFromUnitCell cell := by
  unfold einsteinBrownianNumberDensityPerCm3 numberDensityFromUnitCell
  rw [hcount]

theorem einsteinBrownianNumberDensity_from_step_eq_numberDensityFromUnitCell
    (cell : PhaseUnitCell) (steps : ℕ) {dt : ℝ} (hdt : 0 < dt)
    (hcount : msdAfterSteps steps = (cell.moleculesPerCell : ℝ)) :
    einsteinBrownianNumberDensityPerCm3 cell (diffusionCoeffFromStep dt) (steps * dt) =
      numberDensityFromUnitCell cell := by
  exact einsteinBrownianNumberDensity_eq_numberDensityFromUnitCell cell
    (diffusionCoeffFromStep dt) (steps * dt)
    (by rw [einsteinMsdReadout_from_step steps hdt, hcount])

/--
Finite in-bracket concentration flow from a diffuse shell density to a contracted
contact density.  The interpolation parameter is structural; no fitted correction
coefficient is introduced.
-/
noncomputable def concentrationFlowSlot (θ diffuse contracted : ℝ) : ℝ :=
  diffuse + θ * (contracted - diffuse)

theorem concentrationFlowSlot_zero (diffuse contracted : ℝ) :
    concentrationFlowSlot 0 diffuse contracted = diffuse := by
  unfold concentrationFlowSlot
  ring

theorem concentrationFlowSlot_one (diffuse contracted : ℝ) :
    concentrationFlowSlot 1 diffuse contracted = contracted := by
  unfold concentrationFlowSlot
  ring

theorem concentrationFlowSlot_between
    {θ diffuse contracted : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hdc : diffuse ≤ contracted) :
    diffuse ≤ concentrationFlowSlot θ diffuse contracted ∧
      concentrationFlowSlot θ diffuse contracted ≤ contracted := by
  unfold concentrationFlowSlot
  have hgap : 0 ≤ contracted - diffuse := sub_nonneg.mpr hdc
  constructor
  · have hmove : 0 ≤ θ * (contracted - diffuse) := mul_nonneg hθ0 hgap
    nlinarith
  · have hremain : 0 ≤ (1 - θ) * (contracted - diffuse) :=
      mul_nonneg (sub_nonneg.mpr hθ1) hgap
    nlinarith

theorem concentrationFlowSlot_nonneg
    {θ diffuse contracted : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hdiff : 0 ≤ diffuse) (hdc : diffuse ≤ contracted) :
    0 ≤ concentrationFlowSlot θ diffuse contracted := by
  exact le_trans hdiff (concentrationFlowSlot_between hθ0 hθ1 hdc).1

/-! ## Fick contact flux and diffusion-limited rate slots -/

/-- One-contact Fick slot: positive left-to-right gradient gives negative oriented flux. -/
noncomputable def diffusionFluxSlot (D nLeft nRight : ℝ) : ℝ :=
  -D * (nRight - nLeft)

theorem diffusionFluxSlot_zero_of_equal (D n : ℝ) :
    diffusionFluxSlot D n n = 0 := by
  unfold diffusionFluxSlot
  ring

theorem diffusionFluxSlot_eq_discrete_fick_two_site
    (D : ℝ) (ρ : ZMod 2 → ℝ) (i : ZMod 2) :
    diffusionFluxSlot D (ρ i) (ρ (i + 1)) =
      fickFlux D ρ i := by
  unfold diffusionFluxSlot fickFlux HqivSpine.Physics.DiscreteHeatCycle.fwdDiff
  ring

/-- Diffusion-limited contact-rate slot: `rate = D · n · contactParticipation`. -/
noncomputable def diffusionLimitedContactRateSlot
    (D numberDensity contactParticipation : ℝ) : ℝ :=
  D * numberDensity * contactParticipation

theorem diffusionLimitedContactRateSlot_nonneg
    {D numberDensity contactParticipation : ℝ}
    (hD : 0 ≤ D) (hn : 0 ≤ numberDensity) (hc : 0 ≤ contactParticipation) :
    0 ≤ diffusionLimitedContactRateSlot D numberDensity contactParticipation := by
  unfold diffusionLimitedContactRateSlot
  positivity

/-- Geometry-fed contact rate using shell-scaled diffusion and unit-cell number density. -/
noncomputable def phaseDiffusionContactRateSlot
    (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ) : ℝ :=
  diffusionLimitedContactRateSlot
    (shellDiffusionCoeff m ν)
    (molecularNumberDensityPerCm3 cell)
    contactParticipation

/-! ## Nernst-Einstein-style conductivity slot -/

/-- Carrier density supplied by a carrier fraction against geometry-derived molecular density. -/
noncomputable def geometryCarrierDensity (cell : PhaseUnitCell) (carrierFraction : ℝ) : ℝ :=
  carrierFraction * molecularNumberDensityPerCm3 cell

/-- Nernst-Einstein-style structural slot: `σ = n q² D / T`. -/
noncomputable def nernstEinsteinConductivitySlot
    (carrierDensity chargeSq D T : ℝ) : ℝ :=
  carrierDensity * chargeSq * D / T

theorem nernstEinsteinConductivitySlot_zero_of_zero_carrier
    (chargeSq D T : ℝ) :
    nernstEinsteinConductivitySlot 0 chargeSq D T = 0 := by
  unfold nernstEinsteinConductivitySlot
  ring

theorem nernstEinsteinConductivitySlot_nonneg
    {carrierDensity chargeSq D T : ℝ}
    (hn : 0 ≤ carrierDensity) (hq : 0 ≤ chargeSq) (hD : 0 ≤ D) (hT : 0 < T) :
    0 ≤ nernstEinsteinConductivitySlot carrierDensity chargeSq D T := by
  unfold nernstEinsteinConductivitySlot
  exact div_nonneg (mul_nonneg (mul_nonneg hn hq) hD) (le_of_lt hT)

/--
Shell Nernst-Einstein slot with `D_m = ν T_m`.

Because `T_m` is the same shell temperature appearing in the denominator, the readout
collapses to the geometry carrier density times the mobility scale `ν`.
-/
noncomputable def shellNernstEinsteinConductivitySlot
    (cell : PhaseUnitCell) (m : ℕ) (ν carrierFraction chargeSq : ℝ) : ℝ :=
  nernstEinsteinConductivitySlot
    (geometryCarrierDensity cell carrierFraction)
    chargeSq
    (shellDiffusionCoeff m ν)
    (shellTemp m)

theorem shellNernstEinsteinConductivitySlot_eq_geometry_mobility
    (cell : PhaseUnitCell) (m : ℕ) (ν carrierFraction chargeSq : ℝ) :
    shellNernstEinsteinConductivitySlot cell m ν carrierFraction chargeSq =
      geometryCarrierDensity cell carrierFraction * chargeSq * ν := by
  unfold shellNernstEinsteinConductivitySlot nernstEinsteinConductivitySlot shellDiffusionCoeff
  field_simp [ne_of_gt (shellTemp_pos m)]

theorem shellNernstEinsteinConductivitySlot_zero_of_zero_carrier
    (cell : PhaseUnitCell) (m : ℕ) (ν chargeSq : ℝ) :
    shellNernstEinsteinConductivitySlot cell m ν 0 chargeSq = 0 := by
  rw [shellNernstEinsteinConductivitySlot_eq_geometry_mobility]
  unfold geometryCarrierDensity
  ring

/-- Transport bridge bundle for chemistry consumers. -/
structure MolecularTransportClosure : Prop where
  molar_concentration_mass :
    ∀ cell : PhaseUnitCell,
      molarConcentrationMolPerCm3 cell = massDensityGPerCm3 cell / cell.molecularWeightAmu
  molar_concentration_geometry :
    ∀ cell : PhaseUnitCell, 0 < cell.molecularWeightAmu →
      molarConcentrationMolPerCm3 cell = numberDensityFromUnitCell cell / avogadroNumber
  equal_density_flux_zero : ∀ D n : ℝ, diffusionFluxSlot D n n = 0
  contact_rate_nonneg :
    ∀ {D numberDensity contactParticipation : ℝ}, 0 ≤ D → 0 ≤ numberDensity →
      0 ≤ contactParticipation →
        0 ≤ diffusionLimitedContactRateSlot D numberDensity contactParticipation
  nernst_zero_carrier :
    ∀ (cell : PhaseUnitCell) (m : ℕ) (ν chargeSq : ℝ),
      shellNernstEinsteinConductivitySlot cell m ν 0 chargeSq = 0
  shell_nernst_reduces :
    ∀ (cell : PhaseUnitCell) (m : ℕ) (ν carrierFraction chargeSq : ℝ),
      shellNernstEinsteinConductivitySlot cell m ν carrierFraction chargeSq =
        geometryCarrierDensity cell carrierFraction * chargeSq * ν
  einstein_density_from_unit_cell :
    ∀ (cell : PhaseUnitCell) (D t : ℝ),
      einsteinMsdReadout D t = (cell.moleculesPerCell : ℝ) →
        einsteinBrownianNumberDensityPerCm3 cell D t = numberDensityFromUnitCell cell
  concentration_flow_between :
    ∀ {θ diffuse contracted : ℝ}, 0 ≤ θ → θ ≤ 1 → diffuse ≤ contracted →
      diffuse ≤ concentrationFlowSlot θ diffuse contracted ∧
        concentrationFlowSlot θ diffuse contracted ≤ contracted

/-- The molecular transport bridge is discharged from phase geometry plus discrete diffusion. -/
theorem molecular_transport_closure : MolecularTransportClosure where
  molar_concentration_mass := molarConcentration_eq_massDensity_div_mw
  molar_concentration_geometry := molarConcentration_eq_numberDensity_div_avogadro
  equal_density_flux_zero := diffusionFluxSlot_zero_of_equal
  contact_rate_nonneg := fun hD hn hc => diffusionLimitedContactRateSlot_nonneg hD hn hc
  nernst_zero_carrier := shellNernstEinsteinConductivitySlot_zero_of_zero_carrier
  shell_nernst_reduces := shellNernstEinsteinConductivitySlot_eq_geometry_mobility
  einstein_density_from_unit_cell := einsteinBrownianNumberDensity_eq_numberDensityFromUnitCell
  concentration_flow_between := fun hθ0 hθ1 hdc => concentrationFlowSlot_between hθ0 hθ1 hdc

end

end Hqiv.QuantumChemistry
