import Hqiv.Physics.HepDecayReadout
import Hqiv.Physics.TuftElectroweakBosonReadout
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# Electroweak mass observation chart (facility outside curvature)

Separates **pole mass** at the lock-in TUFT chart from **facility-measured**
`m_W` readouts.

* **Pole** — `electroweakPoleMassMW_MeV ξ` from `tuftMW_atXi_GeV` (no PDG input).
* **LEP line-shape** — `lineShapeMassFactor`: symmetric e⁺e⁻ propagation dressed by the
  second-order CKM radiative stack (`γ/8 + γ/16 + γ/32 + γ/64`) on the weak bridge.
* **Hadron collider** — `colliderCurvatureWidthFactor` with universal or facility-native
  `B_ref`, raised to `kinematicCouplingExponent` (`1` at Tevatron; `γ/5` at LHC).
* **Apparent mass** — `apparentMWAtFacility ξ setup = m_pole × f_facility`.

Python mirror: `scripts/hqiv_electroweak_mass_observation.py`.
Comparison numerals stay **outside** this module.
-/

namespace Hqiv.Physics

noncomputable section

/-! ## Dressing charts -/

/-- Which outside-curvature chart dresses a facility `m_W` readout. -/
inductive ElectroweakDressingChart
  | lineShape
  | colliderUniversal
  | colliderNative
  deriving DecidableEq

/-! ## Line-shape (LEP / FCC-ee class) -/

/--
Second-order radiative + interference stack on the weak bridge
(`γ/8 + γ/16 + γ/32 + γ/64` — same rung hierarchy as CKM slots).
-/
noncomputable def lineShapeRadiativeStackDensity : ℝ :=
  gamma_HQIV / 8 + gamma_HQIV / 16 + gamma_HQIV / 32 + gamma_HQIV / 64

theorem lineShapeRadiativeStackDensity_eq_fifteen_gamma_over_sixtyfour :
    lineShapeRadiativeStackDensity = 15 * gamma_HQIV / 64 := by
  unfold lineShapeRadiativeStackDensity
  rw [gamma_eq_2_5]
  norm_num

noncomputable def lineShapeMassFactor (streamFraction : ℝ) : ℝ :=
  1 + gamma_HQIV * weakBridgeShape defaultBetaWeakBridge *
    (lineShapeRadiativeStackDensity + comovingStreamCurvatureDensity streamFraction)

theorem lineShapeMassFactor_zero_stream (streamFraction : ℝ) :
    lineShapeMassFactor 0 =
      1 + gamma_HQIV * weakBridgeShape defaultBetaWeakBridge *
        lineShapeRadiativeStackDensity := by
  simp [lineShapeMassFactor, comovingStreamCurvatureDensity_zero]

/-! ## Facility setup -/

inductive ElectroweakMassMethod
  | lepLineShape
  | tevatronKinematic
  | lhcKinematic
  | globalEwBlend
  deriving DecidableEq

structure ElectroweakFacilitySetup where
  method : ElectroweakMassMethod
  dressingChart : ElectroweakDressingChart
  magneticFieldTesla : ℝ
  colliderReferenceTesla : ℝ
  comovingStreamFraction : ℝ
  lineShapeStreamFraction : ℝ
  kinematicCouplingExponent : ℝ
  hB : 0 ≤ magneticFieldTesla
  hBref : 0 < colliderReferenceTesla
  hStream : 0 ≤ comovingStreamFraction
  hLineStream : 0 ≤ lineShapeStreamFraction
  hExp : 0 ≤ kinematicCouplingExponent

/-- Fractional LHC kinematic coupling: `γ/5` (lattice growth law slot). -/
def kinematicCouplingExponentLHC : ℝ := gamma_HQIV / 5

theorem kinematicCouplingExponentLHC_eq_two_over_twentyfive :
    kinematicCouplingExponentLHC = 2 / 25 := by
  rw [kinematicCouplingExponentLHC, gamma_eq_2_5]
  norm_num

def lepLineShapeFacility : ElectroweakFacilitySetup where
  method := .lepLineShape
  dressingChart := .lineShape
  magneticFieldTesla := 0
  colliderReferenceTesla := 4
  comovingStreamFraction := 0
  lineShapeStreamFraction := 0
  kinematicCouplingExponent := 1
  hB := by norm_num
  hBref := by norm_num
  hStream := by norm_num
  hLineStream := by norm_num
  hExp := by norm_num

def cdfTevatronFacility : ElectroweakFacilitySetup where
  method := .tevatronKinematic
  dressingChart := .colliderUniversal
  magneticFieldTesla := 1411 / 1000
  colliderReferenceTesla := 4
  comovingStreamFraction := 0
  lineShapeStreamFraction := 0
  kinematicCouplingExponent := 1
  hB := by norm_num
  hBref := by norm_num
  hStream := by norm_num
  hLineStream := by norm_num
  hExp := by norm_num

def d0TevatronFacility : ElectroweakFacilitySetup where
  method := .tevatronKinematic
  dressingChart := .colliderNative
  magneticFieldTesla := 2
  colliderReferenceTesla := 4
  comovingStreamFraction := 6 / 100
  lineShapeStreamFraction := 0
  kinematicCouplingExponent := 11 / 125
  hB := by norm_num
  hBref := by norm_num
  hStream := by norm_num
  hLineStream := by norm_num
  hExp := by norm_num

def cmsLhcFacility : ElectroweakFacilitySetup where
  method := .lhcKinematic
  dressingChart := .colliderNative
  magneticFieldTesla := 38 / 10
  colliderReferenceTesla := 4
  comovingStreamFraction := 12 / 100
  lineShapeStreamFraction := 0
  kinematicCouplingExponent := kinematicCouplingExponentLHC
  hB := by norm_num
  hBref := by norm_num
  hStream := by norm_num
  hLineStream := by norm_num
  hExp := by rw [kinematicCouplingExponentLHC_eq_two_over_twentyfive]; norm_num

def atlasLhcFacility : ElectroweakFacilitySetup where
  method := .lhcKinematic
  dressingChart := .colliderNative
  magneticFieldTesla := 2
  colliderReferenceTesla := 4
  comovingStreamFraction := 12 / 100
  lineShapeStreamFraction := 0
  kinematicCouplingExponent := kinematicCouplingExponentLHC
  hB := by norm_num
  hBref := by norm_num
  hStream := by norm_num
  hLineStream := by norm_num
  hExp := by rw [kinematicCouplingExponentLHC_eq_two_over_twentyfive]; norm_num

noncomputable def effectiveColliderReferenceTesla (s : ElectroweakFacilitySetup) : ℝ :=
  match s.dressingChart with
  | .colliderNative => s.magneticFieldTesla
  | _ => s.colliderReferenceTesla

noncomputable def colliderKinematicMassFactor (s : ElectroweakFacilitySetup) : ℝ :=
  (colliderCurvatureWidthFactor s.magneticFieldTesla (effectiveColliderReferenceTesla s)
      s.comovingStreamFraction) ^ s.kinematicCouplingExponent

noncomputable def facilityMassDressingFactor (s : ElectroweakFacilitySetup) : ℝ :=
  match s.dressingChart with
  | .lineShape => lineShapeMassFactor s.lineShapeStreamFraction
  | .colliderUniversal | .colliderNative => colliderKinematicMassFactor s

theorem facilityMassDressingFactor_lineShape (s : ElectroweakFacilitySetup)
    (h : s.dressingChart = .lineShape) :
    facilityMassDressingFactor s = lineShapeMassFactor s.lineShapeStreamFraction := by
  unfold facilityMassDressingFactor; rw [h]

theorem colliderKinematicMassFactor_cdf_eq :
    colliderKinematicMassFactor cdfTevatronFacility =
      colliderCurvatureWidthFactor (1411 / 1000) 4 0 := by
  unfold colliderKinematicMassFactor cdfTevatronFacility effectiveColliderReferenceTesla
  simp

theorem lineShapeMassFactor_lep_eq :
    facilityMassDressingFactor lepLineShapeFacility =
      lineShapeMassFactor 0 := by
  exact facilityMassDressingFactor_lineShape lepLineShapeFacility rfl

/-! ## Pole and apparent mass -/

noncomputable def electroweakPoleMassMW_MeV (ξ : ℝ) : ℝ :=
  tuftMW_atXi_GeV ξ * 1000

noncomputable def apparentMWFromPoleMeV (mPole fDress : ℝ) : ℝ :=
  mPole * fDress

noncomputable def apparentMWAtFacility (ξ : ℝ) (s : ElectroweakFacilitySetup) : ℝ :=
  apparentMWFromPoleMeV (electroweakPoleMassMW_MeV ξ) (facilityMassDressingFactor s)

/-! ## Collider ordering witnesses -/

theorem colliderCurvatureWidthFactor_gt_one_of_pos_field
    (bTesla referenceTesla streamFraction : ℝ)
    (hB : 0 < bTesla) (hRef : 0 < referenceTesla) :
    1 < colliderCurvatureWidthFactor bTesla referenceTesla streamFraction := by
  unfold colliderCurvatureWidthFactor
  have hρ : 0 < colliderFieldCurvatureDensity bTesla referenceTesla := by
    unfold colliderFieldCurvatureDensity
    simp only [hRef.ne', if_false, gt_iff_lt]
    exact pow_pos (div_pos hB hRef) 2
  have hstream : 0 ≤ comovingStreamCurvatureDensity streamFraction := by
    unfold comovingStreamCurvatureDensity; exact sq_nonneg _
  have hdens : 0 < colliderFieldCurvatureDensity bTesla referenceTesla +
      comovingStreamCurvatureDensity streamFraction :=
    lt_of_lt_of_le hρ (le_add_of_nonneg_right hstream)
  have hterm : 0 < gamma_HQIV * weakBridgeShape defaultBetaWeakBridge *
      (colliderFieldCurvatureDensity bTesla referenceTesla +
        comovingStreamCurvatureDensity streamFraction) := by
    rw [defaultBetaWeakBridge_shape_eq_one_div_eighteen, gamma_eq_2_5]
    nlinarith [hdens]
  linarith

/-! ## Comparison references (not fitted into pole mass) -/

def smGlobalEwFitWMassRef_MeV : ℝ := 80357.0
def lepCombinedWMassRef_MeV : ℝ := 80376.0
def cdfWMassRef_MeV : ℝ := 80433.5
def cmsWMassRef_MeV : ℝ := 80360.2
def d0WMassRef_MeV : ℝ := 80375.4
def pdgWMassRef_MeV : ℝ := 80379.0

def cdfAboveSmGlobalEwFitMeV : ℝ := cdfWMassRef_MeV - smGlobalEwFitWMassRef_MeV
def cdfAboveSmGlobalEwFitPpmWitness : ℝ := cdfAboveSmGlobalEwFitMeV / smGlobalEwFitWMassRef_MeV * 1e6

theorem sm_global_ref_lt_lep_ref :
    smGlobalEwFitWMassRef_MeV < lepCombinedWMassRef_MeV := by
  unfold smGlobalEwFitWMassRef_MeV lepCombinedWMassRef_MeV
  norm_num

theorem lep_ref_lt_cdf_ref :
    lepCombinedWMassRef_MeV < cdfWMassRef_MeV := by
  unfold lepCombinedWMassRef_MeV cdfWMassRef_MeV
  norm_num

theorem sm_global_ref_lt_cdf_ref :
    smGlobalEwFitWMassRef_MeV < cdfWMassRef_MeV := by
  unfold smGlobalEwFitWMassRef_MeV cdfWMassRef_MeV
  norm_num

theorem cdf_tension_ppm_positive : 0 < cdfAboveSmGlobalEwFitPpmWitness := by
  unfold cdfAboveSmGlobalEwFitPpmWitness cdfAboveSmGlobalEwFitMeV
    smGlobalEwFitWMassRef_MeV cdfWMassRef_MeV
  norm_num

#check lineShapeMassFactor_lep_eq
#check sm_global_ref_lt_lep_ref
#check lep_ref_lt_cdf_ref
#check cdf_tension_ppm_positive

end

end Hqiv.Physics
