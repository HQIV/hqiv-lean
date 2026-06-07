import Hqiv.Physics.HomogeneousCurvatureSecondOrder

/-!
# Phase geometry → mass density → local curvature ρ

Condensed-phase readout without macroscopic atom counting:

1. **Preferred allotrope** (e.g.\ ice Ih for H₂O) fixes a unit-cell geometry witness.
2. **Mass density** ρ_mass = Z·M/(N_A·V_cell) from lattice constants and formula weight.
3. **Curvature density** ρ_curv = clamp(ρ_mass / ρ_liquid_ref) feeds
   `homogeneousCurvatureBudgetAtXi` and second-order κ₆ feedback on melt / binding.

Python mirror: `scripts/hqiv_phase_geometry_density.py`.
Melt witness: `scripts/hqiv_thermodynamic_phase_from_tp.py` (`material_scales_bulk_h2o`).

**Orbital extension:** planetary mass + radius + encounter distance supply local curvature
ρ via inverse-square weighting (Earth bulk dominates; dilute limit at large r).
Feeds the same `homogeneousCurvatureBudgetAtXi` spine as condensed phase — no shell-4 pin.
Lean bridge: `Hqiv.Physics.OrbitalFlybyScaffold`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics

/-- Crystalline Bravais class for unit-cell volume (geometry witness only). -/
inductive CrystalSystem
  | hexagonal
  | cubic
  | orthorhombic
  deriving DecidableEq, Repr

/-- Unit-cell geometry witness: lattice constants in ångström, Z molecules per cell. -/
structure PhaseUnitCell where
  allotrope : String
  moleculesPerCell : ℕ
  molecularWeightAmu : ℝ
  aAngstrom : ℝ
  bAngstrom : ℝ
  cAngstrom : ℝ
  crystal : CrystalSystem

/-- Ångström → centimetre (crystallographic convention). -/
noncomputable def angstromToCm : ℝ := 1e-8

/-- Avogadro constant (g/mol per molecule count). -/
noncomputable def avogadroNumber : ℝ := 6.02214076e23

theorem angstromToCm_pos : 0 < angstromToCm := by unfold angstromToCm; norm_num

theorem avogadroNumber_pos : 0 < avogadroNumber := by unfold avogadroNumber; norm_num

/-- Unit-cell volume in cm³ from lattice constants. -/
noncomputable def unitCellVolumeCm3 (cell : PhaseUnitCell) : ℝ :=
  let a := cell.aAngstrom * angstromToCm
  let b := cell.bAngstrom * angstromToCm
  let c := cell.cAngstrom * angstromToCm
  match cell.crystal with
  | .hexagonal => Real.sqrt 3 / 2 * a * a * c
  | .cubic => a * a * a
  | .orthorhombic => a * b * c

/-- Mass density ρ [g/cm³] = Z·M / (N_A·V). -/
noncomputable def massDensityGPerCm3 (cell : PhaseUnitCell) : ℝ :=
  (cell.moleculesPerCell : ℝ) * cell.molecularWeightAmu /
    (avogadroNumber * unitCellVolumeCm3 cell)

/--
Curvature-density fraction ρ ∈ [0,1]: solid geometry density relative to a liquid
reference at the melt comparison (H₂O liquid reference = 1.0 g/cm³ scale).
-/
noncomputable def curvatureDensityFraction (ρSolid ρLiquidRef : ℝ) : ℝ :=
  clampMediumDensity (ρSolid / ρLiquidRef)

/-- Homogeneous curvature budget at contact ξ using phase-derived ρ. -/
noncomputable def homogeneousCurvatureBudgetFromPhase (ξ ρ_phase : ℝ) : ℝ :=
  homogeneousCurvatureBudgetAtXi ξ ρ_phase

/-- Ice Ih hexagonal cell for H₂O at ~273 K (experimental geometry witness). -/
noncomputable def phaseUnitCellH2OIceIh : PhaseUnitCell :=
  { allotrope := "Ih"
    moleculesPerCell := 4
    molecularWeightAmu := 18.015
    aAngstrom := 4.515
    bAngstrom := 4.515
    cAngstrom := 7.362
    crystal := .hexagonal }

/-- Liquid-water reference density at melt comparison [g/cm³]. -/
noncomputable def liquidReferenceDensityH2O : ℝ := 1.0

/-- Curvature fraction for ice Ih vs liquid water reference. -/
noncomputable def curvatureDensityFractionH2OIceIh : ℝ :=
  curvatureDensityFraction (massDensityGPerCm3 phaseUnitCellH2OIceIh) liquidReferenceDensityH2O

/-- Second-order κ₆ feedback at bulk H₂O contact ξ with ice-Ih phase ρ (no nucleation defect). -/
noncomputable def bindingCurvatureFeedbackH2OBulkIceIh (ξ : ℝ) : ℝ :=
  bindingCurvatureFeedbackSecondOrderHomogeneous ξ curvatureDensityFractionH2OIceIh 0

theorem unitCellVolumeCm3_pos_of_pos_lattice (cell : PhaseUnitCell)
    (ha : 0 < cell.aAngstrom) (hb : 0 < cell.bAngstrom) (hc : 0 < cell.cAngstrom) :
    0 < unitCellVolumeCm3 cell := by
  unfold unitCellVolumeCm3
  rcases cell.crystal with _ | _ | _
  all_goals
    have ha' : 0 < cell.aAngstrom * angstromToCm := mul_pos ha angstromToCm_pos
    have hb' : 0 < cell.bAngstrom * angstromToCm := mul_pos hb angstromToCm_pos
    have hc' : 0 < cell.cAngstrom * angstromToCm := mul_pos hc angstromToCm_pos
    positivity

theorem massDensityGPerCm3_pos_of_pos_lattice (cell : PhaseUnitCell)
    (hZ : 0 < cell.moleculesPerCell) (hM : 0 < cell.molecularWeightAmu)
    (ha : 0 < cell.aAngstrom) (hb : 0 < cell.bAngstrom) (hc : 0 < cell.cAngstrom) :
    0 < massDensityGPerCm3 cell := by
  unfold massDensityGPerCm3
  have hV := unitCellVolumeCm3_pos_of_pos_lattice cell ha hb hc
  refine div_pos ?_ (mul_pos avogadroNumber_pos hV)
  exact mul_pos (Nat.cast_pos.mpr hZ) hM

theorem massDensityH2OIceIh_pos : 0 < massDensityGPerCm3 phaseUnitCellH2OIceIh := by
  unfold phaseUnitCellH2OIceIh
  exact massDensityGPerCm3_pos_of_pos_lattice _ (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem liquidReferenceDensityH2O_pos : 0 < liquidReferenceDensityH2O := by
  unfold liquidReferenceDensityH2O; norm_num

theorem curvatureDensityFraction_le_one (ρSolid ρLiquidRef : ℝ) :
    curvatureDensityFraction ρSolid ρLiquidRef ≤ 1 := by
  unfold curvatureDensityFraction clampMediumDensity
  rw [max_le_iff]
  exact ⟨by norm_num, min_le_left (1 : ℝ) (ρSolid / ρLiquidRef)⟩

theorem curvatureDensityFraction_nonneg (ρSolid ρLiquidRef : ℝ) :
    0 ≤ curvatureDensityFraction ρSolid ρLiquidRef := by
  unfold curvatureDensityFraction clampMediumDensity
  exact le_max_left _ _

theorem curvatureDensityFractionH2OIceIh_in_unit_interval :
    0 ≤ curvatureDensityFractionH2OIceIh ∧
      curvatureDensityFractionH2OIceIh ≤ 1 := by
  constructor
  · unfold curvatureDensityFractionH2OIceIh
    exact curvatureDensityFraction_nonneg _ _
  · unfold curvatureDensityFractionH2OIceIh
    exact curvatureDensityFraction_le_one _ _

/-- Clausius–Mossotti ratio from refractive index: ``(n²−1)/(n²+2)``. -/
noncomputable def clausiusMossottiRatioFromN (n : ℝ) : ℝ :=
  let n2 := n * n
  (n2 - 1) / (n2 + 2)

/-- Optical curvature ρ from solid n (n = 1 → dilute limit). -/
noncomputable def opticalCurvatureDensityFraction (n : ℝ) : ℝ :=
  if n ≤ 1 then 0 else clampMediumDensity (clausiusMossottiRatioFromN n)

/--
Unified phase curvature for κ₆: geometric ρ dressed by optical participation.

``ρ_κ = clamp(ρ_geom · (1 + α · ρ_opt(n)))`` — Python ``phase_curvature_density_fraction``.
-/
noncomputable def phaseCurvatureDensityFraction (ρGeom n : ℝ) : ℝ :=
  let ρopt := opticalCurvatureDensityFraction n
  clampMediumDensity (ρGeom * (1 + alpha * ρopt))

theorem opticalCurvatureDensityFraction_dilute :
    opticalCurvatureDensityFraction 1 = 0 := by
  unfold opticalCurvatureDensityFraction
  simp

theorem phaseCurvatureDensityFraction_geom_only (ρGeom : ℝ) :
    phaseCurvatureDensityFraction ρGeom 1 = clampMediumDensity ρGeom := by
  unfold phaseCurvatureDensityFraction opticalCurvatureDensityFraction
  simp [opticalCurvatureDensityFraction_dilute]

/-- Tetrahedral ice reference melt ladder (= 1). -/
noncomputable def meltMotifRelativeScaleTetrahedral : ℝ := 1

/-- Pyramidal H-bond melt: ``(3/4)(1 − γ/8)``. -/
noncomputable def meltMotifRelativeScalePyramidal : ℝ :=
  (3 : ℝ) / 4 * (1 - gamma_HQIV / 8)

/-- Apolar close-pack melt: ``(γ/α)/√n_inter`` (``n_inter = 4`` default). -/
noncomputable def meltMotifRelativeScaleApolar (nInter : ℕ) : ℝ :=
  let n := max nInter 1
  gamma_HQIV / alpha / Real.sqrt (n : ℝ)

/-- Linear-chain melt with halogen dress (``Z=9`` default for HF). -/
noncomputable def meltMotifRelativeScaleLinearChain (nInter zHeavy : ℕ) : ℝ :=
  let n := max nInter 1
  let hal := 1 + gamma_HQIV * (zHeavy : ℝ) / 8
  gamma_HQIV / alpha / (n : ℝ) * hal * (1 + gamma_HQIV) * (1 + gamma_HQIV / 16)

theorem meltMotifRelativeScaleTetrahedral_eq_one :
    meltMotifRelativeScaleTetrahedral = 1 := rfl


theorem homogeneousCurvatureBudgetFromPhase_dilute (ξ : ℝ) :
    homogeneousCurvatureBudgetFromPhase ξ 0 = 1 := by
  unfold homogeneousCurvatureBudgetFromPhase homogeneousCurvatureBudgetAtXi
    clampMediumDensity
  simp

theorem homogeneousCurvatureBudgetFromPhase_condensed (ξ : ℝ) :
    homogeneousCurvatureBudgetFromPhase ξ 1 = curvatureBudgetAtXi ξ := by
  unfold homogeneousCurvatureBudgetFromPhase homogeneousCurvatureBudgetAtXi
    curvatureBudgetAtXi clampMediumDensity
  simp

theorem homogeneousCurvatureBudgetFromPhase_eq_homogeneous (ξ ρ : ℝ) :
    homogeneousCurvatureBudgetFromPhase ξ ρ = homogeneousCurvatureBudgetAtXi ξ ρ := rfl

/-!
## Orbital phase geometry (planetary bulk + inverse-square local curvature)

The condensed-phase pipeline generalizes to flyby readouts: the geometry witness is
`(M, R, r_encounter)` instead of a unit cell.  Bulk planetary density is fully condensed
(ρ_bulk = 1); the local inverse-square slot `(R/r)²` is blended with bulk dominance
`w_bulk = 1 / (1 + (r/R)²)` (macroscopic bulk limit of
`scripts/hqiv_homogeneous_curvature_feedback.py`).

At large encounter radius ρ → 0 and the curvature mass delta vanishes (GR limit).
-/

/-- Orbital geometry witness: central mass, equatorial radius, encounter distance [m]. -/
structure OrbitalPhaseWitness where
  label : String
  centralMassKg : ℝ
  radiusM : ℝ
  encounterRadiusM : ℝ

/-- Bulk-dominated inverse-square weight (size fraction = 1 for planetary samples). -/
noncomputable def orbitalBulkDominanceWeight (rBulk rEncounter : ℝ) : ℝ :=
  if 0 < rBulk then 1 / (1 + (rEncounter / rBulk) ^ (2 : ℕ)) else 0

/-- Local curvature fraction vs surface reference: clamp((R/r)²). -/
noncomputable def orbitalLocalCurvatureFraction (rBulk rEncounter : ℝ) : ℝ :=
  if 0 < rEncounter then clampMediumDensity ((rBulk / rEncounter) ^ (2 : ℕ)) else 0

/--
Effective orbital curvature density ρ ∈ [0,1]:
`ρ_eff = w_bulk·ρ_bulk + (1 − w_bulk)·ρ_local` with ρ_bulk = 1 (condensed body).
-/
noncomputable def orbitalCurvatureDensityFraction (w : OrbitalPhaseWitness) : ℝ :=
  let wBulk := orbitalBulkDominanceWeight w.radiusM w.encounterRadiusM
  let ρLocal := orbitalLocalCurvatureFraction w.radiusM w.encounterRadiusM
  clampMediumDensity (wBulk + (1 - wBulk) * ρLocal)

/-- Homogeneous curvature budget at propagation ξ from orbital phase geometry. -/
noncomputable def homogeneousCurvatureBudgetFromOrbital (ξ : ℝ) (w : OrbitalPhaseWitness) : ℝ :=
  homogeneousCurvatureBudgetFromPhase ξ (orbitalCurvatureDensityFraction w)

/-- Dimensionless mass/curvature delta above dilute limit: `B_hom(ξ, ρ_orb) − 1`. -/
noncomputable def orbitalCurvatureMassDeltaFraction (ξ : ℝ) (w : OrbitalPhaseWitness) : ℝ :=
  homogeneousCurvatureBudgetFromOrbital ξ w - 1

/-- Earth mass [kg] (IAU nominal). -/
noncomputable def earthMassKg : ℝ := 5.9722e24

/-- Earth equatorial radius [m]. -/
noncomputable def earthRadiusM : ℝ := 6.378137e6

/-- Earth orbital witness at encounter distance `r` from centre. -/
noncomputable def orbitalPhaseWitnessEarth (encounterRadiusM : ℝ) : OrbitalPhaseWitness :=
  { label := "Earth"
    centralMassKg := earthMassKg
    radiusM := earthRadiusM
    encounterRadiusM := encounterRadiusM }

theorem orbitalBulkDominanceWeight_nonneg (rBulk rEncounter : ℝ) :
    0 ≤ orbitalBulkDominanceWeight rBulk rEncounter := by
  unfold orbitalBulkDominanceWeight
  split_ifs with h
  · exact div_nonneg (by norm_num) (add_nonneg (by norm_num) (sq_nonneg _))
  · norm_num

theorem orbitalLocalCurvatureFraction_le_one (rBulk rEncounter : ℝ) :
    orbitalLocalCurvatureFraction rBulk rEncounter ≤ 1 := by
  unfold orbitalLocalCurvatureFraction
  split_ifs with h
  · unfold clampMediumDensity
    rw [max_le_iff]
    exact ⟨by norm_num, min_le_left _ _⟩
  · norm_num

theorem orbitalCurvatureDensityFraction_le_one (w : OrbitalPhaseWitness) :
    orbitalCurvatureDensityFraction w ≤ 1 := by
  unfold orbitalCurvatureDensityFraction clampMediumDensity
  rw [max_le_iff]
  exact ⟨by norm_num, min_le_left _ _⟩

theorem orbitalCurvatureDensityFraction_nonneg (w : OrbitalPhaseWitness) :
    0 ≤ orbitalCurvatureDensityFraction w := by
  unfold orbitalCurvatureDensityFraction clampMediumDensity
  exact le_max_left _ _

theorem orbitalCurvatureMassDelta_zero_of_zero_density (ξ : ℝ) (w : OrbitalPhaseWitness)
    (hρ : orbitalCurvatureDensityFraction w = 0) :
    orbitalCurvatureMassDeltaFraction ξ w = 0 := by
  unfold orbitalCurvatureMassDeltaFraction homogeneousCurvatureBudgetFromOrbital
  rw [hρ, homogeneousCurvatureBudgetFromPhase_dilute]
  ring

theorem homogeneousCurvatureBudgetFromOrbital_eq_phase (ξ : ℝ) (w : OrbitalPhaseWitness) :
    homogeneousCurvatureBudgetFromOrbital ξ w =
      homogeneousCurvatureBudgetFromPhase ξ (orbitalCurvatureDensityFraction w) := rfl

end Hqiv.QuantumChemistry
