import Hqiv.Physics.CompactObjectRotatingCrustScaffold
import Hqiv.Physics.CoronalLongitudinalStress
import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Physics.NuclearOutsideTemperatureDynamics

/-!
# Compact-object MHD equivalence scaffold (tradSci ↔ HQIV)

**Purpose:** record the **equation-level reduction** of standard resistive / Hall-MHD crust
dynamics onto existing HQIV slots, with explicit coefficient identification and an honesty
ledger for what is proved vs milestone vs not claimed.

Python: `scripts/hqiv_compact_object_mass.py` (`tradsci_mhd_equivalence_bridge`,
`paper_dynamics_section_bundle`).

Paper: `papers/compact_object_witness/hqiv_compact_object_crust_mhd_equivalence.tex`.

**Thesis (paper-facing):** HQIV is **composite MHD** (`S_O` + modified fluid closure), not a rival
magnetic theory. Traditional η, σ, and turbulent α map to `inductionResistivityEta`, `ohmicAxialField`,
and `hqivEddyViscosity` / `hqivVacuumMomentumSource3` with lattice coefficients α, γ and slots ξ, ε.

**Proved here:** Ohmic classical limit, η nonnegativity and lattice unfold, resistive induction
witness algebra, plasma viscosity split, geometry-slot nonnegativity, discharged honesty ledger.

**Not claimed:** full vector `∇×` Hall-MHD PDE integration over 10³–10⁶ yr; proto-NS αΩ seed for
magnetar 10¹⁴–10¹⁵ G without external boundary **B₀**; numeric σ(T,B) calibration tables.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-!
## §1 Traditional ↔ HQIV coefficient identification (resistive leg)
-/

/-- Traditional ohmic axial field ``E = J/σ`` is `ohmicAxialField`. -/
theorem traditionalOhmicAxialField_eq_J_div_sigma (J sigma : ℝ) :
    ohmicAxialField J sigma = J / sigma := rfl

/-- HQIV induction resistivity unfolded on the outside-environment stack. -/
theorem inductionResistivityEta_eq_gamma_release_geff (xi phiEpsilon : ℝ) :
    inductionResistivityEta xi phiEpsilon =
      gamma_HQIV * outsideCurvatureReleaseFactor xi *
        outsideGravityGeffModulator ⟨phiEpsilon⟩ := rfl

/-- Traditional MHD resistivity η identified with HQIV `inductionResistivityEta(ξ, ε)`. -/
structure TraditionalResistiveEtaIdentification where
  xi : ℝ
  phiEpsilon : ℝ
  tradEta : ℝ
  trad_eq_hqiv : tradEta = inductionResistivityEta xi phiEpsilon

def TraditionalResistiveEtaIdentification.mk'
    (xi phiEpsilon : ℝ) : TraditionalResistiveEtaIdentification :=
  { xi := xi
    phiEpsilon := phiEpsilon
    tradEta := inductionResistivityEta xi phiEpsilon
    trad_eq_hqiv := rfl }

theorem TraditionalResistiveEtaIdentification.trad_nonneg
    (h : TraditionalResistiveEtaIdentification) :
    0 ≤ h.tradEta := by
  rw [h.trad_eq_hqiv]
  exact inductionResistivityEta_nonneg h.xi h.phiEpsilon

/-- Classical Maxwell limit: HQIV longitudinal channel vanishes ⇒ pure Ohmic field. -/
theorem traditional_ohmic_limit_coronalEffectiveAxialField
    (J sigma Estar couplingLog : ℝ) :
    coronalEffectiveAxialField J sigma Estar couplingLog 0 = ohmicAxialField J sigma :=
  coronalEffectiveAxialField_classical_limit J sigma Estar couplingLog

/-!
## §2 Resistive induction witness (scalar discharge of trad `∂B/∂t`)
-/

/-- Bundle linking trad resistive induction scalars to HQIV steady/growth slots. -/
structure ResistiveInductionWitness where
  eta : ℝ
  aLt : ℝ
  aGrav : ℝ
  bSurf : ℝ
  radius : ℝ
  bLt : ℝ
  dBdt : ℝ
  bLt_eq : bLt = steadyInductionFieldLt eta aLt aGrav bSurf
  dBdt_eq : dBdt = inductionGrowthRateFromLt eta aLt radius

/-- Construct witness from coefficients (paper discharge). -/
def mkResistiveInductionWitness (eta aLt aGrav bSurf radius : ℝ) :
    ResistiveInductionWitness :=
  { eta := eta
    aLt := aLt
    aGrav := aGrav
    bSurf := bSurf
    radius := radius
    bLt := steadyInductionFieldLt eta aLt aGrav bSurf
    dBdt := inductionGrowthRateFromLt eta aLt radius
    bLt_eq := rfl
    dBdt_eq := rfl }

/-!
## §3 Momentum / turbulent α identification (F3 bookkeeping)
-/

/-- Traditional ``τ = τ_mol + τ_eddy`` scalar split with HQIV eddy viscosity slot. -/
theorem traditional_plasma_viscosity_eq_mol_add_hqivEddy
    (nuMol nuEddy nuTotal gamma Theta dot lCoh C : ℝ)
    (h : PlasmaFluidClosureAssumptions nuMol nuEddy nuTotal gamma Theta dot lCoh C) :
    nuTotal = nuMol + hqivEddyViscosity gamma Theta dot lCoh C :=
  nuTotal_eq_nuMol_add_hqivEddy nuMol nuEddy nuTotal gamma Theta dot lCoh C h

/-- Traditional turbulent α dynamo maps to `hqivEddyViscosity` + `hqivVacuumMomentumSource3`
(F2 chart hypothesis); this theorem records only the **viscosity leg**. -/
theorem trad_dynamo_alpha_eddy_viscosity_slot
    (nuMol nuEddy nuTotal gamma Theta dot lCoh C : ℝ)
    (h : PlasmaFluidClosureAssumptions nuMol nuEddy nuTotal gamma Theta dot lCoh C) :
    nuEddy = hqivEddyViscosity gamma Theta dot lCoh C :=
  h.eddy_viscosity_hqiv

/-!
## §4 Geometry-first crust slots (spin axis + ε layers)
-/

/-- Coriolis / mid-latitude shear gate is nonnegative. -/
theorem compactObjectLtVectorFraction_spin_axis_slot_nonneg (sinColatitude rhoPol : ℝ) :
    0 ≤ compactObjectLtVectorFraction sinColatitude rhoPol :=
  compactObjectLtVectorFraction_nonneg sinColatitude rhoPol

/-- Misaligning torque vanishes when shear coupling vanishes (obliquity balance degeneracy). -/
theorem crust_misalign_torque_zero_of_zero_shear
    (radius aGrav sinColatitude hShell rhoCrust rhoNuclear : ℝ) :
    crustMisalignTorqueFromStressDivergence radius aGrav 0 sinColatitude hShell rhoCrust
      rhoNuclear = 0 :=
  crustMisalignTorqueFromStressDivergence_zero_of_zero_coupling radius aGrav sinColatitude hShell
    rhoCrust rhoNuclear

/-- Acceleration discharge agrees with stress-divergence torque (τ_mis slot). -/
theorem crust_misalign_torque_acceleration_discharge
    (radius aGrav aLt aParallel sinColatitude hShell rhoCrust rhoNuclear : ℝ) :
    crustMisalignTorqueFromAccelerations radius aGrav aLt aParallel sinColatitude hShell
      rhoCrust rhoNuclear =
      crustMisalignTorqueFromStressDivergence radius aGrav
        (compactObjectShearCoupling aLt aParallel aGrav) sinColatitude hShell rhoCrust
        rhoNuclear :=
  crustMisalignTorqueFromAccelerations_eq_stressDivergence radius aGrav aLt aParallel
    sinColatitude hShell rhoCrust rhoNuclear

/-!
## §5 Honesty ledger (proved vs milestone vs not claimed)
-/

/-- **Proved** reductions discharged in this module. -/
structure CompactObjectMhdProvedReductions where
  ohmic_classical : ∀ J sigma Estar couplingLog : ℝ,
    coronalEffectiveAxialField J sigma Estar couplingLog 0 = ohmicAxialField J sigma
  eta_nonneg : ∀ xi phiEpsilon : ℝ, 0 ≤ inductionResistivityEta xi phiEpsilon
  eta_lockin_zero_gravity : inductionResistivityEta xiLockin 0 = gamma_HQIV
  rindler_screen : compactObjectCrustRindlerScreen = 4 / 5

theorem compactObjectMhdProvedReductions_holds : CompactObjectMhdProvedReductions :=
  { ohmic_classical := traditional_ohmic_limit_coronalEffectiveAxialField
    eta_nonneg := inductionResistivityEta_nonneg
    eta_lockin_zero_gravity := inductionResistivityEta_lockin_zero_gravity
    rindler_screen := compactObjectCrustRindlerScreen_eq_four_fifths }

/-- **Milestones** (same PDE class; vector / time integration not yet discharged). -/
structure CompactObjectMhdMilestones where
  vector_hall_mhd_pde : Prop
  time_dependent_multipoles : Prop
  sigma_T_B_numeric_calibration : Prop

/-- **Not claimed** in the cold-crust witness (paper honesty). -/
structure CompactObjectMhdNotClaimed where
  proto_ns_alpha_omega_seed_without_boundary : Prop
  magnetar_field_generation_without_B0 : Prop
  replaces_hall_mhd_crust_codes : Prop

/-- Paper bundle: coefficient ID + resistive witness + proved ledger at (ξ, ε). -/
structure CompactObjectMhdEquivalenceDischarged where
  xi : ℝ
  phiEpsilon : ℝ
  etaId : TraditionalResistiveEtaIdentification
  eta_nonneg : 0 ≤ inductionResistivityEta xi phiEpsilon
  proved : CompactObjectMhdProvedReductions

/-- Discharge equivalence at environment slots (ξ, ε). -/
def mkCompactObjectMhdEquivalenceDischarged (xi phiEpsilon : ℝ) :
    CompactObjectMhdEquivalenceDischarged :=
  { xi := xi
    phiEpsilon := phiEpsilon
    etaId := TraditionalResistiveEtaIdentification.mk' xi phiEpsilon
    eta_nonneg := inductionResistivityEta_nonneg xi phiEpsilon
    proved := compactObjectMhdProvedReductions_holds }

/-- Machine-checked witness name for papers and JSON audits. -/
theorem compactObjectMhdEquivalenceDischarged_holds (xi phiEpsilon : ℝ) :
    Nonempty CompactObjectMhdEquivalenceDischarged :=
  ⟨mkCompactObjectMhdEquivalenceDischarged xi phiEpsilon⟩

end

end Hqiv.Physics
