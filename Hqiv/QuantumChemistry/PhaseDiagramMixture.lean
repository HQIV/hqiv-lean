import Hqiv.QuantumChemistry.PhaseAllotropeDerivation
import Hqiv.QuantumChemistry.PhaseGeometryDensity

/-!
# Phase diagram mixture algebra (first-principles end members)

Generalized **(T, P) → phase + ρ_curv** spine for pure species and mixtures.

* **End members** — geometry witnesses (coordination-heavy vs lattice-released liquid).
* **Mixture fraction** `f ∈ [0,1]` — derived in Python from HQIV cohesive scales (not MD/DFT).
* **External LLPT / two-state papers** — comparison rows only (`AGENTS/LITERATURE_WATER_TWO_STATE.md`).

Python mirror: `hqiv_lab/phase_diagram.py`, `scripts/hqiv_phase_diagram.py`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Algebra
open Hqiv.Physics

noncomputable section

/-- One branch on a phase diagram (label + curvature-density witness). -/
structure PhaseEndMember where
  label : String
  rhoCurv : ℝ
  coordinationFraction : ℝ

/-- Subphase tag inside a liquid branch (LDL/HDL two-liquid extension). -/
inductive LiquidSubphase
  | lowDensity
  | highDensity
  | mixture
  | indeterminate
  deriving DecidableEq, Repr

/--
Convex mixture of two end-member curvature fractions, clamped to [0,1].

`f = 1` → low-density end member; `f = 0` → high-density end member.
-/
noncomputable def liquidMixtureCurvatureFraction (f ρLow ρHigh : ℝ) : ℝ :=
  clampMediumDensity (f * ρLow + (1 - f) * ρHigh)

theorem liquidMixtureCurvatureFraction_low_limit (ρLow ρHigh : ℝ) :
    liquidMixtureCurvatureFraction 1 ρLow ρHigh = clampMediumDensity ρLow := by
  unfold liquidMixtureCurvatureFraction
  simp

theorem liquidMixtureCurvatureFraction_high_limit (ρLow ρHigh : ℝ) :
    liquidMixtureCurvatureFraction 0 ρLow ρHigh = clampMediumDensity ρHigh := by
  unfold liquidMixtureCurvatureFraction
  simp

theorem liquidMixtureCurvatureFraction_le_one (f ρLow ρHigh : ℝ) :
    liquidMixtureCurvatureFraction f ρLow ρHigh ≤ 1 := by
  unfold liquidMixtureCurvatureFraction clampMediumDensity
  rw [max_le_iff]
  exact ⟨by norm_num, min_le_left (1 : ℝ) _⟩

theorem liquidMixtureCurvatureFraction_nonneg (f ρLow ρHigh : ℝ) :
    0 ≤ liquidMixtureCurvatureFraction f ρLow ρHigh := by
  unfold liquidMixtureCurvatureFraction clampMediumDensity
  exact le_max_left _ _

/-- H₂O low-density liquid end member: tetrahedral coordination-heavy melt ratio. -/
noncomputable def h2oLiquidLowDensityEndMember : PhaseEndMember :=
  { label := "H2O_LDL"
    rhoCurv := clampMediumDensity (tetrahedralMeltDensityRatio 4)
    coordinationFraction := 1 }

/-- H₂O high-density liquid end member: melt-comparison lattice release. -/
noncomputable def h2oLiquidHighDensityEndMember : PhaseEndMember :=
  { label := "H2O_HDL"
    rhoCurv := meltComparisonCurvatureDensityFraction
    coordinationFraction := meltComparisonCurvatureDensityFraction }

theorem h2oLiquidHighDensityEndMember_rho_eq_one :
    h2oLiquidHighDensityEndMember.rhoCurv = 1 := by
  unfold h2oLiquidHighDensityEndMember meltComparisonCurvatureDensityFraction
  rfl

/-- Mixture ρ for H₂O two-liquid branch at fraction ``f`` toward LDL. -/
noncomputable def h2oLiquidMixtureCurvatureFraction (f : ℝ) : ℝ :=
  liquidMixtureCurvatureFraction f
    h2oLiquidLowDensityEndMember.rhoCurv
    h2oLiquidHighDensityEndMember.rhoCurv

theorem h2oLiquidMixture_at_ldl (f : ℝ) (hf : f = 1) :
    h2oLiquidMixtureCurvatureFraction f =
      clampMediumDensity h2oLiquidLowDensityEndMember.rhoCurv := by
  rw [hf, h2oLiquidMixtureCurvatureFraction, liquidMixtureCurvatureFraction_low_limit]

theorem h2oLiquidMixture_at_hdl (f : ℝ) (hf : f = 0) :
    h2oLiquidMixtureCurvatureFraction f = 1 := by
  rw [hf, h2oLiquidMixtureCurvatureFraction, liquidMixtureCurvatureFraction_high_limit,
    h2oLiquidHighDensityEndMember_rho_eq_one]
  unfold clampMediumDensity
  simp

/-- One component in a multi-species mixture (mole fraction witness). -/
structure MixtureComponentWitness where
  label : String
  moleFraction : ℝ
  endLow : PhaseEndMember
  endHigh : PhaseEndMember

/--
Effective mixture ρ from component mole fractions and per-species LDL/HDL fractions.

Each component contributes ``x · (f·ρ_low + (1−f)·ρ_high)``; result clamped.
-/
noncomputable def mixtureCurvatureFraction
    (components : List MixtureComponentWitness) (fPerComponent : List ℝ) : ℝ :=
  let pairs := components.zip fPerComponent
  let raw := pairs.foldl (fun acc p =>
    let c := p.1
    let f := p.2
    acc + c.moleFraction * liquidMixtureCurvatureFraction f c.endLow.rhoCurv c.endHigh.rhoCurv) 0
  clampMediumDensity raw

/-- Kinetic accessibility floor for metastable liquid (γ·α·T_melt ladder slot). -/
noncomputable def metastableLiquidKineticFloorScale : ℝ := gamma_HQIV * alpha

/--
Metastable liquid is structurally allowed when ``T > T_melt · γ·α`` (Python evaluates).

Below this floor the network freezes to solid on the HQIV ladder (no fitted T_g).
-/
noncomputable def metastableLiquidAccessible (T_K T_melt_K : ℝ) : Prop :=
  T_melt_K * metastableLiquidKineticFloorScale < T_K

theorem metastableLiquidAccessible_mono {T₁ T₂ T_melt : ℝ}
    (hT : T₁ < T₂) (hacc : metastableLiquidAccessible T₁ T_melt) :
    metastableLiquidAccessible T₂ T_melt := by
  unfold metastableLiquidAccessible at *
  exact lt_trans hacc hT

/-- Tetrahedral bulk networks admit a two-liquid metastable branch (H₂O, polyols, …). -/
def supportsTwoLiquidBranch (motif : IntermolecularMotif) : Bool :=
  match motif with
  | .tetrahedralHbond | .pyramidalHbond | .polyolHbond => true
  | _ => false

theorem supportsTwoLiquidBranch_h2o :
    supportsTwoLiquidBranch intermolecularMotifH2O = true := by
  native_decide

/-!
## Widom-line / compressibility anomaly proxy

Response proxy from the same cohesive ladder as ``f_LDL`` — no MD compressibility input.
Python mirror: ``widom_line_compressibility_proxy`` in ``hqiv_lab/phase_diagram.py``.
Kim et al. compressibility maxima grade the audit grid (comparison only).
-/

/-- Cohesive-contrast slot for κ anomaly scaling (LDL vs HDL melt scales differ on the ladder). -/
noncomputable def liquidCohesiveContrastScale : ℝ := gamma_HQIV * alpha

/-- Homogeneous ``B_hom(ξ,ρ)−1`` feedback on cohesive contrast (signed). -/
noncomputable def liquidHomogeneousCurvatureFeedback (bHom : ℝ) : ℝ :=
  liquidCohesiveContrastScale * (bHom - 1)

/-- MacroRicci outside dress when ``G_eff(ρ) > 1`` (species-dependent). -/
noncomputable def liquidCohesiveOutsideFeedback (bHom geffAtRho : ℝ) : ℝ :=
  liquidCohesiveContrastScale * (bHom - 1) * max (geffAtRho - 1) 0

/--
Local H–O–H angle mixture slot: ``f·θ_tet + (1−f)·θ_gas`` (Python ``hoh_angle_mixture_deg``).

θ_tet = ``centreAngleRadFromDomains 4`` (LDL); θ_gas = ``dynamicCentreAngleRad 8 2`` (HDL slot).
Gas-phase 104.478° (NIST CCCBDB / Hoy & Bunker 1979) is comparison quarantine only.
-/
noncomputable def hohAngleMixtureSlot (f thetaTet thetaGas : ℝ) : ℝ :=
  f * thetaTet + (1 - f) * thetaGas

/--
Mixture latent-barrier factor ``f·(1−f)``: full first-order cost hidden in mixed LDL/HDL;
second-order susceptibility still carries the barrier (Widom / κ proxy).
-/
noncomputable def mixtureLatentBarrierFactor (f : ℝ) : ℝ := f * (1 - f)

/--
Chemical-potential slot from partial latent barrier between liquid branches:

``(1 − 2f) · L_branch`` — regular-solution barrier, vanishes at pure end members.
-/
noncomputable def liquidBranchBarrierPotential (f lBranch : ℝ) : ℝ :=
  (1 - 2 * f) * lBranch

/--
Combinatorial two-branch mixing shape, with the logarithmic entropy evaluated by Python.

Lean keeps the free-energy algebra explicit; numerical minimization lives in
``hqiv_lab.phase_diagram.low_density_free_energy_minimum``.
-/
noncomputable def liquidMixtureEntropySlot (sMix kT : ℝ) : ℝ := kT * sMix

/--
LDL/HDL branch free energy at fixed ``(T,P)``.

``delta`` is the cohesive + pressure + homogeneous-curvature branch tilt,
``lBranch`` is the partial latent conversion barrier, and ``sMix`` is the
dimensionless two-state mixing entropy shape.
-/
noncomputable def liquidBranchFreeEnergy (f delta lBranch kT sMix : ℝ) : ℝ :=
  f * delta + lBranch * mixtureLatentBarrierFactor f + liquidMixtureEntropySlot sMix kT

/-- A derived low-density fraction is any minimizer of the HQIV two-branch free energy. -/
def stationaryLowDensityFraction
    (f : ℝ) (freeEnergy : ℝ → ℝ) : Prop :=
  0 ≤ f ∧ f ≤ 1 ∧ ∀ g, 0 ≤ g → g ≤ 1 → freeEnergy f ≤ freeEnergy g

/-- Finite-difference curvature slot for susceptibility / Widom proxy witnesses. -/
noncomputable def liquidBranchFreeEnergyCurvature
    (f eps : ℝ) (freeEnergy : ℝ → ℝ) : ℝ :=
  (freeEnergy (f + eps) - 2 * freeEnergy f + freeEnergy (f - eps)) / (eps ^ 2)

/--
Second-order supercooled-window center for the Widom susceptibility branch.

The offset is ``γ²`` of the melt scale: the first-order melt release is already accounted for;
the remaining mixed LDL/HDL anomaly is a second-order latent-barrier response.
-/
noncomputable def widomSecondOrderWindowCenter (T_melt : ℝ) : ℝ :=
  T_melt * (1 - gamma_HQIV ^ 2)

/-- Window width from the same second-order scale with lattice ``α`` imprint. -/
noncomputable def widomSecondOrderWindowWidth (T_melt : ℝ) : ℝ :=
  T_melt * alpha * gamma_HQIV ^ 2

/--
Mixture response slot: ``f·prop_LDL + (1−f)·prop_HDL`` for n, k_th, η readouts.

Python evaluates end-member properties then mixes (``material_response_mixture_readout``).
-/
noncomputable def materialResponseMixture (f propLow propHigh : ℝ) : ℝ :=
  f * propLow + (1 - f) * propHigh

theorem materialResponseMixture_ldl_limit (propLow propHigh : ℝ) :
    materialResponseMixture 1 propLow propHigh = propLow := by
  unfold materialResponseMixture
  ring

theorem materialResponseMixture_hdl_limit (propLow propHigh : ℝ) :
    materialResponseMixture 0 propLow propHigh = propHigh := by
  unfold materialResponseMixture
  simp

end

end Hqiv.QuantumChemistry
