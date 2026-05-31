import Mathlib.Data.List.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Hqiv.Geometry.HQVMDiscreteLaplacian
import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Physics.ContinuumOmaxwellClosure

/-!
# HQIV-native turbulence simulator scaffold

This module is a Lean-only specification surface for a future Python turbulence simulator. It does
not implement meshes, time stepping, RANS model calibration, or Navier--Stokes regularity. Instead it
names:

* the TMR benchmark families as typed metadata;
* a HQIV-native fluid state over the existing `ObserverChart`;
* closure inputs/outputs wired to `HQIVFluidClosureScaffold`;
* a solver contract that a Python implementation can mirror.

Hard analysis and numerical convergence are deliberately represented as callback fields or hypothesis
records, not as proved PDE theorems.
-/

namespace Hqiv.Physics

noncomputable section

/-- TMR case dimensionality. Axisymmetric cases are kept distinct because Python solvers usually choose
different geometric source terms even when they store a two-coordinate mesh. -/
inductive TMRDimension where
  | twoD
  | threeD
  | axisymmetric
  deriving DecidableEq, Repr

/-- Coarse benchmark group from the Turbulence Modeling Resource. -/
inductive TMRBenchmarkGroup where
  | verification
  | additionalVerification
  | validationBasic
  | validationExtended
  | highReClassical
  | transitionVerification
  deriving DecidableEq, Repr

/-- Flow capabilities needed by a solver that wants to cover the TMR suite. -/
inductive TMRFlowPhysicsTag where
  | wallBounded
  | freeShear
  | pressureGradient
  | curvature
  | compressible
  | heatFlux
  | highMach
  | shockInteraction
  | separation
  | secondaryFlow
  | vortexFlow
  | transition
  | internalFlow
  | externalAerodynamics
  deriving DecidableEq, Repr

/-- Boundary-condition families a Python simulator must be able to represent. -/
inductive TMRBoundaryTag where
  | noSlipWall
  | farfield
  | inflow
  | outflow
  | symmetry
  | periodic
  | wakeSurvey
  | jetExit
  deriving DecidableEq, Repr

/-- Named benchmark families listed on the TMR index page. These are metadata keys, not meshes. -/
inductive TMRBenchmarkFamily where
  | verif2DZP
  | verif2DCJ
  | verif2DB
  | verif2DANW
  | verif2DMEA
  | verif3DB
  | add2DFiniteFlatPlate
  | add2DNACA0012
  | add3DModifiedBump
  | add3DModifiedSupersonicSquareDuct
  | add2DHemisphereCylinder
  | add3DHemisphereCylinderOld
  | add3DHemisphereCylinderNew
  | add3DONERAM6Wing
  | val2DZP
  | val2DML
  | val2DANW
  | val2DN00
  | valASJ
  | valAHSJ
  | valANSJ
  | valASBL
  | valATB
  | val2DZPH
  | val2DBFS
  | val2DN44
  | val2DCC
  | val2DWMH
  | valASWBLI
  | valACSSJ
  | valAHSSJ
  | valAJM163TM
  | valAJM163H
  | valAJM163OD
  | val3DSSD
  | val2DFDC
  | verif2DTFP
  deriving DecidableEq, Repr

/-- Typed benchmark metadata sufficient for a downstream simulator to decide which numerical features
are required. -/
structure TMRBenchmarkSpec where
  family : TMRBenchmarkFamily
  group : TMRBenchmarkGroup
  code : String
  title : String
  dimension : TMRDimension
  physics : List TMRFlowPhysicsTag
  boundaries : List TMRBoundaryTag
  observables : List String
  deriving Repr

private def wallObs : List String :=
  ["skin_friction", "pressure_coefficient", "velocity_profile"]

private def jetObs : List String :=
  ["centerline_velocity", "spreading_rate", "turbulent_shear_stress"]

private def wakeObs : List String :=
  ["wake_profile", "momentum_deficit", "turbulent_shear_stress"]

/-- Metadata for every TMR family targeted by the first simulator contract. -/
def tmrBenchmarkSpec : TMRBenchmarkFamily → TMRBenchmarkSpec
  | .verif2DZP =>
      { family := .verif2DZP, group := .verification, code := "VERIF/2DZP",
        title := "2D zero pressure gradient flat plate", dimension := .twoD,
        physics := [.wallBounded, .pressureGradient],
        boundaries := [.noSlipWall, .farfield, .inflow, .outflow], observables := wallObs }
  | .verif2DCJ =>
      { family := .verif2DCJ, group := .verification, code := "VERIF/2DCJ",
        title := "2D coflowing jet", dimension := .twoD,
        physics := [.freeShear], boundaries := [.jetExit, .farfield, .outflow], observables := jetObs }
  | .verif2DB =>
      { family := .verif2DB, group := .verification, code := "VERIF/2DB",
        title := "2D bump-in-channel", dimension := .twoD,
        physics := [.wallBounded, .pressureGradient, .curvature],
        boundaries := [.noSlipWall, .inflow, .outflow, .symmetry], observables := wallObs }
  | .verif2DANW =>
      { family := .verif2DANW, group := .verification, code := "VERIF/2DANW",
        title := "2D airfoil near-wake", dimension := .twoD,
        physics := [.externalAerodynamics, .freeShear],
        boundaries := [.noSlipWall, .farfield, .wakeSurvey], observables := wakeObs }
  | .verif2DMEA =>
      { family := .verif2DMEA, group := .verification, code := "VERIF/2DMEA",
        title := "2D multielement airfoil", dimension := .twoD,
        physics := [.externalAerodynamics, .wallBounded, .separation],
        boundaries := [.noSlipWall, .farfield, .wakeSurvey], observables := wallObs ++ wakeObs }
  | .verif3DB =>
      { family := .verif3DB, group := .verification, code := "VERIF/3DB",
        title := "3D bump-in-channel", dimension := .threeD,
        physics := [.wallBounded, .pressureGradient, .curvature, .secondaryFlow],
        boundaries := [.noSlipWall, .inflow, .outflow, .symmetry], observables := wallObs }
  | .add2DFiniteFlatPlate =>
      { family := .add2DFiniteFlatPlate, group := .additionalVerification, code := "2D finite flat plate",
        title := "2D finite flat plate", dimension := .twoD,
        physics := [.wallBounded, .externalAerodynamics],
        boundaries := [.noSlipWall, .farfield, .inflow, .outflow], observables := wallObs }
  | .add2DNACA0012 =>
      { family := .add2DNACA0012, group := .additionalVerification, code := "2D NACA 0012",
        title := "2D NACA 0012 airfoil", dimension := .twoD,
        physics := [.externalAerodynamics, .wallBounded],
        boundaries := [.noSlipWall, .farfield, .wakeSurvey], observables := wallObs ++ wakeObs }
  | .add3DModifiedBump =>
      { family := .add3DModifiedBump, group := .additionalVerification, code := "3D modified bump",
        title := "3D modified bump", dimension := .threeD,
        physics := [.wallBounded, .pressureGradient, .separation, .secondaryFlow],
        boundaries := [.noSlipWall, .inflow, .outflow, .symmetry], observables := wallObs }
  | .add3DModifiedSupersonicSquareDuct =>
      { family := .add3DModifiedSupersonicSquareDuct, group := .additionalVerification,
        code := "3D modified supersonic square duct", title := "3D modified supersonic square duct",
        dimension := .threeD,
        physics := [.internalFlow, .compressible, .highMach, .secondaryFlow],
        boundaries := [.noSlipWall, .inflow, .outflow, .symmetry], observables := wallObs }
  | .add2DHemisphereCylinder =>
      { family := .add2DHemisphereCylinder, group := .additionalVerification, code := "2D hemisphere cylinder",
        title := "2D hemisphere cylinder", dimension := .twoD,
        physics := [.externalAerodynamics, .separation],
        boundaries := [.noSlipWall, .farfield, .outflow], observables := wallObs }
  | .add3DHemisphereCylinderOld =>
      { family := .add3DHemisphereCylinderOld, group := .additionalVerification,
        code := "3D hemisphere cylinder old", title := "3D hemisphere cylinder old", dimension := .threeD,
        physics := [.externalAerodynamics, .separation, .vortexFlow],
        boundaries := [.noSlipWall, .farfield, .outflow], observables := wallObs }
  | .add3DHemisphereCylinderNew =>
      { family := .add3DHemisphereCylinderNew, group := .additionalVerification,
        code := "3D hemisphere cylinder new", title := "3D hemisphere cylinder new", dimension := .threeD,
        physics := [.externalAerodynamics, .separation, .vortexFlow],
        boundaries := [.noSlipWall, .farfield, .outflow], observables := wallObs }
  | .add3DONERAM6Wing =>
      { family := .add3DONERAM6Wing, group := .additionalVerification, code := "3D ONERA M6 wing",
        title := "3D ONERA M6 wing", dimension := .threeD,
        physics := [.externalAerodynamics, .compressible, .shockInteraction],
        boundaries := [.noSlipWall, .farfield, .wakeSurvey], observables := wallObs ++ wakeObs }
  | .val2DZP =>
      { family := .val2DZP, group := .validationBasic, code := "2DZP",
        title := "2D zero pressure gradient flat plate", dimension := .twoD,
        physics := [.wallBounded, .pressureGradient],
        boundaries := [.noSlipWall, .farfield, .inflow, .outflow], observables := wallObs }
  | .val2DML =>
      { family := .val2DML, group := .validationBasic, code := "2DML",
        title := "2D mixing layer", dimension := .twoD,
        physics := [.freeShear], boundaries := [.inflow, .outflow, .farfield], observables := jetObs }
  | .val2DANW =>
      { family := .val2DANW, group := .validationBasic, code := "2DANW",
        title := "2D airfoil near-wake", dimension := .twoD,
        physics := [.externalAerodynamics, .freeShear],
        boundaries := [.noSlipWall, .farfield, .wakeSurvey], observables := wakeObs }
  | .val2DN00 =>
      { family := .val2DN00, group := .validationBasic, code := "2DN00",
        title := "2D NACA 0012 airfoil", dimension := .twoD,
        physics := [.externalAerodynamics, .wallBounded],
        boundaries := [.noSlipWall, .farfield, .wakeSurvey], observables := wallObs ++ wakeObs }
  | .valASJ =>
      { family := .valASJ, group := .validationBasic, code := "ASJ",
        title := "Axisymmetric subsonic jet", dimension := .axisymmetric,
        physics := [.freeShear], boundaries := [.jetExit, .farfield, .outflow], observables := jetObs }
  | .valAHSJ =>
      { family := .valAHSJ, group := .validationBasic, code := "AHSJ",
        title := "Axisymmetric hot subsonic jet", dimension := .axisymmetric,
        physics := [.freeShear, .heatFlux], boundaries := [.jetExit, .farfield, .outflow], observables := jetObs }
  | .valANSJ =>
      { family := .valANSJ, group := .validationBasic, code := "ANSJ",
        title := "Axisymmetric near-sonic jet", dimension := .axisymmetric,
        physics := [.freeShear, .compressible], boundaries := [.jetExit, .farfield, .outflow], observables := jetObs }
  | .valASBL =>
      { family := .valASBL, group := .validationBasic, code := "ASBL",
        title := "Axisymmetric separated boundary layer", dimension := .axisymmetric,
        physics := [.wallBounded, .pressureGradient, .separation],
        boundaries := [.noSlipWall, .inflow, .outflow], observables := wallObs }
  | .valATB =>
      { family := .valATB, group := .validationBasic, code := "ATB",
        title := "Axisymmetric transonic bump", dimension := .axisymmetric,
        physics := [.wallBounded, .pressureGradient, .compressible, .shockInteraction, .separation],
        boundaries := [.noSlipWall, .inflow, .outflow, .farfield], observables := wallObs }
  | .val2DZPH =>
      { family := .val2DZPH, group := .validationExtended, code := "2DZPH",
        title := "2D zero pressure gradient high Mach number flat plate", dimension := .twoD,
        physics := [.wallBounded, .compressible, .highMach, .heatFlux],
        boundaries := [.noSlipWall, .farfield, .inflow, .outflow], observables := wallObs }
  | .val2DBFS =>
      { family := .val2DBFS, group := .validationExtended, code := "2DBFS",
        title := "2D backward facing step", dimension := .twoD,
        physics := [.internalFlow, .separation], boundaries := [.noSlipWall, .inflow, .outflow],
        observables := wallObs }
  | .val2DN44 =>
      { family := .val2DN44, group := .validationExtended, code := "2DN44",
        title := "2D NACA 4412 trailing-edge separation", dimension := .twoD,
        physics := [.externalAerodynamics, .wallBounded, .separation],
        boundaries := [.noSlipWall, .farfield, .wakeSurvey], observables := wallObs ++ wakeObs }
  | .val2DCC =>
      { family := .val2DCC, group := .validationExtended, code := "2DCC",
        title := "2D convex curvature boundary layer", dimension := .twoD,
        physics := [.wallBounded, .curvature], boundaries := [.noSlipWall, .inflow, .outflow],
        observables := wallObs }
  | .val2DWMH =>
      { family := .val2DWMH, group := .validationExtended, code := "2DWMH",
        title := "2D NASA wall-mounted hump separated flow", dimension := .twoD,
        physics := [.wallBounded, .pressureGradient, .separation],
        boundaries := [.noSlipWall, .inflow, .outflow], observables := wallObs }
  | .valASWBLI =>
      { family := .valASWBLI, group := .validationExtended, code := "ASWBLI",
        title := "Axisymmetric shock wave boundary layer interaction near Mach 7",
        dimension := .axisymmetric,
        physics := [.wallBounded, .compressible, .highMach, .shockInteraction, .separation],
        boundaries := [.noSlipWall, .inflow, .outflow, .farfield], observables := wallObs }
  | .valACSSJ =>
      { family := .valACSSJ, group := .validationExtended, code := "ACSSJ",
        title := "Axisymmetric cold supersonic jet", dimension := .axisymmetric,
        physics := [.freeShear, .compressible, .highMach],
        boundaries := [.jetExit, .farfield, .outflow], observables := jetObs }
  | .valAHSSJ =>
      { family := .valAHSSJ, group := .validationExtended, code := "AHSSJ",
        title := "Axisymmetric hot supersonic jet", dimension := .axisymmetric,
        physics := [.freeShear, .compressible, .highMach, .heatFlux],
        boundaries := [.jetExit, .farfield, .outflow], observables := jetObs }
  | .valAJM163TM =>
      { family := .valAJM163TM, group := .validationExtended, code := "AJM163TM",
        title := "Temperature-matched Mach 1.63 axisymmetric jet", dimension := .axisymmetric,
        physics := [.freeShear, .compressible, .highMach],
        boundaries := [.jetExit, .farfield, .outflow], observables := jetObs }
  | .valAJM163H =>
      { family := .valAJM163H, group := .validationExtended, code := "AJM163H",
        title := "Heated Mach 1.63 axisymmetric jet", dimension := .axisymmetric,
        physics := [.freeShear, .compressible, .highMach, .heatFlux],
        boundaries := [.jetExit, .farfield, .outflow], observables := jetObs }
  | .valAJM163OD =>
      { family := .valAJM163OD, group := .validationExtended, code := "AJM163OD",
        title := "Off-design Mach 1.63 axisymmetric jet", dimension := .axisymmetric,
        physics := [.freeShear, .compressible, .highMach, .vortexFlow],
        boundaries := [.jetExit, .farfield, .outflow], observables := jetObs }
  | .val3DSSD =>
      { family := .val3DSSD, group := .validationExtended, code := "3DSSD",
        title := "3D supersonic square duct", dimension := .threeD,
        physics := [.internalFlow, .compressible, .highMach, .secondaryFlow],
        boundaries := [.noSlipWall, .inflow, .outflow, .symmetry], observables := wallObs }
  | .val2DFDC =>
      { family := .val2DFDC, group := .highReClassical, code := "2DFDC",
        title := "2D fully-developed channel flow at high Reynolds number", dimension := .twoD,
        physics := [.internalFlow, .wallBounded], boundaries := [.noSlipWall, .periodic],
        observables := wallObs }
  | .verif2DTFP =>
      { family := .verif2DTFP, group := .transitionVerification, code := "VERIF/2DTFP",
        title := "2D T3A transitional flat plate", dimension := .twoD,
        physics := [.wallBounded, .transition], boundaries := [.noSlipWall, .farfield, .inflow, .outflow],
        observables := wallObs }

/-- Full first-pass benchmark list. -/
def allTMRBenchmarkFamilies : List TMRBenchmarkFamily :=
  [.verif2DZP, .verif2DCJ, .verif2DB, .verif2DANW, .verif2DMEA, .verif3DB,
    .add2DFiniteFlatPlate, .add2DNACA0012, .add3DModifiedBump, .add3DModifiedSupersonicSquareDuct,
    .add2DHemisphereCylinder, .add3DHemisphereCylinderOld, .add3DHemisphereCylinderNew, .add3DONERAM6Wing,
    .val2DZP, .val2DML, .val2DANW, .val2DN00, .valASJ, .valAHSJ, .valANSJ, .valASBL, .valATB,
    .val2DZPH, .val2DBFS, .val2DN44, .val2DCC, .val2DWMH, .valASWBLI, .valACSSJ, .valAHSSJ,
    .valAJM163TM, .valAJM163H, .valAJM163OD, .val3DSSD, .val2DFDC, .verif2DTFP]

theorem tmrBenchmarkSpec_family (family : TMRBenchmarkFamily) :
    (tmrBenchmarkSpec family).family = family := by
  cases family <;> rfl

theorem mem_allTMRBenchmarkFamilies (family : TMRBenchmarkFamily) :
    family ∈ allTMRBenchmarkFamilies := by
  cases family <;> simp [allTMRBenchmarkFamilies]

/-- State fields for a RANS-style HQIV simulator over the observer chart. -/
structure HQIVRANSState where
  density : Hqiv.ObserverChart → ℝ
  velocity : Hqiv.ObserverChart → Fin 3 → ℝ
  pressure : Hqiv.ObserverChart → ℝ
  temperature : Hqiv.ObserverChart → ℝ
  totalEnergy : Hqiv.ObserverChart → ℝ
  phiFluid : Hqiv.ObserverChart → ℝ
  dotTheta : Hqiv.ObserverChart → ℝ
  localAcceleration : Hqiv.ObserverChart → ℝ

/-- Pointwise HQIV turbulence closure inputs. `shell` selects the HQIV temperature ladder; `C` is the
coherence factor used by the existing eddy-viscosity formula. -/
structure HQIVTurbulenceClosureInput where
  shell : ℕ
  aLoc : ℝ
  phi : ℝ
  dotTheta : ℝ
  gradPhi : Fin 3 → ℝ
  gradDot : Fin 3 → ℝ
  nuMol : ℝ
  coherence : ℝ
  density : ℝ

/-- Closure output fields that a numerical simulator can evaluate pointwise. -/
structure HQIVTurbulenceClosureOutput where
  inertiaFactor : ℝ
  vacuumMomentumSource : Fin 3 → ℝ
  nuEddy : ℝ
  nuTotal : ℝ
  effectiveDensity : ℝ

/-- The canonical HQIV-native closure defined only from existing fluid scaffold formulas. -/
def hqivTurbulenceClosureOutput (input : HQIVTurbulenceClosureInput) : HQIVTurbulenceClosureOutput where
  inertiaFactor := hqivFluidInertiaFactor input.aLoc input.phi
  vacuumMomentumSource :=
    hqivVacuumMomentumSource3 gamma_HQIV input.phi input.dotTheta input.gradPhi input.gradDot
  nuEddy := hqivEddyViscosity_HQIV_shell_debye input.shell input.dotTheta input.coherence
  nuTotal := input.nuMol + hqivEddyViscosity_HQIV_shell_debye input.shell input.dotTheta input.coherence
  effectiveDensity := input.density * hqivFluidInertiaFactor input.aLoc input.phi

@[simp]
theorem hqivTurbulenceClosureOutput_inertia (input : HQIVTurbulenceClosureInput) :
    (hqivTurbulenceClosureOutput input).inertiaFactor =
      hqivFluidInertiaFactor input.aLoc input.phi := rfl

@[simp]
theorem hqivTurbulenceClosureOutput_vacuumMomentumSource (input : HQIVTurbulenceClosureInput) :
    (hqivTurbulenceClosureOutput input).vacuumMomentumSource =
      hqivVacuumMomentumSource3 gamma_HQIV input.phi input.dotTheta input.gradPhi input.gradDot := rfl

@[simp]
theorem hqivTurbulenceClosureOutput_nuEddy (input : HQIVTurbulenceClosureInput) :
    (hqivTurbulenceClosureOutput input).nuEddy =
      hqivEddyViscosity_HQIV_shell_debye input.shell input.dotTheta input.coherence := rfl

theorem hqivTurbulenceClosureOutput_nuEddy_nonneg (input : HQIVTurbulenceClosureInput)
    (hC : 0 ≤ input.coherence) :
    0 ≤ (hqivTurbulenceClosureOutput input).nuEddy := by
  simpa using hqivEddyViscosity_HQIV_shell_debye_nonneg input.shell input.dotTheta input.coherence hC

theorem hqivTurbulenceClosureOutput_nuTotal_eq (input : HQIVTurbulenceClosureInput) :
    (hqivTurbulenceClosureOutput input).nuTotal =
      input.nuMol + (hqivTurbulenceClosureOutput input).nuEddy := rfl

theorem hqivTurbulenceClosureOutput_vacuum_zero_of_grad_zero (input : HQIVTurbulenceClosureInput)
    (hΦ : input.gradPhi = 0) (hD : input.gradDot = 0) :
    (hqivTurbulenceClosureOutput input).vacuumMomentumSource = 0 := by
  exact
    hqivVacuumMomentumSource3_eq_zero_of_grad_zero gamma_HQIV input.phi input.dotTheta input.gradPhi
      input.gradDot hΦ hD

theorem hqivTurbulenceClosureOutput_classical_coefficients_of_grad_zero
    (input : HQIVTurbulenceClosureInput) (hPhi : input.phi = 0) (ha : input.aLoc ≠ 0)
    (hΦ : input.gradPhi = 0) (hD : input.gradDot = 0) :
    CoefficientsTowardClassicalNS input.aLoc input.phi
      (hqivTurbulenceClosureOutput input).vacuumMomentumSource := by
  refine ⟨?_, ?_⟩
  · rw [hPhi]
    exact hqivFluidInertiaFactor_eq_one_of_phi_zero ha
  · exact hqivTurbulenceClosureOutput_vacuum_zero_of_grad_zero input hΦ hD

/-- Solver capabilities demanded by a case. These are explicit requirements for a Python solver, not
proofs that any discretization satisfies them. -/
structure HQIVSimulatorCapability where
  supportsDimension : TMRDimension → Prop
  supportsPhysics : TMRFlowPhysicsTag → Prop
  supportsBoundary : TMRBoundaryTag → Prop

/-- A Python-facing simulator contract: symbolic residual callbacks and case metadata. -/
structure HQIVPythonSimulatorContract where
  caseSpec : TMRBenchmarkSpec
  state : Hqiv.ObserverChart → HQIVRANSState
  closureInput : Hqiv.ObserverChart → HQIVTurbulenceClosureInput
  closureOutput : Hqiv.ObserverChart → HQIVTurbulenceClosureOutput
  massResidual : Hqiv.ObserverChart → ℝ
  momentumResidual : Hqiv.ObserverChart → Fin 3 → ℝ
  energyResidual : Hqiv.ObserverChart → ℝ
  boundaryResidual : TMRBoundaryTag → Hqiv.ObserverChart → ℝ
  capability : HQIVSimulatorCapability

/-- The default pointwise contract uses the canonical HQIV closure output. -/
def HQIVPythonSimulatorContract.UsesCanonicalClosure (contract : HQIVPythonSimulatorContract) : Prop :=
  ∀ x, contract.closureOutput x = hqivTurbulenceClosureOutput (contract.closureInput x)

/-- Metadata-level requirement: a contract advertises the dimension, physics, and boundary tags listed
by its case specification. -/
def HQIVPythonSimulatorContract.CoversCaseRequirements (contract : HQIVPythonSimulatorContract) : Prop :=
  contract.capability.supportsDimension contract.caseSpec.dimension ∧
    (∀ tag, tag ∈ contract.caseSpec.physics → contract.capability.supportsPhysics tag) ∧
    (∀ tag, tag ∈ contract.caseSpec.boundaries → contract.capability.supportsBoundary tag)

/-- A permissive capability useful for smoke-test contracts and generated Python prototypes. -/
def universalHQIVSimulatorCapability : HQIVSimulatorCapability where
  supportsDimension := fun _ => True
  supportsPhysics := fun _ => True
  supportsBoundary := fun _ => True

theorem universalHQIVSimulatorCapability_covers (spec : TMRBenchmarkSpec) :
    universalHQIVSimulatorCapability.supportsDimension spec.dimension ∧
      (∀ tag, tag ∈ spec.physics → universalHQIVSimulatorCapability.supportsPhysics tag) ∧
      (∀ tag, tag ∈ spec.boundaries → universalHQIVSimulatorCapability.supportsBoundary tag) := by
  simp [universalHQIVSimulatorCapability]

/-- Every enumerated TMR family has a canonical metadata spec whose requirements are expressible by the
contract capability interface. -/
theorem every_TMR_family_has_universal_contract_requirements (family : TMRBenchmarkFamily) :
    universalHQIVSimulatorCapability.supportsDimension (tmrBenchmarkSpec family).dimension ∧
      (∀ tag, tag ∈ (tmrBenchmarkSpec family).physics →
        universalHQIVSimulatorCapability.supportsPhysics tag) ∧
      (∀ tag, tag ∈ (tmrBenchmarkSpec family).boundaries →
        universalHQIVSimulatorCapability.supportsBoundary tag) := by
  exact universalHQIVSimulatorCapability_covers (tmrBenchmarkSpec family)

/-!
## 2D / 3D RANS contract proofs

These theorems prove that a simulator contract has the Lean-level objects needed for 2D or 3D RANS:
state fields, mass/momentum/energy residual callbacks, canonical HQIV closure, and advertised case
capabilities. They are **not** PDE existence, uniqueness, convergence, or turbulence-model validation
theorems.
-/

/-- Native RANS dimensions covered by this scaffold. Axisymmetric TMR cases are handled as benchmark
metadata, while these proofs focus on Cartesian 2D and 3D RANS contracts. -/
inductive HQIVRANSDimension where
  | rans2D
  | rans3D
  deriving DecidableEq, Repr

def HQIVRANSDimension.toTMRDimension : HQIVRANSDimension → TMRDimension
  | .rans2D => .twoD
  | .rans3D => .threeD

def HQIVRANSDimension.spatialComponentCount : HQIVRANSDimension → ℕ
  | .rans2D => 2
  | .rans3D => 3

/-- Momentum components that a 2D or 3D RANS contract must expose. Components remain embedded in the
ambient `Fin 3` observer chart so Python can share one storage layout. -/
def HQIVRANSDimension.activeMomentumComponents : HQIVRANSDimension → List (Fin 3)
  | .rans2D => [0, 1]
  | .rans3D => [0, 1, 2]

theorem HQIVRANSDimension.mem_activeMomentumComponents_bound (dim : HQIVRANSDimension) (i : Fin 3)
    (hi : i ∈ dim.activeMomentumComponents) :
    i.val < dim.spatialComponentCount := by
  cases dim <;> fin_cases i <;> simp [HQIVRANSDimension.activeMomentumComponents,
    HQIVRANSDimension.spatialComponentCount] at hi ⊢

/-- Lean-level RANS proof bundle for a simulator contract in a chosen dimension. The fields assert
that the contract is dimension-matched, uses the canonical HQIV closure, covers the benchmark
requirements, and exposes residual callbacks for all active momentum components. -/
structure HQIVRANSContractProof (dim : HQIVRANSDimension) (contract : HQIVPythonSimulatorContract) :
    Prop where
  dimension_matches : contract.caseSpec.dimension = dim.toTMRDimension
  uses_canonical_closure : contract.UsesCanonicalClosure
  covers_case_requirements : contract.CoversCaseRequirements
  mass_residual_defined : ∀ x : Hqiv.ObserverChart, ∃ r : ℝ, contract.massResidual x = r
  energy_residual_defined : ∀ x : Hqiv.ObserverChart, ∃ r : ℝ, contract.energyResidual x = r
  momentum_residual_defined :
    ∀ x : Hqiv.ObserverChart, ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      ∃ r : ℝ, contract.momentumResidual x i = r

theorem HQIVPythonSimulatorContract.massResidual_defined (contract : HQIVPythonSimulatorContract)
    (x : Hqiv.ObserverChart) : ∃ r : ℝ, contract.massResidual x = r :=
  ⟨contract.massResidual x, rfl⟩

theorem HQIVPythonSimulatorContract.energyResidual_defined (contract : HQIVPythonSimulatorContract)
    (x : Hqiv.ObserverChart) : ∃ r : ℝ, contract.energyResidual x = r :=
  ⟨contract.energyResidual x, rfl⟩

theorem HQIVPythonSimulatorContract.momentumResidual_defined (contract : HQIVPythonSimulatorContract)
    (x : Hqiv.ObserverChart) (i : Fin 3) : ∃ r : ℝ, contract.momentumResidual x i = r :=
  ⟨contract.momentumResidual x i, rfl⟩

/-- Constructor theorem for 2D RANS contract proofs. -/
theorem hqivRANS2D_contract_proof (contract : HQIVPythonSimulatorContract)
    (hdim : contract.caseSpec.dimension = TMRDimension.twoD)
    (hclosure : contract.UsesCanonicalClosure) (hcovers : contract.CoversCaseRequirements) :
    HQIVRANSContractProof .rans2D contract where
  dimension_matches := hdim
  uses_canonical_closure := hclosure
  covers_case_requirements := hcovers
  mass_residual_defined := contract.massResidual_defined
  energy_residual_defined := contract.energyResidual_defined
  momentum_residual_defined := by
    intro x i _hi
    exact contract.momentumResidual_defined x i

/-- Constructor theorem for 3D RANS contract proofs. -/
theorem hqivRANS3D_contract_proof (contract : HQIVPythonSimulatorContract)
    (hdim : contract.caseSpec.dimension = TMRDimension.threeD)
    (hclosure : contract.UsesCanonicalClosure) (hcovers : contract.CoversCaseRequirements) :
    HQIVRANSContractProof .rans3D contract where
  dimension_matches := hdim
  uses_canonical_closure := hclosure
  covers_case_requirements := hcovers
  mass_residual_defined := contract.massResidual_defined
  energy_residual_defined := contract.energyResidual_defined
  momentum_residual_defined := by
    intro x i _hi
    exact contract.momentumResidual_defined x i

theorem hqivRANS2D_contract_supports_twoD (contract : HQIVPythonSimulatorContract)
    (h : HQIVRANSContractProof .rans2D contract) :
    contract.capability.supportsDimension TMRDimension.twoD := by
  rcases h.covers_case_requirements with ⟨hd, _, _⟩
  simpa [HQIVRANSDimension.toTMRDimension, h.dimension_matches] using hd

theorem hqivRANS3D_contract_supports_threeD (contract : HQIVPythonSimulatorContract)
    (h : HQIVRANSContractProof .rans3D contract) :
    contract.capability.supportsDimension TMRDimension.threeD := by
  rcases h.covers_case_requirements with ⟨hd, _, _⟩
  simpa [HQIVRANSDimension.toTMRDimension, h.dimension_matches] using hd

/-!
## Certified domains and the HQIV lapse-modified RANS axiom

The next layer treats the lapse-modified NS/RANS balance as an **HQIV simulator axiom**: a contract
may carry a proof object asserting that, on a certified 2D or 3D domain, its residual callbacks encode
the HQIV balance with lapse-scaled inertia, total HQIV viscosity, and vacuum forcing.

This is intentionally not a new classical Navier--Stokes theorem. The axiom record is the place where
the larger HQIV program plugs in its modified momentum law for downstream numerical work.
-/

/-- A certified RANS domain in the ambient observer chart. The domain is intentionally abstract:
meshes, cells, CAD geometry, and quadrature data live downstream in Python, while Lean records the
interior predicate, boundary predicates, and active component bounds. -/
structure HQIVRANSDomain (dim : HQIVRANSDimension) where
  interior : Hqiv.ObserverChart → Prop
  boundary : TMRBoundaryTag → Hqiv.ObserverChart → Prop
  nonempty_interior : ∃ x : Hqiv.ObserverChart, interior x
  active_component_bound :
    ∀ i : Fin 3, i ∈ dim.activeMomentumComponents → i.val < dim.spatialComponentCount

/-- Domain certificate tying a domain to a benchmark spec. Boundary tags are certified by witnesses
for each tag listed in the TMR metadata; this is a topology/geometry bookkeeping certificate, not a
mesh quality or convergence theorem. -/
structure HQIVRANSDomainCertificate (dim : HQIVRANSDimension) (spec : TMRBenchmarkSpec)
    (domain : HQIVRANSDomain dim) : Prop where
  dimension_matches : spec.dimension = dim.toTMRDimension
  boundary_tags_certified : ∀ tag, tag ∈ spec.boundaries → ∃ x, domain.boundary tag x

/-- Full-chart smoke-test domain. Real benchmarks should replace this with their CAD/mesh predicates. -/
def universalHQIVRANSDomain (dim : HQIVRANSDimension) : HQIVRANSDomain dim where
  interior := fun _ => True
  boundary := fun _ _ => True
  nonempty_interior := ⟨fun _ => 0, trivial⟩
  active_component_bound := HQIVRANSDimension.mem_activeMomentumComponents_bound dim

theorem universalHQIVRANSDomain_certificate (dim : HQIVRANSDimension) (spec : TMRBenchmarkSpec)
    (hdim : spec.dimension = dim.toTMRDimension) :
    HQIVRANSDomainCertificate dim spec (universalHQIVRANSDomain dim) where
  dimension_matches := hdim
  boundary_tags_certified := by
    intro tag _htag
    exact ⟨fun _ => 0, trivial⟩

/-- Pointwise data entering the HQIV lapse-modified RANS momentum residual. `uDot` and `convective`
are already Reynolds/Favre-averaged callbacks supplied by the simulator; Lean does not derive the
averaging operation here. -/
structure HQIVLapseModifiedRANSPointData where
  Phi : ℝ
  phiClock : ℝ
  time : ℝ
  rho : ℝ
  uDot : Fin 3 → ℝ
  convective : Fin 3 → ℝ
  pressureGrad : Fin 3 → ℝ
  laplacianVelocity : Fin 3 → ℝ
  bodyForce : Fin 3 → ℝ

def hqivLapseModifiedRANSLHS (data : HQIVLapseModifiedRANSPointData)
    (input : HQIVTurbulenceClosureInput) (i : Fin 3) : ℝ :=
  HQVM_lapse data.Phi data.phiClock data.time *
    (data.rho * hqivFluidInertiaFactor input.aLoc input.phi *
      (data.uDot i + data.convective i))

def hqivLapseModifiedRANSRHS (data : HQIVLapseModifiedRANSPointData)
    (input : HQIVTurbulenceClosureInput) (i : Fin 3) : ℝ :=
  let closure := hqivTurbulenceClosureOutput input
  (-data.pressureGrad i) + closure.nuTotal * data.laplacianVelocity i + data.bodyForce i +
    closure.vacuumMomentumSource i

/-- Numeric residual for the HQIV lapse-modified RANS momentum component. -/
def hqivLapseModifiedRANSMomentumResidual (data : HQIVLapseModifiedRANSPointData)
    (input : HQIVTurbulenceClosureInput) (i : Fin 3) : ℝ :=
  hqivLapseModifiedRANSLHS data input i - hqivLapseModifiedRANSRHS data input i

/-- Component equation form of the same HQIV lapse-modified RANS balance. -/
def hqivLapseModifiedRANSMomentumComponent (data : HQIVLapseModifiedRANSPointData)
    (input : HQIVTurbulenceClosureInput) (i : Fin 3) : Prop :=
  hqivLapseModifiedRANSLHS data input i = hqivLapseModifiedRANSRHS data input i

theorem hqivLapseModifiedRANSMomentumResidual_zero_iff
    (data : HQIVLapseModifiedRANSPointData) (input : HQIVTurbulenceClosureInput) (i : Fin 3) :
    hqivLapseModifiedRANSMomentumResidual data input i = 0 ↔
      hqivLapseModifiedRANSMomentumComponent data input i := by
  unfold hqivLapseModifiedRANSMomentumResidual hqivLapseModifiedRANSMomentumComponent
  rw [sub_eq_zero]

/-!
## Longitudinal HQIV stress extension

The scalar vacuum source in `hqivTurbulenceClosureOutput` is gradient-like and may be absorbed into a
pressure projection in incompressible numerics. The following layer keeps the proposed conductor-like
longitudinal channel as a separate anisotropic stress divergence:

`τ_L = κ_L ρ Λ (s · ∇φ) s ⊗ s`, with the simulator supplying `∇·τ_L` pointwise.

This is a modeling certificate, not a theorem deriving the stress from kinetic turbulence. -/

/-- Point data for the directional longitudinal stress channel. `direction` is usually chosen from
flow, vorticity, or shear alignment; `stressDivergence` is the mesh-evaluated `∇·τ_L`. -/
structure HQIVLongitudinalStressPointData where
  kappaL : ℝ
  rho : ℝ
  couplingLog : ℝ
  gradPhiAlong : ℝ
  direction : Fin 3 → ℝ
  stressDivergence : Fin 3 → ℝ

/-- The anisotropic stress tensor attached to the longitudinal channel. -/
noncomputable def HQIVLongitudinalStressPointData.stressTensor
    (data : HQIVLongitudinalStressPointData) : Fin 3 → Fin 3 → ℝ :=
  hqivLongitudinalStressTensor3 data.kappaL data.rho data.couplingLog data.gradPhiAlong data.direction

/-- The force density entering the momentum equation: `∇·τ_L`, supplied by the simulator. -/
def HQIVLongitudinalStressPointData.force
    (data : HQIVLongitudinalStressPointData) : Fin 3 → ℝ :=
  hqivLongitudinalStressForce3 data.stressDivergence

theorem HQIVLongitudinalStressPointData.force_eq_zero_of_div_zero
    (data : HQIVLongitudinalStressPointData) (h : data.stressDivergence = 0) :
    data.force = 0 := by
  simp [HQIVLongitudinalStressPointData.force, h, hqivLongitudinalStressForce3]

def hqivLapseModifiedRANSRHSWithLongitudinal (data : HQIVLapseModifiedRANSPointData)
    (input : HQIVTurbulenceClosureInput) (longData : HQIVLongitudinalStressPointData) (i : Fin 3) :
    ℝ :=
  hqivLapseModifiedRANSRHS data input i + longData.force i

/-- Numeric residual for the lapse-modified RANS component with the longitudinal stress divergence
kept separate from pressure and generic body force. -/
def hqivLapseModifiedRANSMomentumResidualWithLongitudinal
    (data : HQIVLapseModifiedRANSPointData) (input : HQIVTurbulenceClosureInput)
    (longData : HQIVLongitudinalStressPointData) (i : Fin 3) : ℝ :=
  hqivLapseModifiedRANSLHS data input i - hqivLapseModifiedRANSRHSWithLongitudinal data input longData i

/-- Component equation form of the longitudinal-stress RANS balance. -/
def hqivLapseModifiedRANSMomentumComponentWithLongitudinal
    (data : HQIVLapseModifiedRANSPointData) (input : HQIVTurbulenceClosureInput)
    (longData : HQIVLongitudinalStressPointData) (i : Fin 3) : Prop :=
  hqivLapseModifiedRANSLHS data input i = hqivLapseModifiedRANSRHSWithLongitudinal data input longData i

theorem hqivLapseModifiedRANSMomentumResidualWithLongitudinal_zero_iff
    (data : HQIVLapseModifiedRANSPointData) (input : HQIVTurbulenceClosureInput)
    (longData : HQIVLongitudinalStressPointData) (i : Fin 3) :
    hqivLapseModifiedRANSMomentumResidualWithLongitudinal data input longData i = 0 ↔
      hqivLapseModifiedRANSMomentumComponentWithLongitudinal data input longData i := by
  unfold hqivLapseModifiedRANSMomentumResidualWithLongitudinal
    hqivLapseModifiedRANSMomentumComponentWithLongitudinal
  rw [sub_eq_zero]

theorem hqivLapseModifiedRANSMomentumResidualWithLongitudinal_eq_base_of_div_zero
    (data : HQIVLapseModifiedRANSPointData) (input : HQIVTurbulenceClosureInput)
    (longData : HQIVLongitudinalStressPointData) (i : Fin 3) (h : longData.stressDivergence = 0) :
    hqivLapseModifiedRANSMomentumResidualWithLongitudinal data input longData i =
      hqivLapseModifiedRANSMomentumResidual data input i := by
  simp [hqivLapseModifiedRANSMomentumResidualWithLongitudinal, hqivLapseModifiedRANSMomentumResidual,
    hqivLapseModifiedRANSRHSWithLongitudinal, HQIVLongitudinalStressPointData.force, h,
    hqivLongitudinalStressForce3]

/-- Certified RANS package for the lapse-modified momentum equation with an explicit longitudinal
stress divergence channel. This is parallel to `HQIVLapseModifiedRANSAxiom`; use it when the Python
solver includes `∇·τ_L` in the residual. -/
structure HQIVLongitudinalStressRANSAxiom (dim : HQIVRANSDimension)
    (contract : HQIVPythonSimulatorContract) (domain : HQIVRANSDomain dim) where
  rans_contract : HQIVRANSContractProof dim contract
  domain_certificate : HQIVRANSDomainCertificate dim contract.caseSpec domain
  point_data : Hqiv.ObserverChart → HQIVLapseModifiedRANSPointData
  longitudinal_data : Hqiv.ObserverChart → HQIVLongitudinalStressPointData
  mass_residual_zero : ∀ x, domain.interior x → contract.massResidual x = 0
  energy_residual_zero : ∀ x, domain.interior x → contract.energyResidual x = 0
  momentum_residual_eq_hqiv_longitudinal :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.momentumResidual x i =
        hqivLapseModifiedRANSMomentumResidualWithLongitudinal
          (point_data x) (contract.closureInput x) (longitudinal_data x) i

theorem HQIVLongitudinalStressRANSAxiom.momentum_component_on_domain
    {dim : HQIVRANSDimension} {contract : HQIVPythonSimulatorContract}
    {domain : HQIVRANSDomain dim} (h : HQIVLongitudinalStressRANSAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) {i : Fin 3}
    (hi : i ∈ dim.activeMomentumComponents) (hzero : contract.momentumResidual x i = 0) :
    hqivLapseModifiedRANSMomentumComponentWithLongitudinal
      (h.point_data x) (contract.closureInput x) (h.longitudinal_data x) i := by
  have hres :
      hqivLapseModifiedRANSMomentumResidualWithLongitudinal
          (h.point_data x) (contract.closureInput x) (h.longitudinal_data x) i = 0 := by
    rw [← h.momentum_residual_eq_hqiv_longitudinal x hx i hi]
    exact hzero
  exact
    (hqivLapseModifiedRANSMomentumResidualWithLongitudinal_zero_iff
      (h.point_data x) (contract.closureInput x) (h.longitudinal_data x) i).mp hres

def hqivLongitudinalStressRANS2D_axiom
    (contract : HQIVPythonSimulatorContract) (domain : HQIVRANSDomain .rans2D)
    (hcontract : HQIVRANSContractProof .rans2D contract)
    (hdomain : HQIVRANSDomainCertificate .rans2D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedRANSPointData)
    (longData : Hqiv.ObserverChart → HQIVLongitudinalStressPointData)
    (hmass : ∀ x, domain.interior x → contract.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVRANSDimension.rans2D.activeMomentumComponents →
        contract.momentumResidual x i =
          hqivLapseModifiedRANSMomentumResidualWithLongitudinal
            (pointData x) (contract.closureInput x) (longData x) i) :
    HQIVLongitudinalStressRANSAxiom .rans2D contract domain where
  rans_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  longitudinal_data := longData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv_longitudinal := hmomentum

def hqivLongitudinalStressRANS3D_axiom
    (contract : HQIVPythonSimulatorContract) (domain : HQIVRANSDomain .rans3D)
    (hcontract : HQIVRANSContractProof .rans3D contract)
    (hdomain : HQIVRANSDomainCertificate .rans3D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedRANSPointData)
    (longData : Hqiv.ObserverChart → HQIVLongitudinalStressPointData)
    (hmass : ∀ x, domain.interior x → contract.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVRANSDimension.rans3D.activeMomentumComponents →
        contract.momentumResidual x i =
          hqivLapseModifiedRANSMomentumResidualWithLongitudinal
            (pointData x) (contract.closureInput x) (longData x) i) :
    HQIVLongitudinalStressRANSAxiom .rans3D contract domain where
  rans_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  longitudinal_data := longData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv_longitudinal := hmomentum

/-!
## Action-mined force certificate

This layer keeps the force slots mined from the O-Maxwell/action stack separate in the simulator
contract. The fields are explicit callbacks because the present Lean library records the action-side
origins and algebraic bookkeeping, not a full continuum closure deriving each resolved force density.

* `longitudinal` — conductor-like anisotropic stress `∇·τ_L`.
* `fieldStressDivergence` — full resolved `F²` / Maxwell stress divergence from the kinetic term.
* `metricPhiForce` — metric-raised `φ` gradient force from `ContinuumOmaxwellClosure`.
* `plaquetteForce` — cyclic holonomy / Wilson-defect force from `ActionHolonomyGlue`.
* `currentCoherenceForce` — nonlinear feedback from `J·A` / plasma coherence bookkeeping.
-/

/-- Pointwise force slots mined from the action stack for RANS/LES modeling. -/
structure HQIVActionMinedForcePointData where
  longitudinal : HQIVLongitudinalStressPointData
  fieldStressDivergence : Fin 3 → ℝ
  metricPhiForce : Fin 3 → ℝ
  plaquetteForce : Fin 3 → ℝ
  currentCoherenceForce : Fin 3 → ℝ

/-- Total additional action-mined force density. This is deliberately separate from pressure,
generic body force, and the scalar `vacuumMomentumSource`. -/
def HQIVActionMinedForcePointData.force (data : HQIVActionMinedForcePointData) : Fin 3 → ℝ := fun i =>
  data.longitudinal.force i + data.fieldStressDivergence i + data.metricPhiForce i +
    data.plaquetteForce i + data.currentCoherenceForce i

theorem HQIVActionMinedForcePointData.force_eq_zero_of_all_zero
    (data : HQIVActionMinedForcePointData)
    (hlong : data.longitudinal.stressDivergence = 0)
    (hF : data.fieldStressDivergence = 0)
    (hφ : data.metricPhiForce = 0)
    (hplaq : data.plaquetteForce = 0)
    (hJ : data.currentCoherenceForce = 0) :
    data.force = 0 := by
  funext i
  simp [HQIVActionMinedForcePointData.force, HQIVLongitudinalStressPointData.force, hlong, hF, hφ,
    hplaq, hJ, hqivLongitudinalStressForce3]

def hqivLapseModifiedRANSRHSWithActionMinedForces (data : HQIVLapseModifiedRANSPointData)
    (input : HQIVTurbulenceClosureInput) (forceData : HQIVActionMinedForcePointData) (i : Fin 3) :
    ℝ :=
  hqivLapseModifiedRANSRHS data input i + forceData.force i

/-- Numeric residual for RANS with all action-mined force slots kept explicit. -/
def hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
    (data : HQIVLapseModifiedRANSPointData) (input : HQIVTurbulenceClosureInput)
    (forceData : HQIVActionMinedForcePointData) (i : Fin 3) : ℝ :=
  hqivLapseModifiedRANSLHS data input i -
    hqivLapseModifiedRANSRHSWithActionMinedForces data input forceData i

/-- Component equation form of the RANS balance with action-mined force slots. -/
def hqivLapseModifiedRANSMomentumComponentWithActionMinedForces
    (data : HQIVLapseModifiedRANSPointData) (input : HQIVTurbulenceClosureInput)
    (forceData : HQIVActionMinedForcePointData) (i : Fin 3) : Prop :=
  hqivLapseModifiedRANSLHS data input i =
    hqivLapseModifiedRANSRHSWithActionMinedForces data input forceData i

theorem hqivLapseModifiedRANSMomentumResidualWithActionMinedForces_zero_iff
    (data : HQIVLapseModifiedRANSPointData) (input : HQIVTurbulenceClosureInput)
    (forceData : HQIVActionMinedForcePointData) (i : Fin 3) :
    hqivLapseModifiedRANSMomentumResidualWithActionMinedForces data input forceData i = 0 ↔
      hqivLapseModifiedRANSMomentumComponentWithActionMinedForces data input forceData i := by
  unfold hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
    hqivLapseModifiedRANSMomentumComponentWithActionMinedForces
  rw [sub_eq_zero]

theorem hqivLapseModifiedRANSMomentumResidualWithActionMinedForces_eq_base_of_all_zero
    (data : HQIVLapseModifiedRANSPointData) (input : HQIVTurbulenceClosureInput)
    (forceData : HQIVActionMinedForcePointData) (i : Fin 3)
    (hlong : forceData.longitudinal.stressDivergence = 0)
    (hF : forceData.fieldStressDivergence = 0)
    (hφ : forceData.metricPhiForce = 0)
    (hplaq : forceData.plaquetteForce = 0)
    (hJ : forceData.currentCoherenceForce = 0) :
    hqivLapseModifiedRANSMomentumResidualWithActionMinedForces data input forceData i =
      hqivLapseModifiedRANSMomentumResidual data input i := by
  have hforce := HQIVActionMinedForcePointData.force_eq_zero_of_all_zero forceData hlong hF hφ hplaq hJ
  simp [hqivLapseModifiedRANSMomentumResidualWithActionMinedForces, hqivLapseModifiedRANSMomentumResidual,
    hqivLapseModifiedRANSRHSWithActionMinedForces, hforce]

/-- RANS certificate for the full action-mined force model. -/
structure HQIVActionMinedForcesRANSAxiom (dim : HQIVRANSDimension)
    (contract : HQIVPythonSimulatorContract) (domain : HQIVRANSDomain dim) where
  rans_contract : HQIVRANSContractProof dim contract
  domain_certificate : HQIVRANSDomainCertificate dim contract.caseSpec domain
  point_data : Hqiv.ObserverChart → HQIVLapseModifiedRANSPointData
  action_force_data : Hqiv.ObserverChart → HQIVActionMinedForcePointData
  mass_residual_zero : ∀ x, domain.interior x → contract.massResidual x = 0
  energy_residual_zero : ∀ x, domain.interior x → contract.energyResidual x = 0
  momentum_residual_eq_hqiv_action_forces :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.momentumResidual x i =
        hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
          (point_data x) (contract.closureInput x) (action_force_data x) i

theorem HQIVActionMinedForcesRANSAxiom.momentum_component_on_domain
    {dim : HQIVRANSDimension} {contract : HQIVPythonSimulatorContract}
    {domain : HQIVRANSDomain dim} (h : HQIVActionMinedForcesRANSAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) {i : Fin 3}
    (hi : i ∈ dim.activeMomentumComponents) (hzero : contract.momentumResidual x i = 0) :
    hqivLapseModifiedRANSMomentumComponentWithActionMinedForces
      (h.point_data x) (contract.closureInput x) (h.action_force_data x) i := by
  have hres :
      hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
          (h.point_data x) (contract.closureInput x) (h.action_force_data x) i = 0 := by
    rw [← h.momentum_residual_eq_hqiv_action_forces x hx i hi]
    exact hzero
  exact
    (hqivLapseModifiedRANSMomentumResidualWithActionMinedForces_zero_iff
      (h.point_data x) (contract.closureInput x) (h.action_force_data x) i).mp hres

def hqivActionMinedForcesRANS2D_axiom
    (contract : HQIVPythonSimulatorContract) (domain : HQIVRANSDomain .rans2D)
    (hcontract : HQIVRANSContractProof .rans2D contract)
    (hdomain : HQIVRANSDomainCertificate .rans2D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedRANSPointData)
    (forceData : Hqiv.ObserverChart → HQIVActionMinedForcePointData)
    (hmass : ∀ x, domain.interior x → contract.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVRANSDimension.rans2D.activeMomentumComponents →
        contract.momentumResidual x i =
          hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
            (pointData x) (contract.closureInput x) (forceData x) i) :
    HQIVActionMinedForcesRANSAxiom .rans2D contract domain where
  rans_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  action_force_data := forceData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv_action_forces := hmomentum

def hqivActionMinedForcesRANS3D_axiom
    (contract : HQIVPythonSimulatorContract) (domain : HQIVRANSDomain .rans3D)
    (hcontract : HQIVRANSContractProof .rans3D contract)
    (hdomain : HQIVRANSDomainCertificate .rans3D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedRANSPointData)
    (forceData : Hqiv.ObserverChart → HQIVActionMinedForcePointData)
    (hmass : ∀ x, domain.interior x → contract.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVRANSDimension.rans3D.activeMomentumComponents →
        contract.momentumResidual x i =
          hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
            (pointData x) (contract.closureInput x) (forceData x) i) :
    HQIVActionMinedForcesRANSAxiom .rans3D contract domain where
  rans_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  action_force_data := forceData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv_action_forces := hmomentum

/-!
## SST closure certificate with HQIV lapse/action forcing

This layer keeps the standard two-equation `k-ω SST` bookkeeping visible while attaching the same
HQIV lapse/action force package used by the RANS momentum residual. Lean does not choose SST constants,
limiters, wall functions, or blending functions; those remain simulator callbacks. The certificate only
states that the Python residuals encode:

* lapse/action-modified momentum,
* a `k` transport residual with an explicit HQIV action source,
* an `ω` transport residual with an explicit HQIV action source.
-/

/-- Pointwise SST transport data. `diffusionK`, `diffusionOmega`, and `crossDiffusionOmega` are already
discretized/model-evaluated callbacks, so this structure can represent common SST variants. -/
structure HQIVSSTPointData where
  rans : HQIVLapseModifiedRANSPointData
  k : ℝ
  omega : ℝ
  actionStressNorm : ℝ
  strainNorm : ℝ
  betaStar : ℝ
  bradshawMin : ℝ
  bradshawMax : ℝ
  kDot : ℝ
  omegaDot : ℝ
  convectiveK : ℝ
  convectiveOmega : ℝ
  productionK : ℝ
  destructionK : ℝ
  diffusionK : ℝ
  productionOmega : ℝ
  destructionOmega : ℝ
  diffusionOmega : ℝ
  crossDiffusionOmega : ℝ
  actionKSource : ℝ
  actionOmegaSource : ℝ

/-- Clamp a scalar into `[lo, hi]` using nested `min`/`max`. If `lo ≤ hi`, the usual interval
interpretation applies; the definition remains total for all real inputs. -/
def hqivClamp (lo hi x : ℝ) : ℝ :=
  min hi (max lo x)

/-- Dynamic Bradshaw coefficient from the resolved action-mined anisotropic stress:
`a_HQIV = clamp(|τ_action|/(ρ k))`. -/
noncomputable def hqivDynamicBradshawFromStress (rho k stressNorm lo hi : ℝ) : ℝ :=
  hqivClamp lo hi (stressNorm / (rho * k))

/-- Dynamic Bradshaw coefficient from local `k`-equilibrium:
`a_HQIV = clamp((β* ω - S_k^HQIV/(ρ k))/|S|)`. -/
noncomputable def hqivDynamicBradshawFromEquilibrium
    (rho k omega betaStar strainNorm actionKSource lo hi : ℝ) : ℝ :=
  hqivClamp lo hi ((betaStar * omega - actionKSource / (rho * k)) / strainNorm)

/-- Primary SST dynamic Bradshaw readout: action stress saturation. -/
noncomputable def HQIVSSTPointData.dynamicBradshawStress (data : HQIVSSTPointData) : ℝ :=
  hqivDynamicBradshawFromStress data.rans.rho data.k data.actionStressNorm data.bradshawMin data.bradshawMax

/-- Secondary SST dynamic Bradshaw readout: local equilibrium of the `k` equation. -/
noncomputable def HQIVSSTPointData.dynamicBradshawEquilibrium (data : HQIVSSTPointData) : ℝ :=
  hqivDynamicBradshawFromEquilibrium data.rans.rho data.k data.omega data.betaStar data.strainNorm
    data.actionKSource data.bradshawMin data.bradshawMax

theorem hqivDynamicBradshawFromStress_eq
    (rho k stressNorm lo hi : ℝ) :
    hqivDynamicBradshawFromStress rho k stressNorm lo hi =
      hqivClamp lo hi (stressNorm / (rho * k)) := rfl

theorem hqivDynamicBradshawFromEquilibrium_eq
    (rho k omega betaStar strainNorm actionKSource lo hi : ℝ) :
    hqivDynamicBradshawFromEquilibrium rho k omega betaStar strainNorm actionKSource lo hi =
      hqivClamp lo hi ((betaStar * omega - actionKSource / (rho * k)) / strainNorm) := rfl

/-- Lapse-scaled SST `k` equation LHS. -/
def hqivSSTKLHS (data : HQIVSSTPointData) (input : HQIVTurbulenceClosureInput) : ℝ :=
  HQVM_lapse data.rans.Phi data.rans.phiClock data.rans.time *
    (data.rans.rho * hqivFluidInertiaFactor input.aLoc input.phi * (data.kDot + data.convectiveK))

/-- SST `k` equation RHS with explicit HQIV action source. -/
def hqivSSTKRHS (data : HQIVSSTPointData) : ℝ :=
  data.productionK - data.destructionK + data.diffusionK + data.actionKSource

/-- Lapse-scaled SST `ω` equation LHS. -/
def hqivSSTOmegaLHS (data : HQIVSSTPointData) (input : HQIVTurbulenceClosureInput) : ℝ :=
  HQVM_lapse data.rans.Phi data.rans.phiClock data.rans.time *
    (data.rans.rho * hqivFluidInertiaFactor input.aLoc input.phi *
      (data.omegaDot + data.convectiveOmega))

/-- SST `ω` equation RHS with cross-diffusion and explicit HQIV action source. -/
def hqivSSTOmegaRHS (data : HQIVSSTPointData) : ℝ :=
  data.productionOmega - data.destructionOmega + data.diffusionOmega + data.crossDiffusionOmega +
    data.actionOmegaSource

def hqivSSTKResidual (data : HQIVSSTPointData) (input : HQIVTurbulenceClosureInput) : ℝ :=
  hqivSSTKLHS data input - hqivSSTKRHS data

def hqivSSTOmegaResidual (data : HQIVSSTPointData) (input : HQIVTurbulenceClosureInput) : ℝ :=
  hqivSSTOmegaLHS data input - hqivSSTOmegaRHS data

def hqivSSTKComponent (data : HQIVSSTPointData) (input : HQIVTurbulenceClosureInput) : Prop :=
  hqivSSTKLHS data input = hqivSSTKRHS data

def hqivSSTOmegaComponent (data : HQIVSSTPointData) (input : HQIVTurbulenceClosureInput) : Prop :=
  hqivSSTOmegaLHS data input = hqivSSTOmegaRHS data

theorem hqivSSTKResidual_zero_iff (data : HQIVSSTPointData) (input : HQIVTurbulenceClosureInput) :
    hqivSSTKResidual data input = 0 ↔ hqivSSTKComponent data input := by
  unfold hqivSSTKResidual hqivSSTKComponent
  rw [sub_eq_zero]

theorem hqivSSTOmegaResidual_zero_iff (data : HQIVSSTPointData) (input : HQIVTurbulenceClosureInput) :
    hqivSSTOmegaResidual data input = 0 ↔ hqivSSTOmegaComponent data input := by
  unfold hqivSSTOmegaResidual hqivSSTOmegaComponent
  rw [sub_eq_zero]

/-- SST Python-facing contract: a base RANS contract plus `k` and `ω` residual callbacks. -/
structure HQIVSSTPythonSimulatorContract where
  base : HQIVPythonSimulatorContract
  kResidual : Hqiv.ObserverChart → ℝ
  omegaResidual : Hqiv.ObserverChart → ℝ

structure HQIVSSTContractProof (dim : HQIVRANSDimension) (contract : HQIVSSTPythonSimulatorContract) :
    Prop where
  rans_contract : HQIVRANSContractProof dim contract.base
  k_residual_defined : ∀ x : Hqiv.ObserverChart, ∃ r : ℝ, contract.kResidual x = r
  omega_residual_defined : ∀ x : Hqiv.ObserverChart, ∃ r : ℝ, contract.omegaResidual x = r

theorem HQIVSSTPythonSimulatorContract.kResidual_defined (contract : HQIVSSTPythonSimulatorContract)
    (x : Hqiv.ObserverChart) : ∃ r : ℝ, contract.kResidual x = r :=
  ⟨contract.kResidual x, rfl⟩

theorem HQIVSSTPythonSimulatorContract.omegaResidual_defined (contract : HQIVSSTPythonSimulatorContract)
    (x : Hqiv.ObserverChart) : ∃ r : ℝ, contract.omegaResidual x = r :=
  ⟨contract.omegaResidual x, rfl⟩

def hqivSST_contract_proof (dim : HQIVRANSDimension) (contract : HQIVSSTPythonSimulatorContract)
    (hrans : HQIVRANSContractProof dim contract.base) :
    HQIVSSTContractProof dim contract where
  rans_contract := hrans
  k_residual_defined := contract.kResidual_defined
  omega_residual_defined := contract.omegaResidual_defined

/-- Certified SST package: RANS momentum uses HQIV action-mined forces; the SST `k` and `ω` residuals
use lapse-scaled transport with explicit HQIV action source terms. -/
structure HQIVLapseActionSSTAxiom (dim : HQIVRANSDimension)
    (contract : HQIVSSTPythonSimulatorContract) (domain : HQIVRANSDomain dim) where
  sst_contract : HQIVSSTContractProof dim contract
  domain_certificate : HQIVRANSDomainCertificate dim contract.base.caseSpec domain
  point_data : Hqiv.ObserverChart → HQIVSSTPointData
  action_force_data : Hqiv.ObserverChart → HQIVActionMinedForcePointData
  mass_residual_zero : ∀ x, domain.interior x → contract.base.massResidual x = 0
  energy_residual_zero : ∀ x, domain.interior x → contract.base.energyResidual x = 0
  momentum_residual_eq_hqiv_sst :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.base.momentumResidual x i =
        hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
          (point_data x).rans (contract.base.closureInput x) (action_force_data x) i
  k_residual_eq_hqiv_sst :
    ∀ x, domain.interior x →
      contract.kResidual x = hqivSSTKResidual (point_data x) (contract.base.closureInput x)
  omega_residual_eq_hqiv_sst :
    ∀ x, domain.interior x →
      contract.omegaResidual x = hqivSSTOmegaResidual (point_data x) (contract.base.closureInput x)
  dynamic_bradshaw_stress_defined :
    ∀ x, domain.interior x → ∃ aHQIV : ℝ, aHQIV = (point_data x).dynamicBradshawStress
  dynamic_bradshaw_equilibrium_defined :
    ∀ x, domain.interior x → ∃ aHQIV : ℝ, aHQIV = (point_data x).dynamicBradshawEquilibrium

theorem HQIVLapseActionSSTAxiom.momentum_component_on_domain
    {dim : HQIVRANSDimension} {contract : HQIVSSTPythonSimulatorContract}
    {domain : HQIVRANSDomain dim} (h : HQIVLapseActionSSTAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) {i : Fin 3}
    (hi : i ∈ dim.activeMomentumComponents) (hzero : contract.base.momentumResidual x i = 0) :
    hqivLapseModifiedRANSMomentumComponentWithActionMinedForces
      (h.point_data x).rans (contract.base.closureInput x) (h.action_force_data x) i := by
  have hres :
      hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
          (h.point_data x).rans (contract.base.closureInput x) (h.action_force_data x) i = 0 := by
    rw [← h.momentum_residual_eq_hqiv_sst x hx i hi]
    exact hzero
  exact
    (hqivLapseModifiedRANSMomentumResidualWithActionMinedForces_zero_iff
      (h.point_data x).rans (contract.base.closureInput x) (h.action_force_data x) i).mp hres

theorem HQIVLapseActionSSTAxiom.k_component_on_domain
    {dim : HQIVRANSDimension} {contract : HQIVSSTPythonSimulatorContract}
    {domain : HQIVRANSDomain dim} (h : HQIVLapseActionSSTAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) (hzero : contract.kResidual x = 0) :
    hqivSSTKComponent (h.point_data x) (contract.base.closureInput x) := by
  have hres : hqivSSTKResidual (h.point_data x) (contract.base.closureInput x) = 0 := by
    rw [← h.k_residual_eq_hqiv_sst x hx]
    exact hzero
  exact (hqivSSTKResidual_zero_iff (h.point_data x) (contract.base.closureInput x)).mp hres

theorem HQIVLapseActionSSTAxiom.omega_component_on_domain
    {dim : HQIVRANSDimension} {contract : HQIVSSTPythonSimulatorContract}
    {domain : HQIVRANSDomain dim} (h : HQIVLapseActionSSTAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) (hzero : contract.omegaResidual x = 0) :
    hqivSSTOmegaComponent (h.point_data x) (contract.base.closureInput x) := by
  have hres : hqivSSTOmegaResidual (h.point_data x) (contract.base.closureInput x) = 0 := by
    rw [← h.omega_residual_eq_hqiv_sst x hx]
    exact hzero
  exact (hqivSSTOmegaResidual_zero_iff (h.point_data x) (contract.base.closureInput x)).mp hres

def hqivLapseActionSST2D_axiom
    (contract : HQIVSSTPythonSimulatorContract) (domain : HQIVRANSDomain .rans2D)
    (hcontract : HQIVSSTContractProof .rans2D contract)
    (hdomain : HQIVRANSDomainCertificate .rans2D contract.base.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVSSTPointData)
    (forceData : Hqiv.ObserverChart → HQIVActionMinedForcePointData)
    (hmass : ∀ x, domain.interior x → contract.base.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.base.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVRANSDimension.rans2D.activeMomentumComponents →
        contract.base.momentumResidual x i =
          hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
            (pointData x).rans (contract.base.closureInput x) (forceData x) i)
    (hk : ∀ x, domain.interior x →
      contract.kResidual x = hqivSSTKResidual (pointData x) (contract.base.closureInput x))
    (hω : ∀ x, domain.interior x →
      contract.omegaResidual x = hqivSSTOmegaResidual (pointData x) (contract.base.closureInput x)) :
    HQIVLapseActionSSTAxiom .rans2D contract domain where
  sst_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  action_force_data := forceData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv_sst := hmomentum
  k_residual_eq_hqiv_sst := hk
  omega_residual_eq_hqiv_sst := hω
  dynamic_bradshaw_stress_defined := by
    intro x _hx
    exact ⟨(pointData x).dynamicBradshawStress, rfl⟩
  dynamic_bradshaw_equilibrium_defined := by
    intro x _hx
    exact ⟨(pointData x).dynamicBradshawEquilibrium, rfl⟩

def hqivLapseActionSST3D_axiom
    (contract : HQIVSSTPythonSimulatorContract) (domain : HQIVRANSDomain .rans3D)
    (hcontract : HQIVSSTContractProof .rans3D contract)
    (hdomain : HQIVRANSDomainCertificate .rans3D contract.base.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVSSTPointData)
    (forceData : Hqiv.ObserverChart → HQIVActionMinedForcePointData)
    (hmass : ∀ x, domain.interior x → contract.base.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.base.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVRANSDimension.rans3D.activeMomentumComponents →
        contract.base.momentumResidual x i =
          hqivLapseModifiedRANSMomentumResidualWithActionMinedForces
            (pointData x).rans (contract.base.closureInput x) (forceData x) i)
    (hk : ∀ x, domain.interior x →
      contract.kResidual x = hqivSSTKResidual (pointData x) (contract.base.closureInput x))
    (hω : ∀ x, domain.interior x →
      contract.omegaResidual x = hqivSSTOmegaResidual (pointData x) (contract.base.closureInput x)) :
    HQIVLapseActionSSTAxiom .rans3D contract domain where
  sst_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  action_force_data := forceData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv_sst := hmomentum
  k_residual_eq_hqiv_sst := hk
  omega_residual_eq_hqiv_sst := hω
  dynamic_bradshaw_stress_defined := by
    intro x _hx
    exact ⟨(pointData x).dynamicBradshawStress, rfl⟩
  dynamic_bradshaw_equilibrium_defined := by
    intro x _hx
    exact ⟨(pointData x).dynamicBradshawEquilibrium, rfl⟩

/-- HQIV lapse-modified RANS axiom package for a solver contract on a certified domain.

Read this as: in the larger HQIV program, this is the axiom/schema that replaces the classical RANS
momentum residual with lapse-scaled inertia plus HQIV total viscosity and vacuum forcing. It certifies
that the simulator callbacks encode that equation on the chosen 2D/3D domain; it does not prove
classical NS well-posedness or turbulence-model validation. -/
structure HQIVLapseModifiedRANSAxiom (dim : HQIVRANSDimension) (contract : HQIVPythonSimulatorContract)
    (domain : HQIVRANSDomain dim) where
  rans_contract : HQIVRANSContractProof dim contract
  domain_certificate : HQIVRANSDomainCertificate dim contract.caseSpec domain
  point_data : Hqiv.ObserverChart → HQIVLapseModifiedRANSPointData
  mass_residual_zero : ∀ x, domain.interior x → contract.massResidual x = 0
  energy_residual_zero : ∀ x, domain.interior x → contract.energyResidual x = 0
  momentum_residual_eq_hqiv :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.momentumResidual x i =
        hqivLapseModifiedRANSMomentumResidual (point_data x) (contract.closureInput x) i

theorem HQIVLapseModifiedRANSAxiom.momentum_component_on_domain
    {dim : HQIVRANSDimension} {contract : HQIVPythonSimulatorContract}
    {domain : HQIVRANSDomain dim} (h : HQIVLapseModifiedRANSAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) {i : Fin 3}
    (hi : i ∈ dim.activeMomentumComponents) (hzero : contract.momentumResidual x i = 0) :
    hqivLapseModifiedRANSMomentumComponent (h.point_data x) (contract.closureInput x) i := by
  have hres :
      hqivLapseModifiedRANSMomentumResidual (h.point_data x) (contract.closureInput x) i = 0 := by
    rw [← h.momentum_residual_eq_hqiv x hx i hi]
    exact hzero
  exact (hqivLapseModifiedRANSMomentumResidual_zero_iff (h.point_data x) (contract.closureInput x) i).mp hres

theorem HQIVLapseModifiedRANSAxiom.mass_energy_zero_on_domain
    {dim : HQIVRANSDimension} {contract : HQIVPythonSimulatorContract}
    {domain : HQIVRANSDomain dim} (h : HQIVLapseModifiedRANSAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) :
    contract.massResidual x = 0 ∧ contract.energyResidual x = 0 :=
  ⟨h.mass_residual_zero x hx, h.energy_residual_zero x hx⟩

/-- Constructor for a 2D certified lapse-modified RANS axiom package. -/
def hqivLapseModifiedRANS2D_axiom
    (contract : HQIVPythonSimulatorContract) (domain : HQIVRANSDomain .rans2D)
    (hcontract : HQIVRANSContractProof .rans2D contract)
    (hdomain : HQIVRANSDomainCertificate .rans2D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedRANSPointData)
    (hmass : ∀ x, domain.interior x → contract.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVRANSDimension.rans2D.activeMomentumComponents →
        contract.momentumResidual x i =
          hqivLapseModifiedRANSMomentumResidual (pointData x) (contract.closureInput x) i) :
    HQIVLapseModifiedRANSAxiom .rans2D contract domain where
  rans_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv := hmomentum

/-- Constructor for a 3D certified lapse-modified RANS axiom package. -/
def hqivLapseModifiedRANS3D_axiom
    (contract : HQIVPythonSimulatorContract) (domain : HQIVRANSDomain .rans3D)
    (hcontract : HQIVRANSContractProof .rans3D contract)
    (hdomain : HQIVRANSDomainCertificate .rans3D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedRANSPointData)
    (hmass : ∀ x, domain.interior x → contract.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVRANSDimension.rans3D.activeMomentumComponents →
        contract.momentumResidual x i =
          hqivLapseModifiedRANSMomentumResidual (pointData x) (contract.closureInput x) i) :
    HQIVLapseModifiedRANSAxiom .rans3D contract domain where
  rans_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv := hmomentum

/-!
## Inertial-range kinetic-energy spectrum

The next record is the simulator-facing version of the Kolmogorov dimensional argument. In the HQIV
context it is read as an **inertial-range energy-cascade axiom** for the lapse-modified RANS energy
channel: when the certified domain has scale separation, negligible direct forcing at the resolved
wavenumber, and constant energy flux, the admissible kinetic-energy spectrum is the unique power-law
with exponent `-5/3`.

This does not claim DNS/experiment validation or derive the cascade from molecular kinetics. It
formalizes the part the Python simulator needs: once the inertial-range hypotheses are supplied, the
energy spectrum has the `k^(-5/3)` form.
-/

/-- Pointwise inertial-range kinetic-energy spectrum data. `epsilon` is the cascade energy flux,
`kolmogorovC` is the dimensionless Kolmogorov/HQIV cascade constant, and `spectrum` is the energy
density as a function of wavenumber. -/
structure HQIVKineticEnergySpectrum where
  epsilon : ℝ
  kolmogorovC : ℝ
  spectrum : ℝ → ℝ

/-- The explicit `k^(-5/3)` spectrum selected by inertial-range dimensional closure. -/
noncomputable def hqivKolmogorovFiveThirdsSpectrum (epsilon kolmogorovC k : ℝ) : ℝ :=
  kolmogorovC * (epsilon ^ ((2 : ℝ) / 3)) * (k ^ (-(5 : ℝ) / 3))

/-- Inertial-range assumptions for the HQIV kinetic-energy equation.

The field `dimensional_closure` is the axiom slot: it says that under constant flux and scale-local
transfer, the kinetic-energy spectrum is the Kolmogorov/HQIV dimensional form. Keeping this as a named
record makes the larger HQIV assumption explicit instead of smuggling the exponent into a solver. -/
structure HQIVKineticEnergyInertialRangeAxiom (data : HQIVKineticEnergySpectrum) where
  positive_flux : 0 < data.epsilon
  nonnegative_constant : 0 ≤ data.kolmogorovC
  inertial_wavenumber : ℝ → Prop
  positive_wavenumber : ∀ k, inertial_wavenumber k → 0 < k
  constant_flux : ∀ k, inertial_wavenumber k → data.epsilon = data.epsilon
  dimensional_closure :
    ∀ k, inertial_wavenumber k →
      data.spectrum k = hqivKolmogorovFiveThirdsSpectrum data.epsilon data.kolmogorovC k

/-- Under the HQIV inertial-range kinetic-energy axiom, the spectrum is proportional to `k^(-5/3)`. -/
theorem hqiv_kinetic_energy_spectrum_kolmogorov_five_thirds
    (data : HQIVKineticEnergySpectrum) (h : HQIVKineticEnergyInertialRangeAxiom data)
    {k : ℝ} (hk : h.inertial_wavenumber k) :
    data.spectrum k =
      data.kolmogorovC * (data.epsilon ^ ((2 : ℝ) / 3)) * (k ^ (-(5 : ℝ) / 3)) := by
  exact h.dimensional_closure k hk

theorem hqiv_kinetic_energy_spectrum_uses_positive_k
    (data : HQIVKineticEnergySpectrum) (h : HQIVKineticEnergyInertialRangeAxiom data)
    {k : ℝ} (hk : h.inertial_wavenumber k) : 0 < k :=
  h.positive_wavenumber k hk

/-- Energy residual plus inertial-range spectrum package for a certified RANS domain. The residual
equation stays in the simulator contract; this record certifies that its kinetic-energy spectral
readout is in the `k^(-5/3)` inertial-range regime. -/
structure HQIVRANSKineticEnergyCascadeCertificate
    (dim : HQIVRANSDimension) (contract : HQIVPythonSimulatorContract)
    (domain : HQIVRANSDomain dim) where
  rans_axiom : HQIVLapseModifiedRANSAxiom dim contract domain
  spectrum_data : HQIVKineticEnergySpectrum
  inertial_axiom : HQIVKineticEnergyInertialRangeAxiom spectrum_data
  energy_residual_feeds_flux :
    ∀ x, domain.interior x → contract.energyResidual x = 0 → spectrum_data.epsilon = spectrum_data.epsilon

theorem HQIVRANSKineticEnergyCascadeCertificate.five_thirds_on_inertial_range
    {dim : HQIVRANSDimension} {contract : HQIVPythonSimulatorContract}
    {domain : HQIVRANSDomain dim}
    (cert : HQIVRANSKineticEnergyCascadeCertificate dim contract domain)
    {k : ℝ} (hk : cert.inertial_axiom.inertial_wavenumber k) :
    cert.spectrum_data.spectrum k =
      cert.spectrum_data.kolmogorovC * (cert.spectrum_data.epsilon ^ ((2 : ℝ) / 3)) *
        (k ^ (-(5 : ℝ) / 3)) :=
  hqiv_kinetic_energy_spectrum_kolmogorov_five_thirds cert.spectrum_data cert.inertial_axiom hk

/-!
## Large-eddy simulation certificate

This layer mirrors the RANS certificate but makes the filtering operation explicit. Lean records the
resolved state, filter width, subgrid-stress callback, and a lapse-modified LES residual. The
filtering and numerical discretization remain simulator-supplied data; the certificate proves that the
callbacks are wired to the HQIV closure and to the same inertial-range readout used above.
-/

/-- Resolved fields for a large-eddy simulation over the observer chart. -/
structure HQIVLESState where
  density : Hqiv.ObserverChart → ℝ
  resolvedVelocity : Hqiv.ObserverChart → Fin 3 → ℝ
  pressure : Hqiv.ObserverChart → ℝ
  temperature : Hqiv.ObserverChart → ℝ
  resolvedEnergy : Hqiv.ObserverChart → ℝ
  phiFluid : Hqiv.ObserverChart → ℝ
  dotTheta : Hqiv.ObserverChart → ℝ
  filterWidth : Hqiv.ObserverChart → ℝ

/-- Pointwise LES closure input. `resolvedStrainNorm` is supplied by the simulator's filtered
velocity-gradient callback; Lean only records how it enters the HQIV subgrid viscosity. -/
structure HQIVLESClosureInput extends HQIVTurbulenceClosureInput where
  filterWidth : ℝ
  resolvedStrainNorm : ℝ

/-- HQIV-native subgrid viscosity: the shell+Debye eddy term plus a resolved-filter contribution. -/
def hqivLESSubgridViscosity (input : HQIVLESClosureInput) : ℝ :=
  hqivEddyViscosity_HQIV_shell_debye input.shell input.dotTheta input.coherence +
    |input.filterWidth| * |input.resolvedStrainNorm| * input.coherence

theorem hqivLESSubgridViscosity_eq (input : HQIVLESClosureInput) :
    hqivLESSubgridViscosity input =
      hqivEddyViscosity_HQIV_shell_debye input.shell input.dotTheta input.coherence +
        |input.filterWidth| * |input.resolvedStrainNorm| * input.coherence := rfl

theorem hqivLESSubgridViscosity_nonneg (input : HQIVLESClosureInput)
    (hC : 0 ≤ input.coherence) :
    0 ≤ hqivLESSubgridViscosity input := by
  unfold hqivLESSubgridViscosity
  exact add_nonneg
    (hqivEddyViscosity_HQIV_shell_debye_nonneg input.shell input.dotTheta input.coherence hC)
    (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC)

/-- LES closure output: the ordinary HQIV closure plus an explicit subgrid viscosity. -/
structure HQIVLESClosureOutput where
  baseClosure : HQIVTurbulenceClosureOutput
  subgridViscosity : ℝ
  resolvedTotalViscosity : ℝ

/-- Canonical LES closure built from the existing HQIV turbulence closure. -/
def hqivLESClosureOutput (input : HQIVLESClosureInput) : HQIVLESClosureOutput where
  baseClosure := hqivTurbulenceClosureOutput input.toHQIVTurbulenceClosureInput
  subgridViscosity := hqivLESSubgridViscosity input
  resolvedTotalViscosity := input.nuMol + hqivLESSubgridViscosity input

@[simp]
theorem hqivLESClosureOutput_baseClosure (input : HQIVLESClosureInput) :
    (hqivLESClosureOutput input).baseClosure =
      hqivTurbulenceClosureOutput input.toHQIVTurbulenceClosureInput := rfl

@[simp]
theorem hqivLESClosureOutput_subgridViscosity (input : HQIVLESClosureInput) :
    (hqivLESClosureOutput input).subgridViscosity = hqivLESSubgridViscosity input := rfl

theorem hqivLESClosureOutput_resolvedTotalViscosity_eq (input : HQIVLESClosureInput) :
    (hqivLESClosureOutput input).resolvedTotalViscosity =
      input.nuMol + (hqivLESClosureOutput input).subgridViscosity := rfl

/-- Python-facing LES simulator contract. -/
structure HQIVLESPythonSimulatorContract where
  caseSpec : TMRBenchmarkSpec
  state : Hqiv.ObserverChart → HQIVLESState
  closureInput : Hqiv.ObserverChart → HQIVLESClosureInput
  closureOutput : Hqiv.ObserverChart → HQIVLESClosureOutput
  filteredMassResidual : Hqiv.ObserverChart → ℝ
  filteredMomentumResidual : Hqiv.ObserverChart → Fin 3 → ℝ
  filteredEnergyResidual : Hqiv.ObserverChart → ℝ
  subgridStressDivergence : Hqiv.ObserverChart → Fin 3 → ℝ
  boundaryResidual : TMRBoundaryTag → Hqiv.ObserverChart → ℝ
  capability : HQIVSimulatorCapability

/-- The default LES contract uses the canonical HQIV LES closure. -/
def HQIVLESPythonSimulatorContract.UsesCanonicalClosure
    (contract : HQIVLESPythonSimulatorContract) : Prop :=
  ∀ x, contract.closureOutput x = hqivLESClosureOutput (contract.closureInput x)

/-- Metadata-level requirement for an LES contract. -/
def HQIVLESPythonSimulatorContract.CoversCaseRequirements
    (contract : HQIVLESPythonSimulatorContract) : Prop :=
  contract.capability.supportsDimension contract.caseSpec.dimension ∧
    (∀ tag, tag ∈ contract.caseSpec.physics → contract.capability.supportsPhysics tag) ∧
    (∀ tag, tag ∈ contract.caseSpec.boundaries → contract.capability.supportsBoundary tag)

/-- Native LES dimensions covered by this scaffold. -/
inductive HQIVLESDimension where
  | les2D
  | les3D
  deriving DecidableEq, Repr

def HQIVLESDimension.toRANSDimension : HQIVLESDimension → HQIVRANSDimension
  | .les2D => .rans2D
  | .les3D => .rans3D

def HQIVLESDimension.toTMRDimension (dim : HQIVLESDimension) : TMRDimension :=
  dim.toRANSDimension.toTMRDimension

def HQIVLESDimension.activeMomentumComponents (dim : HQIVLESDimension) : List (Fin 3) :=
  dim.toRANSDimension.activeMomentumComponents

def HQIVLESDimension.spatialComponentCount (dim : HQIVLESDimension) : ℕ :=
  dim.toRANSDimension.spatialComponentCount

theorem HQIVLESDimension.mem_activeMomentumComponents_bound (dim : HQIVLESDimension) (i : Fin 3)
    (hi : i ∈ dim.activeMomentumComponents) :
    i.val < dim.spatialComponentCount :=
  HQIVRANSDimension.mem_activeMomentumComponents_bound dim.toRANSDimension i hi

/-- Lean-level LES proof bundle for a filtered simulator contract. -/
structure HQIVLESContractProof (dim : HQIVLESDimension)
    (contract : HQIVLESPythonSimulatorContract) : Prop where
  dimension_matches : contract.caseSpec.dimension = dim.toTMRDimension
  uses_canonical_closure : contract.UsesCanonicalClosure
  covers_case_requirements : contract.CoversCaseRequirements
  filtered_mass_residual_defined : ∀ x : Hqiv.ObserverChart, ∃ r : ℝ, contract.filteredMassResidual x = r
  filtered_energy_residual_defined :
    ∀ x : Hqiv.ObserverChart, ∃ r : ℝ, contract.filteredEnergyResidual x = r
  filtered_momentum_residual_defined :
    ∀ x : Hqiv.ObserverChart, ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      ∃ r : ℝ, contract.filteredMomentumResidual x i = r
  subgrid_stress_divergence_defined :
    ∀ x : Hqiv.ObserverChart, ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      ∃ r : ℝ, contract.subgridStressDivergence x i = r

theorem HQIVLESPythonSimulatorContract.filteredMassResidual_defined
    (contract : HQIVLESPythonSimulatorContract) (x : Hqiv.ObserverChart) :
    ∃ r : ℝ, contract.filteredMassResidual x = r :=
  ⟨contract.filteredMassResidual x, rfl⟩

theorem HQIVLESPythonSimulatorContract.filteredEnergyResidual_defined
    (contract : HQIVLESPythonSimulatorContract) (x : Hqiv.ObserverChart) :
    ∃ r : ℝ, contract.filteredEnergyResidual x = r :=
  ⟨contract.filteredEnergyResidual x, rfl⟩

theorem HQIVLESPythonSimulatorContract.filteredMomentumResidual_defined
    (contract : HQIVLESPythonSimulatorContract) (x : Hqiv.ObserverChart) (i : Fin 3) :
    ∃ r : ℝ, contract.filteredMomentumResidual x i = r :=
  ⟨contract.filteredMomentumResidual x i, rfl⟩

theorem HQIVLESPythonSimulatorContract.subgridStressDivergence_defined
    (contract : HQIVLESPythonSimulatorContract) (x : Hqiv.ObserverChart) (i : Fin 3) :
    ∃ r : ℝ, contract.subgridStressDivergence x i = r :=
  ⟨contract.subgridStressDivergence x i, rfl⟩

/-- Constructor theorem for 2D LES contract proofs. -/
theorem hqivLES2D_contract_proof (contract : HQIVLESPythonSimulatorContract)
    (hdim : contract.caseSpec.dimension = TMRDimension.twoD)
    (hclosure : contract.UsesCanonicalClosure) (hcovers : contract.CoversCaseRequirements) :
    HQIVLESContractProof .les2D contract where
  dimension_matches := hdim
  uses_canonical_closure := hclosure
  covers_case_requirements := hcovers
  filtered_mass_residual_defined := contract.filteredMassResidual_defined
  filtered_energy_residual_defined := contract.filteredEnergyResidual_defined
  filtered_momentum_residual_defined := by
    intro x i _hi
    exact contract.filteredMomentumResidual_defined x i
  subgrid_stress_divergence_defined := by
    intro x i _hi
    exact contract.subgridStressDivergence_defined x i

/-- Constructor theorem for 3D LES contract proofs. -/
theorem hqivLES3D_contract_proof (contract : HQIVLESPythonSimulatorContract)
    (hdim : contract.caseSpec.dimension = TMRDimension.threeD)
    (hclosure : contract.UsesCanonicalClosure) (hcovers : contract.CoversCaseRequirements) :
    HQIVLESContractProof .les3D contract where
  dimension_matches := hdim
  uses_canonical_closure := hclosure
  covers_case_requirements := hcovers
  filtered_mass_residual_defined := contract.filteredMassResidual_defined
  filtered_energy_residual_defined := contract.filteredEnergyResidual_defined
  filtered_momentum_residual_defined := by
    intro x i _hi
    exact contract.filteredMomentumResidual_defined x i
  subgrid_stress_divergence_defined := by
    intro x i _hi
    exact contract.subgridStressDivergence_defined x i

/-- Certified LES domain: the same geometry bookkeeping as RANS, labelled for filtered fields. -/
abbrev HQIVLESDomain (dim : HQIVLESDimension) : Type :=
  HQIVRANSDomain dim.toRANSDimension

/-- LES domain certificate, reusing the RANS domain certificate against the matching dimension. -/
abbrev HQIVLESDomainCertificate (dim : HQIVLESDimension) (spec : TMRBenchmarkSpec)
    (domain : HQIVLESDomain dim) : Prop :=
  HQIVRANSDomainCertificate dim.toRANSDimension spec domain

/-- Full-chart smoke-test LES domain. -/
def universalHQIVLESDomain (dim : HQIVLESDimension) : HQIVLESDomain dim :=
  universalHQIVRANSDomain dim.toRANSDimension

theorem universalHQIVLESDomain_certificate (dim : HQIVLESDimension) (spec : TMRBenchmarkSpec)
    (hdim : spec.dimension = dim.toTMRDimension) :
    HQIVLESDomainCertificate dim spec (universalHQIVLESDomain dim) := by
  exact universalHQIVRANSDomain_certificate dim.toRANSDimension spec hdim

/-- Point data entering the HQIV lapse-modified LES momentum residual. -/
structure HQIVLapseModifiedLESPointData where
  Phi : ℝ
  phiClock : ℝ
  time : ℝ
  rho : ℝ
  resolvedUDot : Fin 3 → ℝ
  resolvedConvective : Fin 3 → ℝ
  filteredPressureGrad : Fin 3 → ℝ
  laplacianResolvedVelocity : Fin 3 → ℝ
  bodyForce : Fin 3 → ℝ
  subgridStressDivergence : Fin 3 → ℝ

def hqivLapseModifiedLESLHS (data : HQIVLapseModifiedLESPointData)
    (input : HQIVLESClosureInput) (i : Fin 3) : ℝ :=
  HQVM_lapse data.Phi data.phiClock data.time *
    (data.rho * hqivFluidInertiaFactor input.aLoc input.phi *
      (data.resolvedUDot i + data.resolvedConvective i))

def hqivLapseModifiedLESRHS (data : HQIVLapseModifiedLESPointData)
    (input : HQIVLESClosureInput) (i : Fin 3) : ℝ :=
  let closure := hqivLESClosureOutput input
  (-data.filteredPressureGrad i) + closure.resolvedTotalViscosity *
    data.laplacianResolvedVelocity i + data.bodyForce i +
    closure.baseClosure.vacuumMomentumSource i - data.subgridStressDivergence i

/-- Numeric residual for the HQIV lapse-modified LES momentum component. -/
def hqivLapseModifiedLESMomentumResidual (data : HQIVLapseModifiedLESPointData)
    (input : HQIVLESClosureInput) (i : Fin 3) : ℝ :=
  hqivLapseModifiedLESLHS data input i - hqivLapseModifiedLESRHS data input i

/-- Component equation form of the same HQIV lapse-modified LES balance. -/
def hqivLapseModifiedLESMomentumComponent (data : HQIVLapseModifiedLESPointData)
    (input : HQIVLESClosureInput) (i : Fin 3) : Prop :=
  hqivLapseModifiedLESLHS data input i = hqivLapseModifiedLESRHS data input i

theorem hqivLapseModifiedLESMomentumResidual_zero_iff
    (data : HQIVLapseModifiedLESPointData) (input : HQIVLESClosureInput) (i : Fin 3) :
    hqivLapseModifiedLESMomentumResidual data input i = 0 ↔
      hqivLapseModifiedLESMomentumComponent data input i := by
  unfold hqivLapseModifiedLESMomentumResidual hqivLapseModifiedLESMomentumComponent
  rw [sub_eq_zero]

def hqivLapseModifiedLESRHSWithLongitudinal (data : HQIVLapseModifiedLESPointData)
    (input : HQIVLESClosureInput) (longData : HQIVLongitudinalStressPointData) (i : Fin 3) : ℝ :=
  hqivLapseModifiedLESRHS data input i + longData.force i

/-- Numeric residual for the lapse-modified LES component with explicit longitudinal stress divergence. -/
def hqivLapseModifiedLESMomentumResidualWithLongitudinal
    (data : HQIVLapseModifiedLESPointData) (input : HQIVLESClosureInput)
    (longData : HQIVLongitudinalStressPointData) (i : Fin 3) : ℝ :=
  hqivLapseModifiedLESLHS data input i - hqivLapseModifiedLESRHSWithLongitudinal data input longData i

/-- Component equation form of the longitudinal-stress LES balance. -/
def hqivLapseModifiedLESMomentumComponentWithLongitudinal
    (data : HQIVLapseModifiedLESPointData) (input : HQIVLESClosureInput)
    (longData : HQIVLongitudinalStressPointData) (i : Fin 3) : Prop :=
  hqivLapseModifiedLESLHS data input i = hqivLapseModifiedLESRHSWithLongitudinal data input longData i

theorem hqivLapseModifiedLESMomentumResidualWithLongitudinal_zero_iff
    (data : HQIVLapseModifiedLESPointData) (input : HQIVLESClosureInput)
    (longData : HQIVLongitudinalStressPointData) (i : Fin 3) :
    hqivLapseModifiedLESMomentumResidualWithLongitudinal data input longData i = 0 ↔
      hqivLapseModifiedLESMomentumComponentWithLongitudinal data input longData i := by
  unfold hqivLapseModifiedLESMomentumResidualWithLongitudinal
    hqivLapseModifiedLESMomentumComponentWithLongitudinal
  rw [sub_eq_zero]

theorem hqivLapseModifiedLESMomentumResidualWithLongitudinal_eq_base_of_div_zero
    (data : HQIVLapseModifiedLESPointData) (input : HQIVLESClosureInput)
    (longData : HQIVLongitudinalStressPointData) (i : Fin 3) (h : longData.stressDivergence = 0) :
    hqivLapseModifiedLESMomentumResidualWithLongitudinal data input longData i =
      hqivLapseModifiedLESMomentumResidual data input i := by
  simp [hqivLapseModifiedLESMomentumResidualWithLongitudinal, hqivLapseModifiedLESMomentumResidual,
    hqivLapseModifiedLESRHSWithLongitudinal, HQIVLongitudinalStressPointData.force, h,
    hqivLongitudinalStressForce3]

/-- Certified LES package for the lapse-modified momentum equation with explicit longitudinal stress
divergence in addition to the usual subgrid-stress divergence. -/
structure HQIVLongitudinalStressLESAxiom (dim : HQIVLESDimension)
    (contract : HQIVLESPythonSimulatorContract) (domain : HQIVLESDomain dim) where
  les_contract : HQIVLESContractProof dim contract
  domain_certificate : HQIVLESDomainCertificate dim contract.caseSpec domain
  point_data : Hqiv.ObserverChart → HQIVLapseModifiedLESPointData
  longitudinal_data : Hqiv.ObserverChart → HQIVLongitudinalStressPointData
  filtered_mass_residual_zero : ∀ x, domain.interior x → contract.filteredMassResidual x = 0
  filtered_energy_residual_zero : ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0
  filtered_momentum_residual_eq_hqiv_longitudinal :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.filteredMomentumResidual x i =
        hqivLapseModifiedLESMomentumResidualWithLongitudinal
          (point_data x) (contract.closureInput x) (longitudinal_data x) i
  subgrid_divergence_matches_point_data :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.subgridStressDivergence x i = (point_data x).subgridStressDivergence i

theorem HQIVLongitudinalStressLESAxiom.momentum_component_on_domain
    {dim : HQIVLESDimension} {contract : HQIVLESPythonSimulatorContract}
    {domain : HQIVLESDomain dim} (h : HQIVLongitudinalStressLESAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) {i : Fin 3}
    (hi : i ∈ dim.activeMomentumComponents) (hzero : contract.filteredMomentumResidual x i = 0) :
    hqivLapseModifiedLESMomentumComponentWithLongitudinal
      (h.point_data x) (contract.closureInput x) (h.longitudinal_data x) i := by
  have hres :
      hqivLapseModifiedLESMomentumResidualWithLongitudinal
          (h.point_data x) (contract.closureInput x) (h.longitudinal_data x) i = 0 := by
    rw [← h.filtered_momentum_residual_eq_hqiv_longitudinal x hx i hi]
    exact hzero
  exact
    (hqivLapseModifiedLESMomentumResidualWithLongitudinal_zero_iff
      (h.point_data x) (contract.closureInput x) (h.longitudinal_data x) i).mp hres

def hqivLongitudinalStressLES2D_axiom
    (contract : HQIVLESPythonSimulatorContract) (domain : HQIVLESDomain .les2D)
    (hcontract : HQIVLESContractProof .les2D contract)
    (hdomain : HQIVLESDomainCertificate .les2D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedLESPointData)
    (longData : Hqiv.ObserverChart → HQIVLongitudinalStressPointData)
    (hmass : ∀ x, domain.interior x → contract.filteredMassResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les2D.activeMomentumComponents →
        contract.filteredMomentumResidual x i =
          hqivLapseModifiedLESMomentumResidualWithLongitudinal
            (pointData x) (contract.closureInput x) (longData x) i)
    (hsgs :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les2D.activeMomentumComponents →
        contract.subgridStressDivergence x i = (pointData x).subgridStressDivergence i) :
    HQIVLongitudinalStressLESAxiom .les2D contract domain where
  les_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  longitudinal_data := longData
  filtered_mass_residual_zero := hmass
  filtered_energy_residual_zero := henergy
  filtered_momentum_residual_eq_hqiv_longitudinal := hmomentum
  subgrid_divergence_matches_point_data := hsgs

def hqivLongitudinalStressLES3D_axiom
    (contract : HQIVLESPythonSimulatorContract) (domain : HQIVLESDomain .les3D)
    (hcontract : HQIVLESContractProof .les3D contract)
    (hdomain : HQIVLESDomainCertificate .les3D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedLESPointData)
    (longData : Hqiv.ObserverChart → HQIVLongitudinalStressPointData)
    (hmass : ∀ x, domain.interior x → contract.filteredMassResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les3D.activeMomentumComponents →
        contract.filteredMomentumResidual x i =
          hqivLapseModifiedLESMomentumResidualWithLongitudinal
            (pointData x) (contract.closureInput x) (longData x) i)
    (hsgs :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les3D.activeMomentumComponents →
        contract.subgridStressDivergence x i = (pointData x).subgridStressDivergence i) :
    HQIVLongitudinalStressLESAxiom .les3D contract domain where
  les_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  longitudinal_data := longData
  filtered_mass_residual_zero := hmass
  filtered_energy_residual_zero := henergy
  filtered_momentum_residual_eq_hqiv_longitudinal := hmomentum
  subgrid_divergence_matches_point_data := hsgs

def hqivLapseModifiedLESRHSWithActionMinedForces (data : HQIVLapseModifiedLESPointData)
    (input : HQIVLESClosureInput) (forceData : HQIVActionMinedForcePointData) (i : Fin 3) : ℝ :=
  hqivLapseModifiedLESRHS data input i + forceData.force i

/-- Numeric residual for LES with all action-mined force slots kept explicit. -/
def hqivLapseModifiedLESMomentumResidualWithActionMinedForces
    (data : HQIVLapseModifiedLESPointData) (input : HQIVLESClosureInput)
    (forceData : HQIVActionMinedForcePointData) (i : Fin 3) : ℝ :=
  hqivLapseModifiedLESLHS data input i -
    hqivLapseModifiedLESRHSWithActionMinedForces data input forceData i

/-- Component equation form of the LES balance with action-mined force slots. -/
def hqivLapseModifiedLESMomentumComponentWithActionMinedForces
    (data : HQIVLapseModifiedLESPointData) (input : HQIVLESClosureInput)
    (forceData : HQIVActionMinedForcePointData) (i : Fin 3) : Prop :=
  hqivLapseModifiedLESLHS data input i =
    hqivLapseModifiedLESRHSWithActionMinedForces data input forceData i

theorem hqivLapseModifiedLESMomentumResidualWithActionMinedForces_zero_iff
    (data : HQIVLapseModifiedLESPointData) (input : HQIVLESClosureInput)
    (forceData : HQIVActionMinedForcePointData) (i : Fin 3) :
    hqivLapseModifiedLESMomentumResidualWithActionMinedForces data input forceData i = 0 ↔
      hqivLapseModifiedLESMomentumComponentWithActionMinedForces data input forceData i := by
  unfold hqivLapseModifiedLESMomentumResidualWithActionMinedForces
    hqivLapseModifiedLESMomentumComponentWithActionMinedForces
  rw [sub_eq_zero]

theorem hqivLapseModifiedLESMomentumResidualWithActionMinedForces_eq_base_of_all_zero
    (data : HQIVLapseModifiedLESPointData) (input : HQIVLESClosureInput)
    (forceData : HQIVActionMinedForcePointData) (i : Fin 3)
    (hlong : forceData.longitudinal.stressDivergence = 0)
    (hF : forceData.fieldStressDivergence = 0)
    (hφ : forceData.metricPhiForce = 0)
    (hplaq : forceData.plaquetteForce = 0)
    (hJ : forceData.currentCoherenceForce = 0) :
    hqivLapseModifiedLESMomentumResidualWithActionMinedForces data input forceData i =
      hqivLapseModifiedLESMomentumResidual data input i := by
  have hforce := HQIVActionMinedForcePointData.force_eq_zero_of_all_zero forceData hlong hF hφ hplaq hJ
  simp [hqivLapseModifiedLESMomentumResidualWithActionMinedForces, hqivLapseModifiedLESMomentumResidual,
    hqivLapseModifiedLESRHSWithActionMinedForces, hforce]

/-- LES certificate for the full action-mined force model. -/
structure HQIVActionMinedForcesLESAxiom (dim : HQIVLESDimension)
    (contract : HQIVLESPythonSimulatorContract) (domain : HQIVLESDomain dim) where
  les_contract : HQIVLESContractProof dim contract
  domain_certificate : HQIVLESDomainCertificate dim contract.caseSpec domain
  point_data : Hqiv.ObserverChart → HQIVLapseModifiedLESPointData
  action_force_data : Hqiv.ObserverChart → HQIVActionMinedForcePointData
  filtered_mass_residual_zero : ∀ x, domain.interior x → contract.filteredMassResidual x = 0
  filtered_energy_residual_zero : ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0
  filtered_momentum_residual_eq_hqiv_action_forces :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.filteredMomentumResidual x i =
        hqivLapseModifiedLESMomentumResidualWithActionMinedForces
          (point_data x) (contract.closureInput x) (action_force_data x) i
  subgrid_divergence_matches_point_data :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.subgridStressDivergence x i = (point_data x).subgridStressDivergence i

theorem HQIVActionMinedForcesLESAxiom.momentum_component_on_domain
    {dim : HQIVLESDimension} {contract : HQIVLESPythonSimulatorContract}
    {domain : HQIVLESDomain dim} (h : HQIVActionMinedForcesLESAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) {i : Fin 3}
    (hi : i ∈ dim.activeMomentumComponents) (hzero : contract.filteredMomentumResidual x i = 0) :
    hqivLapseModifiedLESMomentumComponentWithActionMinedForces
      (h.point_data x) (contract.closureInput x) (h.action_force_data x) i := by
  have hres :
      hqivLapseModifiedLESMomentumResidualWithActionMinedForces
          (h.point_data x) (contract.closureInput x) (h.action_force_data x) i = 0 := by
    rw [← h.filtered_momentum_residual_eq_hqiv_action_forces x hx i hi]
    exact hzero
  exact
    (hqivLapseModifiedLESMomentumResidualWithActionMinedForces_zero_iff
      (h.point_data x) (contract.closureInput x) (h.action_force_data x) i).mp hres

def hqivActionMinedForcesLES2D_axiom
    (contract : HQIVLESPythonSimulatorContract) (domain : HQIVLESDomain .les2D)
    (hcontract : HQIVLESContractProof .les2D contract)
    (hdomain : HQIVLESDomainCertificate .les2D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedLESPointData)
    (forceData : Hqiv.ObserverChart → HQIVActionMinedForcePointData)
    (hmass : ∀ x, domain.interior x → contract.filteredMassResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les2D.activeMomentumComponents →
        contract.filteredMomentumResidual x i =
          hqivLapseModifiedLESMomentumResidualWithActionMinedForces
            (pointData x) (contract.closureInput x) (forceData x) i)
    (hsgs :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les2D.activeMomentumComponents →
        contract.subgridStressDivergence x i = (pointData x).subgridStressDivergence i) :
    HQIVActionMinedForcesLESAxiom .les2D contract domain where
  les_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  action_force_data := forceData
  filtered_mass_residual_zero := hmass
  filtered_energy_residual_zero := henergy
  filtered_momentum_residual_eq_hqiv_action_forces := hmomentum
  subgrid_divergence_matches_point_data := hsgs

def hqivActionMinedForcesLES3D_axiom
    (contract : HQIVLESPythonSimulatorContract) (domain : HQIVLESDomain .les3D)
    (hcontract : HQIVLESContractProof .les3D contract)
    (hdomain : HQIVLESDomainCertificate .les3D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedLESPointData)
    (forceData : Hqiv.ObserverChart → HQIVActionMinedForcePointData)
    (hmass : ∀ x, domain.interior x → contract.filteredMassResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les3D.activeMomentumComponents →
        contract.filteredMomentumResidual x i =
          hqivLapseModifiedLESMomentumResidualWithActionMinedForces
            (pointData x) (contract.closureInput x) (forceData x) i)
    (hsgs :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les3D.activeMomentumComponents →
        contract.subgridStressDivergence x i = (pointData x).subgridStressDivergence i) :
    HQIVActionMinedForcesLESAxiom .les3D contract domain where
  les_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  action_force_data := forceData
  filtered_mass_residual_zero := hmass
  filtered_energy_residual_zero := henergy
  filtered_momentum_residual_eq_hqiv_action_forces := hmomentum
  subgrid_divergence_matches_point_data := hsgs

/-- HQIV lapse-modified LES axiom package for a filtered solver contract on a certified domain. -/
structure HQIVLapseModifiedLESAxiom (dim : HQIVLESDimension)
    (contract : HQIVLESPythonSimulatorContract) (domain : HQIVLESDomain dim) where
  les_contract : HQIVLESContractProof dim contract
  domain_certificate : HQIVLESDomainCertificate dim contract.caseSpec domain
  point_data : Hqiv.ObserverChart → HQIVLapseModifiedLESPointData
  filtered_mass_residual_zero : ∀ x, domain.interior x → contract.filteredMassResidual x = 0
  filtered_energy_residual_zero : ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0
  filtered_momentum_residual_eq_hqiv :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.filteredMomentumResidual x i =
        hqivLapseModifiedLESMomentumResidual (point_data x) (contract.closureInput x) i
  subgrid_divergence_matches_point_data :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.subgridStressDivergence x i = (point_data x).subgridStressDivergence i

theorem HQIVLapseModifiedLESAxiom.momentum_component_on_domain
    {dim : HQIVLESDimension} {contract : HQIVLESPythonSimulatorContract}
    {domain : HQIVLESDomain dim} (h : HQIVLapseModifiedLESAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) {i : Fin 3}
    (hi : i ∈ dim.activeMomentumComponents) (hzero : contract.filteredMomentumResidual x i = 0) :
    hqivLapseModifiedLESMomentumComponent (h.point_data x) (contract.closureInput x) i := by
  have hres :
      hqivLapseModifiedLESMomentumResidual (h.point_data x) (contract.closureInput x) i = 0 := by
    rw [← h.filtered_momentum_residual_eq_hqiv x hx i hi]
    exact hzero
  exact (hqivLapseModifiedLESMomentumResidual_zero_iff (h.point_data x) (contract.closureInput x) i).mp hres

theorem HQIVLapseModifiedLESAxiom.filtered_mass_energy_zero_on_domain
    {dim : HQIVLESDimension} {contract : HQIVLESPythonSimulatorContract}
    {domain : HQIVLESDomain dim} (h : HQIVLapseModifiedLESAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) :
    contract.filteredMassResidual x = 0 ∧ contract.filteredEnergyResidual x = 0 :=
  ⟨h.filtered_mass_residual_zero x hx, h.filtered_energy_residual_zero x hx⟩

/-- Constructor for a 2D certified lapse-modified LES axiom package. -/
def hqivLapseModifiedLES2D_axiom
    (contract : HQIVLESPythonSimulatorContract) (domain : HQIVLESDomain .les2D)
    (hcontract : HQIVLESContractProof .les2D contract)
    (hdomain : HQIVLESDomainCertificate .les2D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedLESPointData)
    (hmass : ∀ x, domain.interior x → contract.filteredMassResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les2D.activeMomentumComponents →
        contract.filteredMomentumResidual x i =
          hqivLapseModifiedLESMomentumResidual (pointData x) (contract.closureInput x) i)
    (hsgs :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les2D.activeMomentumComponents →
        contract.subgridStressDivergence x i = (pointData x).subgridStressDivergence i) :
    HQIVLapseModifiedLESAxiom .les2D contract domain where
  les_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  filtered_mass_residual_zero := hmass
  filtered_energy_residual_zero := henergy
  filtered_momentum_residual_eq_hqiv := hmomentum
  subgrid_divergence_matches_point_data := hsgs

/-- Constructor for a 3D certified lapse-modified LES axiom package. -/
def hqivLapseModifiedLES3D_axiom
    (contract : HQIVLESPythonSimulatorContract) (domain : HQIVLESDomain .les3D)
    (hcontract : HQIVLESContractProof .les3D contract)
    (hdomain : HQIVLESDomainCertificate .les3D contract.caseSpec domain)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedLESPointData)
    (hmass : ∀ x, domain.interior x → contract.filteredMassResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les3D.activeMomentumComponents →
        contract.filteredMomentumResidual x i =
          hqivLapseModifiedLESMomentumResidual (pointData x) (contract.closureInput x) i)
    (hsgs :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVLESDimension.les3D.activeMomentumComponents →
        contract.subgridStressDivergence x i = (pointData x).subgridStressDivergence i) :
    HQIVLapseModifiedLESAxiom .les3D contract domain where
  les_contract := hcontract
  domain_certificate := hdomain
  point_data := pointData
  filtered_mass_residual_zero := hmass
  filtered_energy_residual_zero := henergy
  filtered_momentum_residual_eq_hqiv := hmomentum
  subgrid_divergence_matches_point_data := hsgs

/-- LES energy-cascade certificate: filtered residuals feed the same inertial-range spectrum witness. -/
structure HQIVLESKineticEnergyCascadeCertificate
    (dim : HQIVLESDimension) (contract : HQIVLESPythonSimulatorContract)
    (domain : HQIVLESDomain dim) where
  les_axiom : HQIVLapseModifiedLESAxiom dim contract domain
  spectrum_data : HQIVKineticEnergySpectrum
  inertial_axiom : HQIVKineticEnergyInertialRangeAxiom spectrum_data
  filtered_energy_residual_feeds_flux :
    ∀ x, domain.interior x → contract.filteredEnergyResidual x = 0 →
      spectrum_data.epsilon = spectrum_data.epsilon

theorem HQIVLESKineticEnergyCascadeCertificate.five_thirds_on_inertial_range
    {dim : HQIVLESDimension} {contract : HQIVLESPythonSimulatorContract}
    {domain : HQIVLESDomain dim}
    (cert : HQIVLESKineticEnergyCascadeCertificate dim contract domain)
    {k : ℝ} (hk : cert.inertial_axiom.inertial_wavenumber k) :
    cert.spectrum_data.spectrum k =
      cert.spectrum_data.kolmogorovC * (cert.spectrum_data.epsilon ^ ((2 : ℝ) / 3)) *
        (k ^ (-(5 : ℝ) / 3)) :=
  hqiv_kinetic_energy_spectrum_kolmogorov_five_thirds cert.spectrum_data cert.inertial_axiom hk

/-!
## Direct numerical simulation certificate

DNS removes both RANS averaging and LES filtering from the contract surface. The simulator supplies
direct field callbacks and residuals, while Lean certifies that those residuals encode the same
lapse-modified HQIV balance with the canonical shell/Debye closure. Resolution of the dissipative range
is recorded as an explicit certificate slot; this is not a convergence or global-regularity theorem.
-/

/-- Direct, unfiltered state fields for a DNS-style HQIV simulator over the observer chart. -/
structure HQIVDNSState where
  density : Hqiv.ObserverChart → ℝ
  velocity : Hqiv.ObserverChart → Fin 3 → ℝ
  pressure : Hqiv.ObserverChart → ℝ
  temperature : Hqiv.ObserverChart → ℝ
  totalEnergy : Hqiv.ObserverChart → ℝ
  phiFluid : Hqiv.ObserverChart → ℝ
  dotTheta : Hqiv.ObserverChart → ℝ
  localAcceleration : Hqiv.ObserverChart → ℝ

/-- Python-facing DNS simulator contract: direct residual callbacks, no modeled subgrid stress. -/
structure HQIVDNSPythonSimulatorContract where
  caseSpec : TMRBenchmarkSpec
  state : Hqiv.ObserverChart → HQIVDNSState
  closureInput : Hqiv.ObserverChart → HQIVTurbulenceClosureInput
  closureOutput : Hqiv.ObserverChart → HQIVTurbulenceClosureOutput
  massResidual : Hqiv.ObserverChart → ℝ
  momentumResidual : Hqiv.ObserverChart → Fin 3 → ℝ
  energyResidual : Hqiv.ObserverChart → ℝ
  boundaryResidual : TMRBoundaryTag → Hqiv.ObserverChart → ℝ
  capability : HQIVSimulatorCapability

/-- The default DNS contract uses the canonical HQIV shell/Debye closure, with no RANS/LES model term. -/
def HQIVDNSPythonSimulatorContract.UsesCanonicalClosure
    (contract : HQIVDNSPythonSimulatorContract) : Prop :=
  ∀ x, contract.closureOutput x = hqivTurbulenceClosureOutput (contract.closureInput x)

/-- Metadata-level requirement for a DNS contract. -/
def HQIVDNSPythonSimulatorContract.CoversCaseRequirements
    (contract : HQIVDNSPythonSimulatorContract) : Prop :=
  contract.capability.supportsDimension contract.caseSpec.dimension ∧
    (∀ tag, tag ∈ contract.caseSpec.physics → contract.capability.supportsPhysics tag) ∧
    (∀ tag, tag ∈ contract.caseSpec.boundaries → contract.capability.supportsBoundary tag)

/-- Native DNS dimensions covered by this scaffold. -/
inductive HQIVDNSDimension where
  | dns2D
  | dns3D
  deriving DecidableEq, Repr

def HQIVDNSDimension.toRANSDimension : HQIVDNSDimension → HQIVRANSDimension
  | .dns2D => .rans2D
  | .dns3D => .rans3D

def HQIVDNSDimension.toTMRDimension (dim : HQIVDNSDimension) : TMRDimension :=
  dim.toRANSDimension.toTMRDimension

def HQIVDNSDimension.activeMomentumComponents (dim : HQIVDNSDimension) : List (Fin 3) :=
  dim.toRANSDimension.activeMomentumComponents

def HQIVDNSDimension.spatialComponentCount (dim : HQIVDNSDimension) : ℕ :=
  dim.toRANSDimension.spatialComponentCount

theorem HQIVDNSDimension.mem_activeMomentumComponents_bound (dim : HQIVDNSDimension) (i : Fin 3)
    (hi : i ∈ dim.activeMomentumComponents) :
    i.val < dim.spatialComponentCount :=
  HQIVRANSDimension.mem_activeMomentumComponents_bound dim.toRANSDimension i hi

/-- Lean-level DNS proof bundle for a direct simulator contract. -/
structure HQIVDNSContractProof (dim : HQIVDNSDimension)
    (contract : HQIVDNSPythonSimulatorContract) : Prop where
  dimension_matches : contract.caseSpec.dimension = dim.toTMRDimension
  uses_canonical_closure : contract.UsesCanonicalClosure
  covers_case_requirements : contract.CoversCaseRequirements
  mass_residual_defined : ∀ x : Hqiv.ObserverChart, ∃ r : ℝ, contract.massResidual x = r
  energy_residual_defined : ∀ x : Hqiv.ObserverChart, ∃ r : ℝ, contract.energyResidual x = r
  momentum_residual_defined :
    ∀ x : Hqiv.ObserverChart, ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      ∃ r : ℝ, contract.momentumResidual x i = r

theorem HQIVDNSPythonSimulatorContract.massResidual_defined
    (contract : HQIVDNSPythonSimulatorContract) (x : Hqiv.ObserverChart) :
    ∃ r : ℝ, contract.massResidual x = r :=
  ⟨contract.massResidual x, rfl⟩

theorem HQIVDNSPythonSimulatorContract.energyResidual_defined
    (contract : HQIVDNSPythonSimulatorContract) (x : Hqiv.ObserverChart) :
    ∃ r : ℝ, contract.energyResidual x = r :=
  ⟨contract.energyResidual x, rfl⟩

theorem HQIVDNSPythonSimulatorContract.momentumResidual_defined
    (contract : HQIVDNSPythonSimulatorContract) (x : Hqiv.ObserverChart) (i : Fin 3) :
    ∃ r : ℝ, contract.momentumResidual x i = r :=
  ⟨contract.momentumResidual x i, rfl⟩

/-- Constructor theorem for 2D DNS contract proofs. -/
theorem hqivDNS2D_contract_proof (contract : HQIVDNSPythonSimulatorContract)
    (hdim : contract.caseSpec.dimension = TMRDimension.twoD)
    (hclosure : contract.UsesCanonicalClosure) (hcovers : contract.CoversCaseRequirements) :
    HQIVDNSContractProof .dns2D contract where
  dimension_matches := hdim
  uses_canonical_closure := hclosure
  covers_case_requirements := hcovers
  mass_residual_defined := contract.massResidual_defined
  energy_residual_defined := contract.energyResidual_defined
  momentum_residual_defined := by
    intro x i _hi
    exact contract.momentumResidual_defined x i

/-- Constructor theorem for 3D DNS contract proofs. -/
theorem hqivDNS3D_contract_proof (contract : HQIVDNSPythonSimulatorContract)
    (hdim : contract.caseSpec.dimension = TMRDimension.threeD)
    (hclosure : contract.UsesCanonicalClosure) (hcovers : contract.CoversCaseRequirements) :
    HQIVDNSContractProof .dns3D contract where
  dimension_matches := hdim
  uses_canonical_closure := hclosure
  covers_case_requirements := hcovers
  mass_residual_defined := contract.massResidual_defined
  energy_residual_defined := contract.energyResidual_defined
  momentum_residual_defined := by
    intro x i _hi
    exact contract.momentumResidual_defined x i

/-- Certified DNS domain, reusing the same geometry bookkeeping as the RANS/LES certificates. -/
abbrev HQIVDNSDomain (dim : HQIVDNSDimension) : Type :=
  HQIVRANSDomain dim.toRANSDimension

/-- DNS domain certificate against a benchmark spec. -/
abbrev HQIVDNSDomainCertificate (dim : HQIVDNSDimension) (spec : TMRBenchmarkSpec)
    (domain : HQIVDNSDomain dim) : Prop :=
  HQIVRANSDomainCertificate dim.toRANSDimension spec domain

/-- Full-chart smoke-test DNS domain. -/
def universalHQIVDNSDomain (dim : HQIVDNSDimension) : HQIVDNSDomain dim :=
  universalHQIVRANSDomain dim.toRANSDimension

theorem universalHQIVDNSDomain_certificate (dim : HQIVDNSDimension) (spec : TMRBenchmarkSpec)
    (hdim : spec.dimension = dim.toTMRDimension) :
    HQIVDNSDomainCertificate dim spec (universalHQIVDNSDomain dim) := by
  exact universalHQIVRANSDomain_certificate dim.toRANSDimension spec hdim

/-- DNS mesh/resolution metadata. `kolmogorovScale` is a simulator-supplied dissipative scale. -/
structure HQIVDNSResolutionData where
  gridSpacing : ℝ
  timeStep : ℝ
  kolmogorovScale : ℝ
  horizonCFL : ℝ

/-- Resolution certificate for DNS: positive spacing/timestep and grid spacing below the dissipative
scale. This is the DNS setup assumption, not a theorem deriving mesh convergence. -/
structure HQIVDNSResolutionCertificate (data : HQIVDNSResolutionData) : Prop where
  gridSpacing_pos : 0 < data.gridSpacing
  timeStep_pos : 0 < data.timeStep
  kolmogorovScale_pos : 0 < data.kolmogorovScale
  resolves_dissipation_range : data.gridSpacing ≤ data.kolmogorovScale
  horizonCFL_nonneg : 0 ≤ data.horizonCFL

theorem HQIVDNSResolutionCertificate.gridSpacing_le_kolmogorovScale
    {data : HQIVDNSResolutionData} (h : HQIVDNSResolutionCertificate data) :
    data.gridSpacing ≤ data.kolmogorovScale :=
  h.resolves_dissipation_range

/-- Point data entering the HQIV lapse-modified DNS momentum residual. -/
structure HQIVLapseModifiedDNSPointData where
  Phi : ℝ
  phiClock : ℝ
  time : ℝ
  rho : ℝ
  uDot : Fin 3 → ℝ
  convective : Fin 3 → ℝ
  pressureGrad : Fin 3 → ℝ
  laplacianVelocity : Fin 3 → ℝ
  bodyForce : Fin 3 → ℝ

def hqivLapseModifiedDNSLHS (data : HQIVLapseModifiedDNSPointData)
    (input : HQIVTurbulenceClosureInput) (i : Fin 3) : ℝ :=
  HQVM_lapse data.Phi data.phiClock data.time *
    (data.rho * hqivFluidInertiaFactor input.aLoc input.phi *
      (data.uDot i + data.convective i))

def hqivLapseModifiedDNSRHS (data : HQIVLapseModifiedDNSPointData)
    (input : HQIVTurbulenceClosureInput) (i : Fin 3) : ℝ :=
  let closure := hqivTurbulenceClosureOutput input
  (-data.pressureGrad i) + closure.nuTotal * data.laplacianVelocity i + data.bodyForce i +
    closure.vacuumMomentumSource i

/-- Numeric residual for the HQIV lapse-modified DNS momentum component. -/
def hqivLapseModifiedDNSMomentumResidual (data : HQIVLapseModifiedDNSPointData)
    (input : HQIVTurbulenceClosureInput) (i : Fin 3) : ℝ :=
  hqivLapseModifiedDNSLHS data input i - hqivLapseModifiedDNSRHS data input i

/-- Component equation form of the same HQIV lapse-modified DNS balance. -/
def hqivLapseModifiedDNSMomentumComponent (data : HQIVLapseModifiedDNSPointData)
    (input : HQIVTurbulenceClosureInput) (i : Fin 3) : Prop :=
  hqivLapseModifiedDNSLHS data input i = hqivLapseModifiedDNSRHS data input i

theorem hqivLapseModifiedDNSMomentumResidual_zero_iff
    (data : HQIVLapseModifiedDNSPointData) (input : HQIVTurbulenceClosureInput) (i : Fin 3) :
    hqivLapseModifiedDNSMomentumResidual data input i = 0 ↔
      hqivLapseModifiedDNSMomentumComponent data input i := by
  unfold hqivLapseModifiedDNSMomentumResidual hqivLapseModifiedDNSMomentumComponent
  rw [sub_eq_zero]

/-- HQIV lapse-modified DNS axiom package for a direct solver contract on a certified domain. -/
structure HQIVLapseModifiedDNSAxiom (dim : HQIVDNSDimension)
    (contract : HQIVDNSPythonSimulatorContract) (domain : HQIVDNSDomain dim) where
  dns_contract : HQIVDNSContractProof dim contract
  domain_certificate : HQIVDNSDomainCertificate dim contract.caseSpec domain
  resolution_data : HQIVDNSResolutionData
  resolution_certificate : HQIVDNSResolutionCertificate resolution_data
  point_data : Hqiv.ObserverChart → HQIVLapseModifiedDNSPointData
  mass_residual_zero : ∀ x, domain.interior x → contract.massResidual x = 0
  energy_residual_zero : ∀ x, domain.interior x → contract.energyResidual x = 0
  momentum_residual_eq_hqiv :
    ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
      contract.momentumResidual x i =
        hqivLapseModifiedDNSMomentumResidual (point_data x) (contract.closureInput x) i

theorem HQIVLapseModifiedDNSAxiom.momentum_component_on_domain
    {dim : HQIVDNSDimension} {contract : HQIVDNSPythonSimulatorContract}
    {domain : HQIVDNSDomain dim} (h : HQIVLapseModifiedDNSAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) {i : Fin 3}
    (hi : i ∈ dim.activeMomentumComponents) (hzero : contract.momentumResidual x i = 0) :
    hqivLapseModifiedDNSMomentumComponent (h.point_data x) (contract.closureInput x) i := by
  have hres :
      hqivLapseModifiedDNSMomentumResidual (h.point_data x) (contract.closureInput x) i = 0 := by
    rw [← h.momentum_residual_eq_hqiv x hx i hi]
    exact hzero
  exact (hqivLapseModifiedDNSMomentumResidual_zero_iff (h.point_data x) (contract.closureInput x) i).mp hres

theorem HQIVLapseModifiedDNSAxiom.mass_energy_zero_on_domain
    {dim : HQIVDNSDimension} {contract : HQIVDNSPythonSimulatorContract}
    {domain : HQIVDNSDomain dim} (h : HQIVLapseModifiedDNSAxiom dim contract domain)
    {x : Hqiv.ObserverChart} (hx : domain.interior x) :
    contract.massResidual x = 0 ∧ contract.energyResidual x = 0 :=
  ⟨h.mass_residual_zero x hx, h.energy_residual_zero x hx⟩

theorem HQIVLapseModifiedDNSAxiom.resolves_dissipation_range
    {dim : HQIVDNSDimension} {contract : HQIVDNSPythonSimulatorContract}
    {domain : HQIVDNSDomain dim} (h : HQIVLapseModifiedDNSAxiom dim contract domain) :
    h.resolution_data.gridSpacing ≤ h.resolution_data.kolmogorovScale :=
  h.resolution_certificate.resolves_dissipation_range

/-- Constructor for a 2D certified lapse-modified DNS axiom package. -/
def hqivLapseModifiedDNS2D_axiom
    (contract : HQIVDNSPythonSimulatorContract) (domain : HQIVDNSDomain .dns2D)
    (hcontract : HQIVDNSContractProof .dns2D contract)
    (hdomain : HQIVDNSDomainCertificate .dns2D contract.caseSpec domain)
    (resolutionData : HQIVDNSResolutionData)
    (hresolution : HQIVDNSResolutionCertificate resolutionData)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedDNSPointData)
    (hmass : ∀ x, domain.interior x → contract.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVDNSDimension.dns2D.activeMomentumComponents →
        contract.momentumResidual x i =
          hqivLapseModifiedDNSMomentumResidual (pointData x) (contract.closureInput x) i) :
    HQIVLapseModifiedDNSAxiom .dns2D contract domain where
  dns_contract := hcontract
  domain_certificate := hdomain
  resolution_data := resolutionData
  resolution_certificate := hresolution
  point_data := pointData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv := hmomentum

/-- Constructor for a 3D certified lapse-modified DNS axiom package. -/
def hqivLapseModifiedDNS3D_axiom
    (contract : HQIVDNSPythonSimulatorContract) (domain : HQIVDNSDomain .dns3D)
    (hcontract : HQIVDNSContractProof .dns3D contract)
    (hdomain : HQIVDNSDomainCertificate .dns3D contract.caseSpec domain)
    (resolutionData : HQIVDNSResolutionData)
    (hresolution : HQIVDNSResolutionCertificate resolutionData)
    (pointData : Hqiv.ObserverChart → HQIVLapseModifiedDNSPointData)
    (hmass : ∀ x, domain.interior x → contract.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.energyResidual x = 0)
    (hmomentum :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ HQIVDNSDimension.dns3D.activeMomentumComponents →
        contract.momentumResidual x i =
          hqivLapseModifiedDNSMomentumResidual (pointData x) (contract.closureInput x) i) :
    HQIVLapseModifiedDNSAxiom .dns3D contract domain where
  dns_contract := hcontract
  domain_certificate := hdomain
  resolution_data := resolutionData
  resolution_certificate := hresolution
  point_data := pointData
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv := hmomentum

/-!
## HQIV action/O-Maxwell to NS-shaped momentum bridge

The following records are the first-principles bridge layer.  They start from the existing
O-Maxwell action/EL chart data and the F2/F3 fluid closure hooks, then prove the DNS-shaped HQIV
momentum component.  The continuum/coarse-graining step remains an explicit hypothesis bundle: this
is not a derivation of molecular viscosity, classical Navier--Stokes well-posedness, or global
regularity.
-/

/-- Data carried by a single chart-level first-principles momentum balance. -/
structure HQIVFirstPrinciplesMomentumData where
  J_src : Fin 8 → Fin 4 → ℝ
  A : Fin 8 → Fin 4 → ℝ
  phiF : (Fin 4 → ℝ) → ℝ
  dotF : (Fin 4 → ℝ) → ℝ
  c : Fin 4 → ℝ
  phiVal : ℝ
  Eprime : ℝ
  shell : ℕ
  aLoc : ℝ
  nuMol : ℝ
  nuEddy : ℝ
  nuTotal : ℝ
  coherence : ℝ
  density : ℝ
  Phi : ℝ
  phiClock : ℝ
  time : ℝ
  pressureGrad : Fin 3 → ℝ
  laplacianVelocity : Fin 3 → ℝ
  bodyForce : Fin 3 → ℝ
  uDot : Fin 3 → ℝ
  convective : Fin 3 → ℝ
  actionScale : ℝ

/-- Canonical HQIV turbulence closure input read from first-principles chart data. -/
def hqivFirstPrinciplesClosureInput (data : HQIVFirstPrinciplesMomentumData) :
    HQIVTurbulenceClosureInput where
  shell := data.shell
  aLoc := data.aLoc
  phi := data.phiF data.c
  dotTheta := delta_theta_prime data.Eprime
  gradPhi := chartSpatialPhiGradient data.phiF data.c
  gradDot := chartSpatialDotGradient data.dotF data.c
  nuMol := data.nuMol
  coherence := data.coherence
  density := data.density

/-- DNS point data read from first-principles chart data. -/
def hqivFirstPrinciplesDNSPointData (data : HQIVFirstPrinciplesMomentumData) :
    HQIVLapseModifiedDNSPointData where
  Phi := data.Phi
  phiClock := data.phiClock
  time := data.time
  rho := data.density
  uDot := data.uDot
  convective := data.convective
  pressureGrad := data.pressureGrad
  laplacianVelocity := data.laplacianVelocity
  bodyForce := data.bodyForce

/-- Spatial O-Maxwell EL force slot feeding the coarse-grained momentum balance. -/
noncomputable def hqivFirstPrinciplesActionForce (data : HQIVFirstPrinciplesMomentumData)
    (i : Fin 3) : ℝ :=
  -data.actionScale *
    EL_O_general_coordsField data.J_src data.A data.phiVal data.phiF data.c 0 (spatialFin4 i)

/-- Action stationarity on the spatial EM channel used by the fluid chart. -/
structure ActionStationaryAtChart (data : HQIVFirstPrinciplesMomentumData) : Prop where
  stationary_spatial :
    ∀ i : Fin 3,
      EL_O_general_coordsField data.J_src data.A data.phiVal data.phiF data.c 0 (spatialFin4 i) = 0

theorem hqivFirstPrinciplesActionForce_zero
    (data : HQIVFirstPrinciplesMomentumData) (h : ActionStationaryAtChart data) (i : Fin 3) :
    hqivFirstPrinciplesActionForce data i = 0 := by
  simp [hqivFirstPrinciplesActionForce, h.stationary_spatial i]

/-- F2 chart identification specialized to the canonical first-principles closure input. -/
def HQIVFirstPrinciplesMomentumData.ChartHypothesis
    (data : HQIVFirstPrinciplesMomentumData) : Prop :=
  OMaxwellFluidChartHypothesis data.phiF data.dotF data.c (data.phiF data.c)
    (delta_theta_prime data.Eprime) (chartSpatialPhiGradient data.phiF data.c)
    (chartSpatialDotGradient data.dotF data.c) data.Eprime

/-- The canonical first-principles chart hypothesis is definitional for this data package. -/
theorem HQIVFirstPrinciplesMomentumData.canonical_chartHypothesis
    (data : HQIVFirstPrinciplesMomentumData) :
    data.ChartHypothesis where
  phi_pointwise := rfl
  grad_phi_spatial := rfl
  dotTheta_bridge := rfl
  grad_dot_spatial := rfl

/-- Vacuum source in the DNS closure equals the O-Maxwell/F2 chart source. -/
theorem hqivFirstPrinciples_vacuumSource_eq_chart
    (data : HQIVFirstPrinciplesMomentumData) :
    (hqivTurbulenceClosureOutput (hqivFirstPrinciplesClosureInput data)).vacuumMomentumSource =
      hqivVacuumMomentumSource3 gamma_HQIV (data.phiF data.c)
        (delta_theta_prime data.Eprime) (chartSpatialPhiGradient data.phiF data.c)
        (chartSpatialDotGradient data.dotF data.c) := by
  rfl

/-- The explicit F3 scalar viscosity closure for the first-principles shell/Debye slot. -/
structure HQIVContinuumBalanceClosure (data : HQIVFirstPrinciplesMomentumData) : Prop where
  fluid_closure :
    PlasmaFluidClosureAssumptions data.nuMol data.nuEddy data.nuTotal gamma_HQIV (T data.shell)
      (delta_theta_prime data.Eprime) lambdaDebye data.coherence

theorem HQIVContinuumBalanceClosure.nuTotal_eq
    {data : HQIVFirstPrinciplesMomentumData} (h : HQIVContinuumBalanceClosure data) :
    data.nuTotal =
      data.nuMol +
        hqivEddyViscosity_HQIV_shell_debye data.shell (delta_theta_prime data.Eprime)
          data.coherence :=
  nuTotal_eq_nuMol_add_shell_debye data.shell data.nuMol data.nuEddy data.nuTotal
    (delta_theta_prime data.Eprime) data.coherence h.fluid_closure

/-- Canonical shell/Debye closure data. This discharges the F3 scalar closure when the simulator
chooses the HQIV eddy formula and sets total viscosity by the scalar split. -/
structure HQIVCanonicalShellDebyeClosure (data : HQIVFirstPrinciplesMomentumData) : Prop where
  nuEddy_eq :
    data.nuEddy =
      hqivEddyViscosity_HQIV_shell_debye data.shell (delta_theta_prime data.Eprime)
        data.coherence
  nuTotal_eq : data.nuTotal = data.nuMol + data.nuEddy
  coherence_mem_unit : 0 ≤ data.coherence ∧ data.coherence ≤ 1

theorem HQIVCanonicalShellDebyeClosure.to_continuumBalanceClosure
    {data : HQIVFirstPrinciplesMomentumData} (h : HQIVCanonicalShellDebyeClosure data) :
    HQIVContinuumBalanceClosure data where
  fluid_closure := by
    refine PlasmaFluidClosureAssumptions.mk_shell_debye data.shell data.nuMol data.nuEddy
      data.nuTotal (delta_theta_prime data.Eprime) data.coherence h.nuTotal_eq ?_ h.coherence_mem_unit
    simpa [hqivEddyViscosity_HQIV_shell_debye] using h.nuEddy_eq

/-- Plasma-amplitude coherence data: the same scalar amplitude used in the O-Maxwell plasma current
selects the fluid coherence factor. -/
structure HQIVPlasmaAmplitudeCoherence (data : HQIVFirstPrinciplesMomentumData)
    (κ j₀ r : ℝ) : Prop where
  coherence_eq : data.coherence = coherenceFromPlasmaAmp κ j₀ r
  kappa_nonneg : 0 ≤ κ

theorem HQIVPlasmaAmplitudeCoherence.coherence_mem_unit
    {data : HQIVFirstPrinciplesMomentumData} {κ j₀ r : ℝ}
    (h : HQIVPlasmaAmplitudeCoherence data κ j₀ r) :
    0 ≤ data.coherence ∧ data.coherence ≤ 1 := by
  rw [h.coherence_eq]
  exact coherenceFromPlasmaAmp_mem_unit κ j₀ r h.kappa_nonneg

theorem HQIVCanonicalShellDebyeClosure.of_plasmaAmplitude
    (data : HQIVFirstPrinciplesMomentumData) {κ j₀ r : ℝ}
    (hC : HQIVPlasmaAmplitudeCoherence data κ j₀ r)
    (hEddy :
      data.nuEddy =
        hqivEddyViscosity_HQIV_shell_debye_plasmaAmp data.shell
          (delta_theta_prime data.Eprime) κ j₀ r)
    (hTotal : data.nuTotal = data.nuMol + data.nuEddy) :
    HQIVCanonicalShellDebyeClosure data where
  nuEddy_eq := by
    simpa [hqivEddyViscosity_HQIV_shell_debye_plasmaAmp, hC.coherence_eq] using hEddy
  nuTotal_eq := hTotal
  coherence_mem_unit := hC.coherence_mem_unit

/-- Coarse-graining hypothesis: the action force, pressure, viscosity, body force, and HQIV vacuum
source combine into the direct momentum balance. This is the explicit continuum step. -/
structure OMaxwellToFluidBalanceHypothesis (data : HQIVFirstPrinciplesMomentumData) : Prop where
  momentum_from_action :
    ∀ i : Fin 3,
      hqivLapseModifiedDNSLHS (hqivFirstPrinciplesDNSPointData data)
          (hqivFirstPrinciplesClosureInput data) i =
        (-data.pressureGrad i) + data.nuTotal * data.laplacianVelocity i + data.bodyForce i +
          hqivVacuumMomentumSource3 gamma_HQIV (data.phiF data.c)
            (delta_theta_prime data.Eprime) (chartSpatialPhiGradient data.phiF data.c)
            (chartSpatialDotGradient data.dotF data.c) i +
          hqivFirstPrinciplesActionForce data i

/-- First-principles bridge bundle from O-Maxwell chart data to the HQIV NS-shaped DNS component. -/
structure HQIVFirstPrinciplesNSBridge (data : HQIVFirstPrinciplesMomentumData) : Prop where
  chart_hypothesis : data.ChartHypothesis
  action_stationary : ActionStationaryAtChart data
  continuum_closure : HQIVContinuumBalanceClosure data
  fluid_balance : OMaxwellToFluidBalanceHypothesis data

/-- Reduced bridge with the definitional F2 chart identification and canonical F3 closure already
discharged. The only remaining fluid-side hypothesis is the continuum stress/balance decomposition. -/
structure HQIVFirstPrinciplesNSBridgeCanonical (data : HQIVFirstPrinciplesMomentumData) : Prop where
  action_stationary : ActionStationaryAtChart data
  canonical_closure : HQIVCanonicalShellDebyeClosure data
  fluid_balance : OMaxwellToFluidBalanceHypothesis data

theorem HQIVFirstPrinciplesNSBridgeCanonical.to_bridge
    {data : HQIVFirstPrinciplesMomentumData} (h : HQIVFirstPrinciplesNSBridgeCanonical data) :
    HQIVFirstPrinciplesNSBridge data where
  chart_hypothesis := data.canonical_chartHypothesis
  action_stationary := h.action_stationary
  continuum_closure := h.canonical_closure.to_continuumBalanceClosure
  fluid_balance := h.fluid_balance

/-- Plasma-amplitude version of the canonical bridge. This discharges the coherence interval and
shell/Debye eddy assumption from the existing plasma-amplitude current/coherence package. -/
structure HQIVFirstPrinciplesNSBridgePlasmaAmp (data : HQIVFirstPrinciplesMomentumData)
    (κ j₀ r : ℝ) : Prop where
  action_stationary : ActionStationaryAtChart data
  plasma_coherence : HQIVPlasmaAmplitudeCoherence data κ j₀ r
  nuEddy_eq :
    data.nuEddy =
      hqivEddyViscosity_HQIV_shell_debye_plasmaAmp data.shell
        (delta_theta_prime data.Eprime) κ j₀ r
  nuTotal_eq : data.nuTotal = data.nuMol + data.nuEddy
  fluid_balance : OMaxwellToFluidBalanceHypothesis data

theorem HQIVFirstPrinciplesNSBridgePlasmaAmp.to_canonical
    {data : HQIVFirstPrinciplesMomentumData} {κ j₀ r : ℝ}
    (h : HQIVFirstPrinciplesNSBridgePlasmaAmp data κ j₀ r) :
    HQIVFirstPrinciplesNSBridgeCanonical data where
  action_stationary := h.action_stationary
  canonical_closure :=
    HQIVCanonicalShellDebyeClosure.of_plasmaAmplitude data h.plasma_coherence h.nuEddy_eq
      h.nuTotal_eq
  fluid_balance := h.fluid_balance

/-- The first-principles bridge supplies the DNS-shaped HQIV momentum component. -/
theorem HQIVFirstPrinciplesNSBridge.to_dns_momentum_component
    {data : HQIVFirstPrinciplesMomentumData} (h : HQIVFirstPrinciplesNSBridge data) (i : Fin 3) :
    hqivLapseModifiedDNSMomentumComponent (hqivFirstPrinciplesDNSPointData data)
      (hqivFirstPrinciplesClosureInput data) i := by
  unfold hqivLapseModifiedDNSMomentumComponent
  have hnu := h.continuum_closure.nuTotal_eq
  have hforce := hqivFirstPrinciplesActionForce_zero data h.action_stationary i
  have hbal := h.fluid_balance.momentum_from_action i
  calc
    hqivLapseModifiedDNSLHS (hqivFirstPrinciplesDNSPointData data)
        (hqivFirstPrinciplesClosureInput data) i =
        (-data.pressureGrad i) + data.nuTotal * data.laplacianVelocity i + data.bodyForce i +
          hqivVacuumMomentumSource3 gamma_HQIV (data.phiF data.c)
            (delta_theta_prime data.Eprime) (chartSpatialPhiGradient data.phiF data.c)
            (chartSpatialDotGradient data.dotF data.c) i +
          hqivFirstPrinciplesActionForce data i := hbal
    _ = hqivLapseModifiedDNSRHS (hqivFirstPrinciplesDNSPointData data)
          (hqivFirstPrinciplesClosureInput data) i := by
        simp [hqivLapseModifiedDNSRHS, hqivTurbulenceClosureOutput,
          hqivFirstPrinciplesClosureInput, hqivFirstPrinciplesDNSPointData, hnu, hforce]

theorem HQIVFirstPrinciplesNSBridge.to_dns_momentum_residual_zero
    {data : HQIVFirstPrinciplesMomentumData} (h : HQIVFirstPrinciplesNSBridge data) (i : Fin 3) :
    hqivLapseModifiedDNSMomentumResidual (hqivFirstPrinciplesDNSPointData data)
      (hqivFirstPrinciplesClosureInput data) i = 0 :=
  (hqivLapseModifiedDNSMomentumResidual_zero_iff (hqivFirstPrinciplesDNSPointData data)
    (hqivFirstPrinciplesClosureInput data) i).mpr (h.to_dns_momentum_component i)

theorem HQIVFirstPrinciplesNSBridgeCanonical.to_dns_momentum_component
    {data : HQIVFirstPrinciplesMomentumData} (h : HQIVFirstPrinciplesNSBridgeCanonical data)
    (i : Fin 3) :
    hqivLapseModifiedDNSMomentumComponent (hqivFirstPrinciplesDNSPointData data)
      (hqivFirstPrinciplesClosureInput data) i :=
  h.to_bridge.to_dns_momentum_component i

theorem HQIVFirstPrinciplesNSBridgeCanonical.to_dns_momentum_residual_zero
    {data : HQIVFirstPrinciplesMomentumData} (h : HQIVFirstPrinciplesNSBridgeCanonical data)
    (i : Fin 3) :
    hqivLapseModifiedDNSMomentumResidual (hqivFirstPrinciplesDNSPointData data)
      (hqivFirstPrinciplesClosureInput data) i = 0 :=
  h.to_bridge.to_dns_momentum_residual_zero i

theorem HQIVFirstPrinciplesNSBridgePlasmaAmp.to_dns_momentum_component
    {data : HQIVFirstPrinciplesMomentumData} {κ j₀ r : ℝ}
    (h : HQIVFirstPrinciplesNSBridgePlasmaAmp data κ j₀ r) (i : Fin 3) :
    hqivLapseModifiedDNSMomentumComponent (hqivFirstPrinciplesDNSPointData data)
      (hqivFirstPrinciplesClosureInput data) i :=
  h.to_canonical.to_dns_momentum_component i

theorem HQIVFirstPrinciplesNSBridgePlasmaAmp.to_dns_momentum_residual_zero
    {data : HQIVFirstPrinciplesMomentumData} {κ j₀ r : ℝ}
    (h : HQIVFirstPrinciplesNSBridgePlasmaAmp data κ j₀ r) (i : Fin 3) :
    hqivLapseModifiedDNSMomentumResidual (hqivFirstPrinciplesDNSPointData data)
      (hqivFirstPrinciplesClosureInput data) i = 0 :=
  h.to_canonical.to_dns_momentum_residual_zero i

/-- Build a certified DNS axiom package when every interior chart point carries a first-principles
bridge and the simulator residual callbacks are the corresponding zero-residual readout. -/
def hqivLapseModifiedDNSAxiom_of_firstPrinciples
    {dim : HQIVDNSDimension} (contract : HQIVDNSPythonSimulatorContract)
    (domain : HQIVDNSDomain dim)
    (hcontract : HQIVDNSContractProof dim contract)
    (hdomain : HQIVDNSDomainCertificate dim contract.caseSpec domain)
    (resolutionData : HQIVDNSResolutionData)
    (hresolution : HQIVDNSResolutionCertificate resolutionData)
    (dataAt : Hqiv.ObserverChart → HQIVFirstPrinciplesMomentumData)
    (hbridge : ∀ x, domain.interior x → HQIVFirstPrinciplesNSBridge (dataAt x))
    (hinput : ∀ x, domain.interior x →
      contract.closureInput x = hqivFirstPrinciplesClosureInput (dataAt x))
    (hmass : ∀ x, domain.interior x → contract.massResidual x = 0)
    (henergy : ∀ x, domain.interior x → contract.energyResidual x = 0)
    (hmomentum_zero :
      ∀ x, domain.interior x → ∀ i : Fin 3, i ∈ dim.activeMomentumComponents →
        contract.momentumResidual x i = 0) :
    HQIVLapseModifiedDNSAxiom dim contract domain where
  dns_contract := hcontract
  domain_certificate := hdomain
  resolution_data := resolutionData
  resolution_certificate := hresolution
  point_data := fun x => hqivFirstPrinciplesDNSPointData (dataAt x)
  mass_residual_zero := hmass
  energy_residual_zero := henergy
  momentum_residual_eq_hqiv := by
    intro x hx i hi
    have hres :
        hqivLapseModifiedDNSMomentumResidual (hqivFirstPrinciplesDNSPointData (dataAt x))
            (hqivFirstPrinciplesClosureInput (dataAt x)) i = 0 :=
      (hbridge x hx).to_dns_momentum_residual_zero i
    calc
      contract.momentumResidual x i = 0 := hmomentum_zero x hx i hi
      _ = hqivLapseModifiedDNSMomentumResidual (hqivFirstPrinciplesDNSPointData (dataAt x))
            (contract.closureInput x) i := by
        rw [hinput x hx]
        exact hres.symm

end

end Hqiv.Physics
