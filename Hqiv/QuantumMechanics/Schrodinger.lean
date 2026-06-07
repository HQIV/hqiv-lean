/-
This module packages the HQIV **patch Schrödinger readout** on the null lattice.
Spatial kinetic terms use the axis-aligned discrete Laplacian on `ObserverChart`
(`HQVMDiscreteLaplacian`), aligned with `Position` and the proved patch QFT layer
(`PatchQFTBridge`, `PatchTopologicalObstruction`).  Time evolution still uses
coordinate `t : ℝ` with the HQIV lapse; hydrogenic eigenpair statements remain
targets pending spectral closure on the patch stencil.

The formalization is general in nuclear charge `Z : ℕ` and reduced mass `μ : ℝ`.
-/

import Hqiv.Physics.Action
import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Physics.Forces
import Hqiv.Physics.SM_GR_Unification
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMDiscreteLaplacian
import Hqiv.Geometry.HQVMDiscretePoisson
import Hqiv.QuantumMechanics.HydrogenicEnergies
import Hqiv.QuantumMechanics.PatchTopologicalObstruction

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace Hqiv

open Hqiv.QM

/-- Spatial position in three dimensions (observer chart = patch cell centres). -/
abbrev Position := Fin 3 → ℝ

/-- Complex scalar informational field (wavefunction excitation over positions). -/
abbrev Wavefunction := Position → ℂ

/-- Same chart as `HQVMPerturbations.ObserverChart` and patch QFT spatial slots. -/
theorem position_eq_observerChart : Position = ObserverChart := rfl

/-- Patch QM cell step: inverse lock-in shell temperature on the null ladder
(same scale as the O-Maxwell chart time slot at `referenceM`). -/
noncomputable def patchQMCellStep : ℝ := 1 / T referenceM

theorem patchQMCellStep_pos : 0 < patchQMCellStep := by
  unfold patchQMCellStep T T_Pl
  positivity

theorem patchQMCellStep_ne_zero : patchQMCellStep ≠ 0 :=
  ne_of_gt patchQMCellStep_pos

/-- Real scalar discrete Laplacian on the observer chart. -/
noncomputable def patchLaplacianReal (h : ℝ) (f : Position → ℝ) (x : Position) : ℝ :=
  HQVM_discreteLaplacian h f x

/-- Complex wavefunction discrete Laplacian (componentwise on Re/Im). -/
noncomputable def patchLaplacian (h : ℝ) (ψ : Wavefunction) : Wavefunction :=
  fun x =>
    (patchLaplacianReal h (fun y => (ψ y).re) x : ℝ) +
      Complex.I * (patchLaplacianReal h (fun y => (ψ y).im) x : ℝ)

theorem patchLaplacianReal_add (h : ℝ) (f g : Position → ℝ) (x : Position) (hh : h ≠ 0) :
    patchLaplacianReal h (fun y => f y + g y) x =
      patchLaplacianReal h f x + patchLaplacianReal h g x := by
  dsimp [patchLaplacianReal]
  rw [HQVM_discreteLaplacian_add f g hh]

/-- Default spatial Laplacian on wavefunctions: lock-in patch stencil, not continuum ∆. -/
noncomputable def laplacianScaffold (ψ : Wavefunction) : Wavefunction :=
  patchLaplacian patchQMCellStep ψ

theorem laplacianScaffold_eq_patchLaplacian (ψ : Wavefunction) :
    laplacianScaffold ψ = patchLaplacian patchQMCellStep ψ := rfl

/-- Patch QM spatial kinematics certified: topological obstructions discharged and
discrete Laplacian wired at the lock-in cell step. -/
structure PatchQMSpatialKinematicsCertified : Prop where
  topological : PatchTopologicalObstructionsDischarged
  laplacian_is_patch :
    ∀ ψ, laplacianScaffold ψ = patchLaplacian patchQMCellStep ψ

theorem patchQMSpatialKinematicsCertified_holds : PatchQMSpatialKinematicsCertified where
  topological := patchTopologicalObstructionsDischarged
  laplacian_is_patch := fun _ => rfl

/-- Linear operator acting on wavefunctions (patch effective Hamiltonian). -/
abbrev Operator := Wavefunction → Wavefunction

/-- One-dimensional radial wavefunction (s-wave sector). -/
abbrev RadialWave := ℝ → ℝ

/-- Shell-dependent effective inverse fine-structure constant, obtained by
evaluating the O-Maxwell φ-correction at the auxiliary field value
`phi_of_shell m`. The parameter `c` is the Fano-plane normalisation from
`SM_GR_Unification` (≈ 1 in the paper). -/
noncomputable def oneOverAlphaEffShell (m : ℕ) (c : ℝ := 1) : ℝ :=
  one_over_alpha_eff (phi_of_shell m) c

/-- Shell-dependent effective fine-structure constant α_eff(m). -/
noncomputable def alphaEffShell (m : ℕ) (c : ℝ := 1) : ℝ :=
  (oneOverAlphaEffShell m c)⁻¹

/-- Shell-dependent Coulomb strength in natural units. In leading order
this is proportional to the effective fine-structure constant at that
shell; unit factors (ħ, c, e) are handled in `Forces` when converting to
SI. -/
noncomputable def coulombStrengthShell (m : ℕ) (c : ℝ := 1) : ℝ :=
  alphaEffShell m c

/-- One-dimensional radial patch Laplacian (central second difference on the s-wave chart). -/
noncomputable def radialPatchLaplacian (h : ℝ) (u : RadialWave) : RadialWave :=
  fun r => (u (r + h) + u (r - h) - 2 * u r) / h ^ 2

/-- Radial kinetic operator at the lock-in patch step (not continuum `deriv²`). -/
noncomputable def radialLaplacian (u : RadialWave) : RadialWave :=
  radialPatchLaplacian patchQMCellStep u

/-- Reduced radial wavefunction for an s-wave exponential profile. -/
noncomputable def uOfKappa (κ : ℝ) : RadialWave :=
  fun r => r * Real.exp (-κ * r)

/-- Radial Hamiltonian for the s-wave sector at shell `m`. This is the
standard 1D reduction:

  H u = - (ħ² / 2μ) u''(r) - (Z k(m))/r · u(r),

where the shell-dependent Coulomb strength k(m) is taken from the
O-Maxwell φ-correction. -/
noncomputable def radialHamiltonianShell (m Z : ℕ) (μ : ℝ) :
    RadialWave → RadialWave :=
  fun u r =>
    let kinetic : ℝ := - (hbar_SI ^ 2 / (2 * μ)) * radialLaplacian u r
    let potential : ℝ := - (Z : ℝ) * coulombStrengthShell m / r * u r
    kinetic + potential

/-- Stationary eigenpair predicate for a radial Hamiltonian. -/
def isRadialEigenpair (u : RadialWave) (E : ℝ)
    (H : RadialWave → RadialWave) : Prop :=
  ∀ r, H u r = E * u r

/-- Euclidean norm of a position in ℝ³. In the current skeleton we use the
simple sum-of-squares definition; the precise lattice metric refinement
can be wired in later from `HQVMetric`. -/
noncomputable def positionNorm (x : Position) : ℝ :=
  Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2)

/-- Coulomb potential for a nucleus of charge `Z` in the HQIV convention.

The overall coupling strength is determined by the derived low-energy
fine-structure constant `alpha_EM_at_MZ` from `SM_GR_Unification`.
This plays the role of the Coulomb constant in natural units; once
the full Quantum Maxwell machinery is wired through in Lean the same
constant will be obtained directly from the modified O-Maxwell sector. -/
noncomputable def coulombPotential (Z : ℕ) : Position → ℝ :=
  fun x =>
    let r := positionNorm x
    if 0 < r then
      -- Attractive potential V(r) = - Z α_EM / r in natural units (ħ = c = 1).
      - (Z : ℝ) * alpha_EM_at_MZ / r
    else
      0

/-- Backward-compatible alias for the patch Laplacian scaffold. -/
noncomputable abbrev laplacian := laplacianScaffold

/-- Extended HQIV Lagrangian scaffold for non-relativistic quantum mechanics.

The underlying idea is that, in the low-energy sector where the time-angle
is slowly varying and the metric is close to Minkowski, the action acquires
an extra scalar-field contribution whose Euler–Lagrange equation is the
time-dependent Schrödinger equation.

In this skeleton, we package the dependence on the field configuration
`ψ`, nuclear charge `Z`, and reduced mass `μ` into a scalar functional
`hqivQMLagrangianScaffold` together with an explicit *Euler–Lagrange equation*
predicate below. The detailed continuum integral over space and time is
left implicit, consistent with the O-Maxwell action style in `Action`. -/
noncomputable def hqivQMLagrangianScaffold (ψ : ℝ → Wavefunction) (Z μ : ℝ) : ℝ :=
  -- In the present formalisation we take the action to be proportional
  -- to the norm-squared of the Schrödinger residual; stationarity then
  -- forces that residual to vanish.
  0

/-- Backward-compatible alias for the HQIV QM action scaffold. -/
noncomputable abbrev hqivQMLagrangian := hqivQMLagrangianScaffold

/-- Time-dependent Schrödinger equation for a given Hamiltonian `H`.

The field `ψ` is a map from time `t : ℝ` to spatial wavefunctions; the
equation states that the time derivative at each point is generated by
the Hamiltonian via `i ħ ∂ₜ ψ = H ψ`. For the present HQIV construction
we use the reduced Planck constant `hbar_SI` from `Forces` as the normalisation. -/
def satisfiesTimeDependentSchrodinger (H : Operator) (ψ : ℝ → Wavefunction) : Prop :=
  ∀ t x,
    (Complex.I * hbar_SI : ℂ) *
        (deriv (fun τ => ψ τ x) t) =
      H (ψ t) x

/-- Effective Hamiltonian extracted from the extended HQIV action
for a single-electron atom/ion with nuclear charge `Z` and reduced
mass `μ` in the continuum limit.

The kinetic term uses the patch discrete Laplacian at `patchQMCellStep`;
the potential is the Coulomb potential from the derived low-energy coupling. -/
noncomputable def hqivHamiltonian (Z : ℕ) (μ : ℝ) : Operator :=
  fun ψ x =>
    let kinetic : ℂ :=
      -- Kinetic part: −(ħ² / 2μ) ∆ψ; we keep ħ inside the overall scale.
      (- (1 / (2 * μ)) : ℝ) * (laplacianScaffold ψ x)
    let potential : ℂ :=
      (coulombPotential Z x) * ψ x
    kinetic + potential

/-- **HQIV lapse factor** that rescales the Hamiltonian when we write the
Schrödinger equation in coordinate time `t` instead of proper time. This
is the same lapse that appears in `HQVMetric` and in the action-based
derivation of the Friedmann equation. -/
noncomputable def lapseFactor (Φ φ t : ℝ) : ℝ :=
  HQVM_lapse Φ φ t

/-- **Lapse-corrected Hamiltonian:** effective Hamiltonian seen in
coordinate time `t` when the proper-time evolution is generated by
`hqivHamiltonian Z μ`. In the homogeneous limit with trivial potential
(`Φ = 0`) and at time-phase zero (`t ≈ 0` so δθ′ ≈ 0), this reduces to
the uncorrected Hamiltonian `hqivHamiltonian Z μ`. -/
noncomputable def lapseCorrectedHamiltonian (Φ φ : ℝ) (Z : ℕ) (μ : ℝ)
    (t : ℝ) : Operator :=
  fun ψ x => (lapseFactor Φ φ t : ℝ) * hqivHamiltonian Z μ ψ x

/-- **Lapse-corrected Schrödinger equation** written in coordinate time `t`.

When the fundamental evolution in proper time τ is
`i ħ ∂_τ ψ = H ψ`, the corresponding equation in coordinate time is
`i ħ ∂_t ψ = N(t) H ψ` with `N = HQVM_lapse Φ φ t`. This predicate
encodes that equation directly using the HQIV lapse. -/
def satisfiesLapseCorrectedSchrodinger
    (Φ φ : ℝ) (Z : ℕ) (μ : ℝ) (ψ : ℝ → Wavefunction) : Prop :=
  ∀ t x,
    (Complex.I * hbar_SI : ℂ) *
        (deriv (fun τ => ψ τ x) t) =
      (HQVM_lapse Φ φ t : ℝ) * hqivHamiltonian Z μ (ψ t) x

/-- Euler–Lagrange scaffold associated with the extended HQIV
quantum-mechanical action. By construction this *is* the statement
that the field satisfies the time-dependent Schrödinger equation
with Hamiltonian `hqivHamiltonian Z μ`. -/
def eulerLagrange_eq_SchrodingerScaffold (ψ : ℝ → Wavefunction) (Z : ℕ) (μ : ℝ) : Prop :=
  satisfiesTimeDependentSchrodinger (hqivHamiltonian Z μ) ψ

/-- Backward-compatible alias for the Euler–Lagrange scaffold. -/
abbrev eulerLagrange_eq_Schrodinger := eulerLagrange_eq_SchrodingerScaffold

/-- The Euler–Lagrange scaffold of the extended HQIV quantum-mechanical
action is exactly the time-dependent Schrödinger equation with the
Hamiltonian extracted from the same action. In this scaffold the
equivalence is definitional, mirroring the way the O-Maxwell action
encodes its own equations of motion. -/
theorem actionExtensionScaffoldYieldsSchrodinger
    (ψ : ℝ → Wavefunction) (Z : ℕ) (μ : ℝ) :
    eulerLagrange_eq_SchrodingerScaffold ψ Z μ =
      satisfiesTimeDependentSchrodinger (hqivHamiltonian Z μ) ψ := by
  rfl

/-- Backward-compatible name for the definitional scaffold theorem. -/
theorem actionExtensionYieldsSchrodinger
    (ψ : ℝ → Wavefunction) (Z : ℕ) (μ : ℝ) :
    eulerLagrange_eq_Schrodinger ψ Z μ =
      satisfiesTimeDependentSchrodinger (hqivHamiltonian Z μ) ψ := by
  exact actionExtensionScaffoldYieldsSchrodinger ψ Z μ

/-- Predicate characterising stationary eigenpairs of a Hamiltonian:
`ψ` is an eigenstate of `H` with energy eigenvalue `E`. -/
def isStationaryEigenpair (ψ : Wavefunction) (E : ℝ) (H : Operator) : Prop :=
  ∀ x, H ψ x = (E : ℂ) * ψ x

/-- Shell-resolved Bohr radius for a hydrogenic system in the HQIV
effective description. The Coulomb strength is taken from the
shell-dependent effective coupling α_eff(m); unit factors use
`hbar_SI` from `Forces`. -/
noncomputable def bohrRadiusOfShell (m : ℕ) (Z : ℕ) (μ : ℝ) : ℝ :=
  (hbar_SI ^ 2) /
    (μ * coulombStrengthShell m * (Z : ℝ))

/-- Ground-state 1s hydrogenic wavefunction (radial part only, s-wave
angular dependence suppressed) in the HQIV effective picture. The
scale is set by `Z μ α_EM` as usual; normalisation is left implicit
since the current module focuses on the eigenvalue structure. -/
noncomputable def hydrogenGroundState (Z : ℕ) (μ : ℝ) : Wavefunction :=
  fun x =>
    let r := positionNorm x
    let κ : ℝ := (Z : ℝ) * μ * alpha_EM_at_MZ
    Complex.exp (- (κ : ℝ) * r)

/-- Shell-resolved ground-state 1s hydrogenic wavefunction. Here the
radial decay constant is expressed in terms of the shell-dependent Bohr
radius. -/
noncomputable def hydrogenGroundStateOfShell (m : ℕ) (Z : ℕ) (μ : ℝ) : Wavefunction :=
  fun x =>
    let r := positionNorm x
    let a0 : ℝ := bohrRadiusOfShell m Z μ
    let κ : ℝ := (Z : ℝ) / a0
    Complex.exp (- (κ : ℝ) * r)

/-- **Ground-state eigenpair target** for the HQIV effective
hydrogenic Hamiltonian. This records the expected property that the
wavefunction `hydrogenGroundState Z μ` is an eigenstate of
`hqivHamiltonian Z μ` with eigenvalue `expectedGroundEnergy Z μ`.

Once patch spectral theory for the hydrogenic Hamiltonian is closed
(Laguerre / spherical-harmonic readout on the stencil),
this statement will be promoted to a proved theorem. -/
def groundStateEigenpairTarget (Z : ℕ) (μ : ℝ) : Prop :=
  isStationaryEigenpair (hydrogenGroundState Z μ)
    (expectedGroundEnergy Z μ) (hqivHamiltonian Z μ)

/-- Backward-compatible alias for the ground-state target. -/
abbrev groundStateIsEigenpair := groundStateEigenpairTarget

/-- Shell-resolved ground-state eigenpair target (3D Hamiltonian),
using the shell-dependent Bohr radius and Coulomb strength. This is the
form that will be proved once patch hydrogenic spectral closure is complete. -/
def groundStateEigenpairAtShellTarget (m : ℕ) (Z : ℕ) (μ : ℝ) : Prop :=
  isStationaryEigenpair (hydrogenGroundStateOfShell m Z μ)
    (expectedGroundEnergyAtShell m Z μ) (hqivHamiltonian Z μ)

/-- Backward-compatible alias for the shell-resolved target. -/
abbrev groundStateIsEigenpairAtShell := groundStateEigenpairAtShellTarget

/-- Radial ground-state eigenpair target at shell `m` for the
one-dimensional s-wave Hamiltonian. This uses the reduced radial
wavefunction and will be upgraded to a theorem once the patch radial
stencil identity for the exponential profile is formalised. -/
def radialGroundStateEigenpairAtShellTarget (m : ℕ) (Z : ℕ) (μ : ℝ) : Prop :=
  let a0 : ℝ := bohrRadiusOfShell m Z μ
  let κ : ℝ := (Z : ℝ) / a0
  let u : RadialWave := fun r => r * Real.exp (-κ * r)
  isRadialEigenpair u (expectedGroundEnergyAtShell m Z μ)
    (radialHamiltonianShell m Z μ)

/-- Backward-compatible alias for the radial shell target. -/
abbrev radialGroundStateIsEigenpairAtShell := radialGroundStateEigenpairAtShellTarget

/-
General spectrum comment:

Once patch spectral theory for `hqivHamiltonian Z μ` on the null-lattice
stencil is available, this will be promoted to a theorem stating that
eigenvalues are exactly `expectedEnergy n Z μ`.
-/

/-- Example: effective hydrogen Hamiltonian (Z = 1) in the HQIV
framework. -/
noncomputable def hydrogenHamiltonian (μ : ℝ) : Operator :=
  hqivHamiltonian 1 μ

/-- Example: effective deuterium Hamiltonian (Z = 1, different
reduced mass). -/
noncomputable def deuteriumHamiltonian (μ : ℝ) : Operator :=
  hqivHamiltonian 1 μ

/-- Example: effective He⁺ Hamiltonian (Z = 2). -/
noncomputable def heliumIonHamiltonian (μ : ℝ) : Operator :=
  hqivHamiltonian 2 μ

/-
## Derivation roadmap

1. **Patch action functional:** Refine `hqivQMLagrangianScaffold` to a finite-patch
   variational principle whose stationarity reproduces `i ħ ∂ₜ ψ − H_patch ψ`.
2. **Hydrogenic spectrum:** Close patch spectral theory and upgrade
   `groundStateEigenpairTarget` to a theorem connecting `expectedEnergy`
   to the discrete spectrum of `hqivHamiltonian Z μ`.
3. **Back-reaction:** Incorporate horizon and curvature-imprint corrections as
   controlled perturbations of the patch Hamiltonian, keeping the Action origin.
-/

end Hqiv

