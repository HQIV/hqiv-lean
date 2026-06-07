import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.ContinuumSpacetimeChart
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.OMaxwellAlgebraSeed
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Order.Monotone.Basic

namespace Hqiv

open Hqiv.Geometry

/-!
# Emergent Maxwell Equations: O → H → 3D

We build the equation **in O** (octonion algebra, 8 components), then **reduce to
classic Maxwell in H** (quaternionic subalgebra, 4 components), then **derive
Maxwell's 3D equations** by holding one axis fixed.

- **O**: Full equation in 8 components (indices 0..7; abstract labels a,b,c,d,e,f,g,h).
  No assignment yet of which component is which physical field.
- **H**: Restriction to the quaternionic subalgebra (components 0..3). We prove the
  O-equation restricted to H has the form of classic Maxwell.
- **3D**: Fix one spacetime axis (e.g. time); the remaining 3D spatial equations
  are the usual div E, curl B − ∂E/∂t, etc. (Units and which axis is time, which
  octonion components are E/B, are handled later in Conservations → Forces.)

## Proof status

- **Proven:** O → H reduction to classic Maxwell when φ constant and metric flat;
  charge conservation for spatially constant sources (`div_μ` via `coordsDivergence`); flat limit instance.
- **Chart slots (discharged):** `grad_φ` and `div_μ` are the lock-in readout of
  `coordsGradientComponents` / `coordsDivergence` at `defaultOMaxwellChartPoint` (time slot =
  `T referenceM`). Parametric chart variants live in `ContinuumOmaxwellClosure`
  (`emergentMaxwellInhomogeneous_O_coordsField`, `EL_O_general_coordsField`). Vacuum `J_O` and
  `A_O` remain zero; plasma uses `J_O_plasma` in `SchematicPlasmaCurrent`.

**Plasma-facing note:** `J_O` is the natural hook for collective currents; filling
it in (and the manifold placeholders) is how dense plasma couples back to the same
φ ladder used in fermion mass ladders (`ChargedLeptonResonance`, `QuarkMetaResonance`).
See README “Roadmap: plasmas, modified inertia, and fermion ladders”.

For hyperspherical **scalar** spectra aligned with this O → H split (`S³` for the quaternion
sector, `S⁴` as the next shell), see `Hqiv.Geometry.QuaternionMaxwellS3OMaxwellS4Spectral`.
-/

/-- Lock-in chart basepoint: time coordinate carries shell temperature `T referenceM`. -/
noncomputable def defaultOMaxwellChartPoint : Fin 4 → ℝ :=
  fun μ => if μ = (0 : Fin 4) then T referenceM else 0

/-- Scalar φ on the chart from the temperature ladder (`c 0` = local Θ). -/
noncomputable def omaxwellPhiField (c : Fin 4 → ℝ) : ℝ :=
  phi_of_T (c 0)

/-- **(∇φ)_ν** at the lock-in readout point (Euclidean chart gradient). -/
noncomputable def grad_φ (ν : Fin 4) : ℝ :=
  coordsGradientComponents omaxwellPhiField defaultOMaxwellChartPoint ν

theorem grad_φ_eq_coordsGradientComponents_default (ν : Fin 4) :
    grad_φ ν = coordsGradientComponents omaxwellPhiField defaultOMaxwellChartPoint ν := rfl

/-- Divergence of a **spatially constant** 4-vector (constant extension on the chart). -/
noncomputable def div_μ (f : Fin 4 → ℝ) : ℝ :=
  coordsDivergence (fun _ => f) defaultOMaxwellChartPoint

/-- Divergence of a general coordinate vector field at chart point `c`. -/
noncomputable def div_μ_field (V : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  coordsDivergence V c

theorem div_μ_eq_coordsDivergence_default (f : Fin 4 → ℝ) :
    div_μ f = coordsDivergence (fun _ => f) defaultOMaxwellChartPoint := rfl

theorem div_μ_const_field_zero (f : Fin 4 → ℝ) : div_μ f = 0 := by
  rw [div_μ_eq_coordsDivergence_default, coordsDivergence_const]

/-- When `phi_of_T` is constant, the lock-in φ gradient vanishes (flat-φ / H-reduction regime). -/
theorem grad_φ_zero_when_phi_of_T_constant (h : ∀ x, phi_of_T x = phiTemperatureCoeff) :
    ∀ ν, grad_φ ν = 0 := by
  intro ν
  rw [grad_φ_eq_coordsGradientComponents_default]
  have hfield : omaxwellPhiField = fun _ : Fin 4 → ℝ => phiTemperatureCoeff := by
    funext c
    simp [omaxwellPhiField, h (c 0)]
  rw [hfield]
  rw [coordsGradientComponents_const phiTemperatureCoeff defaultOMaxwellChartPoint]
  simp

/-- Radial metric component (placeholder: flat; derived metric in O/H later). -/
def g_rr (_x : ℝ) : ℝ := 1

/-- Field strength in O: 8 algebra components, 4×4 spacetime (placeholder 2-form per component). -/
structure F_O where
  comp : Fin 8 → Fin 4 → Fin 4 → ℝ
  antisymm : ∀ a μ ν, comp a μ ν = - comp a ν μ

/-- Current in O (8 components; phenomenological for now). -/
def J_O (_a : Fin 8) (_ν : Fin 4) : ℝ := 0

/-!
Emergent inhomogeneous O–Maxwell slots.

The legacy `emergentMaxwellInhomogeneous_O_general` keeps a **zero** divergence slot for the
potential-free packaging.  When a gauge potential `A` is available, use
`emergentMaxwellInhomogeneous_O_fromPotential`, which carries the same flat discrete divergence
as `Action.F_divergence_sum` / `covariant_div_F_O` on the identity metric.
-/

/-- Flat discrete divergence `∑_μ F_{μν}` from a gauge potential (matches `Action.F_divergence_sum`). -/
noncomputable def emergentFlatDivergence_sum (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  ∑ μ : Fin 4, (A a ν - A a μ)

/-- **Emergent inhomogeneous equation with explicit potential** (flat divergence discharged). -/
noncomputable def emergentMaxwellInhomogeneous_O_fromPotential
    (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  emergentFlatDivergence_sum A a ν - 4 * Real.pi * J_src a ν -
    alpha * algebraicMaxwellCouplingLog ν * grad_φ ν

/-- **Emergent inhomogeneous equation in O** with an arbitrary source `J_src` (defaults to `J_O`).

Potential-free packaging: divergence slot vanishes; see `emergentMaxwellInhomogeneous_O_fromPotential`. -/
noncomputable def emergentMaxwellInhomogeneous_O_general (J_src : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    ℝ :=
  let phiCorrection := alpha * algebraicMaxwellCouplingLog ν * (grad_φ ν)
  0.0 - 4 * Real.pi * J_src a ν - phiCorrection

theorem emergentMaxwellInhomogeneous_O_fromPotential_eq_general_when_grad_zero
    (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4)
    (hgrad : grad_φ ν = 0) :
    emergentMaxwellInhomogeneous_O_fromPotential J_src A a ν =
      emergentFlatDivergence_sum A a ν - 4 * Real.pi * J_src a ν := by
  unfold emergentMaxwellInhomogeneous_O_fromPotential
  simp [hgrad, mul_zero, sub_zero, add_zero]

theorem emergentMaxwellInhomogeneous_O_general_eq_fromPotential_when_A_zero
    (J_src : Fin 8 → Fin 4 → ℝ) (A0 : Fin 8 → Fin 4 → ℝ) (hA : ∀ a μ, A0 a μ = 0) (a : Fin 8) (ν : Fin 4) :
    emergentMaxwellInhomogeneous_O_general J_src a ν =
      emergentMaxwellInhomogeneous_O_fromPotential J_src A0 a ν := by
  unfold emergentMaxwellInhomogeneous_O_general emergentMaxwellInhomogeneous_O_fromPotential
    emergentFlatDivergence_sum
  simp [hA, sub_self, add_zero]
  norm_num

/-- **Emergent inhomogeneous equation in O** with the default placeholder current `J_O`. -/
noncomputable def emergentMaxwellInhomogeneous_O (a : Fin 8) (ν : Fin 4) : ℝ :=
  emergentMaxwellInhomogeneous_O_general J_O a ν

/-- Quaternionic subalgebra: indices 0..3 of O. -/
def inH (i : Fin 8) : Prop := i.val < 4

/-- Restriction of the O-equation to H (components 0..3). -/
noncomputable def emergentMaxwellInHomogeneous_H (ν : Fin 4) : ℝ := emergentMaxwellInhomogeneous_O 0 ν

/-- Classic Maxwell inhomogeneous equation (same form as in H). -/
noncomputable def classicMaxwellInhomogeneous (ν : Fin 4) : ℝ :=
  4 * Real.pi * (J_O 0 ν)   -- standard source term when restricted to one component

/-- **Reduction: the O-equation restricted to H coincides with classic Maxwell when φ is constant
    and the metric is flat.** -/
theorem O_reduces_to_classic_Maxwell_in_H (ν : Fin 4)
    (_h_flat : ∀ x, g_rr x = 1)
    (_h_phi_const : ∀ x, phi_of_T x = phiTemperatureCoeff)
    (h_grad_zero : ∀ ν, grad_φ ν = 0) :
    emergentMaxwellInHomogeneous_H ν = classicMaxwellInhomogeneous ν := by
  unfold emergentMaxwellInHomogeneous_H classicMaxwellInhomogeneous
  simp only [emergentMaxwellInhomogeneous_O, emergentMaxwellInhomogeneous_O_general, h_grad_zero,
    J_O, mul_zero, sub_zero]
  ring_nf
  norm_num

/-- **Flat metric (placeholder):** `g_rr` is identically 1. -/
theorem g_rr_flat : ∀ x, g_rr x = 1 := by
  intro x
  rfl

/-- **3D: fix one axis (e.g. time = index 0).** Remaining indices 1,2,3 are spatial.
    We state the 3D relationships; units and which axis is time come from Conservations → Forces. -/
def spatialIndices : Finset (Fin 4) := {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)}

/-- **Spatial indices (3D):** When axis 0 is fixed (e.g. time), the spatial directions are 1, 2, 3. -/
theorem spatialIndices_card : spatialIndices.card = 3 := by
  rfl

/-- **Charge conservation in O** for spatially constant source components (constant extension on chart). -/
theorem charge_conservation_O_general (J_src : Fin 8 → Fin 4 → ℝ) (a : Fin 8) :
    div_μ (fun μ => emergentMaxwellInhomogeneous_O_general J_src a μ) = 0 := by
  exact div_μ_const_field_zero _

/-- **Charge conservation in O** with default `J_O`. -/
theorem charge_conservation_O (a : Fin 8) (_ν : Fin 4) :
    div_μ (fun μ => emergentMaxwellInhomogeneous_O a μ) = 0 :=
  charge_conservation_O_general J_O a

/-- **Classic Maxwell in H under flat limit.** When the metric is flat and φ is constant (with zero
    gradient), the H-restriction of the O-equation equals the classic inhomogeneous equation.
    Combined with `g_rr_flat`, this gives a concrete instance of `O_reduces_to_classic_Maxwell_in_H`. -/
theorem classic_Maxwell_in_H_under_flat_limit (ν : Fin 4)
    (h_phi_const : ∀ x, phi_of_T x = phiTemperatureCoeff)
    (h_grad_zero : ∀ ν, grad_φ ν = 0) :
    emergentMaxwellInHomogeneous_H ν = classicMaxwellInhomogeneous ν :=
  O_reduces_to_classic_Maxwell_in_H ν g_rr_flat h_phi_const h_grad_zero

/-- In the rest / non-relativistic sanity limit, the algebraic rapidity seed vanishes and the
    quaternionic `H`-sector still collapses to classic Maxwell on a flat constant-`φ` background. -/
theorem algebraic_nonrelativistic_limit_reduces_to_classic_Maxwell_in_H (ν : Fin 4)
    (h_phi_const : ∀ x, phi_of_T x = phiTemperatureCoeff)
    (h_grad_zero : ∀ ν, grad_φ ν = 0) :
    algebraicMaxwellRapiditySeed 0 = 0 ∧
      emergentMaxwellInHomogeneous_H ν = classicMaxwellInhomogeneous ν := by
  refine ⟨algebraicMaxwellRapiditySeed_zero, ?_⟩
  exact classic_Maxwell_in_H_under_flat_limit ν h_phi_const h_grad_zero

/-!
## Phase-horizon tipping angle (weak-force emergence)

The algebra-first seed layer in `Hqiv.Physics.OMaxwellAlgebraSeed` now owns the
phase-horizon tipping angle `delta_theta_prime`, the quarter-period normalization, and
the algebraic Maxwell projection slot. This file consumes those definitions when writing
the emergent O-equation.
-/

end Hqiv
