import Hqiv.Physics.Action
import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Geometry.ContinuumSpacetimeChart
import Hqiv.Geometry.ContinuumMetricGradient
import Hqiv.Geometry.HQVMContinuumMetricBridge
import Hqiv.Geometry.SpacetimeMinkowski11Embed4

/-!
# Continuum φ-gradient closure for O-Maxwell + action

This module **closes the loop** between:

* `Hqiv.Geometry.ContinuumSpacetimeChart` (`coordsGradientComponents` from a scalar field on
  `Fin 4 → ℝ`), and
* the φ-correction slots in `emergentMaxwellInhomogeneous_O_general` (`grad_φ`) and in
  `EL_O_general` / `L_O_phi_coupling` (`grad_phi`).

**Emergent equation:** `emergentMaxwellInhomogeneous_O_coordsField` replaces `grad_φ ν` by
`coordsGradientComponents φF c ν` at a chosen basepoint `c`, keeping the same algebra-first
`alpha * algebraicMaxwellCouplingLog …` factor as `ModifiedMaxwell`.

**Action:** `L_O_phi_coupling_coords` and `EL_O_general_coordsField` use the same gradient components
with `Real.log (φ_val + 1)` (action slot) instead of `phi_of_T (T ν)` (emergent slot). Aligning those
log arguments is a separate physics identification; the **algebraic** closure is component-wise
replacement.

**1+1 null cone:** `Hqiv.Geometry.SpacetimeMinkowski11Embed4` is imported so this file is the natural
import hub for “continuum chart + embedded Minkowski slice”; see `minkowskiSq4_lift11_eq_minkowskiSq11`.

**Metric-raised φ gradient:** `*_coordsField_metric` uses `contravariantGradientComponentsAt gInvAt` from
`ContinuumMetricGradient` (inverse metric at `c`). When `gInvAt c = euclideanInv` and φ is differentiable
on the chart, these agree with the Euclidean `*_coordsField` names.

**QM/QFT bridge (same chart):** `Hqiv.Physics.LightConeMaxwellQFTBridge` ties this continuum layer to
`ContinuumManyBodyQFTScaffold` / `HorizonLimitedRenormLocality` via `LightConeFunctionalBridge`.

**HQVM constant patch:** `Hqiv.Geometry.HQVMContinuumMetricBridge` supplies `hqvmInverseMetricConst`; the
`*_hqvmConst` names below specialize `gInvAt` to frozen `HQVM_inverseMetric N a Φ` on the chart.
-/

namespace Hqiv.Physics

open BigOperators

noncomputable section

open Hqiv.Geometry

/-- Emergent O-Maxwell RHS with continuum `(∇φ)_ν` from `coordsGradientComponents φF c`. -/
noncomputable def emergentMaxwellInhomogeneous_O_coordsField (J_src : Fin 8 → Fin 4 → ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  let phiCorrection := alpha * algebraicMaxwellCouplingLog ν * coordsGradientComponents φF c ν
  (0 : ℝ) - 4 * Real.pi * J_src a ν - phiCorrection

/-- Same φ-gradient slot as the default emergent equation when components match `grad_φ`. -/
theorem emergent_coordsField_eq_general_of_grad (J_src : Fin 8 → Fin 4 → ℝ) (φF : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) (h : coordsGradientComponents φF c ν = grad_φ ν) :
    emergentMaxwellInhomogeneous_O_coordsField J_src φF c a ν =
      emergentMaxwellInhomogeneous_O_general J_src a ν := by
  unfold emergentMaxwellInhomogeneous_O_coordsField emergentMaxwellInhomogeneous_O_general
  simp_rw [h]
  norm_num

/-- Constant scalar field ⇒ zero gradient ⇒ same RHS as `emergentMaxwellInhomogeneous_O_general` with
    placeholder `grad_φ = 0`. -/
theorem emergent_coordsField_const_eq_general (J_src : Fin 8 → Fin 4 → ℝ) (r : ℝ) (c : Fin 4 → ℝ)
    (a : Fin 8) (ν : Fin 4) :
    emergentMaxwellInhomogeneous_O_coordsField J_src (fun _ : Fin 4 → ℝ => r) c a ν =
      emergentMaxwellInhomogeneous_O_general J_src a ν := by
  refine emergent_coordsField_eq_general_of_grad J_src (fun _ => r) c a ν ?_
  simp [coordsGradientComponents_const, grad_φ]

/-- Emergent RHS with `g^{νμ} ∂_μ φ` from `contravariantGradientComponentsAt gInvAt` at `c`. -/
noncomputable def emergentMaxwellInhomogeneous_O_coordsField_metric (J_src : Fin 8 → Fin 4 → ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (c : Fin 4 → ℝ) (a : Fin 8)
    (ν : Fin 4) : ℝ :=
  let phiCorrection :=
    alpha * algebraicMaxwellCouplingLog ν * contravariantGradientComponentsAt gInvAt φF c ν
  (0 : ℝ) - 4 * Real.pi * J_src a ν - phiCorrection

theorem emergent_coordsField_metric_eq_coordsField_of_euclidean (J_src : Fin 8 → Fin 4 → ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (c : Fin 4 → ℝ) (a : Fin 8)
    (ν : Fin 4)
    (hφ : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φF (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) (hg : gInvAt c = euclideanInv) :
    emergentMaxwellInhomogeneous_O_coordsField_metric J_src φF gInvAt c a ν =
      emergentMaxwellInhomogeneous_O_coordsField J_src φF c a ν := by
  unfold emergentMaxwellInhomogeneous_O_coordsField_metric emergentMaxwellInhomogeneous_O_coordsField
  simp_rw [contravariantGradientComponentsAt_euclideanInv_eq_coordsGradientComponents gInvAt φF c hφ hg]

/-- Emergent O-Maxwell with frozen HQVM inverse metric (`N`, `a`, `Φ` as in `HQVMetric`). -/
noncomputable def emergentMaxwellInhomogeneous_O_coordsField_hqvmConst (J_src : Fin 8 → Fin 4 → ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) (aIdx : Fin 8) (ν : Fin 4) : ℝ :=
  emergentMaxwellInhomogeneous_O_coordsField_metric J_src φF (hqvmInverseMetricConst N a Φ) c aIdx ν

@[simp]
theorem emergentMaxwellInhomogeneous_O_coordsField_hqvmConst_eq_metric (J_src : Fin 8 → Fin 4 → ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) (aIdx : Fin 8) (ν : Fin 4) :
    emergentMaxwellInhomogeneous_O_coordsField_hqvmConst J_src φF N a Φ c aIdx ν =
      emergentMaxwellInhomogeneous_O_coordsField_metric J_src φF (hqvmInverseMetricConst N a Φ) c aIdx ν :=
  rfl

theorem emergent_coordsField_metric_eq_of_hqvmInverseMetricConst (J_src : Fin 8 → Fin 4 → ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ)
    (aIdx : Fin 8) (ν : Fin 4) (hg : gInvAt = hqvmInverseMetricConst N a Φ) :
    emergentMaxwellInhomogeneous_O_coordsField_metric J_src φF gInvAt c aIdx ν =
      emergentMaxwellInhomogeneous_O_coordsField_hqvmConst J_src φF N a Φ c aIdx ν := by
  simp [emergentMaxwellInhomogeneous_O_coordsField_hqvmConst, hg]

/-- φ–A coupling using continuum gradient components at `c`. -/
noncomputable def L_O_phi_coupling_coords (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  alpha * Real.log (φ_val + 1) * ∑ ν : Fin 4, coordsGradientComponents φF c ν * A 0 ν

@[simp]
theorem L_O_phi_coupling_coords_const (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) :
    L_O_phi_coupling_coords A φ_val (fun _ : Fin 4 → ℝ => r) c = L_O_phi_coupling A φ_val := by
  unfold L_O_phi_coupling_coords L_O_phi_coupling
  congr 1
  refine Finset.sum_congr rfl ?_
  intro ν _
  simp [coordsGradientComponents_const, grad_phi]

noncomputable def L_O_phi_coupling_coords_metric (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  alpha * Real.log (φ_val + 1) * ∑ ν : Fin 4, contravariantGradientComponentsAt gInvAt φF c ν * A 0 ν

theorem L_O_phi_coupling_coords_metric_eq_coords_of_euclidean (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (c : Fin 4 → ℝ)
    (hφ : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φF (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) (hg : gInvAt c = euclideanInv) :
    L_O_phi_coupling_coords_metric A φ_val φF gInvAt c = L_O_phi_coupling_coords A φ_val φF c := by
  unfold L_O_phi_coupling_coords_metric L_O_phi_coupling_coords
  congr 1
  refine Finset.sum_congr rfl ?_
  intro ν _
  rw [contravariantGradientComponentsAt_euclideanInv_eq_coordsGradientComponents gInvAt φF c hφ hg]

noncomputable def L_O_phi_coupling_coords_hqvmConst (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) : ℝ :=
  L_O_phi_coupling_coords_metric A φ_val φF (hqvmInverseMetricConst N a Φ) c

@[simp]
theorem L_O_phi_coupling_coords_hqvmConst_eq_metric (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) :
    L_O_phi_coupling_coords_hqvmConst A φ_val φF N a Φ c =
      L_O_phi_coupling_coords_metric A φ_val φF (hqvmInverseMetricConst N a Φ) c :=
  rfl

theorem L_O_phi_coupling_coords_metric_const (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) :
    L_O_phi_coupling_coords_metric A φ_val (fun _ : Fin 4 → ℝ => r) (fun _ => euclideanInv) c =
      L_O_phi_coupling A φ_val := by
  refine
    (L_O_phi_coupling_coords_metric_eq_coords_of_euclidean A φ_val (fun _ => r) (fun _ => euclideanInv) c
          ?_ rfl).trans
      (L_O_phi_coupling_coords_const A φ_val r c)
  have hφ :
      DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => (fun _ : Fin 4 → ℝ => r) (spacetimeCoordsEquiv x))
        (spacetimeOfCoords c) := by
    rw [show (fun x : SpacetimeEuclidean4 => (fun _ : Fin 4 → ℝ => r) (spacetimeCoordsEquiv x)) = fun _ => r by
      funext x; rfl]
    exact differentiableAt_const r
  exact hφ

/-- Full O-Maxwell Lagrangian cell with continuum φ–A coupling. -/
noncomputable def L_O_Maxwell_general_coordsField (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  L_O_kinetic A + 4 * Real.pi * L_O_source_general J_src A + L_O_phi_coupling_coords A φ_val φF c

/-- Same as `L_O_Maxwell_general_coordsField` with metric-raised `∇φ`. -/
noncomputable def L_O_Maxwell_general_coordsField_metric (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  L_O_kinetic A + 4 * Real.pi * L_O_source_general J_src A +
    L_O_phi_coupling_coords_metric A φ_val φF gInvAt c

noncomputable def L_O_Maxwell_general_coordsField_hqvmConst (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) : ℝ :=
  L_O_Maxwell_general_coordsField_metric J_src A φ_val φF (hqvmInverseMetricConst N a Φ) c

@[simp]
theorem L_O_Maxwell_general_coordsField_hqvmConst_eq_metric (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) :
    L_O_Maxwell_general_coordsField_hqvmConst J_src A φ_val φF N a Φ c =
      L_O_Maxwell_general_coordsField_metric J_src A φ_val φF (hqvmInverseMetricConst N a Φ) c :=
  rfl

theorem L_O_Maxwell_general_coordsField_const (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) :
    L_O_Maxwell_general_coordsField J_src A φ_val (fun _ : Fin 4 → ℝ => r) c =
      L_O_Maxwell_general J_src A φ_val := by
  unfold L_O_Maxwell_general_coordsField L_O_Maxwell_general
  congr 1
  exact L_O_phi_coupling_coords_const A φ_val r c

theorem L_O_Maxwell_general_coordsField_metric_eq_coordsField_of_euclidean (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (c : Fin 4 → ℝ)
    (hφ : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φF (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) (hg : gInvAt c = euclideanInv) :
    L_O_Maxwell_general_coordsField_metric J_src A φ_val φF gInvAt c =
      L_O_Maxwell_general_coordsField J_src A φ_val φF c := by
  unfold L_O_Maxwell_general_coordsField_metric L_O_Maxwell_general_coordsField
  congr 1
  exact L_O_phi_coupling_coords_metric_eq_coords_of_euclidean A φ_val φF gInvAt c hφ hg

theorem L_O_Maxwell_general_coordsField_metric_const (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) :
    L_O_Maxwell_general_coordsField_metric J_src A φ_val (fun _ => r) (fun _ => euclideanInv) c =
      L_O_Maxwell_general J_src A φ_val := by
  unfold L_O_Maxwell_general_coordsField_metric L_O_Maxwell_general
  congr 1
  exact L_O_phi_coupling_coords_metric_const A φ_val r c

noncomputable def action_O_Maxwell_general_coordsField (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  L_O_Maxwell_general_coordsField J_src A φ_val φF c

theorem action_O_Maxwell_general_coordsField_const (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) :
    action_O_Maxwell_general_coordsField J_src A φ_val (fun _ => r) c =
      action_O_Maxwell_general J_src A φ_val := by
  unfold action_O_Maxwell_general_coordsField action_O_Maxwell_general
  exact L_O_Maxwell_general_coordsField_const J_src A φ_val r c

noncomputable def action_O_Maxwell_general_coordsField_metric (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (c : Fin 4 → ℝ) : ℝ :=
  L_O_Maxwell_general_coordsField_metric J_src A φ_val φF gInvAt c

noncomputable def action_O_Maxwell_general_coordsField_hqvmConst (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) : ℝ :=
  action_O_Maxwell_general_coordsField_metric J_src A φ_val φF (hqvmInverseMetricConst N a Φ) c

@[simp]
theorem action_O_Maxwell_general_coordsField_hqvmConst_eq_metric (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) :
    action_O_Maxwell_general_coordsField_hqvmConst J_src A φ_val φF N a Φ c =
      action_O_Maxwell_general_coordsField_metric J_src A φ_val φF (hqvmInverseMetricConst N a Φ) c :=
  rfl

theorem action_O_Maxwell_general_coordsField_metric_eq_coordsField_of_euclidean (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (c : Fin 4 → ℝ)
    (hφ : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φF (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) (hg : gInvAt c = euclideanInv) :
    action_O_Maxwell_general_coordsField_metric J_src A φ_val φF gInvAt c =
      action_O_Maxwell_general_coordsField J_src A φ_val φF c := by
  unfold action_O_Maxwell_general_coordsField_metric action_O_Maxwell_general_coordsField
  exact L_O_Maxwell_general_coordsField_metric_eq_coordsField_of_euclidean J_src A φ_val φF gInvAt c hφ hg

theorem action_O_Maxwell_general_coordsField_metric_const (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) :
    action_O_Maxwell_general_coordsField_metric J_src A φ_val (fun _ => r) (fun _ => euclideanInv) c =
      action_O_Maxwell_general J_src A φ_val := by
  unfold action_O_Maxwell_general_coordsField_metric action_O_Maxwell_general
  exact L_O_Maxwell_general_coordsField_metric_const J_src A φ_val r c

/-- Euler–Lagrange with continuum gradient in the `a = 0` channel. -/
noncomputable def EL_O_general_coordsField (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_src a ν
    - (if a = 0 then alpha * Real.log (φ_val + 1) * coordsGradientComponents φF c ν else 0)

theorem EL_O_general_coordsField_eq (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    EL_O_general_coordsField J_src A φ_val φF c a ν =
      (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_src a ν
        - (if a = 0 then alpha * Real.log (φ_val + 1) * coordsGradientComponents φF c ν else 0) := by
  rfl

theorem EL_O_general_coordsField_eq_EL_of_grad (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4)
    (h : coordsGradientComponents φF c ν = grad_phi ν) :
    EL_O_general_coordsField J_src A φ_val φF c a ν = EL_O_general J_src A φ_val a ν := by
  unfold EL_O_general_coordsField EL_O_general
  simp [F_divergence_sum, h]

theorem EL_O_general_coordsField_const (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    EL_O_general_coordsField J_src A φ_val (fun _ : Fin 4 → ℝ => r) c a ν =
      EL_O_general J_src A φ_val a ν := by
  refine EL_O_general_coordsField_eq_EL_of_grad J_src A φ_val (fun _ => r) c a ν ?_
  simp [coordsGradientComponents_const, grad_phi]

/-- Euler–Lagrange with metric-raised `∇φ` in the `a = 0` channel. -/
noncomputable def EL_O_general_coordsField_metric (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (c : Fin 4 → ℝ) (a : Fin 8)
    (ν : Fin 4) : ℝ :=
  (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_src a ν
    - (if a = 0 then alpha * Real.log (φ_val + 1) * contravariantGradientComponentsAt gInvAt φF c ν else 0)

noncomputable def EL_O_general_coordsField_hqvmConst (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) (aIdx : Fin 8) (ν : Fin 4) : ℝ :=
  EL_O_general_coordsField_metric J_src A φ_val φF (hqvmInverseMetricConst N a Φ) c aIdx ν

@[simp]
theorem EL_O_general_coordsField_hqvmConst_eq_metric (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ) (aIdx : Fin 8) (ν : Fin 4) :
    EL_O_general_coordsField_hqvmConst J_src A φ_val φF N a Φ c aIdx ν =
      EL_O_general_coordsField_metric J_src A φ_val φF (hqvmInverseMetricConst N a Φ) c aIdx ν :=
  rfl

theorem EL_O_general_coordsField_metric_eq (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (c : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    EL_O_general_coordsField_metric J_src A φ_val φF gInvAt c a ν =
      (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_src a ν
        - (if a = 0 then alpha * Real.log (φ_val + 1) * contravariantGradientComponentsAt gInvAt φF c ν
            else 0) := by
  rfl

theorem EL_O_general_coordsField_metric_eq_coordsField_of_euclidean (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (c : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4)
    (hφ : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φF (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) (hg : gInvAt c = euclideanInv) :
    EL_O_general_coordsField_metric J_src A φ_val φF gInvAt c a ν =
      EL_O_general_coordsField J_src A φ_val φF c a ν := by
  unfold EL_O_general_coordsField_metric EL_O_general_coordsField
  simp_rw [contravariantGradientComponentsAt_euclideanInv_eq_coordsGradientComponents gInvAt φF c hφ hg]

theorem EL_O_general_coordsField_metric_const (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    EL_O_general_coordsField_metric J_src A φ_val (fun _ => r) (fun _ => euclideanInv) c a ν =
      EL_O_general J_src A φ_val a ν := by
  refine (EL_O_general_coordsField_metric_eq_coordsField_of_euclidean J_src A φ_val (fun _ => r)
    (fun _ => euclideanInv) c a ν ?_ rfl).trans ?_
  · rw [show (fun x : SpacetimeEuclidean4 => (fun _ : Fin 4 → ℝ => r) (spacetimeCoordsEquiv x)) = fun _ => r by
      funext x; rfl]
    exact differentiableAt_const r
  · exact EL_O_general_coordsField_const J_src A φ_val r c a ν

noncomputable def action_total_general_coordsField (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (rho_m rho_r : ℝ) : ℝ :=
  action_O_Maxwell_general_coordsField J_src A φ_val φF c + S_HQVM_grav φ_val rho_m rho_r

theorem action_total_general_coordsField_const (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) (rho_m rho_r : ℝ) :
    action_total_general_coordsField J_src A φ_val (fun _ => r) c rho_m rho_r =
      action_total_general J_src A φ_val rho_m rho_r := by
  unfold action_total_general_coordsField action_total_general
  congr 1
  exact action_O_Maxwell_general_coordsField_const J_src A φ_val r c

noncomputable def action_total_general_coordsField_metric (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (c : Fin 4 → ℝ)
    (rho_m rho_r : ℝ) : ℝ :=
  action_O_Maxwell_general_coordsField_metric J_src A φ_val φF gInvAt c + S_HQVM_grav φ_val rho_m rho_r

theorem action_total_general_coordsField_metric_eq_coordsField_of_euclidean (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (c : Fin 4 → ℝ) (rho_m rho_r : ℝ)
    (hφ : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φF (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) (hg : gInvAt c = euclideanInv) :
    action_total_general_coordsField_metric J_src A φ_val φF gInvAt c rho_m rho_r =
      action_total_general_coordsField J_src A φ_val φF c rho_m rho_r := by
  unfold action_total_general_coordsField_metric action_total_general_coordsField
  congr 1
  exact action_O_Maxwell_general_coordsField_metric_eq_coordsField_of_euclidean J_src A φ_val φF gInvAt c hφ hg

theorem action_total_general_coordsField_metric_const (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (r : ℝ) (c : Fin 4 → ℝ) (rho_m rho_r : ℝ) :
    action_total_general_coordsField_metric J_src A φ_val (fun _ => r) (fun _ => euclideanInv) c rho_m rho_r =
      action_total_general J_src A φ_val rho_m rho_r := by
  unfold action_total_general_coordsField_metric action_total_general
  congr 1
  exact action_O_Maxwell_general_coordsField_metric_const J_src A φ_val r c

noncomputable def action_total_general_coordsField_hqvmConst (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ)
    (rho_m rho_r : ℝ) : ℝ :=
  action_total_general_coordsField_metric J_src A φ_val φF (hqvmInverseMetricConst N a Φ) c rho_m rho_r

@[simp]
theorem action_total_general_coordsField_hqvmConst_eq_metric (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (N a Φ : ℝ) (c : Fin 4 → ℝ)
    (rho_m rho_r : ℝ) :
    action_total_general_coordsField_hqvmConst J_src A φ_val φF N a Φ c rho_m rho_r =
      action_total_general_coordsField_metric J_src A φ_val φF (hqvmInverseMetricConst N a Φ) c rho_m rho_r :=
  rfl

end

end Hqiv.Physics
