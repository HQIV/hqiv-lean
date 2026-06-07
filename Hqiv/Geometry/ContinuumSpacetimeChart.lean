import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Continuum chart for 4D HQIV spacetime indices (`Fin 4`)

`Hqiv.Physics.Action` and `Hqiv.Physics.ModifiedMaxwell` index spacetime by `Fin 4 → ℝ` (coordinate
functions). This file installs the **standard Euclidean structure** on the same four-tuple via
`EuclideanSpace ℝ (Fin 4)` so Mathlib’s **Fréchet gradient** and **coordinate divergence** are
well-typed.

This is **flat Riemannian geometry on ℝ⁴** (one chart = whole space). It is **not** the HQVM
Lorentzian line element from `HQVMetric` and **not** the discrete null-lattice embedding discussed
in `HQVMMinkowskiSubstrate`; those are separate layers. Here the goal is a **computable continuum
calculus** hook for φ and vector fields before adding a metric volume factor or covariant derivative.

**Main definitions**
* `SpacetimeEuclidean4` — model space with `InnerProductSpace ℝ` and `CompleteSpace`.
* `spacetimeCoordsEquiv` — `≃L[ℝ]` with bare `Fin 4 → ℝ` (same as `EuclideanSpace.equiv`).
* `spacetimeGradient` — Mathlib `gradient` (scoped notation `∇` in proofs).
* `coordsGradient` / `coordsGradientComponents` — scalar fields on `Fin 4 → ℝ` pulled back to the chart.
* `spacetimeCoordDivergence` — `∑_μ ∂_μ V^μ` at a point via `fderiv` along `EuclideanSpace.single μ 1`.

**Physics use:** `Hqiv.Physics.ContinuumOmaxwellClosure` feeds `coordsGradientComponents` into the emergent
O-Maxwell φ slot and the action / EL φ-coupling alongside the plasma bridge when `J_src` is instantiated.

**Metric raise:** `Hqiv.Geometry.ContinuumMetricGradient` defines coordinate `partialComponents` and
`contravariantGradientComponents gInv`; with `euclideanInv` this agrees with `coordsGradientComponents`
where the scalar is differentiable (see `contravariantGradientComponents_euclideanInv_eq`). The same file
has `coordCovariantDivergence` / `coordCovariantDivergence_constDet` for `∇_μ J^μ` with metric determinant
weighting.

**Spatial slice embed:** `Hqiv.Geometry.SpatialSliceContinuumBridge` relates `spatialSliceToSpacetimeCoords`
to `spacetimeCoordsEquiv` / `spacetimeOfCoords` and records thin-slice membership (`mem_spacetimeThinSlice_iff`).
-/

namespace Hqiv.Geometry

noncomputable section

open scoped BigOperators Gradient
open EuclideanSpace InnerProductSpace

/-- Flat four-dimensional model space with the standard `l²` inner product. -/
abbrev SpacetimeEuclidean4 : Type :=
  EuclideanSpace ℝ (Fin 4)

/-- Linear isometry between `SpacetimeEuclidean4` and raw coordinates `Fin 4 → ℝ`
(same indexing as the physics modules). -/
noncomputable abbrev spacetimeCoordsEquiv : SpacetimeEuclidean4 ≃L[ℝ] Fin 4 → ℝ :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)

/-- Embed a coordinate tuple into the Euclidean chart. -/
noncomputable abbrev spacetimeOfCoords (c : Fin 4 → ℝ) : SpacetimeEuclidean4 :=
  spacetimeCoordsEquiv.symm c

/-- Euclidean gradient of `f : SpacetimeEuclidean4 → ℝ` at `x`. -/
noncomputable abbrev spacetimeGradient (f : SpacetimeEuclidean4 → ℝ) (x : SpacetimeEuclidean4) :
    SpacetimeEuclidean4 :=
  gradient f x

/-- Gradient of a scalar field presented in coordinate form `φ : (Fin 4 → ℝ) → ℝ`. -/
noncomputable def coordsGradient (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : SpacetimeEuclidean4 :=
  spacetimeGradient (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x)) (spacetimeOfCoords c)

/-- `Fin 4 → ℝ` components of `coordsGradient φ c` (drop-in style for discrete slots). -/
noncomputable def coordsGradientComponents (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  spacetimeCoordsEquiv (coordsGradient φ c)

/-- Coordinate divergence `∑_μ ∂_μ V^μ` at `x` for a vector field on the chart. -/
noncomputable def spacetimeCoordDivergence (V : SpacetimeEuclidean4 → SpacetimeEuclidean4)
    (x : SpacetimeEuclidean4) : ℝ :=
  ∑ μ : Fin 4,
    fderiv ℝ (fun y : SpacetimeEuclidean4 => V y μ) x (EuclideanSpace.single μ (1 : ℝ))

/-- Vector field on the chart induced by `V : (Fin 4 → ℝ) → Fin 4 → ℝ`. -/
noncomputable def spacetimeVectorFieldFromCoords (V : (Fin 4 → ℝ) → Fin 4 → ℝ) :
    SpacetimeEuclidean4 → SpacetimeEuclidean4 :=
  fun x => spacetimeOfCoords (V (spacetimeCoordsEquiv x))

/-- Divergence of a coordinate vector field at `c : Fin 4 → ℝ`. -/
noncomputable def coordsDivergence (V : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  spacetimeCoordDivergence (spacetimeVectorFieldFromCoords V) (spacetimeOfCoords c)

/-!
## Elementary lemmas
-/

theorem spacetimeGradient_const (c : ℝ) (x : SpacetimeEuclidean4) :
    spacetimeGradient (fun _ : SpacetimeEuclidean4 => c) x = 0 :=
  gradient_fun_const x c

theorem coordsGradient_const (r : ℝ) (c : Fin 4 → ℝ) : coordsGradient (fun _ : Fin 4 → ℝ => r) c = 0 := by
  unfold coordsGradient spacetimeGradient
  have h :
      (fun x : SpacetimeEuclidean4 => (fun _ : Fin 4 → ℝ => r) (spacetimeCoordsEquiv x)) =
        fun _ : SpacetimeEuclidean4 => r := by
    funext x
    rfl
  rw [h]
  exact gradient_fun_const (spacetimeOfCoords c) r

theorem coordsGradientComponents_const (r : ℝ) (c : Fin 4 → ℝ) :
    coordsGradientComponents (fun _ : Fin 4 → ℝ => r) c = 0 := by
  unfold coordsGradientComponents
  rw [coordsGradient_const]
  simp

theorem spacetimeCoordDivergence_zero (x : SpacetimeEuclidean4) :
    spacetimeCoordDivergence (fun _ : SpacetimeEuclidean4 => (0 : SpacetimeEuclidean4)) x = 0 := by
  unfold spacetimeCoordDivergence
  refine Finset.sum_eq_zero ?_
  intro μ _
  have hf :
      (fun y : SpacetimeEuclidean4 => (0 : SpacetimeEuclidean4) μ) =
        fun _ : SpacetimeEuclidean4 => (0 : ℝ) := by
    funext y
    simp [PiLp.zero_apply]
  rw [hf, fderiv_const_apply (0 : ℝ)]
  simp

theorem coordsDivergence_zero (c : Fin 4 → ℝ) :
    coordsDivergence (fun _ : Fin 4 → ℝ => (0 : Fin 4 → ℝ)) c = 0 := by
  have hV :
      spacetimeVectorFieldFromCoords (fun _ : Fin 4 → ℝ => (0 : Fin 4 → ℝ)) =
        fun _ : SpacetimeEuclidean4 => (0 : SpacetimeEuclidean4) := by
    funext x
    simp [spacetimeVectorFieldFromCoords, spacetimeOfCoords, map_zero]
  simp [coordsDivergence, hV, spacetimeCoordDivergence_zero]

theorem coordsDivergence_const (f : Fin 4 → ℝ) (c : Fin 4 → ℝ) :
    coordsDivergence (fun _ => f) c = 0 := by
  have hV :
      spacetimeVectorFieldFromCoords (fun _ : Fin 4 → ℝ => f) =
        fun _ : SpacetimeEuclidean4 => spacetimeOfCoords f := by
    funext x
    simp [spacetimeVectorFieldFromCoords, spacetimeOfCoords]
  rw [coordsDivergence, hV, spacetimeCoordDivergence]
  refine Finset.sum_eq_zero ?_
  intro μ _
  have hf :
      (fun y : SpacetimeEuclidean4 => (spacetimeOfCoords f) μ) = fun _ : SpacetimeEuclidean4 => f μ := by
    funext y
    simp [spacetimeOfCoords]
  rw [hf, fderiv_const_apply (f μ)]
  simp

end

end Hqiv.Geometry
