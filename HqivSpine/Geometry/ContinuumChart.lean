import HqivSpine.Foundation.ThreeGrowth
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# `HqivSpine.Geometry.ContinuumChart` — flat `ℝ⁴` continuum calculus hook

The discrete physics layer indexes spacetime by `Fin 4 → ℝ` (`spacetimeDim = transverseDim + 1 = 4`).
This module installs the **standard Euclidean structure** on the same four-tuple via
`EuclideanSpace ℝ (Fin 4)`, so Mathlib's Fréchet **gradient** and **coordinate divergence** become
well-typed continuum operators that can be pulled back onto the discrete coordinate slots.

This is flat Riemannian calculus on `ℝ⁴` (one chart = whole space) — a *computable continuum
calculus* hook for scalar fields `φ` and vector fields before any metric volume factor or covariant
derivative. It is deliberately **not** a Lorentzian line element and not the null-lattice embedding;
those are separate layers. The elementary lemmas (gradient/divergence of constants vanish) certify
the hook is wired correctly.

Mathlib + foundation only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Geometry.ContinuumChart

noncomputable section

open scoped BigOperators Gradient
open EuclideanSpace InnerProductSpace HqivSpine.Foundation

/-- The continuum chart has `spacetimeDim = 4` coordinates. -/
theorem chart_dim : spacetimeDim = 4 := rfl

/-- Flat four-dimensional model space with the standard `ℓ²` inner product. -/
abbrev SpacetimeEuclidean4 : Type := EuclideanSpace ℝ (Fin 4)

/-- Linear isometry between the chart and raw coordinates `Fin 4 → ℝ` (the physics indexing). -/
noncomputable abbrev spacetimeCoordsEquiv : SpacetimeEuclidean4 ≃L[ℝ] Fin 4 → ℝ :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)

/-- Embed a coordinate tuple into the Euclidean chart. -/
noncomputable abbrev spacetimeOfCoords (c : Fin 4 → ℝ) : SpacetimeEuclidean4 :=
  spacetimeCoordsEquiv.symm c

/-- Euclidean gradient of `f` at `x`. -/
noncomputable abbrev spacetimeGradient (f : SpacetimeEuclidean4 → ℝ) (x : SpacetimeEuclidean4) :
    SpacetimeEuclidean4 :=
  gradient f x

/-- Gradient of a scalar field presented in coordinate form `φ : (Fin 4 → ℝ) → ℝ`. -/
noncomputable def coordsGradient (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : SpacetimeEuclidean4 :=
  spacetimeGradient (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x)) (spacetimeOfCoords c)

/-- `Fin 4 → ℝ` components of `coordsGradient φ c` (drop-in for the discrete slots). -/
noncomputable def coordsGradientComponents (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  spacetimeCoordsEquiv (coordsGradient φ c)

/-- Coordinate divergence `∑_μ ∂_μ V^μ` at `x` for a chart vector field. -/
noncomputable def spacetimeCoordDivergence (V : SpacetimeEuclidean4 → SpacetimeEuclidean4)
    (x : SpacetimeEuclidean4) : ℝ :=
  ∑ μ : Fin 4,
    fderiv ℝ (fun y : SpacetimeEuclidean4 => V y μ) x (EuclideanSpace.single μ (1 : ℝ))

/-- Chart vector field induced by `V : (Fin 4 → ℝ) → Fin 4 → ℝ`. -/
noncomputable def spacetimeVectorFieldFromCoords (V : (Fin 4 → ℝ) → Fin 4 → ℝ) :
    SpacetimeEuclidean4 → SpacetimeEuclidean4 :=
  fun x => spacetimeOfCoords (V (spacetimeCoordsEquiv x))

/-- Divergence of a coordinate vector field at `c : Fin 4 → ℝ`. -/
noncomputable def coordsDivergence (V : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  spacetimeCoordDivergence (spacetimeVectorFieldFromCoords V) (spacetimeOfCoords c)

/-! ## Elementary lemmas (the hook is wired correctly: constants are flat) -/

theorem spacetimeGradient_const (c : ℝ) (x : SpacetimeEuclidean4) :
    spacetimeGradient (fun _ : SpacetimeEuclidean4 => c) x = 0 :=
  gradient_fun_const x c

theorem coordsGradient_const (r : ℝ) (c : Fin 4 → ℝ) :
    coordsGradient (fun _ : Fin 4 → ℝ => r) c = 0 :=
  gradient_fun_const (spacetimeOfCoords c) r

theorem coordsGradientComponents_const (r : ℝ) (c : Fin 4 → ℝ) :
    coordsGradientComponents (fun _ : Fin 4 → ℝ => r) c = 0 := by
  unfold coordsGradientComponents; rw [coordsGradient_const]; simp

theorem spacetimeCoordDivergence_zero (x : SpacetimeEuclidean4) :
    spacetimeCoordDivergence (fun _ : SpacetimeEuclidean4 => (0 : SpacetimeEuclidean4)) x = 0 := by
  refine Finset.sum_eq_zero fun μ _ => ?_
  have hf : (fun y : SpacetimeEuclidean4 => (0 : SpacetimeEuclidean4) μ) =
      fun _ : SpacetimeEuclidean4 => (0 : ℝ) := by funext y; simp [PiLp.zero_apply]
  rw [hf, fderiv_const_apply (0 : ℝ)]; simp

theorem coordsDivergence_const (f : Fin 4 → ℝ) (c : Fin 4 → ℝ) :
    coordsDivergence (fun _ => f) c = 0 := by
  have hV : spacetimeVectorFieldFromCoords (fun _ : Fin 4 → ℝ => f) =
      fun _ : SpacetimeEuclidean4 => spacetimeOfCoords f := by
    funext x; simp [spacetimeVectorFieldFromCoords, spacetimeOfCoords]
  rw [coordsDivergence, hV, spacetimeCoordDivergence]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have hf : (fun y : SpacetimeEuclidean4 => (spacetimeOfCoords f) μ) =
      fun _ : SpacetimeEuclidean4 => f μ := by funext y; simp [spacetimeOfCoords]
  rw [hf, fderiv_const_apply (f μ)]; simp

theorem coordsDivergence_zero (c : Fin 4 → ℝ) :
    coordsDivergence (fun _ : Fin 4 → ℝ => (0 : Fin 4 → ℝ)) c = 0 :=
  coordsDivergence_const 0 c

end

end HqivSpine.Geometry.ContinuumChart
