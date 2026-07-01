import HqivSpine.Geometry.ContinuumChart
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# `HqivSpine.Geometry.MetricGradient` — metric-raised gradients and divergence

Mined from legacy `ContinuumMetricGradient`, disentangled onto `ContinuumChart`. Adds
contravariant gradients `(∇φ)^ν = g^{νμ} ∂_μ φ` and coordinate divergence `∂_μ J^μ`.

Honest scope: flat **Euclidean** and **Minkowski** inverse metrics on the chart — not a
full Lorentzian volume form or HQVM Christoffel connection (those stay downstream).
-/

namespace HqivSpine.Geometry.MetricGradient

noncomputable section

open scoped BigOperators Gradient
open EuclideanSpace InnerProductSpace
open ContinuumChart

/-- Coordinate partial `∂_μ φ(c)` along the chart basis vector. -/
noncomputable def partialComponents (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  fderiv ℝ (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x)) (spacetimeOfCoords c)
    (EuclideanSpace.single μ (1 : ℝ))

/-- Contravariant gradient `(∇φ)^ν = ∑_μ g^{νμ} ∂_μ φ`. -/
noncomputable def contravariantGradientComponents (gInv : Fin 4 → Fin 4 → ℝ)
    (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun ν => ∑ μ : Fin 4, gInv ν μ * partialComponents φ c μ

/-- Position-dependent inverse metric at the chart point. -/
noncomputable def contravariantGradientComponentsAt (gInvAt : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  contravariantGradientComponents (gInvAt c) φ c

/-- Euclidean inverse metric `δ^{νμ}`. -/
noncomputable def euclideanInv (ν μ : Fin 4) : ℝ := if _ : ν = μ then 1 else 0

/-- Flat Minkowski inverse `η^{νμ}` with signature `(-,+,+,+)`. -/
noncomputable def flatMinkowskiInv (ν μ : Fin 4) : ℝ :=
  if _ : ν = μ then (if ν = (0 : Fin 4) then (-1 : ℝ) else 1) else 0

theorem spacetimeCoordsEquiv_eq_inner_single (v : SpacetimeEuclidean4) (μ : Fin 4) :
    spacetimeCoordsEquiv v μ = inner ℝ v (EuclideanSpace.single μ (1 : ℝ)) := by
  simp [spacetimeCoordsEquiv, PiLp.inner_apply, EuclideanSpace.single_apply, RCLike.inner_apply,
    Finset.sum_eq_single μ]

theorem partialComponents_eq_coordsGradientComponents (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (h : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) :
    (fun μ : Fin 4 => partialComponents φ c μ) = coordsGradientComponents φ c := by
  funext μ
  unfold partialComponents coordsGradientComponents coordsGradient spacetimeGradient
  let f := fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x)
  let x := spacetimeOfCoords c
  calc
    fderiv ℝ f x (EuclideanSpace.single μ (1 : ℝ))
        = inner ℝ (gradient f x) (EuclideanSpace.single μ (1 : ℝ)) := (inner_gradient_left h).symm
    _ = spacetimeCoordsEquiv (gradient f x) μ :=
      (spacetimeCoordsEquiv_eq_inner_single (gradient f x) μ).symm

theorem contravariantGradientComponents_euclideanInv_eq (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (h : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 => φ (spacetimeCoordsEquiv x))
      (spacetimeOfCoords c)) :
    contravariantGradientComponents euclideanInv φ c = coordsGradientComponents φ c := by
  funext ν
  simp only [contravariantGradientComponents, euclideanInv,
    partialComponents_eq_coordsGradientComponents φ c h]
  rw [Finset.sum_eq_single ν]
  · simp
  · intro μ _ hμ; simp [Ne.symm hμ]
  · simp

/-- Coordinate divergence `∂_μ J^μ`. -/
noncomputable def coordPartialDivergence (J : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, partialComponents (fun p => J p μ) c μ

theorem partialComponents_const (r : ℝ) (c : Fin 4 → ℝ) (μ : Fin 4) :
    partialComponents (fun _ : Fin 4 → ℝ => r) c μ = 0 := by
  unfold partialComponents
  have hf : (fun x : SpacetimeEuclidean4 => (fun _ : Fin 4 → ℝ => r) (spacetimeCoordsEquiv x)) =
      fun _ : SpacetimeEuclidean4 => r := rfl
  rw [hf, fderiv_const_apply r, ContinuousLinearMap.zero_apply]

theorem coordPartialDivergence_const (f : Fin 4 → ℝ) (c : Fin 4 → ℝ) :
    coordPartialDivergence (fun _ => f) c = 0 := by
  unfold coordPartialDivergence
  refine Finset.sum_eq_zero fun μ _ => partialComponents_const (f μ) c μ

theorem contravariantGradientComponents_flatMinkowskiInv_time (φ : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) (h : DifferentiableAt ℝ (fun x : SpacetimeEuclidean4 =>
      φ (spacetimeCoordsEquiv x)) (spacetimeOfCoords c)) :
    contravariantGradientComponents flatMinkowskiInv φ c 0 =
      -partialComponents φ c 0 := by
  simp only [contravariantGradientComponents, flatMinkowskiInv,
    partialComponents_eq_coordsGradientComponents φ c h]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro μ _ hμ; simp [Ne.symm hμ]
  · simp

end

end HqivSpine.Geometry.MetricGradient
