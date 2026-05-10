import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

/-!
# Lagrangian density on an arbitrary manifold (anchor parallel to rapidity)

`SpatialSliceRapidityScaffold` fixes **abstract** spatial types `M` with `[TopologicalSpace M]` and
builds rapidity / shell / contour probes without choosing a metric tensor. This file does the same
at the **type** level for densities: the carrier `M` is any type (no topology required until you add
charts with continuity or measures for integration). The object is a **local Lagrangian density**
`ℒ : M → ℝ` — the standard starting point before fixing a measure for `∫ ℒ dμ` or a variational
principle.

**Parallel to rapidity**

* `AuxiliaryScalarField M` (`M → ℝ`) already names continuum scalars on `M`.
* `LagrangianDensity M` is **definitionally** the same type — we alias it for semantic clarity when
  the scalar is intended as an **integrand** for an action functional.
* Chart pullbacks `lagrangianFromChart` transport a coordinate Lagrangian `(Fin d → ℝ) → ℝ` to `M`,
  analogous to embedding polar data via `RapiditiesPolarSliceTarget.polarToSlice`.

**Relation to `Hqiv.Physics.Action`**

The O-Maxwell **number** `L_O_Maxwell … : ℝ` is a single cell / summed index value. A continuum story
chooses a chart `chart : M → (Fin 4 → ℝ)` and fields `A`, `φ` on spacetime, then sets
`ℒ(x) := L_cell (A(chart x))` — **not** formalized as a theorem here; this module only supplies the
type-level anchor and pullback.

**Not here:** smoothness, `Measure M`, `∫ ℒ dμ`, Euler–Lagrange on manifolds, or equivalence with
discrete HQIV index sums — those are separate hypotheses or future work.
-/

namespace Hqiv.Geometry

variable {M : Type u} {N : Type v}

/-- **Lagrangian density** as a real scalar field on `M` (integrand for an action before a measure is
chosen). Definitionally `M → ℝ` — the same underlying type as `AuxiliaryScalarField` in
`SpatialSliceRapidityScaffold` (no import here to keep this file lightweight). -/
abbrev LagrangianDensity (M : Type u) : Type u :=
  M → ℝ

/-- Pull back a density along any map `f : N → M` (change of variables / restriction to subregion). -/
def pullbackLagrangianDensity (L : LagrangianDensity M) (f : N → M) : LagrangianDensity N :=
  L ∘ f

@[simp]
theorem pullbackLagrangianDensity_apply (L : LagrangianDensity M) (f : N → M) (y : N) :
    pullbackLagrangianDensity L f y = L (f y) :=
  rfl

/-- Constant density `ℒ ≡ c`. -/
def constantLagrangianDensity (c : ℝ) : LagrangianDensity M := fun _ => c

@[simp]
theorem constantLagrangianDensity_apply (c : ℝ) (x : M) : constantLagrangianDensity c x = c :=
  rfl

/-- Pull back a **coordinate** Lagrangian `Λ : (Fin d → ℝ) → ℝ` along a chart `chart : M → (Fin d → ℝ)`. -/
def lagrangianFromChart {d : ℕ} (Λ : (Fin d → ℝ) → ℝ) (chart : M → (Fin d → ℝ)) : LagrangianDensity M :=
  fun x => Λ (chart x)

@[simp]
theorem lagrangianFromChart_apply {d : ℕ} (Λ : (Fin d → ℝ) → ℝ) (chart : M → (Fin d → ℝ)) (x : M) :
    lagrangianFromChart Λ chart x = Λ (chart x) :=
  rfl

/-- Pullback commutes with precomposition: `lagrangianFromChart Λ (chart ∘ f) = pullback … (lagrangianFromChart …)`. -/
theorem lagrangianFromChart_comp {d : ℕ} (Λ : (Fin d → ℝ) → ℝ) (chart : M → (Fin d → ℝ)) (f : N → M) :
    lagrangianFromChart Λ (chart ∘ f) = pullbackLagrangianDensity (lagrangianFromChart Λ chart) f :=
  rfl

/-!
### Discrete ↔ continuum coincidence (hypothesis bundle)

Same pattern as `LatticeContinuumRapidityCoincidence`: a **declared** agreement between a number from a
lattice/cell sum and a continuum surrogate (here: a single real value standing in for `∫ ℒ` or a
local evaluation).
-/

/-- Hypothesis: a discrete action proxy (e.g. finite sum over indices) equals a continuum value. -/
structure LatticeContinuumActionCoincidence where
  discreteProxy : ℝ
  continuumProxy : ℝ
  discrete_eq_continuum : discreteProxy = continuumProxy

/-- Diagonal instance. -/
def LatticeContinuumActionCoincidence.refl (r : ℝ) : LatticeContinuumActionCoincidence where
  discreteProxy := r
  continuumProxy := r
  discrete_eq_continuum := rfl

end Hqiv.Geometry
