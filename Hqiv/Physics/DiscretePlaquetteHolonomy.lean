import Mathlib.Algebra.Group.End
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Discrete plaquette holonomy (bottom-up, cutoff-native)

Finite **IR/UV** control in HQIV is modeled by **finitely many** degrees of freedom on a patch.
This file is the smallest algebraic layer for a **closed discrete plaquette**: four directed edges
on a `Fin 4` cycle, each carrying an endomorphism of a type `X` (transport along the edge).

We use `Function.End X` (monoid under `* = ∘`, one = `id`) so the product is **genuinely
non-commutative** when you later specialize `X` and restrict to non-abelian groups of transports.

**Not here:** embedding in `GaugeMatrix` or curvature as commutator of covariant derivatives.

**Action bridge:** `Hqiv.Physics.ActionHolonomyGlue` identifies the **abelian ℝ** cyclic plaquette built
from consecutive `F_from_A` differences with **trivial holonomy** (discrete Stokes), while
`Hqiv.Physics.Action` keeps the **full** `8 × 4 × 4` kinetic sum over the same `F` slots.

**Rapidity / continuum:** only the *discrete* patch data appear; any continuum time or rapidity
parameter enters only when you map charts (`ManifoldLagrangianScaffold`) or EL coincidence bundles,
not in this file.
-/

namespace Hqiv.Physics

open scoped Monoid

variable {X : Type*}

/-- **Directed square:** four edges indexed by `Fin 4` in cyclic order `0 → 1 → 2 → 3 → 0`
(vertices implicit; only the holonomy product is defined here). -/
abbrev PlaquetteEdge (X : Type*) :=
  Fin 4 → Function.End X

/-- **Holonomy** around the directed 4-cycle: ordered product `e 0 * e 1 * e 2 * e 3` in `End X`.

Applying to `x : X` evaluates as `((e 0) ∘ (e 1) ∘ (e 2) ∘ (e 3)) x` when read with `mul = (∘)` and
`(f * g) x = f (g x)` (second factor hits `x` first along the path). -/
def discreteSquareHolonomy (e : PlaquetteEdge X) : Function.End X :=
  e 0 * e 1 * e 2 * e 3

@[simp]
theorem discreteSquareHolonomy_one (e : PlaquetteEdge X) (h : ∀ i, e i = 1) :
    discreteSquareHolonomy e = 1 := by
  unfold discreteSquareHolonomy
  simp [h]

/-- **Open-path holonomy:** list of transports in traversal order; `foldr` so the **last** list
element is applied to `x` first (Wilson-line convention). -/
def pathHolonomy (steps : List (Function.End X)) : Function.End X :=
  steps.foldr (· * ·) 1

@[simp]
theorem pathHolonomy_nil : pathHolonomy ([] : List (Function.End X)) = 1 :=
  rfl

@[simp]
theorem pathHolonomy_cons (u : Function.End X) (us : List (Function.End X)) :
    pathHolonomy (u :: us) = u * pathHolonomy us := by
  simp [pathHolonomy, List.foldr]

theorem pathHolonomy_append (xs ys : List (Function.End X)) :
    pathHolonomy (xs ++ ys) = pathHolonomy xs * pathHolonomy ys := by
  unfold pathHolonomy
  rw [List.foldr_append]
  induction xs generalizing ys with
  | nil =>
      simp
  | cons z zs ih =>
      simp [List.foldr, mul_assoc, ih]

/-- A length-4 path matches the square holonomy when its entries agree edge-wise. -/
theorem discreteSquareHolonomy_eq_path (e : PlaquetteEdge X) :
    discreteSquareHolonomy e =
      pathHolonomy [e 0, e 1, e 2, e 3] := by
  unfold discreteSquareHolonomy pathHolonomy
  simp [List.foldr, mul_assoc]

end Hqiv.Physics
