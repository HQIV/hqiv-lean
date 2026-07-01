import Mathlib.Algebra.Group.End
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.PlaquetteHolonomy` — discrete gauge holonomy, cutoff-native

Finite IR/UV control means **finitely many** transports on a patch. This is the smallest algebraic
layer for a **closed discrete plaquette**: four directed edges on a `Fin 4` cycle, each carrying an
endomorphism of a type `X` (parallel transport along the edge). Transports live in `Function.End X`
(a monoid under `∘`, unit `id`), so the holonomy product is **genuinely non-commutative** once `X`
is specialized to a non-abelian transport group — the discrete seed of curvature `F = [D,D]`.

* `discreteSquareHolonomy` — the ordered plaquette product `e₀·e₁·e₂·e₃`.
* `pathHolonomy` — Wilson-line holonomy of a path (last step hits the point first).
* `pathHolonomy_append` — holonomy is a monoid homomorphism on path concatenation.
* trivial transports ⇒ trivial holonomy (the abelian/flat discrete-Stokes limit).

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.PlaquetteHolonomy

open scoped Monoid

variable {X : Type*}

/-- **Directed square:** four edges indexed by `Fin 4` in cyclic order `0 → 1 → 2 → 3 → 0`. -/
abbrev PlaquetteEdge (X : Type*) := Fin 4 → Function.End X

/-- **Holonomy** around the directed 4-cycle: ordered product `e 0 * e 1 * e 2 * e 3`. -/
def discreteSquareHolonomy (e : PlaquetteEdge X) : Function.End X :=
  e 0 * e 1 * e 2 * e 3

@[simp]
theorem discreteSquareHolonomy_one (e : PlaquetteEdge X) (h : ∀ i, e i = 1) :
    discreteSquareHolonomy e = 1 := by
  unfold discreteSquareHolonomy; simp [h]

/-- **Open-path holonomy:** transports in traversal order; `foldr` so the **last** step is applied
to the point first (Wilson-line convention). -/
def pathHolonomy (steps : List (Function.End X)) : Function.End X :=
  steps.foldr (· * ·) 1

@[simp]
theorem pathHolonomy_nil : pathHolonomy ([] : List (Function.End X)) = 1 := rfl

@[simp]
theorem pathHolonomy_cons (u : Function.End X) (us : List (Function.End X)) :
    pathHolonomy (u :: us) = u * pathHolonomy us := rfl

/-- **Holonomy is a homomorphism on concatenation:** `hol (xs ++ ys) = hol xs * hol ys`. -/
theorem pathHolonomy_append (xs ys : List (Function.End X)) :
    pathHolonomy (xs ++ ys) = pathHolonomy xs * pathHolonomy ys := by
  induction xs with
  | nil => simp
  | cons z zs ih => simp [ih, mul_assoc]

/-- A length-4 path matches the square holonomy when its entries agree edge-wise. -/
theorem discreteSquareHolonomy_eq_path (e : PlaquetteEdge X) :
    discreteSquareHolonomy e = pathHolonomy [e 0, e 1, e 2, e 3] := by
  unfold discreteSquareHolonomy pathHolonomy; simp [mul_assoc]

end HqivSpine.Physics.PlaquetteHolonomy
