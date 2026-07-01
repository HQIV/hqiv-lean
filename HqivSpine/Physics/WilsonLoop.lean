import HqivSpine.Physics.PlaquetteCurvature

/-!
# `HqivSpine.Physics.WilsonLoop` — lattice Stokes: holonomy over a tiling

A region of the lattice is **tiled** by plaquettes. Its Wilson loop is the ordered product of the
plaquette holonomies (the interior edges of a tiling are each traversed once in each direction and
cancel, leaving the boundary loop):

```
wilsonLoop [P₀, P₁, …, Pₙ₋₁] = hol P₀ · hol P₁ · ⋯ · hol Pₙ₋₁ ∈ Function.End X.
```

This is the **discrete non-abelian Stokes** layer built on `Physics.PlaquetteHolonomy` (path
concatenation is a homomorphism) and `Physics.PlaquetteCurvature` (each plaquette's holonomy is
matrix transport by its curvature):

* `wilsonLoop_append` — gluing two tilings multiplies their Wilson loops (Stokes additivity).
* `wilsonLoop_flat` — a **curvature-free** region (every plaquette trivial) has trivial Wilson loop:
  flatness propagates from plaquettes to the whole loop.
* `wilsonLoop_replicate` — `n` copies of one plaquette accumulate as `holⁿ`; the "area" `n` enters
  only through this power, the discrete seed of an area dependence.
* `wilsonLoop_curvature_obstructs_flat` — a tiling that is flat **except for one** curved
  (colour) plaquette has a **non-trivial** Wilson loop: curvature cannot be tiled away.

**Honest scope.** This is the *kinematic* discrete-Stokes identity and the flatness/obstruction
dichotomy. It is **not** a confinement area law `⟨W⟩ ∼ e^{−σ·Area}`, which is a statistical
(measure/path-integral) statement outside this algebraic layer.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.WilsonLoop

open scoped Monoid
open HqivSpine.Physics.PlaquetteHolonomy
open HqivSpine.Physics.PlaquetteCurvature

variable {X : Type*}

/-- **Wilson loop of a tiling:** the ordered product of the plaquette holonomies. -/
def wilsonLoop (plaqs : List (PlaquetteEdge X)) : Function.End X :=
  pathHolonomy (plaqs.map discreteSquareHolonomy)

@[simp]
theorem wilsonLoop_nil : wilsonLoop ([] : List (PlaquetteEdge X)) = 1 := rfl

@[simp]
theorem wilsonLoop_cons (p : PlaquetteEdge X) (ps : List (PlaquetteEdge X)) :
    wilsonLoop (p :: ps) = discreteSquareHolonomy p * wilsonLoop ps := by
  unfold wilsonLoop
  rw [List.map_cons, pathHolonomy_cons]

/-- **Discrete Stokes additivity:** gluing two tilings multiplies their Wilson loops. -/
theorem wilsonLoop_append (xs ys : List (PlaquetteEdge X)) :
    wilsonLoop (xs ++ ys) = wilsonLoop xs * wilsonLoop ys := by
  unfold wilsonLoop
  rw [List.map_append, pathHolonomy_append]

/-- **Flatness propagates:** a curvature-free region (every plaquette holonomy trivial) has a
trivial Wilson loop. -/
theorem wilsonLoop_flat (plaqs : List (PlaquetteEdge X))
    (h : ∀ p ∈ plaqs, discreteSquareHolonomy p = 1) : wilsonLoop plaqs = 1 := by
  induction plaqs with
  | nil => simp
  | cons p ps ih =>
    rw [wilsonLoop_cons, h p (List.mem_cons.mpr (Or.inl rfl)),
      ih fun q hq => h q (List.mem_cons.mpr (Or.inr hq)), one_mul]

/-- **Area accumulation:** `n` copies of one plaquette give the `n`-th power of its holonomy. -/
theorem wilsonLoop_replicate (p : PlaquetteEdge X) (n : ℕ) :
    wilsonLoop (List.replicate n p) = (discreteSquareHolonomy p) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, wilsonLoop_cons, ih, pow_succ']

/-! ## Carrier witness: curvature obstructs flatness of a tiled loop -/

/-- A curvature-free plaquette: identity transport on every edge. -/
def trivialPlaquette : PlaquetteEdge Carrier := fun _ => 1

@[simp]
theorem trivialPlaquette_holonomy : discreteSquareHolonomy trivialPlaquette = 1 :=
  discreteSquareHolonomy_one trivialPlaquette fun _ => rfl

/-- The curved colour plaquette of `PlaquetteCurvature` (the `(e₁,e₇)`/`(e₀,e₇)` commutator). -/
def colourPlaquette : PlaquetteEdge Carrier :=
  quarterEdge (quarterTurn 1 7) (quarterTurn 0 7) (quarterTurn 7 1) (quarterTurn 7 0)

/-- **A flat tiling is trivial.** -/
theorem flat_tiling_trivial :
    wilsonLoop [trivialPlaquette, trivialPlaquette, trivialPlaquette] = (1 : Function.End Carrier) := by
  simp

/-- **Curvature cannot be tiled away.** A loop that is flat everywhere except one curved colour
plaquette still has a non-trivial Wilson loop (it rotates `e₁ ↦ e₀`). -/
theorem wilsonLoop_curvature_obstructs_flat :
    wilsonLoop [trivialPlaquette, colourPlaquette, trivialPlaquette] (e 1) ≠ e 1 := by
  have hloop : wilsonLoop [trivialPlaquette, colourPlaquette, trivialPlaquette]
      = discreteSquareHolonomy colourPlaquette := by
    simp [trivialPlaquette_holonomy]
  rw [hloop]
  unfold colourPlaquette
  exact holonomy_nontrivial

/-! ## Bundled discharge -/

/-- The discharged lattice-Stokes / Wilson-loop layer: holonomy over a tiling is multiplicative
(Stokes additivity), flatness propagates from plaquettes to the loop, area enters as a power, and a
single curved plaquette obstructs flatness of the whole loop. -/
structure WilsonLoopDischarged : Prop where
  stokes_additivity :
    ∀ xs ys : List (PlaquetteEdge Carrier),
      wilsonLoop (xs ++ ys) = wilsonLoop xs * wilsonLoop ys
  flat_propagates :
    ∀ plaqs : List (PlaquetteEdge Carrier),
      (∀ p ∈ plaqs, discreteSquareHolonomy p = 1) → wilsonLoop plaqs = 1
  area_power :
    ∀ (p : PlaquetteEdge Carrier) (n : ℕ),
      wilsonLoop (List.replicate n p) = (discreteSquareHolonomy p) ^ n
  curvature_obstructs :
    wilsonLoop [trivialPlaquette, colourPlaquette, trivialPlaquette] (e 1) ≠ e 1

theorem wilsonLoopDischarged_holds : WilsonLoopDischarged where
  stokes_additivity := wilsonLoop_append
  flat_propagates := wilsonLoop_flat
  area_power := wilsonLoop_replicate
  curvature_obstructs := wilsonLoop_curvature_obstructs_flat

end HqivSpine.Physics.WilsonLoop
