import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.KochenSpecker` — quantum contextuality (Cabello 18-vector KS set)

The **contextuality** counterpart of `Physics.GleasonBorn`. Gleason's representable direction says
density operators give frame functions; `GleasonBorn.gleason_fails_in_dim_two` shows that without
`dim ≥ 3` the trace rule is *not* forced. The complementary impossibility, valid from `dim = 4`
upward, is the **Bell–Kochen–Specker theorem**: there is no *noncontextual* `{0,1}` value
assignment to quantum projectors at all — definite "yes/no" answers cannot be handed out to every
ray independently of the measurement context.

We formalise the **minimal known KS set**: the 18 four-dimensional rays of Cabello, Estebaranz and
García-Alcaine (*Phys. Lett. A* **212**, 183 (1996)), arranged into 9 orthogonal bases with each
ray in exactly two of them.

* `contexts_orthogonal`, `rays_nonzero` — the 9 contexts are genuine orthogonal bases of `ℝ⁴`
  (pairwise inner products vanish, every ray is nonzero), verified by `decide` on the integer
  coordinates. So "exactly one true ray per context" is the legitimate noncontextual constraint.
* `contexts_cover` — each of the 18 rays lies in exactly two contexts (the incidence that drives
  the parity argument).
* **`no_noncontextual_assignment`** — there is no `Assignment : Fin 18 → Bool` making each context
  hold exactly one true ray. Proof by parity: nine "exactly one" constraints sum to `9` (odd), but
  every ray is counted twice, so the same total is `2·(#true)` (even). Contradiction.

This is **state-independent** contextuality: the obstruction is in the orthogonality structure, not
any chosen state. Honest scope: the parity proof needs the even incidence of the `dim = 4` CEG set;
the minimal `dim = 3` KS set (Conway–Kochen, 31 rays) has no parity proof and is left as future
work. The full analytic Gleason converse (every frame function `= tr(ρ·)` for `dim ≥ 3`) likewise
remains cited, not formalised.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.KochenSpecker

/-- The 18 Cabello–Estebaranz–García rays in `ℝ⁴`, with integer coordinates. -/
def V : Fin 18 → Fin 4 → ℤ :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![1, 1, 0, 0], ![1, -1, 0, 0],
    ![0, 1, 0, 0], ![1, 0, 1, 0], ![1, 0, -1, 0], ![1, -1, 1, -1],
    ![1, -1, -1, 1], ![0, 0, 1, 1], ![1, 1, 1, 1], ![0, 1, 0, -1],
    ![1, 0, 0, 1], ![1, 0, 0, -1], ![0, 1, -1, 0], ![1, 1, -1, 1],
    ![1, 1, 1, -1], ![-1, 1, 1, 1]]

/-- Euclidean inner product on `ℤ⁴`. -/
def dotZ (a b : Fin 4 → ℤ) : ℤ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3

/-- The 9 orthogonal contexts (complete bases), as index lists into `V`. Each of the 18 rays
occurs in exactly two contexts. -/
def contexts : List (List (Fin 18)) :=
  [[0, 1, 2, 3], [0, 4, 5, 6], [7, 8, 2, 9], [7, 10, 6, 11], [1, 4, 12, 13],
   [8, 10, 13, 14], [15, 16, 3, 9], [15, 17, 5, 11], [16, 17, 12, 14]]

/-- **Certificate 1.** Every context consists of pairwise-orthogonal rays in `ℝ⁴`. -/
theorem contexts_orthogonal :
    ∀ ctx ∈ contexts, ∀ i ∈ ctx, ∀ j ∈ ctx, i ≠ j → dotZ (V i) (V j) = 0 := by decide

/-- **Certificate 2.** Every ray is nonzero (positive squared norm), so each context is a genuine
orthogonal basis of `ℝ⁴`. -/
theorem rays_nonzero : ∀ v : Fin 18, dotZ (V v) (V v) ≠ 0 := by decide

/-- **Certificate 3.** Each of the 18 rays appears in exactly two of the nine contexts — the even
incidence that powers the parity contradiction. -/
theorem contexts_cover :
    ∀ v : Fin 18, (contexts.filter (fun ctx => v ∈ ctx)).length = 2 := by decide

/-- A noncontextual value assignment: a definite `Bool` truth value for each of the 18 rays. -/
abbrev Assignment : Type := Fin 18 → Bool

/-- The `{0,1}` numeric value of a ray under an assignment. -/
def val (a : Assignment) (v : Fin 18) : ℕ := if a v then 1 else 0

/-- KS consistency: in every orthogonal context exactly one ray is assigned "true". -/
def Consistent (a : Assignment) : Prop :=
  ∀ ctx ∈ contexts, (ctx.map (val a)).sum = 1

/-- **Bell–Kochen–Specker contextuality (Cabello–Estebaranz–García, 18 vectors).** No
noncontextual `{0,1}` value assignment to the 18 rays can select exactly one true ray in each of
the nine orthogonal contexts. Quantum mechanics admits **no** noncontextual hidden-variable value
assignment: definite outcomes cannot be handed to all projectors independently of context.

Proof (parity): summing the nine "exactly one true" constraints totals `9`; but each ray lies in
exactly two contexts (`contexts_cover`), so the same total equals `2·(#true rays)`, an even
number — and `9` is odd. -/
theorem no_noncontextual_assignment : ¬ ∃ a : Assignment, Consistent a := by
  rintro ⟨a, h⟩
  simp only [Consistent, contexts, List.forall_mem_cons,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  omega

end HqivSpine.Physics.KochenSpecker
