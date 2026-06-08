import Hqiv.GeneratorsFromAxioms
import Hqiv.SO8ClosureSymbolic

/-!
# Octonion SO(8) Lie DOF — Story anchor

The YM / Millennium **Story** line (`CompactSimpleGaugeGroup G`, `QuantumYangMillsTheory G`, …) is a
**continuum QFT** interface. Separately, HQIV’s **octonion→matrix** construction supplies a
**finite-dimensional Lie certificate**: 28 `Hqiv.so8Generator` matrices that are antisymmetric, **closed
under the matrix Lie bracket** in their span, and **linearly independent** — a concrete realisation of
`so(8)`-sized **algebraic** degrees of freedom (28 real parameters).

**Story / CI default:** this module re-exports the **symbolic** SO(8) closure interface
(`Hqiv.SO8ClosureSymbolic`) so `lake build HQIVStory` does not compose the heavy matrix certificate
(`Hqiv.GeneratorsLieClosure` + `Hqiv.LieBracketCell.*`). For the certified closure build use
`Hqiv.SO8ClosureInterface` / `lake build HQIVSO8Closure`.

**QFT-facing lightweight feed (no closure import):** `Hqiv.Story.HQIVQFTLieAlgebraFeed` (imported by
`QuantumYangMillsFromPatchHQIV`) packages skew-adjointness of `so8Generator` / `phaseLiftDelta` and
`lieClosureDim = 28` from `GeneratorsFromAxioms` alone; use this when you want matrix consequences
next to the Dojo interface without composing the Lie-closure proof graph.

- **`octonion_so8_lie_dim`:** definitional, `Hqiv.lieClosureDim` is `28` in `Hqiv.GeneratorsFromAxioms`.

- **`octonion_so8_lie_backbone`:** matches `Hqiv.so8_closure_theorem` / `_interface` (up to
  `Matrix.transpose` vs `ᵀ`).

This module remains the Story-level hook: the `HQIVStory` spine is not *only* the small `S₃` sketch in
`GaugeGroupFromHQIVSketch` — that file exists *only* to feed a concrete `G` into abstract Millennium
**bridge** code.
-/

namespace Hqiv.Story

open Hqiv
open BigOperators
open Matrix

/-- **28** = `lieClosureDim`: the octonion-derived construction is *specified* to match real `so(8)` (dim 28). -/
theorem octonion_so8_lie_dim : lieClosureDim = 28 :=
  rfl

/-- **Lie backbone:** antisymmetry, bracket closure in the generator span, linear independence — the same
statement as `Hqiv.so8_closure_theorem_interface` with `transpose` instead of `ᵀ`. -/
theorem octonion_so8_lie_backbone :
    (∀ k : Fin 28, so8Generator k + transpose (so8Generator k) = 0) ∧
    (∀ i j : Fin 28, ∃ f : Fin 28 → ℝ,
      lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k) ∧
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) := by
  have ⟨hanti, hbracket, hli⟩ := Hqiv.so8_closure_theorem_symbolic
  exact And.intro
    (fun k => by simpa [Matrix.transpose] using hanti k) (And.intro hbracket hli)

end Hqiv.Story
