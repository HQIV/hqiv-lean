import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

import Hqiv.GeneratorsFromAxioms
import Hqiv.Generators
import Hqiv.MatrixLieBracket

/-!
# SO(8) closure symbolic interface

This module provides a lightweight symbolic interface for downstream developments
that need the SO(8) closure facts without forcing the heavy matrix-certificate
build (`Hqiv.GeneratorsLieClosure` + `Hqiv.LieBracketCell.*`).

Use this interface for fast iterations (papers, abstract bridges, story modules).
Use `Hqiv.SO8ClosureInterface` / `HQIVSO8Closure` when you explicitly want the
full numeric/certified closure build.
-/

namespace Hqiv

/-- Symbolic SO(8) closure dimension assumption/interface. -/
axiom so8_closure_dim_eq_28_symbolic : lieClosureDim = 28

/-- Symbolic SO(8) closure theorem interface. -/
axiom so8_closure_theorem_symbolic :
    (∀ k : Fin 28, so8Generator k + Matrix.transpose (so8Generator k) = 0) ∧
    (∀ i j : Fin 28, ∃ f : Fin 28 → ℝ,
      lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k) ∧
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k)

/-- Symbolic interface: linear independence of the 28 generators. -/
theorem so8_generators_linear_independent_symbolic :
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) :=
  so8_closure_theorem_symbolic.2.2

/-- Symbolic interface: Lie bracket closure coefficients exist. -/
theorem lieBracket_in_span_symbolic (i j : Fin 28) :
    ∃ f : Fin 28 → ℝ,
      lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k :=
  so8_closure_theorem_symbolic.2.1 i j

end Hqiv
