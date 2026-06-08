import Hqiv.GeneratorsLieClosure
import Hqiv.GeneratorsFromAxioms

/-!
# SO(8) closure — re-export from generator package

The full proof (28 generators antisymmetric, closed under Lie bracket, linearly independent)
lives in Hqiv.GeneratorsLieClosure. This module re-exports the theorem and the dimension.
-/

namespace Hqiv

/-- **SO(8) closure dimension:** the Lie closure from octonion generators has dimension 28. -/
theorem so8_closure_dim_eq_28 : lieClosureDim = 28 :=
  lieClosureDim_eq_so8GeneratorCount.trans rfl

/-- **SO(8) closure theorem** (from GeneratorsLieClosure): the 28 generators are
    antisymmetric, closed under Lie bracket, and linearly independent — a basis for so(8). -/
theorem so8_closure_theorem :
    (∀ k : Fin 28, so8Generator k + (so8Generator k)ᵀ = 0) ∧
    (∀ i j : Fin 28, ∃ f : Fin 28 → ℝ,
      lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k) ∧
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) :=
  generators_from_octonion_closure_theorem

end Hqiv
