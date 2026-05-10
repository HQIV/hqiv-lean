import Hqiv.SO8Closure

/-!
# SO(8) closure interface

Lightweight facade for downstream modules that need the SO(8) closure result
without depending on internal closure data modules directly.

Build the dedicated closure library once (`lake build HQIVSO8Closure`) so
imports of this interface reuse cached `.olean` artifacts.
-/

namespace Hqiv

/-- Interface alias for the proven SO(8) closure dimension. -/
theorem so8_closure_dim_eq_28_interface : lieClosureDim = 28 :=
  so8_closure_dim_eq_28

/-- Interface alias for the proven SO(8) closure theorem. -/
theorem so8_closure_theorem_interface :
    (∀ k : Fin 28, so8Generator k + (so8Generator k)ᵀ = 0) ∧
    (∀ i j : Fin 28, ∃ f : Fin 28 → ℝ,
      lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k) ∧
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) :=
  so8_closure_theorem

end Hqiv
