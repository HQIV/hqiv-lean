import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Basic

open Matrix

namespace Hqiv

/-!
# Matrix Lie bracket (lightweight)

`[A, B] = A * B - B * A` for `8 × 8` real matrices. Factored out so
`GeneratorsLieClosureBracketRow*` can import this module together with `Generators`
without pulling in `OctonionicLightCone` / `GeneratorsFromAxioms`.
-/

/-- Lie bracket of 8×8 real matrices. -/
def lieBracket (A B : Matrix (Fin 8) (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  A * B - B * A

end Hqiv
