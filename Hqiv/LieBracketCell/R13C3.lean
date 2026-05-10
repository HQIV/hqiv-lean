import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

import Hqiv.Generators
import Hqiv.MatrixLieBracket
import Hqiv.GeneratorsLieClosureData

set_option maxRecDepth 100000
set_option maxHeartbeats 80000000

open Matrix BigOperators

namespace Hqiv
/-- Lie bracket closure entry (`i`=13, `j`=3). Single small proof for parallel `lake build`. -/
theorem lieBracket_in_span_r13_c3 :
    lieBracket (so8Generator ⟨13, by decide⟩) (so8Generator ⟨3, by decide⟩) =
      ∑ k : Fin 28, lieBracketCoeff ⟨13, by decide⟩ ⟨3, by decide⟩ k • so8Generator k := by
  ext a b
  simp only [lieBracket, mul_apply, sub_apply, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  fin_cases a <;> fin_cases b <;>
    norm_num (maxSteps := 5000000) [Finset.sum_range_succ, so8Generator, lieBracketCoeff,
      generator_0,
      generator_1,
      generator_2,
      generator_3,
      generator_4,
      generator_5,
      generator_6,
      generator_7,
      generator_8,
      generator_9,
      generator_10,
      generator_11,
      generator_12,
      generator_13,
      generator_14,
      generator_15,
      generator_16,
      generator_17,
      generator_18,
      generator_19,
      generator_20,
      generator_21,
      generator_22,
      generator_23,
      generator_24,
      generator_25,
      generator_26,
      generator_27]

end Hqiv
