import Hqiv.Generators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 40000000

open Matrix BigOperators

namespace Hqiv

/-- Upper-triangle index: p-th pair (i,j) with i < j in lex order (0,1)..(0,7),(1,2)..(6,7). -/
def upperTriangleIdx (p : Fin 28) : Fin 8 × Fin 8 :=
  if p.val = 0 then ((0 : Fin 8), (1 : Fin 8))
  else if p.val = 1 then ((0 : Fin 8), (2 : Fin 8))
  else if p.val = 2 then ((0 : Fin 8), (3 : Fin 8))
  else if p.val = 3 then ((0 : Fin 8), (4 : Fin 8))
  else if p.val = 4 then ((0 : Fin 8), (5 : Fin 8))
  else if p.val = 5 then ((0 : Fin 8), (6 : Fin 8))
  else if p.val = 6 then ((0 : Fin 8), (7 : Fin 8))
  else if p.val = 7 then ((1 : Fin 8), (2 : Fin 8))
  else if p.val = 8 then ((1 : Fin 8), (3 : Fin 8))
  else if p.val = 9 then ((1 : Fin 8), (4 : Fin 8))
  else if p.val = 10 then ((1 : Fin 8), (5 : Fin 8))
  else if p.val = 11 then ((1 : Fin 8), (6 : Fin 8))
  else if p.val = 12 then ((1 : Fin 8), (7 : Fin 8))
  else if p.val = 13 then ((2 : Fin 8), (3 : Fin 8))
  else if p.val = 14 then ((2 : Fin 8), (4 : Fin 8))
  else if p.val = 15 then ((2 : Fin 8), (5 : Fin 8))
  else if p.val = 16 then ((2 : Fin 8), (6 : Fin 8))
  else if p.val = 17 then ((2 : Fin 8), (7 : Fin 8))
  else if p.val = 18 then ((3 : Fin 8), (4 : Fin 8))
  else if p.val = 19 then ((3 : Fin 8), (5 : Fin 8))
  else if p.val = 20 then ((3 : Fin 8), (6 : Fin 8))
  else if p.val = 21 then ((3 : Fin 8), (7 : Fin 8))
  else if p.val = 22 then ((4 : Fin 8), (5 : Fin 8))
  else if p.val = 23 then ((4 : Fin 8), (6 : Fin 8))
  else if p.val = 24 then ((4 : Fin 8), (7 : Fin 8))
  else if p.val = 25 then ((5 : Fin 8), (6 : Fin 8))
  else if p.val = 26 then ((5 : Fin 8), (7 : Fin 8))
  else if p.val = 27 then ((6 : Fin 8), (7 : Fin 8))
  else ((6 : Fin 8), (7 : Fin 8))  -- unreachable: p.val ∈ {0..27} for p : Fin 28

/-- 28×28 matrix of upper-triangle coordinates: so8CoordMatrix p k = (so8Generator k) at p-th (i,j) with i<j.
Lex order (0,1)..(0,7),(1,2)..(6,7). Derived from so8Generator and upperTriangleIdx. -/
def so8CoordMatrix : Matrix (Fin 28) (Fin 28) ℝ :=
  Matrix.of (fun p k => (so8Generator k) (upperTriangleIdx p).1 (upperTriangleIdx p).2)

@[simp]
theorem so8CoordMatrix_eq_coord (p k : Fin 28) :
    so8CoordMatrix p k = (so8Generator k) (upperTriangleIdx p).1 (upperTriangleIdx p).2 :=
  rfl

/-- Extract the p-th upper-triangle coordinate of an 8×8 matrix (same order as so8CoordMatrix). -/
def coordVec (M : Matrix (Fin 8) (Fin 8) ℝ) (p : Fin 28) : ℝ :=
  M (upperTriangleIdx p).1 (upperTriangleIdx p).2

/-- **Columns of so8CoordMatrix are orthonormal:** Mᵀ * M = 1 (28×28 identity).
So det(so8CoordMatrix)² = 1 and so8CoordMatrix.det ≠ 0. -/
theorem so8CoordMatrix_transpose_mul_self : so8CoordMatrixᵀ * so8CoordMatrix = 1 :=
  set_option maxHeartbeats 80000000 in by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, transpose_apply, so8CoordMatrix, upperTriangleIdx, one_apply,
      so8Generator, generator_0, generator_1, generator_2, generator_3, generator_4, generator_5,
      generator_6, generator_7, generator_8, generator_9, generator_10, generator_11,
      generator_12, generator_13, generator_14, generator_15, generator_16, generator_17,
      generator_18, generator_19, generator_20, generator_21, generator_22, generator_23,
      generator_24, generator_25, generator_26, generator_27]

end Hqiv
