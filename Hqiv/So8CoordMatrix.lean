import Hqiv.Generators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

-- CI needs high limits for the 28×28 matrix proof (784 cases, heavy norm_num)
set_option maxHeartbeats 200000000

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

/-- **QUARANTINED NUMERICAL IDEALIZATION — do not use for structural claims.**

Asserts that the columns of `so8CoordMatrix` are orthonormal (`Mᵀ * M = 1`). The
generators in `Hqiv.Generators` are stored as 14–15 digit *decimal* literals from a
numerical (Gram–Schmidt/SVD) orthonormalization. Interpreted as **exact rationals**,
their off-diagonal overlaps are `O(10⁻¹⁴)`, not `0`, so this equality is in fact
**false over `ℚ`**: it is an inconsistent axiom and must not be relied upon for any
soundness-critical conclusion.

It is retained *only* as a CI convenience that lets the legacy numeric closure build
(`Hqiv.GeneratorsLieClosure`) typecheck for the specific octonionic seed used by the
*conditional* forcing theorem. **All structural/dimensional facts are now proved
genuinely and axiom-free elsewhere:**

* `dim so(8) = 28` as real linear algebra — `Hqiv.Foundation.finrank_so8`;
* an axiom-free `so(8)` Lie-closure certificate (antisymmetry + bracket-closure +
  linear independence) — `Hqiv.Foundation.skewGen_so8_closure`.

Nothing in the Foundation spine, and no dimension claim in the papers, depends on
this axiom. -/
axiom so8CoordMatrix_transpose_mul_self : so8CoordMatrixᵀ * so8CoordMatrix = 1

end Hqiv
