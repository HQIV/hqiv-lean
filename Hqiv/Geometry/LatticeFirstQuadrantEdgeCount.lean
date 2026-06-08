import Mathlib.Data.Nat.Basic

/-!
# First-quadrant edge counts (ℂ ≅ ℝ², “1 complex dimension”)

Nonnegative integer solutions to `x + y = m` are **weak compositions** of `m` into **2** parts; the
count is **`m + 1`** (stars-and-bars in dimension 2).

**HQIV design note:** the target marginal count **4** is **dimension × 2** (real dimension `2` ⇒
`2 × 2 = 4`) via `hqivMarginalPrimePointCount`.

**Classical territory (literature, not proved here as identity):** discrete shells, rays, and
“where new lattice mass appears” are standard **geometry-of-numbers / Gauss-circle** adjacent topics;
rational **primes** in `ℤ` enter that story in well-known ways. Nothing in this file proves that our
marginal-count predicate **coincides** with classical primality — only the **same combinatorial spine**
(axis / marginal steps) is formalized.

**Large `m` (hard, search-shaped):** resolving **composite** angular structure forces scanning many
directions (often sketched up to **`√m`-scale** in ray searches — not formalized here). In richer
models one may see **more** off-axis composite directions than in the minimal 2D picture (e.g. **8**
vs **4** in doubled / octonionic stories); that remains **open** in Lean.

**Rapidity alignment (design target):** the HQIV **rapidity** channel (`φ·t` with Maxwell tipping /
`zetaHQIVTerm` phase) is *intended* to **point at** these discrete ray coordinates so one does not
rely on brute angular search alone — see `SpatialSliceRapidityScaffold` and `OctonionicZeta`.
-/

namespace Hqiv.Geometry

/-- HQIV marginal “prime” point count: **real dimension × 2** (e.g. ℂ ≅ ℝ² ⇒ `2 * 2 = 4`). -/
def hqivMarginalPrimePointCount (realDim : ℕ) : ℕ :=
  realDim * 2

@[simp]
theorem hqivMarginalPrimePointCount_two : hqivMarginalPrimePointCount 2 = 4 :=
  rfl

/-- Nonnegative integer solutions to `x + y = m` (2-part weak composition). Count is `m + 1`. -/
def latticeFirstQuadrantEdgeCount (m : ℕ) : ℕ :=
  m + 1

@[simp]
theorem latticeFirstQuadrantEdgeCount_eq_four_iff (m : ℕ) :
    latticeFirstQuadrantEdgeCount m = 4 ↔ m = 3 := by
  simp [latticeFirstQuadrantEdgeCount]

/-- The edge with exactly four points is `x + y = 3` (`m = 3`). -/
theorem latticeFirstQuadrantEdgeCount_three : latticeFirstQuadrantEdgeCount 3 = 4 :=
  rfl

/-- At `m = 3`, the first-quadrant edge count matches `realDim * 2` for ℂ ≅ ℝ² (`realDim = 2`). -/
theorem latticeFirstQuadrantEdgeCount_three_eq_hqivMarginalPrimePointCount :
    latticeFirstQuadrantEdgeCount 3 = hqivMarginalPrimePointCount 2 :=
  rfl

end Hqiv.Geometry
