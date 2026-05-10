import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac

import Hqiv.Geometry.ContinuumSpacetimeChart

/-!
# Discrete lattice indices vs continuous `ℝ⁴` (`SpacetimeEuclidean4`)

HQIV’s **combinatorial** layers (shell rung `m : ℕ`, patch corners `Fin 4`, `LatticeHilbert 4`, etc.)
are naturally **discrete**. The Clay / Dojo `SchwartzSpace` layer is phrased on **continuous**
`Spacetime = EuclideanSpace ℝ (Fin 4)` (same model as `Hqiv.Geometry.ContinuumSpacetimeChart`).

This file does **not** construct a tempered distribution or a full Wightman bridge; it only installs
typed **interface objects** so Story code can name the two standard bridges:

1. **Integer lattice sites** `Fin 4 → ℤ` (signed grid), scaled by a mesh `a : ℝ`, embedded in
   `SpacetimeEuclidean4` via `spacetimeOfCoords` (the same chart as `ContinuumSpacetimeChart`). The
   coordinate formula is `spacetimeCoordsEquiv_latticePointScaled_apply` (pullback to `Fin 4 → ℝ`).
2. **Spacelike quadrant lattice** `Fin 3 → ℕ` at `t = 0` in the same chart — matches the “natural
   numbers on spacelike dimensions” phrasing when you work in one causal wedge and encode signs
   separately (or restrict to a shell / octant story).
3. **Dirac comb (finite approximation):** `latticeDiracCombChartApprox` sums Dirac masses on the
   **chart** `Fin 4 → ℝ` (product Borel structure); continuum limits and pairing with `SchwartzSpace`
   are **analysis obligations** for downstream modules.

For Schwartz pairing one uses **continuum** tests `f : SpacetimeEuclidean4 → ℂ` (or `Fin 4 → ℝ → ℂ`
via the chart); lattice data enters either by **restricting** `f` to `latticePointScaled a n` or by
weak-* limits of `latticeDiracCombChartApprox` against chart-lifted tests (Riemann-sum style).
-/

namespace Hqiv.Story

noncomputable section

open scoped BigOperators
open MeasureTheory

open Hqiv.Geometry

/-- Signed integer sites on the four-dimensional cubic lattice (chart indices). -/
abbrev IntegerLatticeSite4 :=
  Fin 4 → ℤ

/-- Natural-number sites on the three **spacelike** chart directions (`Fin 3` maps into `1…3`). -/
abbrev SpacelikeNaturalLattice3 :=
  Fin 3 → ℕ

/-- Embed a scaled integer lattice site into the Euclidean `ℝ⁴` chart used across HQIV continuum
hooks (`SpacetimeEuclidean4`). -/
noncomputable def latticePointScaled (a : ℝ) (n : IntegerLatticeSite4) : SpacetimeEuclidean4 :=
  spacetimeOfCoords (fun i => a * (n i : ℝ))

/-- Embed a scaled **spacelike** `ℕ³` lattice at vanishing time component in the same chart. -/
noncomputable def spacelikeNaturalLatticePointScaled (a : ℝ) (n : SpacelikeNaturalLattice3) :
    SpacetimeEuclidean4 :=
  spacetimeOfCoords (Fin.cons 0 (fun j : Fin 3 => a * (n j : ℝ)))

theorem spacetimeCoordsEquiv_latticePointScaled_apply (a : ℝ) (n : IntegerLatticeSite4) (i : Fin 4) :
    spacetimeCoordsEquiv (latticePointScaled a n) i = a * (n i : ℝ) := by
  simp [latticePointScaled, spacetimeOfCoords]

theorem spacetimeCoordsEquiv_spacelikeNaturalLatticePointScaled_zero (a : ℝ) (n : SpacelikeNaturalLattice3) :
    spacetimeCoordsEquiv (spacelikeNaturalLatticePointScaled a n) 0 = 0 := by
  simp [spacelikeNaturalLatticePointScaled, spacetimeOfCoords, Fin.cons_zero]

theorem spacetimeCoordsEquiv_spacelikeNaturalLatticePointScaled_succ (a : ℝ) (n : SpacelikeNaturalLattice3)
    (j : Fin 3) :
    spacetimeCoordsEquiv (spacelikeNaturalLatticePointScaled a n) j.succ = a * (n j : ℝ) := by
  simp [spacelikeNaturalLatticePointScaled, spacetimeOfCoords, Fin.cons_succ]

/-- Finite **Dirac comb** on **chart coordinates** `Fin 4 → ℝ` (Borel `ℝ` factors supply
`MeasurableSpace`). Embeddings use `spacetimeCoordsEquiv ∘ latticePointScaled`. -/
noncomputable def latticeDiracCombChartApprox (ε : ℝ) (sites : Finset IntegerLatticeSite4) :
    Measure (Fin 4 → ℝ) :=
  ∑ n ∈ sites, Measure.dirac (spacetimeCoordsEquiv (latticePointScaled ε n))

end

end Hqiv.Story
