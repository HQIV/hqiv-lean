import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith

import Hqiv.Geometry.SpatialSliceRapidityScaffold

/-!
# Euclidean spatial slice and horizon shells (constructive `ShellFamily`)

This file **instantiates** the abstract `ShellFamily` from `SpatialSliceRapidityScaffold` on a
concrete **3D model space** `SpatialSliceEuclidean3 = EuclideanSpace ℝ (Fin 3)` with the standard
Lebesgue measure. It is the first **manifold-level** anchor in the sense of
`AGENTS/MANIFOLD_ZETA_ROADMAP.md` §1 (spatial slice + shells), without claiming Ricci integrals or
identification with `Hqiv.deltaE`.

**Discrete lattice analogue:** integer lattice points in `ℤ³` grouped by `sup_i |p i|` (pairwise disjoint
shells) are in `LatticePointMaxAbsShells`. Here the same nested-shell idea uses **Euclidean** radii and
**L²** balls/annuli in `ℝ³`. Horizontal slices of a `3`-ball as embedded `2`-balls (any coordinate
plane `x k = z`) are in `EuclideanBallHorizontalSlice` (`closedBall_inter_coordPlane_k_eq_image_slice`).

**Definitions**

* `euclideanHorizonShell r` — shell `0` is the **closed ball** `closedBall 0 (r 1)`; shell `m+1` is
  the **annulus** `closedBall 0 (r (m+2)) \\ closedBall 0 (r (m+1))`, i.e. `r (m+1) < ‖x‖ ≤ r (m+2)`.
* `spatialSliceToSpacetimeCoords` — embed `(t, x)` into `Fin 4 → ℝ` as `Fin.cons t (fun i => x i)`,
  matching the indexing of `Hqiv.Geometry.ContinuumSpacetimeChart` (`0` = time component).

**Proved (under `StrictMono r`)**

* `ShellFamilyPairwiseDisjoint (euclideanHorizonShell r)`
* `MeasurableSet` for each shell
* `Bornology.IsBounded` and `volume (shell) < ⊤`

**HQVM narrative:** the spatial block of the ADM line element uses `HQVM_spatial_coeff a Φ` as a
conformal factor on Euclidean 3-space; see `HQVMetric` (“HQVM manifold geometry”).

**Not here (in this file):** Lorentzian metric as a single `PseudoMetricSpace` or `∫ R √g`.

**Next layer:** `Hqiv.Geometry.SpatialSliceContinuumBridge` — `spacetimeCoordsEquiv` / thin-slice lemmas,
`rVolFromGeometricModelTarget` (algebraic inverse of `deltaE_geometricModel`), and hypotheses under which
scaled shell volume reproduces combinatorial `deltaE` through the geometric model.
-/

namespace Hqiv.Geometry

noncomputable section

open scoped ENNReal BigOperators NNReal
open MeasureTheory EuclideanSpace Metric

/-- Flat spatial model (standard `l²` inner product on `Fin 3 → ℝ`). -/
abbrev SpatialSliceEuclidean3 : Type :=
  EuclideanSpace ℝ (Fin 3)

variable {r : ℕ → ℝ}

/-- Concentric shells: center ball of radius `r 1`, then annuli between successive radii.

`r 0` is unused; all radii that appear are `r k` for `k ≥ 1`. -/
noncomputable def euclideanHorizonShell (r : ℕ → ℝ) : ShellFamily SpatialSliceEuclidean3
  | 0 => Metric.closedBall (0 : SpatialSliceEuclidean3) (r 1)
  | Nat.succ m =>
      Metric.closedBall (0 : SpatialSliceEuclidean3) (r (m + 2)) \
        Metric.closedBall (0 : SpatialSliceEuclidean3) (r (m + 1))

theorem euclideanHorizonShell_zero (r : ℕ → ℝ) :
    euclideanHorizonShell r 0 = Metric.closedBall (0 : SpatialSliceEuclidean3) (r 1) := rfl

theorem euclideanHorizonShell_succ (r : ℕ → ℝ) (m : ℕ) :
    euclideanHorizonShell r (Nat.succ m) =
      Metric.closedBall (0 : SpatialSliceEuclidean3) (r (m + 2)) \
        Metric.closedBall (0 : SpatialSliceEuclidean3) (r (m + 1)) := rfl

theorem mem_euclideanHorizonShell_succ_iff {r : ℕ → ℝ} {m : ℕ} {x : SpatialSliceEuclidean3} :
    x ∈ euclideanHorizonShell r (Nat.succ m) ↔
      r (m + 1) < ‖x‖ ∧ ‖x‖ ≤ r (m + 2) := by
  simp only [euclideanHorizonShell_succ, Set.mem_diff, Metric.mem_closedBall, dist_zero_right, not_le]
  constructor
  · intro ⟨hout, hin⟩
    exact ⟨hin, hout⟩
  · intro ⟨hin, hout⟩
    exact ⟨hout, hin⟩

/-- Embed a constant-time spatial point into the `Fin 4` coordinate tuple (`0` = time index). -/
noncomputable def spatialSliceToSpacetimeCoords (t : ℝ) (x : SpatialSliceEuclidean3) : Fin 4 → ℝ :=
  Fin.cons t (fun i : Fin 3 => x i)

@[simp]
theorem spatialSliceToSpacetimeCoords_zero (t : ℝ) (x : SpatialSliceEuclidean3) :
    spatialSliceToSpacetimeCoords t x 0 = t := by
  simp [spatialSliceToSpacetimeCoords]

@[simp]
theorem spatialSliceToSpacetimeCoords_succ (t : ℝ) (x : SpatialSliceEuclidean3) (i : Fin 3) :
    spatialSliceToSpacetimeCoords t x (Fin.succ i) = x i := by
  simp [spatialSliceToSpacetimeCoords]

/-!
### Disjointness (nested radii)
-/

theorem disjoint_euclideanHorizonShell_zero_succ (r : ℕ → ℝ) (hmono : StrictMono r) (m : ℕ) :
    Disjoint (euclideanHorizonShell r 0) (euclideanHorizonShell r (Nat.succ m)) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, euclideanHorizonShell_zero,
    Metric.mem_closedBall, dist_zero_right]
  intro hball hann
  rcases mem_euclideanHorizonShell_succ_iff.mp hann with ⟨hlo, hhi⟩
  cases m with
  | zero =>
    linarith only [hball, hlo]
  | succ m' =>
    have hr : r 1 < r (m' + 2) := hmono (by omega : 1 < m' + 2)
    have bad : r (m' + 2) < r 1 := lt_of_lt_of_le hlo hball
    exact lt_asymm hr bad

theorem disjoint_euclideanHorizonShell_succ_succ_of_lt (r : ℕ → ℝ) (hmono : StrictMono r)
    {m n : ℕ} (h : m < n) :
    Disjoint (euclideanHorizonShell r (Nat.succ m)) (euclideanHorizonShell r (Nat.succ n)) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hxm hxn
  rcases mem_euclideanHorizonShell_succ_iff.mp hxm with ⟨_, hxm_hi⟩
  rcases mem_euclideanHorizonShell_succ_iff.mp hxn with ⟨hxn_lo, _⟩
  have hle : r (m + 2) ≤ r (n + 1) := hmono.monotone (by omega : m + 2 ≤ n + 1)
  linarith only [hxm_hi, hxn_lo, hle]

theorem ShellFamilyPairwiseDisjoint_euclideanHorizonShell (r : ℕ → ℝ) (hmono : StrictMono r) :
    ShellFamilyPairwiseDisjoint (euclideanHorizonShell r) := by
  intro m n hne
  rcases lt_trichotomy m n with (hmn | rfl | hnm)
  · cases m with
    | zero =>
        rcases n with (_ | n')
        · contradiction
        · exact disjoint_euclideanHorizonShell_zero_succ r hmono n'
    | succ m' =>
        rcases n with (_ | n')
        · exact (nomatch hmn)
        · have hm'n' : m' < n' := Nat.succ_lt_succ_iff.mp hmn
          exact disjoint_euclideanHorizonShell_succ_succ_of_lt r hmono hm'n'
  · contradiction
  · cases n with
    | zero =>
        rcases m with (_ | m')
        · contradiction
        · exact Disjoint.symm (disjoint_euclideanHorizonShell_zero_succ r hmono m')
    | succ n' =>
        rcases m with (_ | m')
        · exact (nomatch hnm)
        · have hn'm' : n' < m' := Nat.succ_lt_succ_iff.mp hnm
          exact Disjoint.symm (disjoint_euclideanHorizonShell_succ_succ_of_lt r hmono hn'm')

/-!
### Measurability and finite volume
-/

theorem measurableSet_euclideanHorizonShell (r : ℕ → ℝ) (m : ℕ) :
    MeasurableSet (euclideanHorizonShell r m) := by
  cases m with
  | zero => simpa [euclideanHorizonShell] using measurableSet_closedBall
  | succ m' =>
      simpa [euclideanHorizonShell] using
        (measurableSet_closedBall.diff measurableSet_closedBall :
          MeasurableSet (Metric.closedBall (0 : SpatialSliceEuclidean3) (r (m' + 2)) \
            Metric.closedBall (0 : SpatialSliceEuclidean3) (r (m' + 1))))

theorem isBounded_euclideanHorizonShell (r : ℕ → ℝ) (m : ℕ) :
    Bornology.IsBounded (euclideanHorizonShell r m) := by
  cases m with
  | zero =>
      simpa [euclideanHorizonShell] using isBounded_closedBall (x := (0 : SpatialSliceEuclidean3)) (r := r 1)
  | succ m' =>
      refine (isBounded_closedBall (x := (0 : SpatialSliceEuclidean3)) (r := r (m' + 2))).subset ?_
      intro x hx
      rw [mem_euclideanHorizonShell_succ_iff] at hx
      simpa [dist_zero_right] using hx.2

theorem volume_euclideanHorizonShell_lt_top (r : ℕ → ℝ) (m : ℕ) :
    volume (euclideanHorizonShell r m) < ⊤ :=
  (isBounded_euclideanHorizonShell r m).measure_lt_top

/-- Lebesgue volume of a shell, as a real number (finite under `volume_lt_top` above). -/
noncomputable def euclideanShellVolumeReal (r : ℕ → ℝ) (m : ℕ) : ℝ :=
  (volume (euclideanHorizonShell r m)).toReal

theorem euclideanShellVolumeReal_nonneg (r : ℕ → ℝ) (m : ℕ) : 0 ≤ euclideanShellVolumeReal r m := by
  unfold euclideanShellVolumeReal
  exact ENNReal.toReal_nonneg

/-- Scalar curvature **proxy** per shell: scale the measured volume by a nonnegative constant.

This is **data**, not `∫ R √g`. It feeds `deltaE_geometricModel` only if you prove a separate bridge. -/
noncomputable def geometricScalarSlotFromShellVolume (c : ℝ≥0) (r : ℕ → ℝ) (m : ℕ) : ℝ :=
  (c : ℝ) * euclideanShellVolumeReal r m

/-- Push a spatial set into the `t = t₀` plane of `Fin 4 → ℝ`. -/
def spacetimeThinSlice (t₀ : ℝ) (S : Set SpatialSliceEuclidean3) : Set (Fin 4 → ℝ) :=
  Set.image (spatialSliceToSpacetimeCoords t₀) S

end

end Hqiv.Geometry
