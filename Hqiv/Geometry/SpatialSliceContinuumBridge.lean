import Hqiv.Geometry.SpatialSliceManifold
import Hqiv.Geometry.ContinuumSpacetimeChart
import Hqiv.Geometry.OctonionicLightCone

/-!
# Spatial slice ↔ continuum chart ↔ `deltaE_geometricModel` (bridges)

This module **connects** three layers that stay separate by design until you assume explicit bridges:

1. **`SpatialSliceManifold`** — `SpatialSliceEuclidean3`, Lebesgue shells, `spatialSliceToSpacetimeCoords`;
   horizontal slices of `closedBall` as embedded planar disks are in `EuclideanBallHorizontalSlice`
   (`closedBall_inter_coordPlane_eq_image_slice`).
2. **`ContinuumSpacetimeChart`** — `SpacetimeEuclidean4`, `spacetimeCoordsEquiv`, `spacetimeOfCoords`.
3. **`deltaE_geometricModel`** (`SpatialSliceRapidityScaffold`) — analytic slot `R_vol` with combinatorial
   `alpha` and `curvature_norm_combinatorial`.

**Chart lemmas** are unconditional (equiv identities, thin-slice membership).

**Curvature / volume lemmas** are **algebraic**: `rVolFromGeometricModelTarget` inverts the geometric model in
`R_vol` at each shell; scaled shell volume matches combinatorial `deltaE` **only** if you discharge the
pointwise equality hypothesis (tuning `c` and radii `r` against Lebesgue data — not proved here).

See also `HQVMetric` (“Spatial slice (constructive Euclidean ℝ³)”) for the ADM / HQVM narrative.
-/

namespace Hqiv.Geometry

noncomputable section

open scoped NNReal
open Hqiv

/-!
## Continuum chart (`Fin 4 → ℝ` ↔ `SpacetimeEuclidean4`)
-/

theorem spacetimeCoordsEquiv_spacetimeOfCoords (c : Fin 4 → ℝ) :
    spacetimeCoordsEquiv (spacetimeOfCoords c) = c :=
  spacetimeCoordsEquiv.apply_symm_apply c

theorem spacetimeOfCoords_spacetimeCoordsEquiv (x : SpacetimeEuclidean4) :
    spacetimeOfCoords (spacetimeCoordsEquiv x) = x :=
  spacetimeCoordsEquiv.symm_apply_apply x

/-- Round-trip for spatially embedded coordinates. -/
theorem spacetimeCoordsEquiv_spatialSliceEmbed (t : ℝ) (x : SpatialSliceEuclidean3) :
    spacetimeCoordsEquiv (spacetimeOfCoords (spatialSliceToSpacetimeCoords t x)) =
      spatialSliceToSpacetimeCoords t x :=
  spacetimeCoordsEquiv_spacetimeOfCoords _

/-- Same point in the Euclidean 4-chart as `spacetimeOfCoords` of the raw tuple. -/
noncomputable def spacetimePointFromSpatialSlice (t : ℝ) (x : SpatialSliceEuclidean3) : SpacetimeEuclidean4 :=
  spacetimeOfCoords (spatialSliceToSpacetimeCoords t x)

@[simp]
theorem spacetimeCoordsEquiv_spacetimePointFromSpatialSlice (t : ℝ) (x : SpatialSliceEuclidean3) :
    spacetimeCoordsEquiv (spacetimePointFromSpatialSlice t x) = spatialSliceToSpacetimeCoords t x :=
  spacetimeCoordsEquiv_spacetimeOfCoords _

theorem mem_spacetimeThinSlice_iff (t₀ : ℝ) (S : Set SpatialSliceEuclidean3) (c : Fin 4 → ℝ) :
    c ∈ spacetimeThinSlice t₀ S ↔ c 0 = t₀ ∧ ∃ x ∈ S, spatialSliceToSpacetimeCoords t₀ x = c := by
  simp only [spacetimeThinSlice, Set.mem_image]
  constructor
  · rintro ⟨x, hxS, hceq⟩
    refine ⟨?_, x, hxS, hceq⟩
    rw [← hceq]
    simp
  · rintro ⟨_hc0, x, hxS, hceq⟩
    exact ⟨x, hxS, hceq⟩

/-!
## Invert `deltaE_geometricModel` in the `R_vol` slot; connect shell volume

Given a per-shell target (e.g. combinatorial `deltaE`), solve for the unique `R_vol m` that makes
`deltaE_geometricModel R_vol m = target m` at that shell (assuming `alpha ≠ 0` and positive combinatorial norm).
-/

/-- Algebraic inverse: choose `R_vol m` so `deltaE_geometricModel R_vol m = target m`. -/
noncomputable def rVolFromGeometricModelTarget (target : ℕ → ℝ) (m : ℕ) : ℝ :=
  (target m * (m + 1 : ℝ) / curvature_norm_combinatorial - 1) / alpha

theorem alpha_ne_zero : alpha ≠ 0 := by
  rw [alpha_eq_3_5]
  norm_num

theorem curvature_norm_combinatorial_ne_zero : curvature_norm_combinatorial ≠ 0 :=
  ne_of_gt curvature_norm_combinatorial_pos

theorem deltaE_geometricModel_rVolFromGeometricModelTarget_eq (target : ℕ → ℝ) (m : ℕ) :
    deltaE_geometricModel (fun k => rVolFromGeometricModelTarget target k) m = target m := by
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  unfold deltaE_geometricModel rVolFromGeometricModelTarget
  field_simp [alpha_ne_zero, curvature_norm_combinatorial_ne_zero, hm]
  ring

/-- Specialization when the target is combinatorial `δ_E`. -/
theorem deltaE_geometricModel_rVolFromDeltaE_eq (m : ℕ) :
    deltaE_geometricModel (fun k => rVolFromGeometricModelTarget deltaE k) m = deltaE m :=
  deltaE_geometricModel_rVolFromGeometricModelTarget_eq deltaE m

/-- Specialization when the target is the quaternionic comparison imprint `6^3 * sqrt(3) * shell_shape`. -/
theorem deltaE_geometricModel_rVolFromQuaternionicCandidate_eq (m : ℕ) :
    deltaE_geometricModel (fun k => rVolFromGeometricModelTarget deltaE_quaternionicCandidate k) m =
      deltaE_quaternionicCandidate m :=
  deltaE_geometricModel_rVolFromGeometricModelTarget_eq deltaE_quaternionicCandidate m

/-- The quaternionic comparison target is not the canonical combinatorial `δ_E` shell ladder. -/
theorem deltaE_geometricModel_rVolFromQuaternionicCandidate_ne_deltaE (m : ℕ) :
    deltaE_geometricModel (fun k => rVolFromGeometricModelTarget deltaE_quaternionicCandidate k) m ≠
      deltaE m := by
  rw [deltaE_geometricModel_rVolFromQuaternionicCandidate_eq]
  intro h
  apply deltaE_ne_deltaE_quaternionicCandidate_of_shell_shape_ne_zero m
  have hshape_pos : 0 < shell_shape m := by
    rw [shell_shape_eq_density_succ]
    exact curvatureDensity_pos_succ m
  · exact ne_of_gt hshape_pos
  · exact h.symm

/-- If scaled shell volume equals the inverse slot for `deltaE`, the geometric model reproduces `deltaE`. -/
theorem deltaE_geometricModel_geometricScalarSlotFromShellVolume_eq_deltaE
    (c : ℝ≥0) (r : ℕ → ℝ) (m : ℕ)
    (h : ∀ k, geometricScalarSlotFromShellVolume c r k = rVolFromGeometricModelTarget deltaE k) :
    deltaE_geometricModel (fun k => geometricScalarSlotFromShellVolume c r k) m = deltaE m := by
  have eqf : (fun k => geometricScalarSlotFromShellVolume c r k) =
      (fun k => rVolFromGeometricModelTarget deltaE k) :=
    funext h
  rw [eqf]
  exact deltaE_geometricModel_rVolFromDeltaE_eq m

/-- Packaging: pointwise equality of the volume proxy with the inverse slot implies agreement with combinatorial
`δ_E` **after** applying `deltaE_geometricModel` (not raw `geom = deltaE` unless you intentionally identify them). -/
theorem agreesWithCombinatorialDeltaE_deltaE_geometricModel_of_shellVolume_matches_rVol
    (c : ℝ≥0) (r : ℕ → ℝ) (m : ℕ)
    (h : ∀ k, geometricScalarSlotFromShellVolume c r k = rVolFromGeometricModelTarget deltaE k) :
    agreesWithCombinatorialDeltaE (fun k => deltaE_geometricModel (fun j => geometricScalarSlotFromShellVolume c r j) k) m := by
  rw [agreesWithCombinatorialDeltaE]
  exact deltaE_geometricModel_geometricScalarSlotFromShellVolume_eq_deltaE c r m h

end

end Hqiv.Geometry
