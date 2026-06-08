import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.SpatialSliceManifold
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Comoving worldlines in the HQVM synchronous chart (`Fin 4 → ℝ`)

This is the **next formal step** after `Hqiv.Physics.HQIVGravityReadoutScalars`: a concrete **curve**
in the continuum coordinates used by `SpatialSliceManifold.spatialSliceToSpacetimeCoords` and
`ContinuumSpacetimeChart`, together with the **comoving contravariant four-velocity** normalized by the
HQVM lapse.

**Chart / metric layer:** `ContinuumSpacetimeChart` installs **Euclidean** calculus on `Fin 4 → ℝ`; the
**Lorentzian** HQVM line element (`ds² = -N² dt² + …`) lives in `HQVMetric` via `HQVM_metric` /
`HQVM_inverseMetric` (proved mutual inverses on `Fin 4`). Here we **do not** identify the Euclidean
inner product with `g_μν`. We package **comoving** `u^μ` and lowered `u_μ`, and contractions
`g_{μν} u^μ u^ν = g^{μν} u_μ u_ν = u^μ u_μ = -1` for the standard ansatz `u^t = 1/N`, `u^i = 0`.

**Worldline:** fixed spatial point `x : SpatialSliceEuclidean3`, time coordinate `t ↦ (t, x)`.

See also `HQVMetric` (ADM scalars), `SpatialSliceContinuumBridge` (chart bridges), and
`Hqiv.Physics.HQIVGravityReadoutScalars` (fixed lattice vs time narrative).
-/

noncomputable section

namespace Hqiv.Geometry

open BigOperators

/-- `∂/∂t` in coordinate components: `1` on the time index `0 : Fin 4`, else `0`. -/
def comovingCoordinateVelocity : Fin 4 → ℝ :=
  Pi.single (0 : Fin 4) 1

/-- Comoving worldline through fixed spatial point `x`: same chart as `spatialSliceToSpacetimeCoords`. -/
noncomputable def comovingWorldlineCoords (x : SpatialSliceEuclidean3) (t : ℝ) : Fin 4 → ℝ :=
  spatialSliceToSpacetimeCoords t x

@[simp]
theorem comovingWorldlineCoords_time (x : SpatialSliceEuclidean3) (t : ℝ) :
    comovingWorldlineCoords x t 0 = t := by
  simp [comovingWorldlineCoords]

@[simp]
theorem comovingWorldlineCoords_space (x : SpatialSliceEuclidean3) (t : ℝ) (i : Fin 3) :
    comovingWorldlineCoords x t (Fin.succ i) = x i := by
  simp [comovingWorldlineCoords]

/--
Finite coordinate increment along a comoving worldline equals `Δt` times `comovingCoordinateVelocity`
(componentwise). This is the discrete analogue of `∂_t x^μ = (1, 0, 0, 0)` without invoking `deriv`.
-/
theorem comovingWorldline_finiteIncrement (x : SpatialSliceEuclidean3) (t₀ t₁ : ℝ) (μ : Fin 4) :
    comovingWorldlineCoords x t₁ μ - comovingWorldlineCoords x t₀ μ =
      (t₁ - t₀) * comovingCoordinateVelocity μ := by
  unfold comovingWorldlineCoords comovingCoordinateVelocity
  rcases Fin.eq_zero_or_eq_succ μ with rfl | ⟨i, rfl⟩
  · simp [spatialSliceToSpacetimeCoords, Pi.single]
  · simp [spatialSliceToSpacetimeCoords, Pi.single, Fin.succ_ne_zero i]

/--
Contravariant comoving four-velocity `u^μ` in the HQVM synchronous chart: `u^0 = 1/N`, `u^i = 0`.

This matches `dτ = N dt` along comoving observers (`N = HQVM_lapse …`), hence `dt/dτ = 1/N`.
-/
noncomputable def comovingFourVelocityContr (N : ℝ) (_ : N ≠ 0) : Fin 4 → ℝ :=
  Pi.single (0 : Fin 4) (1 / N)

/--
Covariant comoving four-velocity `u_μ = g_{μν} u^ν`. For diagonal `g` and `u^i = 0`, only
`u_0 = g_tt u^0 = -N` is nonzero.
-/
noncomputable def comovingFourVelocityCov (N : ℝ) (_ : N ≠ 0) : Fin 4 → ℝ :=
  Pi.single (0 : Fin 4) (-N)

@[simp]
theorem comovingFourVelocityCov_zero (N : ℝ) (hN : N ≠ 0) :
    comovingFourVelocityCov N hN 0 = -N := by
  simp [comovingFourVelocityCov]

theorem comovingFourVelocityCov_succ (N : ℝ) (hN : N ≠ 0) (i : Fin 3) :
    comovingFourVelocityCov N hN (Fin.succ i) = 0 := by
  simp [comovingFourVelocityCov, Fin.succ_ne_zero i]

@[simp]
theorem comovingFourVelocityContr_zero (N : ℝ) (hN : N ≠ 0) :
    comovingFourVelocityContr N hN 0 = 1 / N := by
  simp [comovingFourVelocityContr]

theorem comovingFourVelocityContr_succ (N : ℝ) (hN : N ≠ 0) (i : Fin 3) :
    comovingFourVelocityContr N hN (Fin.succ i) = 0 := by
  simp [comovingFourVelocityContr, Fin.succ_ne_zero i]

/--
**Timelike normalization (diagonal `g_tt` only):** for comoving `u`, only `μ = ν = 0` contributes;
`g_tt (u^0)² = (-N²)(1/N)² = -1`.
-/
theorem HQVM_comoving_timeslice_normalized (N : ℝ) (hN : N ≠ 0) :
    HQVM_g_tt N * (comovingFourVelocityContr N hN 0) ^ 2 = -1 := by
  simp [comovingFourVelocityContr, HQVM_g_tt]
  field_simp [hN]

/-- Same statement packaged with `HQVM_lapse` as the lapse. -/
theorem HQVM_comoving_timeslice_normalized_lapse (Φ φ t : ℝ) (hN : HQVM_lapse Φ φ t ≠ 0) :
    HQVM_g_tt (HQVM_lapse Φ φ t) * (comovingFourVelocityContr (HQVM_lapse Φ φ t) hN 0) ^ 2 = -1 :=
  HQVM_comoving_timeslice_normalized _ hN

/-- Matches `HQVM_unit_normal_squared`: the `(1/N)` factor is the same timelike normalization. -/
theorem HQVM_comoving_timeslice_eq_unitNormal (N : ℝ) (hN : N ≠ 0) :
    HQVM_g_tt N * (comovingFourVelocityContr N hN 0) ^ 2 =
      HQVM_g_tt N * (1 / N) ^ 2 := by
  simp [comovingFourVelocityContr]

theorem HQVM_comoving_timeslice_normalized' (N : ℝ) (hN : N ≠ 0) :
    HQVM_g_tt N * (1 / N) ^ 2 = -1 :=
  HQVM_unit_normal_squared N hN

/-- Lowering `u^ν` with `HQVM_metric` gives `comovingFourVelocityCov`. -/
theorem comovingFourVelocityCov_eq_metric_lower (N : ℝ) (hN : N ≠ 0) (a Φ : ℝ) (μ : Fin 4) :
    (∑ ν : Fin 4, HQVM_metric N a Φ μ ν * comovingFourVelocityContr N hN ν) =
      comovingFourVelocityCov N hN μ := by
  fin_cases μ <;> simp [Fin.sum_univ_four, HQVM_metric, HQVM_g_tt, comovingFourVelocityContr,
    comovingFourVelocityCov, Fin.succ_ne_zero] <;> field_simp [hN]

/-- **Full covariant contraction** `g_{μν} u^μ u^ν = -1` (diagonal synchronous HQVM). -/
theorem HQVM_comoving_metric_contraction (N : ℝ) (hN : N ≠ 0) (a Φ : ℝ) :
    (∑ μ : Fin 4, ∑ ν : Fin 4, HQVM_metric N a Φ μ ν * comovingFourVelocityContr N hN μ *
        comovingFourVelocityContr N hN ν) = -1 := by
  rw [Fin.sum_univ_four]
  simp [HQVM_metric, HQVM_g_tt, comovingFourVelocityContr, Fin.succ_ne_zero]
  field_simp [hN]

/-- **Contravariant inverse contraction** `g^{μν} u_μ u_ν = -1`. -/
theorem HQVM_comoving_inverseMetric_contraction (N : ℝ) (hN : N ≠ 0) (a Φ : ℝ) :
    (∑ μ : Fin 4, ∑ ν : Fin 4, HQVM_inverseMetric N a Φ μ ν * comovingFourVelocityCov N hN μ *
        comovingFourVelocityCov N hN ν) = -1 := by
  rw [Fin.sum_univ_four]
  simp [HQVM_inverseMetric, comovingFourVelocityCov, Fin.succ_ne_zero]
  field_simp [hN]

/-- **Mixed contraction** `u^μ u_μ = -1`. -/
theorem HQVM_comoving_mixed_contraction (N : ℝ) (hN : N ≠ 0) :
    (∑ μ : Fin 4, comovingFourVelocityContr N hN μ * comovingFourVelocityCov N hN μ) = -1 := by
  rw [Fin.sum_univ_four]
  simp [comovingFourVelocityContr, comovingFourVelocityCov]
  field_simp [hN]

/-!
### Finite proper-time increment (constant lapse along comoving segment)

Along a comoving worldline with **constant** lapse `N`, coordinate time increment `Δt` corresponds to
proper-time increment `Δτ = N Δt` (finite analogue of `dτ = N dt`).
-/

/-- Proper-time increment for constant lapse `N` over coordinate-time increment `Δt`. -/
noncomputable def properTimeDelta_comoving (N : ℝ) (_ : N ≠ 0) (Δt : ℝ) : ℝ :=
  N * Δt

theorem properTimeDelta_comoving_eq (N : ℝ) (hN : N ≠ 0) (Δt : ℝ) :
    properTimeDelta_comoving N hN Δt = N * Δt :=
  rfl

theorem properTimeDelta_comoving_smul (N : ℝ) (hN : N ≠ 0) (c : ℝ) (Δt : ℝ) :
    properTimeDelta_comoving N hN (c * Δt) = c * properTimeDelta_comoving N hN Δt := by
  simp [properTimeDelta_comoving, mul_assoc, mul_left_comm, mul_comm]

end Hqiv.Geometry
