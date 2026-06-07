import Hqiv.Physics.OrbitalFlybyScaffold
import Hqiv.Geometry.SpatialRotationLorentzClosure
import Mathlib.Data.Real.Sqrt

/-!
# Trajectory integration + J₂ oblateness (Python-side contract, Lean algebra)

`scripts/hqiv_orbital_flyby_omaxwell.py` performs RK4 propagation with optional J₂, third-body
tides, and HQIV inertia screening.  `OrbitalFlybyScaffold` records the **algebraic** flyby spine
but explicitly disclaims trajectory integration and J₂ numerics.

This module locks the **named formulas** the integrator uses so Python and Lean share one contract:

* colatitude weight `sin²θ` (`oblate_latitude_factor` / `spin_colatitude_sin_sq`);
* J₂ acceleration components (`j2_accel`);
* linkage to `flybyHorizonRelease` via `sin²θ`.

**Not claimed:** RK4 convergence, Anderson flyby anomaly matching, or certified SI numerics.
-/

namespace Hqiv.Physics

open Hqiv.Geometry
open Real

noncomputable section

/-- Body-fixed spin / symmetry axis (unit vector hypothesis slot). -/
structure RotatingBodyFrame where
  spinAxis : Fin 3 → ℝ

/-- Euclidean radius `‖r‖` with the Python guard `max(‖r‖, ε)`. -/
noncomputable def orbitalRadius (r : Fin 3 → ℝ) (ε : ℝ) : ℝ :=
  max (Real.sqrt (euclideanNormSq3 r)) ε

/-- Colatitude factor `sin²θ = 1 - cos²θ` relative to a body axis.

Matches `oblate_latitude_factor` when `spinAxis = e_z` and `r` is already body-fixed. -/
noncomputable def colatitudeSinSq (r spinAxis : Fin 3 → ℝ) (ε : ℝ) : ℝ :=
  let rMag := orbitalRadius r ε
  let cosColat := |euclideanInner3 r spinAxis| / rMag
  1 - cosColat ^ 2

theorem colatitudeSinSq_bodyFixed_z (r : Fin 3 → ℝ) (ε : ℝ) :
    colatitudeSinSq r ![0, 0, 1] ε =
      1 - (|r 2| / orbitalRadius r ε) ^ 2 := by
  unfold colatitudeSinSq orbitalRadius
  simp [euclideanInner3, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- J₂ perturbation parameters for a central body. -/
structure J2BodyParams where
  gm : ℝ
  radius : ℝ
  j2 : ℝ

/-- J₂ acceleration (`j2_accel` in Python) in body-fixed coordinates with `z` along spin axis. -/
noncomputable def j2Acceleration (p : J2BodyParams) (r : Fin 3 → ℝ) (ε : ℝ) : Fin 3 → ℝ :=
  if p.j2 = 0 then fun _ => 0
  else
    let x := r 0
    let y := r 1
    let z := r 2
    let rMag := orbitalRadius r ε
    if rMag ≤ p.radius then fun _ => 0
    else
      let mu := p.gm
      let re2 := p.radius ^ 2
      let r2 := rMag ^ 2
      let r5 := rMag ^ 5
      let coef := -(3 / 2 : ℝ) * p.j2 * mu * re2 / r5
      let z2_r2 := z ^ 2 / r2
      ![coef * x * (5 * z2_r2 - 1), coef * y * (5 * z2_r2 - 1), coef * z * (5 * z2_r2 - 3)]

theorem j2Acceleration_zero_j2 (p : J2BodyParams) (r : Fin 3 → ℝ) (ε : ℝ) (hj : p.j2 = 0) :
    j2Acceleration p r ε = fun _ => 0 := by
  unfold j2Acceleration
  simp [hj]

/-- One RK4 step is a Python-side obligation; Lean records the signature only. -/
structure TrajectoryIntegrationPending : Prop where
  rk4_step : True
  asymptotic_speed_readout : True
  oblate_sample_mean : True
  anderson_anomaly_match : True

def trajectoryIntegrationPending_default : TrajectoryIntegrationPending where
  rk4_step := trivial
  asymptotic_speed_readout := trivial
  oblate_sample_mean := trivial
  anderson_anomaly_match := trivial

/-- `sin²θ` is unchanged when `r` and the spin axis rotate together (body-fixed frame). -/
theorem colatitudeSinSq_rotation_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (r spinAxis : Fin 3 → ℝ) (ε : ℝ) :
    colatitudeSinSq (R.mulVec r) (R.mulVec spinAxis) ε = colatitudeSinSq r spinAxis ε := by
  unfold colatitudeSinSq orbitalRadius
  have hnorm := euclideanNormSq3_mulVec_orthogonal R hR r
  have hinner := euclideanInner3_mulVec_orthogonal R hR r spinAxis
  simp [hnorm, hinner]

/-- Horizon-release factor uses the same `sin²θ` slot as the J₂ latitude weight. -/
theorem flybyHorizonRelease_eq_gamma_sin2 (gamma sin2theta rhoPol : ℝ) :
    flybyHorizonRelease gamma sin2theta rhoPol = gamma * sin2theta * rhoPol := by
  unfold flybyHorizonRelease
  ring

/-!
## Trajectory integrator contract (Python-side hypothesis)
-/

/-- Minimal state carried by `propagate_flyby` / RK4 in Python. -/
structure OrbitalTrajectoryState where
  r : Fin 3 → ℝ
  v : Fin 3 → ℝ
  t : ℝ

/-- Lean ↔ Python contract bundle for the flyby integrator. -/
structure OrbitalTrajectoryJ2Program where
  inertia_screen : ∀ aLoc phi : ℝ, hqivFlybyScreenWeight aLoc phi = 1 - hqivFluidInertiaFactor aLoc phi
  colatitude_rotation_invariant :
    ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (_hR : IsOrthogonal3 R) (r axis : Fin 3 → ℝ) (ε : ℝ),
      colatitudeSinSq (R.mulVec r) (R.mulVec axis) ε = colatitudeSinSq r axis ε
  j2_off_when_disabled :
    ∀ (p : J2BodyParams) (r : Fin 3 → ℝ) (ε : ℝ), p.j2 = 0 → j2Acceleration p r ε = fun _ => 0
  integration : TrajectoryIntegrationPending

theorem orbitalTrajectoryJ2Program_default : OrbitalTrajectoryJ2Program where
  inertia_screen := fun _ _ => rfl
  colatitude_rotation_invariant :=
    fun R _hR r axis ε => colatitudeSinSq_rotation_invariant R _hR r axis ε
  j2_off_when_disabled := j2Acceleration_zero_j2
  integration := trajectoryIntegrationPending_default

end

end Hqiv.Physics
