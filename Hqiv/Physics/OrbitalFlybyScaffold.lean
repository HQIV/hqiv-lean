import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone

/-!
# Orbital flyby scaffold (Earth gravity assist + HQIV screen)

**Purpose:** lock the equation names used in `scripts/hqiv_orbital_flyby_omaxwell.py` and
`papers/hqiv_orbital_flyby_anomaly.tex` to the existing Lean spine.

**Proved here:** algebra on the inertia factor `f` and screening weights (same as
`HQIVFluidClosureScaffold`). **Not claimed:** trajectory integration, J₂ numerics, or
matching Anderson et al.\ flyby anomalies in SI.

## Equation spine (paper §2)

* Modified inertia: `hqivFluidInertiaFactor aLoc phi = aLoc / (aLoc + phi/6)`;
  geodesic law \(\mathbf a=\mathbf a_{\rm GR}/f\) (Python `modified_inertia_geodesic`).
* Chart slot screen: `hqivFlybyScreenWeight aLoc phi = 1 - f` (O-Maxwell only; not the geodesic divisor).
* Shell readout: `phi_of_shell m = 2(m+1)`; anchor shell `referenceM = 4`.
* Lattice imprint: `alpha = 3/5` (`alpha_eq_3_5`).

Angular-momentum and O-Maxwell coupling are **hypothesis fields** on the Python side only
until chart-level orbit hypotheses are bundled (same honesty as `OMaxwellFluidChartHypothesis`).

Polar-fiber saturation uses shell transverse floor `h_{z,{\rm eff}}^2=h_z^2+h_{\rm ref}^2/(m+1)^2`
(see `polar_fiber_phi_boost` in the flyby calculator); no `max(h_z,\varepsilon)` clip.
The orbital angular Rindler scale `r |dω_orb/dt|` is likewise kept as a scalar bridge here;
the vector construction `ω_orb=(r×v)/r^2` remains a Python-side orbit hypothesis.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-- HQIV modification fraction active at a point: `1 - f(a,φ)`. -/
noncomputable def hqivFlybyScreenWeight (aLoc phi : ℝ) : ℝ :=
  1 - hqivFluidInertiaFactor aLoc phi

theorem hqivFlybyScreenWeight_nonneg (aLoc phi : ℝ) (ha : 0 < aLoc) (hφ : 0 ≤ phi)
    (hden : 0 < aLoc + phi / 6) :
    0 ≤ hqivFlybyScreenWeight aLoc phi := by
  unfold hqivFlybyScreenWeight
  exact sub_nonneg.mpr (hqivFluidInertiaFactor_le_one_of_nonneg_phi ha hφ hden)

theorem hqivFlybyScreenWeight_eq_zero_of_phi_zero (aLoc : ℝ) (ha : aLoc ≠ 0) :
    hqivFlybyScreenWeight aLoc 0 = 0 := by
  unfold hqivFlybyScreenWeight
  simp [hqivFluidInertiaFactor_eq_one_of_phi_zero ha]

/-- Screened effective-coupling ratio: `1 + ((φ/φ_ref)^α - 1) × w`. -/
noncomputable def hqivScreenedGeffRatio (phi phiRef w alpha : ℝ) : ℝ :=
  1 + ((phi / phiRef) ^ alpha - 1) * w

theorem hqivScreenedGeffRatio_eq_one_of_zero_weight (phi phiRef alpha : ℝ) :
    hqivScreenedGeffRatio phi phiRef 0 alpha = 1 := by
  unfold hqivScreenedGeffRatio
  ring

theorem hqivScreenedGeffRatio_eq_one_of_unit_weight (phi phiRef alpha : ℝ) :
    hqivScreenedGeffRatio phi phiRef 1 alpha = (phi / phiRef) ^ alpha := by
  unfold hqivScreenedGeffRatio
  ring

/-- Minimum equatorial fraction `(h_z/h)²` on shell `m` from `T(m)=1/(m+1)`. -/
noncomputable def flybyEquatorialFractionFloor (m : ℕ) : ℝ := 1 / (m + 1 : ℝ) ^ 2

/-- Per-unit-mass orbital angular Rindler acceleration scale `r |dω_orb/dt|`. -/
noncomputable def flybyAngularRindlerScale (radius angularAccel : ℝ) : ℝ :=
  radius * |angularAccel|

theorem flybyAngularRindlerScale_nonneg (radius angularAccel : ℝ) (hr : 0 ≤ radius) :
    0 ≤ flybyAngularRindlerScale radius angularAccel := by
  unfold flybyAngularRindlerScale
  exact mul_nonneg hr (abs_nonneg angularAccel)

/-- Equatorial inertia scale with the angular Rindler contribution switched on. -/
noncomputable def flybyEquatorialAngularScale
    (aRad centripetal aAngular lEq : ℝ) : ℝ :=
  aRad + (centripetal + aAngular) * lEq

theorem flybyEquatorialAngularScale_eq_withoutAngular_of_zero
    (aRad centripetal lEq : ℝ) :
    flybyEquatorialAngularScale aRad centripetal 0 lEq = aRad + centripetal * lEq := by
  unfold flybyEquatorialAngularScale
  ring

/-- Anchor shell for Earth-flyby readout (`referenceM` proton ladder). -/
def flybyAnchorShell : ℕ := 4

theorem flybyPhiAnchor_eq : phi_of_shell flybyAnchorShell = 10 := by
  rw [phi_of_shell_closed_form, phiTemperatureCoeff_eq_two]
  norm_num [flybyAnchorShell]

end

end Hqiv.Physics
