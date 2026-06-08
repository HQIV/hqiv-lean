import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.QuantumChemistry.PhaseGeometryDensity

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
* **Propagation** shell: `solarSystemPropagationShell = 0` (ξ = 1); not the hadron pin.
* **Source curvature** from orbital phase geometry (`PhaseGeometryDensity`); legacy shell-4 is calibration only.
* Lattice imprint: `alpha = 3/5` (`alpha_eq_3_5`).

Angular-momentum and O-Maxwell coupling are **hypothesis fields** on the Python side only
until chart-level orbit hypotheses are bundled (same honesty as `OMaxwellFluidChartHypothesis`).
Frame-rotation discharge for `‖r×v‖²` and equatorial axis fractions is proved in
`Hqiv.Geometry.SpatialRotationLorentzClosure` (`orbitalAngularMomentumSq_invariant`,
`equatorialFractionFromAxis_invariant`).

Polar-fiber saturation uses shell transverse floor `h_{z,{\rm eff}}^2=h_z^2+h_{\rm ref}^2/(m+1)^2`
(see `polar_fiber_phi_boost` in the flyby calculator); no `max(h_z,\varepsilon)` clip.
The orbital angular Rindler scale `r |dω_orb/dt|` is likewise kept as a scalar bridge here;
the vector construction `ω_orb=(r×v)/r^2` remains a Python-side orbit hypothesis.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.QuantumChemistry

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

/-- Legacy hadron-chart source shell (calibration witness only; not the orbital readout ξ). -/
def flybyLegacySourceShell : ℕ := 4

/-- Backward-compatible alias for the legacy source-shell index. -/
def flybyAnchorShell : ℕ := flybyLegacySourceShell

theorem flybyPhiAnchor_eq : phi_of_shell flybyAnchorShell = 10 := by
  rw [phi_of_shell_closed_form, phiTemperatureCoeff_eq_two]
  norm_num [flybyAnchorShell, flybyLegacySourceShell]

/-- Propagation-shell index for solar-system orbital readouts (near-pole band). -/
def solarSystemPropagationShell : ℕ := 0

theorem solarSystemPropagationShell_eq : solarSystemPropagationShell = 0 := rfl

/-- Continuous propagation coordinate ξ = m + 1 at the solar-system band (not shell 4). -/
noncomputable def flybyPropagationXi : ℝ := xiOfShell solarSystemPropagationShell

theorem flybyPropagationXi_eq_one : flybyPropagationXi = 1 := by
  unfold flybyPropagationXi xiOfShell solarSystemPropagationShell
  norm_num

/-!
## Orbital phase geometry → curvature budget (no shell-4 readout pin)

Earth (or any central body) supplies local curvature via inverse-square geometry.
The small mass/φ delta is `orbitalCurvatureMassDeltaFraction` at the encounter witness.
-/

/-- Curvature density ρ_orb at an encounter witness. -/
noncomputable def flybyCurvatureDensityAt (w : OrbitalPhaseWitness) : ℝ :=
  orbitalCurvatureDensityFraction w

/-- Homogeneous curvature budget at the propagation ξ slot. -/
noncomputable def flybyHomogeneousCurvatureBudget (w : OrbitalPhaseWitness) : ℝ :=
  homogeneousCurvatureBudgetFromOrbital flybyPropagationXi w

/-- Dimensionless curvature mass delta above the dilute (GR) limit. -/
noncomputable def flybyCurvatureMassDeltaFraction (w : OrbitalPhaseWitness) : ℝ :=
  orbitalCurvatureMassDeltaFraction flybyPropagationXi w

theorem flybyCurvatureMassDelta_zero_of_dilute (w : OrbitalPhaseWitness)
    (hρ : orbitalCurvatureDensityFraction w = 0) :
    flybyCurvatureMassDeltaFraction w = 0 :=
  orbitalCurvatureMassDelta_zero_of_zero_density flybyPropagationXi w hρ

/--
Phase-geometry source-shell factor: gate=0 ⇒ unity; gate=1 ⇒ full `B_hom(ξ_prop, ρ_orb)`.

Replaces bare `flybyDynamicKappaPhi m 4 gate` when orbital phase geometry is active.
-/
noncomputable def flybyDynamicKappaPhiFromPhase (w : OrbitalPhaseWitness) (gate : ℝ) : ℝ :=
  let bHom := flybyHomogeneousCurvatureBudget w
  1 + gate * (bHom - 1)

theorem flybyDynamicKappaPhiFromPhase_closed (w : OrbitalPhaseWitness) :
    flybyDynamicKappaPhiFromPhase w 0 = 1 := by
  unfold flybyDynamicKappaPhiFromPhase
  ring

theorem flybyDynamicKappaPhiFromPhase_open (w : OrbitalPhaseWitness) :
    flybyDynamicKappaPhiFromPhase w 1 = flybyHomogeneousCurvatureBudget w := by
  unfold flybyDynamicKappaPhiFromPhase
  ring

/-!
## Dynamic baryonic source-shell factors

The propagation/readout shell and the baryonic source/action shell are distinct
slots.  Solar-system Doppler propagation stays on the near-pole Kirchhoff
band (`solarSystemPropagationShell = 0`, ξ = 1).  Source action uses orbital
phase geometry (`flybyDynamicKappaPhiFromPhase`) when the chord gate is open;
`flybyLegacySourceShell = referenceM = 4` remains a hadron-chart calibration alias only.

The orbit geometry is still a Python-side hypothesis.  Lean records the algebraic
contract for a **dynamic gate**: when the source gate is closed there is no
source-shell boost; when it is fully open the baryonic shell contributes the
same coefficients formerly denoted `kappa_phi = m+1` and
`kappa_vac = phi(m) * (m+1)`.
-/

/-- Source-shell step coefficient `m+1` (the former `kappa_phi` slot). -/
noncomputable def flybySourceShellStep (m : ℕ) : ℝ :=
  (m + 1 : ℝ)

/-- Vacuum/source-shell coefficient `phi(m) * (m+1)` (the former `kappa_vac` slot). -/
noncomputable def flybyVacuumSourceScale (m : ℕ) : ℝ :=
  phi_of_shell m * flybySourceShellStep m

theorem flybySourceShellStep_anchor_eq :
    flybySourceShellStep flybyAnchorShell = 5 := by
  unfold flybySourceShellStep flybyAnchorShell flybyLegacySourceShell
  norm_num

theorem flybyVacuumSourceScale_anchor_eq :
    flybyVacuumSourceScale flybyAnchorShell = 50 := by
  unfold flybyVacuumSourceScale flybySourceShellStep flybyAnchorShell flybyLegacySourceShell
  rw [phi_of_shell_closed_form, phiTemperatureCoeff_eq_two]
  norm_num

/-- Dynamic source-shell factor for the metric-phi/horizon source channel.

`gate = 0` leaves the propagation-only value unchanged; `gate = 1` opens the
full baryonic source-shell coefficient `m+1`. -/
noncomputable def flybyDynamicKappaPhi (m : ℕ) (gate : ℝ) : ℝ :=
  1 + gate * (flybySourceShellStep m - 1)

/-- Dynamic source-shell factor for the vacuum source channel. -/
noncomputable def flybyDynamicKappaVac (m : ℕ) (gate : ℝ) : ℝ :=
  1 + gate * (flybyVacuumSourceScale m - 1)

theorem flybyDynamicKappaPhi_closed (m : ℕ) :
    flybyDynamicKappaPhi m 0 = 1 := by
  unfold flybyDynamicKappaPhi
  ring

theorem flybyDynamicKappaPhi_open (m : ℕ) :
    flybyDynamicKappaPhi m 1 = flybySourceShellStep m := by
  unfold flybyDynamicKappaPhi
  ring

theorem flybyDynamicKappaVac_closed (m : ℕ) :
    flybyDynamicKappaVac m 0 = 1 := by
  unfold flybyDynamicKappaVac
  ring

theorem flybyDynamicKappaVac_open (m : ℕ) :
    flybyDynamicKappaVac m 1 = flybyVacuumSourceScale m := by
  unfold flybyDynamicKappaVac
  ring

theorem flybyDynamicKappaPhi_anchor_open :
    flybyDynamicKappaPhi flybyAnchorShell 1 = 5 := by
  rw [flybyDynamicKappaPhi_open, flybySourceShellStep_anchor_eq]

theorem flybyDynamicKappaVac_anchor_open :
    flybyDynamicKappaVac flybyAnchorShell 1 = 50 := by
  rw [flybyDynamicKappaVac_open, flybyVacuumSourceScale_anchor_eq]

theorem flybyDynamicKappaPhi_anchor_eq (gate : ℝ) :
    flybyDynamicKappaPhi flybyAnchorShell gate = 1 + 4 * gate := by
  unfold flybyDynamicKappaPhi flybySourceShellStep flybyAnchorShell flybyLegacySourceShell
  norm_num
  ring

theorem flybyDynamicKappaVac_anchor_eq (gate : ℝ) :
    flybyDynamicKappaVac flybyAnchorShell gate = 1 + 49 * gate := by
  unfold flybyDynamicKappaVac flybyVacuumSourceScale flybySourceShellStep flybyAnchorShell
    flybyLegacySourceShell
  rw [phi_of_shell_closed_form, phiTemperatureCoeff_eq_two]
  norm_num [flybyLegacySourceShell]
  ring

/-- Geometry-side release fraction; its exact orbit construction remains a hypothesis slot. -/
noncomputable def flybyHorizonRelease (gamma sin2theta rhoPol : ℝ) : ℝ :=
  gamma * sin2theta * rhoPol

theorem flybyHorizonRelease_eq_zero_of_sin2_zero (gamma rhoPol : ℝ) :
    flybyHorizonRelease gamma 0 rhoPol = 0 := by
  unfold flybyHorizonRelease
  ring

theorem flybyHorizonRelease_eq_zero_of_rho_zero (gamma sin2theta : ℝ) :
    flybyHorizonRelease gamma sin2theta 0 = 0 := by
  unfold flybyHorizonRelease
  ring

theorem flybyHorizonRelease_HQIV_eq (sin2theta rhoPol : ℝ) :
    flybyHorizonRelease gamma_HQIV sin2theta rhoPol =
      gamma_HQIV * sin2theta * rhoPol := by
  rfl

/-!
## Coherent vector-channel gate

The chord-integrated flyby calculator distinguishes the isotropic horizon trace
from the Lense--Thirring tangent vector slot.  The vector slot is now opened only
when the polar-fiber release exceeds the HQIV overlap threshold `γ`.

Lean records the algebraic contract; the orbit-level construction of `rhoPol`
from the trajectory and chord quadrature remains the Python-side hypothesis.
-/

/-- Linear coherence gate after the HQIV overlap threshold.

The Python implementation clamps this expression to `[0,1]`.  This unclamped
kernel is the algebraic object proved here: it is zero at `rhoPol = gamma` and
unit at `rhoPol = 1`. -/
noncomputable def flybyVectorCoherenceGate (gamma rhoPol : ℝ) : ℝ :=
  (rhoPol - gamma) / (1 - gamma)

/-- Vector-channel release with an additional coherence gate. -/
noncomputable def flybyCoherentHorizonRelease
    (gamma sin2theta rhoPol coherence : ℝ) : ℝ :=
  flybyHorizonRelease gamma sin2theta rhoPol * coherence

theorem flybyCoherentHorizonRelease_eq_zero_of_coherence_zero
    (gamma sin2theta rhoPol : ℝ) :
    flybyCoherentHorizonRelease gamma sin2theta rhoPol 0 = 0 := by
  unfold flybyCoherentHorizonRelease
  ring

theorem flybyCoherentHorizonRelease_eq_base_of_coherence_one
    (gamma sin2theta rhoPol : ℝ) :
    flybyCoherentHorizonRelease gamma sin2theta rhoPol 1 =
      flybyHorizonRelease gamma sin2theta rhoPol := by
  unfold flybyCoherentHorizonRelease
  ring

theorem flybyVectorCoherenceGate_HQIV_closed :
    flybyVectorCoherenceGate gamma_HQIV gamma_HQIV = 0 := by
  rw [gamma_eq_2_5]
  unfold flybyVectorCoherenceGate
  norm_num

theorem flybyVectorCoherenceGate_HQIV_open :
    flybyVectorCoherenceGate gamma_HQIV 1 = 1 := by
  rw [gamma_eq_2_5]
  unfold flybyVectorCoherenceGate
  norm_num

/-- At the γ threshold, the coherent L-T/vector release collapses to isotropic-only. -/
theorem flybyCoherentHorizonRelease_HQIV_closed_at_gamma (sin2theta : ℝ) :
    flybyCoherentHorizonRelease gamma_HQIV sin2theta gamma_HQIV
      (flybyVectorCoherenceGate gamma_HQIV gamma_HQIV) = 0 := by
  rw [flybyVectorCoherenceGate_HQIV_closed]
  unfold flybyCoherentHorizonRelease
  ring

/-- At full polar release, the coherent L-T/vector release recovers the derived γ split. -/
theorem flybyCoherentHorizonRelease_HQIV_open_at_one (sin2theta : ℝ) :
    flybyCoherentHorizonRelease gamma_HQIV sin2theta 1
      (flybyVectorCoherenceGate gamma_HQIV 1) =
      flybyHorizonRelease gamma_HQIV sin2theta 1 := by
  rw [flybyVectorCoherenceGate_HQIV_open]
  unfold flybyCoherentHorizonRelease
  ring

end

end Hqiv.Physics
