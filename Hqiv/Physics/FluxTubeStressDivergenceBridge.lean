import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Physics.OMaxwellLongitudinalMomentumBridge
import Hqiv.Physics.PromotedOMaxwell

/-!
# 1-D flux-tube stress-divergence bridge (Promoted O-Maxwell)

**Purpose:** extend `OMaxwellLongitudinalMomentumBridge` with an explicit
**1-D flux-tube** stress-divergence chart: how the rank-one longitudinal
`τ_∥` slot feeds the axial momentum equation when `∇·τ` is evaluated on a
straight column, and how the **footpoint-only** HQIV boundary form relates to
bulk-smooth vs concentrated gradients.

Companion: `papers/longitudinal_em_force_hqiv/hqiv_longitudinal_em_force.tex` §momentum-bridge;
`Hqiv.Physics.PromotedOMaxwell`.

## Proof status (all `Prop` / definitional, zero `sorry`)

* **§1.** 1-D axial stress divergence for uniform `κ_L ρ Λ` and varying `∂_s φ`.
* **§2.** Link divergence force density to `hqivLongitudinalStressForce3`.
* **§3.** Coefficient identification through `LongitudinalStressCoefficientIdentification`.
* **§4.** Footpoint-only vs bulk-smooth gradient bundles.
* **§5.** Promoted O-Maxwell + momentum + stress chart bundle.
* **§6.** Discharged honesty ledger.

**Not claimed:** full 3-D MHD `∇·T`; unique φ(s) profile; derived κ_L from kinetics;
automatic equality of promoted EL residual and stress divergence without the
explicit chart hypothesis.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Geometry

noncomputable section

/-!
## §1. 1-D axial stress divergence
-/

/-- Chart data for a straight flux tube with axial coordinate `s`. -/
structure FluxTube1DStressChart where
  kappaL : ℝ
  rho : ℝ
  couplingLog : ℝ
  gradPhiAlong : ℝ
  gradPhiSecond : ℝ

/-- Bulk-smooth axial divergence for `τ_∥ ∝ s⊗s` with uniform coefficients:
`(∇·τ)_s = κ_L ρ Λ · ∂²_s φ` when `Λ` is constant along the column. -/
def fluxTubeAxialStressDivergence (data : FluxTube1DStressChart) : ℝ :=
  data.kappaL * data.rho * data.couplingLog * data.gradPhiSecond

theorem fluxTubeAxialStressDivergence_zero_of_flat_grad
    (data : FluxTube1DStressChart) (h : data.gradPhiSecond = 0) :
    fluxTubeAxialStressDivergence data = 0 := by
  unfold fluxTubeAxialStressDivergence
  rw [h, mul_zero]

/-- Force density slot fed to the momentum equation (simulator supplies the same
value as `hqivLongitudinalStressForce3`). -/
def fluxTubeAxialStressForce (data : FluxTube1DStressChart) : Fin 3 → ℝ :=
  hqivLongitudinalStressForce3 (fun i => if i = 0 then fluxTubeAxialStressDivergence data else 0)

theorem fluxTubeAxialStressForce_axis0
    (data : FluxTube1DStressChart) :
    fluxTubeAxialStressForce data 0 = fluxTubeAxialStressDivergence data := by
  simp [fluxTubeAxialStressForce, hqivLongitudinalStressForce3]

theorem fluxTubeAxialStressForce_off_axis_zero
    (data : FluxTube1DStressChart) {i : Fin 3} (h : i ≠ 0) :
    fluxTubeAxialStressForce data i = 0 := by
  simp [fluxTubeAxialStressForce, hqivLongitudinalStressForce3, h]

/-!
## §2. Coefficient link to carrier HQIV force
-/

/-- Carrier HQIV force density at the chart's linear-gradient point. -/
def fluxTubeCarrierHqivForce (coeff : LongitudinalStressCoefficientIdentification)
    (couplingLog gradPhiAlong : ℝ) : ℝ :=
  coeff.nq * coronalLongitudinalHQIVField coeff.Estar couplingLog gradPhiAlong

/-- When `∂²_s φ = 0` but `∂_s φ ≠ 0`, bulk divergence vanishes while the carrier
HQIV force may remain (footpoint / boundary interpretation). -/
structure FluxTubeFootpointOnlyGradHypothesis
    (coeff : LongitudinalStressCoefficientIdentification) (couplingLog gradPhiAlong gradPhiSecond : ℝ) : Prop where
  grad_second_zero : gradPhiSecond = 0
  grad_along_ne_zero : gradPhiAlong ≠ 0

theorem FluxTubeFootpointOnlyGradHypothesis.bulk_divergence_zero
    {coeff : LongitudinalStressCoefficientIdentification} {couplingLog gradPhiAlong gradPhiSecond : ℝ}
    (hf : FluxTubeFootpointOnlyGradHypothesis coeff couplingLog gradPhiAlong gradPhiSecond) :
    fluxTubeAxialStressDivergence
        { kappaL := coeff.kappaL, rho := coeff.rho, couplingLog := couplingLog,
          gradPhiAlong := gradPhiAlong, gradPhiSecond := gradPhiSecond } = 0 :=
  fluxTubeAxialStressDivergence_zero_of_flat_grad _ hf.grad_second_zero

theorem FluxTubeFootpointOnlyGradHypothesis.carrier_force_ne_zero
    {coeff : LongitudinalStressCoefficientIdentification} {couplingLog gradPhiAlong gradPhiSecond : ℝ}
    (hf : FluxTubeFootpointOnlyGradHypothesis coeff couplingLog gradPhiAlong gradPhiSecond)
    (hnq : 0 < coeff.nq) (hE : 0 < coeff.Estar) (hΛ : 0 < couplingLog) :
    fluxTubeCarrierHqivForce coeff couplingLog gradPhiAlong ≠ 0 := by
  unfold fluxTubeCarrierHqivForce
  intro hzero
  rcases mul_eq_zero.mp hzero with hnq0 | hfield0
  · linarith [hnq]
  · exact coronalLongitudinalHQIVField_ne_zero_of_pos_inputs coeff.Estar couplingLog gradPhiAlong hE hΛ
      hf.grad_along_ne_zero hfield0

/-- Integrated boundary force across cross-section `A` and footpoint φ jump. -/
def fluxTubeIntegratedBoundaryForce
    (A nq Estar couplingLog phiPhoto phiCorona : ℝ) : ℝ :=
  coronalLongitudinalForceBoundary A nq Estar couplingLog phiPhoto phiCorona

theorem fluxTubeIntegratedBoundaryForce_eq_flux_over_velocity
    (A nq Estar couplingLog vParallel phiPhoto phiCorona : ℝ) (hv : vParallel ≠ 0) :
    fluxTubeIntegratedBoundaryForce A nq Estar couplingLog phiPhoto phiCorona =
      A * coronalHeatingFluxBoundary nq Estar couplingLog vParallel phiPhoto phiCorona / vParallel := by
  unfold fluxTubeIntegratedBoundaryForce coronalLongitudinalForceBoundary coronalHeatingFluxBoundary
  field_simp [hv]

/-!
## §3. Promoted O-Maxwell + stress chart bundle
-/

/-- Explicit stress chart matched to a promoted O-Maxwell momentum bridge. -/
structure FluxTube1DPromotedStressBridge (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) (nq J sigma Estar couplingLog dphi_ds : ℝ)
    (stress : FluxTube1DStressChart) (stressCoeff : LongitudinalStressCoefficientIdentification) : Prop where
  omaxwell_momentum :
    OMaxwellLongitudinalMomentumBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds
  stress_coeff_fields :
    stressCoeff.kappaL = stress.kappaL ∧
      stressCoeff.rho = stress.rho ∧
      stressCoeff.nq = nq ∧
      stressCoeff.Estar = Estar
  grad_along_eq : stress.gradPhiAlong = dphi_ds
  promoted_stationary :
    PromotedOMaxwellChartHypotheses φ_val φF c longitudinalAxisFin4

theorem FluxTube1DPromotedStressBridge.stress_force_eq_divergence
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog dphi_ds : ℝ} {stress : FluxTube1DStressChart}
    {stressCoeff : LongitudinalStressCoefficientIdentification}
    (_h : FluxTube1DPromotedStressBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds stress
      stressCoeff) :
    fluxTubeAxialStressForce stress 0 = fluxTubeAxialStressDivergence stress :=
  fluxTubeAxialStressForce_axis0 stress

theorem FluxTube1DPromotedStressBridge.carrier_force_eq_stress_driver
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog dphi_ds : ℝ} {stress : FluxTube1DStressChart}
    {stressCoeff : LongitudinalStressCoefficientIdentification}
    (h : FluxTube1DPromotedStressBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds stress
      stressCoeff)
    (direction : Fin 3 → ℝ) (hunit : direction 0 * direction 0 = 1) :
    hqivLongitudinalStressTensor3 stress.kappaL stress.rho stress.couplingLog stress.gradPhiAlong direction 0 0 =
      stressCoeff.nq * coronalLongitudinalHQIVField stressCoeff.Estar stress.couplingLog stress.gradPhiAlong := by
  rw [← h.stress_coeff_fields.1, ← h.stress_coeff_fields.2.1, h.grad_along_eq]
  exact longitudinalStressDiagonal_eq_carrierHQIVForce stressCoeff stress.couplingLog dphi_ds direction hunit

/-- Footpoint-only bundle: bulk `∇·τ = 0` but carrier force and integrated boundary
may remain (interpretive layer for loop-footpoint anchoring). -/
structure FluxTubeFootpointOnlyStressBridge
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (nq J sigma Estar couplingLog dphi_ds : ℝ) (stress : FluxTube1DStressChart)
    (stressCoeff : LongitudinalStressCoefficientIdentification)
    (phiPhoto phiCorona : ℝ) : Prop where
  promoted :
    FluxTube1DPromotedStressBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds stress stressCoeff
  footpoint_grad :
    FluxTubeFootpointOnlyGradHypothesis stressCoeff stress.couplingLog dphi_ds stress.gradPhiSecond
  phi_jump_eq : phiCorona - phiPhoto = dphi_ds

theorem FluxTubeFootpointOnlyStressBridge.bulk_divergence_zero
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog dphi_ds : ℝ} {stress : FluxTube1DStressChart}
    {stressCoeff : LongitudinalStressCoefficientIdentification} {phiPhoto phiCorona : ℝ}
    (h : FluxTubeFootpointOnlyStressBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds stress
      stressCoeff phiPhoto phiCorona) :
    fluxTubeAxialStressDivergence stress = 0 :=
  fluxTubeAxialStressDivergence_zero_of_flat_grad stress h.footpoint_grad.grad_second_zero

theorem FluxTubeFootpointOnlyStressBridge.integrated_boundary_eq
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog dphi_ds : ℝ} {stress : FluxTube1DStressChart}
    {stressCoeff : LongitudinalStressCoefficientIdentification} {phiPhoto phiCorona : ℝ}
    (A : ℝ)
    (h : FluxTubeFootpointOnlyStressBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds stress
      stressCoeff phiPhoto phiCorona) :
    fluxTubeIntegratedBoundaryForce A nq Estar couplingLog phiPhoto phiCorona =
      coronalLongitudinalForceBoundary A nq Estar couplingLog phiPhoto phiCorona := rfl

/-!
## §4. Honesty ledger
-/

structure FluxTubeStressDivergenceHonestyLedger : Prop where
  stress_force_axis :
    ∀ data : FluxTube1DStressChart,
      fluxTubeAxialStressForce data 0 = fluxTubeAxialStressDivergence data
  footpoint_bulk_zero :
    ∀ coeff couplingLog gradAlong gradSecond,
      FluxTubeFootpointOnlyGradHypothesis coeff couplingLog gradAlong gradSecond →
        fluxTubeAxialStressDivergence
          { kappaL := coeff.kappaL, rho := coeff.rho, couplingLog := couplingLog,
            gradPhiAlong := gradAlong, gradPhiSecond := gradSecond } = 0
  promoted_bundle_stress :
    ∀ φ_val φF c nq J sigma Estar couplingLog dphi_ds stress stressCoeff
      (h : FluxTube1DPromotedStressBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds stress
        stressCoeff),
      fluxTubeAxialStressForce stress 0 = fluxTubeAxialStressDivergence stress

theorem fluxTubeStressDivergenceHonestyLedger_discharged :
    FluxTubeStressDivergenceHonestyLedger where
  stress_force_axis := fun data => fluxTubeAxialStressForce_axis0 data
  footpoint_bulk_zero := fun _ _ _ _ hf => hf.bulk_divergence_zero
  promoted_bundle_stress := fun _ _ _ _ _ _ _ _ _ _ _ h =>
    FluxTube1DPromotedStressBridge.stress_force_eq_divergence h

end

end Hqiv.Physics
