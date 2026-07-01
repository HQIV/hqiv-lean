import Hqiv.Physics.FluxTubeStressDivergenceBridge
import Hqiv.Physics.OMaxwellLongitudinalMomentumBridge
import Hqiv.Physics.PromotedOMaxwell

/-!
# Longitudinal stress ↔ promoted O-Maxwell EL bridge

**Purpose:** make explicit the programme's **typed** link between a stationary
promoted O-Maxwell Euler–Lagrange residual on the longitudinal axis and the
rank-one stress-divergence slot already used in the momentum / flux-tube charts.

Companion: `papers/longitudinal_em_force_hqiv/hqiv_longitudinal_em_force.tex` §momentum-bridge;
`Hqiv.Physics.FluxTubeStressDivergenceBridge`.

## Proof status (all `Prop` / definitional, zero `sorry`)

* **§1.** Stationary promoted EL at the EM leg / longitudinal axis.
* **§2.** φ-source slot equals `4π E_HQIV` bridge (natural units).
* **§3.** Rank-one axial divergence feeds `hqivLongitudinalStressForce3`.
* **§4.** Combined bundle: EL stationary + stress chart + coefficient ID.
* **§5.** Discharged honesty ledger.

**Not claimed:** deriving `∇·T` from the action without the rank-one chart;
unique φ(s); automatic equality of EL residual and stress divergence in 3-D MHD;
kinetic derivation of `κ_L`.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Geometry

noncomputable section

/-!
## §1. Stationary promoted residual at the axis
-/

/-- Promoted O-Maxwell residual vanishes on the EM leg at the longitudinal axis. -/
structure LongitudinalPromotedELStationary
    (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : Prop where
  chart :
    PromotedOMaxwellChartHypotheses φ_val φF c longitudinalAxisFin4
  residual_zero :
    promotedOMaxwellResidual J_src A φF c 0 longitudinalAxisFin4 = 0

theorem LongitudinalPromotedELStationary.residual_eq_EL_zero
    {J_src : Fin 8 → Fin 4 → ℝ} {A : Fin 8 → Fin 4 → ℝ}
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    (h : LongitudinalPromotedELStationary J_src A φ_val φF c) :
    Hqiv.Physics.EL_O_general_coordsField J_src A φ_val φF c 0 longitudinalAxisFin4 = 0 := by
  rcases h.chart with ⟨hAlg, _⟩
  rw [← promotedOMaxwellResidual_eq_EL_coordsField J_src A φ_val φF c 0 longitudinalAxisFin4 hAlg]
  exact h.residual_zero

/-!
## §2. φ-source ↔ HQIV field at the axis
-/

structure LongitudinalPhiSourceHQIVBridge (couplingLog dphi_ds : ℝ) : Prop where
  source_eq :
    omaxwellEmSlotPhiSource couplingLog dphi_ds =
      4 * Real.pi * coronalLongitudinalHQIVField 1 couplingLog dphi_ds
  hqiv_eq :
    omaxwellEffectiveAxialCurrentIncrement couplingLog dphi_ds =
      coronalLongitudinalHQIVField 1 couplingLog dphi_ds

theorem longitudinalPhiSourceHQIVBridge_discharged (couplingLog dphi_ds : ℝ) :
    LongitudinalPhiSourceHQIVBridge couplingLog dphi_ds where
  source_eq := omaxwellEmSlotPhiSource_eq_four_pi_coronalHQIVField couplingLog dphi_ds
  hqiv_eq := omaxwellEffectiveAxialCurrentIncrement_eq_coronalHQIVField couplingLog dphi_ds

/-!
## §3. Rank-one divergence → stress force slot
-/

/-- Axial rank-one divergence `(∇·τ)_0` supplied by the 1-D flux-tube chart. -/
def longitudinalRankOneStressDivergenceAxial (data : FluxTube1DStressChart) : ℝ :=
  fluxTubeAxialStressDivergence data

theorem longitudinalRankOneStressDivergenceAxial_eq_force
    (data : FluxTube1DStressChart) :
    hqivLongitudinalStressForce3 (fun i => if i = 0 then longitudinalRankOneStressDivergenceAxial data else 0) 0 =
      longitudinalRankOneStressDivergenceAxial data := by
  unfold longitudinalRankOneStressDivergenceAxial hqivLongitudinalStressForce3
  simp

theorem longitudinalRankOneStressDivergenceAxial_eq_fluxTube
    (data : FluxTube1DStressChart) :
    longitudinalRankOneStressDivergenceAxial data = fluxTubeAxialStressDivergence data := rfl

/-!
## §4. Combined EL + stress chart bundle
-/

/-- Typed bundle linking stationary promoted EL, O-Maxwell momentum chart, and
rank-one stress divergence on a 1-D flux tube. -/
structure LongitudinalStressActionDivergenceBridge
    (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (nq J sigma Estar couplingLog dphi_ds : ℝ) (stress : FluxTube1DStressChart)
    (stressCoeff : LongitudinalStressCoefficientIdentification) : Prop where
  el_stationary : LongitudinalPromotedELStationary J_src A φ_val φF c
  omaxwell_momentum :
    OMaxwellLongitudinalMomentumBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds
  stress_chart :
    FluxTube1DPromotedStressBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds stress
      stressCoeff
  phi_source : LongitudinalPhiSourceHQIVBridge couplingLog dphi_ds
  stress_force_eq_divergence :
    fluxTubeAxialStressForce stress 0 = longitudinalRankOneStressDivergenceAxial stress

theorem LongitudinalStressActionDivergenceBridge.stress_divergence_eq_rank_one
    {J_src : Fin 8 → Fin 4 → ℝ} {A : Fin 8 → Fin 4 → ℝ}
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog dphi_ds : ℝ} {stress : FluxTube1DStressChart}
    {stressCoeff : LongitudinalStressCoefficientIdentification}
    (h : LongitudinalStressActionDivergenceBridge J_src A φ_val φF c nq J sigma Estar couplingLog
      dphi_ds stress stressCoeff) :
    fluxTubeAxialStressDivergence stress = longitudinalRankOneStressDivergenceAxial stress := rfl

theorem LongitudinalStressActionDivergenceBridge.carrier_hqiv_eq_stress_driver
    {J_src : Fin 8 → Fin 4 → ℝ} {A : Fin 8 → Fin 4 → ℝ}
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog dphi_ds : ℝ} {stress : FluxTube1DStressChart}
    {stressCoeff : LongitudinalStressCoefficientIdentification}
    (h : LongitudinalStressActionDivergenceBridge J_src A φ_val φF c nq J sigma Estar couplingLog
      dphi_ds stress stressCoeff)
    (direction : Fin 3 → ℝ) (hunit : direction 0 * direction 0 = 1) :
    hqivLongitudinalStressTensor3 stress.kappaL stress.rho stress.couplingLog stress.gradPhiAlong direction 0 0 =
      stressCoeff.nq * coronalLongitudinalHQIVField stressCoeff.Estar stress.couplingLog stress.gradPhiAlong :=
  h.stress_chart.carrier_force_eq_stress_driver direction hunit

/-!
## §5. Honesty ledger
-/

structure LongitudinalStressActionDivergenceHonestyLedger : Prop where
  phi_source_bridge :
    ∀ couplingLog dphi_ds, LongitudinalPhiSourceHQIVBridge couplingLog dphi_ds
  rank_one_force :
    ∀ data : FluxTube1DStressChart,
      fluxTubeAxialStressForce data 0 = longitudinalRankOneStressDivergenceAxial data
  promoted_stress :
    ∀ φ_val φF c nq J sigma Estar couplingLog dphi_ds stress stressCoeff
      (h : FluxTube1DPromotedStressBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds stress
        stressCoeff),
      fluxTubeAxialStressForce stress 0 = fluxTubeAxialStressDivergence stress

theorem longitudinalStressActionDivergenceHonestyLedger_discharged :
    LongitudinalStressActionDivergenceHonestyLedger where
  phi_source_bridge := longitudinalPhiSourceHQIVBridge_discharged
  rank_one_force := fun data => by
    rw [longitudinalRankOneStressDivergenceAxial_eq_fluxTube]
    exact fluxTubeAxialStressForce_axis0 data
  promoted_stress := fun _ _ _ _ _ _ _ _ _ _ _ h =>
    FluxTube1DPromotedStressBridge.stress_force_eq_divergence h

end

end Hqiv.Physics
