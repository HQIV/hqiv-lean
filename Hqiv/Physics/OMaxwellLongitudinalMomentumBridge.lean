import Hqiv.Physics.Action
import Hqiv.Physics.ContinuumOmaxwellClosure
import Hqiv.Physics.CoronalLongitudinalStress
import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Physics.PromotedOMaxwell

/-!
# O-Maxwell longitudinal momentum / stress bridge (paper companion)

**Purpose:** close the gaps flagged in the longitudinal EM programme review:
how the modified O-Maxwell **source** couples to carrier force density, directional
Maxwell stress, fluid momentum balance, and the J·E work-rate identity---without
claiming a full MHD or kinetic derivation.

Companion: `papers/longitudinal_em_force_hqiv/hqiv_longitudinal_em_force.tex`;
primer: `papers/include/hqiv_primer_appendix.tex`.

## Proof status (all `Prop` / definitional, zero `sorry`)

* **§1.** EM-slot φ source `α Λ ∂φ` equals `4π E_HQIV` at natural units (`E_∗=1`).
* **§2.** Chart identification bundles link `coordsGradientComponents` / `grad_phi`
  to the axial `∂_s φ` slot used in `CoronalLongitudinalStress`.
* **§3.** Carrier force `f_∥ = nq E_eff` and additive Ohmic + HQIV decomposition.
* **§4.** Directional stress tensor diagonal matches force density under explicit
  `κ_L ρ = nq E_∗` identification.
* **§5.** Work-rate / Poynting analogue: `q̇ = f_∥ v_∥ = nq v E_eff`.
* **§6.** Momentum balance bundles (additive channels; flat limit; discharged ledger).
* **§7.** Distinct fluid vacuum-source channel (`g_vac`) vs longitudinal EM force channel.

**Not claimed:** full `∇·T` from first principles; displacement of Lorentz force;
derivation of `κ_L` from kinetics; energy conservation in dissipative media beyond
the stated work-rate identity.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Geometry

noncomputable section

/-!
## §1. EM-slot φ source ↔ HQIV longitudinal field
-/

/-- φ-gradient contribution on the O-Maxwell EM inhomogeneous slot
(`a = 0`), matching `ModifiedMaxwell` / `Action` before the `4π J` term. -/
def omaxwellEmSlotPhiSource (couplingLog dphi_ds : ℝ) : ℝ :=
  alpha * couplingLog * dphi_ds

/-- Natural-unit bridge: source slot equals `4π` times `E_HQIV` with `E_∗ = 1`. -/
theorem omaxwellEmSlotPhiSource_eq_four_pi_coronalHQIVField
    (couplingLog dphi_ds : ℝ) :
    omaxwellEmSlotPhiSource couplingLog dphi_ds =
      4 * Real.pi * coronalLongitudinalHQIVField 1 couplingLog dphi_ds := by
  unfold omaxwellEmSlotPhiSource coronalLongitudinalHQIVField
  field_simp

theorem omaxwellEmSlotPhiSource_zero_of_dphi_zero (couplingLog : ℝ) :
    omaxwellEmSlotPhiSource couplingLog 0 = 0 := by
  unfold omaxwellEmSlotPhiSource; ring

/-- Effective axial current increment from the φ source:
`J^eff_extra = α Λ ∂φ / (4π) = E_HQIV` at `E_∗ = 1`. -/
def omaxwellEffectiveAxialCurrentIncrement (couplingLog dphi_ds : ℝ) : ℝ :=
  omaxwellEmSlotPhiSource couplingLog dphi_ds / (4 * Real.pi)

theorem omaxwellEffectiveAxialCurrentIncrement_eq_coronalHQIVField
    (couplingLog dphi_ds : ℝ) :
    omaxwellEffectiveAxialCurrentIncrement couplingLog dphi_ds =
      coronalLongitudinalHQIVField 1 couplingLog dphi_ds := by
  unfold omaxwellEffectiveAxialCurrentIncrement
  rw [omaxwellEmSlotPhiSource_eq_four_pi_coronalHQIVField]
  field_simp

/-!
## §2. Chart identification at the longitudinal axis
-/

/-- Default spatial axis for a 1D conductor / flux tube embedded in `Fin 4`
(index `1` = first spatial chart direction). -/
def longitudinalAxisFin4 : Fin 4 := ⟨1, by decide⟩

/-- Axial gradient read from a continuum scalar `φF` at chart point `c`. -/
noncomputable def longitudinalPhiGradient (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  coordsGradientComponents φF c longitudinalAxisFin4

/-- Chart bundle: promoted O-Maxwell hypotheses at the longitudinal axis, with
explicit coupling log and axial gradient slots. -/
structure LongitudinalOMaxwellChartIdentification (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) (couplingLog dphi_ds : ℝ) : Prop extends
    PromotedOMaxwellChartHypotheses φ_val φF c longitudinalAxisFin4 where
  coupling_log_eq :
    couplingLog = algebraicMaxwellCouplingLog longitudinalAxisFin4
  dphi_ds_eq : dphi_ds = longitudinalPhiGradient φF c

theorem LongitudinalOMaxwellChartIdentification.dphi_ds_eq_grad_phi
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ} {couplingLog dphi_ds : ℝ}
    (h : LongitudinalOMaxwellChartIdentification φ_val φF c couplingLog dphi_ds) :
    dphi_ds = grad_phi longitudinalAxisFin4 := by
  rw [h.dphi_ds_eq, h.grad_slot_eq, longitudinalPhiGradient]

/-- Under chart identification, the emergent O-Maxwell φ correction at the axis
matches `omaxwellEmSlotPhiSource`. -/
theorem emergent_coordsField_em_phiCorrection_eq_omaxwellEmSlot
    {φ_val : ℝ} (_J_src : Fin 8 → Fin 4 → ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (couplingLog dphi_ds : ℝ)
    (h : LongitudinalOMaxwellChartIdentification φ_val φF c couplingLog dphi_ds) :
    alpha * algebraicMaxwellCouplingLog longitudinalAxisFin4 *
        coordsGradientComponents φF c longitudinalAxisFin4 =
      omaxwellEmSlotPhiSource couplingLog dphi_ds := by
  rw [omaxwellEmSlotPhiSource]
  rw [h.coupling_log_eq, h.dphi_ds_eq, longitudinalPhiGradient]

/-!
## §3. Carrier force and additive momentum channels
-/

/-- Total axial carrier force density (Ohmic + HQIV). -/
def longitudinalCarrierForceDensity (nq J sigma Estar couplingLog dphi_ds : ℝ) : ℝ :=
  coronalLongitudinalForceDensity nq J sigma Estar couplingLog dphi_ds

theorem longitudinalCarrierForceDensity_eq_nq_effective
    (nq J sigma Estar couplingLog dphi_ds : ℝ) :
    longitudinalCarrierForceDensity nq J sigma Estar couplingLog dphi_ds =
      nq * coronalEffectiveAxialField J sigma Estar couplingLog dphi_ds := by
  rfl

/-- Additive decomposition: Ohmic + HQIV channels. -/
theorem longitudinalCarrierForceDensity_add_decomposition
    (nq J sigma Estar couplingLog dphi_ds : ℝ) :
    longitudinalCarrierForceDensity nq J sigma Estar couplingLog dphi_ds =
      nq * ohmicAxialField J sigma +
        nq * coronalLongitudinalHQIVField Estar couplingLog dphi_ds := by
  unfold longitudinalCarrierForceDensity coronalLongitudinalForceDensity
    coronalEffectiveAxialField
  ring

theorem longitudinalCarrierForceDensity_ohmic_only
    (nq J sigma Estar couplingLog : ℝ) :
    longitudinalCarrierForceDensity nq J sigma Estar couplingLog 0 =
      nq * ohmicAxialField J sigma := by
  unfold longitudinalCarrierForceDensity coronalLongitudinalForceDensity
    coronalEffectiveAxialField
  rw [coronalLongitudinalHQIVField_zero_of_dphi_zero]
  ring

theorem longitudinalCarrierForceDensity_hqiv_only
    (nq Estar couplingLog dphi_ds : ℝ) :
    longitudinalCarrierForceDensity nq 0 1 Estar couplingLog dphi_ds =
      nq * coronalLongitudinalHQIVField Estar couplingLog dphi_ds := by
  unfold longitudinalCarrierForceDensity coronalLongitudinalForceDensity
    coronalEffectiveAxialField ohmicAxialField
  simp [ohmicAxialField]

/-!
## §4. Directional Maxwell stress ↔ carrier force
-/

/-- Coefficient identification `κ_L ρ = nq E_∗ · α/(4π)` linking the rank-one stress
driver to the carrier HQIV field (explicit closure, not derived from kinetics). -/
structure LongitudinalStressCoefficientIdentification where
  kappaL : ℝ
  rho : ℝ
  nq : ℝ
  Estar : ℝ
  coeff_eq : kappaL * rho = nq * Estar * (alpha / (4 * Real.pi))

theorem LongitudinalStressCoefficientIdentification.force_eq_stress_driver
    (h : LongitudinalStressCoefficientIdentification) (couplingLog dphi_ds : ℝ) :
    h.kappaL * h.rho * couplingLog * dphi_ds =
      h.nq * coronalLongitudinalHQIVField h.Estar couplingLog dphi_ds := by
  unfold coronalLongitudinalHQIVField
  calc
    h.kappaL * h.rho * couplingLog * dphi_ds =
        (h.kappaL * h.rho) * (couplingLog * dphi_ds) := by ring
    _ = (h.nq * h.Estar * (alpha / (4 * Real.pi))) * (couplingLog * dphi_ds) := by
      rw [h.coeff_eq]
    _ = h.nq * (h.Estar * (alpha / (4 * Real.pi)) * couplingLog * dphi_ds) := by ring

/-- Axial diagonal of the rank-one stress tensor when the direction is unit along
component `0`. -/
theorem hqivLongitudinalStressTensor3_axis0_diagonal
    (kappaL rho couplingLog dphi_ds : ℝ) (direction : Fin 3 → ℝ) :
    hqivLongitudinalStressTensor3 kappaL rho couplingLog dphi_ds direction 0 0 =
      kappaL * rho * couplingLog * dphi_ds * direction 0 * direction 0 := by
  rfl

/-- Under coefficient identification and unit axis direction, stress diagonal equals
carrier HQIV force density. -/
theorem longitudinalStressDiagonal_eq_carrierHQIVForce
    (h : LongitudinalStressCoefficientIdentification) (couplingLog dphi_ds : ℝ)
    (direction : Fin 3 → ℝ) (hunit : direction 0 * direction 0 = 1) :
    hqivLongitudinalStressTensor3 h.kappaL h.rho couplingLog dphi_ds direction 0 0 =
      h.nq * coronalLongitudinalHQIVField h.Estar couplingLog dphi_ds := by
  rw [hqivLongitudinalStressTensor3_axis0_diagonal]
  have hmul :
      h.kappaL * h.rho * couplingLog * dphi_ds * direction 0 * direction 0 =
        h.kappaL * h.rho * (couplingLog * dphi_ds) := by
    ring_nf
    rw [pow_two, hunit, mul_one]
  rw [hmul]
  convert LongitudinalStressCoefficientIdentification.force_eq_stress_driver h couplingLog dphi_ds using 1
  ring

/-!
## §5. Work-rate / Poynting analogue (J·E)
-/

/-- Axial work-rate density `q̇ = f_∥ v_∥`. -/
def longitudinalWorkRateDensity (nq J sigma Estar couplingLog dphi_ds v_parallel : ℝ) : ℝ :=
  coronalHeatingRateDensity nq J sigma Estar couplingLog dphi_ds v_parallel

theorem longitudinalWorkRateDensity_eq_force_times_velocity
    (nq J sigma Estar couplingLog dphi_ds v_parallel : ℝ) :
    longitudinalWorkRateDensity nq J sigma Estar couplingLog dphi_ds v_parallel =
      longitudinalCarrierForceDensity nq J sigma Estar couplingLog dphi_ds * v_parallel := by
  rfl

theorem longitudinalWorkRateDensity_eq_nq_v_effective
    (nq J sigma Estar couplingLog dphi_ds v_parallel : ℝ) :
    longitudinalWorkRateDensity nq J sigma Estar couplingLog dphi_ds v_parallel =
      nq * v_parallel * coronalEffectiveAxialField J sigma Estar couplingLog dphi_ds := by
  unfold longitudinalWorkRateDensity coronalHeatingRateDensity
    coronalLongitudinalForceDensity coronalEffectiveAxialField
  ring

theorem longitudinalWorkRateDensity_classical_flat_limit
    (nq J sigma Estar couplingLog v_parallel : ℝ) :
    longitudinalWorkRateDensity nq J sigma Estar couplingLog 0 v_parallel =
      nq * v_parallel * (J / sigma) := by
  unfold longitudinalWorkRateDensity
  rw [coronalHeatingRateDensity_classical_flat_limit]
  ring

/-!
## §6. Momentum balance bundles
-/

/-- Explicit resistive-media momentum budget along the axis: total force density is
the sum of Ohmic and HQIV carrier channels. -/
structure LongitudinalMaxwellMomentumBalance (nq J sigma Estar couplingLog dphi_ds : ℝ) : Prop where
  total_eq :
    longitudinalCarrierForceDensity nq J sigma Estar couplingLog dphi_ds =
      nq * ohmicAxialField J sigma +
        nq * coronalLongitudinalHQIVField Estar couplingLog dphi_ds

theorem LongitudinalMaxwellMomentumBalance.mk'
    (nq J sigma Estar couplingLog dphi_ds : ℝ) :
    LongitudinalMaxwellMomentumBalance nq J sigma Estar couplingLog dphi_ds where
  total_eq := longitudinalCarrierForceDensity_add_decomposition nq J sigma Estar couplingLog dphi_ds

theorem LongitudinalMaxwellMomentumBalance.classical_limit
    {nq J sigma Estar couplingLog : ℝ}
    (h : LongitudinalMaxwellMomentumBalance nq J sigma Estar couplingLog 0) :
    longitudinalCarrierForceDensity nq J sigma Estar couplingLog 0 =
      nq * ohmicAxialField J sigma := by
  rw [h.total_eq, coronalLongitudinalHQIVField_zero_of_dphi_zero]
  ring

/-- Bundle linking O-Maxwell chart data to the carrier momentum balance. -/
structure OMaxwellLongitudinalMomentumBridge (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) (nq J sigma Estar couplingLog dphi_ds : ℝ) : Prop where
  chart : LongitudinalOMaxwellChartIdentification φ_val φF c couplingLog dphi_ds
  momentum : LongitudinalMaxwellMomentumBalance nq J sigma Estar couplingLog dphi_ds

theorem OMaxwellLongitudinalMomentumBridge.natural_source_eq_four_pi_field
    {φ_val : ℝ} {φF : (Fin 4 → ℝ) → ℝ} {c : Fin 4 → ℝ}
    {nq J sigma Estar couplingLog dphi_ds : ℝ}
    (_h : OMaxwellLongitudinalMomentumBridge φ_val φF c nq J sigma Estar couplingLog dphi_ds) :
    omaxwellEmSlotPhiSource couplingLog dphi_ds =
      4 * Real.pi * coronalLongitudinalHQIVField 1 couplingLog dphi_ds :=
  omaxwellEmSlotPhiSource_eq_four_pi_coronalHQIVField couplingLog dphi_ds

/-- Discharged honesty ledger for agents (all rows proved above). -/
structure LongitudinalMomentumBridgeHonestyLedger : Prop where
  source_bridge : ∀ couplingLog dphi_ds,
    omaxwellEmSlotPhiSource couplingLog dphi_ds =
      4 * Real.pi * coronalLongitudinalHQIVField 1 couplingLog dphi_ds
  additive_momentum : ∀ nq J sigma Estar couplingLog dphi_ds,
    LongitudinalMaxwellMomentumBalance nq J sigma Estar couplingLog dphi_ds
  work_rate : ∀ nq J sigma Estar couplingLog dphi_ds v_parallel,
    longitudinalWorkRateDensity nq J sigma Estar couplingLog dphi_ds v_parallel =
      longitudinalCarrierForceDensity nq J sigma Estar couplingLog dphi_ds * v_parallel

theorem longitudinalMomentumBridgeHonestyLedger_discharged :
    LongitudinalMomentumBridgeHonestyLedger where
  source_bridge := omaxwellEmSlotPhiSource_eq_four_pi_coronalHQIVField
  additive_momentum := fun nq J sigma Estar couplingLog dphi_ds =>
    LongitudinalMaxwellMomentumBalance.mk' nq J sigma Estar couplingLog dphi_ds
  work_rate := fun nq J sigma Estar couplingLog dphi_ds v_parallel =>
    longitudinalWorkRateDensity_eq_force_times_velocity
      nq J sigma Estar couplingLog dphi_ds v_parallel

/-!
## §7. Fluid vacuum source is a distinct channel
-/

/-- The axial fluid vacuum momentum source (`g_vac`) and the carrier HQIV force
(`nq E_HQIV`) are different slots: one is gradient-of-product, the other is
`nq` times the effective axial field.  Equality holds only under extra hypotheses
(e.g.\ vanishing `δ̇θ′` gradient with oriented `∂φ` only in the EM slot). -/
theorem longitudinalCarrier_hqiv_ne_vacuumSource_without_hypothesis :
    (∀ nq Estar couplingLog dphi_ds phi dotTheta ddot_ds,
      nq * coronalLongitudinalHQIVField Estar couplingLog dphi_ds =
        coronalAxialVacuumMomentumSource phi dotTheta dphi_ds ddot_ds) → False := by
  intro h
  have h1 := h 1 1 1 1 0 1 0
  rw [coronalLongitudinalHQIVField_alpha_3_5,
      coronalAxialVacuumMomentumSource_eq_minus_one_fifteenth] at h1
  have hpos : 0 < 3 / (20 * Real.pi) := by positivity
  linarith [h1, hpos, (show (-(1 / 15 : ℝ)) < 0 by norm_num)]

/-- When both gradients vanish, both channels vanish (shared flat limit). -/
theorem longitudinal_channels_zero_of_flat_gradients
    (nq J sigma Estar couplingLog phi dotTheta v_parallel : ℝ) :
    longitudinalCarrierForceDensity nq J sigma Estar couplingLog 0 =
      nq * ohmicAxialField J sigma ∧
      coronalAxialVacuumMomentumSource phi dotTheta 0 0 = 0 ∧
      longitudinalWorkRateDensity nq J sigma Estar couplingLog 0 v_parallel =
        nq * v_parallel * (J / sigma) := by
  refine ⟨?_, ?_, ?_⟩
  · exact longitudinalCarrierForceDensity_ohmic_only nq J sigma Estar couplingLog
  · exact coronalAxialVacuumMomentumSource_zero_of_grad_zero phi dotTheta
  · rw [longitudinalWorkRateDensity_classical_flat_limit]

end

end Hqiv.Physics
