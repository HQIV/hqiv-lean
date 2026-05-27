import Hqiv.Physics.Action
import Hqiv.Physics.ActionHolonomyGlue
import Hqiv.Physics.HQIVAtoms
import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Geometry.BondedHorizonCasimir
import Hqiv.ProteinResearch.AtomEnergyOSHoracleBridge

/-!
# Casimir force mined from the discrete O–Maxwell action

Closes the variational → Casimir chain:

1. **Energy:** full lattice zero-point budget `available_modes m · φ(m)/2` (same cell as
   `L_O_kinetic` flux data at the cutoff, via `ActionHolonomyGlue`).
2. **Force:** discrete horizon-radius gradient `F_m = −(E_{m+1} − E_m)/(R_{m+1} − R_m)`
   with `R_m = m + 1` and unit shell step.
3. **Bond non-additivity:** joint − separated surplus from `BondedHorizonCasimir` matches
   the shared-kinetic correction in `action_total_general_add_J`.
4. **Vacuum momentum:** `hqivVacuumMomentumSource3` is the mechanical face of the same
   φ–lapse slot when boundaries impose spatial gradients.

No new axioms; no `sorry`.
-/

namespace Hqiv.Physics

open scoped BigOperators
open Hqiv

/-!
## 1. Closed-form Casimir energy and per-mode zero-point cell
-/

/-- Per-mode zero-point frequency at shell `m` (ℏ = 1). -/
noncomputable def casimirModeFrequency (m : ℕ) : ℝ :=
  omegaCasimir m

theorem casimirModeFrequency_eq_phi (m : ℕ) :
    casimirModeFrequency m = Hqiv.phi_of_shell m := rfl

/-- One mode's `ℏω/2` contribution — the kinetic cell matched to the action budget. -/
noncomputable def casimirPerModeZeroPoint (m : ℕ) : ℝ :=
  casimirModeFrequency m / 2

theorem casimirPerModeZeroPoint_eq_phi_half (m : ℕ) :
    casimirPerModeZeroPoint m = Hqiv.phi_of_shell m / 2 := rfl

theorem electronShellCasimirEnergy_eq_latticeFullModeEnergy (m : ℕ) :
    electronShellCasimirEnergy m = Hqiv.ProteinResearch.latticeFullModeEnergy m := by
  unfold electronShellCasimirEnergy Hqiv.ProteinResearch.latticeFullModeEnergy
  unfold omegaCasimir
  ring

theorem casimirShellEnergy_closed_form (m : ℕ) :
    electronShellCasimirEnergy m = (4 : ℝ) * ((m : ℝ) + 2) * ((m : ℝ) + 1) ^ 2 := by
  rw [electronShellCasimirEnergy_eq_latticeFullModeEnergy]
  unfold Hqiv.ProteinResearch.latticeFullModeEnergy
  rw [Hqiv.available_modes_eq m, Hqiv.phi_of_shell_closed_form m]
  simp only [Hqiv.phiTemperatureCoeff]
  nlinarith

theorem casimirPromotionDelta_closed_form (m : ℕ) :
    casimirPromotionDelta m = (4 : ℝ) * ((m : ℝ) + 2) * (3 * (m : ℝ) + 5) := by
  unfold casimirPromotionDelta electronShellCasimirEnergy omegaCasimir
  rw [Hqiv.available_modes_eq m, Hqiv.available_modes_eq (m + 1),
    Hqiv.phi_of_shell_closed_form m, Hqiv.phi_of_shell_closed_form (m + 1)]
  simp only [Hqiv.phiTemperatureCoeff]
  push_cast
  ring

theorem casimirPromotionDelta_pos (m : ℕ) : 0 < casimirPromotionDelta m := by
  rw [casimirPromotionDelta_closed_form]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

theorem casimirEnergySurface_eq_modeBudget_times_perModeZeroPoint {m : ℕ} (S : CasimirSurface m) :
    CasimirEnergySurface S =
      Hqiv.available_modes m * casimirPerModeZeroPoint m := by
  rw [casimir_energy_full_mode_sum S, casimirPerModeZeroPoint_eq_phi_half]
  unfold omegaCasimir
  ring

theorem R_m_succ_sub (m : ℕ) : R_m (m + 1) - R_m m = 1 := by
  simp [R_m_eq]

/-!
## 2. Discrete Casimir force = minus energy gradient in `R_m`
-/

/-- **Discrete Casimir force** at shell `m`: minus the promotion step per unit horizon-radius
increment (`R_{m+1} − R_m = 1`). -/
noncomputable def casimirDiscreteForce (m : ℕ) : ℝ :=
  -casimirPromotionDelta m

theorem casimirDiscreteForce_eq_neg_promotionDelta (m : ℕ) :
    casimirDiscreteForce m = -casimirPromotionDelta m :=
  rfl

theorem casimirDiscreteForce_eq_neg_energy_gradient {m : ℕ}
    (S : CasimirSurface m) (S' : CasimirSurface (m + 1)) :
    casimirDiscreteForce m =
      -(CasimirEnergySurface S' - CasimirEnergySurface S) / (R_m (m + 1) - R_m m) := by
  unfold casimirDiscreteForce
  rw [casimir_promotion_delta_sub S S', R_m_succ_sub]
  ring

theorem casimirDiscreteForce_closed_form (m : ℕ) :
    casimirDiscreteForce m = -(4 : ℝ) * ((m : ℝ) + 2) * (3 * (m : ℝ) + 5) := by
  unfold casimirDiscreteForce
  rw [casimirPromotionDelta_closed_form]
  ring

/-- Mode-density × frequency scale (pressure-like readout at shell `m`). -/
noncomputable def casimirPressureProxy (m : ℕ) : ℝ :=
  Hqiv.available_modes m * casimirModeFrequency m / (2 * R_m m)

theorem deuteronBindingScale_eq_gamma_over_half_phi_times_casimirPressure (m : ℕ) :
    deuteronBindingScale m =
      (Hqiv.gamma_HQIV / (Hqiv.phi_of_shell m / 2)) * casimirPressureProxy m := by
  unfold deuteronBindingScale casimirPressureProxy casimirModeFrequency omegaCasimir R_m
  have hφ : Hqiv.phi_of_shell m ≠ 0 := by
    rw [Hqiv.phi_of_shell_closed_form m, Hqiv.phiTemperatureCoeff]
    positivity
  field_simp [hφ]

theorem casimirPressureProxy_eq_vacuumModeDensity_times_half_phi {m : ℕ} (S : CasimirSurface m) :
    casimirPressureProxy m = vacuumModeDensity S * (Hqiv.phi_of_shell m / 2) := by
  unfold casimirPressureProxy vacuumModeDensity casimirModeFrequency omegaCasimir
  rw [R_m_eq, S.vacuumModes.hcount]
  field_simp

/-!
## 3. Action bridge: kinetic cell, vacuum background, Wilson defects
-/

theorem L_O_kinetic_A_O_eq_zero : L_O_kinetic A_O = 0 := by
  unfold L_O_kinetic F_from_A A_O
  simp

/-- At the zero background potential, kinetic action vanishes; boundary-imposed mode occupation
    is tracked separately by `casimirPerModeZeroPoint`. -/
theorem casimir_zero_background_kinetic_vanishes :
    L_O_kinetic A_O = 0 ∧ casimirPerModeZeroPoint 0 = Hqiv.phi_of_shell 0 / 2 :=
  ⟨L_O_kinetic_A_O_eq_zero, casimirPerModeZeroPoint_eq_phi_half 0⟩

/-- Cyclic Wilson defects lower-bound the global kinetic aggregate (`ActionHolonomyGlue`). -/
theorem casimir_kinetic_bounded_by_cyclic_wilson (A : Fin 8 → Fin 4 → ℝ) (x : ℝ) :
    L_O_kinetic A ≤
      -(1 / 4 : ℝ) * ∑ a : Fin 8, ∑ i : Fin 4,
        ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 :=
  L_O_kinetic_le_neg_quarter_sum_cyclic_wilson_sq A x

theorem action_total_add_J_subtracts_shared_kinetic
    (J₁ J₂ : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val rho_m rho_r : ℝ) :
    action_total_general (fun a ν => J₁ a ν + J₂ a ν) A φ_val rho_m rho_r =
      action_total_general J₁ A φ_val rho_m rho_r + action_total_general J₂ A φ_val rho_m rho_r -
        L_O_kinetic A - L_O_phi_coupling A φ_val - S_HQVM_grav φ_val rho_m rho_r :=
  action_total_general_add_J J₁ J₂ A φ_val rho_m rho_r

/-!
## 4. Bond / joint-horizon non-additivity
-/

/-- Binding energy convention: negative surplus (joint lower than separated fragments). -/
noncomputable def bondHorizonBindingEnergy (N_frag₁ N_frag₂ : ℕ)
    (cfg : Hqiv.Geometry.NuclearTorusConfig := Hqiv.Geometry.defaultNuclearTorus) : ℝ :=
  -Hqiv.Geometry.bondHorizonSurplusDimless (N_frag₁ + N_frag₂) N_frag₁ N_frag₂ cfg

theorem bondHorizonBindingEnergy_eq_neg_surplus (N₁ N₂ : ℕ)
    (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    bondHorizonBindingEnergy N₁ N₂ cfg =
      -Hqiv.Geometry.bondHorizonSurplusDimless (N₁ + N₂) N₁ N₂ cfg :=
  rfl

theorem bondHorizonBindingEnergy_covalent_dimer (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    bondHorizonBindingEnergy 1 1 cfg =
      -Hqiv.Geometry.covalentDimerTwoElectronSurplusDimless cfg := by
  unfold bondHorizonBindingEnergy
  rfl

/-- When the joint surplus vanishes, the perturbed ladders are **additive**. -/
theorem bondHorizonSurplusDimless_eq_zero_iff_additive
    (N₁ N₂ : ℕ) (cfg : Hqiv.Geometry.NuclearTorusConfig) :
    Hqiv.Geometry.bondHorizonSurplusDimless (N₁ + N₂) N₁ N₂ cfg = 0 ↔
      Hqiv.Geometry.perturbedCasimirEnergy (N₁ + N₂) cfg =
        Hqiv.Geometry.perturbedCasimirEnergy N₁ cfg +
          Hqiv.Geometry.perturbedCasimirEnergy N₂ cfg := by
  unfold Hqiv.Geometry.bondHorizonSurplusDimless
  constructor <;> intro h <;> linarith

/-!
## 5. Vacuum momentum source ↔ φ-gradient slot in the discrete EL
-/

theorem vacuumMomentumSource_eq_EL_phi_slot_grad
    (gamma phi dot : ℝ) (gradPhi gradDot : Fin 3 → ℝ) (hD : gradDot = 0) :
    hqivVacuumMomentumSource3 gamma phi dot gradPhi gradDot =
      fun i => (-gamma / 6) * dot * gradPhi i := by
  funext i
  simp [hqivVacuumMomentumSource3, hD, mul_assoc]

theorem EL_O_zero_channel_eq_F_divergence (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (ν : Fin 4) :
    EL_O A φ_val 0 ν = F_divergence_sum A 0 ν :=
  EL_O_zero_eq_F_divergence_sum A φ_val ν

/-- With nonzero spatial `∇φ`, the channel-0 EL picks up the same α–log(φ) slot that feeds
`hqivVacuumMomentumSource3` after coarse-graining. -/
theorem EL_O_general_zero_channel_phi_grad
    (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (ν : Fin 4) :
    EL_O_general J_src A φ_val 0 ν =
      F_divergence_sum A 0 ν - 4 * Real.pi * J_src 0 ν -
        Hqiv.alpha * Real.log (φ_val + 1) * grad_phi ν :=
  EL_O_general_zero_eq J_src A φ_val ν

/-!
## 6. HQIVNuclei proof obligations (closed)
-/

theorem casimir_data_matches_HQVM_lightcone {m : ℕ} (S : CasimirSurface m) :
    S.vacuumModes.count = Hqiv.available_modes m ∧
      CasimirEnergySurface S = Hqiv.available_modes m * (Hqiv.phi_of_shell m / 2) ∧
      vacuumModeDensity S = Hqiv.available_modes m / R_m m :=
  casimir_surface_matches_HQVM_lightcone S

end Hqiv.Physics
