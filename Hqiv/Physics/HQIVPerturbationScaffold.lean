import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMCLASSBridge
import Hqiv.Geometry.HQVMPerturbations
import Hqiv.Physics.LightConeFundamentalsPillars
import Hqiv.Physics.LightConeMaxwellQFTBridge

/-!
# HQIV perturbation scaffold (shell-indexed background)

**Read first:** [AGENTS/HQIV_PERTURBATION_THEORY_ROADMAP.md](../../AGENTS/HQIV_PERTURBATION_THEORY_ROADMAP.md).

`HQVMPerturbations` already proves **observer-centric** linear response for the lapse and for
`phi_of_T`. This module **specializes** the temperature slot to the discrete horizon ladder `T m`
from `AuxiliaryField`, so perturbations are explicitly **background + increment** on the same
axiom chain as the light cone.

**Not claimed:** Bardeen potentials, gauge-fixed GR perturbations, or Boltzmann hierarchies — see
module doc of `HQVMPerturbations`.

## Links

* **Pillar C (Kubo hooks):** `KuboHQIVSpectralWeight` in `LightConeFundamentalsPillars`; the slope
  `deriv phi_of_T (T m)` is the natural discrete “∂φ/∂Θ” factor at shell `m`.
* **Remainder:** `HQVM_lapse_increment_eq` isolates the only bilinear correction `δφ * δt` beyond
  `linearizedHQVM_lapse`.
-/

namespace Hqiv.Physics

open Hqiv
open Filter
open scoped Topology

noncomputable section

/-- `∂_Θ phi_of_T` evaluated on the shell temperature `T m` (same ladder as `phi_of_shell`). -/
noncomputable def kuboPhiSlopeAtShell (m : ℕ) : ℝ :=
  deriv phi_of_T (T m)

theorem kuboPhiSlopeAtShell_eq (m : ℕ) :
    kuboPhiSlopeAtShell m = -phiTemperatureCoeff / (T m) ^ 2 := by
  unfold kuboPhiSlopeAtShell
  exact deriv_phi_of_T (T m) (ne_of_gt (T_pos m))

/-- Exact `phi_of_T` increment when the background temperature is `T m`. -/
theorem phi_of_T_increment_shell (m : ℕ) (δΘ : ℝ) (hΘ' : T m + δΘ ≠ 0) :
    phi_of_T (T m + δΘ) - phi_of_T (T m) =
      -phiTemperatureCoeff * δΘ / (T m * (T m + δΘ)) :=
  phi_of_T_increment (T m) δΘ (ne_of_gt (T_pos m)) hΘ'

/-- Θ-channel linearized lapse with `Θ = T m` on the auxiliary ladder. -/
theorem linearizedLapse_from_shell (m : ℕ) (t δΘ : ℝ) :
    linearizedLapse_from_Theta (T m) t δΘ = t * (-phiTemperatureCoeff / (T m) ^ 2) * δΘ := by
  exact linearizedLapse_from_Theta_eq_onDomain (T m) t δΘ (ne_of_gt (T_pos m))

theorem linearizedLapse_from_shell_kuboSlope (m : ℕ) (t δΘ : ℝ) :
    linearizedLapse_from_Theta (T m) t δΘ = t * kuboPhiSlopeAtShell m * δΘ := by
  rw [linearizedLapse_from_shell]
  rw [kuboPhiSlopeAtShell_eq]

/--
Observer-side rapidity normalization of the shell-induced `φ` increment.

This does **not** add a new field variable: it uses the existing shell slope
`∂_Θ phi_of_T` at `T m`, and weights the resulting `δφ` by the same doubled
observer-time transport factor that already appears in the light-cone/QFT bridge.
-/
noncomputable def rapidityNormalizedShellPhiIncrement
    (m n : ℕ) (kappaBeta δΘ : ℝ) : ℝ :=
  timeAngleBudgetTransportN kappaBeta n * (kuboPhiSlopeAtShell m * δΘ)

theorem rapidityNormalizedShellPhiIncrement_eq
    (m n : ℕ) (kappaBeta δΘ : ℝ) :
    rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ =
      timeAngleBudgetTransportN kappaBeta n *
        ((-phiTemperatureCoeff / (T m) ^ 2) * δΘ) := by
  rw [rapidityNormalizedShellPhiIncrement, kuboPhiSlopeAtShell_eq]

theorem rapidityNormalizedShellPhiIncrement_eq_exp
    (m n : ℕ) (kappaBeta δΘ : ℝ) :
    rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ =
      Real.exp (-(timeAngleBudgetScaleN n / kappaBeta)) *
        ((-phiTemperatureCoeff / (T m) ^ 2) * δΘ) := by
  rw [rapidityNormalizedShellPhiIncrement_eq, timeAngleBudgetTransportN_eq_exp_neg_div]

theorem rapidityNormalizedShellPhiIncrement_tendsto_zero
    (m : ℕ) (kappaBeta δΘ : ℝ) (hκ : 0 < kappaBeta) :
    Tendsto (fun n : ℕ => rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ) atTop (𝓝 0) := by
  have hconst :
      Tendsto
        (fun n : ℕ =>
          kuboPhiSlopeAtShell m * δΘ)
        atTop
        (𝓝 (kuboPhiSlopeAtShell m * δΘ)) :=
    tendsto_const_nhds
  have hmul :
      Tendsto
        (fun n : ℕ =>
          timeAngleBudgetTransportN kappaBeta n * (kuboPhiSlopeAtShell m * δΘ))
        atTop
        (𝓝 (0 * (kuboPhiSlopeAtShell m * δΘ))) :=
    (timeAngleBudgetTransportN_tendsto_zero kappaBeta hκ).mul hconst
  simpa [rapidityNormalizedShellPhiIncrement] using hmul

/--
The rapidity-normalized shell increment is exactly the shell linear-response channel,
multiplied by the observer-side transport weight.
-/
theorem linearizedLapse_from_shell_rapidityNormalized
    (m n : ℕ) (kappaBeta t δΘ : ℝ) :
    linearizedHQVM_lapse (phi_of_shell m) t 0
        (rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ) 0 =
      timeAngleBudgetTransportN kappaBeta n * linearizedLapse_from_Theta (T m) t δΘ := by
  rw [linearizedHQVM_lapse_phi_channel, rapidityNormalizedShellPhiIncrement,
    linearizedLapse_from_shell_kuboSlope]
  ring

/--
Exact homogeneous lapse increment with rapidity-normalized shell response.

This is the perturbative HQIV statement of “rapidity as observer skew
normalization”: the shell-induced `δφ` enters the exact lapse increment only
through the normalized channel below, with the same bilinear remainder
`δφ * δt` as in the unweighted observer-centric lapse algebra.
-/
theorem HQVM_lapse_increment_shell_rapidityNormalized
    (m n : ℕ) (t δΦ δΘ δt kappaBeta : ℝ) :
    HQVM_lapse δΦ
        (phi_of_shell m + rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ)
        (t + δt) -
      HQVM_lapse 0 (phi_of_shell m) t =
        linearizedHQVM_lapse (phi_of_shell m) t δΦ
          (rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ) δt +
        rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ * δt := by
  simpa using
    HQVM_lapse_increment_homogeneous (phi_of_shell m) t δΦ
      (rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ) δt

/--
Geometry-facing consequence of rapidity-normalized shell response.

The observer-side skew normalization now lands directly in the timelike metric
coefficient `g_tt = -N^2`: the exact metric increment splits into the linearized
metric response to the normalized lapse increment plus the quadratic remainder.
-/
theorem HQVM_g_tt_increment_shell_rapidityNormalized
    (m n : ℕ) (t δΦ δΘ δt kappaBeta : ℝ) :
    HQVM_g_tt
        (HQVM_lapse δΦ
          (phi_of_shell m + rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ)
          (t + δt)) -
      HQVM_g_tt (HQVM_lapse 0 (phi_of_shell m) t) =
        Hqiv.linearizedHQVM_g_tt_from_lapse
          (HQVM_lapse 0 (phi_of_shell m) t)
          (linearizedHQVM_lapse (phi_of_shell m) t δΦ
            (rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ) δt +
            rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ * δt) -
        (linearizedHQVM_lapse (phi_of_shell m) t δΦ
          (rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ) δt +
          rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ * δt) ^ 2 := by
  let Nbg := HQVM_lapse 0 (phi_of_shell m) t
  let Npert :=
    HQVM_lapse δΦ
      (phi_of_shell m + rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ)
      (t + δt)
  have hΔ :
      Npert - Nbg =
        linearizedHQVM_lapse (phi_of_shell m) t δΦ
          (rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ) δt +
        rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ * δt := by
    dsimp [Npert, Nbg]
    exact HQVM_lapse_increment_shell_rapidityNormalized m n t δΦ δΘ δt kappaBeta
  simpa [Npert, Nbg, hΔ] using
    (Hqiv.HQVM_g_tt_increment_eq_of_lapse_increment Nbg Npert)

/--
Pure shell-`φ` rapidity channel for `g_tt`: no explicit `δΦ` or `δt`, only the
normalized shell response enters.
-/
theorem HQVM_g_tt_increment_shell_rapidityNormalized_phiChannel
    (m n : ℕ) (t δΘ kappaBeta : ℝ) :
    HQVM_g_tt
        (HQVM_lapse 0
          (phi_of_shell m + rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ)
          t) -
      HQVM_g_tt (HQVM_lapse 0 (phi_of_shell m) t) =
        Hqiv.linearizedHQVM_g_tt_from_lapse
          (HQVM_lapse 0 (phi_of_shell m) t)
          (timeAngleBudgetTransportN kappaBeta n * linearizedLapse_from_Theta (T m) t δΘ) -
        (timeAngleBudgetTransportN kappaBeta n * linearizedLapse_from_Theta (T m) t δΘ) ^ 2 := by
  let Nbg := HQVM_lapse 0 (phi_of_shell m) t
  let Npert :=
    HQVM_lapse 0
      (phi_of_shell m + rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ)
      t
  have hΔ :
      Npert - Nbg = timeAngleBudgetTransportN kappaBeta n * linearizedLapse_from_Theta (T m) t δΘ := by
    dsimp [Npert, Nbg]
    have hbase :=
      HQVM_lapse_increment_shell_rapidityNormalized m n t 0 δΘ 0 kappaBeta
    calc
      HQVM_lapse 0 (phi_of_shell m + rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ) t -
          HQVM_lapse 0 (phi_of_shell m) t
          = t * rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ := by
              simpa [linearizedHQVM_lapse] using hbase
      _ = timeAngleBudgetTransportN kappaBeta n * linearizedLapse_from_Theta (T m) t δΘ := by
            rw [rapidityNormalizedShellPhiIncrement, linearizedLapse_from_shell_kuboSlope]
            ring
  simpa [Npert, Nbg, hΔ] using
    (Hqiv.HQVM_g_tt_increment_eq_of_lapse_increment Nbg Npert)

/--
Pure shell-`φ` rapidity normalization does not move the spatial coefficient at this rung.

`HQVM_spatial_coeff` depends only on `(a, Φ)`, so when the current perturbation channel
changes only the shell/`φ` slot, the spatial coefficient increment is exactly zero.
-/
theorem HQVM_spatial_coeff_increment_zero_of_pure_phi_channel
    (a Φ : ℝ) :
    HQVM_spatial_coeff (a + 0) (Φ + 0) - HQVM_spatial_coeff a Φ = 0 := by
  simp [HQVM_spatial_coeff]

/--
Paired metric statement for the current rapidity-normalized shell rung.

At this level, observer-skew normalization has a timelike metric landing in `g_tt`,
while the spatial coefficient is unchanged unless extra `δa` / `δΦ` data are supplied.
-/
theorem HQVM_metric_shell_rapidityNormalized_phiChannel_timelikeOnly
    (a : ℝ) (m n : ℕ) (t δΘ kappaBeta : ℝ) :
    (HQVM_g_tt
        (HQVM_lapse 0
          (phi_of_shell m + rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ)
          t) -
      HQVM_g_tt (HQVM_lapse 0 (phi_of_shell m) t) =
        Hqiv.linearizedHQVM_g_tt_from_lapse
          (HQVM_lapse 0 (phi_of_shell m) t)
          (timeAngleBudgetTransportN kappaBeta n * linearizedLapse_from_Theta (T m) t δΘ) -
        (timeAngleBudgetTransportN kappaBeta n * linearizedLapse_from_Theta (T m) t δΘ) ^ 2) ∧
      (HQVM_spatial_coeff (a + 0) (0 + 0) - HQVM_spatial_coeff a 0 = 0) := by
  exact ⟨HQVM_g_tt_increment_shell_rapidityNormalized_phiChannel m n t δΘ kappaBeta,
    HQVM_spatial_coeff_increment_zero_of_pure_phi_channel a 0⟩

/--
Observer-side rapidity normalization of a Newtonian-potential increment.

This is the minimal extra structure needed to let the spatial coefficient move at the
current rung without postulating a separate short-distance continuum dynamics.
-/
noncomputable def rapidityNormalizedPotentialIncrement
    (n : ℕ) (kappaBeta δΦ : ℝ) : ℝ :=
  timeAngleBudgetTransportN kappaBeta n * δΦ

theorem rapidityNormalizedPotentialIncrement_eq_exp
    (n : ℕ) (kappaBeta δΦ : ℝ) :
    rapidityNormalizedPotentialIncrement n kappaBeta δΦ =
      Real.exp (-(timeAngleBudgetScaleN n / kappaBeta)) * δΦ := by
  rw [rapidityNormalizedPotentialIncrement, timeAngleBudgetTransportN_eq_exp_neg_div]

theorem rapidityNormalizedPotentialIncrement_tendsto_zero
    (kappaBeta δΦ : ℝ) (hκ : 0 < kappaBeta) :
    Tendsto (fun n : ℕ => rapidityNormalizedPotentialIncrement n kappaBeta δΦ) atTop (𝓝 0) := by
  have hconst : Tendsto (fun _n : ℕ => δΦ) atTop (𝓝 δΦ) := tendsto_const_nhds
  have hmul :
      Tendsto
        (fun n : ℕ => timeAngleBudgetTransportN kappaBeta n * δΦ)
        atTop
        (𝓝 (0 * δΦ)) :=
    (timeAngleBudgetTransportN_tendsto_zero kappaBeta hκ).mul hconst
  simpa [rapidityNormalizedPotentialIncrement] using hmul

/--
Spatial coefficient under a rapidity-normalized potential channel.

This is the first legitimate way the current observer-budget transport law moves the
spatial side: keep `δa = 0`, supply a normalized `δΦ`, and use the exact HQVM
spatial-coefficient increment scaffold.
-/
theorem HQVM_spatial_coeff_increment_rapidityNormalizedPotential
    (a Φ : ℝ) (n : ℕ) (kappaBeta δΦ : ℝ) :
    HQVM_spatial_coeff (a + 0) (Φ + rapidityNormalizedPotentialIncrement n kappaBeta δΦ) -
      HQVM_spatial_coeff a Φ =
        Hqiv.linearizedHQVM_spatial_coeff a Φ 0
          (rapidityNormalizedPotentialIncrement n kappaBeta δΦ) +
        (HQVM_spatial_coeff (a + 0) (Φ + rapidityNormalizedPotentialIncrement n kappaBeta δΦ) -
          HQVM_spatial_coeff a Φ -
          Hqiv.linearizedHQVM_spatial_coeff a Φ 0
            (rapidityNormalizedPotentialIncrement n kappaBeta δΦ)) := by
  exact Hqiv.HQVM_spatial_coeff_increment_eq a Φ 0
    (rapidityNormalizedPotentialIncrement n kappaBeta δΦ)

theorem HQVM_spatial_coeff_increment_rapidityNormalizedPotential_linear
    (a Φ : ℝ) (n : ℕ) (kappaBeta δΦ : ℝ) :
    Hqiv.linearizedHQVM_spatial_coeff a Φ 0
      (rapidityNormalizedPotentialIncrement n kappaBeta δΦ) =
        -2 * a ^ 2 * rapidityNormalizedPotentialIncrement n kappaBeta δΦ := by
  unfold Hqiv.linearizedHQVM_spatial_coeff
  ring

theorem HQVM_spatial_coeff_increment_rapidityNormalizedPotential_homogeneous
    (a : ℝ) (n : ℕ) (kappaBeta δΦ : ℝ) :
    Hqiv.linearizedHQVM_spatial_coeff a 0 0
      (rapidityNormalizedPotentialIncrement n kappaBeta δΦ) =
        -2 * a ^ 2 * rapidityNormalizedPotentialIncrement n kappaBeta δΦ := by
  rw [HQVM_spatial_coeff_increment_rapidityNormalizedPotential_linear]

/--
Paired metric statement with the minimal extra spatial structure added.

The timelike side is still driven by the shell/`φ` channel, while the spatial side now
moves only because an observer-budget-normalized `δΦ` was explicitly supplied.
-/
theorem HQVM_metric_shell_rapidityNormalized_withPotentialChannel
    (a : ℝ) (m n : ℕ) (t δΘ kappaBeta δΦ : ℝ) :
    (HQVM_g_tt
        (HQVM_lapse 0
          (phi_of_shell m + rapidityNormalizedShellPhiIncrement m n kappaBeta δΘ)
          t) -
      HQVM_g_tt (HQVM_lapse 0 (phi_of_shell m) t) =
        Hqiv.linearizedHQVM_g_tt_from_lapse
          (HQVM_lapse 0 (phi_of_shell m) t)
          (timeAngleBudgetTransportN kappaBeta n * linearizedLapse_from_Theta (T m) t δΘ) -
        (timeAngleBudgetTransportN kappaBeta n * linearizedLapse_from_Theta (T m) t δΘ) ^ 2) ∧
      (HQVM_spatial_coeff (a + 0) (0 + rapidityNormalizedPotentialIncrement n kappaBeta δΦ) -
        HQVM_spatial_coeff a 0 =
          Hqiv.linearizedHQVM_spatial_coeff a 0 0
            (rapidityNormalizedPotentialIncrement n kappaBeta δΦ) +
          (HQVM_spatial_coeff (a + 0) (0 + rapidityNormalizedPotentialIncrement n kappaBeta δΦ) -
            HQVM_spatial_coeff a 0 -
            Hqiv.linearizedHQVM_spatial_coeff a 0 0
              (rapidityNormalizedPotentialIncrement n kappaBeta δΦ))) := by
  exact ⟨HQVM_g_tt_increment_shell_rapidityNormalized_phiChannel m n t δΘ kappaBeta,
    HQVM_spatial_coeff_increment_rapidityNormalizedPotential a 0 n kappaBeta δΦ⟩

end

end Hqiv.Physics
