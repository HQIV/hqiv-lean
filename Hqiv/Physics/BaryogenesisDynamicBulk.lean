import Hqiv.Physics.DynamicBBNBaryogenesis
import Hqiv.Physics.BaryogenesisWitness
import Hqiv.Physics.BaryogenesisEtaPaper
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.NuclearOutsideTemperatureDynamics
import Hqiv.QuantumChemistry.DynamicBindingChart
import Mathlib.Data.Real.Basic

/-!
# Dynamic bulk baryogenesis readouts (Lean mirror)

Typed packaging for the per-shell bulk integrator witness
(`scripts/hqiv_dynamic_bulk_bbn.py` → `data/dynamic_bulk_bbn_v2.json`):

* **Colour-singlet projector** `1/3` on the strong octonion channel;
* **Baryon fraction** `Ω_b = Ω_m · (4/8) · (1/3)`;
* **Comparison-layer η bridge** from `(Ω_b, H₀, T_CMB)` (not a first-principles η derivation);
* **Dynamic vital bundle** wiring ratio theorems, binding correction, and bulk budget.

Numeric equality with Python is a witness certificate (`hqiv_baryogenesis_witness.py`), not
an analytic integral theorem.
-/

namespace Hqiv.Physics

open Hqiv

/-!
## Colour-singlet projector and baryon channel fraction
-/

/-- Colour-singlet occupancy on the strong channel (Python `COLOR_SINGLET_FRACTION`). -/
noncomputable def colorSingletFraction : ℝ := 1 / 3

theorem colorSingletFraction_eq_one_third : colorSingletFraction = (1 : ℝ) / 3 := rfl

/-- Baryon track fraction: strong-channel weight × colour-singlet projector. -/
noncomputable def baryonStrongColorFraction : ℝ :=
  strongChannelFraction * colorSingletFraction

theorem baryonStrongColorFraction_eq_one_sixth :
    baryonStrongColorFraction = (1 : ℝ) / 6 := by
  unfold baryonStrongColorFraction colorSingletFraction
  rw [strongChannelFraction_eq_four_eighths]
  norm_num

/-- Comparison-layer baryon fraction from total matter fraction. -/
noncomputable def omegaBFromOmegaM (omega_m : ℝ) : ℝ :=
  omega_m * baryonStrongColorFraction

theorem omegaBFromOmegaM_le_omega_m (omega_m : ℝ) (h : 0 ≤ omega_m) :
    omegaBFromOmegaM omega_m ≤ omega_m := by
  unfold omegaBFromOmegaM baryonStrongColorFraction colorSingletFraction
  rw [strongChannelFraction_eq_four_eighths]
  nlinarith

theorem omegaBFromOmegaM_nonneg (omega_m : ℝ) (h : 0 ≤ omega_m) :
    0 ≤ omegaBFromOmegaM omega_m := by
  unfold omegaBFromOmegaM baryonStrongColorFraction colorSingletFraction
  rw [strongChannelFraction_eq_four_eighths]
  nlinarith

/-!
## Comparison-layer η from late-universe inputs
-/

/-- Baryon number density from Ω_b and critical density (SI chart). -/
noncomputable def baryonNumberDensityFromOmegaB
    (omega_b rho_crit_kg_m3 m_proton_kg : ℝ) : ℝ :=
  omega_b * rho_crit_kg_m3 / m_proton_kg

/-- CMB photon number density at temperature `T_K` (SI chart; ζ(3) factor). -/
noncomputable def cmbPhotonNumberDensity (T_K zeta3 hbar_SI k_B_SI c_SI : ℝ) : ℝ :=
  (2 * zeta3 / Real.pi ^ 2) * ((k_B_SI * T_K) / (hbar_SI * c_SI)) ^ 3

/-- Late-universe η readout: n_b / n_γ. -/
noncomputable def etaComparisonFromCosmology
    (omega_b rho_crit_kg_m3 m_proton_kg T_K zeta3 hbar_SI k_B_SI c_SI : ℝ) : ℝ :=
  baryonNumberDensityFromOmegaB omega_b rho_crit_kg_m3 m_proton_kg /
    cmbPhotonNumberDensity T_K zeta3 hbar_SI k_B_SI c_SI

/-!
## Dynamic η and binding-correction links
-/

/-- Dynamic η at lock-in uses the dimensionless binding correction. -/
theorem eta_at_horizon_dynamic_lockin_eq
    (h : 0 < curvature_integral m_lockin) :
    eta_at_horizon_dynamic m_lockin m_lockin =
      eta_paper * (1 + baryogenesis_binding_curvature_correction_dimless) := by
  have hη : eta_at_horizon m_lockin m_lockin = eta_paper := eta_lockin_calibration h
  unfold eta_at_horizon_dynamic
  rw [hη]

def baryogenesis_dynamic_bulk_vital_holds (omegaMRel : ℝ) : Prop :=
  (colorSingletFraction = (1 : ℝ) / 3) ∧
  (baryonStrongColorFraction = (1 : ℝ) / 6) ∧
  (baryogenesisCurvatureBudgetAtShell m_lockin omegaMRel = 1)

theorem baryogenesis_dynamic_bulk_vital_holds_any (omegaMRel : ℝ) :
    baryogenesis_dynamic_bulk_vital_holds omegaMRel := by
  refine And.intro colorSingletFraction_eq_one_third ?_
  refine And.intro baryonStrongColorFraction_eq_one_sixth ?_
  exact baryogenesisCurvatureBudgetAtShell_lockin omegaMRel

theorem baryogenesis_binding_curvature_correction_mev_eq_dimless :
    baryogenesis_binding_curvature_correction m_QCD m_lockin =
      baryogenesis_binding_curvature_correction_dimless * bbnClusterBinding m_lockin 4 := by
  unfold baryogenesis_binding_curvature_correction baryogenesis_binding_curvature_correction_dimless
    clusterBindingContrastRelative
  ring

/-!
## Per-shell bulk integrator spine (Python `evolve_shell_integrator`)
-/

/-- Radiation floor in the shell partition (Python `RADIATION_FLOOR`). -/
def baryogenesisShellRadiationFloor : ℝ := 1

/-- Non-baryonic imprint strength above unit budget (Python `curvature_seed_excess`). -/
def curvatureSeedExcess (budget : ℝ) : ℝ := max 0 (budget - 1)

theorem curvatureSeedExcess_nonneg (budget : ℝ) : 0 ≤ curvatureSeedExcess budget :=
  le_max_left _ _

theorem curvatureSeedExcess_eq_max_sub_one (budget : ℝ) :
    curvatureSeedExcess budget = max 0 (budget - 1) := rfl

/-- Combined per-shell budget: early seed × same-epoch Casimir local/global. -/
noncomputable def baryogenesisCombinedCurvatureBudget (m : ℕ) (omegaMRel B_local_global : ℝ) : ℝ :=
  baryogenesisCurvatureBudgetAtShell m omegaMRel * B_local_global

/-- Matter fraction from accumulated baryon + seed tracks (Python `omega_m` update). -/
noncomputable def dynamicShellOmegaM (cumulativeBaryon cumulativeSeed : ℝ) : ℝ :=
  let total := cumulativeBaryon + cumulativeSeed + baryogenesisShellRadiationFloor
  gamma_HQIV * cumulativeBaryon / max total (1e-6)

theorem dynamicShellOmegaB_eq (omega_m : ℝ) :
    omegaBFromOmegaM omega_m = omega_m * baryonStrongColorFraction := rfl

/-- Lock-in readout from the discrete shell march (witness certificate fields). -/
structure DynamicShellLockinReadout where
  omega_m : ℝ
  omega_b : ℝ
  cumulative_baryon : ℝ
  cumulative_seed : ℝ

/-- Consistency of the baryon channel readout on a lock-in row. -/
def dynamicShellLockinConsistent (r : DynamicShellLockinReadout) : Prop :=
  omegaBFromOmegaM r.omega_m = r.omega_b

theorem dynamicShellLockinConsistent_of_eq (r : DynamicShellLockinReadout)
    (h : omegaBFromOmegaM r.omega_m = r.omega_b) : dynamicShellLockinConsistent r := h

/-!
## Casimir local/global budget (Python `curvature_budget_local_global_at_xi`)
-/

/-- Casimir separation proxy `d ∝ 1/ξ` on the ladder. -/
noncomputable def casimirGapAtXi (ξ : ℝ) : ℝ :=
  if 0 < ξ then 1 / ξ else 0

/-- Gap-ratio branch of the same-epoch local/global budget (unity when `ξ = ξ_lock`). -/
noncomputable def curvatureBudgetLocalGlobalGap (ξ ξ_lock : ℝ) (p : ℝ := 1) : ℝ :=
  let gap := casimirGapAtXi ξ
  let gap0 := casimirGapAtXi ξ_lock
  let denom := gap + gap0
  let gap_ratio :=
    if 0 < denom then (2 * Real.sqrt (gap * gap0)) / denom else 1
  min (max (gap_ratio ^ p) 1e-6) 4

/-- Same-epoch local/global curvature budget `B_curv(ξ)` (κ₆ + bulk integrator). -/
noncomputable def curvatureBudgetLocalGlobalAtXi (ξ : ℝ) (ξ_lock : ℝ := xiLockin) (p : ℝ := 1) : ℝ :=
  if ξ_lock * 100 < ξ then
    max (outsideCurvatureBindingModulatorChart ξ true) 1e-6
  else
    curvatureBudgetLocalGlobalGap ξ ξ_lock p

/-- κ₆ matter-slot alias (not the ω_K chart ratio). -/
noncomputable def curvatureBudgetAtXi (ξ : ℝ) : ℝ :=
  curvatureBudgetLocalGlobalAtXi ξ xiLockin

theorem casimirGapAtXi_lockin :
    casimirGapAtXi xiLockin = 1 / 5 := by
  unfold casimirGapAtXi
  have hξ : (0 : ℝ) < xiLockin := by rw [xiLockin_eq_five]; norm_num
  simp [hξ, xiLockin_eq_five]

theorem curvatureBudgetLocalGlobalGap_self (ξ : ℝ) (hξ : 0 < ξ) (p : ℝ) :
    curvatureBudgetLocalGlobalGap ξ ξ p = 1 := by
  unfold curvatureBudgetLocalGlobalGap casimirGapAtXi
  simp only [hξ, if_true]
  have hgap : (1 / ξ) + (1 / ξ) = 2 / ξ := by ring
  have hden : 0 < (1 / ξ) + (1 / ξ) := by
    rw [hgap]
    exact div_pos (by norm_num) hξ
  simp only [hden, if_true]
  have hpos : 0 ≤ 1 / ξ := le_of_lt (one_div_pos.mpr hξ)
  have hsqr : (1 / ξ) * (1 / ξ) = (1 / ξ) ^ 2 := by ring
  have hsqrt : Real.sqrt ((1 / ξ) * (1 / ξ)) = 1 / ξ := by
    rw [hsqr, Real.sqrt_sq hpos]
  rw [hsqrt]
  have hratio : (2 * (1 / ξ)) / (1 / ξ + 1 / ξ) = 1 := by
    rw [hgap]
    ring_nf
    field_simp [hξ.ne']
  rw [hratio]
  have hpow : (1 : ℝ) ^ p = 1 := Real.one_rpow p
  rw [hpow]
  norm_num

theorem curvatureBudgetLocalGlobalAtXi_lockin :
    curvatureBudgetLocalGlobalAtXi xiLockin xiLockin = 1 := by
  unfold curvatureBudgetLocalGlobalAtXi
  have hhot : ¬ xiLockin * 100 < xiLockin := by
    rw [xiLockin_eq_five]; norm_num
  simp only [hhot, if_false]
  exact curvatureBudgetLocalGlobalGap_self xiLockin (by rw [xiLockin_eq_five]; norm_num) 1

theorem curvatureBudgetAtXi_lockin : curvatureBudgetAtXi xiLockin = 1 :=
  curvatureBudgetLocalGlobalAtXi_lockin

theorem baryogenesisCombinedCurvatureBudget_shell_lockin (omegaMRel : ℝ) :
    baryogenesisCombinedCurvatureBudget m_lockin omegaMRel (curvatureBudgetLocalGlobalAtXi xiLockin) =
      baryogenesisCurvatureBudgetAtShell m_lockin omegaMRel := by
  dsimp [baryogenesisCombinedCurvatureBudget]
  rw [curvatureBudgetLocalGlobalAtXi_lockin]
  simp

/-!
## Chemistry ↔ baryogenesis binding bridge
 -/

theorem dynamicBindingCurvatureFeedbackAtXi_lockin_eq :
    Hqiv.QuantumChemistry.dynamicBindingCurvatureFeedbackAtXi xiLockin =
      1 + baryogenesis_binding_curvature_correction_dimless :=
  Hqiv.QuantumChemistry.dynamicBindingCurvatureFeedbackAtXi_lockin_eq_baryogenesis

theorem eta_at_horizon_dynamic_lockin_eq_feedback
    (h : 0 < curvature_integral m_lockin) :
    eta_at_horizon_dynamic m_lockin m_lockin =
      eta_paper * Hqiv.QuantumChemistry.dynamicBindingCurvatureFeedbackAtXi xiLockin := by
  rw [eta_at_horizon_dynamic_lockin_eq h, dynamicBindingCurvatureFeedbackAtXi_lockin_eq]

/-- Full HQIV-native baryogenesis spine (ratio + bulk channel + binding bridge). -/
def baryogenesis_native_spine_vital_holds (omegaMRel : ℝ) : Prop :=
  baryogenesis_dynamic_bulk_vital_holds omegaMRel ∧
  (curvatureBudgetLocalGlobalAtXi xiLockin = 1) ∧
  (outsideCurvatureBindingModulatorLockinReadout = 1) ∧
  (Hqiv.QuantumChemistry.dynamicBindingCurvatureCorrectionAtXi xiLockin =
    baryogenesis_binding_curvature_correction_dimless) ∧
  (Hqiv.QuantumChemistry.clusterBindingContrastRelative =
    clusterBindingContrastRelative)

theorem baryogenesis_native_spine_vital_holds_any (omegaMRel : ℝ) :
    baryogenesis_native_spine_vital_holds omegaMRel := by
  refine And.intro (baryogenesis_dynamic_bulk_vital_holds_any omegaMRel) ?_
  refine And.intro curvatureBudgetLocalGlobalAtXi_lockin ?_
  refine And.intro outsideCurvatureBindingModulatorLockinReadout_eq_one ?_
  refine And.intro ?_ rfl
  exact Hqiv.QuantumChemistry.dynamicBindingCurvatureCorrectionAtXi_lockin_eq_baryogenesis_dimless

end Hqiv.Physics
