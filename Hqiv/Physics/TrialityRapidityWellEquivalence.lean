import Hqiv.Physics.HyperchargePathBarrierScaffold
import Hqiv.Physics.FanoDetuningFirstOrder
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Algebra.Triality
import Hqiv.Geometry.AuxiliaryField

namespace Hqiv.Physics

open Hqiv.Algebra
open Hqiv

/-!
# Triality/rapidity well equivalence scaffold

This module turns the question

> do the triality- and rapidity-induced well constructions agree with the current Fano detuning well?

into explicit Lean predicates and theorems:

- **triality side:** representation-indexed well is invariant under the order-3 cycle,
- **rapidity side:** a denominator written directly in terms of `phi_of_shell`,
- **comparison:** residual between the two is exactly zero in the current scaffold, hence
  "near-equivalent" for any nonnegative tolerance.
-/

/--
Representation-indexed per-turn well (triality view).
The current scaffold is rep-neutral, so this ignores `_rep` by design.
-/
noncomputable def trialityRepTurnIncrement
    (line : FanoLineTag) (_rep : So8RepIndex) (m : ℕ) : ℝ :=
  turnIncrementBarrier line m

theorem trialityRepTurnIncrement_invariant_under_cycle
    (line : FanoLineTag) (rep : So8RepIndex) (m : ℕ) :
    trialityRepTurnIncrement line (trialityCycle rep) m =
      trialityRepTurnIncrement line rep m := by
  rfl

theorem trialityRepTurnIncrement_invariant_under_cycle2
    (line : FanoLineTag) (rep : So8RepIndex) (m : ℕ) :
    trialityRepTurnIncrement line (trialityCycle2 rep) m =
      trialityRepTurnIncrement line rep m := by
  rfl

/--
Rapidity-written denominator using `phi_of_shell`.
Because `phi_of_shell m = 2 (m+1)`, this is affine in `m` with slope `gamma/2`.
-/
noncomputable def rapidityLiftedDenominator (m : ℕ) : ℝ :=
  1 + (gamma_HQIV / 4) * (phi_of_shell m - phiTemperatureCoeff)

theorem rapidityLiftedDenominator_eq_affine_shell (m : ℕ) :
    rapidityLiftedDenominator m = 1 + (gamma_HQIV / 2) * (m : ℝ) := by
  unfold rapidityLiftedDenominator
  rw [phi_of_shell_closed_form, phiTemperatureCoeff_eq_two]
  ring_nf

theorem rapidityLiftedDenominator_eq_trialityProjectedDenominator
    (line : FanoLineTag) (m : ℕ) :
    rapidityLiftedDenominator m = trialityProjectedDenominatorTag line m := by
  rw [trialityProjectedDenominatorTag_eq_rindler, rindlerDetuningShared_eq_one_plus_half_gamma]
  exact rapidityLiftedDenominator_eq_affine_shell m

/-- Well surface from the rapidity-written denominator. -/
noncomputable def rapidityLiftedWell (m : ℕ) : ℝ :=
  shellSurface m / rapidityLiftedDenominator m

theorem rapidityLiftedWell_eq_turnIncrementBarrier
    (line : FanoLineTag) (m : ℕ) :
    rapidityLiftedWell m = turnIncrementBarrier line m := by
  unfold rapidityLiftedWell turnIncrementBarrier
  rw [deltaTurnIncrement_eq_projectedDetuned, rapidityLiftedDenominator_eq_trialityProjectedDenominator]

/--
Residual between the triality-indexed turn increment and the rapidity-written well.
`0` means exact equivalence; small absolute value means near-equivalence.
-/
noncomputable def trialityRapidityWellResidual
    (line : FanoLineTag) (rep : So8RepIndex) (m : ℕ) : ℝ :=
  trialityRepTurnIncrement line rep m - rapidityLiftedWell m

theorem trialityRapidityWellResidual_eq_zero
    (line : FanoLineTag) (rep : So8RepIndex) (m : ℕ) :
    trialityRapidityWellResidual line rep m = 0 := by
  unfold trialityRapidityWellResidual trialityRepTurnIncrement
  rw [rapidityLiftedWell_eq_turnIncrementBarrier]
  ring

theorem trialityRapidityWell_nearEquivalent
    (line : FanoLineTag) (rep : So8RepIndex) (m : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    |trialityRapidityWellResidual line rep m| ≤ ε := by
  rw [trialityRapidityWellResidual_eq_zero]
  simpa using hε

/-!
## Rep-sensitive candidate from baryogenesis CP asymmetry

To move beyond the rep-neutral scaffold, we couple the triality representation index to the same
baryogenesis asymmetry channel used in `Hqiv.Physics.Baryogenesis`:

- CP-bias amplitude at shell `m`: curvature-ratio deviation
  `omega_k_at_horizon m m_lockin - 1` (same baryogenesis channel, no `eta_paper` anchor),
- orientation by representation: `8v ↦ 0`, `8s⁺ ↦ +1`, `8s⁻ ↦ -1`.

This produces a small rep-sensitive perturbation of the rapidity/triality baseline well.
-/

/-- Triality-representation CP orientation weights (sum to zero across the 3 reps). -/
def trialityCpOrientation : So8RepIndex → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => -1

theorem trialityCpOrientation_rep8V : trialityCpOrientation rep8V = 0 := rfl
theorem trialityCpOrientation_rep8SPlus : trialityCpOrientation rep8SPlus = 1 := rfl
theorem trialityCpOrientation_rep8SMinus : trialityCpOrientation rep8SMinus = -1 := rfl

theorem trialityCpOrientation_abs_le_one (rep : So8RepIndex) :
    |trialityCpOrientation rep| ≤ 1 := by
  fin_cases rep <;> norm_num [trialityCpOrientation]

/--
Baryogenesis-linked CP-bias amplitude at shell `m` (lockin horizon reference),
defined from the derived curvature ratio only.
-/
noncomputable def rapidityCPBias (m : ℕ) : ℝ :=
  omega_k_at_horizon m m_lockin - 1

theorem rapidityCPBias_eq_curvature_ratio_minus_one (m : ℕ) :
    rapidityCPBias m = omega_k_at_horizon m m_lockin - 1 := rfl

/-- The affine **tilt factors** \((1 + w_{\mathrm{rep}}\cdot\texttt{rapidityCPBias})\) sum to \(3\) and
    therefore average to \(1\) (zero-sum triality weights \(0,+1,-1\)). This is the algebraic core
    behind three-rep averaging; the full increment average is
    \texttt{cpSensitiveTrialityIncrement\_threeRep\_average\_eq\_rapidityWell}. -/
theorem triality_cp_tilt_factors_average_eq_one (m : ℕ) :
    ((1 + rapidityCPBias m * trialityCpOrientation rep8V)
        + (1 + rapidityCPBias m * trialityCpOrientation rep8SPlus)
        + (1 + rapidityCPBias m * trialityCpOrientation rep8SMinus)) / 3 = 1 := by
  rw [trialityCpOrientation_rep8V, trialityCpOrientation_rep8SPlus, trialityCpOrientation_rep8SMinus]
  ring

/--
Rep-sensitive triality increment candidate:
baseline turn increment multiplied by a baryogenesis CP-bias tilt.

The same CP-bias identity in η-calibration language is
`Hqiv.omega_k_cp_bias_eq_eta_ratio_minus_one` in `Hqiv.Physics.BaryogenesisWitness`
(imports the paper η anchor).
-/
noncomputable def cpSensitiveTrialityIncrement
    (line : FanoLineTag) (rep : So8RepIndex) (m : ℕ) : ℝ :=
  turnIncrementBarrier line m * (1 + rapidityCPBias m * trialityCpOrientation rep)

/-- Residual vs rapidity-written well for the CP-sensitive candidate. -/
noncomputable def cpSensitiveTrialityRapidityResidual
    (line : FanoLineTag) (rep : So8RepIndex) (m : ℕ) : ℝ :=
  cpSensitiveTrialityIncrement line rep m - rapidityLiftedWell m

theorem cpSensitiveTrialityRapidityResidual_eq
    (line : FanoLineTag) (rep : So8RepIndex) (m : ℕ) :
    cpSensitiveTrialityRapidityResidual line rep m =
      turnIncrementBarrier line m * rapidityCPBias m * trialityCpOrientation rep := by
  unfold cpSensitiveTrialityRapidityResidual cpSensitiveTrialityIncrement
  rw [rapidityLiftedWell_eq_turnIncrementBarrier]
  ring

theorem cpSensitiveTrialityRapidityResidual_rep8V_eq_zero
    (line : FanoLineTag) (m : ℕ) :
    cpSensitiveTrialityRapidityResidual line rep8V m = 0 := by
  rw [cpSensitiveTrialityRapidityResidual_eq, trialityCpOrientation_rep8V]
  ring

theorem cpSensitiveTrialityRapidityResidual_rep8SPlus_eq
    (line : FanoLineTag) (m : ℕ) :
    cpSensitiveTrialityRapidityResidual line rep8SPlus m =
      turnIncrementBarrier line m * rapidityCPBias m := by
  rw [cpSensitiveTrialityRapidityResidual_eq, trialityCpOrientation_rep8SPlus]
  ring

theorem cpSensitiveTrialityRapidityResidual_rep8SMinus_eq
    (line : FanoLineTag) (m : ℕ) :
    cpSensitiveTrialityRapidityResidual line rep8SMinus m =
      - turnIncrementBarrier line m * rapidityCPBias m := by
  rw [cpSensitiveTrialityRapidityResidual_eq, trialityCpOrientation_rep8SMinus]
  ring

/-- The three triality channels average back to the rapidity well (zero-sum CP orientation). -/
theorem cpSensitiveTrialityIncrement_threeRep_average_eq_rapidityWell
    (line : FanoLineTag) (m : ℕ) :
    (cpSensitiveTrialityIncrement line rep8V m
      + cpSensitiveTrialityIncrement line rep8SPlus m
      + cpSensitiveTrialityIncrement line rep8SMinus m) / 3
      = rapidityLiftedWell m := by
  unfold cpSensitiveTrialityIncrement
  rw [trialityCpOrientation_rep8V, trialityCpOrientation_rep8SPlus, trialityCpOrientation_rep8SMinus]
  rw [rapidityLiftedWell_eq_turnIncrementBarrier]
  ring

/--
Near-equivalence bound for the CP-sensitive residual:
small baryogenesis bias implies proportionally small deviation from the rapidity well.
-/
theorem cpSensitiveTrialityRapidityResidual_bound_of_bias
    (line : FanoLineTag) (rep : So8RepIndex) (m : ℕ) (ε : ℝ)
    (hε : |rapidityCPBias m| ≤ ε) :
    |cpSensitiveTrialityRapidityResidual line rep m|
      ≤ |turnIncrementBarrier line m| * ε := by
  rw [cpSensitiveTrialityRapidityResidual_eq]
  calc
    |turnIncrementBarrier line m * rapidityCPBias m * trialityCpOrientation rep|
        = |turnIncrementBarrier line m| * |rapidityCPBias m| * |trialityCpOrientation rep| := by
            rw [abs_mul, abs_mul]
    _ ≤ |turnIncrementBarrier line m| * |rapidityCPBias m| * 1 := by
          gcongr
          exact trialityCpOrientation_abs_le_one rep
    _ = |turnIncrementBarrier line m| * |rapidityCPBias m| := by ring
    _ ≤ |turnIncrementBarrier line m| * ε := by
          gcongr

end Hqiv.Physics
