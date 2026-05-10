import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Hqiv.QuantumMechanics.FiniteDimVonNeumann
import Hqiv.QuantumMechanics.FiniteManyBodyCore
import Hqiv.QuantumMechanics.HubbardDimerGapBridge
import Hqiv.QuantumMechanics.HubbardDimerWitnessTable
import Hqiv.Physics.HQIVFluidClosureScaffold

namespace Hqiv.QM

open Matrix Complex

/-- Canonical half-filled 2-site Hubbard dimer Hamiltonian in the 4-state basis
`|↑↓,0⟩, |0,↑↓⟩, |↑,↓⟩, |↓,↑⟩`. -/
def canonicalHalfFilledHamiltonian (t U : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(U : ℂ), 0, (-t : ℂ), (t : ℂ);
     0, (U : ℂ), (-t : ℂ), (t : ℂ);
     (-t : ℂ), (-t : ℂ), 0, 0;
     (t : ℂ), (t : ℂ), 0, 0]

theorem canonicalHalfFilledHamiltonian_isHermitian (t U : ℝ) :
    (canonicalHalfFilledHamiltonian t U).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [canonicalHalfFilledHamiltonian, Matrix.of_apply]

/-- Total double occupancy `D = n₁↑n₁↓ + n₂↑n₂↓` in the canonical 4-state basis. -/
def canonicalDoubleOccupancyTotalMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(1 : ℂ), 0, 0, 0;
     0, (1 : ℂ), 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

theorem canonicalDoubleOccupancyTotal_isHermitian :
    canonicalDoubleOccupancyTotalMatrix.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [canonicalDoubleOccupancyTotalMatrix, Matrix.of_apply]

/-- `S₁ · S₂` on the canonical half-filled basis. -/
noncomputable def canonicalSpinCorrelationMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(0 : ℂ), 0, 0, 0;
     0, (0 : ℂ), 0, 0;
     0, 0, (-(1 / 4 : ℂ)), (1 / 2 : ℂ);
     0, 0, (1 / 2 : ℂ), (-(1 / 4 : ℂ))]

theorem canonicalSpinCorrelation_isHermitian :
    canonicalSpinCorrelationMatrix.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [canonicalSpinCorrelationMatrix, Matrix.of_apply]

/-- Observable package for the total double occupancy in canonical half-filled basis. -/
def canonicalDoubleOccupancyTotalObservable : Observable 4 where
  A := canonicalDoubleOccupancyTotalMatrix
  isHerm := canonicalDoubleOccupancyTotal_isHermitian

/-- Observable package for `S₁·S₂` in canonical half-filled basis. -/
noncomputable def canonicalSpinCorrelationObservable : Observable 4 where
  A := canonicalSpinCorrelationMatrix
  isHerm := canonicalSpinCorrelation_isHermitian

/-- Kinetic (`U=0`) Hamiltonian core used by interaction updates. -/
def canonicalHalfFilledKineticMatrix (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  canonicalHalfFilledHamiltonian t 0

theorem canonicalHalfFilledKinetic_isHermitian (t : ℝ) :
    (canonicalHalfFilledKineticMatrix t).IsHermitian :=
  canonicalHalfFilledHamiltonian_isHermitian t 0

noncomputable def canonicalHalfFilledKineticObservable (t : ℝ) : Observable 4 where
  A := canonicalHalfFilledKineticMatrix t
  isHerm := canonicalHalfFilledKinetic_isHermitian t

/-- Named observables registered on the canonical half-filled 4D model. -/
inductive CanonicalHalfFilledObsLabel
  | doubleOcc
  | spinCorr
deriving DecidableEq

/-- Canonical half-filled model as an instance of the general finite many-body core. -/
noncomputable def canonicalHalfFilledModelBase (t : ℝ) : FiniteManyBodyModel 4 where
  H := canonicalHalfFilledKineticObservable t
  ObsLabel := CanonicalHalfFilledObsLabel
  O
    | CanonicalHalfFilledObsLabel.doubleOcc => canonicalDoubleOccupancyTotalObservable
    | CanonicalHalfFilledObsLabel.spinCorr => canonicalSpinCorrelationObservable

/-- Canonical half-filled model with onsite interaction `U * D` using `withInteraction`. -/
noncomputable def canonicalHalfFilledModel (t U : ℝ) : FiniteManyBodyModel 4 :=
  (canonicalHalfFilledModelBase t).withInteraction canonicalDoubleOccupancyTotalObservable U

theorem canonicalHalfFilledModel_H_eq_matrix (t U : ℝ) :
    (canonicalHalfFilledModel t U).H.A = canonicalHalfFilledHamiltonian t U := by
  unfold canonicalHalfFilledModel canonicalHalfFilledModelBase
  unfold FiniteManyBodyModel.withInteraction addInteractionObservable
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalHalfFilledKineticObservable, canonicalHalfFilledKineticMatrix,
      canonicalHalfFilledHamiltonian, canonicalDoubleOccupancyTotalObservable,
      canonicalDoubleOccupancyTotalMatrix, Matrix.of_apply]

/-- Closed-form canonical half-filled dimer gap:
`(sqrt(U^2 + 16 t^2) - U) / 2`. -/
noncomputable def canonicalHalfFilledGapClosed (t U : ℝ) : ℝ :=
  (Real.sqrt (U ^ 2 + 16 * t ^ 2) - U) / 2

/-- Closed-form ground-state total double occupancy for canonical half-filled dimer. -/
noncomputable def canonicalHalfFilledDoubleOccupancyTotalClosed (t U : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 - U / Real.sqrt (U ^ 2 + 16 * t ^ 2))

/-- Closed-form ground-state spin correlation from the same canonical branch. -/
noncomputable def canonicalHalfFilledSpinCorrelationClosed (t U : ℝ) : ℝ :=
  (-(3 / 4 : ℝ)) * (1 - canonicalHalfFilledDoubleOccupancyTotalClosed t U)

theorem canonicalHalfFilledSpinCorrelation_from_double (t U : ℝ) :
    canonicalHalfFilledSpinCorrelationClosed t U
      = (-(3 / 4 : ℝ)) * (1 - canonicalHalfFilledDoubleOccupancyTotalClosed t U) := rfl

theorem canonicalHalfFilledGap_nonneg (t U : ℝ) :
    0 ≤ canonicalHalfFilledGapClosed t U := by
  unfold canonicalHalfFilledGapClosed
  have hs : U ≤ Real.sqrt (U ^ 2 + 16 * t ^ 2) := by
    calc
      U ≤ |U| := le_abs_self U
      _ = Real.sqrt (U ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (U ^ 2 + 16 * t ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
  nlinarith

/-- Canonical gap is half of `hubbardGapClosedForm` at doubled hopping. -/
theorem canonicalHalfFilledGap_as_hubbardGap (t U : ℝ) (hU : 0 ≤ U) :
    canonicalHalfFilledGapClosed t U = (1 / 2 : ℝ) * hubbardGapClosedForm (2 * t) U := by
  unfold canonicalHalfFilledGapClosed hubbardGapClosedForm hubbardEnergyScale
  rw [abs_of_nonneg hU]
  ring_nf

/-- Gap is antitone in `U` on the repulsive branch (`U ≥ 0`) for `t > 0`. -/
theorem canonicalHalfFilledGap_antitoneOn_nonneg (t : ℝ) (ht : 0 < t) :
    AntitoneOn (fun U => canonicalHalfFilledGapClosed t U) (Set.Ici 0) := by
  intro U1 hU1 U2 hU2 h12
  have ht2 : 0 < 2 * t := by nlinarith
  have hcore := hubbardGapClosedForm_antitoneOn_nonneg (2 * t) ht2 hU1 hU2 h12
  have hU1' : 0 ≤ U1 := by simpa using hU1
  have hU2' : 0 ≤ U2 := by simpa using hU2
  simpa [canonicalHalfFilledGap_as_hubbardGap t U1 hU1',
      canonicalHalfFilledGap_as_hubbardGap t U2 hU2']
    using (mul_le_mul_of_nonneg_left hcore (show (0 : ℝ) ≤ 1 / 2 by norm_num))

/-- Total double occupancy decreases with repulsive `U` (`U ≥ 0`, `t > 0`). -/
theorem canonicalHalfFilledDoubleOcc_antitoneOn_nonneg (t : ℝ) (ht : 0 < t) :
    AntitoneOn (fun U => canonicalHalfFilledDoubleOccupancyTotalClosed t U) (Set.Ici 0) := by
  intro U1 hU1 U2 hU2 h12
  have h1 : 0 ≤ U1 := by simpa using hU1
  have h2 : 0 ≤ U2 := by simpa using hU2
  let s1 : ℝ := Real.sqrt (U1 ^ 2 + 16 * t ^ 2)
  let s2 : ℝ := Real.sqrt (U2 ^ 2 + 16 * t ^ 2)
  have hs1_pos : 0 < s1 := by
    unfold s1
    apply Real.sqrt_pos.2
    nlinarith [ht]
  have hs2_pos : 0 < s2 := by
    unfold s2
    apply Real.sqrt_pos.2
    nlinarith [ht]
  have hs1_sq : s1 ^ 2 = U1 ^ 2 + 16 * t ^ 2 := by
    unfold s1
    have hnonneg : 0 ≤ U1 ^ 2 + 16 * t ^ 2 := by nlinarith
    rw [Real.sq_sqrt hnonneg]
  have hs2_sq : s2 ^ 2 = U2 ^ 2 + 16 * t ^ 2 := by
    unfold s2
    have hnonneg : 0 ≤ U2 ^ 2 + 16 * t ^ 2 := by nlinarith
    rw [Real.sq_sqrt hnonneg]
  have hsq_u : U1 ^ 2 ≤ U2 ^ 2 := by nlinarith [h1, h2, h12]
  have hs1_mul : s1 * s1 = U1 ^ 2 + 16 * t ^ 2 := by simpa [pow_two] using hs1_sq
  have hs2_mul : s2 * s2 = U2 ^ 2 + 16 * t ^ 2 := by simpa [pow_two] using hs2_sq
  have hsq : (U1 * s2) ^ 2 ≤ (U2 * s1) ^ 2 := by
    nlinarith [hsq_u, hs1_mul, hs2_mul]
  have hmul : U1 * s2 ≤ U2 * s1 := by
    have hleft_nonneg : 0 ≤ U1 * s2 := mul_nonneg h1 (le_of_lt hs2_pos)
    have hright_nonneg : 0 ≤ U2 * s1 := mul_nonneg h2 (le_of_lt hs1_pos)
    nlinarith [hsq, hleft_nonneg, hright_nonneg]
  have hratio : U1 / s1 ≤ U2 / s2 := by
    have hs1_ne : s1 ≠ 0 := ne_of_gt hs1_pos
    have hs2_ne : s2 ≠ 0 := ne_of_gt hs2_pos
    field_simp [hs1_ne, hs2_ne]
    simpa [mul_comm] using hmul
  unfold canonicalHalfFilledDoubleOccupancyTotalClosed
  nlinarith [hratio]

/-- Spin correlation is antitone with repulsive `U` (`U ≥ 0`, `t > 0`). -/
theorem canonicalHalfFilledSpinCorr_antitoneOn_nonneg (t : ℝ) (ht : 0 < t) :
    AntitoneOn (fun U => canonicalHalfFilledSpinCorrelationClosed t U) (Set.Ici 0) := by
  intro U1 hU1 U2 hU2 h12
  have hD := canonicalHalfFilledDoubleOcc_antitoneOn_nonneg t ht hU1 hU2 h12
  have h1m : 1 - canonicalHalfFilledDoubleOccupancyTotalClosed t U1
      ≤ 1 - canonicalHalfFilledDoubleOccupancyTotalClosed t U2 := by
    nlinarith
  unfold canonicalHalfFilledSpinCorrelationClosed
  have hcoef : (-(3 / 4 : ℝ)) ≤ 0 := by norm_num
  exact mul_le_mul_of_nonpos_left h1m hcoef

/-- Shell-coupled canonical gap using the same `lambdaShell` hook. -/
noncomputable def canonicalHalfFilledGapShell (m : ℕ) (t lambda0 coherence : ℝ) : ℝ :=
  canonicalHalfFilledGapClosed t (lambdaShell m lambda0 coherence)

noncomputable def canonicalHalfFilledDoubleOccShell (m : ℕ) (t lambda0 coherence : ℝ) : ℝ :=
  canonicalHalfFilledDoubleOccupancyTotalClosed t (lambdaShell m lambda0 coherence)

noncomputable def canonicalHalfFilledSpinCorrShell (m : ℕ) (t lambda0 coherence : ℝ) : ℝ :=
  canonicalHalfFilledSpinCorrelationClosed t (lambdaShell m lambda0 coherence)

/-- Derived AF exchange observable (strong-coupling proxy): `J_eff = 4 t^2 / U`. -/
noncomputable def canonicalAFExchangeClosed (t U : ℝ) : ℝ :=
  (4 * t ^ 2) / U

/-- Shell-coupled AF exchange proxy using `U(m)=lambdaShell ...`. -/
noncomputable def canonicalAFExchangeShell (m : ℕ) (t lambda0 coherence : ℝ) : ℝ :=
  canonicalAFExchangeClosed t (lambdaShell m lambda0 coherence)

theorem canonicalUShell_monotone (lambda0 coherence : ℝ) (h_nonneg : 0 ≤ lambda0 * coherence) :
    Monotone (fun m => lambdaShell m lambda0 coherence) :=
  lambdaShell_monotone lambda0 coherence h_nonneg

theorem canonicalUShell_nonneg (m : ℕ) (lambda0 coherence : ℝ) (h_nonneg : 0 ≤ lambda0 * coherence) :
    0 ≤ lambdaShell m lambda0 coherence :=
  lambdaShell_nonneg m lambda0 coherence h_nonneg

theorem canonicalAFExchangeShell_pos (m : ℕ) (t lambda0 coherence : ℝ)
    (ht : t ≠ 0) (hU : 0 < lambdaShell m lambda0 coherence) :
    0 < canonicalAFExchangeShell m t lambda0 coherence := by
  unfold canonicalAFExchangeShell canonicalAFExchangeClosed
  have hnum : 0 < 4 * t ^ 2 := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    nlinarith
  exact div_pos hnum hU

theorem canonicalHalfFilledGapShell_antitone (t lambda0 coherence : ℝ) (ht : 0 < t)
    (h_nonneg : 0 ≤ lambda0 * coherence) :
    Antitone (fun m => canonicalHalfFilledGapShell m t lambda0 coherence) := by
  intro m n hmn
  have hUmono := canonicalUShell_monotone lambda0 coherence h_nonneg hmn
  have hUm : 0 ≤ lambdaShell m lambda0 coherence := canonicalUShell_nonneg m lambda0 coherence h_nonneg
  have hUn : 0 ≤ lambdaShell n lambda0 coherence := canonicalUShell_nonneg n lambda0 coherence h_nonneg
  unfold canonicalHalfFilledGapShell
  exact canonicalHalfFilledGap_antitoneOn_nonneg t ht hUm hUn hUmono

theorem canonicalHalfFilledDoubleOccShell_antitone (t lambda0 coherence : ℝ) (ht : 0 < t)
    (h_nonneg : 0 ≤ lambda0 * coherence) :
    Antitone (fun m => canonicalHalfFilledDoubleOccShell m t lambda0 coherence) := by
  intro m n hmn
  have hUmono := canonicalUShell_monotone lambda0 coherence h_nonneg hmn
  have hUm : 0 ≤ lambdaShell m lambda0 coherence := canonicalUShell_nonneg m lambda0 coherence h_nonneg
  have hUn : 0 ≤ lambdaShell n lambda0 coherence := canonicalUShell_nonneg n lambda0 coherence h_nonneg
  unfold canonicalHalfFilledDoubleOccShell
  exact canonicalHalfFilledDoubleOcc_antitoneOn_nonneg t ht hUm hUn hUmono

theorem canonicalHalfFilledSpinCorrShell_antitone (t lambda0 coherence : ℝ) (ht : 0 < t)
    (h_nonneg : 0 ≤ lambda0 * coherence) :
    Antitone (fun m => canonicalHalfFilledSpinCorrShell m t lambda0 coherence) := by
  intro m n hmn
  have hUmono := canonicalUShell_monotone lambda0 coherence h_nonneg hmn
  have hUm : 0 ≤ lambdaShell m lambda0 coherence := canonicalUShell_nonneg m lambda0 coherence h_nonneg
  have hUn : 0 ≤ lambdaShell n lambda0 coherence := canonicalUShell_nonneg n lambda0 coherence h_nonneg
  unfold canonicalHalfFilledSpinCorrShell
  exact canonicalHalfFilledSpinCorr_antitoneOn_nonneg t ht hUm hUn hUmono

/-- Micro→macro coupling: in the unsaturated plasma-amplitude regime,
the shell coupling is exactly multiplicative in the plasma scalar amplitude. -/
theorem canonicalUShell_eq_plasmaAmp_mul_if_unsat (m : ℕ) (lambda0 κ j₀ r : ℝ)
    (h_unsat : κ * |Hqiv.schematicPlasmaScalar j₀ r| ≤ 1) :
    lambdaShell m lambda0 (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r)
      = lambda0 * (κ * |Hqiv.schematicPlasmaScalar j₀ r|) * ((m + 1 : ℝ) / 5) := by
  have hcoh :
      Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r = κ * |Hqiv.schematicPlasmaScalar j₀ r| :=
    (Hqiv.Physics.coherenceFromPlasmaAmp_eq_mul_iff κ j₀ r).2 h_unsat
  rw [hcoh, lambdaShell_closed_form]

/-- Micro→macro bridge: in the unsaturated coherence regime, `J_eff` from the canonical dimer
feeds directly into the F3 shell+Debye eddy-viscosity term, and the coherence factor cancels
in the product `J_eff * ν_eddy`. -/
theorem canonicalAFExchange_mul_eddy_shell_debye_plasma_unsat
    (m : ℕ) (t lambda0 dotTheta κ j₀ r : ℝ)
    (h_unsat : κ * |Hqiv.schematicPlasmaScalar j₀ r| ≤ 1)
    (h_base : lambda0 * ((m + 1 : ℝ) / 5) ≠ 0)
    (h_amp : κ * |Hqiv.schematicPlasmaScalar j₀ r| ≠ 0) :
    canonicalAFExchangeShell m t lambda0 (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r) *
      Hqiv.Physics.hqivEddyViscosity_HQIV_shell_debye m dotTheta
        (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r)
      =
    ((4 * t ^ 2) / (lambda0 * ((m + 1 : ℝ) / 5))) *
      (Hqiv.gamma_HQIV * Hqiv.T m * |dotTheta| * Hqiv.lambdaDebye ^ 2) := by
  let amp : ℝ := κ * |Hqiv.schematicPlasmaScalar j₀ r|
  have hU :
      lambdaShell m lambda0 (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r) =
        lambda0 * amp * ((m + 1 : ℝ) / 5) := by
    simpa [amp] using canonicalUShell_eq_plasmaAmp_mul_if_unsat m lambda0 κ j₀ r h_unsat
  have hVisc :
      Hqiv.Physics.hqivEddyViscosity_HQIV_shell_debye m dotTheta
          (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r)
        = Hqiv.gamma_HQIV * Hqiv.T m * |dotTheta| * Hqiv.lambdaDebye ^ 2 * amp := by
    rw [Hqiv.Physics.hqivEddyViscosity_HQIV_shell_debye_eq]
    have hcoh :
        Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r = amp := by
      simpa [amp] using (Hqiv.Physics.coherenceFromPlasmaAmp_eq_mul_iff κ j₀ r).2 h_unsat
    rw [hcoh]
  have h_l0 : lambda0 ≠ 0 := by
    intro hz
    exact h_base (by simp [hz])
  calc
    canonicalAFExchangeShell m t lambda0 (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r) *
        Hqiv.Physics.hqivEddyViscosity_HQIV_shell_debye m dotTheta
          (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r)
      =
        ((4 * t ^ 2) / (lambda0 * amp * ((m + 1 : ℝ) / 5))) *
          (Hqiv.gamma_HQIV * Hqiv.T m * |dotTheta| * Hqiv.lambdaDebye ^ 2 * amp) := by
            simp [canonicalAFExchangeShell, canonicalAFExchangeClosed, hU, hVisc]
    _ =
        ((4 * t ^ 2) / (lambda0 * ((m + 1 : ℝ) / 5))) *
          (Hqiv.gamma_HQIV * Hqiv.T m * |dotTheta| * Hqiv.lambdaDebye ^ 2) := by
            field_simp [h_base, h_amp, h_l0]
            have hdiv : amp / amp = (1 : ℝ) := div_self h_amp
            calc
              t ^ 2 * amp * Hqiv.gamma_HQIV * Hqiv.T m * |dotTheta| * Hqiv.lambdaDebye ^ 2 / amp
                  =
                (t ^ 2 * Hqiv.gamma_HQIV * Hqiv.T m * |dotTheta| * Hqiv.lambdaDebye ^ 2) * (amp / amp) := by
                  field_simp [h_amp]
              _ = t ^ 2 * Hqiv.gamma_HQIV * Hqiv.T m * |dotTheta| * Hqiv.lambdaDebye ^ 2 := by
                  simp [hdiv]

/-- Witness-shell specialization (`m ∈ [2..8]`) of the AF-exchange/F3 plasma-unsaturated coupling. -/
theorem canonicalAFExchange_mul_eddy_witnessShells_plasma_unsat
    (t lambda0 dotTheta κ j₀ r : ℝ)
    (h_unsat : κ * |Hqiv.schematicPlasmaScalar j₀ r| ≤ 1)
    (h_base : ∀ m : ℕ, m ∈ (witnessShellMs : List ℕ) → lambda0 * ((m + 1 : ℝ) / 5) ≠ 0)
    (h_amp : κ * |Hqiv.schematicPlasmaScalar j₀ r| ≠ 0) :
    ∀ m : ℕ, m ∈ (witnessShellMs : List ℕ) →
      canonicalAFExchangeShell m t lambda0 (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r) *
        Hqiv.Physics.hqivEddyViscosity_HQIV_shell_debye m dotTheta
          (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r)
        =
      ((4 * t ^ 2) / (lambda0 * ((m + 1 : ℝ) / 5))) *
        (Hqiv.gamma_HQIV * Hqiv.T m * |dotTheta| * Hqiv.lambdaDebye ^ 2) := by
  intro m hm
  exact canonicalAFExchange_mul_eddy_shell_debye_plasma_unsat
    m t lambda0 dotTheta κ j₀ r h_unsat (h_base m hm) h_amp

/-- Infinite-temperature (`β = 0`) canonical half-filled thermal double occupancy. -/
noncomputable def canonicalHalfFilledThermalDoubleOccInfiniteTemp : ℝ := 1 / 2

/-- Infinite-temperature (`β = 0`) canonical half-filled thermal spin correlation. -/
noncomputable def canonicalHalfFilledThermalSpinCorrInfiniteTemp : ℝ := -1 / 8

/-- Infinite-temperature (`β = 0`) thermal energy shell witness (`Tr(H)/4 = U_shell/2`). -/
noncomputable def canonicalHalfFilledThermalEnergyInfiniteTempShell
    (m : ℕ) (lambda0 coherence : ℝ) : ℝ :=
  (lambdaShell m lambda0 coherence) / 2

/-- Witness-shell specialization (`m ∈ [2..8]`) for infinite-temperature canonical thermal observables. -/
theorem canonicalHalfFilledThermalInfiniteTemp_witnessShells
    (lambda0 coherence : ℝ) :
    ∀ m : ℕ, m ∈ (witnessShellMs : List ℕ) →
      canonicalHalfFilledThermalDoubleOccInfiniteTemp = (1 / 2 : ℝ) ∧
      canonicalHalfFilledThermalSpinCorrInfiniteTemp = (-(1 / 8 : ℝ)) ∧
      canonicalHalfFilledThermalEnergyInfiniteTempShell m lambda0 coherence
        = lambda0 * coherence * ((m + 1 : ℝ) / 10) := by
  intro m hm
  constructor
  · rfl
  constructor
  · norm_num [canonicalHalfFilledThermalSpinCorrInfiniteTemp]
  · unfold canonicalHalfFilledThermalEnergyInfiniteTempShell
    rw [lambdaShell_closed_form]
    ring

/-- Finite-temperature coupling (at `β = 0` canonical limit):
in the unsaturated plasma-amplitude branch, shell thermal energy is exactly
multiplicative in the plasma scalar amplitude via the coherence min-factor. -/
theorem canonicalHalfFilledThermalEnergyInfiniteTempShell_eq_plasmaAmp_mul_if_unsat
    (m : ℕ) (lambda0 κ j₀ r : ℝ)
    (h_unsat : κ * |Hqiv.schematicPlasmaScalar j₀ r| ≤ 1) :
    canonicalHalfFilledThermalEnergyInfiniteTempShell m lambda0
      (Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r)
      = lambda0 * (κ * |Hqiv.schematicPlasmaScalar j₀ r|) * ((m + 1 : ℝ) / 10) := by
  unfold canonicalHalfFilledThermalEnergyInfiniteTempShell
  have hcoh :
      Hqiv.Physics.coherenceFromPlasmaAmp κ j₀ r = κ * |Hqiv.schematicPlasmaScalar j₀ r| :=
    (Hqiv.Physics.coherenceFromPlasmaAmp_eq_mul_iff κ j₀ r).2 h_unsat
  rw [hcoh, lambdaShell_closed_form]
  ring

end Hqiv.QM
