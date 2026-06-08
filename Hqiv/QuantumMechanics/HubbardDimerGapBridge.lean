import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Hqiv.QuantumMechanics.HubbardDimerFinite
import Hqiv.QuantumMechanics.HubbardDimerWitnessTable

namespace Hqiv.QM

/-- Closed-form symmetric energy scale from the 2×2 interacting block. -/
noncomputable def hubbardEnergyScale (t lambda : ℝ) : ℝ :=
  Real.sqrt (lambda ^ 2 + 4 * t ^ 2)

/-- Closed-form dimer gap for the candidate spectrum `±E`, `±|λ|`. -/
noncomputable def hubbardGapClosedForm (t lambda : ℝ) : ℝ :=
  hubbardEnergyScale t lambda - |lambda|

/-- Spectral candidate set used by the analytic bridge. -/
noncomputable def hubbardEigenvalueCandidates (t lambda : ℝ) : Fin 4 → ℝ
  | 0 => -hubbardEnergyScale t lambda
  | 1 => -|lambda|
  | 2 => |lambda|
  | 3 => hubbardEnergyScale t lambda

/-- Analytic bridge: `±hubbardEnergyScale` are roots of `x^2 - (λ^2+4t^2)`. -/
theorem hubbardEnergyScale_root_poly (t lambda : ℝ) :
    (hubbardEnergyScale t lambda) ^ 2 - (lambda ^ 2 + 4 * t ^ 2) = 0 := by
  unfold hubbardEnergyScale
  have hnonneg : 0 ≤ lambda ^ 2 + 4 * t ^ 2 := by nlinarith
  rw [Real.sq_sqrt hnonneg]
  ring

theorem neg_hubbardEnergyScale_root_poly (t lambda : ℝ) :
    (-hubbardEnergyScale t lambda) ^ 2 - (lambda ^ 2 + 4 * t ^ 2) = 0 := by
  simpa [pow_two] using hubbardEnergyScale_root_poly t lambda

theorem hubbardGapClosedForm_nonneg (t lambda : ℝ) :
    0 ≤ hubbardGapClosedForm t lambda := by
  unfold hubbardGapClosedForm hubbardEnergyScale
  refine sub_nonneg.mpr ?_
  calc
    |lambda| = Real.sqrt (lambda ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (lambda ^ 2 + 4 * t ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith

/-- Shell coupling in exact affine form from `phi_of_shell_closed_form`. -/
theorem lambdaShell_closed_form (m : ℕ) (lambda0 coherence : ℝ) :
    lambdaShell m lambda0 coherence = lambda0 * coherence * ((m + 1 : ℝ) / 5) := by
  rw [lambdaShell, Hqiv.phi_of_shell_closed_form, Hqiv.phi_of_shell_closed_form]
  rw [Hqiv.phiTemperatureCoeff_eq_two]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  field_simp [h2]
  ring

/-- If `lambda0*coherence ≥ 0`, shell coupling is monotone in shell index. -/
theorem lambdaShell_monotone (lambda0 coherence : ℝ) (h_nonneg : 0 ≤ lambda0 * coherence) :
    Monotone (fun m => lambdaShell m lambda0 coherence) := by
  intro m n hmn
  have hmnReal : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hsucc : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  have hdiv : ((m + 1 : ℝ) / 5) ≤ ((n + 1 : ℝ) / 5) := by
    have h5 : (0 : ℝ) ≤ 5 := by norm_num
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
      (div_le_div_of_nonneg_right hsucc h5)
  calc
    lambdaShell m lambda0 coherence = lambda0 * coherence * ((m + 1 : ℝ) / 5) := by
      simpa using lambdaShell_closed_form m lambda0 coherence
    _ ≤ lambda0 * coherence * ((n + 1 : ℝ) / 5) := by
      exact mul_le_mul_of_nonneg_left hdiv h_nonneg
    _ = lambdaShell n lambda0 coherence := by
      simpa using (lambdaShell_closed_form n lambda0 coherence).symm

/-- Positive-shell regime: if `lambda0*coherence ≥ 0`, all shell couplings are nonnegative. -/
theorem lambdaShell_nonneg (m : ℕ) (lambda0 coherence : ℝ) (h_nonneg : 0 ≤ lambda0 * coherence) :
    0 ≤ lambdaShell m lambda0 coherence := by
  rw [lambdaShell_closed_form]
  have hfac : 0 ≤ ((m + 1 : ℝ) / 5) := by positivity
  nlinarith

/-- Closed-form shell-gap witness used by the dimer scan bridge. -/
noncomputable def hubbardShellGapClosed (m : ℕ) (t lambda0 coherence : ℝ) : ℝ :=
  hubbardGapClosedForm t (lambdaShell m lambda0 coherence)

theorem hubbardCandidateEnergies_ordered_nonneg (t lambda : ℝ) (hLam : 0 ≤ lambda) :
    (-hubbardEnergyScale t lambda) ≤ (-lambda) ∧
      (-lambda) ≤ lambda ∧
      lambda ≤ hubbardEnergyScale t lambda := by
  have hAbsLe : |lambda| ≤ hubbardEnergyScale t lambda := by
    exact (sub_nonneg.mp (hubbardGapClosedForm_nonneg t lambda))
  rw [abs_of_nonneg hLam] at hAbsLe
  constructor
  · nlinarith
  constructor
  · nlinarith
  · exact hAbsLe

/-- Compact ordered-list relation for the four candidate energies when `λ ≥ 0`. -/
theorem hubbardEigenvalueCandidates_orderedList_nonneg (t lambda : ℝ) (hLam : 0 ≤ lambda) :
    [hubbardEigenvalueCandidates t lambda 0,
      hubbardEigenvalueCandidates t lambda 1,
      hubbardEigenvalueCandidates t lambda 2,
      hubbardEigenvalueCandidates t lambda 3]
      = [-hubbardEnergyScale t lambda, -lambda, lambda, hubbardEnergyScale t lambda] ∧
      ((hubbardEigenvalueCandidates t lambda 0) ≤ (hubbardEigenvalueCandidates t lambda 1) ∧
      (hubbardEigenvalueCandidates t lambda 1) ≤ (hubbardEigenvalueCandidates t lambda 2) ∧
      (hubbardEigenvalueCandidates t lambda 2) ≤ (hubbardEigenvalueCandidates t lambda 3)) := by
  constructor
  · simp [hubbardEigenvalueCandidates, abs_of_nonneg hLam]
  · simpa [hubbardEigenvalueCandidates, abs_of_nonneg hLam] using
      hubbardCandidateEnergies_ordered_nonneg t lambda hLam

theorem hubbardGapClosedForm_eq_ratio_nonneg (t lambda : ℝ) (ht : 0 < t) (hLam : 0 ≤ lambda) :
    hubbardGapClosedForm t lambda = (4 * t ^ 2) / (hubbardEnergyScale t lambda + lambda) := by
  have hsqrt_pos : 0 < hubbardEnergyScale t lambda := by
    unfold hubbardEnergyScale
    apply Real.sqrt_pos.2
    nlinarith [ht]
  have hden_ne : hubbardEnergyScale t lambda + lambda ≠ 0 := by
    linarith
  have hsq : (hubbardEnergyScale t lambda) ^ 2 - lambda ^ 2 = 4 * t ^ 2 := by
    nlinarith [hubbardEnergyScale_root_poly t lambda]
  unfold hubbardGapClosedForm
  rw [abs_of_nonneg hLam]
  calc
    hubbardEnergyScale t lambda - lambda
        = ((hubbardEnergyScale t lambda - lambda) * (hubbardEnergyScale t lambda + lambda)) /
            (hubbardEnergyScale t lambda + lambda) := by
          field_simp [hden_ne]
    _ = (((hubbardEnergyScale t lambda) ^ 2 - lambda ^ 2) / (hubbardEnergyScale t lambda + lambda)) := by
          ring_nf
    _ = (4 * t ^ 2) / (hubbardEnergyScale t lambda + lambda) := by rw [hsq]

/-- Gap decreases as `λ` increases on `λ ≥ 0` (for fixed `t > 0`). -/
theorem hubbardGapClosedForm_antitoneOn_nonneg (t : ℝ) (ht : 0 < t) :
    AntitoneOn (fun lambda => hubbardGapClosedForm t lambda) (Set.Ici 0) := by
  intro lambda1 h1 lambda2 h2 h12
  have h1' : 0 ≤ lambda1 := by simpa using h1
  have h2' : 0 ≤ lambda2 := by simpa using h2
  have hden_pos1 : 0 < hubbardEnergyScale t lambda1 + lambda1 := by
    have hs : 0 < hubbardEnergyScale t lambda1 := by
      unfold hubbardEnergyScale
      apply Real.sqrt_pos.2
      nlinarith [ht]
    linarith [h1']
  have hden_pos2 : 0 < hubbardEnergyScale t lambda2 + lambda2 := by
    have hs : 0 < hubbardEnergyScale t lambda2 := by
      unfold hubbardEnergyScale
      apply Real.sqrt_pos.2
      nlinarith [ht]
    linarith [h2']
  have hsq_le : lambda1 ^ 2 ≤ lambda2 ^ 2 := by
    nlinarith [h1', h2', h12]
  have hsqrt_le : hubbardEnergyScale t lambda1 ≤ hubbardEnergyScale t lambda2 := by
    unfold hubbardEnergyScale
    apply Real.sqrt_le_sqrt
    nlinarith [hsq_le]
  have hden_le :
      hubbardEnergyScale t lambda1 + lambda1 ≤ hubbardEnergyScale t lambda2 + lambda2 := by
    linarith
  have hone_div :
      1 / (hubbardEnergyScale t lambda2 + lambda2) ≤
        1 / (hubbardEnergyScale t lambda1 + lambda1) :=
    one_div_le_one_div_of_le hden_pos1 hden_le
  have hnum_nonneg : 0 ≤ 4 * t ^ 2 := by nlinarith
  have hratio :
      (4 * t ^ 2) / (hubbardEnergyScale t lambda2 + lambda2) ≤
        (4 * t ^ 2) / (hubbardEnergyScale t lambda1 + lambda1) := by
    simpa [div_eq_mul_inv, one_div] using mul_le_mul_of_nonneg_left hone_div hnum_nonneg
  simpa [hubbardGapClosedForm_eq_ratio_nonneg t lambda1 ht h1',
    hubbardGapClosedForm_eq_ratio_nonneg t lambda2 ht h2'] using hratio

theorem hubbardShellGap_antitone (t lambda0 coherence : ℝ) (ht : 0 < t)
    (h_nonneg : 0 ≤ lambda0 * coherence) :
    Antitone (fun m => hubbardShellGapClosed m t lambda0 coherence) := by
  intro m n hmn
  have hLamMono := lambdaShell_monotone lambda0 coherence h_nonneg hmn
  have hLamM : 0 ≤ lambdaShell m lambda0 coherence := lambdaShell_nonneg m lambda0 coherence h_nonneg
  have hLamN : 0 ≤ lambdaShell n lambda0 coherence := lambdaShell_nonneg n lambda0 coherence h_nonneg
  unfold hubbardShellGapClosed
  exact hubbardGapClosedForm_antitoneOn_nonneg t ht hLamM hLamN hLamMono

/-- Ordered-spectrum instantiation for all shell indices listed in `witnessShellMs` (`m=2..8`). -/
theorem hubbardEigenvalueCandidates_ordered_on_witnessShells
    (t lambda0 coherence : ℝ) (h_nonneg : 0 ≤ lambda0 * coherence) :
    ∀ m : ℕ, m ∈ (witnessShellMs : List ℕ) →
      let lam := lambdaShell m lambda0 coherence
      [hubbardEigenvalueCandidates t lam 0,
        hubbardEigenvalueCandidates t lam 1,
        hubbardEigenvalueCandidates t lam 2,
        hubbardEigenvalueCandidates t lam 3]
        = [-hubbardEnergyScale t lam, -lam, lam, hubbardEnergyScale t lam] ∧
        ((hubbardEigenvalueCandidates t lam 0) ≤ (hubbardEigenvalueCandidates t lam 1) ∧
        (hubbardEigenvalueCandidates t lam 1) ≤ (hubbardEigenvalueCandidates t lam 2) ∧
        (hubbardEigenvalueCandidates t lam 2) ≤ (hubbardEigenvalueCandidates t lam 3)) := by
  intro m hm
  have hLam : 0 ≤ lambdaShell m lambda0 coherence :=
    lambdaShell_nonneg m lambda0 coherence h_nonneg
  simpa using
    (hubbardEigenvalueCandidates_orderedList_nonneg t (lambdaShell m lambda0 coherence) hLam)

end Hqiv.QM
