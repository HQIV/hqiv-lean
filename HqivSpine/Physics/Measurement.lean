import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.Measurement` — Born normalisation and collapse as energy conservation

The **real-carrier** measurement layer, complementing the complex `Physics.VonNeumann`
(observables / Born rule on `ℂ²`). A finite state `ψ : Fin n → ℝ` carries an *informational
energy* `normSq ψ = ∑ (ψ i)²`, and:

* **Born rule** — the normalised weights `(ψ i)²/normSq ψ` are nonnegative and sum to `1`
  (`bornProbN_nonneg`, `sum_bornProbN_eq_one`), and are **forced from first principles**: the
  only probability vector summing to `1` that is *amplitude–square coherent* (`pᵢ|ψⱼ|²=pⱼ|ψᵢ|²`)
  is `bornProbN` — no nonnegativity assumption required (`bornProbN_unique_of_coherence`).
* **Collapse conserves informational energy** — measuring outcome `i` collapses `ψ` to the
  single basis component, whose energy is the Born weight `(ψ i)²`; the remainder goes into an
  **auxiliary transfer channel** that is itself nonnegative, so
  `normSq ψ = normSq (collapse) + auxTransfer` with `auxTransfer ≥ 0`
  (`measurement_energy_closure`, `auxTransfer_nonneg`). No informational energy is destroyed by
  measurement — only repartitioned. This is the monogamy/conservation theme of `Exclusion`
  and `Monogamy` in the measurement register.
* **Redshift channel** — the collapsed energy is *exactly* recoverable through a birefringence
  redshift `z = e^{β/κ} − 1` (`measurement_observed_energy_with_redshift`), the "now"-slice
  bookkeeping that re-expresses the realised outcome's energy as an observed (redshifted) energy
  times its blueshift factor.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.Measurement

open scoped BigOperators

/-- Finite real-carrier state with `n` outcomes. -/
abbrev StateN (n : ℕ) := Fin n → ℝ

/-- Informational energy (squared norm) on the finite carrier. -/
noncomputable def normSq {n : ℕ} (ψ : StateN n) : ℝ :=
  ∑ i : Fin n, (ψ i) ^ 2

/-- Born weight for outcome `i`. -/
def bornWeight {n : ℕ} (ψ : StateN n) (i : Fin n) : ℝ :=
  (ψ i) ^ 2

/-- Born probability for outcome `i`. -/
noncomputable def bornProbN {n : ℕ} (ψ : StateN n) (i : Fin n) : ℝ :=
  bornWeight ψ i / normSq ψ

theorem normSq_nonneg {n : ℕ} (ψ : StateN n) : 0 ≤ normSq ψ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A single Born weight never exceeds the total informational energy. -/
theorem bornWeight_le_normSq {n : ℕ} (ψ : StateN n) (i : Fin n) :
    bornWeight ψ i ≤ normSq ψ :=
  Finset.single_le_sum (fun j _ => sq_nonneg (ψ j)) (Finset.mem_univ i)

theorem normSq_pos_of_exists_nonzero {n : ℕ} (ψ : StateN n)
    (h : ∃ i : Fin n, ψ i ≠ 0) : 0 < normSq ψ := by
  obtain ⟨i, hi⟩ := h
  exact Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨i, Finset.mem_univ i, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))⟩

theorem bornProbN_nonneg {n : ℕ} (ψ : StateN n) (i : Fin n)
    (hpos : 0 < normSq ψ) : 0 ≤ bornProbN ψ i :=
  div_nonneg (sq_nonneg _) hpos.le

theorem sum_bornWeight_eq_normSq {n : ℕ} (ψ : StateN n) :
    (∑ i : Fin n, bornWeight ψ i) = normSq ψ := rfl

/-- **Born normalisation:** the outcome probabilities sum to `1`. -/
theorem sum_bornProbN_eq_one {n : ℕ} (ψ : StateN n) (hden : normSq ψ ≠ 0) :
    (∑ i : Fin n, bornProbN ψ i) = 1 := by
  unfold bornProbN bornWeight
  rw [← Finset.sum_div]
  exact div_self hden

/-! ## Born rule from first principles (ratio uniqueness)

The Born weights are not an ad-hoc choice: they are the **unique** normalised nonnegative
probability assignment satisfying *amplitude–square coherence* (`pᵢ|ψⱼ|² = pⱼ|ψᵢ|²`). -/

/-- Squared-amplitude coherence: probabilities track amplitude squares pairwise. -/
def BornCoherent {n : ℕ} (ψ : StateN n) (p : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, (ψ j) ^ 2 * p i = (ψ i) ^ 2 * p j

theorem bornProbN_coherent {n : ℕ} (ψ : StateN n) :
    BornCoherent ψ (bornProbN ψ) := by
  intro i j
  have hcomm : (ψ j) ^ 2 * (ψ i) ^ 2 = (ψ i) ^ 2 * (ψ j) ^ 2 := by ring
  simp only [bornProbN, bornWeight, mul_div_assoc']
  rw [hcomm]

/-- **Uniqueness (first principles):** any probability vector that sums to `1` and is
Born-coherent for nonzero `ψ` equals `bornProbN ψ` — *no nonnegativity assumption needed*. So
the Born weights are **forced** by coherence + normalisation, not assumed. -/
theorem bornProbN_unique_of_coherence {n : ℕ} (ψ : StateN n) (p : Fin n → ℝ)
    (hsum : (∑ i : Fin n, p i) = 1)
    (hcoh : BornCoherent ψ p)
    (hψ : ∃ k : Fin n, ψ k ≠ 0) :
    ∀ i : Fin n, p i = bornProbN ψ i := by
  have hpos : 0 < normSq ψ := normSq_pos_of_exists_nonzero ψ hψ
  have hden : normSq ψ ≠ 0 := ne_of_gt hpos
  rcases hψ with ⟨j0, hj0⟩
  have hj0sq : 0 < (ψ j0) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj0))
  have hsumj0 : ((ψ j0) ^ 2 : ℝ) * (∑ i : Fin n, p i) = p j0 * normSq ψ := by
    rw [Finset.mul_sum, normSq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hcoh i j0]; ring
  rw [hsum, mul_one] at hsumj0
  have hpj0 : p j0 = (ψ j0) ^ 2 / normSq ψ := by
    rw [hsumj0]; field_simp
  intro i
  by_cases hi : ψ i = 0
  · have hci0 : (ψ j0) ^ 2 * p i = 0 := by
      have h := hcoh i j0; rw [hi] at h; simpa using h
    have pi0 : p i = 0 := by
      rcases mul_eq_zero.mp hci0 with h | h
      · exact absurd h (ne_of_gt hj0sq)
      · exact h
    simp [bornProbN, bornWeight, pi0, hi]
  · have hci := hcoh i j0
    rw [hpj0] at hci
    unfold bornProbN bornWeight
    field_simp [hden, hi] at hci ⊢
    nlinarith [hci, hj0sq, hpos]

/-! ## Collapse and informational-energy conservation -/

/-- Outcome-conditioned collapse to basis outcome `i`. -/
def collapseTo {n : ℕ} (i : Fin n) (ψ : StateN n) : StateN n :=
  fun j => if j = i then ψ i else 0

theorem collapseTo_support {n : ℕ} (i : Fin n) (ψ : StateN n) :
    ∀ j : Fin n, j ≠ i → collapseTo i ψ j = 0 := fun j hj => by
  simp [collapseTo, hj]

theorem normSq_collapseTo_eq_weight {n : ℕ} (i : Fin n) (ψ : StateN n) :
    normSq (collapseTo i ψ) = bornWeight ψ i := by
  unfold normSq collapseTo bornWeight
  simp

/-- Energy routed into the auxiliary (non-realised) channel on outcome `i`. -/
noncomputable def auxTransfer {n : ℕ} (i : Fin n) (ψ : StateN n) : ℝ :=
  normSq ψ - normSq (collapseTo i ψ)

/-- **Collapse conserves informational energy:** total = realised outcome + auxiliary channel. -/
theorem measurement_energy_closure {n : ℕ} (i : Fin n) (ψ : StateN n) :
    normSq ψ = normSq (collapseTo i ψ) + auxTransfer i ψ := by
  unfold auxTransfer; ring

/-- The auxiliary channel never carries negative energy. -/
theorem auxTransfer_nonneg {n : ℕ} (i : Fin n) (ψ : StateN n) :
    0 ≤ auxTransfer i ψ := by
  unfold auxTransfer
  rw [normSq_collapseTo_eq_weight]
  linarith [bornWeight_le_normSq ψ i]

/-! ## Redshift recovery channel ("now"-slice bookkeeping) -/

/-- Redshifted observed energy channel. -/
noncomputable def redshiftedEnergyN (Epost z : ℝ) : ℝ :=
  Epost / (1 + z)

/-- Birefringence-linked redshift in the HQIV "now" bookkeeping chain. -/
noncomputable def birefringenceRedshiftN (betaRad kappaBeta : ℝ) : ℝ :=
  Real.exp (betaRad / kappaBeta) - 1

theorem one_add_birefringenceRedshiftN (betaRad kappaBeta : ℝ) :
    1 + birefringenceRedshiftN betaRad kappaBeta = Real.exp (betaRad / kappaBeta) := by
  unfold birefringenceRedshiftN; ring

/-- The redshift channel exactly recovers the source energy: observed × blueshift = source. -/
theorem redshiftedEnergyN_birefringence_balance (Epost betaRad kappaBeta : ℝ) :
    redshiftedEnergyN Epost (birefringenceRedshiftN betaRad kappaBeta)
      * Real.exp (betaRad / kappaBeta) = Epost := by
  unfold redshiftedEnergyN
  rw [one_add_birefringenceRedshiftN]
  field_simp

/-- **Observed-energy decomposition:** the realised outcome's energy is recoverable through the
redshift channel, and total informational energy still splits as realised + auxiliary. -/
theorem measurement_observed_energy_with_redshift
    {n : ℕ} (i : Fin n) (ψ : StateN n) (betaRad kappaBeta : ℝ) :
    normSq ψ
      = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransfer i ψ := by
  rw [redshiftedEnergyN_birefringence_balance]
  exact measurement_energy_closure i ψ

end HqivSpine.Physics.Measurement
