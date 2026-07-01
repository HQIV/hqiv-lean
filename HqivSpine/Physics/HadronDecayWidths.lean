import HqivSpine.Physics.HadronSpectrum

/-!
# `HqivSpine.Physics.HadronDecayWidths` — phase space and branching ratios

Extending `HadronSpectrum` from masses to **decays**. A channel opens by phase space: the `Q`-value
`Q = M_parent − ∑ M_daughters` must be positive, and the partial width grows as a phase-space power
`Γ = g·Q^p` (the weak `p = 5` of `WeakDecay` is the special case).

* **Threshold.** A decay is allowed iff it is energetically open, `Q > 0 ↔ daughters < parent`
  (`decayAllowed_iff`); the width is then positive (`decayWidth_pos`) and grows with the release
  (`decayWidth_strictMono_in_Q`).
* **Width ratios are phase-space ratios.** Same coupling and power ⇒ `Γ₁/Γ₂ = (Q₁/Q₂)^p`
  (`widthRatio_eq`) — no PDG width input.
* **Branching ratios partition unity.** With `Γ_tot = ∑ Γ_i`, the branching fractions
  `b_i = Γ_i/Γ_tot` are in `[0,1]` (`branchingRatio_nonneg`, `branchingRatio_le_one`) and sum to `1`
  (`branchingRatio_sum`).

Bundled in `DecayClosure` / `hadron_decay_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.HadronDecayWidths

open HqivSpine.Physics

/-! ## Q-value and threshold -/

/-- **Decay `Q`-value:** parent mass minus the total daughter mass. -/
def decayQ (parentMass daughterMassSum : ℝ) : ℝ := parentMass - daughterMassSum

/-- **Threshold:** a decay is energetically open iff the daughters are lighter than the parent. -/
theorem decayAllowed_iff (parentMass daughterMassSum : ℝ) :
    0 < decayQ parentMass daughterMassSum ↔ daughterMassSum < parentMass := by
  unfold decayQ; constructor <;> intro h <;> linarith

/-! ## Phase-space width -/

/-- **Phase-space partial width** `Γ = g·Q^p`. -/
noncomputable def decayWidth (g Q : ℝ) (p : ℕ) : ℝ := g * Q ^ p

theorem decayWidth_pos {g Q : ℝ} (hg : 0 < g) (hQ : 0 < Q) (p : ℕ) : 0 < decayWidth g Q p := by
  unfold decayWidth; positivity

/-- **More phase space ⇒ wider:** the width strictly increases with the energy release. -/
theorem decayWidth_strictMono_in_Q {g : ℝ} (hg : 0 < g) {p : ℕ} (hp : p ≠ 0) {Q Q' : ℝ}
    (hQ : 0 < Q) (h : Q < Q') : decayWidth g Q p < decayWidth g Q' p := by
  unfold decayWidth
  have hpow : Q ^ p < Q' ^ p := by gcongr
  exact mul_lt_mul_of_pos_left hpow hg

/-- **Width ratios are phase-space ratios:** same coupling and power give `Γ₁/Γ₂ = (Q₁/Q₂)^p`. -/
theorem widthRatio_eq {g Q₁ Q₂ : ℝ} (hg : 0 < g) (p : ℕ) :
    decayWidth g Q₁ p / decayWidth g Q₂ p = (Q₁ / Q₂) ^ p := by
  unfold decayWidth
  rw [div_pow, mul_div_mul_left _ _ hg.ne']

/-! ## Branching ratios -/

/-- **Branching ratio** `b = Γ_channel / Γ_total`. -/
noncomputable def branchingRatio (Γi Γtot : ℝ) : ℝ := Γi / Γtot

theorem branchingRatio_nonneg {Γi Γtot : ℝ} (hi : 0 ≤ Γi) (ht : 0 < Γtot) :
    0 ≤ branchingRatio Γi Γtot := div_nonneg hi ht.le

theorem branchingRatio_le_one {Γi Γtot : ℝ} (hle : Γi ≤ Γtot) (ht : 0 < Γtot) :
    branchingRatio Γi Γtot ≤ 1 := by
  unfold branchingRatio; rw [div_le_one ht]; exact hle

/-- **Branching ratios partition unity:** with `Γ_tot = ∑ Γ_i` they sum to `1`. -/
theorem branchingRatio_sum {n : ℕ} (Γ : Fin n → ℝ) (htot : (∑ i, Γ i) ≠ 0) :
    ∑ i, branchingRatio (Γ i) (∑ j, Γ j) = 1 := by
  unfold branchingRatio
  rw [← Finset.sum_div, div_self htot]

/-! ## Closure -/

/-- **Hadron-decay discharge bundle.** -/
structure DecayClosure : Prop where
  allowed_iff : ∀ (parentMass daughterMassSum : ℝ),
    0 < decayQ parentMass daughterMassSum ↔ daughterMassSum < parentMass
  width_positive : ∀ {g Q : ℝ}, 0 < g → 0 < Q → ∀ p : ℕ, 0 < decayWidth g Q p
  phase_space_monotone : ∀ {g : ℝ}, 0 < g → ∀ {p : ℕ}, p ≠ 0 → ∀ {Q Q' : ℝ}, 0 < Q → Q < Q' →
    decayWidth g Q p < decayWidth g Q' p
  branching_partition : ∀ {n : ℕ} (Γ : Fin n → ℝ), (∑ i, Γ i) ≠ 0 →
    ∑ i, branchingRatio (Γ i) (∑ j, Γ j) = 1

/-- **The hadron decay story is discharged:** phase-space thresholds set which channels open, widths
grow as `Q^p`, width ratios are phase-space ratios, and branching fractions partition unity. -/
theorem hadron_decay_closure : DecayClosure where
  allowed_iff := decayAllowed_iff
  width_positive := decayWidth_pos
  phase_space_monotone := decayWidth_strictMono_in_Q
  branching_partition := branchingRatio_sum

end HqivSpine.Physics.HadronDecayWidths
