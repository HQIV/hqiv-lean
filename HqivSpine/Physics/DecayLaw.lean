import HqivSpine.Physics.MultichannelReadout

/-!
# `HqivSpine.Physics.DecayLaw` — the exponential decay law, lifetime, and half-life

The bridge from the spine's decay *widths* to an observable *lifetime*. A state of total width `Γ`
survives with probability `S(t) = e^{−Γt}`; this fixes the lifetime `τ = 1/Γ` and half-life
`t₁⸍₂ = (ln 2)/Γ`.

* **Survival law.** `S(0)=1` (`survival_zero`), `S>0` (`survival_pos`), memoryless
  `S(t)·S(s)=S(t+s)` (`survival_add`), and strictly decreasing for `Γ>0` (`survival_antitone`).
* **Lifetime / half-life.** `Γτ = 1` (`lifetime_mul_width`); after one half-life the survival is exactly
  `1/2` (`survival_halfLife`).
* **Width–lifetime bridge.** The branching fraction of a channel equals its width times the parent
  lifetime, `bᵢ = Γᵢ·τ` (`branching_eq_width_mul_lifetime`), tying `MultichannelReadout` to the clock.

Bundled in `DecayLawClosure` / `decay_law_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.DecayLaw

open HqivSpine.Physics HqivSpine.Physics.MultichannelReadout

/-- **Survival probability** `S(t) = e^{−Γt}` of a state of total width `Γ`. -/
noncomputable def survival (Γ t : ℝ) : ℝ := Real.exp (-(Γ * t))

/-- **Lifetime** `τ = 1/Γ`. -/
noncomputable def lifetime (Γ : ℝ) : ℝ := 1 / Γ

/-- **Half-life** `t₁⸍₂ = (ln 2)/Γ`. -/
noncomputable def halfLife (Γ : ℝ) : ℝ := Real.log 2 / Γ

theorem survival_zero (Γ : ℝ) : survival Γ 0 = 1 := by
  simp [survival]

theorem survival_pos (Γ t : ℝ) : 0 < survival Γ t := Real.exp_pos _

/-- **Memoryless property:** `S(t+s) = S(t)·S(s)`. -/
theorem survival_add (Γ t s : ℝ) : survival Γ (t + s) = survival Γ t * survival Γ s := by
  unfold survival
  rw [← Real.exp_add]
  congr 1; ring

/-- **The survival probability strictly decreases** for a positive width. -/
theorem survival_antitone {Γ : ℝ} (hΓ : 0 < Γ) {t t' : ℝ} (h : t < t') :
    survival Γ t' < survival Γ t := by
  unfold survival
  rw [Real.exp_lt_exp]
  nlinarith

/-- **`Γ τ = 1`** — the width–lifetime reciprocity. -/
theorem lifetime_mul_width {Γ : ℝ} (hΓ : Γ ≠ 0) : Γ * lifetime Γ = 1 := by
  unfold lifetime; field_simp

/-- **After one half-life the survival probability is exactly `1/2`.** -/
theorem survival_halfLife {Γ : ℝ} (hΓ : Γ ≠ 0) : survival Γ (halfLife Γ) = 1 / 2 := by
  unfold survival halfLife
  rw [show Γ * (Real.log 2 / Γ) = Real.log 2 from by field_simp]
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-! ## Bridge to the multichannel readout -/

/-- **Branching = width × parent lifetime:** `bᵢ = Γᵢ · τ`, with `τ = 1/Γ_tot`. -/
theorem branching_eq_width_mul_lifetime {ι : Type*} [Fintype ι] {n : ℕ}
    (g : ι → ℝ) (ch : Fin n → DecayChannel ι) (i : Fin n) :
    branching g ch i = channelWidth g (ch i) * lifetime (totalWidth g ch) := by
  unfold branching lifetime
  rw [mul_one_div]

/-! ## Closure -/

/-- **Decay-law discharge bundle.** -/
structure DecayLawClosure : Prop where
  start_certain : ∀ Γ : ℝ, survival Γ 0 = 1
  positive : ∀ Γ t : ℝ, 0 < survival Γ t
  memoryless : ∀ Γ t s : ℝ, survival Γ (t + s) = survival Γ t * survival Γ s
  decreasing : ∀ {Γ : ℝ}, 0 < Γ → ∀ {t t' : ℝ}, t < t' → survival Γ t' < survival Γ t
  reciprocity : ∀ {Γ : ℝ}, Γ ≠ 0 → Γ * lifetime Γ = 1
  half_life : ∀ {Γ : ℝ}, Γ ≠ 0 → survival Γ (halfLife Γ) = 1 / 2

/-- **The decay law is discharged:** survival starts certain, stays positive, is memoryless and
strictly decreasing, the width and lifetime are reciprocal, and one half-life halves the population —
PDG-free. -/
theorem decay_law_closure : DecayLawClosure where
  start_certain := survival_zero
  positive := survival_pos
  memoryless := survival_add
  decreasing := survival_antitone
  reciprocity := lifetime_mul_width
  half_life := survival_halfLife

end HqivSpine.Physics.DecayLaw
