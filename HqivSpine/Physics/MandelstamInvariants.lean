import HqivSpine.Physics.RelativisticKinematics

/-!
# `HqivSpine.Physics.MandelstamInvariants` — `2 → 2` scattering invariants and the `s+t+u` sum rule

The scattering companion to `RelativisticKinematics`: the Lorentz-invariant Mandelstam variables
`s, t, u` of a `2 → 2` process and their defining constraint. Purely algebraic on four-momenta;
no PDG number.

* **4D Minkowski form.** `Q(p) = p₀² − p₁² − p₂² − p₃²` with bilinear pairing and polarization
  identity `Q(p+q) = Q(p) + Q(q) + 2B(p,q)` (`mink4_polarization`).
* **Mandelstam sum rule.** With energy–momentum conservation `p₁+p₂ = p₃+p₄`, the three invariants
  satisfy `s + t + u = m₁² + m₂² + m₃² + m₄²` (`mandelstam_sum`), and on-shell this is
  `∑ mᵢ²` (`mandelstam_sum_onShell`).
* **Resonance bridge.** The Breit–Wigner variable *is* the Mandelstam `s`: a `2 → 2` cross-section
  peaks when the invariant mass `s` hits the resonance `M²` (`resonance_peaks_at_invariant_mass`),
  tying the scattering invariants to `RelativisticKinematics.breitWigner`.

Bundled in `MandelstamClosure` / `mandelstam_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.MandelstamInvariants

open HqivSpine.Physics

/-! ## 4D Minkowski quadratic form (signature `+ − − −`) -/

/-- **Minkowski quadratic form** `Q(p) = p₀² − p₁² − p₂² − p₃²` (energy component first). -/
def mink4 (p : Fin 4 → ℝ) : ℝ := (p 0) ^ 2 - (p 1) ^ 2 - (p 2) ^ 2 - (p 3) ^ 2

/-- **Minkowski bilinear pairing** `B(p,q) = p₀q₀ − p₁q₁ − p₂q₂ − p₃q₃`. -/
def mink4Bilin (p q : Fin 4 → ℝ) : ℝ :=
  (p 0) * (q 0) - (p 1) * (q 1) - (p 2) * (q 2) - (p 3) * (q 3)

theorem mink4_self (p : Fin 4 → ℝ) : mink4 p = mink4Bilin p p := by
  unfold mink4 mink4Bilin; ring

/-- **Polarization:** `Q(p+q) = Q(p) + Q(q) + 2 B(p,q)`. -/
theorem mink4_polarization (p q : Fin 4 → ℝ) :
    mink4 (p + q) = mink4 p + mink4 q + 2 * mink4Bilin p q := by
  simp only [mink4, mink4Bilin, Pi.add_apply]; ring

/-! ## Mandelstam invariants -/

/-- **Mandelstam `s`** `= (p₁+p₂)²` — the squared centre-of-mass energy. -/
def sMandelstam (p1 p2 : Fin 4 → ℝ) : ℝ := mink4 (p1 + p2)

/-- **Mandelstam `t`** `= (p₁−p₃)²` — the squared momentum transfer. -/
def tMandelstam (p1 p3 : Fin 4 → ℝ) : ℝ := mink4 (p1 - p3)

/-- **Mandelstam `u`** `= (p₁−p₄)²` — the crossed momentum transfer. -/
def uMandelstam (p1 p4 : Fin 4 → ℝ) : ℝ := mink4 (p1 - p4)

/-- **The Mandelstam sum rule:** with energy–momentum conservation `p₁+p₂ = p₃+p₄`,
`s + t + u = Q(p₁) + Q(p₂) + Q(p₃) + Q(p₄)` (the sum of the four squared masses). -/
theorem mandelstam_sum (p1 p2 p3 p4 : Fin 4 → ℝ) (hcons : p1 + p2 = p3 + p4) :
    sMandelstam p1 p2 + tMandelstam p1 p3 + uMandelstam p1 p4
      = mink4 p1 + mink4 p2 + mink4 p3 + mink4 p4 := by
  have h0 : p4 0 = p1 0 + p2 0 - p3 0 := by
    have := congrFun hcons 0; simp only [Pi.add_apply] at this; linarith
  have h1 : p4 1 = p1 1 + p2 1 - p3 1 := by
    have := congrFun hcons 1; simp only [Pi.add_apply] at this; linarith
  have h2 : p4 2 = p1 2 + p2 2 - p3 2 := by
    have := congrFun hcons 2; simp only [Pi.add_apply] at this; linarith
  have h3 : p4 3 = p1 3 + p2 3 - p3 3 := by
    have := congrFun hcons 3; simp only [Pi.add_apply] at this; linarith
  simp only [sMandelstam, tMandelstam, uMandelstam, mink4, Pi.add_apply, Pi.sub_apply]
  rw [h0, h1, h2, h3]; ring

/-- **On-shell:** a four-momentum is on the mass shell when `Q(p) = m²`. -/
def OnShell (p : Fin 4 → ℝ) (m : ℝ) : Prop := mink4 p = m ^ 2

/-- **Sum rule on-shell:** `s + t + u = m₁² + m₂² + m₃² + m₄²`. -/
theorem mandelstam_sum_onShell {p1 p2 p3 p4 : Fin 4 → ℝ} {m1 m2 m3 m4 : ℝ}
    (hcons : p1 + p2 = p3 + p4)
    (h1 : OnShell p1 m1) (h2 : OnShell p2 m2) (h3 : OnShell p3 m3) (h4 : OnShell p4 m4) :
    sMandelstam p1 p2 + tMandelstam p1 p3 + uMandelstam p1 p4 = m1 ^ 2 + m2 ^ 2 + m3 ^ 2 + m4 ^ 2 := by
  rw [mandelstam_sum p1 p2 p3 p4 hcons]
  rw [show mink4 p1 = m1 ^ 2 from h1, show mink4 p2 = m2 ^ 2 from h2,
    show mink4 p3 = m3 ^ 2 from h3, show mink4 p4 = m4 ^ 2 from h4]

/-! ## Bridge to the resonance lineshape -/

/-- **The Breit–Wigner variable is the Mandelstam `s`:** a `2 → 2` cross-section through a resonance
of mass `M` peaks exactly when the invariant mass `s = (p₁+p₂)²` reaches `M²`. -/
theorem resonance_peaks_at_invariant_mass {M Γ : ℝ} (hM : M ≠ 0) (hΓ : Γ ≠ 0) (p1 p2 : Fin 4 → ℝ) :
    RelativisticKinematics.breitWigner (sMandelstam p1 p2) M Γ
      ≤ RelativisticKinematics.breitWigner (M ^ 2) M Γ :=
  RelativisticKinematics.breitWigner_le_peak hM hΓ _

/-! ## Closure -/

/-- **Mandelstam discharge bundle.** -/
structure MandelstamClosure : Prop where
  polarization : ∀ p q : Fin 4 → ℝ, mink4 (p + q) = mink4 p + mink4 q + 2 * mink4Bilin p q
  sum_rule : ∀ (p1 p2 p3 p4 : Fin 4 → ℝ), p1 + p2 = p3 + p4 →
    sMandelstam p1 p2 + tMandelstam p1 p3 + uMandelstam p1 p4
      = mink4 p1 + mink4 p2 + mink4 p3 + mink4 p4
  sum_rule_onShell : ∀ {p1 p2 p3 p4 : Fin 4 → ℝ} {m1 m2 m3 m4 : ℝ}, p1 + p2 = p3 + p4 →
    OnShell p1 m1 → OnShell p2 m2 → OnShell p3 m3 → OnShell p4 m4 →
    sMandelstam p1 p2 + tMandelstam p1 p3 + uMandelstam p1 p4
      = m1 ^ 2 + m2 ^ 2 + m3 ^ 2 + m4 ^ 2
  resonance_in_s : ∀ {M Γ : ℝ}, M ≠ 0 → Γ ≠ 0 → ∀ p1 p2 : Fin 4 → ℝ,
    RelativisticKinematics.breitWigner (sMandelstam p1 p2) M Γ
      ≤ RelativisticKinematics.breitWigner (M ^ 2) M Γ

/-- **The Mandelstam story is discharged:** the invariant quadratic form polarises, the three
`2 → 2` invariants obey `s+t+u = ∑mᵢ²` under conservation, and the resonance lineshape peaks at the
invariant mass — PDG-free. -/
theorem mandelstam_closure : MandelstamClosure where
  polarization := mink4_polarization
  sum_rule := mandelstam_sum
  sum_rule_onShell := mandelstam_sum_onShell
  resonance_in_s := fun hM hΓ p1 p2 => resonance_peaks_at_invariant_mass hM hΓ p1 p2

end HqivSpine.Physics.MandelstamInvariants
