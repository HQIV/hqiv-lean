import HqivSpine.Physics.MandelstamInvariants

/-!
# `HqivSpine.Physics.CrossingSymmetry` — `s`/`t`/`u` channels and crossing

Crossing symmetry in the **all-incoming convention**: four momenta with `p₁+p₂+p₃+p₄ = 0` (an
outgoing particle is an incoming antiparticle, `p → −p`). The three Mandelstam channels are the three
pairwise invariants, and crossing is the statement that negating a momentum exchanges channels while
the squared mass — the Minkowski invariant — is untouched.

* **Reflection invariance.** `Q(−p) = Q(p)` (`mink4_neg`) — the kinematic root of crossing.
* **Channel duality.** Each channel equals its complementary pairing: `s = (p₁+p₂)² = (p₃+p₄)²`
  (`crossing_s`), and likewise `crossing_t`, `crossing_u`.
* **Crossing sum rule.** `s + t + u = ∑mᵢ²` in the all-incoming convention (`crossing_sum`,
  `crossing_sum_onShell`) — the same total as the decay/scattering sum rules, now manifestly symmetric
  under permuting the legs.

Bundled in `CrossingClosure` / `crossing_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.CrossingSymmetry

open HqivSpine.Physics HqivSpine.Physics.MandelstamInvariants

/-- **Reflection invariance** `Q(−p) = Q(p)` — squared mass is blind to the in/out sign. -/
theorem mink4_neg (p : Fin 4 → ℝ) : mink4 (-p) = mink4 p := by
  simp only [mink4, Pi.neg_apply]; ring

/-- **`s`-channel invariant** `(p₁+p₂)²` (all-incoming). -/
def sChan (p1 p2 : Fin 4 → ℝ) : ℝ := mink4 (p1 + p2)

/-- **`t`-channel invariant** `(p₁+p₃)²`. -/
def tChan (p1 p3 : Fin 4 → ℝ) : ℝ := mink4 (p1 + p3)

/-- **`u`-channel invariant** `(p₁+p₄)²`. -/
def uChan (p1 p4 : Fin 4 → ℝ) : ℝ := mink4 (p1 + p4)

/-- **`s`-channel duality:** `(p₁+p₂)² = (p₃+p₄)²`. -/
theorem crossing_s {p1 p2 p3 p4 : Fin 4 → ℝ} (hsum : p1 + p2 + p3 + p4 = 0) :
    sChan p1 p2 = mink4 (p3 + p4) := by
  have h : p1 + p2 = -(p3 + p4) := by
    have hsum' : (p1 + p2) + (p3 + p4) = 0 := by rw [← hsum]; abel
    exact eq_neg_of_add_eq_zero_left hsum'
  unfold sChan; rw [h, mink4_neg]

/-- **`t`-channel duality:** `(p₁+p₃)² = (p₂+p₄)²`. -/
theorem crossing_t {p1 p2 p3 p4 : Fin 4 → ℝ} (hsum : p1 + p2 + p3 + p4 = 0) :
    tChan p1 p3 = mink4 (p2 + p4) := by
  have h : p1 + p3 = -(p2 + p4) := by
    have hsum' : (p1 + p3) + (p2 + p4) = 0 := by rw [← hsum]; abel
    exact eq_neg_of_add_eq_zero_left hsum'
  unfold tChan; rw [h, mink4_neg]

/-- **`u`-channel duality:** `(p₁+p₄)² = (p₂+p₃)²`. -/
theorem crossing_u {p1 p2 p3 p4 : Fin 4 → ℝ} (hsum : p1 + p2 + p3 + p4 = 0) :
    uChan p1 p4 = mink4 (p2 + p3) := by
  have h : p1 + p4 = -(p2 + p3) := by
    have hsum' : (p1 + p4) + (p2 + p3) = 0 := by rw [← hsum]; abel
    exact eq_neg_of_add_eq_zero_left hsum'
  unfold uChan; rw [h, mink4_neg]

/-- **The crossing sum rule:** in the all-incoming convention `s + t + u = ∑ Q(pᵢ)`. -/
theorem crossing_sum (p1 p2 p3 p4 : Fin 4 → ℝ) (hsum : p1 + p2 + p3 + p4 = 0) :
    sChan p1 p2 + tChan p1 p3 + uChan p1 p4 = mink4 p1 + mink4 p2 + mink4 p3 + mink4 p4 := by
  have h0 : p4 0 = -(p1 0 + p2 0 + p3 0) := by
    have := congrFun hsum 0; simp only [Pi.add_apply, Pi.zero_apply] at this; linarith
  have h1 : p4 1 = -(p1 1 + p2 1 + p3 1) := by
    have := congrFun hsum 1; simp only [Pi.add_apply, Pi.zero_apply] at this; linarith
  have h2 : p4 2 = -(p1 2 + p2 2 + p3 2) := by
    have := congrFun hsum 2; simp only [Pi.add_apply, Pi.zero_apply] at this; linarith
  have h3 : p4 3 = -(p1 3 + p2 3 + p3 3) := by
    have := congrFun hsum 3; simp only [Pi.add_apply, Pi.zero_apply] at this; linarith
  simp only [sChan, tChan, uChan, mink4, Pi.add_apply]
  rw [h0, h1, h2, h3]; ring

/-- **Crossing sum rule on-shell:** `s + t + u = m₁² + m₂² + m₃² + m₄²`. -/
theorem crossing_sum_onShell {p1 p2 p3 p4 : Fin 4 → ℝ} {m1 m2 m3 m4 : ℝ}
    (hsum : p1 + p2 + p3 + p4 = 0)
    (h1 : OnShell p1 m1) (h2 : OnShell p2 m2) (h3 : OnShell p3 m3) (h4 : OnShell p4 m4) :
    sChan p1 p2 + tChan p1 p3 + uChan p1 p4 = m1 ^ 2 + m2 ^ 2 + m3 ^ 2 + m4 ^ 2 := by
  rw [crossing_sum p1 p2 p3 p4 hsum]
  rw [show mink4 p1 = m1 ^ 2 from h1, show mink4 p2 = m2 ^ 2 from h2,
    show mink4 p3 = m3 ^ 2 from h3, show mink4 p4 = m4 ^ 2 from h4]

/-! ## Closure -/

/-- **Crossing-symmetry discharge bundle.** -/
structure CrossingClosure : Prop where
  reflection : ∀ p : Fin 4 → ℝ, mink4 (-p) = mink4 p
  s_duality : ∀ {p1 p2 p3 p4 : Fin 4 → ℝ}, p1 + p2 + p3 + p4 = 0 → sChan p1 p2 = mink4 (p3 + p4)
  t_duality : ∀ {p1 p2 p3 p4 : Fin 4 → ℝ}, p1 + p2 + p3 + p4 = 0 → tChan p1 p3 = mink4 (p2 + p4)
  u_duality : ∀ {p1 p2 p3 p4 : Fin 4 → ℝ}, p1 + p2 + p3 + p4 = 0 → uChan p1 p4 = mink4 (p2 + p3)
  sum_rule : ∀ (p1 p2 p3 p4 : Fin 4 → ℝ), p1 + p2 + p3 + p4 = 0 →
    sChan p1 p2 + tChan p1 p3 + uChan p1 p4 = mink4 p1 + mink4 p2 + mink4 p3 + mink4 p4
  sum_rule_onShell : ∀ {p1 p2 p3 p4 : Fin 4 → ℝ} {m1 m2 m3 m4 : ℝ}, p1 + p2 + p3 + p4 = 0 →
    OnShell p1 m1 → OnShell p2 m2 → OnShell p3 m3 → OnShell p4 m4 →
    sChan p1 p2 + tChan p1 p3 + uChan p1 p4 = m1 ^ 2 + m2 ^ 2 + m3 ^ 2 + m4 ^ 2

/-- **Crossing symmetry is discharged:** squared mass is reflection-invariant, each channel equals its
complementary pairing, and `s+t+u = ∑mᵢ²` symmetrically across the legs — PDG-free. -/
theorem crossing_closure : CrossingClosure where
  reflection := mink4_neg
  s_duality := crossing_s
  t_duality := crossing_t
  u_duality := crossing_u
  sum_rule := crossing_sum
  sum_rule_onShell := crossing_sum_onShell

end HqivSpine.Physics.CrossingSymmetry
