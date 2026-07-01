import HqivSpine.Physics.LadderMixingHierarchy

/-!
# `HqivSpine.Physics.MassDrivenMixing` — the residual hierarchy *is* the mass spectrum

`LadderMixingHierarchy` bent the democratic `1/3` with the **derived linear ladder** `λ(g)=g+1`, but
that ladder is too mild for the steep measured mixing. This module discharges the remaining gap by
making the Gatto–Sartori–Tonin relation a precise **transfer function**: the mixing fraction is a
*monotone, invertible* function of the generation **mass ratio**, so the residual smallness of the
angles is exactly the steepness of the mass spectrum — "the gap comes from mass."

* **Gap = mass ratio.** `sin²θ = m_light/(m_light+m_heavy) = (1 + m_heavy/m_light)⁻¹`
  (`sinθMass_sq`, `sinθMass_sq_eq_oneDiv`): the angle is a strictly decreasing function of the mass
  ratio `m_heavy/m_light` (`angle_strictAnti_in_massRatio`). A steeper hierarchy *is* a smaller angle.
* **A geometric mass ladder closes it.** For `m(g)=m₀·rᵍ` the fraction is the closed form
  `sin²θ(gₗ,gₕ)=1/(1+r^{gₕ−gₗ})` (`geomMixing_sq`), strictly decreasing in the steepness `r`
  (`geomMixing_strictAnti_r`) and reaching **any** target: for every `ε>0` some `r` gives
  `sin²θ<ε` (`geomMixing_lt_eps`).
* **Steep mass beats the mild ladder.** A geometric ladder with `r>2` is strictly below the linear
  Beltrami-ladder angle of `LadderMixingHierarchy` (`geom_below_linear`): going steeper *in mass*
  carries the prediction past the democratic regime toward the observed small angles.

**Honest scope.** The transfer function (angle ⇔ mass ratio) and the geometric closed form are
*derived*. What is **not** derived here is the steepness `r` itself: the absolute/steep generation
mass spectrum is the `MassLadder` frontier (`leptonAbsoluteScaleFrontier`, `heavyQuarkScaleFrontier`).
So this reduces the open mixing question to a single, sharply-stated input — *how steep is the mass
ladder* — rather than a separate mixing mechanism. Pin the steep spectrum and the angles follow.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.MassDrivenMixing

open HqivSpine.Physics
open HqivSpine.Physics.CabibboInterference
open HqivSpine.Physics.LadderMixingHierarchy

/-! ## The transfer function: angle ⇔ mass ratio -/

/-- Sine of the sector mixing angle driven by a generic positive mass pair. -/
noncomputable def sinθMass (mL mH : ℝ) : ℝ := sinθ mL mH

/-- **GST mixing fraction:** `sin²θ = m_light/(m_light+m_heavy)`. -/
theorem sinθMass_sq {mL mH : ℝ} (hL : 0 < mL) (hH : 0 < mH) :
    sinθMass mL mH ^ 2 = mL / (mL + mH) := by
  unfold sinθMass sinθ
  rw [Real.sq_sqrt (div_nonneg hL.le (add_pos hL hH).le)]

/-- **The angle is a function of the mass ratio:** `sin²θ = (1 + m_heavy/m_light)⁻¹`,
written as `1/(1 + m_heavy/m_light)`. -/
theorem sinθMass_sq_eq_oneDiv {mL mH : ℝ} (hL : 0 < mL) (hH : 0 < mH) :
    sinθMass mL mH ^ 2 = 1 / (1 + mH / mL) := by
  rw [sinθMass_sq hL hH]
  field_simp

/-- **The gap comes from mass:** a steeper hierarchy (larger `m_heavy/m_light`) gives a strictly
smaller mixing fraction. -/
theorem angle_strictAnti_in_massRatio {mL mH mL' mH' : ℝ}
    (hL : 0 < mL) (hH : 0 < mH) (hL' : 0 < mL') (hH' : 0 < mH')
    (h : mH / mL < mH' / mL') :
    sinθMass mL' mH' ^ 2 < sinθMass mL mH ^ 2 := by
  rw [sinθMass_sq_eq_oneDiv hL' hH', sinθMass_sq_eq_oneDiv hL hH]
  have hpos : 0 < mH / mL := div_pos hH hL
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-! ## A geometric mass ladder closes the gap -/

/-- Geometric mass ladder `m(g) = m₀ · rᵍ` (steepness `r`). -/
noncomputable def geomMass (m0 r : ℝ) (g : ℕ) : ℝ := m0 * r ^ g

theorem geomMass_pos {m0 r : ℝ} (hm : 0 < m0) (hr : 0 < r) (g : ℕ) : 0 < geomMass m0 r g := by
  unfold geomMass; positivity

/-- **Geometric closed form:** `sin²θ(gₗ,gₕ) = 1/(1 + r^{gₕ−gₗ})`. -/
theorem geomMixing_sq {m0 r : ℝ} (hm : 0 < m0) (hr : 0 < r) {gL gH : ℕ} (h : gL ≤ gH) :
    sinθMass (geomMass m0 r gL) (geomMass m0 r gH) ^ 2 = 1 / (1 + r ^ (gH - gL)) := by
  rw [sinθMass_sq_eq_oneDiv (geomMass_pos hm hr gL) (geomMass_pos hm hr gH)]
  have hratio : geomMass m0 r gH / geomMass m0 r gL = r ^ (gH - gL) := by
    unfold geomMass
    rw [mul_div_mul_left _ _ hm.ne', pow_sub₀ r hr.ne' h, div_eq_mul_inv]
  rw [hratio]

/-- **Steeper mass ⇒ smaller angle:** for a fixed split the geometric mixing fraction strictly
decreases as the steepness `r` grows. -/
theorem geomMixing_strictAnti_r {m0 : ℝ} (hm : 0 < m0) {gL gH : ℕ} (h : gL < gH)
    {r r' : ℝ} (hr : 0 < r) (hrr : r < r') :
    sinθMass (geomMass m0 r' gL) (geomMass m0 r' gH) ^ 2
      < sinθMass (geomMass m0 r gL) (geomMass m0 r gH) ^ 2 := by
  rw [geomMixing_sq hm (by linarith) h.le, geomMixing_sq hm hr h.le]
  apply one_div_lt_one_div_of_lt (by positivity)
  have hpow : r ^ (gH - gL) < r' ^ (gH - gL) := pow_lt_pow_left₀ hrr hr.le (by omega)
  linarith

/-- **Any observed smallness is reachable from mass:** for every target `ε ∈ (0,1)` there is a
steepness `r` whose geometric mixing fraction falls below `ε`. -/
theorem geomMixing_lt_eps {m0 ε : ℝ} (hm : 0 < m0) (hε : 0 < ε) (hε1 : ε < 1)
    {gL gH : ℕ} (h : gL < gH) :
    ∃ r : ℝ, 0 < r ∧ sinθMass (geomMass m0 r gL) (geomMass m0 r gH) ^ 2 < ε := by
  refine ⟨1 / ε, by positivity, ?_⟩
  rw [geomMixing_sq hm (by positivity) h.le]
  set r : ℝ := 1 / ε with hrdef
  have hrpos : 0 < r := by positivity
  have hr1 : 1 ≤ r := by rw [hrdef, le_div_iff₀ hε]; linarith
  have hpow : r ≤ r ^ (gH - gL) := le_self_pow₀ hr1 (by omega)
  have hstep : (1 : ℝ) / (1 + r ^ (gH - gL)) ≤ 1 / (1 + r) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hlt : (1 : ℝ) / (1 + r) < ε := by
    rw [div_lt_iff₀ (by linarith), hrdef]
    have hclear : ε * (1 + 1 / ε) = ε + 1 := by field_simp
    rw [hclear]; linarith
  linarith

/-! ## Steep mass beats the mild linear ladder -/

/-- **Going steeper in mass carries the prediction below the linear-ladder regime:** a geometric
ladder with steepness `r > 2` gives a strictly smaller mixing fraction than the derived linear
Beltrami ladder of `LadderMixingHierarchy`, for the same generation pair `(0, gₕ)`. -/
theorem geom_below_linear {m0 r : ℝ} (hm : 0 < m0) (hr : 2 < r) {gH : ℕ} (h : 1 ≤ gH) :
    sinθMass (geomMass m0 r 0) (geomMass m0 r gH) ^ 2 < sinθLadder 0 gH ^ 2 := by
  rw [geomMixing_sq hm (by linarith) (Nat.zero_le gH), sinθLadder_sq]
  simp only [Nat.cast_zero, zero_add, Nat.sub_zero]
  apply one_div_lt_one_div_of_lt (by positivity)
  have hnat : gH + 1 ≤ 2 ^ gH := Nat.succ_le_of_lt gH.lt_two_pow_self
  have hbound : (gH : ℝ) + 1 ≤ 2 ^ gH := by
    calc (gH : ℝ) + 1 = ((gH + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ gH : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (2 : ℝ) ^ gH := by push_cast; ring
  have hstrict : (2 : ℝ) ^ gH < r ^ gH := pow_lt_pow_left₀ hr (by norm_num) (by omega)
  linarith

/-! ## Closure -/

/-- **Mass-driven-mixing discharge bundle.** -/
structure MassDrivenMixingDischarged : Prop where
  transfer : ∀ {mL mH : ℝ}, 0 < mL → 0 < mH → sinθMass mL mH ^ 2 = 1 / (1 + mH / mL)
  steeper_smaller : ∀ {mL mH mL' mH' : ℝ}, 0 < mL → 0 < mH → 0 < mL' → 0 < mH' →
    mH / mL < mH' / mL' → sinθMass mL' mH' ^ 2 < sinθMass mL mH ^ 2
  geometric_closed_form : ∀ {m0 r : ℝ}, 0 < m0 → 0 < r → ∀ {gL gH : ℕ}, gL ≤ gH →
    sinθMass (geomMass m0 r gL) (geomMass m0 r gH) ^ 2 = 1 / (1 + r ^ (gH - gL))
  reaches_any_target : ∀ {m0 ε : ℝ}, 0 < m0 → 0 < ε → ε < 1 → ∀ {gL gH : ℕ}, gL < gH →
    ∃ r : ℝ, 0 < r ∧ sinθMass (geomMass m0 r gL) (geomMass m0 r gH) ^ 2 < ε

/-- **The residual mixing hierarchy is the mass spectrum.** The GST relation is an exact, monotone,
invertible transfer function from the generation mass ratio to the mixing fraction; a geometric mass
ladder of steepness `r` reaches any observed angle. The remaining input is the steepness of the mass
spectrum itself — the `MassLadder` absolute-scale frontier — not a separate mixing mechanism. -/
theorem massDrivenMixingDischarged_holds : MassDrivenMixingDischarged where
  transfer := sinθMass_sq_eq_oneDiv
  steeper_smaller := angle_strictAnti_in_massRatio
  geometric_closed_form := geomMixing_sq
  reaches_any_target := geomMixing_lt_eps

end HqivSpine.Physics.MassDrivenMixing
