import HqivSpine.Physics.NeutrinoMixing
import HqivSpine.Physics.MassDrivenMixing

/-!
# `HqivSpine.Physics.PMNSCrossCheck` — asking the mixing question from two places

The mixing structure is now derivable along **two independent routes**, and this module makes them
meet — turning agreement into a *prediction* about the neutrino mass spectrum.

* **Route A — geometry/incidence.** `NeutrinoMixing` gives the atmospheric angle `θ₂₃ = π/4`
  (maximal, from the lock-in shell `4 = 2²`), and `FanoMixingWeights` gives the solar fraction
  `sin²θ₁₂ = 1/3` (Fano democratic baseline). These are the tri-bimaximal values, fixed by geometry.
* **Route B — the mass transfer function.** `MassDrivenMixing` gives `sin²θ = m_light/(m_light+m_heavy)`
  as an exact, invertible function of the generation mass ratio.

**Where the two routes meet pins the spectrum.** Equating them inverts the transfer function:
* maximal `θ₂₃ = π/4` ⇔ `sin²θ = 1/2` ⇔ **mass degeneracy** `m_light = m_heavy`
  (`sinθMass_sq_eq_half_iff`, `atmospheric_forces_degeneracy`);
* democratic `θ₁₂` with `sin²θ = 1/3` ⇔ **leading ladder rung** `m_heavy = 2·m_light`
  (`sinθMass_sq_eq_third_iff`, `solar_forces_leading_rung`) — exactly the Beltrami step `λ = 1 : 2`.

So both PMNS routes demand a **mild** neutrino spectrum (ratios `1` and `2`). The same transfer
function with a **steep** quark spectrum gives **small** CKM angles (`steeper_is_smaller`): one
mechanism, two regimes — large lepton mixing and small quark mixing are the mild-vs-steep faces of
the identical `sin²θ = m_light/(m_light+m_heavy)` law.

**Honest scope.** The two routes and their meeting points are *derived*; what they jointly *predict*
is the implied mass-ratio (`1`, `2`) in each neutrino sector — a near-degenerate spectrum — which is a
testable consequence, not an absolute-mass derivation (that scale stays the `MassLadder` frontier).

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.PMNSCrossCheck

open HqivSpine.Physics
open HqivSpine.Physics.MassDrivenMixing
open HqivSpine.Physics.FanoMixingWeights

/-! ## Inverting the transfer function at the geometric values -/

/-- **Maximal mixing ⇔ mass degeneracy:** `sin²θ = 1/2` exactly when the sector masses coincide. -/
theorem sinθMass_sq_eq_half_iff {mL mH : ℝ} (hL : 0 < mL) (hH : 0 < mH) :
    sinθMass mL mH ^ 2 = 1 / 2 ↔ mL = mH := by
  rw [sinθMass_sq hL hH, div_eq_iff (add_pos hL hH).ne']
  constructor <;> intro h <;> linarith

/-- **Democratic mixing ⇔ leading ladder rung:** `sin²θ = 1/3` exactly when `m_heavy = 2·m_light`,
the Beltrami step `λ = 1 : 2`. -/
theorem sinθMass_sq_eq_third_iff {mL mH : ℝ} (hL : 0 < mL) (hH : 0 < mH) :
    sinθMass mL mH ^ 2 = 1 / 3 ↔ mH = 2 * mL := by
  rw [sinθMass_sq hL hH, div_eq_iff (add_pos hL hH).ne']
  constructor <;> intro h <;> linarith

/-! ## Route A values, as `sin²θ` -/

/-- The geometric atmospheric angle `π/4` has `sin²θ₂₃ = 1/2` (maximal). -/
theorem neutrino_atmospheric_sinSq : Real.sin neutrinoMixingAngle ^ 2 = 1 / 2 := by
  rw [neutrinoMixingAngle_eq_pi_div_four, Real.sin_pi_div_four, div_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

/-! ## Where the two routes meet -/

/-- **Two-place cross-check (atmospheric):** if the geometric maximal angle equals the
mass-transfer-function angle, the neutrino sector masses must be **degenerate**. -/
theorem atmospheric_forces_degeneracy {mL mH : ℝ} (hL : 0 < mL) (hH : 0 < mH)
    (h : Real.sin neutrinoMixingAngle ^ 2 = sinθMass mL mH ^ 2) : mL = mH := by
  rw [neutrino_atmospheric_sinSq] at h
  exact (sinθMass_sq_eq_half_iff hL hH).mp h.symm

/-- **Two-place cross-check (solar):** if the Fano democratic fraction equals the
mass-transfer-function angle, the neutrino sector sits on the **leading ladder rung**
`m_heavy = 2·m_light`. -/
theorem solar_forces_leading_rung {mL mH : ℝ} (hL : 0 < mL) (hH : 0 < mH)
    (h : sinθFano ^ 2 = sinθMass mL mH ^ 2) : mH = 2 * mL := by
  rw [sinθFano_sq] at h
  exact (sinθMass_sq_eq_third_iff hL hH).mp h.symm

/-! ## One mechanism, two regimes: large lepton vs small quark mixing -/

/-- **Steep beats mild:** the *same* transfer function gives a strictly smaller angle for the
steeper (quark) spectrum than for the milder (neutrino) spectrum. Large PMNS and small CKM mixing
are the two regimes of one law. -/
theorem steeper_is_smaller {mLν mHν mLq mHq : ℝ}
    (hLν : 0 < mLν) (hHν : 0 < mHν) (hLq : 0 < mLq) (hHq : 0 < mHq)
    (h : mHν / mLν < mHq / mLq) :
    sinθMass mLq mHq ^ 2 < sinθMass mLν mHν ^ 2 :=
  angle_strictAnti_in_massRatio hLν hHν hLq hHq h

/-! ## Closure -/

/-- **PMNS two-place discharge bundle.** -/
structure PMNSCrossCheckDischarged : Prop where
  atmospheric_value : Real.sin neutrinoMixingAngle ^ 2 = 1 / 2
  maximal_iff_degenerate : ∀ {mL mH : ℝ}, 0 < mL → 0 < mH →
    (sinθMass mL mH ^ 2 = 1 / 2 ↔ mL = mH)
  democratic_iff_leading_rung : ∀ {mL mH : ℝ}, 0 < mL → 0 < mH →
    (sinθMass mL mH ^ 2 = 1 / 3 ↔ mH = 2 * mL)
  atmospheric_predicts_degeneracy : ∀ {mL mH : ℝ}, 0 < mL → 0 < mH →
    Real.sin neutrinoMixingAngle ^ 2 = sinθMass mL mH ^ 2 → mL = mH
  solar_predicts_leading_rung : ∀ {mL mH : ℝ}, 0 < mL → 0 < mH →
    sinθFano ^ 2 = sinθMass mL mH ^ 2 → mH = 2 * mL
  one_mechanism_two_regimes : ∀ {mLν mHν mLq mHq : ℝ}, 0 < mLν → 0 < mHν → 0 < mLq → 0 < mHq →
    mHν / mLν < mHq / mLq → sinθMass mLq mHq ^ 2 < sinθMass mLν mHν ^ 2

/-- **The mixing question, answered from two places.** The geometric/incidence route (`π/4`, `1/3`)
and the mass-transfer-function route meet exactly at a mild, near-degenerate neutrino spectrum
(ratios `1` and `2`), while a steep quark spectrum gives small CKM angles through the *same* law. -/
theorem pmnsCrossCheckDischarged_holds : PMNSCrossCheckDischarged where
  atmospheric_value := neutrino_atmospheric_sinSq
  maximal_iff_degenerate := sinθMass_sq_eq_half_iff
  democratic_iff_leading_rung := sinθMass_sq_eq_third_iff
  atmospheric_predicts_degeneracy := atmospheric_forces_degeneracy
  solar_predicts_leading_rung := solar_forces_leading_rung
  one_mechanism_two_regimes := steeper_is_smaller

end HqivSpine.Physics.PMNSCrossCheck
