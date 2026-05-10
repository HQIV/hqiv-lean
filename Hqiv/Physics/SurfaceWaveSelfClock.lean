import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.ComptonHorizonPhase
import Hqiv.Physics.BaryogenesisCore

/-!
# Surface-wave self-clock and rapidity updates (time-only dynamics)

The particle surface stores only its own **self-clock** (Compton phase loop). Each interaction
adds a rapidity increment `φ * Δt` from the global lapse story (`HQVM_lapse`, `timeAngle`).

The **Mexican-hat** potential `V_eff(m, φt) := 1 / effCorrected(δ_global, m)` uses the same
`δ_global = λ · (Φ + φ·t)` as `GlobalDetuning` (`fromLapseScalars`).

* **In `m` at fixed `t`:** for `0 ≤ δ_global`, larger shells have larger `effCorrected`
  (`effCorrected_strictMono_nat`), hence **smaller** `V_eff` — see `mexicanHatVeff_lt_of_shell_lt`.
* **In `t` at fixed `m`:** for `λ > 0` and `φ > 0`, `δ_global` strictly increases in `t`
  (`deltaGlobal_strictMono_in_t`), so `effCorrected` **decreases** (`effCorrected_lt_of_lt_delta`) and
  **`V_eff = 1 / eff` strictly increases** — see `mexicanHatVeff_lt_of_lt_time`.

Together, these match “stretching” (denominator grows with `Φ + φ·t`) and the **outward migration**
of the discrete shell-wise minimum in `m`; the **value** of `V_eff` along the time direction at fixed
`m` goes **up**, not down.

Purely **local and temporal** (phase vs. time); no spatial warping is asserted here.
-/

namespace Hqiv.Physics

open scoped Real
open Hqiv

noncomputable section

/-- Compton-scale angular frequency at shell `m`: `(m+1)` in natural units (`T m = 1/(m+1)`). -/
noncomputable def comptonAngularFrequency (m : ℕ) : ℝ :=
  (m + 1 : ℝ)

/-- Quarter-turn phase at the lock-in shell (`m_lockin = referenceM`), used as the τ birth baseline. -/
noncomputable def compton_quarter_turn_at_T_lockin : ℝ :=
  comptonAngularFrequency m_lockin * (Real.pi / 2)

/-- Self-clock phase loop on the horizon shell surface, updated by cumulative rapidity. -/
noncomputable def selfClockPhase (m : ℕ) (cumulativeRapidity : ℝ) : ℝ :=
  comptonAngularFrequency m * (Real.pi / 2) + cumulativeRapidity

/-- Mexican-hat potential: inverse δ-corrected surface with global detuning from lapse scalars. -/
noncomputable def mexicanHatVeff (lam Φ φ t : ℝ) (m : ℕ) : ℝ :=
  1 / effCorrected (deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t)) m

theorem selfClock_rapidity_update (m : ℕ) (cumulativeRapidity phi Δt : ℝ) :
    selfClockPhase m (cumulativeRapidity + phi * Δt) =
      selfClockPhase m cumulativeRapidity + phi * Δt := by
  unfold selfClockPhase
  ring

/-- Larger shells have **lower** `mexicanHatVeff` when `δ_global ≥ 0` and denominators stay positive. -/
theorem mexicanHatVeff_lt_of_shell_lt (lam Φ φ t : ℝ) {m n : ℕ} (hmn : m < n)
    (hδ : 0 ≤ deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t))
    (hδm : RindlerDenDeltaPos (deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t)) m)
    (_hδn : RindlerDenDeltaPos (deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t)) n) :
    mexicanHatVeff lam Φ φ t n < mexicanHatVeff lam Φ φ t m := by
  unfold mexicanHatVeff
  let δ := deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t)
  have hmono : effCorrected δ m < effCorrected δ n :=
    effCorrected_strictMono_nat hδ hmn
  have hm : 0 < effCorrected δ m := effCorrected_pos δ m hδm
  exact one_div_lt_one_div_of_lt hm hmono

/-- At fixed shell `m`, `V_eff` **increases** in time: larger `t` ⇒ larger `δ` ⇒ smaller `eff` ⇒ larger `1/eff`. -/
theorem mexicanHatVeff_lt_of_lt_time (lam Φ φ : ℝ) (m : ℕ) (t1 t2 : ℝ) (h_lam : 0 < lam) (h_phi : 0 < φ)
    (h_t : t1 < t2)
    (hδ1 : RindlerDenDeltaPos (deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t1)) m)
    (hδ2 : RindlerDenDeltaPos (deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t2)) m) :
    mexicanHatVeff lam Φ φ t1 m < mexicanHatVeff lam Φ φ t2 m := by
  unfold mexicanHatVeff
  let δ1 := deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t1)
  let δ2 := deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t2)
  have hδlt : δ1 < δ2 := deltaGlobal_strictMono_in_t lam Φ φ t1 t2 h_lam h_phi h_t
  have heff : effCorrected δ2 m < effCorrected δ1 m := effCorrected_lt_of_lt_delta m hδlt hδ1 hδ2
  exact one_div_lt_one_div_of_lt (effCorrected_pos δ2 m hδ2) heff

end

end Hqiv.Physics
