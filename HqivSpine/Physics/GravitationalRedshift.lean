import HqivSpine.Physics.NowSlice

/-!
# `HqivSpine.Physics.GravitationalRedshift` — the shift from the lapse ratio

A photon's frequency tracks the clock rate, and the clock rate is the HQVM lapse `N` carried by
`NowSlice`. A photon emitted where the lapse is `N_e` and received where it is `N_o` is shifted by
`1 + z = N_o/N_e`, i.e. `z = N_o/N_e − 1`.

* **Sign of the shift.** Climbing out of a well (`N_e < N_o`) gives a genuine **redshift** `z > 0`
  (`redshift_pos`); falling in gives a **blueshift** (`redshift_neg`); equal lapses give no shift
  (`redshift_zero_iff`).
* **Deeper wells shift more.** For a fixed observer the redshift strictly decreases in the emission
  lapse (`redshift_strictAnti_in_emit`) — emission from deeper in the potential is shifted further.
* **Shifts compose.** The redshift *factors* multiply along a relay `e → m → o`
  (`redshiftFactor_compose`).
* **Now-slice anchor.** Between two slices the shift is the ratio of their lapses
  (`nowSlice_redshift_eq`), so a more redshifted source sits on a slice with smaller lapse
  (`nowSlice_redshift_pos`) — no new input beyond the now slice.

Bundled in `RedshiftClosure` / `gravitational_redshift_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.GravitationalRedshift

open HqivSpine.Physics

/-- **Redshift factor** `1 + z = N_o/N_e` (ratio of receiver to emitter lapse). -/
noncomputable def redshiftFactor (Nemit Nobs : ℝ) : ℝ := Nobs / Nemit

/-- **Redshift** `z = N_o/N_e − 1`. -/
noncomputable def redshift (Nemit Nobs : ℝ) : ℝ := Nobs / Nemit - 1

/-- **Climbing out of a well redshifts:** `N_e < N_o ⇒ z > 0`. -/
theorem redshift_pos {Nemit Nobs : ℝ} (hNe : 0 < Nemit) (h : Nemit < Nobs) :
    0 < redshift Nemit Nobs := by
  unfold redshift
  have : 1 < Nobs / Nemit := (one_lt_div hNe).mpr h
  linarith

/-- **Falling in blueshifts:** `N_o < N_e ⇒ z < 0`. -/
theorem redshift_neg {Nemit Nobs : ℝ} (hNo : 0 < Nobs) (h : Nobs < Nemit) :
    redshift Nemit Nobs < 0 := by
  unfold redshift
  have hNe : 0 < Nemit := lt_trans hNo h
  have : Nobs / Nemit < 1 := (div_lt_one hNe).mpr h
  linarith

/-- **No shift iff equal lapse.** -/
theorem redshift_zero_iff {Nemit Nobs : ℝ} (hNe : 0 < Nemit) :
    redshift Nemit Nobs = 0 ↔ Nemit = Nobs := by
  unfold redshift
  rw [sub_eq_zero, div_eq_one_iff_eq hNe.ne']
  exact eq_comm

/-- **Deeper wells shift more:** for a fixed observer the redshift strictly decreases in the
emission lapse. -/
theorem redshift_strictAnti_in_emit {Nobs : ℝ} (hNo : 0 < Nobs) {Ne Ne' : ℝ} (hNe : 0 < Ne)
    (h : Ne < Ne') : redshift Ne' Nobs < redshift Ne Nobs := by
  unfold redshift
  have hlt : Nobs / Ne' < Nobs / Ne := by
    rw [div_eq_mul_one_div Nobs Ne', div_eq_mul_one_div Nobs Ne]
    exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hNe h) hNo
  linarith

/-- **Redshift factors compose** along a relay `e → m → o`. -/
theorem redshiftFactor_compose (Ne Nm No : ℝ) (hNm : Nm ≠ 0) :
    redshiftFactor Ne Nm * redshiftFactor Nm No = redshiftFactor Ne No := by
  unfold redshiftFactor
  field_simp

/-! ## Now-slice anchor -/

/-- Between two slices the shift is the ratio of their lapses (now-scales). -/
theorem nowSlice_redshift_eq (se so : NowSlice) :
    redshift se.massUnit so.massUnit = so.massUnit / se.massUnit - 1 := rfl

/-- A source seen redshifted sits on a slice with the smaller lapse. -/
theorem nowSlice_redshift_pos (se so : NowSlice) (he : 0 < se.massUnit)
    (h : se.massUnit < so.massUnit) : 0 < redshift se.massUnit so.massUnit :=
  redshift_pos he h

/-! ## Closure -/

/-- **Gravitational-redshift discharge bundle.** -/
structure RedshiftClosure : Prop where
  redshifts_climbing_out : ∀ {Ne No : ℝ}, 0 < Ne → Ne < No → 0 < redshift Ne No
  blueshifts_falling_in : ∀ {Ne No : ℝ}, 0 < No → No < Ne → redshift Ne No < 0
  zero_iff_equal : ∀ {Ne No : ℝ}, 0 < Ne → (redshift Ne No = 0 ↔ Ne = No)
  deeper_shifts_more : ∀ {No : ℝ}, 0 < No → ∀ {Ne Ne' : ℝ}, 0 < Ne → Ne < Ne' →
    redshift Ne' No < redshift Ne No
  factors_compose : ∀ (Ne Nm No : ℝ), Nm ≠ 0 →
    redshiftFactor Ne Nm * redshiftFactor Nm No = redshiftFactor Ne No

/-- **Gravitational redshift is discharged:** a lapse-ratio shift, positive climbing out and negative
falling in, deeper wells shifting more, with multiplicatively composing factors. -/
theorem gravitational_redshift_closure : RedshiftClosure where
  redshifts_climbing_out := redshift_pos
  blueshifts_falling_in := redshift_neg
  zero_iff_equal := redshift_zero_iff
  deeper_shifts_more := redshift_strictAnti_in_emit
  factors_compose := redshiftFactor_compose

end HqivSpine.Physics.GravitationalRedshift
