import HqivSpine.Physics.GRFromMaxwell

/-!
# `HqivSpine.Physics.GravitationalLensing` — light deflection off `G_eff`

The companion to `GRFromMaxwell`: a null ray grazing a mass `M` at impact parameter `b` is bent by
`δ = 4·G_eff(φ)·M / b`, where the coupling is the lattice `G_eff(φ) = φ^α` (no new constant).

* **The relativistic factor of two.** The full deflection is exactly twice the naive Newtonian
  `2GM/b` (`einstein_eq_two_newtonian`) — space curvature contributes equally to time curvature.
* **Positive, mass-linear, `1/b`.** The deflection is positive (`einsteinDeflection_pos`), strictly
  increasing in the lens mass (`einsteinDeflection_strictMono_in_M`), and strictly decreasing in the
  impact parameter (`einsteinDeflection_antitone_in_b`) — closer rays bend more.
* **Stronger curvature bends more.** Since `G_eff` is strictly monotone in `φ`, deeper now-slice
  curvature lenses harder (`einsteinDeflection_strictMono_in_phi`).

Bundled in `LensingClosure` / `gravitational_lensing_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.GravitationalLensing

open HqivSpine.Physics

/-- **Newtonian (naive) deflection** `2·G_eff(φ)·M / b`. -/
noncomputable def newtonianDeflection (φ M b : ℝ) : ℝ := 2 * gEff φ * M / b

/-- **Einstein (relativistic) deflection** `4·G_eff(φ)·M / b`. -/
noncomputable def einsteinDeflection (φ M b : ℝ) : ℝ := 4 * gEff φ * M / b

/-- **The relativistic factor of two:** GR doubles the Newtonian light bending. -/
theorem einstein_eq_two_newtonian (φ M b : ℝ) :
    einsteinDeflection φ M b = 2 * newtonianDeflection φ M b := by
  unfold einsteinDeflection newtonianDeflection; ring

theorem einsteinDeflection_pos {φ M b : ℝ} (hφ : 0 < φ) (hM : 0 < M) (hb : 0 < b) :
    0 < einsteinDeflection φ M b := by
  unfold einsteinDeflection
  have hG : 0 < gEff φ := gEff_pos hφ
  positivity

/-- **Closer rays bend more:** the deflection strictly decreases in the impact parameter. -/
theorem einsteinDeflection_antitone_in_b {φ M : ℝ} (hφ : 0 < φ) (hM : 0 < M) {b b' : ℝ}
    (hb : 0 < b) (h : b < b') : einsteinDeflection φ M b' < einsteinDeflection φ M b := by
  unfold einsteinDeflection
  have hG : 0 < gEff φ := gEff_pos hφ
  have hnum : 0 < 4 * gEff φ * M := by positivity
  have hrec : 1 / b' < 1 / b := one_div_lt_one_div_of_lt hb h
  rw [div_eq_mul_one_div (4 * gEff φ * M) b', div_eq_mul_one_div (4 * gEff φ * M) b]
  exact mul_lt_mul_of_pos_left hrec hnum

/-- **Heavier lenses bend more:** the deflection is strictly increasing in the lens mass. -/
theorem einsteinDeflection_strictMono_in_M {φ b : ℝ} (hφ : 0 < φ) (hb : 0 < b) {M M' : ℝ}
    (h : M < M') : einsteinDeflection φ M b < einsteinDeflection φ M' b := by
  unfold einsteinDeflection
  have hG : 0 < gEff φ := gEff_pos hφ
  have hc : 0 < 4 * gEff φ / b := by positivity
  rw [show 4 * gEff φ * M / b = (4 * gEff φ / b) * M from by ring,
      show 4 * gEff φ * M' / b = (4 * gEff φ / b) * M' from by ring]
  exact mul_lt_mul_of_pos_left h hc

/-- **Deeper curvature lenses harder:** the deflection is strictly increasing in `φ`
(`G_eff` is strictly monotone). -/
theorem einsteinDeflection_strictMono_in_phi {M b : ℝ} (hM : 0 < M) (hb : 0 < b) {φ φ' : ℝ}
    (hφ : 0 ≤ φ) (h : φ < φ') : einsteinDeflection φ M b < einsteinDeflection φ' M b := by
  unfold einsteinDeflection
  have hφ' : 0 ≤ φ' := le_of_lt (lt_of_le_of_lt hφ h)
  have hg : gEff φ < gEff φ' :=
    gEff_strictMonoOn (Set.mem_Ici.mpr hφ) (Set.mem_Ici.mpr hφ') h
  have hc : 0 < 4 * M / b := by positivity
  rw [show 4 * gEff φ * M / b = (4 * M / b) * gEff φ from by ring,
      show 4 * gEff φ' * M / b = (4 * M / b) * gEff φ' from by ring]
  exact mul_lt_mul_of_pos_left hg hc

/-! ## Closure -/

/-- **Gravitational-lensing discharge bundle.** -/
structure LensingClosure : Prop where
  relativistic_factor_two : ∀ (φ M b : ℝ),
    einsteinDeflection φ M b = 2 * newtonianDeflection φ M b
  positive : ∀ {φ M b : ℝ}, 0 < φ → 0 < M → 0 < b → 0 < einsteinDeflection φ M b
  mass_increasing : ∀ {φ b : ℝ}, 0 < φ → 0 < b → ∀ {M M' : ℝ}, M < M' →
    einsteinDeflection φ M b < einsteinDeflection φ M' b
  impact_decreasing : ∀ {φ M : ℝ}, 0 < φ → 0 < M → ∀ {b b' : ℝ}, 0 < b → b < b' →
    einsteinDeflection φ M b' < einsteinDeflection φ M b

/-- **Gravitational lensing is discharged:** a positive, mass-linear, `1/b` deflection that is
exactly twice the Newtonian value, with the lattice coupling `G_eff` setting the strength. -/
theorem gravitational_lensing_closure : LensingClosure where
  relativistic_factor_two := einstein_eq_two_newtonian
  positive := einsteinDeflection_pos
  mass_increasing := einsteinDeflection_strictMono_in_M
  impact_decreasing := einsteinDeflection_antitone_in_b

end HqivSpine.Physics.GravitationalLensing
