import HqivSpine.Physics.TextureZeroDerivation
import HqivSpine.Physics.NeutrinoMixing

/-!
# `HqivSpine.Physics.NeutrinoSeesaw` — light-neutrino **mass** from the seesaw structure

`NeutrinoMixing` already fixed the neutrino *angle* (`θ = π/4`, maximal) and CP phase (`δ = π/5`) from
shell geometry — those are HQIV-native *numbers* out of the lock-in shell. The seesaw here is a
different kind of statement and the honest scope must be stated up front:

**Scope / what is and is not derived.** This module proves the seesaw *relations* — given the
type-I structure `[[0, m_D], [m_D, M_R]]`. It does **not** derive that a right-handed neutrino
exists, nor does it fix the scales: `m_D` and `M_R` are *free inputs* tied to nothing in HQIV. So
this does **not** produce an absolute `m_ν` number (unlike the angle/phase). Its content is twofold:
(i) the exact relational structure `m_ν = m_D²/m_heavy` with suppression, and (ii) the **unification**
showing the seesaw matrix is the *same* texture-zero canonical form derived in `TextureZeroDerivation`.
Making it HQIV-native would require deriving the right-handed mode and fixing `M_R` (e.g. a
horizon/Planck scale) and `m_D` (a ladder rung) — a frontier, not done here.

A right-handed neutrino enters with a heavy Majorana mass `M_R` and a Dirac coupling `m_D` to the
left-handed mode, which is itself a would-be-zero mode (no Majorana mass). The mass matrix is the
texture zero `[[0, m_D], [m_D, M_R]]` — exactly `TextureZeroDerivation.symMatrix 0 M_R m_D`, whose
determinant `−m_D² < 0` is a genuine seesaw (`seesaw_carriesSpectrum`).

* **Exact seesaw relation:** `m_heavy · m_ν = m_D²` (`seesaw_product`) — the product of eigenvalues is
  the off-diagonal squared, i.e. `b² = m₁m₂` from `TextureZeroDerivation` read as `m_ν = m_D²/m_heavy`
  (`lightNeutrino_eq_ratio`).
* **Suppression:** the light mass sits **below the naive Dirac/Majorana scale**,
  `m_ν < m_D²/M_R` (`seesaw_suppression`), and below the Dirac scale itself `m_ν < m_D` when
  `m_D < M_R` (`lightNeutrino_lt_dirac`); it is positive (`lightNeutrino_pos`) and vanishes as
  `M_R → ∞` (`lightNeutrino_lt_of_heavier_MR`: heavier `M_R` ⇒ lighter `ν`).
* **Unified with the texture-zero derivation:** the seesaw matrix carries the spectrum
  `{m_heavy, −m_ν}` (`seesaw_carriesSpectrum`), so it is an instance of the canonical form proved
  realizable-iff-`det≤0` in `TextureZeroDerivation`.

So the neutrino sector splits cleanly: **angle + CP phase** are HQIV-native (`NeutrinoMixing`), while
the **mass** is given here only *relationally* (`m_ν = m_D²/M_R`) — correct and PDG-free, but the
absolute scale awaits an HQIV-native `m_D`, `M_R`. No PMNS entry, no measured `m_ν` imported.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.NeutrinoSeesaw

open HqivSpine.Physics.TextureZeroDerivation

/-! ## The seesaw eigenvalues -/

/-- Discriminant `√(M_R² + 4 m_D²)` of the seesaw matrix `[[0, m_D], [m_D, M_R]]`. -/
noncomputable def seesawDisc (mD MR : ℝ) : ℝ := Real.sqrt (MR ^ 2 + 4 * mD ^ 2)

/-- Heavy (mostly-Majorana) eigenvalue. -/
noncomputable def heavyNeutrino (mD MR : ℝ) : ℝ := (MR + seesawDisc mD MR) / 2

/-- Light (physical) neutrino mass `= (√(M_R²+4m_D²) − M_R)/2 ≥ 0`. -/
noncomputable def lightNeutrino (mD MR : ℝ) : ℝ := (seesawDisc mD MR - MR) / 2

theorem seesawDisc_sq (mD MR : ℝ) : seesawDisc mD MR ^ 2 = MR ^ 2 + 4 * mD ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The discriminant exceeds `M_R` whenever the Dirac coupling is nonzero. -/
theorem MR_lt_seesawDisc (mD MR : ℝ) (hD : mD ≠ 0) (hMR : 0 < MR) : MR < seesawDisc mD MR := by
  have hmD2 : 0 < mD * mD := mul_self_pos.mpr hD
  have hsq : MR ^ 2 < seesawDisc mD MR ^ 2 := by rw [seesawDisc_sq]; nlinarith [hmD2]
  exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) hsq

/-! ## The exact seesaw relation -/

/-- **Exact seesaw relation:** `m_heavy · m_ν = m_D²` (the eigenvalue product is the off-diagonal
squared). -/
theorem seesaw_product (mD MR : ℝ) : heavyNeutrino mD MR * lightNeutrino mD MR = mD ^ 2 := by
  have hD := seesawDisc_sq mD MR
  unfold heavyNeutrino lightNeutrino
  linear_combination (1 / 4 : ℝ) * hD

theorem heavyNeutrino_pos (mD MR : ℝ) (hMR : 0 < MR) : 0 < heavyNeutrino mD MR := by
  unfold heavyNeutrino seesawDisc; positivity

theorem lightNeutrino_pos (mD MR : ℝ) (hD : mD ≠ 0) (hMR : 0 < MR) : 0 < lightNeutrino mD MR := by
  unfold lightNeutrino
  have := MR_lt_seesawDisc mD MR hD hMR
  linarith

/-- `m_ν = m_D² / m_heavy`. -/
theorem lightNeutrino_eq_ratio (mD MR : ℝ) (hMR : 0 < MR) :
    lightNeutrino mD MR = mD ^ 2 / heavyNeutrino mD MR := by
  rw [eq_div_iff (heavyNeutrino_pos mD MR hMR).ne', mul_comm]
  exact seesaw_product mD MR

/-! ## Suppression -/

/-- **Seesaw suppression:** the light mass is below the naive ratio, `m_ν < m_D²/M_R`. -/
theorem seesaw_suppression (mD MR : ℝ) (hD : mD ≠ 0) (hMR : 0 < MR) :
    lightNeutrino mD MR < mD ^ 2 / MR := by
  rw [lightNeutrino_eq_ratio mD MR hMR]
  have hMRlt : MR < heavyNeutrino mD MR := by
    unfold heavyNeutrino
    have := MR_lt_seesawDisc mD MR hD hMR; linarith
  have hmD2 : 0 < mD ^ 2 := by have h := mul_self_pos.mpr hD; nlinarith [h]
  rw [div_eq_mul_one_div (mD ^ 2) (heavyNeutrino mD MR), div_eq_mul_one_div (mD ^ 2) MR]
  exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hMR hMRlt) hmD2

/-- The light mass is below the **Dirac** scale when `m_D < M_R`. -/
theorem lightNeutrino_lt_dirac (mD MR : ℝ) (hD : 0 < mD) (h : mD < MR) :
    lightNeutrino mD MR < mD := by
  have hsupp := seesaw_suppression mD MR hD.ne' (lt_trans hD h)
  have : mD ^ 2 / MR < mD := by
    rw [div_lt_iff₀ (lt_trans hD h)]; nlinarith
  linarith

/-- **Heavier `M_R` ⇒ lighter neutrino** (`m_ν → 0` as `M_R → ∞`), at fixed Dirac coupling. -/
theorem lightNeutrino_lt_of_heavier_MR (mD : ℝ) {MR MR' : ℝ} (hD : mD ≠ 0) (hMR : 0 < MR)
    (h : MR < MR') : lightNeutrino mD MR' < lightNeutrino mD MR := by
  rw [lightNeutrino_eq_ratio mD MR hMR, lightNeutrino_eq_ratio mD MR' (lt_trans hMR h)]
  have hmD2 : 0 < mD ^ 2 := by have hh := mul_self_pos.mpr hD; nlinarith [hh]
  have hh : heavyNeutrino mD MR < heavyNeutrino mD MR' := by
    unfold heavyNeutrino seesawDisc
    have hlt : MR ^ 2 + 4 * mD ^ 2 < MR' ^ 2 + 4 * mD ^ 2 := by nlinarith
    have hs := Real.sqrt_lt_sqrt (by positivity) hlt
    linarith
  rw [div_eq_mul_one_div (mD ^ 2) (heavyNeutrino mD MR'),
    div_eq_mul_one_div (mD ^ 2) (heavyNeutrino mD MR)]
  exact mul_lt_mul_of_pos_left
    (one_div_lt_one_div_of_lt (heavyNeutrino_pos mD MR hMR) hh) hmD2

/-! ## Unification with the texture-zero derivation -/

/-- **The seesaw matrix is an instance of the texture-zero canonical form:** `[[0, m_D], [m_D, M_R]]`
carries the spectrum `{m_heavy, −m_ν}` (`det = −m_D² < 0`, a genuine seesaw). -/
theorem seesaw_carriesSpectrum (mD MR : ℝ) :
    carriesSpectrum (symMatrix 0 MR mD) (lightNeutrino mD MR) (heavyNeutrino mD MR) := by
  constructor
  · rw [symMatrix_trace]
    unfold heavyNeutrino lightNeutrino; ring
  · rw [symMatrix_det]
    linear_combination seesaw_product mD MR

/-! ## Closure -/

/-- **Neutrino seesaw bundle:** exact relation, suppression, and unification with the texture-zero
canonical form. -/
structure NeutrinoSeesawClosure : Prop where
  exact_relation : ∀ (mD MR : ℝ), heavyNeutrino mD MR * lightNeutrino mD MR = mD ^ 2
  suppression : ∀ (mD MR : ℝ), mD ≠ 0 → 0 < MR → lightNeutrino mD MR < mD ^ 2 / MR
  decreasing_in_MR : ∀ (mD : ℝ) {MR MR' : ℝ}, mD ≠ 0 → 0 < MR → MR < MR' →
    lightNeutrino mD MR' < lightNeutrino mD MR
  is_texture_zero : ∀ (mD MR : ℝ),
    carriesSpectrum (symMatrix 0 MR mD) (lightNeutrino mD MR) (heavyNeutrino mD MR)

/-- **The neutrino mass scale is seesaw-resolved:** `m_heavy·m_ν = m_D²`, suppressed as `M_R` grows,
and the matrix is the texture-zero canonical form — the same structure as the quark sector, read for
neutrinos. Mixing angle and CP phase come separately from `NeutrinoMixing`. -/
theorem neutrino_seesaw_closure : NeutrinoSeesawClosure where
  exact_relation := seesaw_product
  suppression := seesaw_suppression
  decreasing_in_MR := lightNeutrino_lt_of_heavier_MR
  is_texture_zero := seesaw_carriesSpectrum

end HqivSpine.Physics.NeutrinoSeesaw
