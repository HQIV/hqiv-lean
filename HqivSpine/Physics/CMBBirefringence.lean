import HqivSpine.Physics.Blackbody
import HqivSpine.Physics.Measurement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# `HqivSpine.Physics.CMBBirefringence` — cosmic birefringence from the shell angle

Isotropic cosmic birefringence as the **rotation of the CMB linear-polarisation plane** by the
per-shell angle `β(m) = α·log(m+1)` already derived in `Blackbody` (`α = alphaEM = 3/5`). Linear
polarisation is a spin-2 field, so the `(E, B)` mode pair rotates by `2β`:

`E' = cos(2β)·E − sin(2β)·B`,  `B' = sin(2β)·E + cos(2β)·B`.

* **Unitarity.** The rotation preserves the total polarisation power `E² + B²` (`rot_norm_sq`) —
  birefringence shuffles power between `E` and `B` without creating or destroying it. The per-shell
  `E→B` leakage from a pure-`E` source is *exactly* the `Blackbody` greybody split
  `cos²(2β) / sin²(2β)` (`observed_Emode_power_eq_greybody`, `observed_Bmode_power_eq_greybody`).
* **Parity violation.** A pure-`E` source acquires a nonzero `EB` cross-correlation
  `½·sin(4β)·E²` (`EBcorrelation_pure_E_eq_half_sin`); it vanishes **iff** `sin(4β) = 0`
  (`EBcorrelation_pure_E_eq_zero_iff`) — the standard-ΛCDM `EB = 0` is the special un-rotated case.
* **Inter-shell rotation.** The net rotation between an emission shell `m_e` and an observation
  shell `m_o` is `β(m_o) − β(m_e) = α·log((m_o+1)/(m_e+1))` (`birefringenceRotationAngle_eq`),
  nonnegative outward (`birefringenceRotationAngle_nonneg`) and zero on-shell.
* **Now-slice redshift link.** The same accumulated angle drives `Measurement`'s birefringence
  redshift `1 + z = e^{β/κ}` (`birefringence_drives_redshift`).

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.CMBBirefringence

open HqivSpine.Physics

/-! ## The spin-2 polarisation rotation -/

/-- Rotated **E-mode** amplitude under birefringence by spin-2 angle `2β`. -/
noncomputable def rotE (β E B : ℝ) : ℝ := Real.cos (2 * β) * E - Real.sin (2 * β) * B

/-- Rotated **B-mode** amplitude under birefringence by spin-2 angle `2β`. -/
noncomputable def rotB (β E B : ℝ) : ℝ := Real.sin (2 * β) * E + Real.cos (2 * β) * B

/-- **Unitarity:** birefringence preserves the total polarisation power `E² + B²`. -/
theorem rot_norm_sq (β E B : ℝ) :
    rotE β E B ^ 2 + rotB β E B ^ 2 = E ^ 2 + B ^ 2 := by
  unfold rotE rotB
  linear_combination (E ^ 2 + B ^ 2) * Real.sin_sq_add_cos_sq (2 * β)

theorem rotE_pure_E (β E : ℝ) : rotE β E 0 = Real.cos (2 * β) * E := by unfold rotE; ring

theorem rotB_pure_E (β E : ℝ) : rotB β E 0 = Real.sin (2 * β) * E := by unfold rotB; ring

/-! ## Parity-violating EB correlation -/

/-- `EB` cross-correlation produced by the rotation. -/
noncomputable def EBcorrelation (β E B : ℝ) : ℝ := rotE β E B * rotB β E B

theorem EBcorrelation_pure_E (β E : ℝ) :
    EBcorrelation β E 0 = Real.cos (2 * β) * Real.sin (2 * β) * E ^ 2 := by
  unfold EBcorrelation rotE rotB; ring

/-- The pure-`E` source's `EB` signal is `½·sin(4β)·E²` — the cosmic-birefringence parity signal. -/
theorem EBcorrelation_pure_E_eq_half_sin (β E : ℝ) :
    EBcorrelation β E 0 = (1 / 2) * Real.sin (4 * β) * E ^ 2 := by
  rw [EBcorrelation_pure_E]
  have hsin : Real.sin (4 * β) = 2 * Real.sin (2 * β) * Real.cos (2 * β) := by
    rw [show (4 : ℝ) * β = 2 * (2 * β) by ring, Real.sin_two_mul]
  rw [hsin]; ring

/-- **Parity test:** for a nonzero `E` source the birefringence `EB` correlation vanishes **iff**
`sin(4β) = 0` — i.e. only at the un-rotated angles `β ∈ (π/4)ℤ`. -/
theorem EBcorrelation_pure_E_eq_zero_iff (β E : ℝ) (hE : E ≠ 0) :
    EBcorrelation β E 0 = 0 ↔ Real.sin (4 * β) = 0 := by
  rw [EBcorrelation_pure_E_eq_half_sin]
  constructor
  · intro h
    have hE2 : (E : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hE
    have h2 : (1 / 2 : ℝ) * Real.sin (4 * β) = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hE2
    rcases mul_eq_zero.mp h2 with h' | h'
    · norm_num at h'
    · exact h'
  · intro h; rw [h]; ring

/-! ## Coupling to the `Blackbody` greybody split -/

/-- The observed **E-mode power** from a pure-`E` source emitted at shell `m` is `cos²(2β(m))·E²` —
the `Blackbody` greybody emissivity. -/
theorem observed_Emode_power_eq_greybody (m : ℕ) (E : ℝ) :
    rotE (shellBirefringenceAngle m) E 0 ^ 2 = greybodyEmissivity m * E ^ 2 := by
  rw [rotE_pure_E]; unfold greybodyEmissivity; ring

/-- The observed **B-mode power** (the `E→B` leakage) is `sin²(2β(m))·E²` — the `Blackbody`
cross-channel greybody emissivity. -/
theorem observed_Bmode_power_eq_greybody (m : ℕ) (E : ℝ) :
    rotB (shellBirefringenceAngle m) E 0 ^ 2 = greybodyEmissivityB m * E ^ 2 := by
  rw [rotB_pure_E]; unfold greybodyEmissivityB; ring

/-- Total observed polarisation power is conserved shell-by-shell: `E_obs² + B_obs² = E²`. -/
theorem observed_power_conserved (m : ℕ) (E : ℝ) :
    rotE (shellBirefringenceAngle m) E 0 ^ 2 + rotB (shellBirefringenceAngle m) E 0 ^ 2 = E ^ 2 := by
  have h := rot_norm_sq (shellBirefringenceAngle m) E 0
  simpa using h

/-! ## Inter-shell rotation angle -/

/-- Net birefringence rotation accumulated between emission shell `m_e` and observation shell `m_o`. -/
noncomputable def birefringenceRotationAngle (m_emit m_obs : ℕ) : ℝ :=
  shellBirefringenceAngle m_obs - shellBirefringenceAngle m_emit

theorem birefringenceRotationAngle_self (m : ℕ) : birefringenceRotationAngle m m = 0 := by
  unfold birefringenceRotationAngle; ring

/-- Closed form: the rotation is `α·log((m_o+1)/(m_e+1))`. -/
theorem birefringenceRotationAngle_eq (m_e m_o : ℕ) :
    birefringenceRotationAngle m_e m_o = alphaEM * Real.log (((m_o : ℝ) + 1) / ((m_e : ℝ) + 1)) := by
  unfold birefringenceRotationAngle shellBirefringenceAngle
  rw [Real.log_div (by positivity) (by positivity)]; ring

/-- `β(m) = α·log(m+1)` is monotone in the shell index (`α = 3/5 > 0`, `log` monotone). -/
theorem shellBirefringenceAngle_mono : Monotone shellBirefringenceAngle := by
  intro a b hab
  unfold shellBirefringenceAngle
  have hα : (0 : ℝ) ≤ alphaEM := by rw [alphaEM_eq]; norm_num
  have hlog : Real.log ((a : ℝ) + 1) ≤ Real.log ((b : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  exact mul_le_mul_of_nonneg_left hlog hα

/-- Birefringence accumulates **outward**: the rotation between an inner and an outer shell is
nonnegative. -/
theorem birefringenceRotationAngle_nonneg {m_e m_o : ℕ} (h : m_e ≤ m_o) :
    0 ≤ birefringenceRotationAngle m_e m_o := by
  unfold birefringenceRotationAngle
  have := shellBirefringenceAngle_mono h
  linarith

/-! ## Now-slice redshift link -/

/-- The same accumulated birefringence angle drives the `Measurement` now-slice redshift
`1 + z = e^{β/κ}`. -/
theorem birefringence_drives_redshift (m_e m_o : ℕ) (κ : ℝ) :
    1 + Measurement.birefringenceRedshiftN (birefringenceRotationAngle m_e m_o) κ
      = Real.exp (birefringenceRotationAngle m_e m_o / κ) :=
  Measurement.one_add_birefringenceRedshiftN _ _

end HqivSpine.Physics.CMBBirefringence
