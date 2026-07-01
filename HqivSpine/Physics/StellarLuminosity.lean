import HqivSpine.Physics.ThermalArrow

/-!
# `HqivSpine.Physics.StellarLuminosity` — bounded Stefan–Boltzmann luminosity

`Blackbody` replaced the divergent continuum `σT⁴` by a finite shell sum bounded by the
Rayleigh–Jeans envelope `T·∑N_m`. This module reads that as a **luminosity** and adds the missing
monotonicity: hotter baths shine brighter, and on the shell temperature ladder the hotter inner
shells outshine the cooler outer ones.

* **Monotone in temperature.** Each Planck mode energy strictly increases with `T`
  (`planckMeanEnergy_strictMono_in_T`), so over any non-empty mode window the luminosity does too
  (`luminosity_strictMono_in_T`).
* **Finite Stefan–Boltzmann ceiling.** The luminosity is positive (`luminosity_pos`) and capped by
  `T·∑N_m` (`luminosity_ceiling`) — no UV/IR divergence, no fitted `σ`.
* **Inner shells outshine outer.** Using the shell temperature `T_m = 1/(m+1)` (hotter inward), the
  shell luminosity strictly decreases outward (`shellLuminosity_antitone_in_bath`).

Bundled in `LuminosityClosure` / `stellar_luminosity_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.StellarLuminosity

open HqivSpine.Physics HqivSpine.Physics.Thermodynamics

/-! ## Planck mode energy is monotone in temperature -/

/-- **A warmer bath fills every mode further:** the Planck mean energy strictly increases in `T`. -/
theorem planckMeanEnergy_strictMono_in_T (ω : ℝ) {T₁ T₂ : ℝ} (hω : 0 < ω) (hT₁ : 0 < T₁)
    (h : T₁ < T₂) : planckMeanEnergy ω T₁ < planckMeanEnergy ω T₂ := by
  have hT₂ : 0 < T₂ := lt_trans hT₁ h
  unfold planckMeanEnergy nBose
  have hr : ω / T₂ < ω / T₁ := by
    rw [div_eq_mul_one_div ω T₂, div_eq_mul_one_div ω T₁]
    exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hT₁ h) hω
  have he : Real.exp (ω / T₂) < Real.exp (ω / T₁) := Real.exp_lt_exp.mpr hr
  have hd1 : 0 < Real.exp (ω / T₁) - 1 := by
    have : 1 < Real.exp (ω / T₁) := Real.one_lt_exp_iff.mpr (div_pos hω hT₁)
    linarith
  have hd2 : 0 < Real.exp (ω / T₂) - 1 := by
    have : 1 < Real.exp (ω / T₂) := Real.one_lt_exp_iff.mpr (div_pos hω hT₂)
    linarith
  have hrec : 1 / (Real.exp (ω / T₁) - 1) < 1 / (Real.exp (ω / T₂) - 1) :=
    one_div_lt_one_div_of_lt hd2 (by linarith)
  exact mul_lt_mul_of_pos_left hrec hω

/-- Per-shell spectral energy strictly increases with temperature. -/
theorem shellSpectralEnergy_strictMono_in_T (m : ℕ) {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (h : T₁ < T₂) :
    shellSpectralEnergy m T₁ < shellSpectralEnergy m T₂ := by
  unfold shellSpectralEnergy
  exact mul_lt_mul_of_pos_left
    (planckMeanEnergy_strictMono_in_T (shellOmega m) (shellOmega_pos m) hT₁ h)
    (shellModeMultiplicity_pos m)

/-! ## Luminosity -/

/-- **Luminosity** of a bath at temperature `T` over the mode window `[m_UV, m_IR]`. -/
noncomputable def luminosity (T : ℝ) (m_UV m_IR : ℕ) : ℝ := blackbodyEnergyDensity T m_UV m_IR

theorem luminosity_pos (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) (h : m_UV ≤ m_IR) :
    0 < luminosity T m_UV m_IR :=
  blackbodyEnergyDensity_pos_of_le T m_UV m_IR hT h

/-- **Finite Stefan–Boltzmann ceiling:** `L ≤ T·∑N_m`. -/
theorem luminosity_ceiling (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    luminosity T m_UV m_IR ≤ T * cumulativeModeBudget m_UV m_IR :=
  stefanBoltzmann_ceiling T m_UV m_IR hT

/-- **Hotter shines brighter:** the luminosity strictly increases with temperature. -/
theorem luminosity_strictMono_in_T (m_UV m_IR : ℕ) {T₁ T₂ : ℝ} (hle : m_UV ≤ m_IR) (hT₁ : 0 < T₁)
    (h : T₁ < T₂) : luminosity T₁ m_UV m_IR < luminosity T₂ m_UV m_IR := by
  unfold luminosity blackbodyEnergyDensity
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨m_UV, Finset.mem_Icc.mpr ⟨le_rfl, hle⟩⟩
  · intro m _
    exact shellSpectralEnergy_strictMono_in_T m hT₁ h

/-! ## On the shell temperature ladder -/

/-- **Shell luminosity:** the luminosity of a bath at the shell temperature `T_m = 1/(m+1)`. -/
noncomputable def shellLuminosity (m_UV m_IR mBath : ℕ) : ℝ :=
  luminosity (shellTemp mBath) m_UV m_IR

/-- **Inner shells outshine outer ones:** the shell luminosity strictly decreases outward
(the inner shells are hotter). -/
theorem shellLuminosity_antitone_in_bath (m_UV m_IR : ℕ) (hle : m_UV ≤ m_IR) {a b : ℕ}
    (h : a < b) : shellLuminosity m_UV m_IR b < shellLuminosity m_UV m_IR a := by
  unfold shellLuminosity
  exact luminosity_strictMono_in_T m_UV m_IR hle (shellTemp_pos b) (ThermalArrow.shellTemp_strictAnti h)

/-! ## Closure -/

/-- **Stellar-luminosity discharge bundle.** -/
structure LuminosityClosure : Prop where
  positive : ∀ (T : ℝ) (m_UV m_IR : ℕ), 0 < T → m_UV ≤ m_IR → 0 < luminosity T m_UV m_IR
  ceiling : ∀ (T : ℝ) (m_UV m_IR : ℕ), 0 < T →
    luminosity T m_UV m_IR ≤ T * cumulativeModeBudget m_UV m_IR
  hotter_brighter : ∀ (m_UV m_IR : ℕ) {T₁ T₂ : ℝ}, m_UV ≤ m_IR → 0 < T₁ → T₁ < T₂ →
    luminosity T₁ m_UV m_IR < luminosity T₂ m_UV m_IR
  inner_outshines : ∀ (m_UV m_IR : ℕ), m_UV ≤ m_IR → ∀ {a b : ℕ}, a < b →
    shellLuminosity m_UV m_IR b < shellLuminosity m_UV m_IR a

/-- **Stellar luminosity is discharged:** a positive, temperature-increasing radiated power with a
finite Stefan–Boltzmann ceiling, hottest at the core. -/
theorem stellar_luminosity_closure : LuminosityClosure where
  positive := luminosity_pos
  ceiling := luminosity_ceiling
  hotter_brighter := luminosity_strictMono_in_T
  inner_outshines := shellLuminosity_antitone_in_bath

end HqivSpine.Physics.StellarLuminosity
