import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.HorizonBlackbodySpectrum
import Hqiv.Physics.CMBBirefringenceFirstPrinciples

/-!
# HQIV Horizon-Lattice Blackbody Ladder

Standard textbook ladder adjacent to the Planck spectrum
(`HorizonBlackbodySpectrum`), built from the same HQIV null-lattice mode budget
and the curvature imprint exponent `α = 3/5`.

* **§1 Birefringence-resolved emission.** Per-shell polarization phase
  driven by the HQIV curvature imprint via `CMBBirefringenceFirstPrinciples`.
  Each shell `m` carries the anchor phase `β(m) = α · log(m+1)`, while a
  line-of-sight CMB observation reads the **relative** shell traversal
  `Δβ = α · log((m_obs+1)/(m_emit+1))`.  The spectrum splits into `E`-mode
  and `B`-mode channels that sum back to the unpolarized total.

* **§2 Asymptotic limits.** Universal Rayleigh–Jeans upper bound
  `planckMeanEnergy ω T < T` (any `ω, T > 0`) and a Wien-tail bound for
  `ω ≥ T`.  No `ω/T → 0` or `ω/T → ∞` continuum limits are taken; both bounds
  are clean inequalities.

* **§3 Thermodynamic readouts.** Photon number density, radiation pressure
  `P = U/3`, entropy density `s = (4/3) U / T` — all on the truncated shell
  sum with explicit IR/UV cutoffs.

* **§4 Kirchhoff equilibrium.** Detailed-balance bundle: emission rate equals
  absorption rate at each shell.  Stated as a `structure` carrying the rates,
  with the textbook *emissivity = absorptivity* identity as a one-line theorem.

* **§5 Debye phonon alias.** The same blackbody object with the IR cutoff
  reinterpreted as the Debye shell.

Every quantity here is a finite shell sum; no `sorry`; no new axioms.
-/

namespace Hqiv.Physics

open scoped BigOperators
open Hqiv

noncomputable section

/-! ## §1 Birefringence-resolved emission -/

/-- **Per-shell birefringence angle** (radians): `β(m) := α · log(m + 1)`.

Same construction as `betaRad_HQIV_imprint` but evaluated at an arbitrary shell.
`β(0) = 0` (Planck pole — no rotation); `β(referenceM) = betaRad_HQIV_imprint`. -/
noncomputable def shellBirefringenceAngle (m : ℕ) : ℝ :=
  Hqiv.alpha * Real.log ((m + 1 : ℝ))

theorem shellBirefringenceAngle_zero :
    shellBirefringenceAngle 0 = 0 := by
  simp [shellBirefringenceAngle, Real.log_one]

theorem shellBirefringenceAngle_nonneg (m : ℕ) :
    0 ≤ shellBirefringenceAngle m := by
  unfold shellBirefringenceAngle
  apply mul_nonneg
  · rw [Hqiv.alpha_eq_3_5]; norm_num
  · apply Real.log_nonneg
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    linarith

theorem shellBirefringenceAngle_referenceM :
    shellBirefringenceAngle Hqiv.referenceM = betaRad_HQIV_imprint :=
  rfl

/-- Relative shell traversal between emission shell `m_emit` and observer shell
`m_obs`, in the cumulative sense used by the CMB birefringence readout. -/
noncomputable def shellTraversalRatio (m_emit m_obs : ℕ) : ℝ :=
  (m_obs + 1 : ℝ) / (m_emit + 1 : ℝ)

theorem shellTraversalRatio_pos (m_emit m_obs : ℕ) :
    0 < shellTraversalRatio m_emit m_obs := by
  unfold shellTraversalRatio
  positivity

/-- Cumulative birefringence shift between emission shell `m_emit` and
observer shell `m_obs`: `Δβ = α · log((m_obs+1)/(m_emit+1))`.

This is the observable CMB birefringence convention.  In contrast,
`betaRad_HQIV_imprint = α · log(referenceM+1)` is the proton-anchor shell
imprint obtained by comparing `referenceM` to the Planck pole, not by inserting
the proton lock-in shell as the CMB emission/observation pair. -/
noncomputable def cumulativeBirefringenceShift (m_emit m_obs : ℕ) : ℝ :=
  Hqiv.alpha * Real.log (shellTraversalRatio m_emit m_obs)

theorem cumulativeBirefringenceShift_self (m : ℕ) :
    cumulativeBirefringenceShift m m = 0 := by
  unfold cumulativeBirefringenceShift shellTraversalRatio
  have h : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp [h, Real.log_one]
  simp [Real.log_one]

theorem cumulativeBirefringenceShift_from_planckPole (m : ℕ) :
    cumulativeBirefringenceShift 0 m = shellBirefringenceAngle m := by
  unfold cumulativeBirefringenceShift shellTraversalRatio shellBirefringenceAngle
  norm_num

theorem cumulativeBirefringenceShift_referenceM_from_planckPole :
    cumulativeBirefringenceShift 0 Hqiv.referenceM = betaRad_HQIV_imprint := by
  rw [cumulativeBirefringenceShift_from_planckPole, shellBirefringenceAngle_referenceM]

/-- Observational inverse: a measured rotation `β` corresponds to the relative
shell ratio `exp(β/α)`.  For a small CMB angle this ratio is close to `1`, which
is a statement about the emission/observation shell pair, not a failure of the
proton-anchor imprint. -/
noncomputable def shellRatioFromObservedBirefringence (betaRad : ℝ) : ℝ :=
  Real.exp (betaRad / Hqiv.alpha)

theorem shellRatioFromObservedBirefringence_pos (betaRad : ℝ) :
    0 < shellRatioFromObservedBirefringence betaRad := by
  unfold shellRatioFromObservedBirefringence
  positivity

theorem alpha_log_shellRatioFromObservedBirefringence (betaRad : ℝ) :
    Hqiv.alpha * Real.log (shellRatioFromObservedBirefringence betaRad) = betaRad := by
  unfold shellRatioFromObservedBirefringence
  rw [Real.log_exp]
  have hα : Hqiv.alpha ≠ 0 := by
    rw [Hqiv.alpha_eq_3_5]
    norm_num
  field_simp [hα]

/-- **E-mode fraction** of emitted intensity at shell `m`: `cos²(2β(m))`.
Comes from the `2β` polarization rotation that distinguishes parity-even
(E-mode) from parity-odd (B-mode) channels on the sky. -/
noncomputable def emissionEModeFraction (m : ℕ) : ℝ :=
  (Real.cos (2 * shellBirefringenceAngle m)) ^ 2

/-- **B-mode fraction** of emitted intensity at shell `m`: `sin²(2β(m))`. -/
noncomputable def emissionBModeFraction (m : ℕ) : ℝ :=
  (Real.sin (2 * shellBirefringenceAngle m)) ^ 2

/-- **Polarization completeness:** `cos²(2β) + sin²(2β) = 1`. -/
theorem emissionEMode_plus_BMode (m : ℕ) :
    emissionEModeFraction m + emissionBModeFraction m = 1 := by
  unfold emissionEModeFraction emissionBModeFraction
  have h := Real.sin_sq_add_cos_sq (2 * shellBirefringenceAngle m)
  linarith

theorem emissionEModeFraction_nonneg (m : ℕ) :
    0 ≤ emissionEModeFraction m := sq_nonneg _

theorem emissionBModeFraction_nonneg (m : ℕ) :
    0 ≤ emissionBModeFraction m := sq_nonneg _

theorem emissionEModeFraction_le_one (m : ℕ) :
    emissionEModeFraction m ≤ 1 := by
  have h := emissionEMode_plus_BMode m
  have hB := emissionBModeFraction_nonneg m
  linarith

theorem emissionBModeFraction_le_one (m : ℕ) :
    emissionBModeFraction m ≤ 1 := by
  have h := emissionEMode_plus_BMode m
  have hE := emissionEModeFraction_nonneg m
  linarith

/-- **B/E asymmetry** at shell `m` (sky observable). -/
noncomputable def emissionPolarizationAsymmetry (m : ℕ) : ℝ :=
  emissionBModeFraction m - emissionEModeFraction m

theorem emissionPolarizationAsymmetry_zero_at_planckPole :
    emissionPolarizationAsymmetry 0 = -1 := by
  unfold emissionPolarizationAsymmetry emissionBModeFraction emissionEModeFraction
  rw [shellBirefringenceAngle_zero]
  simp [Real.sin_zero, Real.cos_zero]

/-- Per-shell **E-mode** spectral energy. -/
noncomputable def shellSpectralEnergyEMode (m : ℕ) (T : ℝ) : ℝ :=
  shellSpectralEnergy m T * emissionEModeFraction m

/-- Per-shell **B-mode** spectral energy. -/
noncomputable def shellSpectralEnergyBMode (m : ℕ) (T : ℝ) : ℝ :=
  shellSpectralEnergy m T * emissionBModeFraction m

/-- **Total = E-mode + B-mode** at each shell (birefringence is unitary on
polarization channels). -/
theorem shellSpectral_E_plus_B (m : ℕ) (T : ℝ) :
    shellSpectralEnergyEMode m T + shellSpectralEnergyBMode m T =
      shellSpectralEnergy m T := by
  unfold shellSpectralEnergyEMode shellSpectralEnergyBMode
  rw [← mul_add, emissionEMode_plus_BMode]
  ring

theorem shellSpectralEnergyEMode_nonneg (m : ℕ) (T : ℝ) (hT : 0 < T) :
    0 ≤ shellSpectralEnergyEMode m T :=
  mul_nonneg (shellSpectralEnergy_nonneg m T hT) (emissionEModeFraction_nonneg m)

theorem shellSpectralEnergyBMode_nonneg (m : ℕ) (T : ℝ) (hT : 0 < T) :
    0 ≤ shellSpectralEnergyBMode m T :=
  mul_nonneg (shellSpectralEnergy_nonneg m T hT) (emissionBModeFraction_nonneg m)

/-- Truncated **E-mode** blackbody energy density. -/
noncomputable def blackbodyEnergyDensityEMode (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellSpectralEnergyEMode m T

/-- Truncated **B-mode** blackbody energy density. -/
noncomputable def blackbodyEnergyDensityBMode (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellSpectralEnergyBMode m T

/-- **Birefringence preserves total energy density:** `U_E + U_B = U`. -/
theorem blackbodyEnergyDensity_E_plus_B (T : ℝ) (m_UV m_IR : ℕ) :
    blackbodyEnergyDensityEMode T m_UV m_IR +
        blackbodyEnergyDensityBMode T m_UV m_IR =
      blackbodyEnergyDensity T m_UV m_IR := by
  unfold blackbodyEnergyDensityEMode blackbodyEnergyDensityBMode blackbodyEnergyDensity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  exact shellSpectral_E_plus_B m T

theorem blackbodyEnergyDensityEMode_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ blackbodyEnergyDensityEMode T m_UV m_IR := by
  unfold blackbodyEnergyDensityEMode
  refine Finset.sum_nonneg (fun m _ => ?_)
  exact shellSpectralEnergyEMode_nonneg m T hT

theorem blackbodyEnergyDensityBMode_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ blackbodyEnergyDensityBMode T m_UV m_IR := by
  unfold blackbodyEnergyDensityBMode
  refine Finset.sum_nonneg (fun m _ => ?_)
  exact shellSpectralEnergyBMode_nonneg m T hT

/-! ## §2 Asymptotic limits: Rayleigh–Jeans and Wien -/

/-- **Universal Rayleigh–Jeans upper bound:** the mean thermal energy per mode
is strictly less than the temperature, for every `ω, T > 0`.

Follows from `Real.add_one_lt_exp`: `x + 1 < exp(x)` for `x ≠ 0`, hence
`exp(x) − 1 > x`, hence `1/(exp(x) − 1) < 1/x`, hence `ω · n_B(ω, T) < T`. -/
theorem planckMeanEnergy_lt_T (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) :
    planckMeanEnergy ω T < T := by
  unfold planckMeanEnergy nBose
  have hpos : 0 < ω / T := div_pos hω hT
  have hne : ω / T ≠ 0 := ne_of_gt hpos
  have hexp : ω / T + 1 < Real.exp (ω / T) := Real.add_one_lt_exp hne
  have hsub : ω / T < Real.exp (ω / T) - 1 := by linarith
  have hsub_pos : 0 < Real.exp (ω / T) - 1 := lt_trans hpos hsub
  rw [show ω * (1 / (Real.exp (ω / T) - 1)) =
        ω / (Real.exp (ω / T) - 1) from by ring]
  rw [div_lt_iff₀ hsub_pos]
  have hkey : T * (ω / T) < T * (Real.exp (ω / T) - 1) :=
    mul_lt_mul_of_pos_left hsub hT
  have hcancel : T * (ω / T) = ω := by field_simp
  linarith

/-- **Per-shell Rayleigh–Jeans bound:** `u_m(T) < N_m · T`. -/
theorem shellSpectralEnergy_lt_RJ (m : ℕ) (T : ℝ) (hT : 0 < T) :
    shellSpectralEnergy m T < shellModeMultiplicity m * T := by
  unfold shellSpectralEnergy
  have h := planckMeanEnergy_lt_T (shellOmega m) T (shellOmega_pos m) hT
  exact mul_lt_mul_of_pos_left h (shellModeMultiplicity_pos m)

/-- **Wien-tail bound for `ω ≥ T`:** the Bose occupation is bounded by the
fixed constant `1 / (e − 1)`.  At `ω = T` this gives `n_B ≤ 1/(e−1) ≈ 0.582`;
for larger `ω/T` the bound is conservative but uniform. -/
theorem nBose_le_wien_constant (ω T : ℝ) (_hω : 0 < ω) (hT : 0 < T) (h : T ≤ ω) :
    nBose ω T ≤ 1 / (Real.exp 1 - 1) := by
  unfold nBose
  have hge : 1 ≤ ω / T := (one_le_div hT).mpr h
  have hexp_one_lt : (1 : ℝ) < Real.exp 1 :=
    Real.one_lt_exp_iff.mpr (by norm_num)
  have hexp_pos : 0 < Real.exp 1 - 1 := by linarith
  have hexp_mono : Real.exp 1 ≤ Real.exp (ω / T) :=
    Real.exp_le_exp.mpr hge
  have hsub_le : Real.exp 1 - 1 ≤ Real.exp (ω / T) - 1 := by linarith
  exact one_div_le_one_div_of_le hexp_pos hsub_le

/-- **Per-shell Wien-tail bound:** for shells with `ω_m ≥ T` (i.e. small `m`),
the spectral energy is bounded by a fixed geometric multiple of `ω_m · N_m`. -/
theorem shellSpectralEnergy_le_wien (m : ℕ) (T : ℝ) (hT : 0 < T)
    (h : T ≤ shellOmega m) :
    shellSpectralEnergy m T ≤
      shellModeMultiplicity m * shellOmega m / (Real.exp 1 - 1) := by
  unfold shellSpectralEnergy planckMeanEnergy
  have hbose := nBose_le_wien_constant (shellOmega m) T (shellOmega_pos m) hT h
  have hNm : 0 ≤ shellModeMultiplicity m := shellModeMultiplicity_nonneg m
  have hω : 0 ≤ shellOmega m := le_of_lt (shellOmega_pos m)
  have hexp_pos : 0 < Real.exp 1 - 1 := by
    have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  calc shellModeMultiplicity m * (shellOmega m * nBose (shellOmega m) T)
      ≤ shellModeMultiplicity m * (shellOmega m * (1 / (Real.exp 1 - 1))) := by
        apply mul_le_mul_of_nonneg_left _ hNm
        exact mul_le_mul_of_nonneg_left hbose hω
    _ = shellModeMultiplicity m * shellOmega m / (Real.exp 1 - 1) := by ring

/-! ## §3 Thermodynamic readouts -/

/-- **Photon number density** between cutoffs: `∑ N_m · n_B(ω_m, T)`.
Same shell sum as the spectrum but without the `ω_m` factor. -/
noncomputable def photonNumberDensity (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR,
    shellModeMultiplicity m * nBose (shellOmega m) T

theorem photonNumberDensity_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ photonNumberDensity T m_UV m_IR := by
  unfold photonNumberDensity
  refine Finset.sum_nonneg (fun m _ => ?_)
  exact mul_nonneg (shellModeMultiplicity_nonneg m)
    (nBose_nonneg (shellOmega m) T (shellOmega_pos m) hT)

theorem photonNumberDensity_pos (T : ℝ) (m_UV m_IR : ℕ)
    (hT : 0 < T) (h : m_UV ≤ m_IR) :
    0 < photonNumberDensity T m_UV m_IR := by
  unfold photonNumberDensity
  have hne : (Finset.Icc m_UV m_IR).Nonempty :=
    ⟨m_UV, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
  refine Finset.sum_pos (fun k _ => ?_) hne
  exact mul_pos (shellModeMultiplicity_pos k)
    (nBose_pos (shellOmega k) T (shellOmega_pos k) hT)

/-- **Radiation pressure** for a massless photon gas: `P = U / 3`. -/
noncomputable def radiationPressure (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  blackbodyEnergyDensity T m_UV m_IR / 3

theorem radiationPressure_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ radiationPressure T m_UV m_IR := by
  unfold radiationPressure
  exact div_nonneg
    (blackbodyEnergyDensity_nonneg T m_UV m_IR hT) (by norm_num)

/-- Photon-gas identity: `U = 3 P`. -/
theorem energyDensity_eq_three_pressure (T : ℝ) (m_UV m_IR : ℕ) :
    blackbodyEnergyDensity T m_UV m_IR = 3 * radiationPressure T m_UV m_IR := by
  unfold radiationPressure
  ring

/-- **Entropy density** of the photon gas: `s = (4/3) · U / T`.
Standard photon-gas thermodynamic identity at fixed cutoffs. -/
noncomputable def entropyDensity (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  (4 / 3 : ℝ) * blackbodyEnergyDensity T m_UV m_IR / T

theorem entropyDensity_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ entropyDensity T m_UV m_IR := by
  unfold entropyDensity
  have hU : 0 ≤ blackbodyEnergyDensity T m_UV m_IR :=
    blackbodyEnergyDensity_nonneg T m_UV m_IR hT
  have hcoef : 0 ≤ (4 : ℝ) / 3 := by norm_num
  exact div_nonneg (mul_nonneg hcoef hU) (le_of_lt hT)

/-- Photon-gas Euler identity: `T · s = (4/3) · U`. -/
theorem T_times_entropy_eq (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    T * entropyDensity T m_UV m_IR =
      (4 / 3 : ℝ) * blackbodyEnergyDensity T m_UV m_IR := by
  unfold entropyDensity
  have hT_ne : T ≠ 0 := ne_of_gt hT
  field_simp

/-! ## §4 Kirchhoff equilibrium (detailed balance) -/

/-- **Equilibrium bundle:** per-shell emission and absorption rates that
coincide on every accessible shell.

Honesty: this is a `structure` carrying the two rate functions and the
coincidence proof.  We do **not** derive cross-sections microscopically; the
geometric content of the predicate is provided by `gamma_HQIV` (no net
horizon-correlation flux at steady state, `Hqiv.gamma_eq_2_5`). -/
structure KirchhoffEquilibrium (T : ℝ) (m_UV m_IR : ℕ) where
  /-- Emission rate per shell. -/
  emission : ℕ → ℝ
  /-- Absorption rate per shell. -/
  absorption : ℕ → ℝ
  /-- Detailed balance on the accessible window. -/
  emission_eq_absorption :
    ∀ m, m_UV ≤ m → m ≤ m_IR → emission m = absorption m

/-- **Kirchhoff's law:** at equilibrium, emissivity equals absorptivity at
every accessible shell, where both are measured against the same saturated
reference (here: the shell spectral energy = perfect-absorber baseline at
that shell). -/
theorem kirchhoff_emissivity_eq_absorptivity
    (T : ℝ) (m_UV m_IR : ℕ)
    (h : KirchhoffEquilibrium T m_UV m_IR) (m : ℕ)
    (hl : m_UV ≤ m) (hr : m ≤ m_IR) :
    h.emission m / shellSpectralEnergy m T =
      h.absorption m / shellSpectralEnergy m T := by
  rw [h.emission_eq_absorption m hl hr]

/-- Canonical equilibrium: emission and absorption both equal the shell
spectral energy `u_m(T)`.  Witnesses that the predicate is satisfiable
(detailed balance with the Planck spectrum as the reference). -/
noncomputable def planckSpectrumEquilibrium (T : ℝ) (m_UV m_IR : ℕ) :
    KirchhoffEquilibrium T m_UV m_IR :=
  { emission := fun m => shellSpectralEnergy m T
  , absorption := fun m => shellSpectralEnergy m T
  , emission_eq_absorption := by intros; rfl }

/-! ## §5 Debye phonon alias -/

/-- **Debye phonon energy density** is the same blackbody sum with the IR
cutoff reinterpreted: `m_Debye` set by the lattice spacing instead of the
cosmological horizon.  This is just a rename — the truncated mode list is
identical, and `P = U/3`, `s = (4/3) U/T` carry over verbatim. -/
noncomputable def debyeEnergyDensity (T : ℝ) (m_Debye : ℕ) : ℝ :=
  blackbodyEnergyDensity T 0 m_Debye

theorem debyeEnergyDensity_eq_blackbody (T : ℝ) (m_Debye : ℕ) :
    debyeEnergyDensity T m_Debye =
      blackbodyEnergyDensity T planckUVCutoff m_Debye := rfl

theorem debyeEnergyDensity_nonneg (T : ℝ) (m_Debye : ℕ) (hT : 0 < T) :
    0 ≤ debyeEnergyDensity T m_Debye :=
  blackbodyEnergyDensity_nonneg T 0 m_Debye hT

/-- Debye pressure: same `P = U/3`. -/
noncomputable def debyePressure (T : ℝ) (m_Debye : ℕ) : ℝ :=
  debyeEnergyDensity T m_Debye / 3

theorem debyePressure_eq_radiationPressure (T : ℝ) (m_Debye : ℕ) :
    debyePressure T m_Debye = radiationPressure T 0 m_Debye := rfl

/-- Debye entropy density: same `s = (4/3) U/T`. -/
noncomputable def debyeEntropyDensity (T : ℝ) (m_Debye : ℕ) : ℝ :=
  (4 / 3 : ℝ) * debyeEnergyDensity T m_Debye / T

theorem debyeEntropyDensity_eq_entropyDensity (T : ℝ) (m_Debye : ℕ) :
    debyeEntropyDensity T m_Debye = entropyDensity T 0 m_Debye := rfl

end

end Hqiv.Physics
