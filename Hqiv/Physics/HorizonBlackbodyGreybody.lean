import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.HorizonBlackbodySpectrum
import Hqiv.Physics.HorizonBlackbodyLadder
import Hqiv.Physics.HorizonBlackbodyStefan

/-!
# HQIV polarized greybody coefficients

Reinterpret the HQIV per-shell birefringence E/B fractions
`emissionEModeFraction m = cos²(2β(m))` and
`emissionBModeFraction m = sin²(2β(m))` from
`HorizonBlackbodyLadder` as **per-shell greybody emissivities**.

Standard greybody: `U_grey(T) = ε · σ · T⁴` with constant `ε ∈ [0, 1]`.
HQIV greybody: per-shell emissivity `ε(m) = cos²(2β(m))` derived from
the cumulative HQIV birefringence angle `β(m) = α · log(m+1)` — no
empirical greybody parameter.

We define
* `greybodyEmissivity m := emissionEModeFraction m` (E-mode = co-polarized)
* `greybodyEmissivityB m := emissionBModeFraction m` (B-mode = cross-polarized)
* `cumulativeGreybodyEmissivity m_UV m_IR := Σ N_m · ε(m)`
* `cumulativeGreybodyEmissivityB m_UV m_IR := Σ N_m · ε_B(m)`

and prove

* **Greybody completeness:** `ε(m) + ε_B(m) = 1` and the cumulative
  `cumulativeGreybodyEmissivity + cumulativeGreybodyEmissivityB =
   cumulativeShellModeMultiplicity`.
* **Stefan-Boltzmann E-mode upper bound:**
  `U_E(T) ≤ T · cumulativeGreybodyEmissivity m_UV m_IR`.
* **Stefan-Boltzmann B-mode upper bound:**
  `U_B(T) ≤ T · cumulativeGreybodyEmissivityB m_UV m_IR`.
* **Polarized Kirchhoff law (per shell):** at equilibrium, polarized
  emissivity equals polarized absorptivity in each channel separately.
* **Numerical witness at the lock-in window:** the cumulative greybody
  emissivity at `[0, referenceM]` is bounded by `120` (the integer mode
  budget at `referenceM = 4`).

Zero `sorry`; no new axioms.
-/

namespace Hqiv.Physics

open scoped BigOperators
open Hqiv

noncomputable section

/-! ## Per-shell greybody emissivity aliases -/

/-- **HQIV greybody emissivity** at shell `m`: the E-mode fraction
`cos²(2β(m))`. Plays the role of the empirical greybody coefficient `ε`,
but is fully derived from HQIV birefringence. -/
noncomputable def greybodyEmissivity (m : ℕ) : ℝ := emissionEModeFraction m

/-- **HQIV greybody cross-channel coefficient** at shell `m`: the B-mode
fraction `sin²(2β(m))`. -/
noncomputable def greybodyEmissivityB (m : ℕ) : ℝ := emissionBModeFraction m

theorem greybodyEmissivity_nonneg (m : ℕ) :
    0 ≤ greybodyEmissivity m :=
  emissionEModeFraction_nonneg m

theorem greybodyEmissivity_le_one (m : ℕ) :
    greybodyEmissivity m ≤ 1 :=
  emissionEModeFraction_le_one m

theorem greybodyEmissivityB_nonneg (m : ℕ) :
    0 ≤ greybodyEmissivityB m :=
  emissionBModeFraction_nonneg m

theorem greybodyEmissivityB_le_one (m : ℕ) :
    greybodyEmissivityB m ≤ 1 :=
  emissionBModeFraction_le_one m

/-- **Greybody completeness:** `ε(m) + ε_B(m) = 1`. -/
theorem greybodyEmissivity_complement (m : ℕ) :
    greybodyEmissivity m + greybodyEmissivityB m = 1 := by
  unfold greybodyEmissivity greybodyEmissivityB
  exact emissionEMode_plus_BMode m

/-- At the Planck-pole shell `m = 0`, the birefringence angle is zero, so
the channel is **purely E-mode**: `ε(0) = 1`. -/
theorem greybodyEmissivity_zero : greybodyEmissivity 0 = 1 := by
  unfold greybodyEmissivity emissionEModeFraction
  rw [shellBirefringenceAngle_zero]
  simp

/-- At the Planck-pole shell, the B-mode coefficient is zero. -/
theorem greybodyEmissivityB_zero : greybodyEmissivityB 0 = 0 := by
  unfold greybodyEmissivityB emissionBModeFraction
  rw [shellBirefringenceAngle_zero]
  simp

/-! ## Cumulative greybody emissivity -/

/-- Cumulative mode-weighted greybody emissivity on the window. -/
noncomputable def cumulativeGreybodyEmissivity (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR,
    shellModeMultiplicity m * greybodyEmissivity m

/-- Cumulative mode-weighted greybody cross-channel coefficient. -/
noncomputable def cumulativeGreybodyEmissivityB (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR,
    shellModeMultiplicity m * greybodyEmissivityB m

theorem cumulativeGreybodyEmissivity_nonneg (m_UV m_IR : ℕ) :
    0 ≤ cumulativeGreybodyEmissivity m_UV m_IR :=
  Finset.sum_nonneg (fun m _ =>
    mul_nonneg (shellModeMultiplicity_nonneg m) (greybodyEmissivity_nonneg m))

theorem cumulativeGreybodyEmissivityB_nonneg (m_UV m_IR : ℕ) :
    0 ≤ cumulativeGreybodyEmissivityB m_UV m_IR :=
  Finset.sum_nonneg (fun m _ =>
    mul_nonneg (shellModeMultiplicity_nonneg m) (greybodyEmissivityB_nonneg m))

/-- **Cumulative greybody completeness:**
`Σ N_m ε(m) + Σ N_m ε_B(m) = Σ N_m`. -/
theorem cumulativeGreybodyEmissivity_complement (m_UV m_IR : ℕ) :
    cumulativeGreybodyEmissivity m_UV m_IR +
        cumulativeGreybodyEmissivityB m_UV m_IR =
      cumulativeShellModeMultiplicity m_UV m_IR := by
  unfold cumulativeGreybodyEmissivity cumulativeGreybodyEmissivityB
    cumulativeShellModeMultiplicity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  have h := greybodyEmissivity_complement m
  calc shellModeMultiplicity m * greybodyEmissivity m +
          shellModeMultiplicity m * greybodyEmissivityB m
      = shellModeMultiplicity m *
          (greybodyEmissivity m + greybodyEmissivityB m) := by ring
    _ = shellModeMultiplicity m * 1 := by rw [h]
    _ = shellModeMultiplicity m := by ring

/-- The cumulative E-mode greybody emissivity is bounded by the cumulative
mode budget. -/
theorem cumulativeGreybodyEmissivity_le_cumulative (m_UV m_IR : ℕ) :
    cumulativeGreybodyEmissivity m_UV m_IR ≤
      cumulativeShellModeMultiplicity m_UV m_IR := by
  have h := cumulativeGreybodyEmissivity_complement m_UV m_IR
  have hB := cumulativeGreybodyEmissivityB_nonneg m_UV m_IR
  linarith

theorem cumulativeGreybodyEmissivityB_le_cumulative (m_UV m_IR : ℕ) :
    cumulativeGreybodyEmissivityB m_UV m_IR ≤
      cumulativeShellModeMultiplicity m_UV m_IR := by
  have h := cumulativeGreybodyEmissivity_complement m_UV m_IR
  have hE := cumulativeGreybodyEmissivity_nonneg m_UV m_IR
  linarith

/-! ## Per-shell Stefan-Boltzmann bounds (greybody form) -/

/-- **Per-shell E-mode greybody bound:** `u_E(m, T) ≤ N_m · T · ε(m)`. -/
theorem shellSpectralEnergyEMode_le_greybodyRJ (m : ℕ) (T : ℝ) (hT : 0 < T) :
    shellSpectralEnergyEMode m T ≤
      shellModeMultiplicity m * T * greybodyEmissivity m := by
  unfold shellSpectralEnergyEMode greybodyEmissivity
  have hRJ : shellSpectralEnergy m T < shellModeMultiplicity m * T :=
    shellSpectralEnergy_lt_RJ m T hT
  have hε := emissionEModeFraction_nonneg m
  exact mul_le_mul_of_nonneg_right (le_of_lt hRJ) hε

/-- **Per-shell B-mode greybody bound:** `u_B(m, T) ≤ N_m · T · ε_B(m)`. -/
theorem shellSpectralEnergyBMode_le_greybodyRJ (m : ℕ) (T : ℝ) (hT : 0 < T) :
    shellSpectralEnergyBMode m T ≤
      shellModeMultiplicity m * T * greybodyEmissivityB m := by
  unfold shellSpectralEnergyBMode greybodyEmissivityB
  have hRJ : shellSpectralEnergy m T < shellModeMultiplicity m * T :=
    shellSpectralEnergy_lt_RJ m T hT
  have hε := emissionBModeFraction_nonneg m
  exact mul_le_mul_of_nonneg_right (le_of_lt hRJ) hε

/-! ## Polarized Stefan-Boltzmann bounds -/

/-- **HQIV Stefan-Boltzmann E-mode (greybody) upper bound:**
`U_E(T) ≤ T · Σ_m N_m · ε(m)`. -/
theorem stefanBoltzmann_EMode_greybody_upperBound
    (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    blackbodyEnergyDensityEMode T m_UV m_IR ≤
      T * cumulativeGreybodyEmissivity m_UV m_IR := by
  unfold blackbodyEnergyDensityEMode cumulativeGreybodyEmissivity
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have h := shellSpectralEnergyEMode_le_greybodyRJ m T hT
  have hrw : T * (shellModeMultiplicity m * greybodyEmissivity m) =
             shellModeMultiplicity m * T * greybodyEmissivity m := by ring
  linarith

/-- **HQIV Stefan-Boltzmann B-mode (greybody) upper bound:**
`U_B(T) ≤ T · Σ_m N_m · ε_B(m)`. -/
theorem stefanBoltzmann_BMode_greybody_upperBound
    (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    blackbodyEnergyDensityBMode T m_UV m_IR ≤
      T * cumulativeGreybodyEmissivityB m_UV m_IR := by
  unfold blackbodyEnergyDensityBMode cumulativeGreybodyEmissivityB
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have h := shellSpectralEnergyBMode_le_greybodyRJ m T hT
  have hrw : T * (shellModeMultiplicity m * greybodyEmissivityB m) =
             shellModeMultiplicity m * T * greybodyEmissivityB m := by ring
  linarith

/-- **Sanity check:** sum of E- and B-mode greybody bounds equals the total
Rayleigh-Jeans ceiling. -/
theorem stefanBoltzmann_total_from_greybody
    (T : ℝ) (m_UV m_IR : ℕ) :
    T * cumulativeGreybodyEmissivity m_UV m_IR +
        T * cumulativeGreybodyEmissivityB m_UV m_IR =
      T * cumulativeShellModeMultiplicity m_UV m_IR := by
  rw [← mul_add, cumulativeGreybodyEmissivity_complement]

/-! ## Polarized Kirchhoff law -/

/-- **Polarized Kirchhoff equilibrium structure.** At each shell, polarized
emissivity equals polarized absorptivity in each channel separately. -/
structure PolarizedKirchhoffEquilibrium (T : ℝ) (m_UV m_IR : ℕ) where
  emissionE : ℕ → ℝ
  absorptionE : ℕ → ℝ
  emissionB : ℕ → ℝ
  absorptionB : ℕ → ℝ
  emissionE_eq_absorptionE :
    ∀ m, m_UV ≤ m → m ≤ m_IR → emissionE m = absorptionE m
  emissionB_eq_absorptionB :
    ∀ m, m_UV ≤ m → m ≤ m_IR → emissionB m = absorptionB m

/-- **Standard polarized Kirchhoff witness:** the E-mode/B-mode spectral
energies are themselves an equilibrium pair (emission = absorption in each
channel, trivially). -/
def standardPolarizedKirchhoff (T : ℝ) (m_UV m_IR : ℕ) :
    PolarizedKirchhoffEquilibrium T m_UV m_IR :=
  { emissionE := fun m => shellSpectralEnergyEMode m T
    absorptionE := fun m => shellSpectralEnergyEMode m T
    emissionB := fun m => shellSpectralEnergyBMode m T
    absorptionB := fun m => shellSpectralEnergyBMode m T
    emissionE_eq_absorptionE := fun _ _ _ => rfl
    emissionB_eq_absorptionB := fun _ _ _ => rfl }

/-- **Polarized Kirchhoff theorem:** for any polarized equilibrium, the
sums over the shell window of emission and absorption agree in each
channel. -/
theorem polarized_kirchhoff_total
    (T : ℝ) (m_UV m_IR : ℕ) (_h : m_UV ≤ m_IR)
    (K : PolarizedKirchhoffEquilibrium T m_UV m_IR) :
    (∑ m ∈ Finset.Icc m_UV m_IR, K.emissionE m =
        ∑ m ∈ Finset.Icc m_UV m_IR, K.absorptionE m) ∧
    (∑ m ∈ Finset.Icc m_UV m_IR, K.emissionB m =
        ∑ m ∈ Finset.Icc m_UV m_IR, K.absorptionB m) := by
  refine ⟨Finset.sum_congr rfl (fun m hm => ?_),
          Finset.sum_congr rfl (fun m hm => ?_)⟩
  · rcases Finset.mem_Icc.mp hm with ⟨ha, hb⟩
    exact K.emissionE_eq_absorptionE m ha hb
  · rcases Finset.mem_Icc.mp hm with ⟨ha, hb⟩
    exact K.emissionB_eq_absorptionB m ha hb

/-! ## Polarization asymmetry density -/

/-- **Cumulative polarization asymmetry:** `U_E − U_B`, summed over the
shell window. Positive means E-mode dominant; negative means B-mode dominant. -/
noncomputable def polarizationAsymmetryDensity
    (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  blackbodyEnergyDensityEMode T m_UV m_IR -
    blackbodyEnergyDensityBMode T m_UV m_IR

/-- **Sum/difference decomposition:**
`U_E = (U + Δ)/2` and `U_B = (U − Δ)/2` where `Δ` is the asymmetry. -/
theorem polarizationAsymmetry_decomposition
    (T : ℝ) (m_UV m_IR : ℕ) :
    blackbodyEnergyDensityEMode T m_UV m_IR =
        (blackbodyEnergyDensity T m_UV m_IR +
          polarizationAsymmetryDensity T m_UV m_IR) / 2 ∧
    blackbodyEnergyDensityBMode T m_UV m_IR =
        (blackbodyEnergyDensity T m_UV m_IR -
          polarizationAsymmetryDensity T m_UV m_IR) / 2 := by
  unfold polarizationAsymmetryDensity
  have h := blackbodyEnergyDensity_E_plus_B T m_UV m_IR
  refine ⟨?_, ?_⟩ <;> linarith

/-! ## Numerical witnesses at the lock-in window -/

/-- **Lock-in window E-mode bound:**
`cumulativeGreybodyEmissivity 0 referenceM ≤ 120`. -/
theorem cumulativeGreybodyEmissivity_referenceM_bound :
    cumulativeGreybodyEmissivity 0 Hqiv.referenceM ≤ 120 := by
  have h1 := cumulativeGreybodyEmissivity_le_cumulative 0 Hqiv.referenceM
  have h2 :
      cumulativeShellModeMultiplicity 0 Hqiv.referenceM =
        Hqiv.available_modes Hqiv.referenceM :=
    cumulativeShellModeMultiplicity_zero_eq_availableModes _
  have h3 : Hqiv.available_modes Hqiv.referenceM = 120 :=
    availableModes_referenceM_eq_120
  linarith

/-- **Lock-in window B-mode bound:**
`cumulativeGreybodyEmissivityB 0 referenceM ≤ 120`. -/
theorem cumulativeGreybodyEmissivityB_referenceM_bound :
    cumulativeGreybodyEmissivityB 0 Hqiv.referenceM ≤ 120 := by
  have h1 := cumulativeGreybodyEmissivityB_le_cumulative 0 Hqiv.referenceM
  have h2 :
      cumulativeShellModeMultiplicity 0 Hqiv.referenceM =
        Hqiv.available_modes Hqiv.referenceM :=
    cumulativeShellModeMultiplicity_zero_eq_availableModes _
  have h3 : Hqiv.available_modes Hqiv.referenceM = 120 :=
    availableModes_referenceM_eq_120
  linarith

/-- **Lock-in Stefan-Boltzmann polarized witness:** at `[0, referenceM]`,
both `U_E(T) ≤ 120 T` and `U_B(T) ≤ 120 T`. -/
theorem stefanBoltzmann_polarized_referenceM_bound (T : ℝ) (hT : 0 < T) :
    blackbodyEnergyDensityEMode T 0 Hqiv.referenceM ≤ 120 * T ∧
    blackbodyEnergyDensityBMode T 0 Hqiv.referenceM ≤ 120 * T := by
  refine ⟨?_, ?_⟩
  · have hE := stefanBoltzmann_EMode_greybody_upperBound T 0 Hqiv.referenceM hT
    have hbound := cumulativeGreybodyEmissivity_referenceM_bound
    have : T * cumulativeGreybodyEmissivity 0 Hqiv.referenceM ≤ T * 120 :=
      mul_le_mul_of_nonneg_left hbound hT.le
    linarith
  · have hB := stefanBoltzmann_BMode_greybody_upperBound T 0 Hqiv.referenceM hT
    have hbound := cumulativeGreybodyEmissivityB_referenceM_bound
    have : T * cumulativeGreybodyEmissivityB 0 Hqiv.referenceM ≤ T * 120 :=
      mul_le_mul_of_nonneg_left hbound hT.le
    linarith

end

end Hqiv.Physics
