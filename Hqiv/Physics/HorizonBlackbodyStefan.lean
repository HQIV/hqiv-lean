import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.HorizonBlackbodySpectrum
import Hqiv.Physics.HorizonBlackbodyLadder

/-!
# HQIV Stefan–Boltzmann scaling on the truncated shell sum

Honest "Stefan–Boltzmann" bounds for `blackbodyEnergyDensity T m_UV m_IR` from
`HorizonBlackbodySpectrum`.  The HQIV null-lattice mode count is
`Hqiv.available_modes m = 4(m+1)(m+2)` — the cumulative grows quadratically
in shell index, not cubically.  So the *finite-cutoff* analog of Stefan–
Boltzmann is **not** `U ∝ T⁴`; it is a clean bracketing of the truncated sum
between explicit Rayleigh–Jeans (upper) and Wien (lower) envelopes.

* **Cumulative mode budget.**
  `cumulativeShellModeMultiplicity m_UV m_IR := Σ_{m ∈ [m_UV, m_IR]} N_m`
  with the closed-form identity (proved):
  `cumulativeShellModeMultiplicity 0 M = Hqiv.available_modes M`.

* **Rayleigh–Jeans upper bound (Stefan-Boltzmann ceiling).**
  `blackbodyEnergyDensity T m_UV m_IR < T · cumulativeShellModeMultiplicity m_UV m_IR`
  for every `T > 0` and `m_UV ≤ m_IR`.  Direct consequence of the universal
  per-shell bound `u_m(T) < N_m · T` (`shellSpectralEnergy_lt_RJ`).

* **Wien lower bound (Stefan-Boltzmann floor).**
  `Σ N_m · ω_m · exp(-ω_m/T) < U(T)` via the universal Bose-factor lower
  bound `exp(-ω/T) < n_B(ω, T)` (from `exp(x) − 1 < exp(x)`).

* **Stefan-Boltzmann radiance ratio.**
  `U(T) / T < cumulativeShellModeMultiplicity m_UV m_IR` — the HQIV-derived
  *integer* mode budget plays the role of the dimensionful Stefan–Boltzmann
  constant `σ`.  No empirical input.

* **Numerical witness at the lock-in window.**
  `U(T) < 120 · T` between shells `0` and `Hqiv.referenceM = 4`
  (since `available_modes 4 = 4·5·6 = 120`).

Zero `sorry`; no new axioms.
-/

namespace Hqiv.Physics

open scoped BigOperators
open Hqiv

noncomputable section

/-! ## Cumulative mode budget on a shell window -/

/-- Cumulative shell mode multiplicity on the window `[m_UV, m_IR]`. -/
noncomputable def cumulativeShellModeMultiplicity (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellModeMultiplicity m

theorem cumulativeShellModeMultiplicity_nonneg (m_UV m_IR : ℕ) :
    0 ≤ cumulativeShellModeMultiplicity m_UV m_IR := by
  unfold cumulativeShellModeMultiplicity
  exact Finset.sum_nonneg (fun m _ => shellModeMultiplicity_nonneg m)

theorem cumulativeShellModeMultiplicity_pos (m_UV m_IR : ℕ)
    (h : m_UV ≤ m_IR) :
    0 < cumulativeShellModeMultiplicity m_UV m_IR := by
  unfold cumulativeShellModeMultiplicity
  refine Finset.sum_pos (fun k _ => shellModeMultiplicity_pos k) ?_
  exact ⟨m_UV, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩

/-- **Telescoping identity** between cumulative shell sum and `available_modes`:
the cumulative budget from the Planck-pole shell `0` to a cutoff `M` equals
the standard HQIV cumulative mode count `available_modes M`. -/
theorem cumulativeShellModeMultiplicity_zero_eq_availableModes (M : ℕ) :
    cumulativeShellModeMultiplicity 0 M = Hqiv.available_modes M := by
  induction M with
  | zero =>
      unfold cumulativeShellModeMultiplicity shellModeMultiplicity
      simp [Finset.Icc_self, new_modes_zero]
  | succ M ih =>
      have hIcc : Finset.Icc (0 : ℕ) (M + 1) = insert (M + 1) (Finset.Icc 0 M) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert, Nat.zero_le, true_and]
        omega
      have hnotin : (M + 1) ∉ Finset.Icc (0 : ℕ) M := by
        simp [Finset.mem_Icc]
      unfold cumulativeShellModeMultiplicity at ih ⊢
      rw [hIcc, Finset.sum_insert hnotin, ih]
      unfold shellModeMultiplicity
      have hnew : new_modes (M + 1) = available_modes (M + 1) - available_modes M := by
        unfold new_modes
        simp
      rw [hnew]
      ring

/-! ## Stefan–Boltzmann upper bound (Rayleigh–Jeans envelope) -/

/-- **HQIV Stefan-Boltzmann upper bound:** the truncated blackbody energy
density is strictly bounded above by `T × (cumulative mode count)`.

Direct consequence of the universal per-shell bound
`shellSpectralEnergy m T < shellModeMultiplicity m · T`. -/
theorem stefanBoltzmann_RJ_upperBound
    (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) (h : m_UV ≤ m_IR) :
    blackbodyEnergyDensity T m_UV m_IR <
      T * cumulativeShellModeMultiplicity m_UV m_IR := by
  unfold blackbodyEnergyDensity cumulativeShellModeMultiplicity
  have hsum :
      T * (∑ m ∈ Finset.Icc m_UV m_IR, shellModeMultiplicity m) =
        ∑ m ∈ Finset.Icc m_UV m_IR, shellModeMultiplicity m * T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hsum]
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · exact ⟨m_UV, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
  · intro k _
    exact shellSpectralEnergy_lt_RJ k T hT

/-! ## Stefan–Boltzmann lower bound (Wien envelope) -/

/-- **Universal Bose-factor lower bound** by the Wien exponential:
`exp(-ω/T) < n_B(ω, T)`.

Proof: `exp(x) − 1 < exp(x)` for any `x > 0`, hence
`1/exp(x) < 1/(exp(x) − 1)`, and `exp(-x) = 1/exp(x)`. -/
theorem nBose_gt_exp_neg (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) :
    Real.exp (-(ω / T)) < nBose ω T := by
  unfold nBose
  have hpos : 0 < ω / T := div_pos hω hT
  have hexp_gt_one : 1 < Real.exp (ω / T) := Real.one_lt_exp_iff.mpr hpos
  have hsub_pos : 0 < Real.exp (ω / T) - 1 := by linarith
  have hsub_lt : Real.exp (ω / T) - 1 < Real.exp (ω / T) := by linarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt hsub_pos hsub_lt

/-- **Per-shell Wien lower bound:**
`N_m · ω_m · exp(-ω_m/T) < u_m(T)`. -/
theorem shellSpectralEnergy_gt_wien (m : ℕ) (T : ℝ) (hT : 0 < T) :
    shellModeMultiplicity m * shellOmega m * Real.exp (-(shellOmega m / T)) <
      shellSpectralEnergy m T := by
  unfold shellSpectralEnergy planckMeanEnergy
  have hbose := nBose_gt_exp_neg (shellOmega m) T (shellOmega_pos m) hT
  have hNm_pos : 0 < shellModeMultiplicity m := shellModeMultiplicity_pos m
  have hω_pos : 0 < shellOmega m := shellOmega_pos m
  have h1 :
      shellOmega m * Real.exp (-(shellOmega m / T)) <
        shellOmega m * nBose (shellOmega m) T :=
    mul_lt_mul_of_pos_left hbose hω_pos
  calc shellModeMultiplicity m * shellOmega m *
          Real.exp (-(shellOmega m / T))
      = shellModeMultiplicity m *
          (shellOmega m * Real.exp (-(shellOmega m / T))) := by ring
    _ < shellModeMultiplicity m *
          (shellOmega m * nBose (shellOmega m) T) :=
        mul_lt_mul_of_pos_left h1 hNm_pos

/-- **HQIV Stefan-Boltzmann lower bound (Wien envelope):**
`Σ_{m ∈ [m_UV, m_IR]} N_m · ω_m · exp(-ω_m/T) < U(T)`
for any `T > 0` and `m_UV ≤ m_IR`. -/
theorem stefanBoltzmann_Wien_lowerBound
    (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) (h : m_UV ≤ m_IR) :
    (∑ m ∈ Finset.Icc m_UV m_IR,
        shellModeMultiplicity m * shellOmega m *
          Real.exp (-(shellOmega m / T))) <
      blackbodyEnergyDensity T m_UV m_IR := by
  unfold blackbodyEnergyDensity
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · exact ⟨m_UV, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
  · intro k _
    exact shellSpectralEnergy_gt_wien k T hT

/-! ## Stefan–Boltzmann radiance ratio -/

/-- **Stefan–Boltzmann radiance ratio bound:** `U(T) / T < (cumulative count)`.

The right-hand side is an *integer* (after division by 4): the HQIV cumulative
mode budget, derived from the lattice combinatorics alone.  It plays the role
of the dimensionful Stefan–Boltzmann constant `σ` — bounded by a discrete,
parameter-free mode budget instead of an empirical constant. -/
theorem stefanBoltzmann_radianceRatio_bound
    (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) (h : m_UV ≤ m_IR) :
    blackbodyEnergyDensity T m_UV m_IR / T <
      cumulativeShellModeMultiplicity m_UV m_IR := by
  rw [div_lt_iff₀ hT, mul_comm]
  exact stefanBoltzmann_RJ_upperBound T m_UV m_IR hT h

/-! ## Default-window and numerical witnesses -/

/-- At the default window `[0, M]` the Stefan-Boltzmann upper bound reads
`U(T) < T · available_modes M`. -/
theorem stefanBoltzmann_planckPoleWindow_bound (T : ℝ) (M : ℕ) (hT : 0 < T) :
    blackbodyEnergyDensity T 0 M < T * Hqiv.available_modes M := by
  have h := stefanBoltzmann_RJ_upperBound T 0 M hT (Nat.zero_le _)
  rw [cumulativeShellModeMultiplicity_zero_eq_availableModes] at h
  exact h

/-- Closed-form numerical witness: `available_modes referenceM = 120`. -/
theorem availableModes_referenceM_eq_120 :
    Hqiv.available_modes Hqiv.referenceM = 120 := by
  rw [available_modes_eq]
  have hr : Hqiv.referenceM = 4 := by
    unfold Hqiv.referenceM Hqiv.qcdShell Hqiv.stepsFromQCDToLockin
      Hqiv.latticeStepCount
    norm_num
  rw [hr]
  push_cast
  norm_num

/-- **Numerical Stefan–Boltzmann witness** at the lock-in window
`[0, referenceM]`: `U(T) < 120 · T`. -/
theorem stefanBoltzmann_referenceM_bound (T : ℝ) (hT : 0 < T) :
    blackbodyEnergyDensity T 0 Hqiv.referenceM < 120 * T := by
  have h := stefanBoltzmann_planckPoleWindow_bound T Hqiv.referenceM hT
  rw [availableModes_referenceM_eq_120] at h
  linarith

/-- Radiance ratio version of the lock-in witness:
`U(T) / T < 120` at the default `[0, referenceM]` window. -/
theorem stefanBoltzmann_referenceM_ratio_bound (T : ℝ) (hT : 0 < T) :
    blackbodyEnergyDensity T 0 Hqiv.referenceM / T < 120 := by
  have h := stefanBoltzmann_referenceM_bound T hT
  rw [div_lt_iff₀ hT]
  linarith

end

end Hqiv.Physics
