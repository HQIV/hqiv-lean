import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField
import Hqiv.QuantumOptics.HorizonQED

/-!
# HQIV Horizon-Lattice Blackbody Spectrum

This module derives the **blackbody spectrum** from HQIV first principles:

* **Shell-mode frequencies** come from the temperature ladder
  `T(m) = T_Pl / (m+1)` in `Hqiv.Geometry.AuxiliaryField`.  Every shell `m`
  contributes a single dimensionless frequency tag
  `ω_m := T(m) = 1/(m+1)` in natural Planck units
  (`Hqiv.QuantumOptics.dimensionlessOmegaShell_eq`).
* **Per-shell mode multiplicity** is the *new* modes coming online at that shell:
  `N_m := Hqiv.new_modes m`.  Closed forms (`new_modes_zero`, `new_modes_succ`):
  `N_0 = 8`, `N_{m+1} = 8(m+2)` — the octonion × stars-and-bars count from
  `OctonionicLightCone`.
* **Bose–Einstein occupation**: `n_B(ω, T) = 1/(exp(ω/T) − 1)`.
* **Spectral energy at shell `m`, temperature `T`**:
  `u_m(T) := N_m · ω_m · n_B(ω_m, T)`.
* **Truncated total energy density** between explicit cutoffs `m_UV ≤ m_IR`:
  `U(T; m_UV, m_IR) := ∑_{m ∈ [m_UV, m_IR]} u_m(T)`.

## Geometric origin of the IR / UV cutoffs

In HQIV both Planck-law divergences ("ultraviolet catastrophe" and the
unbounded long-wavelength tail of a continuum integral) are **structurally
absent**: the mode list is *finite* on every finite shell window.

* **UV cutoff (`m_UV : ℕ`):** smallest shell index included.  Shell `m = 0` is
  the **Planck pole** with `ω = T_Pl = 1`.  Increasing `m_UV` truncates UV modes
  explicitly; the choice `m_UV = 0` is the parameter-free default
  (`planckUVCutoff`).  *No new regulator* — the cutoff is just where the
  octonion null lattice begins.

* **IR cutoff (`m_IR : ℕ`):** largest shell index included.  The outer horizon
  radius is `R_h(m_IR) = m_IR + 1` in Planck units, so the smallest accessible
  frequency is `ω_min = T(m_IR) = 1/(m_IR + 1)`.  Frequencies below this are
  *not in the HQIV mode list*; there is no `ω → 0` integration to regulate.
  The honest derived default is `referenceIRCutoff = Hqiv.referenceM` (the
  lock-in shell from `OctonionicLightCone.referenceM`).

The truncated spectrum `blackbodyEnergyDensity T m_UV m_IR` is therefore a
finite real for **every** `(T, m_UV, m_IR)` with `T > 0`.  The continuum
"thermodynamic" limit `m_IR → ∞` is *not* taken here: each truncation is finite
by construction (`Finset.sum`).  This is the same honesty discipline as
`LightConeFundamentalsPillars` Pillar E (IR/UV regulators stated as the same
`available_modes` / shell budget, never an added bare parameter).

## What this file does *not* claim

* No PDG / measured blackbody anchor is imported; no Stefan–Boltzmann fit.
* No continuum `dω`-integral identity.  All Planck-spectrum statements are
  *finite shell sums* at the HQIV honesty level.
* Kirchhoff's law and detailed balance are *narrated* downstream in the paper;
  here we only build the spectral object that they refer to.

Zero `sorry`; no new axioms.
-/

namespace Hqiv.Physics

open scoped BigOperators
open Hqiv
open Hqiv.QuantumOptics

noncomputable section

/-! ## Shell-mode frequency -/

/-- Shell-mode angular frequency tag in natural Planck units:
`ω_m := T(m) = 1/(m+1)`.  Equal to `dimensionlessOmegaShell m` from
`HorizonQED`. -/
noncomputable def shellOmega (m : ℕ) : ℝ := T m

theorem shellOmega_eq (m : ℕ) : shellOmega m = 1 / (m + 1 : ℝ) := by
  unfold shellOmega
  exact T_eq m

theorem shellOmega_eq_dimensionlessOmegaShell (m : ℕ) :
    shellOmega m = dimensionlessOmegaShell m := by
  unfold shellOmega dimensionlessOmegaShell
  rw [T_Pl_eq]
  ring

theorem shellOmega_pos (m : ℕ) : 0 < shellOmega m := T_pos m

/-- Frequency ladder is **decreasing** in shell index: deeper IR shells have
smaller `ω_m`. -/
theorem shellOmega_antitone : Antitone shellOmega := by
  intro a b hab
  rw [shellOmega_eq a, shellOmega_eq b]
  apply one_div_le_one_div_of_le
  · have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    linarith
  · exact_mod_cast Nat.add_le_add_right hab 1

/-! ## Bose–Einstein occupation -/

/-- Bose–Einstein occupation number: `n_B(ω, T) = 1/(exp(ω/T) − 1)`. -/
noncomputable def nBose (ω T : ℝ) : ℝ := 1 / (Real.exp (ω / T) - 1)

theorem nBose_pos (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) :
    0 < nBose ω T := by
  unfold nBose
  have hpos : 0 < ω / T := div_pos hω hT
  have hexp : 1 < Real.exp (ω / T) := Real.one_lt_exp_iff.mpr hpos
  have hsub : 0 < Real.exp (ω / T) - 1 := by linarith
  exact one_div_pos.mpr hsub

theorem nBose_nonneg (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) :
    0 ≤ nBose ω T :=
  le_of_lt (nBose_pos ω T hω hT)

/-! ## Per-shell mode multiplicity -/

/-- Per-shell mode multiplicity: equal to `Hqiv.new_modes m`
(octonion × stars-and-bars count).  Closed form: `N_0 = 8`,
`N_{m+1} = 8(m+2)`. -/
noncomputable def shellModeMultiplicity (m : ℕ) : ℝ := Hqiv.new_modes m

theorem shellModeMultiplicity_zero :
    shellModeMultiplicity 0 = 8 := by
  unfold shellModeMultiplicity
  rw [new_modes_zero, available_modes_eq]
  push_cast
  norm_num

theorem shellModeMultiplicity_succ (m : ℕ) :
    shellModeMultiplicity (m + 1) = 8 * ((m : ℝ) + 2) :=
  new_modes_succ m

theorem shellModeMultiplicity_pos (m : ℕ) : 0 < shellModeMultiplicity m := by
  unfold shellModeMultiplicity
  cases m with
  | zero =>
      rw [new_modes_zero, available_modes_eq]
      push_cast
      norm_num
  | succ k =>
      rw [new_modes_succ]
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      positivity

theorem shellModeMultiplicity_nonneg (m : ℕ) : 0 ≤ shellModeMultiplicity m :=
  le_of_lt (shellModeMultiplicity_pos m)

/-! ## Planck mean energy per mode -/

/-- Mean *thermal* energy of a single oscillator mode at frequency `ω` and
temperature `T`:
`⟨E⟩(ω, T) = ω · n_B(ω, T) = ω / (exp(ω/T) − 1)`. -/
noncomputable def planckMeanEnergy (ω T : ℝ) : ℝ :=
  ω * nBose ω T

theorem planckMeanEnergy_pos (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) :
    0 < planckMeanEnergy ω T :=
  mul_pos hω (nBose_pos ω T hω hT)

theorem planckMeanEnergy_nonneg (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) :
    0 ≤ planckMeanEnergy ω T :=
  le_of_lt (planckMeanEnergy_pos ω T hω hT)

/-- Mean *total* energy per mode **including** the zero-point cell `ω/2`
(Casimir vacuum slot, same cell as `casimirPerModeZeroPoint`). -/
noncomputable def planckMeanEnergyWithVacuum (ω T : ℝ) : ℝ :=
  ω / 2 + planckMeanEnergy ω T

theorem planckMeanEnergyWithVacuum_pos (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) :
    0 < planckMeanEnergyWithVacuum ω T := by
  unfold planckMeanEnergyWithVacuum
  have h1 : 0 < ω / 2 := by positivity
  have h2 : 0 < planckMeanEnergy ω T := planckMeanEnergy_pos ω T hω hT
  linarith

/-! ## Per-shell spectral energy (Planck contribution at shell `m`) -/

/-- Spectral energy contribution of shell `m` at temperature `T`:
`u_m(T) := N_m · ω_m · n_B(ω_m, T)`. -/
noncomputable def shellSpectralEnergy (m : ℕ) (T : ℝ) : ℝ :=
  shellModeMultiplicity m * planckMeanEnergy (shellOmega m) T

theorem shellSpectralEnergy_pos (m : ℕ) (T : ℝ) (hT : 0 < T) :
    0 < shellSpectralEnergy m T :=
  mul_pos (shellModeMultiplicity_pos m)
    (planckMeanEnergy_pos (shellOmega m) T (shellOmega_pos m) hT)

theorem shellSpectralEnergy_nonneg (m : ℕ) (T : ℝ) (hT : 0 < T) :
    0 ≤ shellSpectralEnergy m T :=
  le_of_lt (shellSpectralEnergy_pos m T hT)

/-- Shell spectral energy including the vacuum (zero-point) cell. -/
noncomputable def shellSpectralEnergyWithVacuum (m : ℕ) (T : ℝ) : ℝ :=
  shellModeMultiplicity m * planckMeanEnergyWithVacuum (shellOmega m) T

theorem shellSpectralEnergyWithVacuum_pos (m : ℕ) (T : ℝ) (hT : 0 < T) :
    0 < shellSpectralEnergyWithVacuum m T :=
  mul_pos (shellModeMultiplicity_pos m)
    (planckMeanEnergyWithVacuum_pos (shellOmega m) T (shellOmega_pos m) hT)

/-! ## Truncated blackbody spectrum (explicit IR/UV cutoffs) -/

/-- **Truncated blackbody energy density** between shell cutoffs
`m_UV ≤ m_IR`, **without** vacuum zero-point.

The sum runs over `m ∈ [m_UV, m_IR]` (inclusive on both ends).

* **UV cutoff** `m_UV` — smallest shell index. Shell `m = 0` is the **Planck
  pole**, with `ω_0 = T_Pl = 1`. Setting `m_UV > 0` removes ultraviolet
  shells explicitly.

* **IR cutoff** `m_IR` — largest shell index. Outer horizon radius
  `R_h(m_IR) = m_IR + 1`. Frequencies smaller than `ω_min = 1/(m_IR + 1)`
  do not exist in the HQIV mode list.

This is a *finite* sum for every choice of cutoffs; no IR/UV divergence is
possible at the spectrum level. -/
noncomputable def blackbodyEnergyDensity (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellSpectralEnergy m T

theorem blackbodyEnergyDensity_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ blackbodyEnergyDensity T m_UV m_IR := by
  unfold blackbodyEnergyDensity
  refine Finset.sum_nonneg ?_
  intro m _
  exact shellSpectralEnergy_nonneg m T hT

theorem blackbodyEnergyDensity_pos_of_le
    (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) (h : m_UV ≤ m_IR) :
    0 < blackbodyEnergyDensity T m_UV m_IR := by
  unfold blackbodyEnergyDensity
  have hne : (Finset.Icc m_UV m_IR).Nonempty :=
    ⟨m_UV, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
  exact Finset.sum_pos (fun k _ => shellSpectralEnergy_pos k T hT) hne

/-- Extending the **IR cutoff** (more low-frequency shells) only adds
positive contributions. -/
theorem blackbodyEnergyDensity_mono_IR (T : ℝ) (m_UV m_IR m_IR' : ℕ)
    (hT : 0 < T) (h : m_IR ≤ m_IR') :
    blackbodyEnergyDensity T m_UV m_IR ≤ blackbodyEnergyDensity T m_UV m_IR' := by
  unfold blackbodyEnergyDensity
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1, le_trans hm.2 h⟩
  · intro m _ _
    exact shellSpectralEnergy_nonneg m T hT

/-- Lowering the **UV cutoff** (more high-frequency shells) only adds
positive contributions. -/
theorem blackbodyEnergyDensity_mono_UV (T : ℝ) (m_UV m_UV' m_IR : ℕ)
    (hT : 0 < T) (h : m_UV' ≤ m_UV) :
    blackbodyEnergyDensity T m_UV m_IR ≤ blackbodyEnergyDensity T m_UV' m_IR := by
  unfold blackbodyEnergyDensity
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨le_trans h hm.1, hm.2⟩
  · intro m _ _
    exact shellSpectralEnergy_nonneg m T hT

/-! ## Vacuum zero-point sum and full spectrum -/

/-- Truncated **vacuum zero-point** sum: `Σ_{m ∈ [m_UV, m_IR]} N_m · ω_m / 2`.
Same per-mode cell as `casimirPerModeZeroPoint` (with `ω = ω_m`). -/
noncomputable def vacuumZeroPointEnergy (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellModeMultiplicity m * shellOmega m / 2

theorem vacuumZeroPointEnergy_nonneg (m_UV m_IR : ℕ) :
    0 ≤ vacuumZeroPointEnergy m_UV m_IR := by
  unfold vacuumZeroPointEnergy
  refine Finset.sum_nonneg ?_
  intro m _
  have h1 : 0 ≤ shellModeMultiplicity m := shellModeMultiplicity_nonneg m
  have h2 : 0 ≤ shellOmega m := le_of_lt (shellOmega_pos m)
  have hmul : 0 ≤ shellModeMultiplicity m * shellOmega m := mul_nonneg h1 h2
  exact div_nonneg hmul (by norm_num : (0 : ℝ) ≤ 2)

/-- Total spectrum **including vacuum cell**, between explicit IR/UV cutoffs. -/
noncomputable def blackbodyEnergyDensityWithVacuum (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellSpectralEnergyWithVacuum m T

/-- **Decomposition:** total = zero-point + thermal. -/
theorem blackbodyEnergyDensityWithVacuum_eq (T : ℝ) (m_UV m_IR : ℕ) :
    blackbodyEnergyDensityWithVacuum T m_UV m_IR =
      vacuumZeroPointEnergy m_UV m_IR + blackbodyEnergyDensity T m_UV m_IR := by
  unfold blackbodyEnergyDensityWithVacuum vacuumZeroPointEnergy
    blackbodyEnergyDensity shellSpectralEnergyWithVacuum shellSpectralEnergy
    planckMeanEnergyWithVacuum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem blackbodyEnergyDensityWithVacuum_pos (T : ℝ) (m_UV m_IR : ℕ)
    (hT : 0 < T) (h : m_UV ≤ m_IR) :
    0 < blackbodyEnergyDensityWithVacuum T m_UV m_IR := by
  unfold blackbodyEnergyDensityWithVacuum
  have hne : (Finset.Icc m_UV m_IR).Nonempty :=
    ⟨m_UV, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
  exact Finset.sum_pos (fun k _ => shellSpectralEnergyWithVacuum_pos k T hT) hne

/-! ## HQIV-anchored cutoffs and boundary frequencies -/

/-- **Default UV cutoff:** Planck pole `m = 0`. -/
def planckUVCutoff : ℕ := 0

/-- **Default IR cutoff:** lock-in reference shell from `OctonionicLightCone`
(QCD shell + steps from QCD to lock-in; numerically `4`). -/
def referenceIRCutoff : ℕ := Hqiv.referenceM

/-- Spectrum at the default `(planckUVCutoff, referenceIRCutoff)` window. -/
noncomputable def blackbodySpectrumAtReference (T : ℝ) : ℝ :=
  blackbodyEnergyDensity T planckUVCutoff referenceIRCutoff

theorem blackbodySpectrumAtReference_nonneg (T : ℝ) (hT : 0 < T) :
    0 ≤ blackbodySpectrumAtReference T :=
  blackbodyEnergyDensity_nonneg T planckUVCutoff referenceIRCutoff hT

/-- The default window `(planckUVCutoff, referenceIRCutoff)` is nonempty
(`0 ≤ referenceM`). -/
theorem default_window_nonempty :
    planckUVCutoff ≤ referenceIRCutoff := by
  unfold planckUVCutoff referenceIRCutoff
  exact Nat.zero_le _

theorem blackbodySpectrumAtReference_pos (T : ℝ) (hT : 0 < T) :
    0 < blackbodySpectrumAtReference T :=
  blackbodyEnergyDensity_pos_of_le T _ _ hT default_window_nonempty

/-- Outer horizon radius set by the IR cutoff: `R_h(m_IR) = m_IR + 1`. -/
noncomputable def outerHorizonRadius (m_IR : ℕ) : ℝ := (m_IR : ℝ) + 1

theorem outerHorizonRadius_pos (m_IR : ℕ) : 0 < outerHorizonRadius m_IR := by
  unfold outerHorizonRadius
  have : (0 : ℝ) ≤ (m_IR : ℝ) := Nat.cast_nonneg _
  linarith

/-- Smallest HQIV-accessible frequency: `ω_min(m_IR) = T(m_IR) = 1/(m_IR + 1)`. -/
noncomputable def minFrequency (m_IR : ℕ) : ℝ := T m_IR

theorem minFrequency_eq_inv_horizon (m_IR : ℕ) :
    minFrequency m_IR = 1 / outerHorizonRadius m_IR := by
  unfold minFrequency outerHorizonRadius
  exact T_eq m_IR

theorem minFrequency_pos (m_IR : ℕ) : 0 < minFrequency m_IR := T_pos m_IR

/-- Largest HQIV-accessible frequency: `ω_max(m_UV) = T(m_UV) = 1/(m_UV + 1)`.
With `m_UV = 0` this equals `T_Pl = 1`. -/
noncomputable def maxFrequency (m_UV : ℕ) : ℝ := T m_UV

theorem maxFrequency_at_planckUVCutoff :
    maxFrequency planckUVCutoff = T_Pl := by
  unfold maxFrequency planckUVCutoff
  rw [T_eq 0, T_Pl_eq]
  norm_num

theorem maxFrequency_le_T_Pl (m_UV : ℕ) :
    maxFrequency m_UV ≤ T_Pl := by
  unfold maxFrequency
  rw [T_eq m_UV, T_Pl_eq]
  have h0 : (0 : ℝ) < (m_UV + 1 : ℝ) := by
    have : (0 : ℝ) ≤ (m_UV : ℝ) := Nat.cast_nonneg _
    linarith
  have h1 : (1 : ℝ) ≤ (m_UV + 1 : ℝ) := by
    have : (0 : ℝ) ≤ (m_UV : ℝ) := Nat.cast_nonneg _
    linarith
  exact (div_le_one h0).mpr h1

/-- The IR cutoff is **below** the UV cutoff in frequency:
`ω_min(m_IR) ≤ ω_max(m_UV)` whenever `m_UV ≤ m_IR`. -/
theorem minFrequency_le_maxFrequency (m_UV m_IR : ℕ) (h : m_UV ≤ m_IR) :
    minFrequency m_IR ≤ maxFrequency m_UV := by
  unfold minFrequency maxFrequency
  exact shellOmega_antitone h |>.trans_eq (by rfl) |>.trans_eq (by rfl)
  -- shellOmega antitone gives ω_{m_IR} ≤ ω_{m_UV}; both equal to T at those shells.

/-! ## Continuum-limit handle (statement only)

The Rayleigh–Jeans regime is `ω ≪ T`, where `n_B(ω, T) ≈ T/ω − 1/2`.  We do
*not* derive the continuum integral here: the HQIV honesty discipline is to
work shell-by-shell on the finite mode list, and `blackbodyEnergyDensity T 0 M`
is the **single-block** Planck spectrum at the chosen `M`.

The pillar-level Kubo / linear-response hooks live in
`Hqiv.Physics.LightConeFundamentalsPillars` (`KuboHQIVSpectralWeight`); they
take this spectrum as the underlying mode budget.
-/

end

end Hqiv.Physics
