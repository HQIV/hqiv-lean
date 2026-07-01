import HqivSpine.Physics.Shell
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.Blackbody` — the Planck spectrum and Kirchhoff's law from the shell ladder

The horizon shell ladder fixes a *finite* mode list, and the whole blackbody
story falls out of it with no continuum `dω`-integral and no fitted
Stefan–Boltzmann constant. Everything below rests only on Mathlib and the
spine's own constants (`carrierMultiplicity = 8`, `alphaEM = 3/5`,
`referenceM = 4`); there is no measured anchor.

* **Frequency ladder.** `shellOmega m = 1/(m+1)` is the dimensionless Planck-unit
  frequency tag of shell `m` (`m = 0` is the Planck pole `ω = 1`); it is positive
  and strictly decreasing in `m` (deeper IR shells are softer).

* **Bose occupation & Planck mean energy.** `nBose ω T = 1/(exp(ω/T) − 1)` and
  `planckMeanEnergy ω T = ω·n_B`. The structural heart is the **Rayleigh–Jeans
  ceiling** `planckMeanEnergy ω T < T`, a one-line consequence of the strict
  convexity inequality `x + 1 < eˣ` (`Real.add_one_lt_exp`) — the discrete cure
  for the ultraviolet catastrophe — together with the **Wien-tail bound**
  `n_B ≤ 1/(e−1)` whenever `ω ≥ T`.

* **Mode multiplicity & spectrum.** The per-shell new-mode count is the carrier
  channel count times the radial depth, `shellModeMultiplicity m = 8·(m+1)`, so
  the truncated spectrum `U(T) = ∑_{[m_UV,m_IR]} N_m·planckMeanEnergy` is finite
  for every cutoff window, and obeys the **Stefan–Boltzmann ceiling**
  `U(T) ≤ T·∑ N_m` with no UV/IR divergence to regulate.

* **Wien displacement.** The continuum Wien constant `2.821` is replaced by the
  transition shell `m*(T) = ⌊1/T⌋ − 1` (deepest Rayleigh–Jeans-side shell, the
  next strictly Wien-side). The ratio is bracketed `1 ≤ ω_{m*}/T < 1 + ω_{m*}`,
  so the **HQIV Wien displacement constant is exactly `1`** in Planck units; at
  the lock-in bath `T = 1/(referenceM+1)` the transition shell is `referenceM`.

* **Greybody from birefringence.** The per-shell birefringence angle
  `β(m) = α·log(m+1)` splits each channel into E/B-mode emissivities
  `cos²(2β)`, `sin²(2β)` summing to `1` (greybody completeness) — a *derived*
  greybody coefficient, no empirical `ε`.

* **Kirchhoff's law.** Detailed balance is a `structure` carrying per-shell
  emission/absorption rates that agree on the accessible window; emissivity then
  equals absorptivity channel-by-channel and cumulatively, with the Planck
  spectrum itself as the canonical equilibrium witness.

* **Photon-gas thermodynamics.** `P = U/3`, `s = (4/3)·U/T`, and the Euler
  identity `T·s = (4/3)·U`.

Zero `sorry`; no new axioms; no `native_decide`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation
open scoped BigOperators

noncomputable section

/-! ## Frequency ladder -/

/-- **Shell frequency tag** in Planck units: `ω_m = 1/(m+1)`. Shell `m = 0` is
the Planck pole `ω = 1`; the ladder softens with depth. -/
noncomputable def shellOmega (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

theorem shellOmega_eq (m : ℕ) : shellOmega m = 1 / ((m : ℝ) + 1) := rfl

theorem shellOmega_pos (m : ℕ) : 0 < shellOmega m := by
  unfold shellOmega
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  positivity

/-- The frequency ladder is **antitone**: deeper IR shells carry smaller `ω_m`. -/
theorem shellOmega_antitone : Antitone shellOmega := by
  intro a b hab
  unfold shellOmega
  apply one_div_le_one_div_of_le
  · have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    linarith
  · exact_mod_cast Nat.add_le_add_right hab 1

/-! ## Bose–Einstein occupation and Planck mean energy -/

/-- **Bose–Einstein occupation** `n_B(ω, T) = 1/(exp(ω/T) − 1)`. -/
noncomputable def nBose (ω T : ℝ) : ℝ := 1 / (Real.exp (ω / T) - 1)

theorem nBose_pos (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) : 0 < nBose ω T := by
  unfold nBose
  have hpos : 0 < ω / T := div_pos hω hT
  have hexp : 1 < Real.exp (ω / T) := Real.one_lt_exp_iff.mpr hpos
  have hsub : 0 < Real.exp (ω / T) - 1 := by linarith
  exact one_div_pos.mpr hsub

theorem nBose_nonneg (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) : 0 ≤ nBose ω T :=
  le_of_lt (nBose_pos ω T hω hT)

/-- **Planck mean energy per mode** `⟨E⟩(ω, T) = ω·n_B(ω, T) = ω/(exp(ω/T) − 1)`. -/
noncomputable def planckMeanEnergy (ω T : ℝ) : ℝ := ω * nBose ω T

theorem planckMeanEnergy_pos (ω T : ℝ) (hω : 0 < ω) (hT : 0 < T) :
    0 < planckMeanEnergy ω T :=
  mul_pos hω (nBose_pos ω T hω hT)

/-- **Rayleigh–Jeans ceiling** (the discrete cure for the UV catastrophe): the
mean thermal energy per mode is strictly below the temperature for every
`ω, T > 0`. One line from `x + 1 < eˣ` (`Real.add_one_lt_exp`): with `x = ω/T`,
`eˣ − 1 > x`, so `ω/(eˣ−1) < ω/x = T`. -/
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

/-- **Wien-tail bound** for `ω ≥ T`: the Bose occupation is bounded by the fixed
constant `1/(e − 1) ≈ 0.582`, uniformly. -/
theorem nBose_le_wien_constant (ω T : ℝ) (hT : 0 < T) (h : T ≤ ω) :
    nBose ω T ≤ 1 / (Real.exp 1 - 1) := by
  unfold nBose
  have hge : 1 ≤ ω / T := (one_le_div hT).mpr h
  have hexp_pos : 0 < Real.exp 1 - 1 := by
    have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hsub_le : Real.exp 1 - 1 ≤ Real.exp (ω / T) - 1 := by
    have := Real.exp_le_exp.mpr hge; linarith
  exact one_div_le_one_div_of_le hexp_pos hsub_le

/-! ## Per-shell mode multiplicity (carrier × radial depth) -/

/-- **Per-shell new-mode count** `N_m = carrierMultiplicity·(m+1) = 8·(m+1)`:
the eight octonion carrier channels times the radial depth `m+1`. -/
noncomputable def shellModeMultiplicity (m : ℕ) : ℝ :=
  (carrierMultiplicity : ℝ) * ((m : ℝ) + 1)

theorem shellModeMultiplicity_eq (m : ℕ) :
    shellModeMultiplicity m = 8 * ((m : ℝ) + 1) := by
  unfold shellModeMultiplicity
  rw [show (carrierMultiplicity : ℝ) = 8 from by exact_mod_cast carrierMultiplicity_eq_eight]

theorem shellModeMultiplicity_pos (m : ℕ) : 0 < shellModeMultiplicity m := by
  rw [shellModeMultiplicity_eq]
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  positivity

theorem shellModeMultiplicity_nonneg (m : ℕ) : 0 ≤ shellModeMultiplicity m :=
  le_of_lt (shellModeMultiplicity_pos m)

/-- **The lattice is incompressible — each shell carries one carrier's worth of
zero-point.** The mode count and frequency are exact reciprocals up to the carrier
size: `N_m · ω_m = 8 = carrierMultiplicity`, *independent of `m`*. So the discrete
zero-point slice `N_m·ω_m/2 = 4` is the same on every shell — the lattice cannot be
smoothed into a continuum, and the trapped budget grows strictly linearly outward
toward the horizon. This constant slice is the discrete weight in the tug-of-war
against the Planck-pole curvature concentration. -/
theorem shell_zeroPoint_slice_const (m : ℕ) :
    shellModeMultiplicity m * shellOmega m = (carrierMultiplicity : ℝ) := by
  rw [shellModeMultiplicity_eq, shellOmega_eq,
    show (carrierMultiplicity : ℝ) = 8 from by exact_mod_cast carrierMultiplicity_eq_eight]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ## Per-shell spectral energy and the truncated spectrum -/

/-- **Spectral energy at shell `m`** `u_m(T) = N_m·planckMeanEnergy(ω_m, T)`. -/
noncomputable def shellSpectralEnergy (m : ℕ) (T : ℝ) : ℝ :=
  shellModeMultiplicity m * planckMeanEnergy (shellOmega m) T

theorem shellSpectralEnergy_pos (m : ℕ) (T : ℝ) (hT : 0 < T) :
    0 < shellSpectralEnergy m T :=
  mul_pos (shellModeMultiplicity_pos m)
    (planckMeanEnergy_pos (shellOmega m) T (shellOmega_pos m) hT)

theorem shellSpectralEnergy_nonneg (m : ℕ) (T : ℝ) (hT : 0 < T) :
    0 ≤ shellSpectralEnergy m T :=
  le_of_lt (shellSpectralEnergy_pos m T hT)

/-- **Per-shell Rayleigh–Jeans bound** `u_m(T) < N_m·T`. -/
theorem shellSpectralEnergy_lt_RJ (m : ℕ) (T : ℝ) (hT : 0 < T) :
    shellSpectralEnergy m T < shellModeMultiplicity m * T := by
  unfold shellSpectralEnergy
  exact mul_lt_mul_of_pos_left
    (planckMeanEnergy_lt_T (shellOmega m) T (shellOmega_pos m) hT)
    (shellModeMultiplicity_pos m)

/-- **Truncated blackbody energy density** between explicit cutoffs
`m_UV ≤ m_IR`: a finite shell sum, so no UV/IR divergence is even expressible. -/
noncomputable def blackbodyEnergyDensity (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellSpectralEnergy m T

theorem blackbodyEnergyDensity_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ blackbodyEnergyDensity T m_UV m_IR :=
  Finset.sum_nonneg (fun m _ => shellSpectralEnergy_nonneg m T hT)

theorem blackbodyEnergyDensity_pos_of_le
    (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) (h : m_UV ≤ m_IR) :
    0 < blackbodyEnergyDensity T m_UV m_IR := by
  unfold blackbodyEnergyDensity
  exact Finset.sum_pos (fun k _ => shellSpectralEnergy_pos k T hT)
    ⟨m_UV, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩

/-- **Cumulative mode budget** `∑ N_m` on the window. -/
noncomputable def cumulativeModeBudget (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellModeMultiplicity m

/-- **Stefan–Boltzmann ceiling:** the finite spectrum is bounded by the
Rayleigh–Jeans envelope `T·∑ N_m` — the bounded, regulator-free replacement for
the divergent continuum `σT⁴` integral. -/
theorem stefanBoltzmann_ceiling (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    blackbodyEnergyDensity T m_UV m_IR ≤ T * cumulativeModeBudget m_UV m_IR := by
  unfold blackbodyEnergyDensity cumulativeModeBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have h := shellSpectralEnergy_lt_RJ m T hT
  have hc : shellModeMultiplicity m * T = T * shellModeMultiplicity m := mul_comm _ _
  linarith

/-! ## Wien displacement: the transition shell

The continuum Wien constant `ω_peak/T ≈ 2.821` is replaced by a clean
**transition-shell theorem**. The transition shell `m*(T) = ⌊1/T⌋ − 1` is the
deepest shell still on the Rayleigh–Jeans side; the next shell is strictly
Wien-side. The displacement ratio is bracketed `1 ≤ ω_{m*}/T < 1 + ω_{m*}`, so
the **HQIV Wien displacement constant is exactly `1`** in Planck units (the
residue `ω_{m*} → 0` as `T → 0`). At the lock-in bath `T = 1/(referenceM+1)` the
transition shell is exactly `referenceM = 4`. -/

/-- **Transition shell index** `m*(T) = ⌊1/T⌋ − 1` (`ℕ`-truncated): the deepest
shell whose frequency `ω_m` is still at least the bath temperature `T`. -/
noncomputable def transitionShellIndex (T : ℝ) : ℕ := Nat.floor (1 / T) - 1

/-- In the cold regime `0 < T ≤ 1`, `m*(T) + 1 = ⌊1/T⌋`. -/
theorem transitionShellIndex_succ_eq_floor (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    transitionShellIndex T + 1 = Nat.floor (1 / T : ℝ) := by
  unfold transitionShellIndex
  have hfloor_pos : 1 ≤ Nat.floor (1 / T : ℝ) := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro h
    have hh : (1 / T : ℝ) < 1 := Nat.floor_eq_zero.mp h
    have : (1 : ℝ) ≤ 1 / T := by rw [le_div_iff₀ hT]; linarith
    linarith
  omega

/-- **Rayleigh–Jeans side:** the transition shell still satisfies `T ≤ ω_{m*}`. -/
theorem transitionShell_RJ_side (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    T ≤ shellOmega (transitionShellIndex T) := by
  rw [shellOmega_eq]
  have key := transitionShellIndex_succ_eq_floor T hT hT_le
  have hcast : ((transitionShellIndex T : ℕ) : ℝ) + 1 =
      (Nat.floor (1 / T : ℝ) : ℝ) := by
    have : ((transitionShellIndex T + 1 : ℕ) : ℝ) =
        (Nat.floor (1 / T : ℝ) : ℝ) := by exact_mod_cast key
    push_cast at this; linarith
  rw [hcast]
  have hfloor_pos : 1 ≤ Nat.floor (1 / T : ℝ) := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro h
    have hh : (1 / T : ℝ) < 1 := Nat.floor_eq_zero.mp h
    have : (1 : ℝ) ≤ 1 / T := by rw [le_div_iff₀ hT]; linarith
    linarith
  have hfloor_pos_real : (0 : ℝ) < (Nat.floor (1 / T : ℝ) : ℝ) := by
    have : (1 : ℝ) ≤ (Nat.floor (1 / T : ℝ) : ℝ) := by exact_mod_cast hfloor_pos
    linarith
  have hfloor_le : (Nat.floor (1 / T : ℝ) : ℝ) ≤ 1 / T := by
    apply Nat.floor_le; positivity
  rw [le_div_iff₀ hfloor_pos_real]
  calc T * (Nat.floor (1 / T : ℝ) : ℝ) ≤ T * (1 / T) :=
        mul_le_mul_of_nonneg_left hfloor_le hT.le
    _ = 1 := by field_simp

/-- **Wien side:** the next shell strictly satisfies `ω_{m*+1} < T`. -/
theorem transitionShell_Wien_side (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    shellOmega (transitionShellIndex T + 1) < T := by
  rw [shellOmega_eq]
  have key := transitionShellIndex_succ_eq_floor T hT hT_le
  have hcast : ((transitionShellIndex T + 1 : ℕ) : ℝ) + 1 =
      (Nat.floor (1 / T : ℝ) : ℝ) + 1 := by
    have : ((transitionShellIndex T + 1 : ℕ) : ℝ) =
        (Nat.floor (1 / T : ℝ) : ℝ) := by exact_mod_cast key
    linarith
  rw [hcast]
  have hbound : (1 / T : ℝ) < (Nat.floor (1 / T : ℝ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloor_plus_one_pos : (0 : ℝ) < (Nat.floor (1 / T : ℝ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (Nat.floor (1 / T : ℝ) : ℝ) := by exact_mod_cast Nat.zero_le _
    linarith
  rw [div_lt_iff₀ hfloor_plus_one_pos]
  have h1 : T * (1 / T) < T * ((Nat.floor (1 / T : ℝ) : ℝ) + 1) :=
    mul_lt_mul_of_pos_left hbound hT
  have h2 : T * (1 / T) = 1 := by field_simp
  linarith

/-- **Wien displacement lower bound:** `1 ≤ ω_{m*}/T`. -/
theorem wienDisplacement_lowerBound (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    1 ≤ shellOmega (transitionShellIndex T) / T := by
  rw [le_div_iff₀ hT, one_mul]
  exact transitionShell_RJ_side T hT hT_le

/-- **Wien displacement upper bound:** `ω_{m*}/T < 1 + ω_{m*}` — so the ratio
tends to `1` as `T → 0`; the HQIV Wien constant is exactly `1`. -/
theorem wienDisplacement_upperBound (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    shellOmega (transitionShellIndex T) / T <
      1 + shellOmega (transitionShellIndex T) := by
  set m := transitionShellIndex T with hm_def
  have hWien : shellOmega (m + 1) < T := transitionShell_Wien_side T hT hT_le
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm2_pos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hWien_eq : shellOmega (m + 1) = 1 / ((m : ℝ) + 2) := by
    rw [shellOmega_eq (m + 1)]; push_cast; ring
  rw [hWien_eq] at hWien
  have h1lt : (1 : ℝ) < T * ((m : ℝ) + 2) := by
    rw [div_lt_iff₀ hm2_pos] at hWien; linarith
  rw [shellOmega_eq m]
  rw [div_div, div_lt_iff₀ (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * T)]
  have hne : ((m : ℝ) + 1) ≠ 0 := ne_of_gt hm1_pos
  field_simp
  nlinarith [h1lt, hm1_pos, hT]

/-- **Symmetric Wien bracket:** `1 ≤ ω_{m*}/T < 1 + ω_{m*}` for `0 < T ≤ 1`. -/
theorem wienDisplacement_bracket (T : ℝ) (hT : 0 < T) (hT_le : T ≤ 1) :
    1 ≤ shellOmega (transitionShellIndex T) / T ∧
      shellOmega (transitionShellIndex T) / T <
        1 + shellOmega (transitionShellIndex T) :=
  ⟨wienDisplacement_lowerBound T hT hT_le, wienDisplacement_upperBound T hT hT_le⟩

/-- **Emission-resonance fixed point.** The Wien transition shell of a bath at
temperature equal to a shell's *own* frequency `ω_m` is exactly that shell:
`transitionShellIndex (ω_m) = m`. So the emission of a bath at scale `ω_m`
localizes on shell `m`, and conversely shell `m` is the unique shell selected by
that scale — the photon-emission reading of "why information lives on shell `m`".
The proton lock-in (`m = referenceM` at `T = 1/5`) is the instance `m = 4`. -/
theorem transitionShellIndex_shellOmega (m : ℕ) :
    transitionShellIndex (shellOmega m) = m := by
  unfold transitionShellIndex shellOmega
  rw [one_div_one_div, show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) from by push_cast; ring,
    Nat.floor_natCast]
  omega

/-- **Lock-in witness:** at the bath `T = ω₄ = 1/(referenceM+1) = 1/5` the
transition shell is exactly `referenceM = 4` — the instance of the
emission-resonance fixed point at the proton anchor. -/
theorem transitionShellIndex_at_referenceM :
    transitionShellIndex (shellOmega referenceM) = referenceM :=
  transitionShellIndex_shellOmega referenceM

/-! ## Stability of the lock-in shell

Why does the proton sit at `referenceM = 4` and stay there? Not by minimising a
binding energy — the binding coupling `latticeSimplexCount(m)·α_eff(m)` *grows*
with `m`. The lock-in is a **resonance/trapping** stability:

* **Emission fits the horizon (no outward drift).** The inverse frequency of
  shell `m` is the integer `m+1` — the outer-horizon radius `R_h(m)`. The emitted
  mode is a standing wave that exactly fills the horizon and carries no net energy
  away, so the radiating shell does not cool itself off its resonance.
* **Resonance fixed point.** Shell `m` is the unique Wien transition shell at its
  own frequency `ω_m` (`transitionShellIndex_shellOmega`).
* **No inward collapse.** The inner shell is strictly hotter (`ω_{m} > ω_{m+1}`):
  collapsing `m+1 → m` requires *absorbing* the frequency gap, forbidden for an
  isolated radiating soliton. For the proton the gap is `ω₃ − ω₄ = 1/20`.

For the proton these three combine into `proton_lockin_stable`. -/

/-- **Horizon / emission count.** `⌊1/ω_m⌋ = m + 1`: the emitted mode's inverse
frequency is exactly the integer outer-horizon radius `R_h(m) = m+1` — a standing,
trapped mode rather than escaping radiation. -/
theorem horizonCount (m : ℕ) : Nat.floor (1 / shellOmega m) = m + 1 := by
  rw [shellOmega, one_div_one_div,
    show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) from by push_cast; ring, Nat.floor_natCast]

/-- **The inner shell is strictly hotter:** `ω_{m+1} < ω_m`. Collapsing inward
raises the frequency, so it costs energy. -/
theorem shellOmega_succ_lt (m : ℕ) : shellOmega (m + 1) < shellOmega m := by
  rw [shellOmega_eq, shellOmega_eq]
  apply one_div_lt_one_div_of_lt
  · have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _; linarith
  · push_cast; linarith

/-- **Photon emission of the proton lock-in shell happens at count `5`**
(= `referenceM + 1`): the proton at shell `4` radiates the mode whose inverse
frequency is the horizon radius `5`. -/
theorem proton_emission_count : Nat.floor (1 / shellOmega referenceM) = 5 := by
  rw [horizonCount]; rfl

/-- **The proton cannot collapse to shell `3` for free:** the inward frequency
gap is `ω₃ − ω₄ = 1/4 − 1/5 = 1/20 > 0`. -/
theorem proton_collapse_gap_eq : shellOmega 3 - shellOmega referenceM = 1 / 20 := by
  rw [shellOmega_eq, shellOmega_eq]; norm_num [referenceM]

/-- **Lock-in stability certificate** for the proton shell `referenceM = 4`:
(1) it is the unique emission-resonance shell at its own frequency;
(2) its photon emission count is the horizon radius `5`;
(3) collapse to the inner shell `3` is gapped by `ω₃ − ω₄ = 1/20 > 0`. -/
theorem proton_lockin_stable :
    transitionShellIndex (shellOmega referenceM) = referenceM ∧
      Nat.floor (1 / shellOmega referenceM) = 5 ∧
      0 < shellOmega 3 - shellOmega referenceM := by
  refine ⟨transitionShellIndex_shellOmega referenceM, proton_emission_count, ?_⟩
  rw [proton_collapse_gap_eq]; norm_num

/-! ## Greybody emissivity from the shell birefringence angle -/

/-- **Per-shell birefringence angle** `β(m) = α·log(m+1)` (`α = 3/5`). Vanishes
at the Planck pole `m = 0`. -/
noncomputable def shellBirefringenceAngle (m : ℕ) : ℝ :=
  alphaEM * Real.log ((m : ℝ) + 1)

theorem shellBirefringenceAngle_zero : shellBirefringenceAngle 0 = 0 := by
  simp [shellBirefringenceAngle]

/-- **E-mode greybody emissivity** `ε(m) = cos²(2β(m))` — the *derived* greybody
coefficient, fixed by the curvature exponent `α`, not an empirical fit. -/
noncomputable def greybodyEmissivity (m : ℕ) : ℝ :=
  (Real.cos (2 * shellBirefringenceAngle m)) ^ 2

/-- **B-mode (cross-channel) greybody emissivity** `ε_B(m) = sin²(2β(m))`. -/
noncomputable def greybodyEmissivityB (m : ℕ) : ℝ :=
  (Real.sin (2 * shellBirefringenceAngle m)) ^ 2

theorem greybodyEmissivity_nonneg (m : ℕ) : 0 ≤ greybodyEmissivity m := sq_nonneg _

theorem greybodyEmissivityB_nonneg (m : ℕ) : 0 ≤ greybodyEmissivityB m := sq_nonneg _

/-- **Greybody completeness** `ε(m) + ε_B(m) = 1` (Pythagorean `cos² + sin²`). -/
theorem greybodyEmissivity_complement (m : ℕ) :
    greybodyEmissivity m + greybodyEmissivityB m = 1 := by
  unfold greybodyEmissivity greybodyEmissivityB
  have h := Real.sin_sq_add_cos_sq (2 * shellBirefringenceAngle m)
  linarith

theorem greybodyEmissivity_le_one (m : ℕ) : greybodyEmissivity m ≤ 1 := by
  have h := greybodyEmissivity_complement m
  have hB := greybodyEmissivityB_nonneg m
  linarith

/-- At the Planck pole the channel is purely E-mode: `ε(0) = 1`. -/
theorem greybodyEmissivity_zero : greybodyEmissivity 0 = 1 := by
  unfold greybodyEmissivity
  rw [shellBirefringenceAngle_zero]; simp

/-- Per-shell **E-mode** spectral energy. -/
noncomputable def shellSpectralEnergyEMode (m : ℕ) (T : ℝ) : ℝ :=
  shellSpectralEnergy m T * greybodyEmissivity m

/-- Per-shell **B-mode** spectral energy. -/
noncomputable def shellSpectralEnergyBMode (m : ℕ) (T : ℝ) : ℝ :=
  shellSpectralEnergy m T * greybodyEmissivityB m

/-- **Birefringence is unitary on the channels:** `u_E + u_B = u` at each shell. -/
theorem shellSpectral_E_plus_B (m : ℕ) (T : ℝ) :
    shellSpectralEnergyEMode m T + shellSpectralEnergyBMode m T =
      shellSpectralEnergy m T := by
  unfold shellSpectralEnergyEMode shellSpectralEnergyBMode
  rw [← mul_add, greybodyEmissivity_complement]; ring

/-- Truncated **E-mode** energy density. -/
noncomputable def blackbodyEnergyDensityEMode (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellSpectralEnergyEMode m T

/-- Truncated **B-mode** energy density. -/
noncomputable def blackbodyEnergyDensityBMode (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc m_UV m_IR, shellSpectralEnergyBMode m T

/-- **Birefringence preserves the total density:** `U_E + U_B = U`. -/
theorem blackbodyEnergyDensity_E_plus_B (T : ℝ) (m_UV m_IR : ℕ) :
    blackbodyEnergyDensityEMode T m_UV m_IR +
        blackbodyEnergyDensityBMode T m_UV m_IR =
      blackbodyEnergyDensity T m_UV m_IR := by
  unfold blackbodyEnergyDensityEMode blackbodyEnergyDensityBMode blackbodyEnergyDensity
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => shellSpectral_E_plus_B m T)

/-! ## Kirchhoff's law (detailed balance) -/

/-- **Equilibrium bundle:** per-shell emission and absorption rates that
coincide on every accessible shell. The detailed-balance hypothesis is carried
as data; we do not derive microscopic cross-sections. -/
structure KirchhoffEquilibrium (m_UV m_IR : ℕ) where
  /-- Emission rate per shell. -/
  emission : ℕ → ℝ
  /-- Absorption rate per shell. -/
  absorption : ℕ → ℝ
  /-- Detailed balance on the accessible window. -/
  emission_eq_absorption :
    ∀ m, m_UV ≤ m → m ≤ m_IR → emission m = absorption m

/-- **Kirchhoff's law:** at equilibrium, emissivity equals absorptivity at every
accessible shell (measured against the same shell spectral-energy reference). -/
theorem kirchhoff_emissivity_eq_absorptivity
    (T : ℝ) (m_UV m_IR : ℕ) (K : KirchhoffEquilibrium m_UV m_IR) (m : ℕ)
    (hl : m_UV ≤ m) (hr : m ≤ m_IR) :
    K.emission m / shellSpectralEnergy m T =
      K.absorption m / shellSpectralEnergy m T := by
  rw [K.emission_eq_absorption m hl hr]

/-- **Canonical equilibrium witness:** the Planck spectrum itself is in detailed
balance — emission and absorption both equal `u_m(T)`. -/
noncomputable def planckSpectrumEquilibrium (T : ℝ) (m_UV m_IR : ℕ) :
    KirchhoffEquilibrium m_UV m_IR where
  emission := fun m => shellSpectralEnergy m T
  absorption := fun m => shellSpectralEnergy m T
  emission_eq_absorption := by intros; rfl

/-- **Cumulative detailed balance:** total emission equals total absorption over
the accessible window. -/
theorem kirchhoff_cumulative_balance
    (m_UV m_IR : ℕ) (K : KirchhoffEquilibrium m_UV m_IR) :
    ∑ m ∈ Finset.Icc m_UV m_IR, K.emission m =
      ∑ m ∈ Finset.Icc m_UV m_IR, K.absorption m := by
  apply Finset.sum_congr rfl
  intro m hm
  rcases Finset.mem_Icc.mp hm with ⟨ha, hb⟩
  exact K.emission_eq_absorption m ha hb

/-! ## Photon-gas thermodynamics -/

/-- **Radiation pressure** for the massless photon gas: `P = U/3`. -/
noncomputable def radiationPressure (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  blackbodyEnergyDensity T m_UV m_IR / 3

theorem radiationPressure_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ radiationPressure T m_UV m_IR :=
  div_nonneg (blackbodyEnergyDensity_nonneg T m_UV m_IR hT) (by norm_num)

/-- Photon-gas equation of state `U = 3P`. -/
theorem energyDensity_eq_three_pressure (T : ℝ) (m_UV m_IR : ℕ) :
    blackbodyEnergyDensity T m_UV m_IR = 3 * radiationPressure T m_UV m_IR := by
  unfold radiationPressure; ring

/-- **Entropy density** of the photon gas: `s = (4/3)·U/T`. -/
noncomputable def entropyDensity (T : ℝ) (m_UV m_IR : ℕ) : ℝ :=
  (4 / 3 : ℝ) * blackbodyEnergyDensity T m_UV m_IR / T

theorem entropyDensity_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ entropyDensity T m_UV m_IR := by
  unfold entropyDensity
  exact div_nonneg
    (mul_nonneg (by norm_num) (blackbodyEnergyDensity_nonneg T m_UV m_IR hT))
    (le_of_lt hT)

/-- Photon-gas Euler identity `T·s = (4/3)·U`. -/
theorem T_times_entropy_eq (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    T * entropyDensity T m_UV m_IR =
      (4 / 3 : ℝ) * blackbodyEnergyDensity T m_UV m_IR := by
  unfold entropyDensity
  field_simp

end

end HqivSpine.Physics
