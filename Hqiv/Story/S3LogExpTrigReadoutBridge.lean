import Hqiv.Story.S3StripRollingProjection
import Hqiv.Story.S3ExplicitFormulaDualitySlot
import Hqiv.Story.DimensionalGrowthAnalyticScaffold
import Hqiv.Story.S3HarmonicPrimeZetaPath
import Hqiv.Story.S3ClosureDeltaLiftBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Log/exp arithmetic ↔ SO(4) trig readout bridge

Prime-counting and Chebyshev data live in **log/exp** language (`Λ(p)=log p`,
`exp(∑ -log(1-p^{-s}))`, explicit-formula powers `x^ρ`).  The SO(4) zeta readout
lives in **trig** language (`sin/cos`, `e^{it}`, quarter-turn phases).

This module packages the proved translation dictionary in one place:

1. **Critical-line powers** — `x^{1/2+iγ}` as `√x · exp(iγ log x)` with real
   cos/sin readout;
2. **Prime explicit term ↔ rolling twiddle** — von Mangoldt log weights paired
   with the S³ Fourier twiddle amplitude;
3. **Harmonic + log curvature → `S¹` phase** — `K(n)=H_n+α·∑(log i)/i` feeds a
   certified `UnitCirclePhaseReadout`.

No new analytic input is introduced.  The bridge identifies layers that were
already proved across `S3HarmonicPrimeZetaPath`, `S3StripRollingProjection`,
`S3ExplicitFormulaIdentity`, and `DimensionalGrowthAnalyticScaffold`.
-/

namespace Hqiv.Story

open Complex Real ArithmeticFunction
open scoped ComplexConjugate

noncomputable section

/-! ## §1 Critical-line log/exp power → trig oscillation -/

/-- Critical-line zero exponent `ρ = 1/2 + iγ`. -/
noncomputable def criticalLineExponent (γ : ℝ) : ℂ :=
  (1 / 2 : ℂ) + γ * I

theorem criticalLineExponent_re (γ : ℝ) :
    (criticalLineExponent γ).re = (1 / 2 : ℝ) := by
  simp [criticalLineExponent]

theorem criticalLineExponent_im (γ : ℝ) :
    (criticalLineExponent γ).im = γ := by
  simp [criticalLineExponent]

/-- Phase coordinate `γ log x` for the explicit-formula zero oscillation. -/
noncomputable def zeroOscillationPhase (γ x : ℝ) : ℝ :=
  γ * Real.log x

/-- Unit-circle phase factor `exp(i γ log x)` (the trig image of the log channel). -/
noncomputable def zeroOscillationUnitPhase (γ x : ℝ) : ℂ :=
  exp (I * (zeroOscillationPhase γ x))

theorem zeroOscillationUnitPhase_on_circle (γ x : ℝ) :
    ‖zeroOscillationUnitPhase γ x‖ = 1 :=
  norm_exp_I_mul_ofReal (zeroOscillationPhase γ x)

theorem zeroOscillationUnitPhase_re (γ x : ℝ) :
    (zeroOscillationUnitPhase γ x).re = Real.cos (zeroOscillationPhase γ x) := by
  rw [zeroOscillationUnitPhase, mul_comm I, exp_ofReal_mul_I_re]

theorem zeroOscillationUnitPhase_im (γ x : ℝ) :
    (zeroOscillationUnitPhase γ x).im = Real.sin (zeroOscillationPhase γ x) := by
  rw [zeroOscillationUnitPhase, mul_comm I, exp_ofReal_mul_I_im]

/--
For `x > 0`, the explicit-formula power factors into a real amplitude and a
unit-circle trig phase:

`x^{1/2+iγ} = √x · exp(i γ log x)`.
-/
theorem cpow_critical_line_trig_decomposition {x γ : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ criticalLineExponent γ =
      (Real.sqrt x : ℂ) * zeroOscillationUnitPhase γ x := by
  unfold criticalLineExponent zeroOscillationUnitPhase zeroOscillationPhase
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hadd :
      (1 / 2 : ℂ) + γ * I = ((1 / 2 : ℝ) : ℂ) + (γ * I) := by
    push_cast; ring_nf
  rw [hadd, Complex.cpow_add _ _ hx']
  have hsqrt :
      (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) = (Real.sqrt x : ℂ) := by
    rw [← Complex.ofReal_cpow (le_of_lt hx), Real.sqrt_eq_rpow]
  have hosc :
      (x : ℂ) ^ (γ * I) = exp (I * (γ * Real.log x)) := by
    rw [Complex.cpow_def_of_ne_zero hx', Complex.ofReal_log (le_of_lt hx)]
    congr 1
    ring_nf
  rw [hsqrt, hosc]
  congr 1
  rw [Complex.ofReal_mul]

/--
Trig decomposition of the critical-line power: real amplitude `√x` times
`cos(γ log x) + i sin(γ log x)`.
-/
theorem cpow_critical_line_cos_sin_decomposition {x γ : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ criticalLineExponent γ =
      (Real.sqrt x : ℂ) *
        (Real.cos (zeroOscillationPhase γ x) + Real.sin (zeroOscillationPhase γ x) * I) := by
  rw [cpow_critical_line_trig_decomposition hx, zeroOscillationUnitPhase,
    exp_eq_exp_re_mul_sin_add_cos]
  simp [zeroOscillationPhase]

/-! ## §2 Prime log weights ↔ rolling Fourier twiddle -/

/--
Prime-side / rolling-twiddle pairing at height `t`.

The log-weighted explicit-formula term uses `Λ(n)`; the SO(4) survivor amplitude
is the rolled 45° projection; the twiddle multiplies it by `e^{it}`.
-/
structure PrimeLogTrigRollingSlot (t : ℝ) where
  survivor_amp : ℝ
  amp_eq : survivor_amp = criticalProj (stripRollingMap t)
  prime_log_term : ℝ
  prime_log_term_eq : prime_log_term = primeExplicitTerm 2 (fun _ => survivor_amp)
  twiddle : ℂ
  twiddle_eq : twiddle = rollingFourierTwiddle t
  prime_term_ne_zero_iff_amp_ne_zero :
    prime_log_term ≠ 0 ↔ survivor_amp ≠ 0

/-- Canonical pairing induced by the strip rolling map at height `t`. -/
noncomputable def primeLogTrigRollingSlot (t : ℝ) : PrimeLogTrigRollingSlot t where
  survivor_amp := criticalProj (stripRollingMap t)
  amp_eq := rfl
  prime_log_term := primeExplicitTerm 2 (fun _ => criticalProj (stripRollingMap t))
  prime_log_term_eq := rfl
  twiddle := rollingFourierTwiddle t
  twiddle_eq := rfl
  prime_term_ne_zero_iff_amp_ne_zero := by
    constructor
    · intro hterm hamp
      rw [hamp] at hterm
      dsimp [primeExplicitTerm] at hterm
      have h1 : (1 : ℕ) ≤ 2 := by norm_num
      rw [Finset.sum_Icc_succ_top h1] at hterm
      have hhead :
          ∑ k ∈ Finset.Icc 1 1, vonMangoldt k * (0 : ℝ) = 0 := by
        rw [Finset.Icc_self, Finset.sum_singleton, vonMangoldt_one_eq_zero, zero_mul]
      rw [hhead, zero_add, show (1 + 1 : ℕ) = 2 by norm_num, mul_zero] at hterm
      exact hterm rfl
    · intro hamp hterm
      exact rolling_survivor_forces_prime_explicit_term t hamp hterm

/--
The twiddle carries the same survivor amplitude as the prime log term, rotated
by the unit phase `exp(it)`.
-/
theorem prime_log_trig_twiddle_factor (t : ℝ) :
    rollingFourierTwiddle t =
      exp (I * t) * (criticalProj (stripRollingMap t) : ℂ) := by
  simp [rollingFourierTwiddle, mul_comm I]

theorem prime_log_term_eq_vonMangoldt_times_amp (t : ℝ) :
    (primeLogTrigRollingSlot t).prime_log_term =
      vonMangoldt 2 * criticalProj (stripRollingMap t) := by
  dsimp [primeLogTrigRollingSlot, PrimeLogTrigRollingSlot.mk, primeExplicitTerm]
  have h1 : (1 : ℕ) ≤ 2 := by norm_num
  rw [Finset.sum_Icc_succ_top h1]
  have hhead :
      ∑ k ∈ Finset.Icc 1 1, vonMangoldt k * criticalProj (stripRollingMap t) = 0 := by
    rw [Finset.Icc_self, Finset.sum_singleton, vonMangoldt_one_eq_zero, zero_mul]
  rw [hhead, zero_add, show (1 + 1 : ℕ) = 2 by norm_num]

/-! ## §3 Harmonic + log curvature channel → unit-circle phase -/

/--
Curvature shell phase: cumulative harmonic+log growth `K(n)` mapped to `S¹` via
`exp(i·K(n))`.  The angle grows (non-periodic cumulative readout), but every
value lies on the unit circle.
-/
noncomputable def curvatureHarmonicLogPhaseReadout : UnitCirclePhaseReadout where
  u := fun n => exp (I * (Hqiv.curvature_integral n))
  onCircle := fun n => norm_exp_I_mul_ofReal (Hqiv.curvature_integral n)

/-- Fractional part of the curvature shell index (quarter-turn chart input). -/
noncomputable def curvaturePhaseFraction (n : ℕ) : ℝ :=
  Int.fract (Hqiv.curvature_integral n)

/--
Quarter-turn phase readout: fractional part of `K(n)` scaled to `[0,2π)`.
This is the discrete trig chart used by the Python quarter-orbit probes.
-/
noncomputable def curvatureQuarterTurnPhaseReadout : UnitCirclePhaseReadout where
  u := fun n => exp (I * ↑(2 * Real.pi * curvaturePhaseFraction n))
  onCircle := fun n =>
    norm_exp_I_mul_ofReal (2 * Real.pi * curvaturePhaseFraction n)

/--
Harmonic-only shell phase readout at `exp(i·H_n)`.
-/
noncomputable def harmonicShellPhaseReadout : UnitCirclePhaseReadout where
  u := fun n => exp (I * (harmonicPartialSum n))
  onCircle := fun n => norm_exp_I_mul_ofReal (harmonicPartialSum n)

/-- Curvature phase factors into harmonic and log channels on `S¹`. -/
theorem curvature_shell_phase_factors_harmonic_log (n : ℕ) :
    exp (I * (Hqiv.curvature_integral n)) =
      exp (I * (harmonicPartialSum n)) *
        exp (I * (Hqiv.alpha * Hqiv.logWeightedSum n)) := by
  rw [← Complex.exp_add]
  congr 1
  rw [curvature_integral_harmonic_log_split n, Complex.ofReal_add, mul_add,
    Complex.ofReal_mul, harmonicPartialSum]

/-- The certified curvature phase readout uses the harmonic+log angle split. -/
theorem curvatureHarmonicLogPhaseReadout_u_eq (n : ℕ) :
    curvatureHarmonicLogPhaseReadout.u n = exp (I * (Hqiv.curvature_integral n)) :=
  rfl

/-! ## §4 Master bridge packaging -/

/--
The log/exp ↔ trig readout bridge.

All three fields are populated from proved definitions; no analytic capstone is
assumed.
-/
structure LogExpTrigReadoutBridge where
  /-- Critical-line powers decompose into `√x` and `exp(iγ log x)`. -/
  cpow_trig :
    ∀ {x γ : ℝ}, 0 < x →
      (x : ℂ) ^ criticalLineExponent γ =
        (Real.sqrt x : ℂ) * zeroOscillationUnitPhase γ x
  /-- Curvature shell phases factor through harmonic + log channels. -/
  curvature_factors :
    ∀ n : ℕ,
      exp (I * (Hqiv.curvature_integral n)) =
        exp (I * (harmonicPartialSum n)) *
          exp (I * (Hqiv.alpha * Hqiv.logWeightedSum n))
  /-- Prime log explicit term pairs with the rolling twiddle amplitude. -/
  prime_twiddle :
    ∀ t : ℝ,
      (primeLogTrigRollingSlot t).prime_log_term =
        vonMangoldt 2 * criticalProj (stripRollingMap t)

/-- Canonical bridge instance from the proved theorems above. -/
noncomputable def logExpTrigReadoutBridge : LogExpTrigReadoutBridge where
  cpow_trig := fun hx => cpow_critical_line_trig_decomposition hx
  curvature_factors := curvature_shell_phase_factors_harmonic_log
  prime_twiddle := prime_log_term_eq_vonMangoldt_times_amp

end

end Hqiv.Story
