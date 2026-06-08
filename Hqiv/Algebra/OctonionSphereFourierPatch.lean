import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic

import Hqiv.Algebra.OctonionSphereFourierAxis

/-!
# Parameterized “Fourier patch” concentration (DFT-style peak on a finite window)

Discrete **window** `w` and **kernel** `κ` on `Fin n` are paired with the shell phasor
`exp(i · θ_m · j)` where `θ_m = intrinsicShellAxisAngle m` and `j` steps along the patch index.

When **`Ω m = k`**, `θ_m` agrees with the narrative **`π/(2k)` axis** (`axisAngle k`); see
`fourierPatchPeakCorrelation_eq_axisAngle`.

**Moiré / patch score (discrete):** the downstream story looks for a **step change in slope** of a
real score along the **ordered patch index** `j` — first difference `S(j+1)−S(j)` as discrete slope,
then change in that slope (second difference on interior indices). **Patch search** is this
**one-dimensional** moiré–cusp story (`Hqiv.Archive.Algebra.MoireCuspBracket`, threshold/BST layer in
`Hqiv.Archive.Algebra.MoireToyThresholdSearch`);
see `moirePatchScoreSlope` and `moirePatchSlopeStep`. There is no separate “quantum ray” or auxiliary
2D vector search in that pipeline.

**`fourier_patch_concentration`** bundles a **peak magnitude** and **side-lobe** bounds once those
inequalities are supplied (typically from character orthogonality on `ℤ/nℤ` for the harmonic kernel,
plus radial decay of `w`). The proof is definitional (`⟨hpeak, hside⟩`).

**`sum_exp_two_pi_int_mul_fin_eq_zero`:** proves the geometric series
`∑_{j<n} exp(2π i d j / n) = 0` when `n ∤ d` (geometric sum of a nontrivial `n`-th root of unity).

For Mathlib’s abstract additive-character viewpoint, compare `AddChar.sum_eq_zero_of_ne_one` in
`Mathlib.NumberTheory.LegendreSymbol.AddCharacter`.
-/

noncomputable section

open scoped ArithmeticFunction.Omega BigOperators
open ArithmeticFunction Finset

namespace Hqiv.Algebra

variable {n : ℕ}

/-- Peak-mode correlation: window × kernel × intrinsic-shell phasor at index `j`. -/
noncomputable def fourierPatchPeakCorrelation (m : ℕ) (hm : 1 < m) (w κ : Fin n → ℂ) : ℂ :=
  ∑ j : Fin n,
    w j * Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm * (j.val : ℝ))) * κ j

/-- Side-mode correlation at arity `k'` (comparison modes use `axisAngle k'`, not `intrinsicShellAxisAngle`). -/
noncomputable def fourierPatchSideCorrelation (k' : ℕ) (hk' : 0 < k') (w κ : Fin n → ℂ) : ℂ :=
  ∑ j : Fin n, w j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * κ j

/-- When `Ω m = k`, the peak sum uses the same phasor as the `π/(2k)` axis. -/
theorem fourierPatchPeakCorrelation_eq_axisAngle (_hn : 0 < n) (m : ℕ) (hm : 1 < m) (k : ℕ)
    (hk : 0 < k) (hΩ : Ω m = k) (w κ : Fin n → ℂ) :
    fourierPatchPeakCorrelation m hm w κ =
      ∑ j : Fin n, w j * Complex.exp (Complex.I * (axisAngle k hk * (j.val : ℝ))) * κ j := by
  dsimp [fourierPatchPeakCorrelation]
  refine Finset.sum_congr rfl ?_
  intro j _
  congr 2
  rw [intrinsicShellAxisAngle_eq_axisAngle_of_Omega hm hk hΩ]

/-- Scaffold: window is real and nonnegative (radial projection onto the patch — refine later). -/
structure WindowIsRadialProjection (w : Fin n → ℂ) : Prop where
  real_nonneg : ∀ j : Fin n, (w j).im = 0 ∧ 0 ≤ (w j).re

/-- Scaffold: kernel matches the length-`n` harmonic character at frequency `k` (DFT twiddle). -/
structure KernelIsHarmonic (hn : 0 < n) (k : ℕ) (κ : Fin n → ℂ) : Prop where
  is_char :
    ∀ j : Fin n,
      κ j = Complex.exp ((2 * Real.pi * Complex.I * (k * j.val : ℂ)) / (n : ℂ))

/-- Harmonic characters are unimodular (`‖κ j‖ = 1`). -/
lemma KernelIsHarmonic.norm_eq_one {n : ℕ} (hn : 0 < n) (k : ℕ) (κ : Fin n → ℂ)
    (hκ : KernelIsHarmonic hn k κ) (j : Fin n) : ‖κ j‖ = 1 := by
  rw [hκ.is_char j, Complex.norm_exp]
  have hz : (2 * Real.pi * Complex.I * (k * j.val : ℂ)).re = 0 := by
    simp [mul_assoc, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
  have hre : ((2 * Real.pi * Complex.I * (k * j.val : ℂ)) / (n : ℂ)).re = 0 := by
    rw [Complex.div_natCast_re, hz]
    simp
  rw [hre, Real.exp_zero]

/-- Expand `κ j` as the length-`n` DFT twiddle at frequency `k` (harmonic kernel). -/
lemma fourierPatchSideCorrelation_with_kernel_expanded {n : ℕ} (hn : 0 < n) (k k' : ℕ) (hk' : 0 < k')
    (w κ : Fin n → ℂ) (hκ : KernelIsHarmonic hn k κ) :
    fourierPatchSideCorrelation k' hk' w κ =
      ∑ j : Fin n,
        w j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) *
          Complex.exp ((2 * Real.pi * Complex.I * (k * j.val : ℂ)) / (n : ℂ)) := by
  dsimp [fourierPatchSideCorrelation]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hκ.is_char j]

/-- Side-lobe bound: all non-`k` arity correlations are small relative to `maxCoeff`. -/
def OtherCoeffsSmall (k : ℕ) (w κ : Fin n → ℂ) (ε maxCoeff : ℝ) : Prop :=
  ∀ (k' : ℕ) (hk' : 0 < k'), k' ≠ k →
    ‖fourierPatchSideCorrelation k' hk' w κ‖ ≤ ε * maxCoeff

/-- Combined patch concentration target (peak = `maxCoeff`, off-peak ≤ `ε * maxCoeff`). -/
structure FourierPatchConcentration (hn : 0 < n) (m : ℕ) (hm : 1 < m) (k : ℕ)
    (w κ : Fin n → ℂ) (maxCoeff ε : ℝ) : Prop where
  peak_eq : ‖fourierPatchPeakCorrelation m hm w κ‖ = maxCoeff
  others : OtherCoeffsSmall k w κ ε maxCoeff

/-!
### Packaging (quantitative bounds as hypotheses)

Once `hpeak` and `hside` are established — e.g. from **character orthogonality**
(`sum_exp_two_pi_int_mul_fin_eq_zero` on the kernel factors) together with **radial decay** of `w` —
this bundles them into `FourierPatchConcentration`.
-/

/-- Bundle peak and side-lobe data into `FourierPatchConcentration`.

**Proof:** by definition; orthogonality enters only through the hypotheses `hpeak` / `hside`, which
in applications follow from `sum_exp_two_pi_int_mul_fin_eq_zero` (geometric series on roots of unity)
and window decay. -/
theorem fourier_patch_concentration {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : 1 < m) (k : ℕ) (_hk : 0 < k)
    (_hΩ : Ω m = k) (window kernel : Fin n → ℂ)
    (_hwin : WindowIsRadialProjection window)
    (_hker : KernelIsHarmonic hn k kernel)
    (maxCoeff ε : ℝ) (_hε : 0 < ε)
    (hpeak : ‖fourierPatchPeakCorrelation m hm window kernel‖ = maxCoeff)
    (hside :
      ∀ (k' : ℕ) (hk' : 0 < k'), k' ≠ k →
        ‖fourierPatchSideCorrelation k' hk' window kernel‖ ≤ ε * maxCoeff) :
    FourierPatchConcentration hn m hm k window kernel maxCoeff ε :=
  ⟨hpeak, hside⟩

/-- Backward-compatible name for the packaging lemma. -/
theorem fourier_patch_concentration_of_bounds (hn : 0 < n) (m : ℕ) (hm : 1 < m) (k : ℕ)
    (w κ : Fin n → ℂ) (maxCoeff ε : ℝ)
    (hpeak : ‖fourierPatchPeakCorrelation m hm w κ‖ = maxCoeff)
    (hside :
      ∀ (k' : ℕ) (hk' : 0 < k'), k' ≠ k →
        ‖fourierPatchSideCorrelation k' hk' w κ‖ ≤ ε * maxCoeff) :
    FourierPatchConcentration hn m hm k w κ maxCoeff ε :=
  ⟨hpeak, hside⟩

/-!
### Discrete moiré score: slope and step-change along `Fin n`

A **real** score on patch indices models moiré / tomography. The **search narrative** targets a
**transition** where the discrete **slope** changes (first difference jumps), not alignment with a
fixed pair of directions in `ℝ²` alone.

* `moirePatchScoreSlope` — edge slope `S(j+1) − S(j)`.
* `moirePatchSlopeStep` — interior **change in slope** (second difference of `S`).

A global score built from `‖fourierPatchPeakCorrelation‖` or a real part is **not** fixed here; only
the discrete calculus on `Fin n → ℝ`.
-/

/-- Real-valued score sampled along patch indices (moiré / tomographic proxy). -/
abbrev MoirePatchScore (n : ℕ) :=
  Fin n → ℝ

/-- Discrete slope on the edge from `j` to `j+1` (first difference along the patch). -/
noncomputable def moirePatchScoreSlope {n : ℕ} (hn : 1 < n) (S : MoirePatchScore n) (j : Fin (n - 1)) :
    ℝ :=
  S ⟨j.val + 1, by omega⟩ - S ⟨j.val, by omega⟩

/-- Change in discrete slope at an interior pair of edges (`j : Fin (n-2)` indexes a step in slope). -/
noncomputable def moirePatchSlopeStep {n : ℕ} (hn : 2 < n) (S : MoirePatchScore n) (j : Fin (n - 2)) :
    ℝ :=
  let hn1 : 1 < n := by omega
  moirePatchScoreSlope hn1 S ⟨j.val + 1, by omega⟩ - moirePatchScoreSlope hn1 S ⟨j.val, by omega⟩

theorem moirePatchScoreSlope_const {n : ℕ} (hn : 1 < n) (c : ℝ) (j : Fin (n - 1)) :
    moirePatchScoreSlope hn (fun _ : Fin n => c) j = 0 := by
  simp [moirePatchScoreSlope]

theorem moirePatchScoreSlope_affine {n : ℕ} (hn : 1 < n) (a b : ℝ) (j : Fin (n - 1)) :
    moirePatchScoreSlope hn (fun i : Fin n => a * (i.val : ℝ) + b) j = a := by
  dsimp [moirePatchScoreSlope]
  simp [Nat.cast_add, Nat.cast_one]
  ring

theorem moirePatchSlopeStep_affine {n : ℕ} (hn : 2 < n) (a b : ℝ) (j : Fin (n - 2)) :
    moirePatchSlopeStep hn (fun i : Fin n => a * (i.val : ℝ) + b) j = 0 := by
  have hn1 : 1 < n := by omega
  dsimp [moirePatchSlopeStep]
  rw [moirePatchScoreSlope_affine hn1 a b ⟨j.val + 1, by omega⟩,
    moirePatchScoreSlope_affine hn1 a b ⟨j.val, by omega⟩]
  ring

/-!
### Peak calibration

To use `fourierPatchSideCorrelation_bound_from_orthogonality` one needs `(n : ℝ) ≤ maxCoeff`.  This does
not follow from `fourierPatchPeakCorrelation_eq_axisAngle`, but it **does** follow if the peak magnitude
is `maxCoeff` and is bounded below by `n` (e.g. from a separate physical / modeling argument).
-/

/-- If `‖peak‖ = maxCoeff` and `n ≤ ‖peak‖`, then `n ≤ maxCoeff`. -/
theorem maxCoeff_ge_n_of_peak_eq_and_peak_norm_ge {n : ℕ} {m : ℕ} {hm : 1 < m} (w κ : Fin n → ℂ)
    (maxCoeff : ℝ)
    (hpeak : ‖fourierPatchPeakCorrelation m hm w κ‖ = maxCoeff)
    (hge : (n : ℝ) ≤ ‖fourierPatchPeakCorrelation m hm w κ‖) :
    (n : ℝ) ≤ maxCoeff := by
  rw [← hpeak]
  exact hge

/-- Triangle inequality: peak correlation is bounded by the sum of window norms (phasor and kernel are unimodular). -/
lemma norm_fourierPatchPeakCorrelation_le_sum_norm_window {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : 1 < m) (k : ℕ)
    (w κ : Fin n → ℂ) (hκ : KernelIsHarmonic hn k κ) :
    ‖fourierPatchPeakCorrelation m hm w κ‖ ≤ ∑ j : Fin n, ‖w j‖ := by
  dsimp [fourierPatchPeakCorrelation]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro j _
  have hex :
      ‖Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm * (j.val : ℝ)))‖ = 1 := by
    simpa [Complex.ofReal_mul, mul_assoc] using
      complex_exp_mul_I_real_unit (intrinsicShellAxisAngle m hm * (j.val : ℝ))
  have hk1 : ‖κ j‖ = 1 := KernelIsHarmonic.norm_eq_one hn k κ hκ j
  calc
    ‖w j * Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm * (j.val : ℝ))) * κ j‖
        ≤ ‖w j * Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm * (j.val : ℝ)))‖ * ‖κ j‖ :=
      norm_mul_le _ _
    _ ≤ (‖w j‖ * ‖Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm * (j.val : ℝ)))‖) * ‖κ j‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖w j‖ := by rw [hex, hk1, mul_one, mul_one]

/-!
### Character orthogonality (geometric series on `Fin n`)
-/

/-- Geometric sum of `n`-th roots of unity along `exp(2π i d j / n)` vanishes when `n` does not divide `d`. -/
theorem sum_exp_two_pi_int_mul_fin_eq_zero (n : ℕ) (hn : 0 < n) {d : ℤ} (hd : ¬(n : ℤ) ∣ d) :
    (∑ j : Fin n,
        Complex.exp ((2 * Real.pi * Complex.I * (d * (j.val : ℤ) : ℂ)) / (n : ℂ))) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  set ζ : ℂ := Complex.exp ((2 * Real.pi * Complex.I * (d : ℂ)) / (n : ℂ))
  have hmul :
      (n : ℂ) * ((2 * Real.pi * Complex.I * (d : ℂ)) / (n : ℂ)) = (d : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp [hn0]
  have hterm (j : Fin n) :
      Complex.exp ((2 * Real.pi * Complex.I * (d * (j.val : ℤ) : ℂ)) / (n : ℂ)) = ζ ^ j.val := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul ((2 * Real.pi * Complex.I * (d : ℂ)) / (n : ℂ)) j.val]
    refine congrArg Complex.exp ?_
    push_cast
    field_simp [hn0]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  rw [Fin.sum_univ_eq_sum_range (fun i => ζ ^ i) n]
  have hζn : ζ ^ n = 1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul ((2 * Real.pi * Complex.I * (d : ℂ)) / (n : ℂ)) n, hmul]
    exact Complex.exp_int_mul_two_pi_mul_I d
  have hζ1 : ζ ≠ 1 := by
    intro h1
    have hex : Complex.exp ((2 * Real.pi * Complex.I * (d : ℂ)) / (n : ℂ)) = 1 := by simpa [ζ] using h1
    rcases (Complex.exp_eq_one_iff).mp hex with ⟨m, hm⟩
    have hnz : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    have hdiv : (d : ℂ) / (n : ℂ) = (m : ℂ) := by
      apply_fun (fun z : ℂ => z / (2 * Real.pi * Complex.I)) at hm
      field_simp [hnz] at hm ⊢
      exact hm
    have hdn : (d : ℂ) = (n : ℂ) * (m : ℂ) := by
      simpa [mul_comm] using (div_eq_iff hn0).1 hdiv
    have hdvd : (n : ℤ) ∣ d := by
      refine ⟨m, ?_⟩
      rw [← Int.cast_inj (α := ℂ), hdn]
      simp [Int.cast_mul, Int.cast_natCast]
    exact hd hdvd
  rw [geom_sum_eq hζ1 n, hζn, sub_self, zero_div]

/-!
### Bridge: intrinsic shell phasor ↔ `π/(2k)` axis (and orthogonality packaging)

The **additive character** used in `KernelIsHarmonic` is `j ↦ exp(2π i k j / n)` (DFT twiddle).
The **patch story** uses `axisAngle k = π/(2k)` in `fourierPatchSideCorrelation`. These are not the same
function of `j`; the lemmas below identify the **shell** phasor with the narrative `π/(2k)` axis once
`Ω m = k`. Relating that axis to `2π j / n` is a separate scale/frequency identification (depends on
how `n` is chosen relative to `k`).
-/

/-- Under `Ω m = k`, the intrinsic polar phasor agrees with the `axisAngle k` phasor (`π/(2k)`). -/
lemma intrinsicShellAxisAngle_phasor_eq_axisAngle_phasor {n : ℕ} (m : ℕ) (hm : 1 < m) (k : ℕ)
    (hk : 0 < k) (hΩ : Ω m = k) (j : Fin n) :
    Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm * (j.val : ℝ))) =
      Complex.exp (Complex.I * (axisAngle k hk * (j.val : ℝ))) := by
  apply congrArg Complex.exp
  rw [intrinsicShellAxisAngle_eq_axisAngle_of_Omega hm hk hΩ]

/-- Same bridge with `π/(2k)` written explicitly (unfolding `axisAngle`). -/
lemma intrinsicShellAxisAngle_phasor_eq_pi_div_two_k_mul_j {n : ℕ} (m : ℕ) (hm : 1 < m) (k : ℕ)
    (hk : 0 < k) (hΩ : Ω m = k) (j : Fin n) :
    Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm * (j.val : ℝ))) =
      Complex.exp (Complex.I * ((Real.pi / (2 * (k : ℝ))) * (j.val : ℝ))) := by
  rw [intrinsicShellAxisAngle_eq_axisAngle_of_Omega hm hk hΩ]
  congr 1
  simp [axisAngle]

/-- Off-peak **shell** phasor: if `Ω m = k'` then the intrinsic angle is `π/(2k')` (same as `axisAngle k'`).

**Naming note:** this is the narrative arity-axis phasor, *not* the length-`n` DFT twiddle
`exp(2π i · j / n)` from `KernelIsHarmonic`. Linking those frequencies is extra calibration. -/
lemma intrinsicShellAxisAngle_phasor_eq_pi_div_two_k'_mul_j_of_Omega {n : ℕ} (m : ℕ) (hm : 1 < m) (k' : ℕ)
    (hk' : 0 < k') (hΩ' : Ω m = k') (j : Fin n) :
    Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm * (j.val : ℝ))) =
      Complex.exp (Complex.I * ((Real.pi / (2 * (k' : ℝ))) * (j.val : ℝ))) := by
  rw [intrinsicShellAxisAngle_eq_axisAngle_of_Omega hm hk' hΩ']
  congr 1
  simp [axisAngle]

/-- Alias for the narrative “DFT-style” wording in notes: still the `π/(2k')` axis, not the `2π j / n` twiddle. -/
theorem intrinsicShellAxisAngle_phasor_eq_dft_character {n : ℕ} (m : ℕ) (hm : 1 < m) (k' : ℕ)
    (hk' : 0 < k') (hΩ' : Ω m = k') (j : Fin n) :
    Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm * (j.val : ℝ))) =
      Complex.exp (Complex.I * ((Real.pi / (2 * (k' : ℝ))) * (j.val : ℝ))) :=
  intrinsicShellAxisAngle_phasor_eq_pi_div_two_k'_mul_j_of_Omega m hm k' hk' hΩ' j

/-- Side correlation with the arity phasor written as `π/(2k')` (unfold `axisAngle`).

This is definitionally the same sum as `fourierPatchSideCorrelation`; there is no `intrinsicShellAxisAngle`
in the side-mode definition. -/
theorem fourierPatchSideCorrelation_rewrite_as_dft {n : ℕ} (_hn : 0 < n) (k' : ℕ) (hk' : 0 < k')
    (w κ : Fin n → ℂ) :
    fourierPatchSideCorrelation k' hk' w κ =
      ∑ j : Fin n, w j * Complex.exp (Complex.I * ((Real.pi / (2 * (k' : ℝ))) * (j.val : ℝ))) * κ j := by
  simp [fourierPatchSideCorrelation, axisAngle, mul_assoc]

/-- Convenience: orthogonality for frequency difference `k - k'` (as an integer shift). -/
theorem sum_exp_two_pi_int_mul_fin_eq_zero_sub {n : ℕ} (hn : 0 < n) {k k' : ℕ}
    (hd : ¬(n : ℤ) ∣ ((k : ℤ) - (k' : ℤ))) :
    (∑ j : Fin n,
        Complex.exp ((2 * Real.pi * Complex.I * (((k : ℤ) - (k' : ℤ)) * (j.val : ℤ) : ℂ)) / (n : ℂ))) =
      0 := by
  simpa using sum_exp_two_pi_int_mul_fin_eq_zero (n := n) hn hd

/-!
### Sharp cancellation (unit window + DFT alignment)

Envelope bounds later use only `norm_sum_le` and `‖window j‖ ≤ ε`.  **Literal character
cancellation** is `fourierPatchSideCorrelation_eq_zero_of_unit_window_and_dft_align`: if each term
matches the unweighted `k − k'` DFT twiddle, the sum is `sum_exp_two_pi_int_mul_fin_eq_zero_sub`.

The per-term hypothesis `halign` is **one** calibration constraint (one mode pair `k'`, one kernel
frequency `k`, one patch length `n`). In applications, **identifying** the physical parameters that make
arity-axis phasors, window, and harmonic kernel line up with the DFT lattice is not a single scalar
equation: it behaves like a **system** — multiple side modes `k'`, multiple shells or patch lengths, or
multiple observation channels supply independent “curves”; only with **enough** such constraints does
one pin the analogue of an **intercept** (the joint scale/frequency calibration). This file proves
the **per-constraint** implication (`halign` ⇒ sum vanishes), not solvability or uniqueness of the full
system.
-/

/-- Side correlation vanishes for a **unit window** when each summand equals the DFT character at
frequency difference `k − k'`. -/
theorem fourierPatchSideCorrelation_eq_zero_of_unit_window_and_dft_align
    {n : ℕ} (hn : 0 < n) (k k' : ℕ) (hk' : 0 < k')
    (window kernel : Fin n → ℂ)
    (hwin : ∀ j : Fin n, window j = 1)
    (hd : ¬(n : ℤ) ∣ ((k : ℤ) - (k' : ℤ)))
    (halign :
      ∀ j : Fin n,
        Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j =
          Complex.exp ((2 * Real.pi * Complex.I * (((k : ℤ) - (k' : ℤ)) * (j.val : ℤ) : ℂ)) / (n : ℂ))) :
    fourierPatchSideCorrelation k' hk' window kernel = 0 := by
  classical
  dsimp [fourierPatchSideCorrelation]
  refine Eq.trans ?_ (sum_exp_two_pi_int_mul_fin_eq_zero_sub hn hd)
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hwin j, one_mul]
  exact halign j

theorem fourierPatchSideCorrelation_norm_eq_zero_of_unit_window_and_dft_align
    {n : ℕ} (hn : 0 < n) (k k' : ℕ) (hk' : 0 < k')
    (window kernel : Fin n → ℂ)
    (hwin : ∀ j : Fin n, window j = 1)
    (hd : ¬(n : ℤ) ∣ ((k : ℤ) - (k' : ℤ)))
    (halign :
      ∀ j : Fin n,
        Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j =
          Complex.exp ((2 * Real.pi * Complex.I * (((k : ℤ) - (k' : ℤ)) * (j.val : ℤ) : ℂ)) / (n : ℂ))) :
    ‖fourierPatchSideCorrelation k' hk' window kernel‖ = 0 := by
  rw [fourierPatchSideCorrelation_eq_zero_of_unit_window_and_dft_align hn k k' hk' window kernel hwin hd
    halign]
  simp

/--
**Sharp side-lobe sketch (orthogonality certificate + explicit kernel-expanded form).**

Rewrites with `fourierPatchSideCorrelation_with_kernel_expanded`.  The quantitative conclusion is still the
**coarse envelope** (`‖w‖ ≤ ε`) — same bound as `fourierPatchSideCorrelation_bound_from_orthogonality` —
unless per-term alignment holds, in which case see
`fourierPatchSideCorrelation_eq_zero_of_unit_window_and_dft_align`.

Hypotheses `hwin_bdd` and `hmaxCoeff` package peak-scale calibration.

`hk'neq` is narrative (off-peak mode); `hd` is the divisibility hypothesis for the DFT geometric sum.
-/
theorem fourierPatchSideCorrelation_bound_sharp_from_orthogonality_sketch
    {n : ℕ} (hn : 0 < n) (m : ℕ) (_hm : 1 < m) (k : ℕ) (_hk : 0 < k) (_hΩ : Ω m = k)
    (window kernel : Fin n → ℂ)
    (_hwin : WindowIsRadialProjection window)
    (hker : KernelIsHarmonic hn k kernel)
    (k' : ℕ) (hk' : 0 < k')
    (_hk'neq : k' ≠ k)
    (ε maxCoeff : ℝ) (hε : 0 < ε)
    (_hd : ¬(n : ℤ) ∣ ((k : ℤ) - (k' : ℤ)))
    (hwin_bdd : ∀ j : Fin n, ‖window j‖ ≤ ε)
    (hmaxCoeff : (n : ℝ) ≤ maxCoeff) :
    ‖fourierPatchSideCorrelation k' hk' window kernel‖ ≤ ε * maxCoeff := by
  classical
  have hε0 : 0 ≤ ε := le_of_lt hε
  rw [fourierPatchSideCorrelation_with_kernel_expanded hn k k' hk' window kernel hker]
  have hterm (j : Fin n) :
      ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) *
          Complex.exp ((2 * Real.pi * Complex.I * (k * j.val : ℂ)) / (n : ℂ))‖ ≤ ε := by
    rw [← hker.is_char j]
    have hex :
        ‖Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ)))‖ = 1 := by
      simpa [Complex.ofReal_mul, mul_assoc] using
        complex_exp_mul_I_real_unit (axisAngle k' hk' * (j.val : ℝ))
    have hk1 : ‖kernel j‖ = 1 := KernelIsHarmonic.norm_eq_one hn k kernel hker j
    calc
      ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖
          ≤ ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ)))‖ * ‖kernel j‖ :=
        norm_mul_le _ _
      _ ≤ (‖window j‖ * ‖Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ)))‖) * ‖kernel j‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖window j‖ := by rw [hex, hk1, mul_one, mul_one]
      _ ≤ ε := hwin_bdd j
  have hs :=
    calc
      ‖∑ j : Fin n,
            window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) *
              Complex.exp ((2 * Real.pi * Complex.I * (k * j.val : ℂ)) / (n : ℂ))‖
          ≤ ∑ j : Fin n,
              ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) *
                  Complex.exp ((2 * Real.pi * Complex.I * (k * j.val : ℂ)) / (n : ℂ))‖ :=
        norm_sum_le Finset.univ _
      _ ≤ ∑ j : Fin n, ε := Finset.sum_le_sum fun j _ => hterm j
      _ = (n : ℝ) * ε := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc
    ‖∑ j : Fin n,
          window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) *
            Complex.exp ((2 * Real.pi * Complex.I * (k * j.val : ℂ)) / (n : ℂ))‖
        ≤ (n : ℝ) * ε := hs
    _ = ε * (n : ℝ) := by ring
    _ ≤ ε * maxCoeff := mul_le_mul_of_nonneg_left hmaxCoeff hε0

/--
**“Sharp” side-lobe bound** (orthogonality hypothesis + explicit rewrite path).

This is a **definitional alias** of `fourierPatchSideCorrelation_bound_sharp_from_orthogonality_sketch`:
the proof still bounds the sum by **triangle inequality** (`norm_sum_le`) and the window envelope
`‖window j‖ ≤ ε`, together with unimodular phasor and kernel. For **literal cancellation** to `0` when
`∀ j, window j = 1`, see `fourierPatchSideCorrelation_eq_zero_of_unit_window_and_dft_align`.

Hypotheses `hwin_bdd` and `hmaxCoeff` are explicit. There is no `WindowIsRadialProjection.radial_envelope`
in the library, and `fourierPatchPeakCorrelation_eq_axisAngle` does **not** imply `(n : ℝ) ≤ maxCoeff`
without additional peak-calibration assumptions.
-/
theorem fourierPatchSideCorrelation_bound_sharp_from_orthogonality
    {n : ℕ} (hn : 0 < n) (m : ℕ) (_hm : 1 < m) (k : ℕ) (_hk : 0 < k) (_hΩ : Ω m = k)
    (window kernel : Fin n → ℂ)
    (_hwin : WindowIsRadialProjection window)
    (hker : KernelIsHarmonic hn k kernel)
    (k' : ℕ) (hk' : 0 < k')
    (_hk'neq : k' ≠ k)
    (ε maxCoeff : ℝ) (hε : 0 < ε)
    (hd : ¬(n : ℤ) ∣ ((k : ℤ) - (k' : ℤ)))
    (hwin_bdd : ∀ j : Fin n, ‖window j‖ ≤ ε)
    (hmaxCoeff : (n : ℝ) ≤ maxCoeff) :
    ‖fourierPatchSideCorrelation k' hk' window kernel‖ ≤ ε * maxCoeff :=
  fourierPatchSideCorrelation_bound_sharp_from_orthogonality_sketch hn m _hm k _hk _hΩ window kernel _hwin
    hker k' hk' _hk'neq ε maxCoeff hε hd hwin_bdd hmaxCoeff

/-- Same bound as `fourierPatchSideCorrelation_bound_sharp_from_orthogonality`, with `(n : ℝ) ≤ maxCoeff`
derived from peak calibration (`‖peak‖ = maxCoeff` and `n ≤ ‖peak‖`), instead of assuming `hmaxCoeff` outright. -/
theorem fourierPatchSideCorrelation_bound_sharp_from_orthogonality_peak_calibrated
    {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : 1 < m) (k : ℕ) (_hk : 0 < k) (_hΩ : Ω m = k)
    (window kernel : Fin n → ℂ)
    (_hwin : WindowIsRadialProjection window)
    (hker : KernelIsHarmonic hn k kernel)
    (k' : ℕ) (hk' : 0 < k')
    (_hk'neq : k' ≠ k)
    (ε maxCoeff : ℝ) (hε : 0 < ε)
    (hd : ¬(n : ℤ) ∣ ((k : ℤ) - (k' : ℤ)))
    (hwin_bdd : ∀ j : Fin n, ‖window j‖ ≤ ε)
    (hpeak : ‖fourierPatchPeakCorrelation m hm window kernel‖ = maxCoeff)
    (hpeak_ge : (n : ℝ) ≤ ‖fourierPatchPeakCorrelation m hm window kernel‖) :
    ‖fourierPatchSideCorrelation k' hk' window kernel‖ ≤ ε * maxCoeff :=
  fourierPatchSideCorrelation_bound_sharp_from_orthogonality hn m hm k _hk _hΩ window kernel _hwin hker k'
    hk' _hk'neq ε maxCoeff hε hd hwin_bdd
    (maxCoeff_ge_n_of_peak_eq_and_peak_norm_ge window kernel maxCoeff hpeak hpeak_ge)

/-!
The **DFT character** `exp(2π i k j / n)` differs from the **arity-axis** phasor `exp(i · π/(2k') · j)`
used in `fourierPatchSideCorrelation`. Sharp cancellation uses `sum_exp_two_pi_int_mul_fin_eq_zero_sub`.
The theorem below is the complementary **envelope** bound (triangle inequality + unimodular kernel):
it does not require phase alignment with the DFT sum.
-/

/-- **Envelope bound** for the side correlation: triangle inequality + `‖exp(iθ)‖ = 1` + `‖κ j‖ = 1`.

Hypotheses:
* `hwin_bdd`: quantitative radial envelope (`‖window j‖ ≤ ε`), strengthening the qualitative
  `WindowIsRadialProjection` scaffold.
* `hmaxCoeff`: calibration `n ≤ maxCoeff` so `n * ε ≤ ε * maxCoeff` (same `ε` scale as the peak
  normalization in `fourier_patch_concentration`).

Orthogonality (`sum_exp_two_pi_int_mul_fin_eq_zero_sub`) gives a **stronger** cancellation when the
integrand matches the DFT sum; it is not needed for this coarse bound. -/
theorem fourierPatchSideCorrelation_bound_from_orthogonality
    {n : ℕ} (hn : 0 < n) (k k' : ℕ) (hk' : 0 < k')
    (window kernel : Fin n → ℂ)
    (hker : KernelIsHarmonic hn k kernel)
    (_hwin : WindowIsRadialProjection window)
    (ε maxCoeff : ℝ) (hε : 0 < ε)
    (hwin_bdd : ∀ j : Fin n, ‖window j‖ ≤ ε)
    (hmaxCoeff : (n : ℝ) ≤ maxCoeff) :
    ‖fourierPatchSideCorrelation k' hk' window kernel‖ ≤ ε * maxCoeff := by
  classical
  have hε0 : 0 ≤ ε := le_of_lt hε
  have hterm (j : Fin n) :
      ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖ ≤ ε := by
    have hex :
        ‖Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ)))‖ = 1 := by
      simpa [Complex.ofReal_mul, mul_assoc] using
        complex_exp_mul_I_real_unit (axisAngle k' hk' * (j.val : ℝ))
    have hk1 : ‖kernel j‖ = 1 := KernelIsHarmonic.norm_eq_one hn k kernel hker j
    calc
      ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖
          ≤ ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ)))‖ * ‖kernel j‖ :=
        norm_mul_le _ _
      _ ≤ (‖window j‖ * ‖Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ)))‖) * ‖kernel j‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖window j‖ := by rw [hex, hk1, mul_one, mul_one]
      _ ≤ ε := hwin_bdd j
  dsimp [fourierPatchSideCorrelation]
  have hs :=
    calc
      ‖∑ j : Fin n,
            window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖
          ≤ ∑ j : Fin n,
              ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖ :=
        norm_sum_le Finset.univ _
      _ ≤ ∑ j : Fin n, ε := Finset.sum_le_sum fun j _ => hterm j
      _ = (n : ℝ) * ε := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc
    ‖∑ j : Fin n, window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖
        ≤ (n : ℝ) * ε := hs
    _ = ε * (n : ℝ) := by ring
    _ ≤ ε * maxCoeff := mul_le_mul_of_nonneg_left hmaxCoeff hε0

/-- Bundle `FourierPatchConcentration` from peak equality + **envelope** data (no separate `hside`).

Uses `fourierPatchSideCorrelation_bound_from_orthogonality`. The alias
`fourierPatchSideCorrelation_bound_sharp_from_orthogonality` proves the **same inequality** when
`hd : ¬(n : ℤ) ∣ (k - k')` is also assumed, but still does not discharge `hside` by literal orthogonality
cancellation of the weighted sum (see its docstring).

`maxCoeff` calibration `(n : ℝ) ≤ maxCoeff` is an explicit hypothesis (not derived from
`fourierPatchPeakCorrelation_eq_axisAngle` alone). -/
theorem fourier_patch_concentration_of_envelope {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : 1 < m) (k : ℕ)
    (_hk : 0 < k) (_hΩ : Ω m = k) (window kernel : Fin n → ℂ)
    (_hwin : WindowIsRadialProjection window)
    (hker : KernelIsHarmonic hn k kernel)
    (maxCoeff ε : ℝ) (hε : 0 < ε)
    (hpeak : ‖fourierPatchPeakCorrelation m hm window kernel‖ = maxCoeff)
    (hwin_bdd : ∀ j : Fin n, ‖window j‖ ≤ ε)
    (hmaxCoeff : (n : ℝ) ≤ maxCoeff) :
    FourierPatchConcentration hn m hm k window kernel maxCoeff ε :=
  ⟨hpeak, fun _k' _hk' _hkne =>
    fourierPatchSideCorrelation_bound_from_orthogonality hn k _k' _hk' window kernel hker _hwin ε maxCoeff hε
      hwin_bdd hmaxCoeff⟩

/-- Same conclusion as `fourier_patch_concentration_of_envelope`, but with `n ≤ maxCoeff` derived from
peak magnitude: `‖peak‖ = maxCoeff` and `(n : ℝ) ≤ ‖peak‖` (instead of a bare `hmaxCoeff`). -/
theorem fourier_patch_concentration_of_envelope_from_peak_lower {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : 1 < m)
    (k : ℕ) (_hk : 0 < k) (_hΩ : Ω m = k) (window kernel : Fin n → ℂ)
    (_hwin : WindowIsRadialProjection window)
    (hker : KernelIsHarmonic hn k kernel)
    (maxCoeff ε : ℝ) (hε : 0 < ε)
    (hpeak : ‖fourierPatchPeakCorrelation m hm window kernel‖ = maxCoeff)
    (hpeak_ge : (n : ℝ) ≤ ‖fourierPatchPeakCorrelation m hm window kernel‖)
    (hwin_bdd : ∀ j : Fin n, ‖window j‖ ≤ ε) :
    FourierPatchConcentration hn m hm k window kernel maxCoeff ε :=
  fourier_patch_concentration_of_envelope hn m hm k _hk _hΩ window kernel _hwin hker maxCoeff ε hε hpeak
    hwin_bdd (maxCoeff_ge_n_of_peak_eq_and_peak_norm_ge window kernel maxCoeff hpeak hpeak_ge)

/-!
### Orthogonality sketch (same bound, explicit DFT certificate)

`Ω m = k` identifies the **shell** phasor with `axisAngle k` (`intrinsicShellAxisAngle_phasor_eq_axisAngle_phasor`),
not with `axisAngle k'` when `k' ≠ k`. A literal bridge
`intrinsicShellAxisAngle … = axisAngle k'` from `_hΩ` is therefore unavailable off-peak.

What *does* apply for DFT orthogonality is the frequency-difference hypothesis
`¬(n : ℤ) ∣ (k - k')`, yielding `sum_exp_two_pi_int_mul_fin_eq_zero_sub` (unweighted geometric sum).

Sharp **termwise** alignment is `fourierPatchSideCorrelation_eq_zero_of_unit_window_and_dft_align`
(unit window + explicit per-`j` equality with the `k−k'` DFT twiddle).  Until that hypothesis is
available, the quantitative conclusion below still follows from the **envelope** argument (triangle
inequality + unit moduli), matching `fourierPatchSideCorrelation_bound_from_orthogonality`.
-/

theorem fourierPatchSideCorrelation_bound_from_orthogonality_sketch
    {n : ℕ} (hn : 0 < n) (m : ℕ) (_hm : 1 < m) (k : ℕ) (_hk : 0 < k) (_hΩ : Ω m = k)
    (window kernel : Fin n → ℂ)
    (_hwin : WindowIsRadialProjection window)
    (hker : KernelIsHarmonic hn k kernel)
    (k' : ℕ) (hk' : 0 < k')
    (_hd : ¬(n : ℤ) ∣ ((k : ℤ) - (k' : ℤ)))
    (ε maxCoeff : ℝ) (hε : 0 < ε)
    (hwin_bdd : ∀ j : Fin n, ‖window j‖ ≤ ε)
    (hmaxCoeff : (n : ℝ) ≤ maxCoeff) :
    ‖fourierPatchSideCorrelation k' hk' window kernel‖ ≤ ε * maxCoeff := by
  classical
  have hε0 : 0 ≤ ε := le_of_lt hε
  have hterm (j : Fin n) :
      ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖ ≤ ε := by
    have hex :
        ‖Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ)))‖ = 1 := by
      simpa [Complex.ofReal_mul, mul_assoc] using
        complex_exp_mul_I_real_unit (axisAngle k' hk' * (j.val : ℝ))
    have hk1 : ‖kernel j‖ = 1 := KernelIsHarmonic.norm_eq_one hn k kernel hker j
    calc
      ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖
          ≤ ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ)))‖ * ‖kernel j‖ :=
        norm_mul_le _ _
      _ ≤ (‖window j‖ * ‖Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ)))‖) * ‖kernel j‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖window j‖ := by rw [hex, hk1, mul_one, mul_one]
      _ ≤ ε := hwin_bdd j
  dsimp [fourierPatchSideCorrelation]
  have hs :=
    calc
      ‖∑ j : Fin n,
            window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖
          ≤ ∑ j : Fin n,
              ‖window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖ :=
        norm_sum_le Finset.univ _
      _ ≤ ∑ j : Fin n, ε := Finset.sum_le_sum fun j _ => hterm j
      _ = (n : ℝ) * ε := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc
    ‖∑ j : Fin n, window j * Complex.exp (Complex.I * (axisAngle k' hk' * (j.val : ℝ))) * kernel j‖
        ≤ (n : ℝ) * ε := hs
    _ = ε * (n : ℝ) := by ring
    _ ≤ ε * maxCoeff := mul_le_mul_of_nonneg_left hmaxCoeff hε0

/-!
### Roadmap: `patch_address_from_surface_vectors` (not formalized here)

Sketches that conclude `∃ address : Fin 8 → ℤ, …` from Fourier patch hypotheses need glue **outside** this
module:

* **Index mismatch:** `FourierPatchConcentration` / window–kernel data live on `Fin n → ℂ` and discrete
  `j : Fin n`.  An octonion **address** is `Fin 8 → ℤ`.  There is no canonical map `Fin n` patch data →
  `ℤ⁸` in the current formalization — that is physics/pipeline design, not proved from concentration alone.

* **Automatic concentration:** `fourier_patch_concentration_of_envelope_from_peak_lower` already builds
  `FourierPatchConcentration` from `hpeak`, `hpeak_ge`, and `hwin_bdd` — it does **not** take a separate
  `hside` hypothesis (off-peak bounds come from `fourierPatchSideCorrelation_bound_from_orthogonality`).

* **Norm / shell:** use `sumSqInt8` and `latticeShell8Finset` / `mem_latticeShell8Finset_iff`
  (`IntegerLatticeShellCount8`), or `o8normSq (intLatticeToO8 z)` (`OctonionSphereConstruction`).  The sketch’s
  bare `o8normSq address` is a type error: `o8normSq` expects `O8`, not `Fin 8 → ℤ`.

* **Discrete score / slope:** `MoirePatchScore`, `moirePatchScoreSlope`, `moirePatchSlopeStep` package the
  **first and second differences** along the patch (step change in slope). For **pure sinusoid** scores
  along the patch index tied to `intrinsicShellAxisAngle` and `Ω m = k`, closed forms and the zero-jerk
  iff are in `Hqiv.Archive.Algebra.MoireJerkSphereModeBridge` (`moirePatchSlopeStep_sin_intrinsic_of_Omega`,
  `moirePatchSlopeStep_sin_intrinsic_eq_zero_iff`). A concrete global score map from complex correlations
  (e.g. `Re` of a mode) is still a separate choice; `gradient_of_score_on_patch`, `is_on_fourier_patch`,
  and the `∃ … four_squares …` step are not in the codebase.

* **Orthogonality alignment:** `fourierPatchSideCorrelation_eq_zero_of_unit_window_and_dft_align` gives
  exact cancellation for a unit window when each term matches the DFT character; weighted / non-aligned
  regimes still use the envelope lemmas.
-/

end Hqiv.Algebra

end
