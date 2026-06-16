import Hqiv.Story.S3SemiprimeExplicitFormulaMediation

/-!
# Finite-frame main↔probe cross-talk law

This module names the **actual cross-talk term** between the main `45°` channel and a
higher-twiddle probe inside a level-`N` frame, and proves its support structure:

* **Spectral leg** — semiprime-only (`finiteSpectralCrossTalk_eq_semiprime_sum`);
* **Explicit-formula leg** — prime-square-only
  (`twiddleCrossTalkExplicitFormulaWeight_eq_prime_square_sum`).

The frame ratio law (`twiddleInteriorFrameAssembly_div_interiorStripHFrame`) lives in
`S3HigherTwiddleFactorizationProbe`: at common strip points,
`h_probe^{(N)} / h_main^{(N)} = so4CriticalFactor / free_probe` whenever the shared
Dirichlet numerator is nonzero.

RH discharge remains on the main `interiorStripH` capstone.
-/

namespace Hqiv.Story

noncomputable section

open ArithmeticFunction Complex Real Finset

/-! ## Cross-talk term -/

/--
The finite-frame **main↔probe cross-talk term**: semiprime spectral leakage from
probe to main readout at level `N`.
-/
noncomputable def twiddleMainProbeCrossTalk (N : ℕ) (ct : HigherTwiddleCrossTalk) (s : ℂ) : ℂ :=
  ct.finiteLeakage N s

theorem twiddleMainProbeCrossTalk_def (N : ℕ) (ct : HigherTwiddleCrossTalk) (s : ℂ) :
    twiddleMainProbeCrossTalk N ct s = finiteSpectralCrossTalk N ct.weight s := by
  rfl

/--
The **Λ-side projection** of cross-talk: the portion visible to the explicit-formula
prime channel at truncation `N`.
-/
noncomputable def twiddleCrossTalkExplicitFormulaWeight (N : ℕ) (ct : HigherTwiddleCrossTalk) : ℝ :=
  explicitFormulaWeightPair N (fun n => (ct.weight n).re)

theorem twiddleCrossTalkExplicitFormulaWeight_def (N : ℕ) (ct : HigherTwiddleCrossTalk) :
    twiddleCrossTalkExplicitFormulaWeight N ct =
      ∑ n ∈ Finset.Icc 1 N, vonMangoldt n * (ct.weight n).re := by
  rfl

/--
**Spectral support.**  Cross-talk is a semiprime sum of spectral lines; primes and
non-semiprimes carry zero weight.
-/
theorem twiddleMainProbeCrossTalk_eq_semiprime_sum
    (N : ℕ) (ct : HigherTwiddleCrossTalk) (h : ct.semiprimeMediated) (s : ℂ) :
    twiddleMainProbeCrossTalk N ct s =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => isSemiprime n),
        ct.weight n * so4SpectralLine n s := by
  unfold twiddleMainProbeCrossTalk
  exact finiteSpectralCrossTalk_eq_semiprime_sum h N s

/--
**Explicit-formula support.**  The Λ-side projection vanishes off prime squares; this
is the precise "semiprime mediated → weak/indirect" content.
-/
theorem twiddleCrossTalkExplicitFormulaWeight_eq_prime_square_sum
    (N : ℕ) (ct : HigherTwiddleCrossTalk) (h : ct.semiprimeMediated) :
    twiddleCrossTalkExplicitFormulaWeight N ct =
      ∑ n ∈ primeSquareIndicesInFrame N, vonMangoldt n * (ct.weight n).re := by
  unfold twiddleCrossTalkExplicitFormulaWeight
  exact explicitFormulaWeightPair_eq_prime_square_sum
    (w := fun n => (ct.weight n).re)
    (by
      intro n hnot
      show (ct.weight n).re = 0
      rw [h n hnot, Complex.zero_re])
    N

theorem twiddleCrossTalkExplicitFormulaWeight_eq_zero_of_no_prime_squares
    (N : ℕ) (ct : HigherTwiddleCrossTalk) (h : ct.semiprimeMediated)
    (hempty : primeSquareIndicesInFrame N = ∅) :
    twiddleCrossTalkExplicitFormulaWeight N ct = 0 := by
  rw [twiddleCrossTalkExplicitFormulaWeight_eq_prime_square_sum N ct h, hempty, Finset.sum_empty]

/--
**Prime-square spectral leg.**  The spectral cross-talk sum restricted to prime
squares is exactly the prime-square subsum.
-/
noncomputable def twiddleMainProbePrimeSquareCrossTalk (N : ℕ) (ct : HigherTwiddleCrossTalk)
    (s : ℂ) : ℂ :=
  ∑ n ∈ primeSquareIndicesInFrame N, ct.weight n * so4SpectralLine n s

theorem twiddleMainProbePrimeSquareCrossTalk_eq_filter
    (N : ℕ) (ct : HigherTwiddleCrossTalk) (h : ct.semiprimeMediated) (s : ℂ) :
    twiddleMainProbePrimeSquareCrossTalk N ct s =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => isPrimeSquare n),
        ct.weight n * so4SpectralLine n s := by
  unfold twiddleMainProbePrimeSquareCrossTalk primeSquareIndicesInFrame
  rfl

/--
Packaging: semiprime-mediated cross-talk has a **two-tier** support decomposition —
all semiprimes spectrally, but only prime squares on the explicit-formula leg.
-/
structure SemiprimeCrossTalkSupportLaw (N : ℕ) (ct : HigherTwiddleCrossTalk) where
  semiprime_mediates : ct.semiprimeMediated
  explicit_prime_square :
    twiddleCrossTalkExplicitFormulaWeight N ct =
      ∑ n ∈ primeSquareIndicesInFrame N, vonMangoldt n * (ct.weight n).re
  spectral_semiprime (s : ℂ) :
    twiddleMainProbeCrossTalk N ct s =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => isSemiprime n),
        ct.weight n * so4SpectralLine n s

theorem semiprimeCrossTalkSupportLaw (N : ℕ) (ct : HigherTwiddleCrossTalk)
    (h : ct.semiprimeMediated) :
    SemiprimeCrossTalkSupportLaw N ct :=
  { semiprime_mediates := h
    explicit_prime_square :=
      twiddleCrossTalkExplicitFormulaWeight_eq_prime_square_sum N ct h
    spectral_semiprime := fun s =>
      twiddleMainProbeCrossTalk_eq_semiprime_sum N ct h s }

/--
Quantitative bound on the explicit-formula leg of cross-talk for a bounded carrier.
-/
theorem twiddleCrossTalkExplicitFormulaWeight_abs_le
    (N : ℕ) (ct : HigherTwiddleCrossTalk) (h : ct.semiprimeMediated) (hN1 : 1 ≤ N)
    (C : ℝ) (hC : ∀ n ∈ Finset.Icc 1 N, |(ct.weight n).re| ≤ C) (hC0 : 0 ≤ C) :
    |twiddleCrossTalkExplicitFormulaWeight N ct| ≤
      C * (primeSquareIndicesInFrame N).card * Real.log N := by
  unfold twiddleCrossTalkExplicitFormulaWeight
  exact explicitFormulaWeightPair_abs_le
    (w := fun n => (ct.weight n).re)
    (by
      intro n hnot
      show (ct.weight n).re = 0
      rw [h n hnot, Complex.zero_re])
    hN1 C hC hC0

end

end Hqiv.Story
