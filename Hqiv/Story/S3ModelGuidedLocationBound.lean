import Hqiv.Story.S3ModelGuidedZeroLocator
import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3HopfJKUnitCircleZeroReadout
import Mathlib.Algebra.Order.Round

/-!
# Model-guided zero location bounds (Option 2 scaffold)

## Exact geometric chart (proved)

* `A(θ) = 0` ⟺ `θ = balanceCandidateHeight k`;
* cumulative harmonic phase sum vanishes on the same locus when `N > 0`;
* every real `t` lies within `π/2` of some model candidate (`distance_to_nearest_..._le_half_period`).

## Exact conditional localization (rolling identification)

Under `RollingZetaIdentificationAtCriticalLine`, a critical-line ordinate is a ζ-zero
**iff** the amplitude vanishes **iff** `t` is exactly a balance candidate — not merely
near one (`zeta_zero_iff_exact_balance_candidate`).

## Deviation / remainder slot (named analytic input)

Real zeros have average spacing `≈ 2π / log t`, while model candidates are spaced by
`π`.  Any proved deviation bound will likely **grow with `T`**: fixed `π` spacing
vs shrinking classical spacing, and `|Δ_N|/Λ_N` is not uniformly small in `N`.

`ModelGuidedLocationBound` packages remainder-driven error budgets;
`ZetaZeroNearModelCandidate` is the zero-location hypothesis to prove from analytic
input.  `ModelGuidedZeroLocationTheoremTarget` records the intended theorem shape
(Option B).  No unconditional deviation theorem is claimed here.

See `scripts/model_guided_zero_locator.py` for the hybrid numerical locator (Option 1).
-/

namespace Hqiv.Story

noncomputable section

open Real Complex

/-! ## Nearest balance candidate -/

/-- Index of the nearest model candidate to ordinate `t`. -/
noncomputable def nearestBalanceCandidateIndex (t : ℝ) : ℤ :=
  round ((t - 3 * Real.pi / 4) / Real.pi)

/-- Height of the nearest model candidate. -/
noncomputable def nearestBalanceCandidateHeight (t : ℝ) : ℝ :=
  balanceCandidateHeight (nearestBalanceCandidateIndex t)

/-- Distance from `t` to the nearest model candidate `t_k`. -/
noncomputable def distanceToNearestBalanceCandidate (t : ℝ) : ℝ :=
  |t - nearestBalanceCandidateHeight t|

theorem nearest_balance_candidate_height_eq (t : ℝ) :
    nearestBalanceCandidateHeight t =
      balanceCandidateHeight (nearestBalanceCandidateIndex t) := rfl

theorem distance_to_nearest_balance_candidate_at_candidate (k : ℤ) :
    distanceToNearestBalanceCandidate (balanceCandidateHeight k) = 0 := by
  dsimp [distanceToNearestBalanceCandidate, nearestBalanceCandidateHeight,
    nearestBalanceCandidateIndex, balanceCandidateHeight]
  have hround :
      round ((balanceCandidateHeight k - 3 * Real.pi / 4) / Real.pi) = k := by
    have hk : (balanceCandidateHeight k - 3 * Real.pi / 4) / Real.pi = (k : ℝ) := by
      dsimp [balanceCandidateHeight]
      field_simp
      ring
    rw [hk, round_intCast]
  simp [hround, sub_self, abs_zero]

/-- Every ordinate lies within half a candidate period of some model point. -/
theorem distance_to_nearest_balance_candidate_le_half_period (t : ℝ) :
    distanceToNearestBalanceCandidate t ≤ Real.pi / 2 := by
  dsimp only [distanceToNearestBalanceCandidate, nearestBalanceCandidateHeight,
    nearestBalanceCandidateIndex]
  have hunit :
      t - balanceCandidateHeight (round ((t - 3 * Real.pi / 4) / Real.pi)) =
        ((t - 3 * Real.pi / 4) / Real.pi - round ((t - 3 * Real.pi / 4) / Real.pi)) * Real.pi := by
    dsimp [balanceCandidateHeight]
    field_simp
    ring
  have habs :
      |t - balanceCandidateHeight (round ((t - 3 * Real.pi / 4) / Real.pi))| =
        |((t - 3 * Real.pi / 4) / Real.pi - round ((t - 3 * Real.pi / 4) / Real.pi)) * Real.pi| := by
    rw [hunit]
  have hhalf :
      |((t - 3 * Real.pi / 4) / Real.pi - round ((t - 3 * Real.pi / 4) / Real.pi))| ≤ 1 / 2 :=
    abs_sub_round ((t - 3 * Real.pi / 4) / Real.pi)
  rw [habs, abs_mul, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos, hhalf]

theorem distance_to_nearest_balance_candidate_eq_zero_iff {t : ℝ} :
    distanceToNearestBalanceCandidate t = 0 ↔ ∃ k : ℤ, t = balanceCandidateHeight k := by
  constructor
  · intro h
    have ht : t = nearestBalanceCandidateHeight t := by
      dsimp [distanceToNearestBalanceCandidate] at h
      rw [abs_eq_zero] at h
      exact eq_of_sub_eq_zero h
    exact ⟨nearestBalanceCandidateIndex t, ht⟩
  · intro ⟨k, ht⟩
    rw [ht]
    exact distance_to_nearest_balance_candidate_at_candidate k

/-! ## Exact conditional localization (identification bridge) -/

theorem critical_amplitude_eq_zero_iff_distance_zero (t : ℝ) :
    criticalAmplitudeAt t = 0 ↔ distanceToNearestBalanceCandidate t = 0 :=
  (critical_amplitude_at_eq_zero_iff_balance t).trans
    (distance_to_nearest_balance_candidate_eq_zero_iff.symm)

theorem zeta_zero_iff_exact_balance_candidate
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    riemannZeta (criticalLinePointAtHeight t) = 0 ↔
      ∃ k : ℤ, t = balanceCandidateHeight k := by
  simpa [criticalAmplitudeAt] using
    (zeta_zero_iff_hopf_jk_amplitude hId t).trans (critical_amplitude_at_eq_zero_iff_balance t)

theorem zeta_zero_iff_distance_zero_of_identification
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    riemannZeta (criticalLinePointAtHeight t) = 0 ↔
      distanceToNearestBalanceCandidate t = 0 := by
  rw [zeta_zero_iff_exact_balance_candidate hId t, distance_to_nearest_balance_candidate_eq_zero_iff]

/-! ## Remainder-driven deviation budget (Option 2 packaging) -/

/--
Remainder-controlled locator error budget at truncation depth `N`.

`remainder_controls_deviation` is the analytic link: normalized weight difference
`|Δ_N| / max(1, Λ_N)` feeds the declared `deviationBound`.  Instantiating this plus
`ZetaZeroNearModelCandidate` yields a model-guided location theorem.
-/
structure ModelGuidedLocationBound (N : ℕ) where
  /-- Cover height on the critical line. -/
  coverHeight : ℝ
  coverHeight_pos : 0 < coverHeight
  /-- Declared per-zero deviation from nearest model candidate. -/
  deviationBound : ℝ
  deviationBound_nonneg : 0 ≤ deviationBound
  /-- Asymptotic remainder slot for `weightDifference N`. -/
  asymptoticSlot : WeightDifferenceAsymptoticSlot N
  /-- Normalized remainder control (Euler–Maclaurin / explicit-formula input). -/
  remainder_controls_deviation :
    |weightDifference N| / max 1 (partialVonMangoldtWeight N) ≤ deviationBound

/--
Named analytic hypothesis: every ζ-zero ordinate up to `coverHeight` lies within
`deviationBound` of a model balance candidate.

This is the **deviation theorem** target — not proved unconditionally here.
-/
structure ZetaZeroNearModelCandidate where
  identification : RollingZetaIdentificationAtCriticalLine
  coverHeight : ℝ
  coverHeight_pos : 0 < coverHeight
  deviationBound : ℝ
  deviationBound_nonneg : 0 ≤ deviationBound
  zero_within_bound :
    ∀ t : ℝ,
      0 < t →
        t ≤ coverHeight →
          riemannZeta (criticalLinePointAtHeight t) = 0 →
            distanceToNearestBalanceCandidate t ≤ deviationBound

/--
Full model-guided location certificate: remainder budget + zero localization hypothesis.
-/
structure ModelGuidedLocationTheorem (N : ℕ) where
  bound : ModelGuidedLocationBound N
  localization : ZetaZeroNearModelCandidate
  /-- Cover heights align. -/
  coverHeight_eq : bound.coverHeight = localization.coverHeight
  /-- Deviation budgets align. -/
  deviationBound_eq : bound.deviationBound = localization.deviationBound

/-- Unconditional half-period envelope (geometry only — no ζ input). -/
theorem model_candidate_half_period_envelope (t : ℝ) :
    distanceToNearestBalanceCandidate t ≤ Real.pi / 2 :=
  distance_to_nearest_balance_candidate_le_half_period t

/-! ## Spacing comparison (why deviation may grow with `T`) -/

/-- Model candidate spacing (`π`). -/
noncomputable def modelCandidateSpacing : ℝ := Real.pi

/-- Classical average zero spacing at height `T` — `2π / log T` (for `T > 1`). -/
noncomputable def classicalZeroSpacingAt (T : ℝ) : ℝ :=
  2 * Real.pi / asymptoticLog (Nat.floor T)

/-! ## Option A: asymptotic sketch hook -/

/-- Normalized remainder `|Δ_N| / max(1, Λ_N)`. -/
noncomputable def normalizedWeightDifference (N : ℕ) : ℝ :=
  |weightDifference N| / max 1 (partialVonMangoldtWeight N)

/-! ## Option B: deviation theorem target -/

/--
**Theorem target (model-guided zero location).**

Let `γ` be a ζ-zero ordinate with `0 < γ ≤ T`.  Let `t_k` be the nearest model
balance candidate.  Suppose `|Δ_N| / Λ_N ≤ ε` from `WeightDifferenceAsymptoticSlot`.
Then prove `|γ − t_k| ≤ f(ε, T)` via explicit-formula / Hardy-`Z` argument variation.

The coarse envelope `π/2 + ε · T` is recorded as a **design target** — deviation
bounds are not expected to be uniform in `T` because model spacing is fixed at `π`
while classical spacing shrinks like `2π / log T`.
-/
structure ModelGuidedZeroLocationTheoremTarget (N : ℕ) where
  coverHeight : ℝ
  coverHeight_pos : 0 < coverHeight
  /-- ε(N,T) — normalized remainder budget. -/
  normalizedRemainderBound : ℝ
  normalizedRemainderBound_nonneg : 0 ≤ normalizedRemainderBound
  /-- Declared locator deviation `f(ε, T)`. -/
  deviationBound : ℝ
  deviationBound_nonneg : 0 ≤ deviationBound
  /-- Remainder hypothesis at truncation `N`. -/
  remainder_hypothesis :
    normalizedWeightDifference N ≤ normalizedRemainderBound
  /-- Design envelope: `f(ε,T) ≤ π/2 + ε·T` (may be improved analytically). -/
  deviation_coarse_envelope :
    deviationBound ≤ Real.pi / 2 + normalizedRemainderBound * coverHeight
  /-- Zero localization target. -/
  zero_localization :
    ∀ t : ℝ,
      0 < t →
        t ≤ coverHeight →
          riemannZeta (criticalLinePointAtHeight t) = 0 →
            distanceToNearestBalanceCandidate t ≤ deviationBound

/--
Named analytic input: Hardy-`Z` / argument-variation converts remainder control into
an ordinate deviation bound.  Prove this from explicit-formula estimates.
-/
structure ExplicitFormulaLocationInput (N : ℕ) where
  coverHeight : ℝ
  coverHeight_pos : 0 < coverHeight
  normalizedRemainderBound : ℝ
  normalizedRemainderBound_nonneg : 0 ≤ normalizedRemainderBound
  deviationBound : ℝ
  deviationBound_nonneg : 0 ≤ deviationBound
  remainder_hypothesis :
    normalizedWeightDifference N ≤ normalizedRemainderBound
  deviation_coarse_envelope :
    deviationBound ≤ Real.pi / 2 + normalizedRemainderBound * coverHeight
  argument_variation_bound :
    ∀ t : ℝ,
      0 < t →
        t ≤ coverHeight →
          riemannZeta (criticalLinePointAtHeight t) = 0 →
            distanceToNearestBalanceCandidate t ≤ deviationBound

/-- Build `ZetaZeroNearModelCandidate` from explicit-formula location input. -/
noncomputable def zetaZeroNearModelCandidate_of_explicit_formula_input {N : ℕ}
    (hId : RollingZetaIdentificationAtCriticalLine)
    (h : ExplicitFormulaLocationInput N) :
    ZetaZeroNearModelCandidate where
  identification := hId
  coverHeight := h.coverHeight
  coverHeight_pos := h.coverHeight_pos
  deviationBound := h.deviationBound
  deviationBound_nonneg := h.deviationBound_nonneg
  zero_within_bound := h.argument_variation_bound

/-- Under exact identification, ζ-zeros lie exactly on candidates (`distance = 0`). -/
theorem zeta_zero_distance_eq_zero_of_identification
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ)
    (hζ : riemannZeta (criticalLinePointAtHeight t) = 0) :
    distanceToNearestBalanceCandidate t = 0 := by
  rw [← zeta_zero_iff_distance_zero_of_identification hId t]
  exact hζ

/-- Build a location bound from remainder data and normalized remainder control. -/
noncomputable def modelGuidedLocationBound_from_remainder {N : ℕ}
    (coverHeight : ℝ) (hT : 0 < coverHeight)
    (deviationBound : ℝ) (hδ : 0 ≤ deviationBound)
    (hRem : WeightDifferenceRemainderBound N)
    (hε :
      |weightDifference N| / max 1 (partialVonMangoldtWeight N) ≤ deviationBound) :
    ModelGuidedLocationBound N where
  coverHeight := coverHeight
  coverHeight_pos := hT
  deviationBound := deviationBound
  deviationBound_nonneg := hδ
  asymptoticSlot := weightDifferenceAsymptoticSketch N hRem
  remainder_controls_deviation := hε

/-- Package location bound + explicit-formula input into a full certificate. -/
noncomputable def modelGuidedLocationTheorem_of_input {N : ℕ}
    (hId : RollingZetaIdentificationAtCriticalLine)
    (bound : ModelGuidedLocationBound N)
    (h : ExplicitFormulaLocationInput N)
    (cover_eq : bound.coverHeight = h.coverHeight)
    (dev_eq : bound.deviationBound = h.deviationBound) :
    ModelGuidedLocationTheorem N where
  bound := bound
  localization := zetaZeroNearModelCandidate_of_explicit_formula_input hId h
  coverHeight_eq := cover_eq
  deviationBound_eq := dev_eq

/-!
## Status

* **Unconditional:** nearest-candidate distance `≤ π/2`; exact balance ⟺ distance `0`.
* **Exact conditional:** `RollingZetaIdentification` ⟹ zeros at candidates exactly (`distance = 0`).
* **Option A:** `weightDifferenceLeadingTerm` + `weightDifferenceAsymptoticSketch`.
* **Option B:** `ModelGuidedZeroLocationTheoremTarget` + `ExplicitFormulaLocationInput`.
* **Path A (Perron):** relaxed Cauchy rectangle error at unit scale packages as
  `goldbachSmoothedPerronCauchyRectangleErrorTotalBound` =
  tail bookkeeping `+` `goldbachGaussianLeftEdgeMellinLinkError` (A₂ smoothed `+ 8×` FMPlusOne);
  see `SmoothedPerronRelaxedAnalyticCertificate` in `S3GoldbachPerronContourRemainder`.
  Feeding this into `deviationBound` / `normalizedRemainderBound` still needs
  `ExplicitFormulaLocationInput.argument_variation_bound`.
* **Target:** prove `ExplicitFormulaLocationInput` from remainder bounds + Hardy-`Z` estimates.
* **Practical:** hybrid locator in `scripts/model_guided_zero_locator.py`.
-/

end

end Hqiv.Story
