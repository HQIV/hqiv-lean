import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3ModelGuidedLocationBound
import Hqiv.Story.S3GoldbachPerronContourRemainder
import Hqiv.Story.S3GoldbachHolomorphicWeightBridge
import Hqiv.Story.S3CumulativeHarmonicPhase
import Hqiv.Story.S3ExplicitFormulaIdentity

/-!
# Explicit-formula location bridge (Perron remainder → zero deviation)

Wires the Path A relaxed Cauchy rectangle error into the classical
`weightDifferenceEulerMaclaurinRemainder` via the **Step 3 identification lemma**.

## Formal pipeline (proved wiring)

1. `GoldbachPerronEulerMaclaurinContourIdentification` — exact equality
   `weightDifferenceEulerMaclaurinRemainder N = goldbachSmoothedPerronChartRemainderAtUnitScale …`
2. `SmoothedPerronRelaxedAnalyticCertificate` — `|chart| ≤` Cauchy total bound (Path A)
3. `perronToWeightDifferenceBridge_of_identification_and_relaxed_certificate` — transitivity
   ⇒ `PerronToWeightDifferenceBridge.em_remainder_le`

The analytic content of (1) is packaged as
`GoldbachExplicitFormulaEulerMaclaurinContourDuality` (harmonic and Perron routes share
the same explicit-formula contour remainder).

## Numerical probe (Python)

`scripts/hqiv_perron_cauchy_error_probe.py` → `data/perron_cauchy_error_probe.json`.
-/

namespace Hqiv.Story

noncomputable section

open Real

/-! ## Explicit-formula input packaging -/

/--
Build `ExplicitFormulaLocationInput` from proved normalized-remainder control plus
the Hardy-`Z` / argument-variation localization target.
-/
noncomputable def explicitFormulaLocationInput_mk {N : ℕ}
    (coverHeight : ℝ) (hT : 0 < coverHeight)
    (normalizedRemainderBound deviationBound : ℝ)
    (hε₀ : 0 ≤ normalizedRemainderBound) (hδ : 0 ≤ deviationBound)
    (hRem : normalizedWeightDifference N ≤ normalizedRemainderBound)
    (hEnv : deviationBound ≤ Real.pi / 2 + normalizedRemainderBound * coverHeight)
    (hLoc :
      ∀ t : ℝ,
        0 < t →
          t ≤ coverHeight →
            riemannZeta (criticalLinePointAtHeight t) = 0 →
              distanceToNearestBalanceCandidate t ≤ deviationBound) :
    ExplicitFormulaLocationInput N where
  coverHeight := coverHeight
  coverHeight_pos := hT
  normalizedRemainderBound := normalizedRemainderBound
  normalizedRemainderBound_nonneg := hε₀
  deviationBound := deviationBound
  deviationBound_nonneg := hδ
  remainder_hypothesis := hRem
  deviation_coarse_envelope := hEnv
  argument_variation_bound := hLoc

/-! ## Perron → weight-difference bridge -/

/--
Relaxed (or exact) Perron contour bookkeeping controls the Euler–Maclaurin tail in
`weightDifference N`.  The field `em_remainder_le` is **proved** by
`perronToWeightDifferenceBridge_of_identification_and_relaxed_certificate`.
-/
structure PerronToWeightDifferenceBridge (N : ℕ) where
  relaxed_total_bound : ℝ
  relaxed_total_bound_nonneg : 0 ≤ relaxed_total_bound
  em_remainder_le :
    |weightDifferenceEulerMaclaurinRemainder N| ≤ relaxed_total_bound

theorem weight_difference_euler_remainder_le_of_perron_bridge {N : ℕ}
    (h : PerronToWeightDifferenceBridge N) :
    |weightDifferenceEulerMaclaurinRemainder N| ≤ h.relaxed_total_bound :=
  h.em_remainder_le

theorem normalized_euler_remainder_le_of_perron_bridge {N : ℕ}
    (h : PerronToWeightDifferenceBridge N) :
    |weightDifferenceEulerMaclaurinRemainder N| / max 1 (partialVonMangoldtWeight N) ≤
      h.relaxed_total_bound / max 1 (partialVonMangoldtWeight N) := by
  gcongr
  exact h.em_remainder_le

/--
**EM identification lemma (proved):** once step-3 identification and the Path A relaxed
certificate hold at aligned `(N, T, σ, σ₀)`, the classical EM tail is bounded by the
Cauchy rectangle total error.
-/
noncomputable def perronToWeightDifferenceBridge_of_identification_and_relaxed_certificate
    {N T : ℕ} {σ : ℝ} (hN : 0 < N) (hσ : 0 < σ) (hT : 1 ≤ T)
    (hId : GoldbachPerronEulerMaclaurinContourIdentification N N T σ hσ hT)
    (cert : SmoothedPerronRelaxedAnalyticCertificate N T σ) :
    PerronToWeightDifferenceBridge N where
  relaxed_total_bound :=
    goldbachSmoothedPerronCauchyRectangleErrorTotalBound N T σ cert.σ₀ hT cert.contour_input
  relaxed_total_bound_nonneg :=
    goldbach_smoothed_perron_cauchy_rectangle_error_total_bound_nonneg N T σ cert.σ₀ hN hσ
      cert.σ₀_pos hT cert.contour_input
  em_remainder_le := by
    rw [hId.em_remainder_eq_chart]
    exact cert.total_error_le

noncomputable def perronToWeightDifferenceBridge_of_identification_and_cauchy_rectangle
    {N T : ℕ} {σ : ℝ} (hN : 0 < N) (hσ : 0 < σ) (hT : 1 ≤ T)
    (hσT : σ * (T : ℝ) ≤ 2 * Real.pi)
    (hId : GoldbachPerronEulerMaclaurinContourIdentification N N T σ hσ hT)
    (hrect : GoldbachSmoothedPerronCauchyRectangleErrorHypothesis N T σ 1 hσ hT (by norm_num))
    (input : GoldbachSmoothedPerronContourInput N σ) :
    PerronToWeightDifferenceBridge N :=
  perronToWeightDifferenceBridge_of_identification_and_relaxed_certificate hN hσ hT hId
    (smoothedPerronRelaxedAnalyticCertificate_from_cauchy_rectangle_error N T σ hσ hT hσT
      input hrect)

/-- Backward-compatible alias (identification supplied explicitly). -/
noncomputable def perronToWeightDifferenceBridge_of_relaxed_certificate {N M T : ℕ} {σ : ℝ}
    (hM : M = N)
    (hMpos : 0 < M)
    (hσ : 0 < σ)
    (hT : 1 ≤ T)
    (cert : SmoothedPerronRelaxedAnalyticCertificate M T σ)
    (hId : GoldbachPerronEulerMaclaurinContourIdentification N M T σ hσ hT) :
    PerronToWeightDifferenceBridge N := by
  subst hM
  exact perronToWeightDifferenceBridge_of_identification_and_relaxed_certificate hMpos hσ hT hId
    cert

/-! ## Explicit-formula duality → identification -/

noncomputable def perronToWeightDifferenceBridge_of_explicit_formula_duality_and_relaxed_certificate
    {N T : ℕ} {σ : ℝ} (hN : 0 < N) (hσ : 0 < σ) (hT : 1 ≤ T)
    (hDual : GoldbachExplicitFormulaEulerMaclaurinContourDuality N N T σ hσ hT)
    (cert : SmoothedPerronRelaxedAnalyticCertificate N T σ) :
    PerronToWeightDifferenceBridge N :=
  perronToWeightDifferenceBridge_of_identification_and_relaxed_certificate hN hσ hT
    (goldbach_perron_euler_maclaurin_contour_identification_of_explicit_formula_duality hσ hT
      hDual)
    cert

/-! ## Hardy Z / explicit-formula localization (named input) -/

structure HardyZExplicitFormulaLocationHypothesis (N : ℕ) where
  coverHeight : ℝ
  coverHeight_pos : 0 < coverHeight
  normalizedRemainderBound : ℝ
  normalizedRemainderBound_nonneg : 0 ≤ normalizedRemainderBound
  deviationBound : ℝ
  deviationBound_nonneg : 0 ≤ deviationBound
  deviation_coarse_envelope :
    deviationBound ≤ Real.pi / 2 + normalizedRemainderBound * coverHeight
  argument_variation_bound :
    ∀ t : ℝ,
      0 < t →
        t ≤ coverHeight →
          riemannZeta (criticalLinePointAtHeight t) = 0 →
            distanceToNearestBalanceCandidate t ≤ deviationBound

def explicitFormulaLocationInput_of_hardy_z {N : ℕ}
    (h : HardyZExplicitFormulaLocationHypothesis N)
    (hRem : normalizedWeightDifference N ≤ h.normalizedRemainderBound) :
    ExplicitFormulaLocationInput N :=
  explicitFormulaLocationInput_mk h.coverHeight h.coverHeight_pos
    h.normalizedRemainderBound h.deviationBound h.normalizedRemainderBound_nonneg
    h.deviationBound_nonneg hRem h.deviation_coarse_envelope h.argument_variation_bound

/-! ## Contour growth certificate (classical side) -/

/--
From the proved bridge, obtain `ContourGrowthControlsEulerRemainder` at default truncation.
-/
noncomputable def contourGrowthControlsEulerRemainder_of_perron_bridge {N : ℕ}
    (hN : 0 < N)
    (hBridge : PerronToWeightDifferenceBridge N) :
    ContourGrowthControlsEulerRemainder N where
  generating := goldbachPartitionGeneratingFunctionDefault N
  remainderBound := hBridge.relaxed_total_bound
  remainder_bound_nonneg := hBridge.relaxed_total_bound_nonneg
  holomorphic_implies_remainder_bound := fun _ => hBridge.em_remainder_le

noncomputable def goldbachHolomorphicRegularityCertificate_of_perron_bridge {N : ℕ}
    (hN : 0 < N)
    (hBridge : PerronToWeightDifferenceBridge N) :
    GoldbachHolomorphicRegularityCertificate N :=
  goldbachHolomorphicRegularityCertificate_of_default_contour
    (contourGrowthControlsEulerRemainder_at_default_truncation
      (contourGrowthControlsEulerRemainder_of_perron_bridge hN hBridge) rfl)

/-! ## Full location theorem scaffold -/

noncomputable def modelGuidedLocationTheorem_of_perron_and_hardy {N : ℕ}
    (hId : RollingZetaIdentificationAtCriticalLine)
    (hP : PerronToWeightDifferenceBridge N)
    (hZ : HardyZExplicitFormulaLocationHypothesis N)
    (hRem : normalizedWeightDifference N ≤ hZ.normalizedRemainderBound)
    (hDev : normalizedWeightDifference N ≤ hZ.deviationBound) :
    ModelGuidedLocationTheorem N :=
  modelGuidedLocationTheorem_of_input hId
    (modelGuidedLocationBound_from_remainder hZ.coverHeight hZ.coverHeight_pos
      hZ.deviationBound hZ.deviationBound_nonneg
      { remainderBound := hP.relaxed_total_bound
        remainderBound_nonneg := hP.relaxed_total_bound_nonneg
        remainder_le := hP.em_remainder_le }
      hDev)
    (explicitFormulaLocationInput_of_hardy_z hZ hRem)
    rfl rfl

/-!
## Status

* **Proved:** `perronToWeightDifferenceBridge_of_identification_and_relaxed_certificate`
  (EM identification + Path A certificate ⇒ `em_remainder_le`).
* **Proved:** duality ⇒ identification; identification + certificate ⇒
  `ContourGrowthControlsEulerRemainder` / holomorphic certificate.
* **Named (step 3 analytic content):** `GoldbachExplicitFormulaEulerMaclaurinContourDuality`
  — instantiate from discrete explicit formula + Goldbach Mellin contour.
* **Named:** `HardyZExplicitFormulaLocationHypothesis` (argument variation).
* **Probe:** `scripts/hqiv_perron_cauchy_error_probe.py`.
-/

end

end Hqiv.Story
