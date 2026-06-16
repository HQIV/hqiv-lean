import Hqiv.Story.S3CumulativeHarmonicPhase
import Mathlib.Data.Int.Interval

/-!
# Model-guided zero locator (Option 1 scaffold)

The geometric chart supplies an **exact** balance locus on the critical circle:

`A(θ) = cos(θ − π/4) = 0`  ⟺  `θ = 3π/4 + kπ` (`k ∈ ℤ`).

Because `cumulativeHarmonicPhaseSum N θ = A(θ) · W_N` for every `N > 0`, the full
cumulative harmonic phase sum vanishes on the **same** arithmetic sequence — antipodal
pair cancellation is unconditional, so the locator is robust to that symmetry.

This module names the candidate ordinates and packages the hybrid locator spec
(model candidates + classical Hardy-`Z` verification in `scripts/model_guided_zero_locator.py`).

## Honesty

Model points are **candidate** ordinates with perfect cancellation in the geometric
chart.  Locating actual ζ-zeros uses classical `Z(t)` sign-change search in windows
around each candidate (unconditional numerics; not a zero-location theorem).
-/

namespace Hqiv.Story

noncomputable section

open Real

/-! ## Balance candidate sequence -/

/-- Model ordinate `t_k = 3π/4 + kπ` on the critical line (`θ = t`). -/
noncomputable def balanceCandidateHeight (k : ℤ) : ℝ :=
  (3 * Real.pi / 4) + (k : ℝ) * Real.pi

theorem balance_candidate_height_eq (k : ℤ) :
    balanceCandidateHeight k = (3 * Real.pi / 4) + (k : ℝ) * Real.pi := rfl

theorem balance_candidate_amplitude_vanishes (k : ℤ) :
    criticalAmplitudeAt (balanceCandidateHeight k) = 0 :=
  (critical_amplitude_at_eq_zero_iff_balance (balanceCandidateHeight k)).mpr ⟨k, rfl⟩

/-- Smallest index with positive model height (`k = 0` gives `3π/4`). -/
noncomputable def balanceCandidateKMinPos : ℤ := 0

theorem balance_candidate_k_min_pos_height :
    0 < balanceCandidateHeight balanceCandidateKMinPos := by
  dsimp [balanceCandidateHeight, balanceCandidateKMinPos]
  positivity

/-- Largest index `k` with `t_k ≤ T` (empty range when `T < 3π/4`). -/
noncomputable def balanceCandidateKMax (T : ℝ) : ℤ :=
  Int.floor ((T - 3 * Real.pi / 4) / Real.pi)

/-- Indices `k` with `0 ≤ k ≤ k_max(T)` and `t_k ≤ T`. -/
noncomputable def modelCandidateIndicesUpTo (T : ℝ) : Finset ℤ :=
  if balanceCandidateKMax T < 0 then ∅
  else Finset.Icc balanceCandidateKMinPos (balanceCandidateKMax T)

theorem balance_candidate_height_le_T_of_mem_indices {T : ℝ} {k : ℤ}
    (hk : k ∈ modelCandidateIndicesUpTo T) :
    balanceCandidateHeight k ≤ T := by
  dsimp [modelCandidateIndicesUpTo] at hk
  split_ifs at hk with hneg
  · cases hk
  · rcases Finset.mem_Icc.mp hk with ⟨hk0, hkmax⟩
    have hfloor :
        (k : ℝ) ≤ (T - 3 * Real.pi / 4) / Real.pi := by
      calc
        (k : ℝ) ≤ (balanceCandidateKMax T : ℝ) := Int.cast_le.mpr hkmax
        _ ≤ (T - 3 * Real.pi / 4) / Real.pi := by
          simpa [balanceCandidateKMax] using
            Int.floor_le ((T - 3 * Real.pi / 4) / Real.pi)
    have hle :
        (3 * Real.pi / 4) + (k : ℝ) * Real.pi ≤ T := by
      have hkpi : (k : ℝ) * Real.pi ≤ T - 3 * Real.pi / 4 := by
        rw [le_div_iff₀ Real.pi_pos] at hfloor
        linarith
      linarith
    simpa [balanceCandidateHeight] using hle

/-- Cumulative harmonic phase vanishes exactly on the balance candidate locus when `N > 0`. -/
theorem cumulative_harmonic_phase_sum_eq_zero_iff_balance_candidate {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    cumulativeHarmonicPhaseSum N θ = 0 ↔
      ∃ k : ℤ, θ = balanceCandidateHeight k :=
  (cumulative_harmonic_phase_sum_eq_zero_iff hN θ).trans
    (critical_amplitude_at_eq_zero_iff_balance θ)

theorem cumulative_harmonic_phase_vanishes_on_candidate {N : ℕ} (hN : 0 < N) (k : ℤ) :
    cumulativeHarmonicPhaseSum N (balanceCandidateHeight k) = 0 :=
  (cumulative_harmonic_phase_sum_eq_zero_iff_balance_candidate hN _).mpr ⟨k, rfl⟩

/-! ## Hybrid locator specification (classical verification slot) -/

/--
Data returned by classical zero location near one model candidate
(`scripts/model_guided_zero_locator.locate_zeros_near`).
-/
structure LocatedZeroNearCandidate where
  candidateHeight : ℝ
  candidateIndex : ℤ
  locatedHeight : ℝ
  hardyZAtLocated : ℝ
  distanceToCandidate : ℝ
  distance_nonneg : 0 ≤ distanceToCandidate

/--
Option-1 hybrid locator: model candidates up to height `T`, plus classical Hardy-`Z`
sign-change search in windows (implemented numerically in Python).
-/
structure ModelGuidedZeroLocatorSpec where
  /-- Cover height on the critical line. -/
  coverHeight : ℝ
  /-- Half-width of the classical search window around each candidate. -/
  window : ℝ
  window_pos : 0 < window
  /-- Model candidate indices with `t_k ≤ coverHeight`. -/
  candidateIndices : Finset ℤ
  /-- Every listed candidate lies below the cover height. -/
  candidate_height_le :
    ∀ k ∈ candidateIndices, balanceCandidateHeight k ≤ coverHeight
  /-- Classical located zeros (may be empty until numerics are run). -/
  locatedZeros : List LocatedZeroNearCandidate

/-- Populate candidate indices from the closed-form range (proof-backed). -/
noncomputable def modelCandidateIndicesUpTo_cover (T : ℝ) : Finset ℤ :=
  modelCandidateIndicesUpTo T

/-!
## Status

* **Exact locator (model):** `A(θ) = 0` ⟺ `θ = balanceCandidateHeight k`; same for
  `cumulativeHarmonicPhaseSum N θ` when `N > 0`.
* **Hybrid:** `ModelGuidedZeroLocatorSpec` + Python `model_guided_zero_locator.py`.
* **Not claimed:** every ζ-zero lies near a model point (Option 2 deviation theorem).
-/

end

end Hqiv.Story
