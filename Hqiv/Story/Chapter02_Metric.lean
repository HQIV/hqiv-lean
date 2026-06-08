import Hqiv.Story.Chapter01_Foundation
import Hqiv.Geometry.HQVMetric

/-!
# Story — Chapter 2: HQVM metric

Lapse `N = 1 + Φ + φ·t`, monogamy coefficient `γ`, and the effective Friedmann interface on the same
horizon substrate as Chapter 1.

Downstream: `Chapter03_ConservedShell` (conservations forced by the metric structure).

## Mass-gap narrative

**Input:** `MassGap.step01_lightConeAuxiliarySubstrate`. **Output:** `MassGap.step02_metricConservationGate`
(monotone time-angle along each shell’s `φ(m)`; `Hqiv.HQVMetric.timeAngle_mono_t`).
-/

namespace Hqiv.Story.MassGap

open Hqiv

/-- **Ch 2 → 3.** HQVM time-angle `φ t` is monotone in `t` for each shell’s positive `φ(m)` (`HQVMetric`). -/
def step02_metricConservationGate : Prop :=
  ∀ (m : ℕ) (t₁ t₂ : ℝ), t₁ ≤ t₂ → timeAngle (phi_of_shell m) t₁ ≤ timeAngle (phi_of_shell m) t₂

theorem step02_of_step01 (h : step01_lightConeAuxiliarySubstrate) : step02_metricConservationGate := by
  rcases h with ⟨_, hφ⟩
  intro m t₁ t₂ ht
  exact timeAngle_mono_t _ _ _ (hφ m) ht

end Hqiv.Story.MassGap
