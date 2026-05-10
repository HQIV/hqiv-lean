import Problems.YangMills.Millennium

/-!
# Small proved lemmas for Clay / Dojo spectral packaging

Pure bookkeeping: turning an explicit global upper bound on admissible gaps into
`FiniteMassSpectrum`.
-/

namespace Hqiv.Story

open MillenniumYangMills
open MillenniumYangMillsDefs

/-- If every spectral gap witnessed by `HasMassGapSpectrum` is bounded above by `M`, and `M > 0`,
    then `FiniteMassSpectrum` holds with witness `M`. -/
theorem FiniteMassSpectrum_of_global_bound {G : Type} [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (M : ℝ) (hM : 0 < M)
    (h : ∀ Δ : ℝ, HasMassGapSpectrum G qft Δ → Δ ≤ M) :
    FiniteMassSpectrum G qft :=
  ⟨M, hM, h⟩

end Hqiv.Story
