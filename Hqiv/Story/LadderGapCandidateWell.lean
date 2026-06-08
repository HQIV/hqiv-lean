import Hqiv.Physics.BaryogenesisCore
import Hqiv.Algebra.IntegerLatticeShellCount8

/-!
# Ladder gap scale + finite mode bound (no Story completion / Clay imports)

`MillenniumBridgePatchPoincareWightman` needs a **positive** ladder-derived Hamiltonian scale
`ladderGapCandidate` and the lock-in mode-count proxy `finiteModeBoundAtLockin = r8 m_lockin`.

Those definitions previously lived in `SketchesConsumedLadderWell`, which also imported
`DiscreteOMaxwellHQIVInstance` and therefore the **`MassGapCompletionBundle` → `Chapter08`**
transitive chain. That created an import cycle once `Chapter08` (or anything upstream of
`MassGapCompletionBundle`) needed the patch Wightman / HQIV QFT stack.

This module **isolates** the ladder-only lemmas on **`BaryogenesisCore`** + **`IntegerLatticeShellCount8`**
so patch Schwartz modules can import it **without** pulling the mass-gap completion spine.

Downstream: `SketchesConsumedLadderWell` re-uses the same names in `Hqiv.Story`; `MillenniumBridgePatchPoincareWightman`
imports **only** this file for `ladderGapCandidate` / `ladderGapCandidate_pos`.
-/

namespace Hqiv.Story

open Hqiv
open Hqiv.Algebra

noncomputable section

/-- Sketch-consumed ladder gap candidate at lock-in.
Positive factorization mirrors the intent of `DeltaPositiveFromLadder.lean`. -/
noncomputable def ladderGapCandidate : ℝ :=
  (shell_shape_abs m_lockin) * (T m_lockin) * (1 / 2 : ℝ)

/-- Consumed sketch result: the ladder gap candidate is strictly positive. -/
theorem ladderGapCandidate_pos : 0 < ladderGapCandidate := by
  unfold ladderGapCandidate
  exact mul_pos (mul_pos (shell_shape_abs_pos m_lockin) (T_pos m_lockin)) (by norm_num)

/-- Sketch-consumed finite shell-mode control at lock-in. -/
def finiteModeBoundAtLockin : ℕ := r8 m_lockin

/-- The shell-mode control value is strictly positive. -/
theorem finiteModeBoundAtLockin_pos : 0 < finiteModeBoundAtLockin :=
  r8_pos m_lockin

/-- Finite mode-control can be viewed as an explicit upper-bound witness value. -/
theorem finiteModeBoundAtLockin_is_finite : ∃ M : ℕ, M = finiteModeBoundAtLockin := by
  exact ⟨finiteModeBoundAtLockin, rfl⟩

end

end Hqiv.Story
