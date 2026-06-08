import Hqiv.Story.PlasticPhaseBalanceImpliesReHalf

/-!
# Near-diagonal three signed cubes (dedicated slot)

The formal target `EverySufficientlyLargeIntegerIsNearDiagonalSumOfThreeSignedCubes` is
stated in `PlasticPhaseBalanceImpliesReHalf` and used in Sub-goal-1 packaging.
This module is a small anchor for future Diophantine lemmas so the story spine can
import this file alone once proofs are split out.

## Main definition

The canonical definition remains in `PlasticPhaseBalanceImpliesReHalf` to avoid
duplicate `def`s. Use that name, or the alias below, in downstream modules.
-/

namespace Hqiv.Story

/-- Alias pointing at the Sub-goal-1 Diophantine hypothesis (single source of truth). -/
abbrev NearDiagonalThreeCubesTarget : Prop :=
  EverySufficientlyLargeIntegerIsNearDiagonalSumOfThreeSignedCubes

end Hqiv.Story
