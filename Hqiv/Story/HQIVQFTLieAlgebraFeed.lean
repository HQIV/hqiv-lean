import Hqiv.GeneratorsFromAxioms

/-!
# Matrix Lie data feeding HQIV QFT (without the SO(8) **closure proof** chain)

The full **Lie closure** certificate (bracket coefficients in the `so8Generator` span + linear
independence) is proved in `Hqiv.GeneratorsLieClosure` and surfaced in Story through
`Hqiv.Story.OctonionLieDOF` → `Hqiv.SO8ClosureInterface` (build `lake build HQIVSO8Closure` for a
cold cache).

This module is intentionally **narrower**: it imports only `Hqiv.GeneratorsFromAxioms`, so HQIV QFT
and Yang–Mills **bridge** code can cite the **octonion-first** objects and the skew-adjointness
consequences that are proved **before** the heavy closure shards:

* target dimension `lieClosureDim = 28` (matches `so8GeneratorCount`);
* the **phase-lift** matrix `phaseLiftDelta` is skew-adjoint;
* each `so8Generator k` is skew-adjoint (`Generators.so8Generator_antisymm`);
* explicit **G₂** commutator seeds `g2_comm_*` and `phaseLiftDelta` are the `G₂ ∪ {Δ}` matrix story
  used in `GeneratorsFromAxioms` / `OMaxwellAlgebraSeed` (algebra layer, not the Dojo
  `CompactSimpleGaugeGroup` slot).

The **combined** closure proposition `Hqiv.generators_from_octonion_closure` is only **named**
here; discharging it still requires `OctonionLieDOF` (or importing `SO8ClosureInterface` directly).
-/

namespace Hqiv.Story

open Matrix

open Hqiv

/-- Same as `lieClosureDim`; convenient name when discussing finite-dimensional gauge DOF next to
`QuantumYangMillsTheory`. -/
theorem hqivMatrixGaugeLieTargetDim : lieClosureDim = 28 :=
  rfl

/-- Re-export: each `so8Generator` is skew-symmetric (proved in `Hqiv.Generators`, no Lie-closure
data). -/
theorem hqiv_so8Generator_skewAdjoint (k : Fin 28) :
    so8Generator k + (so8Generator k)ᵀ = 0 :=
  so8Generator_antisymm k

/-- Phase-lift Δ is skew-adjoint as an 8×8 matrix. -/
theorem hqiv_phaseLiftDelta_skewAdjoint : phaseLiftDelta + (phaseLiftDelta)ᵀ = 0 := by
  ext i j
  simpa [Matrix.add_apply, Matrix.transpose_apply] using phaseLiftDelta_antisymm i j

/-- Packaging statement for the full octonion closure target (proved elsewhere). -/
abbrev HQIVGeneratorsFromOctonionClosureStatement : Prop :=
  generators_from_octonion_closure

end Hqiv.Story
