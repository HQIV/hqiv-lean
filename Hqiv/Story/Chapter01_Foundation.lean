import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField

/-!
# Story — Chapter 1: light cone and auxiliary field

**Read first.** Discrete null-lattice mode counts, curvature norm / `δ_E` ladder, reference shell `referenceM`,
and the auxiliary field `φ` on the temperature ladder `T(m) = 1/(m+1)` in natural units.

Downstream: `Chapter02_Metric` (HQVM metric built from the same data).

**Octonion Lie DOF (28 = dim so(8)):** the matrix generator closure and independence are not part of
this chapter’s imports, but the Story spine includes `Hqiv.Story.OctonionLieDOF` as the Lie-algebra DOF
hook, proved by re-export from `Hqiv.SO8ClosureInterface` (the same mathematics as `Hqiv.SO8Closure` /
`Hqiv.GeneratorsLieClosure` — build `HQIVSO8Closure` to warm the heavy shard precompile) parallel to the
QFT / Dojo track in later chapters.

## Mass-gap narrative (`Hqiv.Story.MassGap`)

**Output for Ch 2:** `MassGap.step01_lightConeAuxiliarySubstrate` — discrete null data + `φ` ladder the lapse layer is
supposed to consume (proved from `Hqiv.T_pos`, `Hqiv.phi_of_shell_pos` in this module).
-/

namespace Hqiv.Story.MassGap

open Hqiv

/-- **Ch 1 → 2.** Positive temperature ladder and auxiliary field on every shell (inputs to lapse / time-angle). -/
def step01_lightConeAuxiliarySubstrate : Prop :=
  (∀ m : ℕ, 0 < T m) ∧ (∀ m : ℕ, 0 < phi_of_shell m)

/-- Discharged from `AuxiliaryField` only (re-exports `OctonionicLightCone` via that import chain). -/
theorem step01_lightConeAuxiliarySubstrate_holds : step01_lightConeAuxiliarySubstrate :=
  ⟨fun m => T_pos m, fun m => phi_of_shell_pos m⟩

end Hqiv.Story.MassGap
