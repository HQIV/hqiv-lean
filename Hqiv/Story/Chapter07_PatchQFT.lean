import Hqiv.Story.Chapter06_Fluid
import Hqiv.QuantumMechanics.PatchQFTBridge
import Hqiv.QuantumMechanics.PatchTopologicalObstruction

/-!
# Story — Chapter 7: patch QFT (support-restricted net, Minkowski chart)

Scaffold-level local algebra on `Fin 4` patches; abelian `smearedField` building blocks; pairing with
spacelike Minkowski geometry for microcausality-style *hooks*. The same finite-patch ontology
discharges instanton/theta/first-Chern/U(1)-winding sectors at the patch level. This is **not** the
non-abelian `QuantumYangMillsTheory` package in Lean Dojo’s YM file — it is a discrete/locality layer.

Downstream: `Chapter08_ClayMillennium` (formal YM/NS problem statements + witness wiring).

## Mass-gap narrative

**Input:** `MassGap.step06_continuumToWightmanScaffold` (narrative pin). **Output:**
`MassGap.step07_patchAbelianCommutator` — abelian patch operators have **zero** commutator
(`Hqiv.QM.patchAlgebraAt_opCommutator_zero`).  A Dojo-scale `QuantumYangMillsTheory` witness is **not**
proved here; see `Hqiv.Story.MassGap.step07_yangMillsWitnessBundle` in `Chapter08_ClayMillennium`.
-/

namespace Hqiv.Story.MassGap

open Hqiv.QM

/-- **Ch 7 (patch layer).** Abelian smeared operators on regions commute (`PatchQFTBridge`). -/
def step07_patchAbelianCommutator : Prop :=
  ∀ (R S : SpacetimeRegion) (A B : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4),
    A ∈ patchAlgebraAt R → B ∈ patchAlgebraAt S → opCommutator A B = 0

theorem step07_patchAbelianCommutator_holds : step07_patchAbelianCommutator :=
  fun _R _S _A _B hA hB => patchAlgebraAt_opCommutator_zero _A _B hA hB

theorem step07_of_step06 (_ : step06_continuumToWightmanScaffold) : step07_patchAbelianCommutator :=
  step07_patchAbelianCommutator_holds

/-- **Ch 7 (patch topology).** The finite patch has one topological sector, so instanton,
theta, first-Chern, U(1)-winding, and abelian commutator obstructions are absent at the patch level. -/
def step07_patchTopologicalObstructions : Prop :=
  PatchTopologicalObstructionsDischarged

theorem step07_patchTopologicalObstructions_holds : step07_patchTopologicalObstructions :=
  patchTopologicalObstructionsDischarged

end Hqiv.Story.MassGap
