import Hqiv.Story.Chapter05_Baryogenesis
import Hqiv.Physics.HQIVFluidClosureScaffold

/-!
# Story — Chapter 6: effective fluid closure (HQIV / plasma scaffold)

Vocabulary toward classical NS (modified inertia, eddy viscosity, coefficient maps). **Not** a proof
of Fefferman (A)–(D); see `Hqiv.Bridge.LeanDojoClayMillennium` for the official Clay `Prop`s.

Downstream: `Chapter07_PatchQFT`.

## Mass-gap narrative

**Input:** `MassGap.step05_referenceShellGapWitness` (narrative pin). **Output:**
`MassGap.step06_continuumToWightmanScaffold` — a proved **sign** lemma for the HQIV eddy viscosity at
the lock-in shell (`hqivEddyViscosity_HQIV_shell_debye_nonneg`), not a Wightman construction.
-/

namespace Hqiv.Story.MassGap

open Hqiv Hqiv.Physics

/-- **Ch 6 → 7.** Nonnegative HQIV eddy viscosity at `m_lockin` with schematic Debye length (`HQIVFluidClosureScaffold`). -/
def step06_continuumToWightmanScaffold : Prop :=
  0 ≤ hqivEddyViscosity_HQIV_shell_debye m_lockin (0 : ℝ) (0 : ℝ)

theorem step06_continuumToWightmanScaffold_holds : step06_continuumToWightmanScaffold :=
  hqivEddyViscosity_HQIV_shell_debye_nonneg m_lockin (0 : ℝ) (0 : ℝ) (le_refl _)

theorem step06_of_step05 (_ : step05_referenceShellGapWitness) : step06_continuumToWightmanScaffold :=
  step06_continuumToWightmanScaffold_holds

end Hqiv.Story.MassGap
