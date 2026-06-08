import Hqiv.Story.Chapter03_ConservedShell
import Hqiv.Physics.HarmonicLadderMass

/-!
# Story — Chapter 4: harmonic ladder and mass couplings

Shell index `m` → temperature → `φ` → `shell_shape` → effective `α` and hydrogenic-style binding
**without** triality (triality is later algebra chapters in the full repo graph).

Downstream: `Chapter05_Baryogenesis` (QCD/lock-in shell geometry and Ω_k).

## Mass-gap narrative

**Input:** `MassGap.step03_conservedContentInterface` (unused — ladder facts are unconditional here). **Output:**
`MassGap.step04_harmonicLadderSpectralAnchor` := `∀ …, harmonic_ladder_mass_coupling_chain` from
`Hqiv.Physics.HarmonicLadderMass`.
-/

namespace Hqiv.Story.MassGap

/-- **Ch 4 → 5.** Shell-resolved α_eff / binding (defeq to `harmonic_ladder_mass_coupling_chain`; expanded so
the `∀` body parses as a `Prop`, not a proof-ascription). -/
def step04_harmonicLadderSpectralAnchor : Prop :=
  ∀ (m : ℕ) (Z : ℕ) (μ : ℝ) (c : ℝ),
    Hqiv.Physics.alphaEffAtShell m c = (Hqiv.Physics.oneOverAlphaEffAtShell m c)⁻¹ ∧
      Hqiv.Physics.E_bind_atomic_shell_magnitude m Z μ c =
        μ * (Z : ℝ) ^ 2 * (Hqiv.Physics.oneOverAlphaEffAtShell m c)⁻¹ ^ 2 / 2

theorem step04_of_step03 (_ : step03_conservedContentInterface) : step04_harmonicLadderSpectralAnchor := by
  intro m Z μ c
  simpa using Hqiv.Physics.harmonic_ladder_mass_coupling_chain m Z μ c

end Hqiv.Story.MassGap
