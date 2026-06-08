import Hqiv.Physics.ActionHolonomyGlue
import Hqiv.Physics.FanoResonance

namespace Hqiv.Physics

/-!
# Discrete holonomy ↔ kinetic readout (abelian ℝ sector)

**Proved content today:** repackage `ActionHolonomyGlue` as the discrete **plaquette / Wilson-defect**
sandwich for `L_O_kinetic` on the minimal `Fin 4` cycle (per octonion channel `a : Fin 8`).

**Open (roadmap):** non-abelian matrix transport on the color chart, finite lattice Wilson loops whose
weight grows with a horizon-area readout such as `shellSurface m` / `detunedShellSurface m`, and any
identification with continuum confinement. Those require new definitions beyond this file.
-/

/-- Horizon-area **driver** shared with resonance ladders (`FanoResonance.shellSurface`).
    Intended use: future Wilson-loop / plaquette counting once a lattice link graph is fixed. -/
abbrev holonomyAreaDriver (m : ℕ) : ℝ :=
  shellSurface m

/-- Same sandwich as `L_O_kinetic_two_sided_cyclic_wilson_sq`, under a YM-facing name. -/
theorem discrete_kinetic_two_sided_cyclic_wilson (A : Fin 8 → Fin 4 → ℝ) (x : ℝ) :
    -(1 / 2 : ℝ) * ∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 ≤
        L_O_kinetic A ∧
      L_O_kinetic A ≤
        -(1 / 4 : ℝ) * ∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 :=
  L_O_kinetic_two_sided_cyclic_wilson_sq A x

end Hqiv.Physics
