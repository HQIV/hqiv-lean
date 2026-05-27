import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.FanoLine

namespace Hqiv.Physics

open Hqiv

/-!
# Brane–bulk Fano-truss readout (HQIV-native)

Maps the discrete null-lattice **mode budget** to the resonance **shell-surface** driver and keeps
the Fano incidence package in the same import cone for narrative alignment with external
brane–bulk frameworks.

**Proved here:** \(A(m)=4(m+1)(m+2)\) as `Hqiv.available_modes`, and its equality with `4 * shellSurface m`.

**Not proved here:** auxetic elasticity, Poisson ratio \(\nu=-1\), or any continuum truss mechanics.
-/

/-- Discrete brane mode-area readout \(A(m)=4(m+1)(m+2)\): definitionally `Hqiv.available_modes`. -/
abbrev braneTrussModeArea (m : Nat) : ℝ :=
  available_modes m

theorem braneTrussModeArea_eq (m : Nat) :
    braneTrussModeArea m = (4 : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
  rw [braneTrussModeArea, available_modes_eq m]
  ring

theorem braneTrussModeArea_eq_four_mul_shellSurface (m : Nat) :
    braneTrussModeArea m = (4 : ℝ) * shellSurface m := by
  unfold braneTrussModeArea available_modes shellSurface latticeSimplexCount
  push_cast
  ring

end Hqiv.Physics
