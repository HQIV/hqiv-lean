import Hqiv.Story.OctonionLieDOF
import Hqiv.Physics.RapidityZetaPhaseBridge

/-!
# Toward `CompactSimpleGaugeGroup G` from O–Maxwell + SO(8) closure + rapidity

The Dojo `CompactSimpleGaugeGroup` class (`Problems.YangMills.Quantum`) requires a **topological
group** type `G`, a finite-dimensional normed real `lie_algebra`, compactness, and a bespoke
simplicity predicate. HQIV’s proved **matrix Lie algebra** backbone (28 `so8Generator` directions,
closure under `lieBracket`, linear independence) and the **rapidity ↔ δθ′ phase** identity live in a
different layer of statements until that group model is built.

This module wires the two **Story-accessible** certificates you named:

* **SO(8) closure (octonion derived):** `OctonionLieDOF.octonion_so8_lie_backbone` (re-export of the
  closure pack; heavy build: `lake build HQIVSO8Closure`).
* **Rapidity / zeta phase:** `Hqiv.Physics.zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity`
  (`RapidityZetaPhaseBridge` — polar-angle scaffold from `SpatialSliceRapidityScaffold`).

**O–Maxwell (continuum φ–Maxwell):** not imported here (keeps this file’s graph lighter than
`Hqiv.Physics.HQIVYangMillsPackage`). Compose `Hqiv.Physics.LightConeMaxwellQFTBridge` /
`Hqiv.Physics.PromotedOMaxwell` at call sites when you need the null-ladder → continuum Maxwell
pipeline in the same narrative arc (`MassGapWiring` dependency table).

**SM / unification + single `hqivYangMillsPackage` bundle:** `Hqiv.Physics.HQIVYangMillsPackage` packages
SO(8) span facts, SM generator membership, `alpha_gamma_forced`, rapidity phase, and
`YangMills_SM_GR_Unification_statement` in one structure — import that module when you want the full
physics object rather than the two lemmas below.

**SO(8) `G` slot (matrix subgroup):** `Hqiv.Story.HQIVSO8GaugeGroupConstruction` packages
`HQIVSO8Gauge = ↥(Matrix.specialOrthogonalGroup (Fin 8) ℝ)`, compactness, a normed `Fin 28`
`lie_algebra`, and explicit non-abelian permutations; `IsSimpleLieGroup.no_normal_subgroups` is still
`sorry` there (Lie correspondence not one-step in Mathlib). The `S₃` sketch in
`GaugeGroupFromHQIVSketch` remains the minimal bridge-sized `CompactSimpleGaugeGroup`.
-/

namespace Hqiv.Story

/-- SO(8) matrix Lie backbone: skew-adjoint generators, bracket closure in their span, independence. -/
abbrev hqiv_gauge_so8_lie_backbone :=
  octonion_so8_lie_backbone

/-- Rapidity oracle phase alignment for the zeta phase channel (`RapidityZetaPhaseBridge`). -/
theorem hqiv_gauge_rapidity_zeta_phase (φ t : ℝ) (m : ℕ) :
    Complex.I * φ * t * Hqiv.delta_theta_prime (m : ℝ) =
      Complex.I * (Hqiv.Geometry.polarAngleFromRapidity φ t m : ℂ) :=
  Hqiv.Physics.zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity φ t m

end Hqiv.Story
