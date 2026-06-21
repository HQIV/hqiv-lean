import Mathlib.LinearAlgebra.Matrix.ConjTranspose

import Hqiv.Algebra.MulModBSDLSeriesScaffold
import Hqiv.Story.S3FortyFiveProjection
import Hqiv.Story.S3HarmonicHolonomyCriticalLineFrontier
import Hqiv.Story.S3RotationRigidity

/-!
# Mul-mod BSD channel ↔ rotation angle ladder (45° vs 90°)

The SO(4)/strip geometry already separates two real-axis landmarks:

* **45° (`rot45Free`).**  Vanishing on the functional-equation pair `(σ, 1−σ)`
  occurs at `σ = 1/2` — the **critical line** (`S3FortyFiveProjection`,
  `S3RotationRigidity.projectionLine_pi_div_four`).  The cascade holonomy
  transformer satisfies its FE-adjoint law exactly on this line
  (`harmonic_cascade_holonomy_transformer_adjoint_iff`).

* **90° (`rot90Free`).**  Vanishing occurs at `σ = 1` — the **right strip edge**
  where absolute convergence of Dirichlet series is traditionally tested.
  The mul-mod coefficient stream is bounded with abscissa `≤ 1`, and
  `mulModBSDLSeries` is holomorphic on the open half-plane `{Re s > 1}`.

This module packages the **honest bridge**: the same rotation formalism that
localizes FE symmetry at 45° localizes the BSD-facing convergence wall at 90°.
It does **not** identify `mulModBSDLSeries` with `ζ(s)` or prove modularity.
-/

namespace Hqiv.Story

open Hqiv.Algebra Complex Real Matrix

noncomputable section

/--
Rotation-angle identification for the mul-mod BSD coefficient channel:
critical line (45°) vs absolute-convergence wall (90°).
-/
structure MulModBSDConvergenceRotationBridge where
  fortyfive_pins_critical_line :
    projectionLine (Real.pi / 4) = (1 / 2 : ℝ)
  ninety_pins_convergence_wall :
    projectionLine (Real.pi / 2) = (1 : ℝ)
  rot90_vanishes_at_sigma_one :
    ∀ σ : ℝ, rot90Free (functionalPair σ) = 0 ↔ σ = (1 : ℝ)
  rot45_vanishes_at_sigma_half :
    ∀ σ : ℝ, rotFree (Real.pi / 4) (functionalPair σ) = 0 ↔ σ = (1 / 2 : ℝ)

noncomputable def mulMod_bsd_convergence_rotation_bridge : MulModBSDConvergenceRotationBridge where
  fortyfive_pins_critical_line := projectionLine_pi_div_four
  ninety_pins_convergence_wall := projectionLine_pi_div_two
  rot90_vanishes_at_sigma_one := fun σ => rot90Free_functionalPair_eq_zero_iff σ
  rot45_vanishes_at_sigma_half := fun σ => by
    rw [rotFree_pi_div_four]
    exact rot45Free_functionalPair_eq_zero_iff σ

theorem mulMod_bsd_ninety_degree_pins_re_one (σ : ℝ) :
    rot90Free (functionalPair σ) = 0 ↔ σ = (1 : ℝ) :=
  mulMod_bsd_convergence_rotation_bridge.rot90_vanishes_at_sigma_one σ

theorem mulMod_bsd_fortyfive_degree_pins_re_half (σ : ℝ) :
    rotFree (Real.pi / 4) (functionalPair σ) = 0 ↔ σ = (1 / 2 : ℝ) :=
  mulMod_bsd_convergence_rotation_bridge.rot45_vanishes_at_sigma_half σ

theorem mulMod_bsd_rotation_angle_ladder :
    projectionLine (Real.pi / 4) = (1 / 2 : ℝ) ∧
      projectionLine (Real.pi / 2) = (1 : ℝ) :=
  rotation_angle_critical_line_vs_convergence_wall

theorem mulMod_bsd_holonomy_adjoint_iff_critical_line {N : ℕ} (hN : 2 ≤ N) {s : ℂ} :
    harmonicCascadeHolonomyTransformer N hN (1 - s) =
      (harmonicCascadeHolonomyTransformer N hN s)ᴴ ↔
        s.re = (1 / 2 : ℝ) :=
  harmonic_cascade_holonomy_transformer_adjoint_iff hN

theorem mulMod_bsd_lseries_holomorphic_beyond_re_one :
    DifferentiableOn ℂ mulModBSDLSeries {s : ℂ | 1 < s.re} :=
  differentiableOn_mulModBSDLSeries

def MulModBSDConvergenceRotationCapstone : Prop :=
  Nonempty MulModBSDConvergenceRotationBridge

theorem mulMod_bsd_convergence_rotation_capstone : MulModBSDConvergenceRotationCapstone :=
  ⟨mulMod_bsd_convergence_rotation_bridge⟩

end

end Hqiv.Story
