import Hqiv.Story.S3MulModBSDCoefficientBridge
import Hqiv.Story.S3MulModBSDConvergenceRotationBridge
import Hqiv.Story.S3HarmonicHolonomyCriticalLineFrontier

/-!
# Mul-mod BSD rotation dual capstone — RH adjoint (45°) + L-series wall (90°)

Story-level bundle linking the **same** SO(4)/FE rotation machinery to two
landmarks:

| Track | Rotation | Vanishing locus | Formal anchor |
|-------|----------|-----------------|---------------|
| **RH / Hilbert–Pólya** | 45° (`rot45Free`) | `Re s = 1/2` | `harmonic_cascade_holonomy_transformer_adjoint_iff` |
| **BSD / coefficient** | 90° (`rot90Free`) | `Re s = 1` | `differentiableOn_mulModBSDLSeries` on `{Re s > 1}` |

Both are instances of `rotFree θ` on the functional-equation pair `(σ, 1−σ)`
(`S3RotationRigidity.rotation_angle_critical_line_vs_convergence_wall`).

The mul-mod BSD channel is therefore **dual-purpose**: prefix modularity / weak
Hecke on good shells (`MulModBSDCascadePrefixModularityObjectExtended`) shares
the geometric spine with the cascade holonomy operator used on the RH frontier.

**Not claimed:** identification of `mulModBSDLSeries` with `ζ(s)`, modularity,
or BSD.
-/

namespace Hqiv.Story

open Hqiv.Algebra Complex Real Matrix

noncomputable section

/--
Unified capstone: coefficient/L-series fit, prefix Hecke bundle, and the
45°/90° rotation bridge tying FE adjoint logic to the convergence wall.
-/
structure MulModBSDRotationDualCapstone where
  coefficient_channel : MulModBSDTransportCoefficientFit
  prefix_hecke : MulModBSDCascadePrefixModularityObjectExtended
  rotation_bridge : MulModBSDConvergenceRotationBridge
  fortyfive_is_critical : projectionLine (Real.pi / 4) = (1 / 2 : ℝ)
  ninety_is_convergence_wall : projectionLine (Real.pi / 2) = (1 : ℝ)
  holonomy_adjoint_on_line :
    ∀ {N : ℕ} (hN : 2 ≤ N) {s : ℂ},
      harmonicCascadeHolonomyTransformer N hN (1 - s) =
        (harmonicCascadeHolonomyTransformer N hN s)ᴴ ↔
          s.re = (1 / 2 : ℝ)
  lseries_beyond_wall :
    DifferentiableOn ℂ mulModBSDLSeries {s : ℂ | 1 < s.re}

noncomputable def mulMod_bsd_rotation_dual_capstone : MulModBSDRotationDualCapstone where
  coefficient_channel := mulMod_bsd_transport_coefficient_fit
  prefix_hecke := mulModBSD_cascade_prefix_modularity_extended
  rotation_bridge := mulMod_bsd_convergence_rotation_bridge
  fortyfive_is_critical := projectionLine_pi_div_four
  ninety_is_convergence_wall := projectionLine_pi_div_two
  holonomy_adjoint_on_line := fun {N} (hN : 2 ≤ N) {_s : ℂ} =>
    harmonic_cascade_holonomy_transformer_adjoint_iff (N := N) hN
  lseries_beyond_wall := differentiableOn_mulModBSDLSeries

def MulModBSDRotationDualCapstoneInhabited : Prop :=
  Nonempty MulModBSDRotationDualCapstone

theorem mulMod_bsd_rotation_dual_capstone_inhabited :
    MulModBSDRotationDualCapstoneInhabited :=
  ⟨mulMod_bsd_rotation_dual_capstone⟩

/--
**Angle ladder at story level:** 45° pins the FE critical line; 90° pins the
mul-mod absolute-convergence wall; the L-series is holomorphic beyond `Re s = 1`.
-/
theorem mulMod_bsd_rotation_pins_critical_line_and_convergence_wall :
    projectionLine (Real.pi / 4) = (1 / 2 : ℝ) ∧
      projectionLine (Real.pi / 2) = (1 : ℝ) ∧
        DifferentiableOn ℂ mulModBSDLSeries {s : ℂ | 1 < s.re} :=
  ⟨projectionLine_pi_div_four, projectionLine_pi_div_two, differentiableOn_mulModBSDLSeries⟩

/--
**Dual readout:** FE adjoint on cascade holonomy ⟺ critical line; 90° free
coordinate ⟺ right strip edge (`σ = 1`).
-/
theorem mulMod_bsd_dual_rotation_readouts (σ : ℝ) :
    (rotFree (Real.pi / 4) (functionalPair σ) = 0 ↔ σ = (1 / 2 : ℝ)) ∧
      (rot90Free (functionalPair σ) = 0 ↔ σ = (1 : ℝ)) :=
  ⟨mulMod_bsd_fortyfive_degree_pins_re_half σ, mulMod_bsd_ninety_degree_pins_re_one σ⟩

end

end Hqiv.Story
