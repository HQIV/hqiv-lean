import Hqiv.Algebra.MulModHodgeLift
import Hqiv.Story.S3AlphaDimUnitSplitProjection
import Hqiv.Story.S3MulModBSDConvergenceRotationBridge
import Hqiv.Story.S3MulModBSDRotationDualCapstone

/-!
# Mul-mod Hodge-lift ↔ rotation filtration (45° vs 90°)

Packages the **same** SO(4)/strip rotation ladder used for RH/BSD dual capstones as a
Hodge-flavored readout on mul-mod cascade data:

* **45° (`rot45Free`).**  Filtration / adjoint step — pins `σ = 1/2` (`projectionLine (π/4)`).
  On good prefix shells, numerator rigidity `(index) · coeff = 6` is the proved
  integrality analog (`MulModHodgeLift`).

* **90° (`rot90Free`).**  Weight / convergence step — pins `σ = 1`; `mulModBSDLSeries` is
  holomorphic beyond `Re s = 1`.

* **Bad shell `p = 7`.**  Tamagawa analog records RP excess and normalized residue `6/7` —
  narrative analog of limiting mixed structure / monodromy at bad reduction.

Does **not** prove the Hodge conjecture, modularity, or BSD.
-/

namespace Hqiv.Story

open Hqiv.Algebra Complex Real Matrix

noncomputable section

/--
Hodge-flavored rotation bridge: mul-mod lift + 45°/90° landmarks + good rigidity / bad defect.
-/
structure MulModHodgeRotationBridge where
  hodge_lift : MulModHodgeLift
  rotation_bridge : MulModBSDConvergenceRotationBridge
  fortyfive_filtration : projectionLine (Real.pi / 4) = (1 / 2 : ℝ)
  ninety_weight : projectionLine (Real.pi / 2) = (1 : ℝ)
  good_prefix_numerator_rigid :
    ∀ {n : ℕ} (hn : 0 < n), IsHarmonicCascadeGoodCompositeShell n →
      (n : ℝ) * mulModBSDLocalResidueCoeffReal n hn = 6
  bad_shell_ramanujan_fails : ¬ MulModBSDRamanujanPeterssonAt 7 Nat.prime_seven

noncomputable def mulMod_hodge_rotation_bridge : MulModHodgeRotationBridge where
  hodge_lift := mulMod_hodge_lift_default
  rotation_bridge := mulMod_bsd_convergence_rotation_bridge
  fortyfive_filtration := projectionLine_pi_div_four
  ninety_weight := projectionLine_pi_div_two
  good_prefix_numerator_rigid := fun hn h =>
    mulMod_hodge_good_prefix_numerator_rigid hn h
  bad_shell_ramanujan_fails :=
    mulMod_hodge_lift_default.bad_shell_defect.shell.ramanujan_fails

theorem mulMod_hodge_fortyfive_pins_filtration :
    projectionLine (Real.pi / 4) = (1 / 2 : ℝ) :=
  mulMod_hodge_rotation_bridge.fortyfive_filtration

theorem mulMod_hodge_ninety_pins_weight_wall :
    projectionLine (Real.pi / 2) = (1 : ℝ) :=
  mulMod_hodge_rotation_bridge.ninety_weight

theorem mulMod_hodge_fortyfive_implies_good_prefix_rigidity {n : ℕ} (hn : 0 < n)
    (h : IsHarmonicCascadeGoodCompositeShell n) :
    (n : ℝ) * mulModBSDLocalResidueCoeffReal n hn = 6 :=
  mulMod_hodge_rotation_bridge.good_prefix_numerator_rigid hn h

theorem mulMod_hodge_bad_shell_defect_fails_purity :
    ¬ MulModBSDRamanujanPeterssonAt 7 Nat.prime_seven :=
  mulMod_hodge_rotation_bridge.bad_shell_ramanujan_fails

/--
On good shells the 45° filtration landmark aligns with prefix numerator rigidity; at the
bad Fano shell the defect measures failure of the good-prefix Ramanujan bound.
-/
theorem mulMod_hodge_filtration_rigidity_vs_bad_defect :
    (∀ {n : ℕ} (hn : 0 < n), IsHarmonicCascadeGoodCompositeShell n →
        (n : ℝ) * mulModBSDLocalResidueCoeffReal n hn = 6) ∧
      (¬ MulModBSDRamanujanPeterssonAt 7 Nat.prime_seven) :=
  ⟨fun hn h => mulMod_hodge_fortyfive_implies_good_prefix_rigidity hn h,
    mulMod_hodge_bad_shell_defect_fails_purity⟩

theorem mulMod_hodge_holonomy_adjoint_on_critical_line {N : ℕ} (hN : 2 ≤ N) {s : ℂ} :
    harmonicCascadeHolonomyTransformer N hN (1 - s) =
      (harmonicCascadeHolonomyTransformer N hN s)ᴴ ↔
        s.re = (1 / 2 : ℝ) :=
  mulMod_bsd_holonomy_adjoint_iff_critical_line hN

def MulModHodgeRotationCapstone : Prop :=
  Nonempty MulModHodgeRotationBridge

theorem mulMod_hodge_rotation_capstone : MulModHodgeRotationCapstone :=
  ⟨mulMod_hodge_rotation_bridge⟩

/--
Unified capstone: BSD rotation dual + mul-mod Hodge lift + rotation bridge.
-/
structure MulModHodgeRotationDualCapstone where
  bsd_dual : MulModBSDRotationDualCapstone
  hodge_rotation : MulModHodgeRotationBridge

noncomputable def mulMod_hodge_rotation_dual_capstone : MulModHodgeRotationDualCapstone where
  bsd_dual := mulMod_bsd_rotation_dual_capstone
  hodge_rotation := mulMod_hodge_rotation_bridge

def MulModHodgeRotationDualCapstoneInhabited : Prop :=
  Nonempty MulModHodgeRotationDualCapstone

theorem mulMod_hodge_rotation_dual_capstone_inhabited :
    MulModHodgeRotationDualCapstoneInhabited :=
  ⟨mulMod_hodge_rotation_dual_capstone⟩

/-! ## 4D fibre imprint row for the BSD-facing Hodge channel -/

/--
Four-dimensional fibre upgrade: the dimension-indexed imprint row `α₄ = 4/7`
is packaged with the BSD-facing Hodge rotation bridge.  This records the clean
4D/Hodge carrier without changing the physical 3D lattice row `α₃ = 3/5`.
-/
structure FourDimBSDHodgeImprintBridge where
  four_dim_budget : TransverseDim.FourDimHodgeImprintBudgetWitness
  hodge_rotation : MulModHodgeRotationBridge
  alpha_four : TransverseDim.imprintAlpha ⟨4, by decide⟩ = 4 / 7
  gamma_four : TransverseDim.overlapGamma ⟨4, by decide⟩ = 3 / 7
  denom_four : TransverseDim.imprintDenom ⟨4, by decide⟩ = 7
  so4_lie_dim_six : TransverseDim.soLieDim 4 = 6
  fortyfive_filtration : projectionLine (Real.pi / 4) = (1 / 2 : ℝ)
  ninety_weight_wall : projectionLine (Real.pi / 2) = (1 : ℝ)

noncomputable def fourDim_bsd_hodge_imprint_bridge : FourDimBSDHodgeImprintBridge where
  four_dim_budget := TransverseDim.fourDimHodgeImprintBudgetWitness_holds
  hodge_rotation := mulMod_hodge_rotation_bridge
  alpha_four := TransverseDim.imprintAlpha_four
  gamma_four := TransverseDim.overlapGamma_four
  denom_four := TransverseDim.imprintDenom_four
  so4_lie_dim_six := TransverseDim.soLieDim_four
  fortyfive_filtration := mulMod_hodge_fortyfive_pins_filtration
  ninety_weight_wall := mulMod_hodge_ninety_pins_weight_wall

theorem fourDim_bsd_hodge_alpha_four :
    TransverseDim.imprintAlpha ⟨4, by decide⟩ = 4 / 7 :=
  fourDim_bsd_hodge_imprint_bridge.alpha_four

theorem fourDim_bsd_hodge_gamma_four :
    TransverseDim.overlapGamma ⟨4, by decide⟩ = 3 / 7 :=
  fourDim_bsd_hodge_imprint_bridge.gamma_four

theorem fourDim_bsd_hodge_rotation_landmarks :
    projectionLine (Real.pi / 4) = (1 / 2 : ℝ) ∧
      projectionLine (Real.pi / 2) = (1 : ℝ) :=
  ⟨fourDim_bsd_hodge_imprint_bridge.fortyfive_filtration,
    fourDim_bsd_hodge_imprint_bridge.ninety_weight_wall⟩

/--
The bad Fano-shell normalized residue is not arbitrary in the 4D fibre reading:
`6/7 = 2γ₄ = 1 - 1/7`.  This reinterprets the defect as the four-dimensional
boundary complement; it does **not** make Ramanujan--Petersson true at `p = 7`.
-/
theorem fourDim_bad_shell_residue_eq_two_gamma_four :
    mulModBSDLocalResidueCoeffReal 7 (by decide) =
      (2 : ℝ) * (TransverseDim.overlapGamma ⟨4, by decide⟩ : ℝ) := by
  rw [mulMod_hodge_lift_default.bad_shell_defect.normalized_residue,
    TransverseDim.overlapGamma_four]
  norm_num

theorem fourDim_bad_shell_residue_eq_one_minus_denominator_skew :
    mulModBSDLocalResidueCoeffReal 7 (by decide) =
      1 - (1 : ℝ) / (TransverseDim.imprintDenom ⟨4, by decide⟩ : ℝ) := by
  rw [mulMod_hodge_lift_default.bad_shell_defect.normalized_residue,
    TransverseDim.imprintDenom_four]
  norm_num

theorem fourDim_bad_shell_trace_eq_denom_minus_one :
    mulModBSDPrimeHolonomyTrace 7 Nat.prime_seven =
      TransverseDim.imprintDenom ⟨4, by decide⟩ - 1 := by
  rw [mulModBSDPrimeHolonomyTrace_seven, TransverseDim.imprintDenom_four]

/--
The 4D row resolves the *meaning* of the bad residue while preserving the proved
RP failure.  This is the scoped answer to the BSD bad-shell audit: `α₄` organizes
the defect but does not erase it.
-/
structure FourDimBadResidueResolution where
  four_dim_bridge : FourDimBSDHodgeImprintBridge
  residue_eq_two_gamma_four :
    mulModBSDLocalResidueCoeffReal 7 (by decide) =
      (2 : ℝ) * (TransverseDim.overlapGamma ⟨4, by decide⟩ : ℝ)
  residue_eq_boundary_complement :
    mulModBSDLocalResidueCoeffReal 7 (by decide) =
      1 - (1 : ℝ) / (TransverseDim.imprintDenom ⟨4, by decide⟩ : ℝ)
  trace_eq_denom_minus_one :
    mulModBSDPrimeHolonomyTrace 7 Nat.prime_seven =
      TransverseDim.imprintDenom ⟨4, by decide⟩ - 1
  rp_still_fails : ¬ MulModBSDRamanujanPeterssonAt 7 Nat.prime_seven

noncomputable def fourDim_bad_residue_resolution : FourDimBadResidueResolution where
  four_dim_bridge := fourDim_bsd_hodge_imprint_bridge
  residue_eq_two_gamma_four := fourDim_bad_shell_residue_eq_two_gamma_four
  residue_eq_boundary_complement := fourDim_bad_shell_residue_eq_one_minus_denominator_skew
  trace_eq_denom_minus_one := fourDim_bad_shell_trace_eq_denom_minus_one
  rp_still_fails := mulMod_hodge_bad_shell_defect_fails_purity

def FourDimBadResidueResolutionInhabited : Prop :=
  Nonempty FourDimBadResidueResolution

theorem fourDim_bad_residue_resolution_inhabited :
    FourDimBadResidueResolutionInhabited :=
  ⟨fourDim_bad_residue_resolution⟩

def FourDimBSDHodgeImprintBridgeInhabited : Prop :=
  Nonempty FourDimBSDHodgeImprintBridge

theorem fourDim_bsd_hodge_imprint_bridge_inhabited :
    FourDimBSDHodgeImprintBridgeInhabited :=
  ⟨fourDim_bsd_hodge_imprint_bridge⟩

end

end Hqiv.Story
