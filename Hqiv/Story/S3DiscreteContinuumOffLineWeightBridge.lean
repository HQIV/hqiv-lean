import Hqiv.Story.S3DBNDiscreteContinuumComparison
import Hqiv.Story.S3DBNConstantPort
import Hqiv.Story.S3HeatFlowArrowNoBackprojection
import Hqiv.Story.S3SpectralResonanceChanneling
import Hqiv.Story.S3SO4InteriorWitness

/-!
# Discrete→continuous press vs off-line weight debt — bridge capstone

This module packages the synthesis discussed after
`S3DBNDiscreteContinuumComparison`:

1. **Anchor discrete dominance (proved).**  On `Re s > 1`, forward lattice
   sums dominate backward continuum deformation
   (`discrete_dominates_continuum_anchor`); the horizon shell weight is
   flow-invariant (`hqivHeatKernelWeight_horizon`).

2. **Escape via backprojection forbidden (proved).**  Backward heat weights
   expand and are unbounded along the ladder; the thermodynamic arrow keeps
   deformation nonnegative (`arrow_forbids_backprojection`).

3. **Off-line zero weight debt (proved).**  At any nontrivial zero with
   `Re ρ ≠ 1/2`, the strip factorization forces `interiorStripH ρ = 0`: the
   free assembly must absorb the entire cancellation
   (`offline_zero_forces_assembly_vanish`).

The **capstone** is that the geometric channel always absorbs zeros — the
interior assembly stays nonzero off the line at nontrivial zeros:

`InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH`.

Equivalently: off-line weight debt is never payable at a real zero, because
forward discrete press outruns backward escape before backprojection can
restore an off-line channel.

**Honesty.**  Faces (1–3) are unconditional.  Extending anchor dominance into
the critical strip with zero-tracking is exactly `dbnLambda ≤ lambdaHQIV`
(`StripLatticeDominatesContinuum`), proved equivalent to RH given the classical
dBN imports.  The capstone itself is equivalent to RH
(`geometric_channel_absorption_iff_RH`).  This module names both frontiers and
shows they are the same target as the vaporization / on-line localization
payloads already in the repo.
-/

namespace Hqiv.Story

open Hqiv.Physics

noncomputable section

/-! ## Named faces of the press-vs-escape picture -/

/-- Off-line nontrivial zeros force the interior assembly to vanish (weight debt). -/
def OffLineZeroCarriesInteriorWeightDebt : Prop :=
  ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ρ.re ≠ (1 / 2 : ℝ) → interiorStripH ρ = 0

/-- Thermodynamic forward arrow plus unbounded backward shell weights. -/
def EscapeViaBackprojectionForbidden : Prop :=
  (∀ u : Fin 3 → ℝ, ¬ arrowDeformationCycle3 u < 0) ∧
    (∀ τ T_ref : ℝ, τ < 0 → 0 < T_ref →
      ∀ C : ℝ, ∃ m : ℕ, C < hqivHeatKernelWeight τ T_ref m)

/-- Anchor-region discrete dominance over backward continuum readout. -/
def AnchorDiscreteDominatesBackwardContinuum : Prop :=
  ∀ (τ T_ref δ t' t σ : ℝ) (z : ℝ),
    0 ≤ τ → 0 < T_ref → 0 ≤ δ → (∀ m, RindlerDenDeltaPos δ m) → 1 < σ → t ≤ 0 →
      ∃ c : ℝ, 0 < c ∧
        c * ‖dbnHeatFamily t (z : ℂ)‖ ≤
          ‖HQIVDeformedSum τ T_ref δ 0 t' (σ : ℂ)‖

/-- Geometric channel absorption: interior assembly nonzero off-line at zeros. -/
def GeometricChannelAbsorbsAllZeros : Prop :=
  InteriorAssemblyNonzeroAtNontrivialZerosOffLine interiorStripH

/--
Strip extension of anchor dominance: the classical dBN constant is dominated
by the proved discrete λ-lock (`lambdaHQIV = 0`).
-/
def StripLatticeDominatesContinuum (W : TempLadderFiniteWindowConcrete) : Prop :=
  dbnLambda ≤ (W.toLambdaHQIVZero).lambdaHQIV

/-- The capstone bridge: proved ladder lock + geometric absorption. -/
structure OffLineWeightPressBridge (W : TempLadderFiniteWindowConcrete) where
  lambda_zero : (W.toLambdaHQIVZero).lambdaHQIV = 0
  geometric_absorption : GeometricChannelAbsorbsAllZeros

/-! ## Unconditional faces (proved today) -/

theorem off_line_zero_carries_interior_weight_debt :
    OffLineZeroCarriesInteriorWeightDebt :=
  fun _ h hσ => offline_zero_forces_assembly_vanish h hσ

theorem escape_via_backprojection_forbidden :
    EscapeViaBackprojectionForbidden :=
  ⟨fun u => arrow_forbids_backprojection u,
   fun _ _ hτ hT C => backprojection_weight_unbounded hτ hT C⟩

theorem anchor_discrete_dominates_backward_continuum :
    AnchorDiscreteDominatesBackwardContinuum :=
  fun τ T_ref δ t' t σ z hτ hT hδ hden hσ ht =>
    discrete_dominates_continuum_anchor τ T_ref δ t' t σ hτ hT hδ hden hσ ht z

theorem unconditional_off_line_weight_press_faces :
    OffLineZeroCarriesInteriorWeightDebt ∧
      EscapeViaBackprojectionForbidden ∧
        AnchorDiscreteDominatesBackwardContinuum :=
  ⟨off_line_zero_carries_interior_weight_debt,
   escape_via_backprojection_forbidden,
   anchor_discrete_dominates_backward_continuum⟩

/-! ## Capstone recharacterizations -/

/--
**Weight debt vs geometric absorption.**  The capstone is exactly the
statement that no nontrivial zero can sit off-line: off-line zeros *always*
force `interiorStripH = 0`, so requiring nonzero assembly off-line is the
same as requiring every zero on `Re = 1/2`.
-/
theorem geometric_absorption_iff_all_zeros_on_line :
    GeometricChannelAbsorbsAllZeros ↔ AllNontrivialZerosOnLine := by
  constructor
  · intro h ρ hzz
    by_contra hne
    have hdebt := offline_zero_forces_assembly_vanish hzz hne
    exact h ρ hzz hne hdebt
  · intro h ρ hzz hσ _hne
    exact absurd (h ρ hzz) hσ

theorem geometric_absorption_iff_RH :
    GeometricChannelAbsorbsAllZeros ↔ RiemannHypothesis :=
  geometric_channel_absorption_iff_RH

theorem strip_lattice_dominates_iff_RH
    (hRT : RodgersTaoStatement) (hN : NewmanDBNStatement)
    (W : TempLadderFiniteWindowConcrete) :
    StripLatticeDominatesContinuum W ↔ RiemannHypothesis := by
  unfold StripLatticeDominatesContinuum
  exact concrete_lattice_dominates_iff_RiemannHypothesis hRT hN W

/-! ## Bridge packaging -/

theorem lambda_zero_of_offLineWeightPressBridge
    {W : TempLadderFiniteWindowConcrete} (_B : OffLineWeightPressBridge W) :
    (W.toLambdaHQIVZero).lambdaHQIV = 0 :=
  _B.lambda_zero

theorem RiemannHypothesis_of_offLineWeightPressBridge
    {W : TempLadderFiniteWindowConcrete} (B : OffLineWeightPressBridge W) :
    RiemannHypothesis :=
  geometric_absorption_iff_RH.mp B.geometric_absorption

def offLineWeightPressBridge_of_RH
    (W : TempLadderFiniteWindowConcrete) (hRH : RiemannHypothesis) :
    OffLineWeightPressBridge W where
  lambda_zero := lambdaHQIV_eq_zero_of_finiteWindowConcrete W
  geometric_absorption := geometric_absorption_iff_RH.mpr hRH

/--
**Capstone ↔ RH.**  The proved ladder λ-lock is free; inhabiting the bridge
is exactly the geometric-absorption capstone, hence RH.
-/
theorem offLineWeightPressBridge_iff_RiemannHypothesis
    (W : TempLadderFiniteWindowConcrete) :
    Nonempty (OffLineWeightPressBridge W) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨B⟩
    exact RiemannHypothesis_of_offLineWeightPressBridge B
  · intro hRH
    exact ⟨offLineWeightPressBridge_of_RH W hRH⟩

/--
**Same frontier, discrete→continuous wording.**  Given the classical dBN
imports, strip lattice dominance and geometric absorption are both equivalent
to RH — the anchor comparison pushes up to that named bound, not beyond it
without the capstone.
-/
theorem strip_dominance_and_geometric_absorption_same_frontier
    (hRT : RodgersTaoStatement) (hN : NewmanDBNStatement)
    (W : TempLadderFiniteWindowConcrete) :
    (StripLatticeDominatesContinuum W ↔ RiemannHypothesis) ∧
      (GeometricChannelAbsorbsAllZeros ↔ RiemannHypothesis) :=
  ⟨strip_lattice_dominates_iff_RH hRT hN W, geometric_absorption_iff_RH⟩

/--
**Logical shape of the synthesis (unconditional part).**  If a nontrivial
zero were off-line, the weight-debt face forces `interiorStripH = 0`; the
capstone forbids that.  The discrete press faces (anchor dominance + no
backprojection) are proved independently and match the strip extension and
vaporization bridges already recorded elsewhere.
-/
theorem off_line_zero_weight_debt_contradicts_capstone
    (hCap : GeometricChannelAbsorbsAllZeros) {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) (hσ : ρ.re ≠ (1 / 2 : ℝ)) :
    False := by
  have hdebt := off_line_zero_carries_interior_weight_debt ρ hρ hσ
  exact hCap ρ hρ hσ hdebt

theorem capstone_forbids_off_line_nontrivial_zeros
    (hCap : GeometricChannelAbsorbsAllZeros) :
    ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ρ.re = (1 / 2 : ℝ) :=
  (geometric_absorption_iff_all_zeros_on_line.mp hCap)

/-!
## Status

| Layer | Content | Status |
|-------|---------|--------|
| Anchor dominance | `AnchorDiscreteDominatesBackwardContinuum` | **Proved** |
| No backprojection | `EscapeViaBackprojectionForbidden` | **Proved** |
| Off-line weight debt | `OffLineZeroCarriesInteriorWeightDebt` | **Proved** |
| Strip extension | `StripLatticeDominatesContinuum W` | **↔ RH** (classical dBN imports) |
| Capstone | `GeometricChannelAbsorbsAllZeros` | **↔ RH** |
| Bridge | `OffLineWeightPressBridge W` | **↔ RH** (`offLineWeightPressBridge_iff_RiemannHypothesis`) |
-/

end

end Hqiv.Story
