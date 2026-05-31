import Hqiv.Physics.DynamicBetaIsotope

/-!
# Dynamic isotope stability and half-life slots

This module turns the dynamic β/isotope ledgers into a stability predicate.

The rule is structural:

* β residuals come from `DynamicBetaIsotope`.
* A bonded nuclear well shields those residuals by `nucleonWellContribution`.
* A β channel is structurally open only when the shielded residual is positive.
* A stability / half-life **claim** also requires an explicit EM-tipping qualification.
  Without that qualification, the readout is only “residual shielded/open”.
-/

namespace Hqiv.Physics

noncomputable section

/-- Shielding supplied by the bonded nuclear well. -/
noncomputable def isotopeWellShield (env : NucleonEnvironment) : ℝ :=
  nucleonWellContribution env

/-- Effective β− residual after nuclear well shielding. -/
noncomputable def betaMinusEffectiveResidualAtXi
    (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  betaMinusResidualAtXi env c - isotopeWellShield env

/-- Effective β+ residual after nuclear well shielding. -/
noncomputable def betaPlusEffectiveResidualAtXi
    (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  betaPlusResidualAtXi env c - isotopeWellShield env

/-- A β channel is energetically active when its shielded residual is positive. -/
def betaChannelActive (residual : ℝ) : Prop := 0 < residual

/-- Weak β channel is kinematically open once the endpoint Q and overlap residual are positive. -/
def weakBetaChannelOpen (endpointQ residual : ℝ) : Prop :=
  0 < endpointQ ∧ 0 < residual

/-- Structural shielding: neither β− nor β+ residual is open after the nuclear well. -/
def structurallyShieldedIsotope (env : NucleonEnvironment) (c : ℝ := 1) : Prop :=
  betaMinusEffectiveResidualAtXi env c ≤ 0 ∧
    betaPlusEffectiveResidualAtXi env c ≤ 0

/-- EM/electric tipping has been qualified for this environment and residual model. -/
def EMTippingQualified (_env : NucleonEnvironment) (_c : ℝ := 1) : Prop := False

/--
Qualified dynamic stability.

The residuals must be structurally shielded, and the EM-tipping channel must be
qualified separately.  This prevents the model from turning a caustic residual
statement into a nuclear stability claim too early.
-/
def dynamicallyStableIsotope (env : NucleonEnvironment) (c : ℝ := 1) : Prop :=
  structurallyShieldedIsotope env c ∧ EMTippingQualified env c

/-- Width slot for an active β channel. `Γ` is supplied by the weak tipping model. -/
noncomputable def betaHalfLifeFromWidth (Γ : ℝ) : ℝ :=
  half_life_from_width Γ

theorem betaHalfLifeFromWidth_eq (Γ : ℝ) :
    betaHalfLifeFromWidth Γ = Real.log 2 / Γ := rfl

theorem dynamicallyStable_of_residuals_nonpos
    (env : NucleonEnvironment) (c : ℝ)
    (hm : betaMinusEffectiveResidualAtXi env c ≤ 0)
    (hp : betaPlusEffectiveResidualAtXi env c ≤ 0)
    (hEM : EMTippingQualified env c) :
    dynamicallyStableIsotope env c := ⟨⟨hm, hp⟩, hEM⟩

theorem structurallyShielded_of_residuals_nonpos
    (env : NucleonEnvironment) (c : ℝ)
    (hm : betaMinusEffectiveResidualAtXi env c ≤ 0)
    (hp : betaPlusEffectiveResidualAtXi env c ≤ 0) :
    structurallyShieldedIsotope env c := ⟨hm, hp⟩

theorem free_lockin_wellShield_zero :
    isotopeWellShield freeLockinNucleonEnvironment = 0 := by
  unfold isotopeWellShield nucleonWellContribution freeLockinNucleonEnvironment
  simp

end

end Hqiv.Physics
