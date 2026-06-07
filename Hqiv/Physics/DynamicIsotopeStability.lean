import Hqiv.Physics.DynamicBetaIsotope
import Hqiv.Physics.DerivedGaugeAndLeptonSector

/-!
# Dynamic isotope stability and half-life slots

This module turns the dynamic β/isotope ledgers into a stability predicate.

The rule is structural:

* β residuals come from `DynamicBetaIsotope`.
* A bonded nuclear well shields those residuals by `nucleonWellContribution`.
* A β channel is structurally open only when the shielded residual is positive.
* A stability / half-life **claim** requires `betaWidthLedgerQualified`: positive
  endpoint `Q` and positive shielded overlap residual on the weak channel.
  Stable isotopes instead require structural shielding (residuals non-positive).
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

/--
Weak width ledger qualified: kinematic endpoint `Q` and shielded overlap residual
are both positive (`weakBetaChannelOpen`).
-/
def betaWidthLedgerQualified (env : NucleonEnvironment) (m_e : ℝ) (c : ℝ := 1) : Prop :=
  weakBetaChannelOpen (betaMinusEndpointQAtXi env m_e c) (betaMinusEffectiveResidualAtXi env c)

/-- Legacy export name used in papers and Python witnesses. -/
def EMTippingQualified (env : NucleonEnvironment) (c : ℝ := 1) : Prop :=
  betaWidthLedgerQualified env m_e_PDG c

/--
Qualified dynamic stability for bonded nuclei: β channels structurally closed.
Half-life **width** claims on open channels use `betaWidthLedgerQualified` instead.
-/
def dynamicallyStableIsotope (env : NucleonEnvironment) (c : ℝ := 1) : Prop :=
  structurallyShieldedIsotope env c

theorem betaWidthLedgerQualified_of_open
    (env : NucleonEnvironment) (m_e c : ℝ)
    (hQ : 0 < betaMinusEndpointQAtXi env m_e c)
    (hR : 0 < betaMinusEffectiveResidualAtXi env c) :
    betaWidthLedgerQualified env m_e c :=
  ⟨hQ, hR⟩

theorem EMTippingQualified_of_open
    (env : NucleonEnvironment) (c : ℝ)
    (hQ : 0 < betaMinusEndpointQAtXi env m_e_PDG c)
    (hR : 0 < betaMinusEffectiveResidualAtXi env c) :
    EMTippingQualified env c :=
  betaWidthLedgerQualified_of_open env m_e_PDG c hQ hR

theorem structurallyShielded_of_residuals_nonpos
    (env : NucleonEnvironment) (c : ℝ)
    (hm : betaMinusEffectiveResidualAtXi env c ≤ 0)
    (hp : betaPlusEffectiveResidualAtXi env c ≤ 0) :
    structurallyShieldedIsotope env c := ⟨hm, hp⟩

theorem dynamicallyStable_of_residuals_nonpos
    (env : NucleonEnvironment) (c : ℝ)
    (hm : betaMinusEffectiveResidualAtXi env c ≤ 0)
    (hp : betaPlusEffectiveResidualAtXi env c ≤ 0) :
    dynamicallyStableIsotope env c :=
  structurallyShielded_of_residuals_nonpos env c hm hp

/-- Width slot for an active β channel. `Γ` is supplied by the weak tipping model. -/
noncomputable def betaHalfLifeFromWidth (Γ : ℝ) : ℝ :=
  half_life_from_width Γ

theorem betaHalfLifeFromWidth_eq (Γ : ℝ) :
    betaHalfLifeFromWidth Γ = Real.log 2 / Γ := rfl

theorem free_lockin_wellShield_zero :
    isotopeWellShield freeLockinNucleonEnvironment = 0 := by
  unfold isotopeWellShield nucleonWellContribution freeLockinNucleonEnvironment
  simp

end

end Hqiv.Physics
