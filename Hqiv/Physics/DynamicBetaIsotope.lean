import Hqiv.Physics.DynamicNucleonPN

/-!
# Dynamic isotope and β-channel readouts

This module is the next layer over `DynamicNucleonPN`.

It does **not** derive weak lifetimes from the strong/curvature overlap energy.
Instead it keeps the three ledgers separate:

* p/n mass gap: from `DerivedNucleonMass`, preserved by shared outside-curvature binding.
* β overlap: from `NeutronBindingStabilityScaffold` via `betaMinusOverlapAtXi`.
* weak width: from `NuclearAndAtomicSpectra.beta_decay_rate` / `G_F_from_beta`.
* geometry / spin-statistics: valley-count + caustic-well trapping for bonded clusters.

This is the right place to build isotope-ladder β bookkeeping before adding a
flavor-dependent weak/EM tipping correction to the nucleon mass itself.
-/

namespace Hqiv.Physics

noncomputable section

/-- A dynamic isotope environment: mass number, proton number, ladder witness, and p/n environment. -/
structure DynamicIsotopeEnvironment (A Z : ℕ) where
  ladder : IsotopeLadder A Z
  nucleonEnv : NucleonEnvironment

/-- Neutron count in an isotope bookkeeping state. -/
def neutronCount (A Z : ℕ) : ℕ := A - Z

/-- Isotope mass budget from dynamic p/n masses, before electron/rest-frame bookkeeping. -/
noncomputable def isotopeNucleonMassBudget
    {A Z : ℕ} (env : DynamicIsotopeEnvironment A Z) (c : ℝ := 1) : ℝ :=
  (Z : ℝ) * protonMassAtXi env.nucleonEnv c +
    (neutronCount A Z : ℝ) * neutronMassAtXi env.nucleonEnv c

/-- β− mass-gap slot: one neutron changes to one proton in the same environment. -/
noncomputable def betaMinusMassGapAtXi (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  neutronMassAtXi env c - protonMassAtXi env c

/-- β+ mass-gap slot: one proton changes to one neutron in the same environment. -/
noncomputable def betaPlusMassGapAtXi (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  protonMassAtXi env c - neutronMassAtXi env c

theorem betaMinusMassGapAtXi_eq_derivedDeltaM
    (env : NucleonEnvironment) (c : ℝ) :
    betaMinusMassGapAtXi env c = derivedDeltaM := by
  unfold betaMinusMassGapAtXi
  exact neutron_proton_gap_preserved_at_xi env c

theorem betaPlusMassGapAtXi_eq_neg_derivedDeltaM
    (env : NucleonEnvironment) (c : ℝ) :
    betaPlusMassGapAtXi env c = -derivedDeltaM := by
  unfold betaPlusMassGapAtXi
  have h := neutron_proton_gap_preserved_at_xi env c
  linarith

/-- Strong/curvature overlap slot for β−, kept separate from weak width. -/
noncomputable def betaMinusCurvatureOverlap
    (env : NucleonEnvironment) : ℝ :=
  betaMinusOverlapForEnvironment env

/-- β+ mirror overlap slot; this is structural, not a weak width. -/
noncomputable def betaPlusCurvatureOverlap
    (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  betaPlusOverlapForEnvironment env c

/-- Residual β− energy after the curvature-overlap ledger. -/
noncomputable def betaMinusResidualAtXi
    (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  betaMinusMassGapAtXi env c - betaMinusCurvatureOverlap env

/-- Residual β+ energy after the curvature-overlap ledger. -/
noncomputable def betaPlusResidualAtXi
    (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  betaPlusMassGapAtXi env c - betaPlusCurvatureOverlap env c

/-- Kinematic β− endpoint Q after the lepton mass slot (not the overlap residual). -/
noncomputable def betaMinusEndpointQAtXi
    (env : NucleonEnvironment) (m_e : ℝ) (c : ℝ := 1) : ℝ :=
  betaMinusMassGapAtXi env c - m_e

/-- Kinematic β+ endpoint Q after the lepton mass slot. -/
noncomputable def betaPlusEndpointQAtXi
    (env : NucleonEnvironment) (m_e : ℝ) (c : ℝ := 1) : ℝ :=
  betaPlusMassGapAtXi env c - m_e

theorem betaMinusEndpointQAtXi_eq_derivedDeltaM_minus_m_e
    (env : NucleonEnvironment) (m_e c : ℝ) :
    betaMinusEndpointQAtXi env m_e c = derivedDeltaM - m_e := by
  unfold betaMinusEndpointQAtXi
  rw [betaMinusMassGapAtXi_eq_derivedDeltaM]

/-- Weak matrix-element slot: overlap residual carried to fourth power by m_e. -/
noncomputable def betaWeakMatrixElementSquared
    (residual m_e : ℝ) : ℝ :=
  (max residual 0 / max m_e 1e-30) ^ 4

/-- Generic valley-count bound for a mass number: `2 · (A − 1)` (`HQIVNuclei.valleyCount_le_two_mul_pred`). -/
def betaValleyCountBound (A : ℕ) : ℕ :=
  if A ≤ 1 then 0 else 2 * (A - 1)

/-- Active caustic layer count from the hierarchical stack (pair + torus + deepen + optional tetra). -/
def betaCausticLayerCount (A : ℕ) : ℕ :=
  if A ≤ 1 then 0
  else
    let deepen := if A ≤ 2 then 0 else A - 2
    (if 4 ≤ A then 1 else 0) + 2 + deepen

/--
Geometry / spin-statistics width factor for bonded clusters.

Free nucleons (`A ≤ 1`) carry unit factor.  Bonded clusters suppress weak tipping by
`(residual / well)^(valley + 1)`: each valley contact from the isotope ladder plus
one fermionic spin-statistics slot (`SpinStatistics` / `HQIVNuclei`).
-/
noncomputable def betaGeometryWidthFactor
    (A : ℕ) (residual well : ℝ) (bonded : Bool) : ℝ :=
  if A ≤ 1 ∨ ¬ bonded then 1
  else
    let valley := (betaValleyCountBound A : ℝ)
    let ratio := max residual 0 / max well (max residual 1e-30)
    ratio ^ (valley + 1)

/-- Weak width from `beta_decay_rate` with the overlap residual in the matrix-element slot. -/
noncomputable def betaWeakWidthFromResidual
    (channel : BetaDecayChannel) (residual m_e ℳ : ℝ) : ℝ :=
  let slot := betaWeakMatrixElementSquared residual m_e
  match channel with
  | .betaMinus => beta_decay_rate Fermion.neutron m_e (ℳ * Real.sqrt slot)
  | .betaPlus => beta_decay_rate Fermion.proton m_e (ℳ * Real.sqrt slot)

/-- Weak β width slot using the existing Fermi/tipping scaffold. -/
noncomputable def betaWeakWidthSlot
    (channel : BetaDecayChannel) (m_e ℳ : ℝ) : ℝ :=
  match channel with
  | .betaMinus => beta_decay_rate Fermion.neutron m_e ℳ
  | .betaPlus => beta_decay_rate Fermion.proton m_e ℳ

theorem betaWeakWidthSlot_betaMinus (m_e ℳ : ℝ) :
    betaWeakWidthSlot .betaMinus m_e ℳ = beta_decay_rate Fermion.neutron m_e ℳ := rfl

theorem betaWeakWidthSlot_betaPlus (m_e ℳ : ℝ) :
    betaWeakWidthSlot .betaPlus m_e ℳ = beta_decay_rate Fermion.proton m_e ℳ := rfl

/-- Deuteron dynamic environment from the existing isotope ladder witness. -/
def dynamicDeuteronEnvironment (env : NucleonEnvironment) :
    DynamicIsotopeEnvironment 2 1 where
  ladder := deuteron
  nucleonEnv := env

/-- ³He dynamic environment from the existing isotope ladder witness. -/
def dynamicHelium3Environment (env : NucleonEnvironment) :
    DynamicIsotopeEnvironment 3 2 where
  ladder := helium3
  nucleonEnv := env

/-- ⁴He dynamic environment from the existing isotope ladder witness. -/
def dynamicHelium4Environment (env : NucleonEnvironment) :
    DynamicIsotopeEnvironment 4 2 where
  ladder := helium4
  nucleonEnv := env

theorem dynamicHelium4_valleyCount (env : NucleonEnvironment) :
    valleyCount (dynamicHelium4Environment env).ladder = 6 := by
  rfl

end

end Hqiv.Physics
