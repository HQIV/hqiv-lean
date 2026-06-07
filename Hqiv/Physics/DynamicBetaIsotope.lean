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

/-!
## Curvature mass imprints and endpoint-$Q$ policies (generic ledger)

The primary HQIV width readout uses the **nucleon-gap** endpoint from shared p/n readouts
(`betaMinusEndpointQAtXi`).  A separate **spectroscopy / mass-table** layer closes each
isotope budget with its own reference imprint
`curvatureMassImprint = M_ref / M_derived`.  Uniform imprints preserve $\Delta M$;
independent parent/daughter imprints move $Q_{\beta^-}$ to the mass-table slot.
The geometric-mean interior width well is the width-ledger companion (not the mass endpoint).
These are generic bookkeeping policies for endpoint $Q$ and width-well imprints; they carry
no claim about nuclear structure beyond the named mass-budget identities proved below.
-/

/-- Curvature mass imprint: reference mass over derived budget (spectroscopy ledger). -/
noncomputable def curvatureMassImprint (M_ref M_der : ℝ) : ℝ :=
  M_ref / max M_der 1e-30

/-- Mass budget after applying a curvature imprint. -/
noncomputable def imprintedMassBudget (M_der κ : ℝ) : ℝ :=
  κ * M_der

theorem imprintedMassBudget_eq_ref
    (M_der κ M_ref : ℝ) (hκ : curvatureMassImprint M_ref M_der = κ)
    (hder : 1e-30 < M_der) :
    imprintedMassBudget M_der κ = M_ref := by
  unfold imprintedMassBudget
  calc
    κ * M_der = curvatureMassImprint M_ref M_der * M_der := by rw [hκ]
    _ = M_ref := by
      unfold curvatureMassImprint
      have hmax : max M_der 1e-30 = M_der := max_eq_left (le_of_lt hder)
      rw [hmax]
      field_simp [ne_of_lt hder]

theorem curvatureMassImprint_imprinted_closes_budget
    (M_der M_ref : ℝ) (hder : 1e-30 < M_der) :
    imprintedMassBudget M_der (curvatureMassImprint M_ref M_der) = M_ref :=
  imprintedMassBudget_eq_ref M_der (curvatureMassImprint M_ref M_der) M_ref rfl hder

/-- Generic β− endpoint from parent and daughter mass budgets and the lepton slot. -/
noncomputable def betaMinusEndpointQFromBudgets (M_parent M_daughter m_e : ℝ) : ℝ :=
  M_parent - M_daughter - m_e

/-- β− endpoint with one uniform imprint on both isotope budgets. -/
noncomputable def betaMinusEndpointQUniformImprint
    (κ M_parent_der M_daughter_der m_e : ℝ) : ℝ :=
  imprintedMassBudget M_parent_der κ - imprintedMassBudget M_daughter_der κ - m_e

/-- β− endpoint with independent per-isotope curvature imprints. -/
noncomputable def betaMinusEndpointQPerIsotopeImprint
    (κ_parent M_parent_der κ_daughter M_daughter_der m_e : ℝ) : ℝ :=
  imprintedMassBudget M_parent_der κ_parent -
    imprintedMassBudget M_daughter_der κ_daughter - m_e

theorem betaMinusEndpointQUniformImprint_eq_kappa_gap_minus_m_e
    (κ M_parent_der M_daughter_der m_e : ℝ) :
    betaMinusEndpointQUniformImprint κ M_parent_der M_daughter_der m_e =
      κ * (M_parent_der - M_daughter_der) - m_e := by
  unfold betaMinusEndpointQUniformImprint imprintedMassBudget
  ring

theorem betaMinusEndpointQPerIsotopeImprint_eq_reference_budgets
    (κ_p M_p κ_d M_d M_p_ref M_d_ref m_e : ℝ)
    (hp : imprintedMassBudget M_p κ_p = M_p_ref)
    (hd : imprintedMassBudget M_d κ_d = M_d_ref) :
    betaMinusEndpointQPerIsotopeImprint κ_p M_p κ_d M_d m_e =
      betaMinusEndpointQFromBudgets M_p_ref M_d_ref m_e := by
  unfold betaMinusEndpointQPerIsotopeImprint betaMinusEndpointQFromBudgets
  rw [hp, hd]

theorem betaMinusEndpointQPerIsotopeImprint_eq_mass_table
    (M_p_der M_d_der M_p_ref M_d_ref m_e : ℝ)
    (hp : 1e-30 < M_p_der) (hd : 1e-30 < M_d_der) :
    betaMinusEndpointQPerIsotopeImprint
      (curvatureMassImprint M_p_ref M_p_der) M_p_der
      (curvatureMassImprint M_d_ref M_d_der) M_d_der m_e =
      betaMinusEndpointQFromBudgets M_p_ref M_d_ref m_e :=
  betaMinusEndpointQPerIsotopeImprint_eq_reference_budgets _ _ _ _ _ _ _
    (imprintedMassBudget_eq_ref M_p_der (curvatureMassImprint M_p_ref M_p_der) M_p_ref rfl hp)
    (imprintedMassBudget_eq_ref M_d_der (curvatureMassImprint M_d_ref M_d_der) M_d_ref rfl hd)

/--
Mass-budget difference for a $\beta^-$ step $(A,Z)\to(A,Z+1)$ at fixed p/n environment.
Matches `betaMinusMassGapAtXi` (nucleon-gap ledger).
-/
noncomputable def betaMinusIsotopeMassGapAtXi
    (A Z : ℕ) (env : NucleonEnvironment) (c : ℝ := 1) : ℝ :=
  (Z : ℝ) * protonMassAtXi env c + (neutronCount A Z : ℝ) * neutronMassAtXi env c -
    ((Z + 1 : ℕ) : ℝ) * protonMassAtXi env c -
      (neutronCount A (Z + 1) : ℝ) * neutronMassAtXi env c

theorem betaMinusIsotopeMassGapAtXi_eq_betaMinusMassGapAtXi
    (A Z : ℕ) (env : NucleonEnvironment) (c : ℝ) (h : Z < A) :
    betaMinusIsotopeMassGapAtXi A Z env c = betaMinusMassGapAtXi env c := by
  unfold betaMinusIsotopeMassGapAtXi betaMinusMassGapAtXi neutronCount
  have hle : Z ≤ A := Nat.le_of_lt h
  have hle' : Z + 1 ≤ A := by omega
  simp only [Nat.cast_sub hle, Nat.cast_sub hle', Nat.cast_add, Nat.cast_one]
  ring

/-- Primary width-ledger endpoint: isotope budgets at shared p/n environment. -/
noncomputable def betaMinusEndpointQNucleonGap
    (A Z : ℕ) (env : NucleonEnvironment) (m_e : ℝ) (c : ℝ := 1) : ℝ :=
  betaMinusIsotopeMassGapAtXi A Z env c - m_e

theorem betaMinusEndpointQNucleonGap_eq_betaMinusEndpointQAtXi
    (A Z : ℕ) (env : NucleonEnvironment) (m_e c : ℝ) (h : Z < A) :
    betaMinusEndpointQNucleonGap A Z env m_e c = betaMinusEndpointQAtXi env m_e c := by
  unfold betaMinusEndpointQNucleonGap betaMinusEndpointQAtXi
  rw [betaMinusIsotopeMassGapAtXi_eq_betaMinusMassGapAtXi (A:=A) (Z:=Z) env c h,
    betaMinusMassGapAtXi_eq_derivedDeltaM]

theorem betaMinusEndpointQNucleonGap_eq_derivedDeltaM_minus_m_e
    (A Z : ℕ) (env : NucleonEnvironment) (m_e c : ℝ) (h : Z < A) :
    betaMinusEndpointQNucleonGap A Z env m_e c = derivedDeltaM - m_e := by
  rw [betaMinusEndpointQNucleonGap_eq_betaMinusEndpointQAtXi (A:=A) (Z:=Z) env m_e c h,
    betaMinusEndpointQAtXi_eq_derivedDeltaM_minus_m_e]

theorem betaMinusEndpointQUniformImprint_preserves_gap_shape
    (κ M_p M_d m_e : ℝ) :
    betaMinusEndpointQUniformImprint κ M_p M_d m_e =
      κ * (M_p - M_d) - m_e :=
  betaMinusEndpointQUniformImprint_eq_kappa_gap_minus_m_e κ M_p M_d m_e

/-- Symmetric cluster mass well ``B_cluster / A`` (mass ledger). -/
noncomputable def betaClusterMassWell (clusterTotal A : ℝ) : ℝ :=
  clusterTotal / max A 1

/-- Interior partner well ``B_cluster / (A-1)`` for bonded clusters. -/
noncomputable def betaInteriorPartnerWell (clusterTotal partners : ℝ) : ℝ :=
  clusterTotal / max partners 1

/--
Geometric-mean blend of symmetric mass well and interior partner well (width ledger).
Witness exponent ``blend = 1/(2·partners)`` in \texttt{hqiv\_dynamic\_beta\_isotope.py}.
-/
noncomputable def betaWidthWellGeometricBlend
    (massWell interiorPartner partners : ℝ) : ℝ :=
  let blend := 1 / (2 * max partners 1)
  massWell * (interiorPartner / max massWell 1e-30) ^ blend

/-- Width-ledger curvature imprint on cluster caustic depth (comparison layer). -/
noncomputable def widthWellCurvatureImprint (τ_ref τ_pred valley : ℝ) : ℝ :=
  (τ_ref / max τ_pred 1e-30) ^ (1 / max (valley + 1) 1)

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
