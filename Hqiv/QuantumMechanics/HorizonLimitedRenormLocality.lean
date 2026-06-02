import Mathlib.Data.Real.Basic
import Hqiv.QuantumMechanics.HorizonLimitedQM_QFT_Closure
import Hqiv.QuantumMechanics.ContinuumManyBodyQFTScaffold
import Hqiv.QuantumMechanics.HorizonFreeFieldScaffold
import Hqiv.Physics.SpinStatistics

namespace Hqiv.QM

/-!
# Horizon-limited continuum closure (renormalization + locality package)

This module packages the remaining continuum-QFT bridge requirements into a
single formal assumption bundle and proves the corresponding closure statement.
It is designed to align with standard QFT criteria while keeping the domain
explicitly horizon-limited.

Spin–statistics is wired constructively: `spin_statistics_in_domain_holds` is
`HQIV_satisfies_SpinStatistics_from_triality_and_causality` from
`Hqiv.Physics.SpinStatistics`, so `horizon_continuum_closure_core_HQIV` and
`horizon_qm_qft_full_package_core_HQIV` do not assume spin–statistics as a free
axiom in the `HorizonContinuumAxiomsCore` bundle.

The finite classical CPTP/Markov composition slot is discharged by
`cptp_density_closure_finite_classical_holds` from `HorizonLimitedQM_QFT_Closure`.
Use `HorizonContinuumAxiomsMinimal` plus `horizon_qm_qft_full_package_minimal_HQIV`
when only the five field-level continuum assumptions should remain explicit.
-/

/-- Assumption bundle for horizon-limited continuum closure. -/
structure HorizonContinuumAxioms where
  shell_to_harmonic_limit : Prop
  renormalization_in_domain : Prop
  microcausality_in_domain : Prop
  spin_statistics_in_domain : Prop
  cptp_density_closure_in_domain : Prop
  cluster_decomposition_in_domain : Prop
  scattering_consistency_in_domain : Prop

/-- Core continuum assumptions with spin-statistics removed (proved separately). -/
structure HorizonContinuumAxiomsCore where
  shell_to_harmonic_limit : Prop
  renormalization_in_domain : Prop
  microcausality_in_domain : Prop
  cptp_density_closure_in_domain : Prop
  cluster_decomposition_in_domain : Prop
  scattering_consistency_in_domain : Prop

/--
Minimal continuum assumptions: shell / renorm / locality / cluster / scattering only.
The finite-layer `StochasticKernel` composition closure
(`cptp_density_closure_finite_classical`) is proved in
`HorizonLimitedQM_QFT_Closure` and can be merged into `HorizonContinuumAxiomsCore`
via `horizonContinuumAxiomsCore_of_minimal`.
-/
structure HorizonContinuumAxiomsMinimal where
  shell_to_harmonic_limit : Prop
  renormalization_in_domain : Prop
  microcausality_in_domain : Prop
  cluster_decomposition_in_domain : Prop
  scattering_consistency_in_domain : Prop

/-- Extend minimal continuum axioms with the constructive finite CPTP/Markov slot. -/
def horizonContinuumAxiomsCore_of_minimal (A : HorizonContinuumAxiomsMinimal) : HorizonContinuumAxiomsCore where
  shell_to_harmonic_limit := A.shell_to_harmonic_limit
  renormalization_in_domain := A.renormalization_in_domain
  microcausality_in_domain := A.microcausality_in_domain
  cptp_density_closure_in_domain := cptp_density_closure_finite_classical
  cluster_decomposition_in_domain := A.cluster_decomposition_in_domain
  scattering_consistency_in_domain := A.scattering_consistency_in_domain

/-- Master closure claim in the horizon-limited continuum domain. -/
def HorizonContinuumClosureStatement : Prop :=
  ∃ A : HorizonContinuumAxioms,
    A.shell_to_harmonic_limit ∧
    A.renormalization_in_domain ∧
    A.microcausality_in_domain ∧
    A.spin_statistics_in_domain ∧
    A.cptp_density_closure_in_domain ∧
    A.cluster_decomposition_in_domain ∧
    A.scattering_consistency_in_domain

/-- Master closure claim where spin-statistics is injected from proved HQIV theorem. -/
def HorizonContinuumClosureStatementCore (spin_statistics_in_domain_proved : Prop) : Prop :=
  ∃ A : HorizonContinuumAxiomsCore,
    A.shell_to_harmonic_limit ∧
    A.renormalization_in_domain ∧
    A.microcausality_in_domain ∧
    spin_statistics_in_domain_proved ∧
    A.cptp_density_closure_in_domain ∧
    A.cluster_decomposition_in_domain ∧
    A.scattering_consistency_in_domain

/-- Spin–statistics slot for the continuum package (HQIV abstract statement from SpinStatistics). -/
def spin_statistics_in_domain_proved : Prop :=
  Hqiv.Physics.SpinStatistics_from_triality_and_causality_statement

theorem spin_statistics_in_domain_holds : spin_statistics_in_domain_proved :=
  Hqiv.Physics.HQIV_satisfies_SpinStatistics_from_triality_and_causality

/-- Core continuum closure with spin–statistics discharged via `spin_statistics_in_domain_holds`. -/
abbrev HorizonContinuumClosureStatementCoreHQIV : Prop :=
  HorizonContinuumClosureStatementCore spin_statistics_in_domain_proved

/--
If the continuum bridge axioms hold, then the horizon-limited continuum
closure statement holds.
-/
theorem horizon_continuum_closure_of_axioms
    (A : HorizonContinuumAxioms)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hSpin : A.spin_statistics_in_domain)
    (hCptp : A.cptp_density_closure_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    HorizonContinuumClosureStatement := by
  refine ⟨A, hShell, hRenorm, hLocal, hSpin, hCptp, hCluster, hScatter⟩

/--
Core closure theorem: same continuum closure, but with spin-statistics supplied
constructively by the existing HQIV theorem rather than as a free assumption.
-/
theorem horizon_continuum_closure_core_of_axioms
    (A : HorizonContinuumAxiomsCore)
    (hSpin : Prop)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hSpinProof : hSpin)
    (hCptp : A.cptp_density_closure_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    HorizonContinuumClosureStatementCore hSpin := by
  refine ⟨A, hShell, hRenorm, hLocal, ?_, hCptp, hCluster, hScatter⟩
  exact hSpinProof

/--
Core closure with HQIV spin–statistics wired to `HQIV_satisfies_SpinStatistics_from_triality_and_causality`.
-/
theorem horizon_continuum_closure_core_HQIV
    (A : HorizonContinuumAxiomsCore)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hCptp : A.cptp_density_closure_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_core_of_axioms A spin_statistics_in_domain_proved hShell hRenorm hLocal
    spin_statistics_in_domain_holds hCptp hCluster hScatter

/--
Convenience theorem: the finite `horizon_finite_closure_theorem` layer plus continuum assumptions
gives the full horizon-limited QM/QFT closure package.
-/
theorem horizon_qm_qft_full_package
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ)
    (A : HorizonContinuumAxioms)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hSpin : A.spin_statistics_in_domain)
    (hCptp : A.cptp_density_closure_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
    (normSq ψ
      = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransferForOutcome i ψ) ∧
    HorizonContinuumClosureStatement := by
  refine ⟨?_, ?_, ?_⟩
  · exact (horizon_finite_closure_theorem ψ hψ κ i betaRad kappaBeta).1
  · exact (horizon_finite_closure_theorem ψ hψ κ i betaRad kappaBeta).2
  · exact horizon_continuum_closure_of_axioms A hShell hRenorm hLocal hSpin hCptp hCluster hScatter

/--
Version of the full package theorem with spin-statistics supplied as an explicit
`Prop` parameter and proof witness (generic form).
-/
theorem horizon_qm_qft_full_package_core
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ)
    (A : HorizonContinuumAxiomsCore)
    (hSpin : Prop)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hSpinProof : hSpin)
    (hCptp : A.cptp_density_closure_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
    (normSq ψ
      = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransferForOutcome i ψ) ∧
    HorizonContinuumClosureStatementCore hSpin := by
  refine ⟨?_, ?_, ?_⟩
  · exact (horizon_finite_closure_theorem ψ hψ κ i betaRad kappaBeta).1
  · exact (horizon_finite_closure_theorem ψ hψ κ i betaRad kappaBeta).2
  · exact horizon_continuum_closure_core_of_axioms A hSpin hShell hRenorm hLocal hSpinProof hCptp hCluster hScatter

/--
Continuum closure (core + HQIV spin) with only minimal field-level assumptions;
the CPTP-density slot is filled by `cptp_density_closure_finite_classical_holds`.
-/
theorem horizon_continuum_closure_minimal_HQIV
    (A : HorizonContinuumAxiomsMinimal)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_core_HQIV (horizonContinuumAxiomsCore_of_minimal A) hShell hRenorm hLocal
    cptp_density_closure_finite_classical_holds hCluster hScatter

/--
Full finite + continuum package with spin–statistics discharged by the HQIV
`SpinStatistics` theorem (no free spin–statistics assumption).
-/
theorem horizon_qm_qft_full_package_core_HQIV
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ)
    (A : HorizonContinuumAxiomsCore)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hCptp : A.cptp_density_closure_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
    (normSq ψ
      = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransferForOutcome i ψ) ∧
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_qm_qft_full_package_core ψ hψ κ i betaRad kappaBeta A spin_statistics_in_domain_proved hShell
    hRenorm hLocal spin_statistics_in_domain_holds hCptp hCluster hScatter

/--
Full finite + continuum package: minimal continuum axioms, constructive finite CPTP/Markov layer,
and HQIV spin–statistics (no free assumptions in those two slots).
-/
theorem horizon_qm_qft_full_package_minimal_HQIV
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ)
    (A : HorizonContinuumAxiomsMinimal)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
    (normSq ψ
      = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransferForOutcome i ψ) ∧
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_qm_qft_full_package_core_HQIV ψ hψ κ i betaRad kappaBeta (horizonContinuumAxiomsCore_of_minimal A) hShell
    hRenorm hLocal cptp_density_closure_finite_classical_holds hCluster hScatter

/-!
## Ratio-bridge witness (honest partial continuum step)

`horizonContinuumAxiomsMinimal_ratioWitness` instantiates `HorizonContinuumAxiomsMinimal`
with `shell_to_harmonic_limit := ShellToHarmonicLimit` (proved by
`shell_to_harmonic_limit_holds` from `ContinuumManyBodyQFTScaffold`),
`microcausality_in_domain := microcausality_in_domain_free_lattice` (proved by
`microcausality_in_domain_free_lattice_holds` from `HorizonFreeFieldScaffold` — the
abelian diagonal lattice scaffold, not full Minkowski microcausality), and discharges
the remaining three fields by **structured scaffold witnesses** from
`ContinuumManyBodyQFTScaffold`:
`renormalization_in_domain := RenormalizationInDomainStatement` (proof
`renormalization_in_domain_discreteUV_holds` — closed-form `available_modes` from `OctonionicLightCone`;
alias `renormalization_in_domain_trivial_holds`),
`cluster_decomposition_in_domain := ClusterDecompositionStatement clusterCorrelationZero`
(proof `cluster_decomposition_zero_kernel_holds` — vanishing NN correlation surrogate),
`scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelZero`
(proof `scattering_consistency_zero_channel_holds`). These are honest **minimal**
instances of the proposition schemas, not raw `True`, but they are **not** yet
physical many-body cluster/scattering theorems for interacting QFT.

`continuum_many_body_closure_ratioWitness_trivialRest` then yields
`HorizonContinuumClosureStatementCoreHQIV` from this bundle with those proofs.

**Minkowski upgrade:** `horizonContinuumAxiomsMinimal_minkowskiMicroWitness` replaces only the
microcausality field with `microcausality_in_domain_minkowski_scaffold` (η-spacelike pairs
via `spacelikeRelationMinkowski` in `ContinuumManyBodyQFTScaffold`). The commutator surrogate
is still identically zero, but the causal **predicate** matches flat-space QFT conventions.
`continuum_many_body_closure_minkowskiMicroWitness` discharges `HorizonContinuumClosureStatementCoreHQIV`
the same way.

**Interval-max commutator:** `horizonContinuumAxiomsMinimal_minkowskiIntervalWitness` uses
`microcausality_in_domain_minkowski_interval_scaffold` — the commutator surrogate is
`commutatorKernelIntervalMax` (`max 0 η`), **zero on spacelike pairs** and **positive on some timelike
pairs** (`commutatorKernelIntervalMax_nontrivial`). Still scalar-valued, not operator commutators.
`continuum_many_body_closure_minkowskiIntervalWitness` proves the same closure statement.

**Monogamy/redshift cluster upgrade:** `horizonContinuumAxiomsMinimal_minkowskiIntervalMonogamyClusterWitness`
keeps the same Minkowski interval-max microcausality slot, but replaces the zero cluster kernel by
`clusterCorrelationDirectionalMonogamyRedshift 1`: coherence is concentrated on the forward `n → n+1`
channel, capped by `coherenceProxy`, and damped by the extra shell-redshift factor `1 / phi_of_shell n`.
The proved theorem `cluster_decomposition_directional_monogamy_redshift_holds 1` gives a nontrivial
cluster limit with a nonzero witness at `(0,1)`.

**Photon-geodesic transport upgrade:** `horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonGeodesicClusterWitness`
keeps the same microcausality slot, but uses
`clusterCorrelationDirectionalMonogamyPhotonGeodesic 1 1`: the forward `n → n+1` channel is weighted by
the monogamy proxy `coherenceProxy` and transported by the finite measurement ledger's observed-energy
factor `redshiftedEnergyN 1 (birefringenceRedshiftN ((n:ℝ)+1) 1) = exp (-(n+1))`.
`continuum_many_body_closure_minkowskiIntervalPhotonGeodesicClusterWitness` packages the stronger closure.

**Photon-budget transport upgrade:** `horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetClusterWitness`
keeps the same microcausality slot, but uses
`clusterCorrelationDirectionalMonogamyPhotonBudget 1 1`: the forward `n → n+1` channel is weighted by
the monogamy proxy and transported by the cumulative photon mode budget
`photonModeBudgetScaleN n = available_modes n`, so the attenuation is
`exp (-(available_modes n))` at the concrete witness scale `κ = 1`.
`continuum_many_body_closure_minkowskiIntervalPhotonBudgetClusterWitness` packages this second concrete closure.

**Photon-budget + associator scattering:** `horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetAssociatorWitness`
keeps the photon-budget cluster kernel, but sets `scattering_consistency_in_domain` to
`scatteringChannelAssociatorVorticity` (proof `scattering_consistency_associatorVorticity_holds`).
`continuum_many_body_closure_minkowskiIntervalPhotonBudgetAssociatorWitness` packages that closure.

**Operator layer (same η witness):** `PatchIntervalMaxSmeared` lifts the interval functional to
`smearedOpIntervalMax` / `opCommutator` on `LatticeHilbert 2` (Pauli carrier).  Spacelike bilinear
support ⇒ vanishing smeared operators and vanishing integrated commutators — aligned with the scalar
microcausality slot above without changing the `HorizonContinuumAxiomsMinimal` record (still discharged by
`microcausality_in_domain_minkowski_interval_scaffold_holds`).  See
`continuum_interval_max_microcausality_operator_layer_notes` in `ContinuumManyBodyQFTClosureLink`.
-/

/-- Minimal axiom record: shell/harmonic + lattice microcausality + discrete-UV renorm + cluster/scattering witnesses. -/
def horizonContinuumAxiomsMinimal_ratioWitness : HorizonContinuumAxiomsMinimal where
  shell_to_harmonic_limit := ShellToHarmonicLimit
  renormalization_in_domain := RenormalizationInDomainStatement
  microcausality_in_domain := microcausality_in_domain_free_lattice
  cluster_decomposition_in_domain := ClusterDecompositionStatement clusterCorrelationZero
  scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelZero

/-- Same scaffold as `horizonContinuumAxiomsMinimal_ratioWitness`, but microcausality uses Minkowski spacelike separation (chart-quantified). -/
def horizonContinuumAxiomsMinimal_minkowskiMicroWitness : HorizonContinuumAxiomsMinimal where
  shell_to_harmonic_limit := ShellToHarmonicLimit
  renormalization_in_domain := RenormalizationInDomainStatement
  microcausality_in_domain := microcausality_in_domain_minkowski_scaffold
  cluster_decomposition_in_domain := ClusterDecompositionStatement clusterCorrelationZero
  scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelZero

/-- Minkowski microcausality with **nontrivial** timelike commutator surrogate (`max 0 η`). -/
def horizonContinuumAxiomsMinimal_minkowskiIntervalWitness : HorizonContinuumAxiomsMinimal where
  shell_to_harmonic_limit := ShellToHarmonicLimit
  renormalization_in_domain := RenormalizationInDomainStatement
  microcausality_in_domain := microcausality_in_domain_minkowski_interval_scaffold
  cluster_decomposition_in_domain := ClusterDecompositionStatement clusterCorrelationZero
  scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelZero

/-- Minkowski interval-max microcausality with a directional monogamy/redshift cluster witness. -/
def horizonContinuumAxiomsMinimal_minkowskiIntervalMonogamyClusterWitness : HorizonContinuumAxiomsMinimal where
  shell_to_harmonic_limit := ShellToHarmonicLimit
  renormalization_in_domain := RenormalizationInDomainStatement
  microcausality_in_domain := microcausality_in_domain_minkowski_interval_scaffold
  cluster_decomposition_in_domain := ClusterDecompositionStatement (clusterCorrelationDirectionalMonogamyRedshift 1)
  scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelZero

/-- Minkowski interval-max microcausality with directional monogamy and photon-geodesic transport. -/
def horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonGeodesicClusterWitness : HorizonContinuumAxiomsMinimal where
  shell_to_harmonic_limit := ShellToHarmonicLimit
  renormalization_in_domain := RenormalizationInDomainStatement
  microcausality_in_domain := microcausality_in_domain_minkowski_interval_scaffold
  cluster_decomposition_in_domain := ClusterDecompositionStatement
    (clusterCorrelationDirectionalMonogamyPhotonGeodesic 1 1)
  scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelZero

/-- Minkowski interval-max microcausality with directional monogamy and photon-budget transport. -/
def horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetClusterWitness : HorizonContinuumAxiomsMinimal where
  shell_to_harmonic_limit := ShellToHarmonicLimit
  renormalization_in_domain := RenormalizationInDomainStatement
  microcausality_in_domain := microcausality_in_domain_minkowski_interval_scaffold
  cluster_decomposition_in_domain := ClusterDecompositionStatement
    (clusterCorrelationDirectionalMonogamyPhotonBudget 1 1)
  scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelZero

/-- Like `horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetClusterWitness`, but scattering uses the
octonionic associator/vorticity channel (`scatteringChannelAssociatorVorticity`). -/
def horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetAssociatorWitness : HorizonContinuumAxiomsMinimal where
  shell_to_harmonic_limit := ShellToHarmonicLimit
  renormalization_in_domain := RenormalizationInDomainStatement
  microcausality_in_domain := microcausality_in_domain_minkowski_interval_scaffold
  cluster_decomposition_in_domain := ClusterDecompositionStatement
    (clusterCorrelationDirectionalMonogamyPhotonBudget 1 1)
  scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelAssociatorVorticity

/-- The shell/harmonic field is the concrete `Tendsto` bridge from the scaffold. -/
theorem horizonContinuumAxiomsMinimal_ratioWitness_shell :
    horizonContinuumAxiomsMinimal_ratioWitness.shell_to_harmonic_limit :=
  shell_to_harmonic_limit_holds

theorem horizonContinuumAxiomsMinimal_ratioWitness_renorm :
    horizonContinuumAxiomsMinimal_ratioWitness.renormalization_in_domain :=
  renormalization_in_domain_discreteUV_holds

theorem horizonContinuumAxiomsMinimal_ratioWitness_cluster :
    horizonContinuumAxiomsMinimal_ratioWitness.cluster_decomposition_in_domain :=
  cluster_decomposition_zero_kernel_holds

theorem horizonContinuumAxiomsMinimal_ratioWitness_scattering :
    horizonContinuumAxiomsMinimal_ratioWitness.scattering_consistency_in_domain :=
  scattering_consistency_zero_channel_holds

theorem horizonContinuumAxiomsMinimal_minkowskiMicroWitness_micro :
    horizonContinuumAxiomsMinimal_minkowskiMicroWitness.microcausality_in_domain :=
  microcausality_in_domain_minkowski_scaffold_holds

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalWitness_micro :
    horizonContinuumAxiomsMinimal_minkowskiIntervalWitness.microcausality_in_domain :=
  microcausality_in_domain_minkowski_interval_scaffold_holds

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalMonogamyClusterWitness_micro :
    horizonContinuumAxiomsMinimal_minkowskiIntervalMonogamyClusterWitness.microcausality_in_domain :=
  microcausality_in_domain_minkowski_interval_scaffold_holds

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalMonogamyClusterWitness_cluster :
    horizonContinuumAxiomsMinimal_minkowskiIntervalMonogamyClusterWitness.cluster_decomposition_in_domain :=
  cluster_decomposition_directional_monogamy_redshift_holds 1

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonGeodesicClusterWitness_micro :
    horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonGeodesicClusterWitness.microcausality_in_domain :=
  microcausality_in_domain_minkowski_interval_scaffold_holds

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonGeodesicClusterWitness_cluster :
    horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonGeodesicClusterWitness.cluster_decomposition_in_domain :=
  cluster_decomposition_directional_monogamy_photonGeodesic_holds 1 1 zero_lt_one

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetClusterWitness_micro :
    horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetClusterWitness.microcausality_in_domain :=
  microcausality_in_domain_minkowski_interval_scaffold_holds

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetClusterWitness_cluster :
    horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetClusterWitness.cluster_decomposition_in_domain :=
  cluster_decomposition_directional_monogamy_photonBudget_holds 1 1 zero_lt_one

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetAssociatorWitness_micro :
    horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetAssociatorWitness.microcausality_in_domain :=
  microcausality_in_domain_minkowski_interval_scaffold_holds

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetAssociatorWitness_cluster :
    horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetAssociatorWitness.cluster_decomposition_in_domain :=
  cluster_decomposition_directional_monogamy_photonBudget_holds 1 1 zero_lt_one

theorem horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetAssociatorWitness_scattering :
    horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetAssociatorWitness.scattering_consistency_in_domain :=
  scattering_consistency_associatorVorticity_holds

/-- All five `HorizonContinuumAxiomsMinimal` fields of `horizonContinuumAxiomsMinimal_ratioWitness`, packaged. -/
theorem horizonContinuumAxiomsMinimal_ratioWitness_all_slots :
    horizonContinuumAxiomsMinimal_ratioWitness.shell_to_harmonic_limit ∧
    horizonContinuumAxiomsMinimal_ratioWitness.renormalization_in_domain ∧
    horizonContinuumAxiomsMinimal_ratioWitness.microcausality_in_domain ∧
    horizonContinuumAxiomsMinimal_ratioWitness.cluster_decomposition_in_domain ∧
    horizonContinuumAxiomsMinimal_ratioWitness.scattering_consistency_in_domain :=
  ⟨shell_to_harmonic_limit_holds, renormalization_in_domain_discreteUV_holds,
    microcausality_in_domain_free_lattice_holds, cluster_decomposition_zero_kernel_holds,
    scattering_consistency_zero_channel_holds⟩

/--
Scattering consistency for the **non-zero** associator/vorticity channel
(`scatteringChannelAssociatorVorticity` from `ContinuumManyBodyQFTScaffold` / `OctonionBasics`).
-/
theorem continuum_scattering_associatorVorticity_holds :
    ScatteringConsistencyStatement scatteringChannelAssociatorVorticity :=
  scattering_consistency_associatorVorticity_holds

/-- Continuum closure: shell/harmonic + lattice microcausality + discrete-UV renorm + cluster/scattering witnesses. -/
theorem continuum_many_body_closure_ratioWitness_trivialRest :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_minimal_HQIV horizonContinuumAxiomsMinimal_ratioWitness
    shell_to_harmonic_limit_holds renormalization_in_domain_discreteUV_holds
    microcausality_in_domain_free_lattice_holds cluster_decomposition_zero_kernel_holds
    scattering_consistency_zero_channel_holds

/-- Continuum closure with Minkowski-chart microcausality (same renorm/cluster/scattering witnesses as `continuum_many_body_closure_ratioWitness_trivialRest`). -/
theorem continuum_many_body_closure_minkowskiMicroWitness :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_minimal_HQIV horizonContinuumAxiomsMinimal_minkowskiMicroWitness
    shell_to_harmonic_limit_holds renormalization_in_domain_discreteUV_holds
    microcausality_in_domain_minkowski_scaffold_holds cluster_decomposition_zero_kernel_holds
    scattering_consistency_zero_channel_holds

/-- Continuum closure with interval-max commutator surrogate (nontrivial on timelike pairs). -/
theorem continuum_many_body_closure_minkowskiIntervalWitness :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_minimal_HQIV horizonContinuumAxiomsMinimal_minkowskiIntervalWitness
    shell_to_harmonic_limit_holds renormalization_in_domain_discreteUV_holds
    microcausality_in_domain_minkowski_interval_scaffold_holds cluster_decomposition_zero_kernel_holds
    scattering_consistency_zero_channel_holds

/-- Continuum closure with interval-max microcausality and directional monogamy/redshift clustering. -/
theorem continuum_many_body_closure_minkowskiIntervalMonogamyClusterWitness :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_minimal_HQIV horizonContinuumAxiomsMinimal_minkowskiIntervalMonogamyClusterWitness
    shell_to_harmonic_limit_holds renormalization_in_domain_discreteUV_holds
    microcausality_in_domain_minkowski_interval_scaffold_holds
    (cluster_decomposition_directional_monogamy_redshift_holds 1)
    scattering_consistency_zero_channel_holds

/-- Continuum closure with interval-max microcausality and photon-geodesic monogamy transport. -/
theorem continuum_many_body_closure_minkowskiIntervalPhotonGeodesicClusterWitness :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_minimal_HQIV horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonGeodesicClusterWitness
    shell_to_harmonic_limit_holds renormalization_in_domain_discreteUV_holds
    microcausality_in_domain_minkowski_interval_scaffold_holds
    (cluster_decomposition_directional_monogamy_photonGeodesic_holds 1 1 zero_lt_one)
    scattering_consistency_zero_channel_holds

/-- Continuum closure with interval-max microcausality and photon-budget monogamy transport. -/
theorem continuum_many_body_closure_minkowskiIntervalPhotonBudgetClusterWitness :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_minimal_HQIV horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetClusterWitness
    shell_to_harmonic_limit_holds renormalization_in_domain_discreteUV_holds
    microcausality_in_domain_minkowski_interval_scaffold_holds
    (cluster_decomposition_directional_monogamy_photonBudget_holds 1 1 zero_lt_one)
    scattering_consistency_zero_channel_holds

/-- Continuum closure: photon-budget cluster kernel + associator/vorticity scattering channel. -/
theorem continuum_many_body_closure_minkowskiIntervalPhotonBudgetAssociatorWitness :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_minimal_HQIV horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetAssociatorWitness
    shell_to_harmonic_limit_holds renormalization_in_domain_discreteUV_holds
    microcausality_in_domain_minkowski_interval_scaffold_holds
    (cluster_decomposition_directional_monogamy_photonBudget_holds 1 1 zero_lt_one)
    scattering_consistency_associatorVorticity_holds

end Hqiv.QM
