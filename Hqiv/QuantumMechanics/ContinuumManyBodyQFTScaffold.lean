import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Hqiv.Geometry.SphericalHarmonicsBridge
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Algebra.OctonionBasics
import Hqiv.QuantumMechanics.BornMeasurementFinite
import Hqiv.QuantumMechanics.MonogamyTanglesPhiConditions

namespace Hqiv.QM

open scoped Topology
open Filter Topology
open Matrix
open Hqiv.Algebra

/-!
# Continuum many-body QFT in the horizon-limited domain (scaffold)

This module is a **lightweight entry point** that (i) documents the formal path
toward continuum many-body QFT inside HQIV and (ii) re-proves the first
**concrete** large-shell bridge from the discrete light-cone ladder to spherical-harmonic
mode counting (`SphericalHarmonicsBridge`).

## Full many-body QFT (eventual target)

A complete horizon-limited many-body QFT layer would add, beyond the finite QM
closure in `HorizonLimitedQM_QFT_Closure`, items such as: smeared fields / net
algebras, vacuum and multi-particle states, microcausality, renormalized
correlators, cluster decomposition, and scattering—packaged in practice by the
`HorizonContinuumAxiomsMinimal` bundle in `HorizonLimitedRenormLocality` (import
that module for `HorizonContinuumClosureStatementCoreHQIV` and
`horizon_qm_qft_full_package_minimal_HQIV`).

Related HQIV modules already in the library:

* `Hqiv.Physics.SpinStatistics` — spin–statistics chain (abstract + HQIV instance).
* `Hqiv.Geometry.AuxiliaryFieldSmeared` — discrete horizon smearing of `phi_of_shell` + Jensen
  regularization lemma (`phi_of_smeared_temperature_le_smeared_auxField`).
* `Hqiv.QuantumOptics.HorizonQED` — discrete shell QED scaffolding (not full Fock).
* `Hqiv.QuantumMechanics.HorizonLimitedRenormLocality` — continuum assumption bundle +
  finite+CPTP+spin closure theorems (**heavy** import chain).
* `Hqiv.Physics.LightConeMaxwellQFTBridge` — single import hub pairing continuum O–Maxwell (`Fin 4 → ℝ`)
  with this scaffold + `HorizonContinuumAxiomsMinimal` (`LightConeFunctionalBridge`).
* `Hqiv.QuantumMechanics.FiniteManyBodyTensorScaffold` — finite **non-interacting** tensor/Kronecker-sum
  observables on `Fin (n * m)` (numerical twin: `scripts/qm_finite_tensor_toy.py`).
* `Hqiv.QuantumMechanics.HubbardDimerFinite` — first finite interacting toy in 4D (`H = H₀ + λV`) with
  shell-coupled `lambdaShell` and Python mirror `scripts/qm_hubbard_dimer.py`.

## Proof-obligation checklist (informal)

The five `Prop` fields of `HorizonContinuumAxiomsMinimal` are the remaining
**lemma gaps** toward closing the continuum story: shell/harmonic limit,
renormalization-in-domain (**now** the proved discrete closed form `RenormalizationInDomainStatement` via
`available_modes_eq`), microcausality, cluster decomposition, scattering
consistency. The inductive type `ContinuumManyBodyLemmaGap` mirrors that list for
grepability and planning.
-/

/-- Checklist mirroring `HorizonContinuumAxiomsMinimal` (see `HorizonLimitedRenormLocality`). -/
inductive ContinuumManyBodyLemmaGap : Type
  | shellToHarmonicLimit
  | renormalizationInDomain
  | microcausalityInDomain
  | clusterDecompositionInDomain
  | scatteringConsistencyInDomain

/-!
## First concrete bridge (combinatorial ↔ harmonic counting)

This is a **proved** `Tendsto` statement—not yet an operator-level
`shell_to_harmonic_limit`, but the standard HQIV discrete-vs-$S^2$ asymptotic match.
-/

/-- Light-cone combinatorial capacity vs cumulative $S^2$ harmonic degeneracy
tends to the octonion factor `4` as shell index $m\to\infty$. -/
theorem continuum_shell_harmonic_ratio_limit :
    Filter.Tendsto
      (fun m : ℕ => Hqiv.available_modes m / Hqiv.sphericalHarmonicCumulativeCount m)
      Filter.atTop
      (nhds (4 : ℝ)) :=
  Hqiv.tendsto_available_modes_div_sphericalHarmonicCumulative

/-!
### HQIV octonionic zeta (same `ℕ` shell axis)

The rapidity-modulated lattice zeta `Hqiv.Physics.zeta_HQIV` sums over the **same** discrete shell
index `m : ℕ` as this scaffold’s mode-ratio limit. Import `Hqiv.Physics.OctonionicZeta` for
`zeta_HQIV_same_shell_axis_as_modeRatio_bridge` (no circular import: that module imports this file).
-/

/-!
## Structured proposition targets (next-step formalization)

These definitions make the five continuum obligations explicit as
Lean-readable proposition schemas. They are still lightweight and do not yet
instantiate full Wightman/Haag-Kastler objects.

**Minkowski microcausality:** `minkowskiIntervalSq`, `spacelikeRelationMinkowski`, and
`microcausality_in_domain_minkowski_scaffold` supply a chart-quantified η-spacelike predicate
(signature $(+,{-},{-},{-})$); the commutator surrogate can be identically zero **or** the
**interval-max** kernel `commutatorKernelIntervalMax` (`max 0 η`), which is microcausal and
**positive on timelike pairs** (`commutatorKernelIntervalMax_nontrivial`). Operator-valued hooks:
`IntervalMaxOperatorCommutator` / `PatchIntervalMaxSmeared` (Pauli carrier, patch smearing).
-/

/-- Shell-to-harmonic continuum matching target used in the current HQIV bridge. -/
def ShellToHarmonicLimit : Prop :=
  Filter.Tendsto
    (fun m : ℕ => Hqiv.available_modes m / Hqiv.sphericalHarmonicCumulativeCount m)
    Filter.atTop
    (nhds (4 : ℝ))

/-- Proved shell-to-harmonic limit from the geometry bridge. -/
theorem shell_to_harmonic_limit_holds : ShellToHarmonicLimit :=
  continuum_shell_harmonic_ratio_limit

/-- Minimal abstract index type for spacetime-localized observables/channels. -/
abbrev EventLabel := ℕ

/-- Abstract commutator surrogate. In a full field model this would be operator-valued. -/
abbrev CommutatorKernel := EventLabel → EventLabel → ℝ

/-- Abstract spacelike-separation relation on event labels. -/
abbrev SpacelikeRelation := EventLabel → EventLabel → Prop

/-- Microcausality schema: spacelike-separated events have vanishing commutator kernel. -/
def MicrocausalityStatement (comm : CommutatorKernel) (spacelike : SpacelikeRelation) : Prop :=
  ∀ x y, spacelike x y → comm x y = 0

/-- Vanishing commutator surrogate (any spacelike relation). -/
def commutatorKernelZero : CommutatorKernel :=
  fun _ _ => (0 : ℝ)

/-- Degenerate “all pairs spacelike” relation (schema-only; not Minkowski causality). -/
def spacelikeRelationAll : SpacelikeRelation :=
  fun _ _ => True

theorem microcausality_zero_comm_allSpacelike_holds :
    MicrocausalityStatement commutatorKernelZero spacelikeRelationAll :=
  fun _ _ _ => rfl

/-!
### Minkowski spacelike relation (chart-level; signature $(+,{-},{-},{-})$)

Index `0` is the time coordinate. This upgrades the **causal predicate** in the
microcausality schema from the degenerate `spacelikeRelationAll` to genuine
η-spacelike separation. The commutator surrogate remains identically zero
(`commutatorKernelZero`), so the proof is still `rfl` — the progress is **structural**:
future operator-valued kernels can reuse the same `SpacelikeRelation` without changing
the formal hook.
-/

/-- Minkowski four-vector (continuum chart point). Convention: `v 0` is time. -/
abbrev SpacetimeChart := Fin 4 → ℝ

/-- Squared interval $\eta(z,z) = z^0^2 - z^1^2 - z^2^2 - z^3^2$ (units where $c=1$). -/
def minkowskiIntervalSq (z : SpacetimeChart) : ℝ :=
  z 0 * z 0 - z 1 * z 1 - z 2 * z 2 - z 3 * z 3

/-- Separation four-vector $x - y$. -/
def minkowskiSep (x y : SpacetimeChart) : SpacetimeChart :=
  fun i => x i - y i

/-- Strict spacelike separation: $\eta(x-y,x-y) < 0$ (same as Minkowski “spacelike”). -/
def minkowskiSpacelikeSep (x y : SpacetimeChart) : Prop :=
  minkowskiIntervalSq (minkowskiSep x y) < 0

/-- Same-time events with nonzero spatial separation are spacelike (standard fact). -/
theorem minkowski_spacelike_of_same_time {x y : SpacetimeChart}
    (ht : x 0 = y 0)
    (h : 0 < (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 + (x 3 - y 3) ^ 2) :
    minkowskiSpacelikeSep x y := by
  dsimp [minkowskiSpacelikeSep, minkowskiIntervalSq, minkowskiSep]
  have z0 : x 0 - y 0 = 0 := sub_eq_zero.mpr ht
  simp_rw [z0]
  nlinarith [h, sq_nonneg (x 1 - y 1), sq_nonneg (x 2 - y 2), sq_nonneg (x 3 - y 3)]

/-- Assigns each abstract event label a point in Minkowski space. -/
abbrev EventChart := EventLabel → SpacetimeChart

/-- Spacelike pairs **pulled back** along a chart: labels are spacelike iff their coordinates are. -/
def spacelikeRelationMinkowski (chart : EventChart) : SpacelikeRelation :=
  fun x y => minkowskiSpacelikeSep (chart x) (chart y)

theorem microcausality_zero_comm_minkowskiChart (chart : EventChart) :
    MicrocausalityStatement commutatorKernelZero (spacelikeRelationMinkowski chart) :=
  fun _ _ _ => rfl

/-- Chart-universal Minkowski microcausality (still with the zero commutator surrogate). -/
def microcausality_in_domain_minkowski_scaffold : Prop :=
  ∀ chart : EventChart, MicrocausalityStatement commutatorKernelZero (spacelikeRelationMinkowski chart)

theorem microcausality_in_domain_minkowski_scaffold_holds :
    microcausality_in_domain_minkowski_scaffold :=
  fun chart => microcausality_zero_comm_minkowskiChart chart

/-!
### Nontrivial commutator surrogate (positive on timelike pairs; still microcausal)

Take the **positive part** of the squared interval,
`max 0 (η(z,z))` with `z = x - y` in chart.  Then:

* If `η < 0` (spacelike), the kernel is `0` — **microcausality** holds for
  `spacelikeRelationMinkowski`.
* If `η > 0` (timelike), the kernel is strictly positive — **not** identically zero.

This is still a **scalar surrogate**, not an operator commutator, but it is the natural
next formal step toward nontrivial locality.
-/

/-- `max 0 (η(z,z))` along the chart separation; vanishes exactly when `η ≤ 0`. -/
noncomputable def commutatorKernelIntervalMax (chart : EventChart) : CommutatorKernel :=
  fun x y =>
    max (0 : ℝ) (minkowskiIntervalSq (minkowskiSep (chart x) (chart y)))

theorem microcausality_intervalMax_minkowski (chart : EventChart) :
    MicrocausalityStatement (commutatorKernelIntervalMax chart) (spacelikeRelationMinkowski chart) := by
  intro x y hsp
  unfold commutatorKernelIntervalMax spacelikeRelationMinkowski minkowskiSpacelikeSep at *
  have hη : minkowskiIntervalSq (minkowskiSep (chart x) (chart y)) < 0 := hsp
  rw [max_eq_left (le_of_lt hη)]

/-- Chart-universal statement: interval-max kernel is microcausal w.r.t. Minkowski spacelike. -/
def microcausality_in_domain_minkowski_interval_scaffold : Prop :=
  ∀ chart : EventChart, MicrocausalityStatement (commutatorKernelIntervalMax chart)
    (spacelikeRelationMinkowski chart)

theorem microcausality_in_domain_minkowski_interval_scaffold_holds :
    microcausality_in_domain_minkowski_interval_scaffold :=
  fun chart => microcausality_intervalMax_minkowski chart

/-- Example chart: events `0` and `1` lie on the time axis with nonzero separation (timelike). -/
noncomputable def chartTimelikeExample : EventChart
  | 0 => ![1, 0, 0, 0]
  | 1 => ![0, 0, 0, 0]
  | _ => ![0, 0, 0, 0]

theorem chartTimelikeExample_interval_sq :
    minkowskiIntervalSq (minkowskiSep (chartTimelikeExample 0) (chartTimelikeExample 1)) = 1 := by
  have hsep :
      minkowskiSep (chartTimelikeExample 0) (chartTimelikeExample 1) = ![1, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp [chartTimelikeExample, minkowskiSep, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hsep]
  simp [minkowskiIntervalSq, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem chartTimelikeExample_not_spacelike : ¬ spacelikeRelationMinkowski chartTimelikeExample 0 1 := by
  intro h
  unfold spacelikeRelationMinkowski minkowskiSpacelikeSep at h
  rw [chartTimelikeExample_interval_sq] at h
  linarith

theorem chartTimelikeExample_comm_ne_zero :
    commutatorKernelIntervalMax chartTimelikeExample 0 1 ≠ 0 := by
  unfold commutatorKernelIntervalMax
  rw [chartTimelikeExample_interval_sq]
  norm_num

/-- **Domain witness:** some chart has a **nonzero** `commutatorKernelIntervalMax` (timelike pair, η > 0). -/
theorem commutatorKernelIntervalMax_exists_ne_zero :
    ∃ ch : EventChart, ∃ x y : EventLabel, commutatorKernelIntervalMax ch x y ≠ 0 :=
  ⟨chartTimelikeExample, 0, 1, chartTimelikeExample_comm_ne_zero⟩

/-- Interval-max microcausality **holds** on all charts, **and** some chart has a **nonzero** surrogate on a pair (timelike / η > 0 domain). -/
theorem microcausality_intervalMax_scaffold_and_surrogate_nonzero :
    microcausality_in_domain_minkowski_interval_scaffold ∧
      (∃ ch : EventChart, ∃ x y : EventLabel, commutatorKernelIntervalMax ch x y ≠ 0) :=
  ⟨microcausality_in_domain_minkowski_interval_scaffold_holds, commutatorKernelIntervalMax_exists_ne_zero⟩

/-- There exist a chart and labels that are **not** spacelike but have **nonzero** interval-max commutator. -/
theorem commutatorKernelIntervalMax_nontrivial :
    ∃ ch : EventChart, ∃ x y : EventLabel,
      ¬ spacelikeRelationMinkowski ch x y ∧ commutatorKernelIntervalMax ch x y ≠ 0 :=
  ⟨chartTimelikeExample, 0, 1, chartTimelikeExample_not_spacelike, chartTimelikeExample_comm_ne_zero⟩

/-- Simple two-point correlation surrogate. -/
abbrev CorrelationKernel := EventLabel → EventLabel → ℝ

/-- Cluster-decomposition schema (lightweight surrogate): nearest-neighbor shift
correlation tends to zero at large label. -/
def ClusterDecompositionStatement (corr : CorrelationKernel) : Prop :=
  Filter.Tendsto (fun n : ℕ => corr n (n + 1)) Filter.atTop (nhds 0)

/-- Scattering consistency schema (lightweight surrogate): channel outputs lie in
`[0,1]`, matching probability-style consistency constraints. -/
def ScatteringConsistencyStatement (S : ℕ → ℝ) : Prop :=
  ∀ n, 0 ≤ S n ∧ S n ≤ 1

/-- Discrete UV regularity: explicit closed form for cumulative shell mode budget (`OctonionicLightCone`). -/
def RenormalizationInDomainStatement : Prop :=
  ∀ m : ℕ, Hqiv.available_modes m = (4 : ℝ) * ((m : ℝ) + 2) * ((m : ℝ) + 1)

/-- Proof from `Hqiv.available_modes_eq` (same ladder identity used throughout HQIV). -/
theorem renormalization_in_domain_discreteUV_holds : RenormalizationInDomainStatement := fun m =>
  Hqiv.available_modes_eq m

/-- Backward-compatible alias (formerly the `True` placeholder; now the discrete-UV statement). -/
theorem renormalization_in_domain_trivial_holds : RenormalizationInDomainStatement :=
  renormalization_in_domain_discreteUV_holds

/-- Zero two-point kernel: cluster surrogate `corr n (n+1)` is identically `0`. -/
noncomputable def clusterCorrelationZero : CorrelationKernel :=
  fun _ _ => (0 : ℝ)

theorem cluster_decomposition_zero_kernel_holds :
    ClusterDecompositionStatement clusterCorrelationZero := by
  dsimp [ClusterDecompositionStatement, clusterCorrelationZero]
  exact tendsto_const_nhds (f := atTop) (x := (0 : ℝ))

/--
Directional monogamy/redshift kernel.

Interpretation: coherent sharing is concentrated on the forward travel channel
`x ↦ x + 1`; the available coherent budget is capped by `coherenceProxy x τPair`,
and propagation redshifts it by an additional inverse shell factor `1 / phi_of_shell x`.
-/
noncomputable def clusterCorrelationDirectionalMonogamyRedshift (τPair : ℝ) : CorrelationKernel :=
  fun x y =>
    if y = x + 1 then coherenceProxy x τPair / phi_of_shell x else 0

/-- On the forward channel, the directional monogamy/redshift kernel is exactly `coherenceProxy / phi_of_shell`. -/
theorem clusterCorrelationDirectionalMonogamyRedshift_succ (τPair : ℝ) (n : ℕ) :
    clusterCorrelationDirectionalMonogamyRedshift τPair n (n + 1) =
      coherenceProxy n τPair / phi_of_shell n := by
  simp [clusterCorrelationDirectionalMonogamyRedshift]

/-- Closed form: the directional monogamy/redshift kernel is a constant monogamy budget over `2 (n+1)`. -/
theorem clusterCorrelationDirectionalMonogamyRedshift_succ_eq_const_div (τPair : ℝ) (n : ℕ) :
    clusterCorrelationDirectionalMonogamyRedshift τPair n (n + 1) =
      (1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) /
        (2 * (n + 1 : ℝ)) := by
  rw [clusterCorrelationDirectionalMonogamyRedshift_succ, coherenceProxy, etaModePhi_constant,
    phi_of_shell_linear]

/-- The directional monogamy/redshift kernel is a genuine nonzero witness whenever `τPair ≠ 0`. -/
theorem clusterCorrelationDirectionalMonogamyRedshift_nonzero_at_zero {τPair : ℝ} (hτ : τPair ≠ 0) :
    clusterCorrelationDirectionalMonogamyRedshift τPair 0 1 ≠ 0 := by
  rw [clusterCorrelationDirectionalMonogamyRedshift_succ_eq_const_div τPair 0]
  norm_num
  exact ⟨⟨by positivity, by positivity⟩, hτ⟩

/-- Cluster decomposition for the directional forward-channel kernel: monogamy budget times shell redshift tends to `0`. -/
theorem cluster_decomposition_directional_monogamy_redshift_holds (τPair : ℝ) :
    ClusterDecompositionStatement (clusterCorrelationDirectionalMonogamyRedshift τPair) := by
  dsimp [ClusterDecompositionStatement]
  have hC :
      (fun n : ℕ =>
        clusterCorrelationDirectionalMonogamyRedshift τPair n (n + 1)) =
      fun n : ℕ =>
        ((1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) / 2) *
          (1 / (n + 1 : ℝ)) := by
    funext n
    rw [clusterCorrelationDirectionalMonogamyRedshift_succ_eq_const_div]
    have hn' : (n + 1 : ℝ) ≠ 0 := by positivity
    have htwo : 1 / (2 * (n + 1 : ℝ)) = (1 / 2 : ℝ) * (1 / (n + 1 : ℝ)) := by
      field_simp [hn']
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hC]
  have hone' :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
    ((tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0)).comp
      (tendsto_add_atTop_nat 1))
  have hone :
      Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    convert hone' using 1
    funext n
    simp
  have hlim :
      Tendsto
        (fun n : ℕ =>
          ((1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) / 2) *
            (1 / (n + 1 : ℝ)))
        atTop
        (𝓝
          (((1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) / 2) * 0)) :=
    (tendsto_const_nhds (x := ((1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) / 2))).mul hone
  simpa using hlim

/-- Photon-geodesic transport factor: the observed unit-energy channel under birefringence redshift after `n+1` shell/time steps. -/
noncomputable def photonGeodesicTransportN (kappaBeta : ℝ) (n : ℕ) : ℝ :=
  redshiftedEnergyN 1 (birefringenceRedshiftN ((n : ℝ) + 1) kappaBeta)

/-- General photon-geodesic transport driven by an HQIV scale function. -/
noncomputable def photonGeodesicTransportFromScale (scale : ℕ → ℝ) (kappaBeta : ℝ) (n : ℕ) : ℝ :=
  redshiftedEnergyN 1 (birefringenceRedshiftN (scale n) kappaBeta)

/-- The photon geodesic transport factor is exactly exponential attenuation. -/
theorem photonGeodesicTransportN_eq_exp_neg_div (kappaBeta : ℝ) (n : ℕ) :
    photonGeodesicTransportN kappaBeta n = Real.exp (-(((n : ℝ) + 1) / kappaBeta)) := by
  unfold photonGeodesicTransportN redshiftedEnergyN
  rw [one_add_birefringenceRedshiftN ((n : ℝ) + 1) kappaBeta]
  simpa [div_eq_mul_inv] using (Real.exp_neg (((n : ℝ) + 1) / kappaBeta)).symm

/-- Any HQIV scale inserted into the birefringence redshift channel gives exponential attenuation. -/
theorem photonGeodesicTransportFromScale_eq_exp_neg_div
    (scale : ℕ → ℝ) (kappaBeta : ℝ) (n : ℕ) :
    photonGeodesicTransportFromScale scale kappaBeta n =
      Real.exp (-(scale n / kappaBeta)) := by
  unfold photonGeodesicTransportFromScale redshiftedEnergyN
  rw [one_add_birefringenceRedshiftN (scale n) kappaBeta]
  simpa [div_eq_mul_inv] using (Real.exp_neg (scale n / kappaBeta)).symm

/-- Positive birefringence scale gives genuine photon-geodesic decoherence along the forward channel. -/
theorem photonGeodesicTransportN_tendsto_zero (kappaBeta : ℝ) (hκ : 0 < kappaBeta) :
    Tendsto (photonGeodesicTransportN kappaBeta) atTop (𝓝 0) := by
  rw [show photonGeodesicTransportN kappaBeta = fun n : ℕ => Real.exp (-(((n : ℝ) + 1) / kappaBeta)) by
    funext n
    exact photonGeodesicTransportN_eq_exp_neg_div kappaBeta n]
  have htop : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hbot :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) * (-(1 / kappaBeta))) atTop atBot :=
    (tendsto_mul_const_atBot_of_neg (by
      have : 0 < 1 / kappaBeta := one_div_pos.mpr hκ
      linarith)).2 htop
  have hexpArg : Tendsto (fun n : ℕ => -(((n : ℝ) + 1) / kappaBeta)) atTop atBot := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbot
  exact Real.tendsto_exp_atBot.comp hexpArg

/-- Any scale that tends to `atTop` gives photon-geodesic transport decaying to `0`. -/
theorem photonGeodesicTransportFromScale_tendsto_zero
    (scale : ℕ → ℝ) (kappaBeta : ℝ)
    (hscale : Tendsto scale atTop atTop) (hκ : 0 < kappaBeta) :
    Tendsto (photonGeodesicTransportFromScale scale kappaBeta) atTop (𝓝 0) := by
  rw [show photonGeodesicTransportFromScale scale kappaBeta =
      fun n : ℕ => Real.exp (-(scale n / kappaBeta)) by
        funext n
        exact photonGeodesicTransportFromScale_eq_exp_neg_div scale kappaBeta n]
  have hbot : Tendsto (fun n : ℕ => scale n * (-(1 / kappaBeta))) atTop atBot :=
    (tendsto_mul_const_atBot_of_neg (by
      have : 0 < 1 / kappaBeta := one_div_pos.mpr hκ
      linarith)).2 hscale
  have hexpArg : Tendsto (fun n : ℕ => -(scale n / kappaBeta)) atTop atBot := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbot
  exact Real.tendsto_exp_atBot.comp hexpArg

/-- Photon mode budget scale on shell `n`; matches the finite-patch photon budget used downstream. -/
noncomputable def photonModeBudgetScaleN (n : ℕ) : ℝ :=
  Hqiv.available_modes n

/-- The photon mode budget scale tends to `atTop`. -/
theorem photonModeBudgetScaleN_tendsto_atTop :
    Tendsto photonModeBudgetScaleN atTop atTop := by
  rw [show photonModeBudgetScaleN = fun n : ℕ => (4 : ℝ) * (((n : ℝ) + 2) * ((n : ℝ) + 1)) by
    funext n
    rw [photonModeBudgetScaleN, Hqiv.available_modes_eq]
    ring]
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => (((n : ℝ) + 2) * ((n : ℝ) + 1))) atTop atTop :=
    h1.atTop_mul_atTop₀ h2
  exact Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) hmul

/-- Photon-geodesic transport using the cumulative photon mode budget as the transport scale. -/
noncomputable def photonModeBudgetTransportN (kappaBeta : ℝ) (n : ℕ) : ℝ :=
  photonGeodesicTransportFromScale photonModeBudgetScaleN kappaBeta n

/-- Closed form for the photon-mode-budget transport factor. -/
theorem photonModeBudgetTransportN_eq_exp_neg_div (kappaBeta : ℝ) (n : ℕ) :
    photonModeBudgetTransportN kappaBeta n =
      Real.exp (-(photonModeBudgetScaleN n / kappaBeta)) := by
  exact photonGeodesicTransportFromScale_eq_exp_neg_div photonModeBudgetScaleN kappaBeta n

/-- Positive birefringence scale gives vanishing photon-budget transport. -/
theorem photonModeBudgetTransportN_tendsto_zero (kappaBeta : ℝ) (hκ : 0 < kappaBeta) :
    Tendsto (photonModeBudgetTransportN kappaBeta) atTop (𝓝 0) := by
  exact photonGeodesicTransportFromScale_tendsto_zero photonModeBudgetScaleN kappaBeta
    photonModeBudgetScaleN_tendsto_atTop hκ

/--
Directional monogamy kernel with photon-geodesic transport.

Interpretation: the pairwise coherence budget is still capped by `coherenceProxy`,
but transport now follows the finite measurement ledger's photon redshift channel
instead of a shell-only inverse-`phi` damping.
-/
noncomputable def clusterCorrelationDirectionalMonogamyPhotonGeodesic
    (τPair kappaBeta : ℝ) : CorrelationKernel :=
  fun x y =>
    if y = x + 1 then coherenceProxy x τPair * photonGeodesicTransportN kappaBeta x else 0

/-- On the forward channel, the photon-geodesic kernel is `coherenceProxy * photonGeodesicTransportN`. -/
theorem clusterCorrelationDirectionalMonogamyPhotonGeodesic_succ
    (τPair kappaBeta : ℝ) (n : ℕ) :
    clusterCorrelationDirectionalMonogamyPhotonGeodesic τPair kappaBeta n (n + 1) =
      coherenceProxy n τPair * photonGeodesicTransportN kappaBeta n := by
  simp [clusterCorrelationDirectionalMonogamyPhotonGeodesic]

/-- Closed form: constant monogamy budget times photon-geodesic exponential attenuation. -/
theorem clusterCorrelationDirectionalMonogamyPhotonGeodesic_succ_eq
    (τPair kappaBeta : ℝ) (n : ℕ) :
    clusterCorrelationDirectionalMonogamyPhotonGeodesic τPair kappaBeta n (n + 1) =
      (1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) *
        Real.exp (-(((n : ℝ) + 1) / kappaBeta)) := by
  rw [clusterCorrelationDirectionalMonogamyPhotonGeodesic_succ, coherenceProxy,
    etaModePhi_constant, photonGeodesicTransportN_eq_exp_neg_div]

/-- For positive birefringence scale and nonzero pair budget, the photon-geodesic kernel is nontrivial. -/
theorem clusterCorrelationDirectionalMonogamyPhotonGeodesic_nonzero_at_zero
    {τPair kappaBeta : ℝ} (hτ : τPair ≠ 0) :
    clusterCorrelationDirectionalMonogamyPhotonGeodesic τPair kappaBeta 0 1 ≠ 0 := by
  rw [clusterCorrelationDirectionalMonogamyPhotonGeodesic_succ_eq]
  refine mul_ne_zero ?_ (Real.exp_ne_zero _)
  exact mul_ne_zero (by positivity) hτ

/-- Cluster decomposition for the photon-geodesic forward kernel. -/
theorem cluster_decomposition_directional_monogamy_photonGeodesic_holds
    (τPair kappaBeta : ℝ) (hκ : 0 < kappaBeta) :
    ClusterDecompositionStatement (clusterCorrelationDirectionalMonogamyPhotonGeodesic τPair kappaBeta) := by
  dsimp [ClusterDecompositionStatement]
  have hC :
      (fun n : ℕ =>
        clusterCorrelationDirectionalMonogamyPhotonGeodesic τPair kappaBeta n (n + 1)) =
      fun n : ℕ =>
        (1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) *
          photonGeodesicTransportN kappaBeta n := by
    funext n
    rw [clusterCorrelationDirectionalMonogamyPhotonGeodesic_succ_eq]
    rw [photonGeodesicTransportN_eq_exp_neg_div]
  rw [hC]
  have hlim :
      Tendsto
        (fun n : ℕ =>
          (1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) *
            photonGeodesicTransportN kappaBeta n)
        atTop
        (𝓝
          ((1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) * 0)) :=
    (tendsto_const_nhds (x := (1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair))).mul
      (photonGeodesicTransportN_tendsto_zero kappaBeta hκ)
  simpa using hlim

/--
Directional monogamy kernel with photon-mode-budget transport.

Interpretation: the monogamy budget is transported through the cumulative photon
mode budget rather than only by shell step count.
-/
noncomputable def clusterCorrelationDirectionalMonogamyPhotonBudget
    (τPair kappaBeta : ℝ) : CorrelationKernel :=
  fun x y =>
    if y = x + 1 then coherenceProxy x τPair * photonModeBudgetTransportN kappaBeta x else 0

/-- On the forward channel, the photon-budget kernel is `coherenceProxy * photonModeBudgetTransportN`. -/
theorem clusterCorrelationDirectionalMonogamyPhotonBudget_succ
    (τPair kappaBeta : ℝ) (n : ℕ) :
    clusterCorrelationDirectionalMonogamyPhotonBudget τPair kappaBeta n (n + 1) =
      coherenceProxy n τPair * photonModeBudgetTransportN kappaBeta n := by
  simp [clusterCorrelationDirectionalMonogamyPhotonBudget]

/-- Closed form: constant monogamy budget times photon-budget transport. -/
theorem clusterCorrelationDirectionalMonogamyPhotonBudget_succ_eq
    (τPair kappaBeta : ℝ) (n : ℕ) :
    clusterCorrelationDirectionalMonogamyPhotonBudget τPair kappaBeta n (n + 1) =
      (1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) *
        Real.exp (-(photonModeBudgetScaleN n / kappaBeta)) := by
  rw [clusterCorrelationDirectionalMonogamyPhotonBudget_succ, coherenceProxy,
    etaModePhi_constant, photonModeBudgetTransportN_eq_exp_neg_div]

/-- For positive birefringence scale and nonzero pair budget, the photon-budget kernel is nontrivial. -/
theorem clusterCorrelationDirectionalMonogamyPhotonBudget_nonzero_at_zero
    {τPair kappaBeta : ℝ} (hτ : τPair ≠ 0) :
    clusterCorrelationDirectionalMonogamyPhotonBudget τPair kappaBeta 0 1 ≠ 0 := by
  rw [clusterCorrelationDirectionalMonogamyPhotonBudget_succ_eq]
  refine mul_ne_zero ?_ (Real.exp_ne_zero _)
  exact mul_ne_zero (by positivity) hτ

/-- Cluster decomposition for the photon-budget forward kernel. -/
theorem cluster_decomposition_directional_monogamy_photonBudget_holds
    (τPair kappaBeta : ℝ) (hκ : 0 < kappaBeta) :
    ClusterDecompositionStatement (clusterCorrelationDirectionalMonogamyPhotonBudget τPair kappaBeta) := by
  dsimp [ClusterDecompositionStatement]
  have hC :
      (fun n : ℕ =>
        clusterCorrelationDirectionalMonogamyPhotonBudget τPair kappaBeta n (n + 1)) =
      fun n : ℕ =>
        (1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) *
          photonModeBudgetTransportN kappaBeta n := by
    funext n
    rw [clusterCorrelationDirectionalMonogamyPhotonBudget_succ_eq]
    rw [photonModeBudgetTransportN_eq_exp_neg_div]
  rw [hC]
  have hlim :
      Tendsto
        (fun n : ℕ =>
          (1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) *
            photonModeBudgetTransportN kappaBeta n)
        atTop
        (𝓝
          ((1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair) * 0)) :=
    (tendsto_const_nhds (x := (1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) * τPair))).mul
      (photonModeBudgetTransportN_tendsto_zero kappaBeta hκ)
  simpa using hlim

/-- Trivial scattering channel: all outputs are `0` (valid probability-style surrogate). -/
noncomputable def scatteringChannelZero : ℕ → ℝ := fun _ => (0 : ℝ)

theorem scattering_consistency_zero_channel_holds :
    ScatteringConsistencyStatement scatteringChannelZero := by
  intro n
  simp [scatteringChannelZero, zero_le_one]

/-- Unit scattering surrogate (identity lossless channel in `[0,1]`). -/
noncomputable def scatteringChannelUnit : ℕ → ℝ := fun _ => (1 : ℝ)

theorem scattering_consistency_unit_channel_holds :
    ScatteringConsistencyStatement scatteringChannelUnit := by
  intro n
  exact ⟨zero_le_one, le_rfl⟩

/-- Associator/vorticity scattering channel: `‖[e₁,e₂,e₄]‖² / (‖·‖²+1)` in `[0,1]` (non-zero generically). -/
noncomputable def scatteringChannelAssociatorVorticity : ℕ → ℝ :=
  fun _ => scatteringAmpFromAssociator e1 e2 e4

theorem scatteringAmpFromAssociator_mem_unit (x y z : OctonionVec) :
    0 ≤ scatteringAmpFromAssociator x y z ∧ scatteringAmpFromAssociator x y z ≤ 1 := by
  have ha : 0 ≤ octonionAssociatorNormSq x y z := by
    unfold octonionAssociatorNormSq
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hden : 0 < octonionAssociatorNormSq x y z + 1 := by
    have h1 : (1 : ℝ) ≤ octonionAssociatorNormSq x y z + 1 := by linarith [ha]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h1
  unfold scatteringAmpFromAssociator
  refine ⟨div_nonneg ha (le_of_lt hden), ?_⟩
  rw [div_le_one hden]
  linarith [ha]

theorem scattering_consistency_associatorVorticity_holds :
    ScatteringConsistencyStatement scatteringChannelAssociatorVorticity := by
  intro n
  simpa [scatteringChannelAssociatorVorticity] using scatteringAmpFromAssociator_mem_unit e1 e2 e4

/-- Compact structured bundle mirroring the five continuum obligations. -/
structure ContinuumManyBodyAxioms where
  shell_to_harmonic_limit : ShellToHarmonicLimit
  renormalization_in_domain : RenormalizationInDomainStatement
  microcausality_in_domain : Prop
  cluster_decomposition_in_domain : Prop
  scattering_consistency_in_domain : Prop

/-- A concrete worked instance: shell/harmonic limit discharged constructively;
remaining slots filled by simple witness kernels to keep the scaffold executable. -/
def continuum_many_body_axioms_worked_example : ContinuumManyBodyAxioms :=
  { shell_to_harmonic_limit := shell_to_harmonic_limit_holds
    renormalization_in_domain := renormalization_in_domain_discreteUV_holds
    microcausality_in_domain := MicrocausalityStatement commutatorKernelZero spacelikeRelationAll
    cluster_decomposition_in_domain := ClusterDecompositionStatement clusterCorrelationZero
    scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelZero }

theorem continuum_many_body_axioms_worked_example_micro_holds :
    continuum_many_body_axioms_worked_example.microcausality_in_domain :=
  microcausality_zero_comm_allSpacelike_holds

theorem continuum_many_body_axioms_worked_example_cluster_holds :
    continuum_many_body_axioms_worked_example.cluster_decomposition_in_domain :=
  cluster_decomposition_zero_kernel_holds

theorem continuum_many_body_axioms_worked_example_scattering_holds :
    continuum_many_body_axioms_worked_example.scattering_consistency_in_domain :=
  scattering_consistency_zero_channel_holds

end Hqiv.QM
