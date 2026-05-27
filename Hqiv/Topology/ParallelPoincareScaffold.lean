import Hqiv.Topology.DiscretePhaseEvolution

/-!
# Parallel Poincaré programme (roadmap + template track)

HQIV-native topology as **output** of null-lattice combinatorics on a finite horizon
`0 … n`, not a Perelman-style Ricci flow.

## Proved here (template track)

* `HolonomyViaHorizonGrowth` — horizon quadratic shell law + `SO8AdmissibleHolonomy`.
* `ParallelPoincareTemplateCertificate` — no extinction + equilibrium ⇒ `S3NullReference` template.
* `discrete_parallel_poincare_from_template` / `discrete_parallel_poincare`.

Live end-to-end witness: `Hqiv.Topology.ParallelPoincareReferenceModel`.

## Proved elsewhere (obstructions — do not re-prove)

* `not_quadratic_null_shell_growth` — global `QuadraticNullShellGrowth` (∀ `m : ℕ`) is impossible on
  finite complexes (`DiscreteNullLatticeComplex`).
* `S3NullReference_quadratic_on_horizon` — correct finite law on the reference complex.
* `S3NullReference_not_combinatorially_spherical` — vertex-only reference has χ ≠ 0.

## Roadmap (not formalized as theorems in this file)

| Milestone | Blocker |
|-----------|---------|
| **χ track** | Triangulated `Discrete3Complex` (1/2/3-cells); χ = 0 does not follow from shell vertices alone. |
| **Real `step`** | Curvature-channel evolution with nontrivial `linkDeficit`; discharge certificate fields without axioms. |
| **ℝ Lyapunov** | Unconditional descent while `linkDeficit ≡ 0` — use `NatLyapunovDescent` / `RealLyapunovDescent` certificates (`DiscretePhaseEvolution`). |
| **Continuum** | Refinement + mesh → 0 + Gromov–Hausdorff limit recovering classical Poincaré. |
| **Link holonomy** | `link ↦ G2DeltaHolonomyCoeffs.toMatrix` on complexes (`G2Embedding`). |
-/

namespace Hqiv.Topology

open Hqiv RhFourierLift

/-!
## Inputs
-/

structure HolonomyViaHorizonGrowth (M : Discrete3Complex NullShellVertex) (n : ℕ) where
  growth : QuadraticNullShellGrowthOnHorizon M n
  holonomy : SO8AdmissibleHolonomy M

/-- Template-track certificate: termination reaches `S3NullReference n` combinatorics. -/
structure ParallelPoincareTemplateCertificate
    (evo : DiscreteCurvatureEvolution) (M : Discrete3Complex NullShellVertex) (n : ℕ)
    extends HolonomyViaHorizonGrowth M n where
  extinction_excluded : ∀ k, evo.iterate k M ≠ none
  equilibrium_template :
    ∀ Mₜ, evo.IsEquilibrium Mₜ → IsS3NullVertexTemplate Mₜ n

/-- χ-track certificate (future milestone; obstructed on vertex-only `S3NullReference`). -/
structure ParallelPoincareChiCertificate
    (evo : DiscreteCurvatureEvolution) (M : Discrete3Complex NullShellVertex) (n : ℕ) where
  equilibrium_chi_zero :
    ∀ Mₜ, evo.IsEquilibrium Mₜ → Mₜ.eulerCharacteristic = 0

/-!
## Obstruction lemmas (finite horizon vs global growth / χ)
-/

theorem parallel_poincare_global_growth_obstruction
    (M : Discrete3Complex NullShellVertex) (h_growth : QuadraticNullShellGrowth M) : False :=
  not_quadratic_null_shell_growth M h_growth

theorem parallel_poincare_bridge_obstruction (M : Discrete3Complex NullShellVertex) (n : ℕ) :
    (¬ QuadraticNullShellGrowth M) ∧
      QuadraticNullShellGrowthOnHorizon (S3NullReference n) n ∧
      ¬ IsCombinatoriallySpherical (S3NullReference n) := by
  refine ⟨not_quadratic_null_shell_growth M, ?_, S3NullReference_not_combinatorially_spherical n⟩
  exact S3NullReference_quadratic_on_horizon n

/-!
## Template convergence (proved from certificate + termination)
-/

theorem discrete_parallel_poincare_from_template
    (evo : DiscreteCurvatureEvolution)
    (M : Discrete3Complex NullShellVertex)
    (n : ℕ)
    (h_term : FlowTerminatesAt evo M)
    (cert : ParallelPoincareTemplateCertificate evo M n) :
    ∃ k M',
      evo.iterate k M = some M' ∧
        IsS3NullVertexTemplate M' n := by
  rcases FlowTerminatesAt.exists_equilibrium_of_no_extinction evo M h_term
      cert.extinction_excluded with
    ⟨k, M', hiter, heq⟩
  exact ⟨k, M', hiter, cert.equilibrium_template M' heq⟩

theorem discrete_parallel_poincare_from_template_of_real_descent
    (evo : DiscreteCurvatureEvolution)
    (M : Discrete3Complex NullShellVertex)
    (n : ℕ)
    (h_descent : RealLyapunovDescent evo)
    (cert : ParallelPoincareTemplateCertificate evo M n) :
    ∃ k M',
      evo.iterate k M = some M' ∧
        IsS3NullVertexTemplate M' n :=
  discrete_parallel_poincare_from_template evo M n
    (flow_terminates_at_of_real_descent evo h_descent M) cert

/-!
## Packaged hypothesis
-/

structure DiscreteParallelPoincareData where
  M : Discrete3Complex NullShellVertex
  no_boundary :
    ∀ e ∈ M.edges, ∃ t ∈ M.triangles, e.a = t.1 ∧ e.b = t.2.1 ∨ e.a = t.2.1 ∧ e.b = t.1
  maxShell : ℕ
  quadraticGrowthOnHorizon : QuadraticNullShellGrowthOnHorizon M maxShell
  so8Admissible : SO8AdmissibleHolonomy M

def DiscreteParallelPoincareData.holonomyViaHorizon (D : DiscreteParallelPoincareData) :
    HolonomyViaHorizonGrowth D.M D.maxShell :=
  { growth := D.quadraticGrowthOnHorizon
    holonomy := D.so8Admissible }

structure DiscreteParallelPoincareHypothesis where
  evo : DiscreteCurvatureEvolution
  data : DiscreteParallelPoincareData
  curvatureChannel : UsesCurvatureChannel evo
  flowTerminates : FlowTerminatesAt evo data.M
  templateCertificate : ParallelPoincareTemplateCertificate evo data.M data.maxShell

namespace DiscreteParallelPoincareHypothesis

theorem evolutionTerminates (H : DiscreteParallelPoincareHypothesis) :
    FlowTerminatesAt H.evo H.data.M :=
  H.flowTerminates

noncomputable def of_real_descent (evo : DiscreteCurvatureEvolution) (data : DiscreteParallelPoincareData)
    (curvatureChannel : UsesCurvatureChannel evo) (realDescent : RealLyapunovDescent evo)
    (templateCertificate : ParallelPoincareTemplateCertificate evo data.M data.maxShell) :
    DiscreteParallelPoincareHypothesis :=
  { evo := evo, data := data, curvatureChannel := curvatureChannel,
    flowTerminates := flow_terminates_at_of_real_descent evo realDescent data.M,
    templateCertificate := templateCertificate }

end DiscreteParallelPoincareHypothesis

theorem discrete_parallel_poincare (H : DiscreteParallelPoincareHypothesis) :
    ∃ k M',
      H.evo.iterate k H.data.M = some M' ∧
        IsS3NullVertexTemplate M' H.data.maxShell :=
  discrete_parallel_poincare_from_template H.evo H.data.M H.data.maxShell
    (DiscreteParallelPoincareHypothesis.evolutionTerminates H) H.templateCertificate

end Hqiv.Topology
