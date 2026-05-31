import Hqiv.Topology.DiscretePhaseEvolution
import Hqiv.Topology.ShellOpeningEvolution

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
    evo.IsEquilibrium M → IsS3NullVertexTemplate M n
  /-- Opening / template-pinned flows reach equilibrium on the certified complex. -/
  terminal_eq :
    ∀ k M', evo.iterate k M = some M' → evo.IsEquilibrium M' → M' = M

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
  have hM' := cert.terminal_eq k M' hiter heq
  exact ⟨k, M', hiter, hM'.symm ▸ cert.equilibrium_template (hM' ▸ heq)⟩

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

/-- Placeholder holonomy certificate (same fields as `ParallelPoincareReferenceModel.referenceSO8Admissible`). -/
def referenceSO8Admissible (_n : ℕ) (M : Discrete3Complex NullShellVertex) :
    SO8AdmissibleHolonomy M where
  fields_g2_delta_recoverable := True
  uses_six_pack_middle_chart := True
  two_e1_e4_rotations := True
  triality_three_slots := True
  diophantine_phase_readout := True
  delta_resolves_pinched_links := True
  bracket_closure_symbolic := so8_bracket_closure_symbolic

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

theorem shellOpening_equilibrium_is_S3NullReference (α : ℝ) (n : ℕ) (href : 0 < K n α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) (hmax : maxVertexShell M = n)
    (hdef : deficitOnlyOnHorizon M n) (hq : QuadraticNullShellGrowthOnHorizon M n)
    (heq : (shellOpeningEvolution α n href).IsEquilibrium M) :
    IsS3NullReference M n :=
  quadraticOnHorizon_is_S3NullReference M n hq (by simpa [hmax] using le_rfl)

/-- At a converged opening equilibrium (`totalNegativeBudget = 0` on a deficit-only horizon state). -/
noncomputable def shellOpeningConvergedTemplateCertificate (α : ℝ) (n : ℕ) (href : 0 < K n α) (hα : 0 < α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) (hmax : maxVertexShell M = n)
    (hdef : deficitOnlyOnHorizon M n) (hq : QuadraticNullShellGrowthOnHorizon M n)
    (heq : (shellOpeningEvolution α n href).IsEquilibrium M) :
    ParallelPoincareTemplateCertificate (shellOpeningEvolution α n href) M n where
  growth := hq
  holonomy := referenceSO8Admissible n M
  extinction_excluded := fun k => by
    rcases k with _ | k
    · intro h; cases h
    · intro hnone
      simpa [shellOpening_iterate_succ_eq_self_at_equilibrium α n href M hV heq k] using hnone
  equilibrium_template heq' :=
    shellOpening_equilibrium_is_S3NullReference α n href M hV hmax hdef hq heq'
  terminal_eq k M' hiter _heqM' := by
    have hm := shellOpening_iterate_eq_self_at_equilibrium α n href M hV heq k
    exact Option.some.inj (hiter.symm.trans hm)

/-- `of_real_descent` for opening flow at horizon `n`, at a converged equilibrium complex. -/
noncomputable def of_shell_opening_real_descent (α : ℝ) (n : ℕ) (href : 0 < K n α) (hα : 0 < α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) (hmax : maxVertexShell M = n)
    (hdef : deficitOnlyOnHorizon M n) (hq : QuadraticNullShellGrowthOnHorizon M n)
    (heq : (shellOpeningEvolution α n href).IsEquilibrium M) :
    DiscreteParallelPoincareHypothesis :=
  let evo := shellOpeningEvolution α n href
  of_real_descent evo
    { M := M
      no_boundary := by
        intro e he
        rcases hV with ⟨hedges, _, _⟩
        simpa [hedges] using he
      maxShell := n
      quadraticGrowthOnHorizon := hq
      so8Admissible := referenceSO8Admissible n M }
    (shellOpeningUsesCurvatureChannel α n href hα)
    (shellOpeningRealLyapunovDescent α n href)
    (shellOpeningConvergedTemplateCertificate α n href hα M hV hmax hdef hq heq)

/-- From a deficit-only horizon initial state, opening reaches `S3NullReference` and yields a
`DiscreteParallelPoincareHypothesis` at the converged equilibrium. -/
theorem shell_opening_discrete_parallel_poincare_at_horizon (α : ℝ) (n : ℕ) (href : 0 < K n α) (hα : 0 < α)
    (M₀ : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M₀)
    (hmax : maxVertexShell M₀ = n) (hdef : deficitOnlyOnHorizon M₀ n) :
    ∃ k M', (shellOpeningEvolution α n href).iterate k M₀ = some M' ∧
      IsS3NullReference M' n ∧
      ∃ H : DiscreteParallelPoincareHypothesis,
        H.evo = shellOpeningEvolution α n href ∧
          H.data.M = M' ∧ IsS3NullReference H.data.M n := by
  rcases shellOpening_reaches_zero_totalNegative α n href M₀ hV with ⟨k, M', hiter, hz⟩
  have hV' := IsVertexOnly_of_shellOpening_iterate α n href k M₀ hV M' hiter
  have hmax' := maxVertexShell_eq_of_shellOpening_iterate α n href n k M₀ hV hmax M' hiter
  have hdef' := deficitOnlyOnHorizon_of_shellOpening_iterate α n href n k M₀ hV hmax hdef M' hiter
  have heq := (shellOpening_equilibrium_iff_totalNegative_zero α n href M' hV').mpr hz
  have hq := deficitOnly_no_negative_budget_imp_quadraticOnHorizon M' n hdef'
    (by simpa [hmax'] using le_rfl) (shellOpening_not_negative_on_active_of_totalNeg_zero M' hz)
  have htmpl := quadraticOnHorizon_is_S3NullReference M' n hq (by simpa [hmax'] using le_rfl)
  refine ⟨k, M', hiter, htmpl, ?_⟩
  refine ⟨of_shell_opening_real_descent α n href hα M' hV' hmax' hdef' hq heq, rfl, rfl, htmpl⟩

end DiscreteParallelPoincareHypothesis

theorem discrete_parallel_poincare (H : DiscreteParallelPoincareHypothesis) :
    ∃ k M',
      H.evo.iterate k H.data.M = some M' ∧
        IsS3NullVertexTemplate M' H.data.maxShell :=
  discrete_parallel_poincare_from_template H.evo H.data.M H.data.maxShell
    (DiscreteParallelPoincareHypothesis.evolutionTerminates H) H.templateCertificate

end Hqiv.Topology
