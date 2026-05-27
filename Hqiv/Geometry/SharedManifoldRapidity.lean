import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic

/-!
# Shared-manifold rapidity interface (minimal)

`SATSharedManifold`, profiles, the smooth-bridge record, and
`shared_manifold_induces_common_rapidity` — the slice needed by
`Hqiv.Story.CausalRapidityForcing` / `HQIVPaperClaims`.

The larger SAT rapidity scaffold (successor-step bounds, polynomial budgets, etc.)
lives in `Hqiv.Geometry.SATRapidityManifold` and is **not** required for the
closure-focused publication bundle.
-/

namespace Hqiv.Geometry

noncomputable section

/--
Shared SAT manifold with variable and clause embeddings into one ambient space.
We keep the ambient carrier abstract (`M`) and record only the data needed to
express a common rapidity channel.
-/
structure SATSharedManifold (M : Type*) where
  varDim : ℕ
  clauseDim : ℕ
  embedVar : Fin varDim → M
  embedClause : Fin clauseDim → M

/--
Scalar rapidity observable on the shared manifold: the common channel through
which variable-side and clause-side geometry are compared.
-/
abbrev SharedRapidityObservable (M : Type*) := M → ℝ

/-- Rapidity seen from the variable embedding. -/
def variableRapidityProfile
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M) : Fin S.varDim → ℝ :=
  fun i => ρ (S.embedVar i)

/-- Rapidity seen from the clause embedding. -/
def clauseRapidityProfile
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M) : Fin S.clauseDim → ℝ :=
  fun j => ρ (S.embedClause j)

/--
Smooth manifold bridge: chart maps from Euclidean parameter spaces into `M`,
together with a chosen rapidity readout and existence of chart preimages for each
embedded variable/clause point.

(This record is intentionally lightweight: it packages only what is needed to
state the common-rapidity transport lemma below.)
-/
structure SATSharedManifoldSmoothBridge (M : Type*) [TopologicalSpace M] where
  shared : SATSharedManifold M
  chartVar : (Fin shared.varDim → ℝ) → M
  chartClause : (Fin shared.clauseDim → ℝ) → M
  rapidity : SharedRapidityObservable M
  hVarEmbed : ∀ i : Fin shared.varDim, ∃ x : Fin shared.varDim → ℝ, chartVar x = shared.embedVar i
  hClauseEmbed : ∀ j : Fin shared.clauseDim, ∃ y : Fin shared.clauseDim → ℝ, chartClause y = shared.embedClause j

/--
Once the bridge carries a rapidity observable `B.rapidity`, that same map is a
`SharedRapidityObservable` inducing identical variable and clause profiles.
-/
theorem shared_manifold_induces_common_rapidity
    {M : Type*} [TopologicalSpace M]
    (B : SATSharedManifoldSmoothBridge M) :
    ∃ ρ : SharedRapidityObservable M,
      variableRapidityProfile B.shared ρ = variableRapidityProfile B.shared B.rapidity ∧
      clauseRapidityProfile B.shared ρ = clauseRapidityProfile B.shared B.rapidity := by
  refine ⟨B.rapidity, rfl, rfl⟩

end

end Hqiv.Geometry
