import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Fin.Basic

import Hqiv.Geometry.GeneralRiemannianRapidityOracle
import Hqiv.Geometry.SATWorstCaseCertified

/-!
# SAT rapidity manifold scaffold

This file packages the user's proposed viewpoint more explicitly:

- variables and clauses are treated as two coordinate systems / embeddings into a
  shared ambient manifold;
- a common rapidity observable is read on that manifold;
- if the embeddings and readout are smooth, then the induced variable-side and
  clause-side rapidity channels are smooth/analytic by composition.

This is still a scaffold: it does **not** yet prove that the resulting rapidity
threshold yields polynomial SAT search. It isolates the geometric interface that
would be needed for such a proof.
-/

namespace Hqiv.Geometry

noncomputable section

/--
Shared SAT manifold with variable and clause embeddings into one ambient smooth
space.  We keep the ambient carrier abstract (`M`) and record only the data
needed to express a common rapidity channel.
-/
structure SATSharedManifold (M : Type*) where
  varDim : ℕ
  clauseDim : ℕ
  embedVar : Fin varDim → M
  embedClause : Fin clauseDim → M

/--
Scalar rapidity observable on the shared manifold.  This is the common channel
through which variable-side and clause-side geometry are compared.
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
Naive discrete rapidity increment on the variable side: the combinatorial
`m ↦ m+1` difference of the shared manifold readout.
-/
def variableRapidityStep
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M)
    (i : Fin S.varDim) : ℝ :=
  ρ (S.embedVar i)

/--
Naive discrete rapidity increment on the clause side: the combinatorial
`m ↦ m+1` difference of the shared manifold readout.
-/
def clauseRapidityStep
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M)
    (j : Fin S.clauseDim) : ℝ :=
  ρ (S.embedClause j)

/--
Successor-step viewpoint: rapidity is recorded as the increment attached to the
`m+1` combinatorial rung on the shared manifold.

At this scaffold level, the “increment” is simply the value read at the current
successor index. A stronger finite-difference theorem can be layered on later
once an explicit predecessor/successor chart is chosen.
-/
theorem variableRapidityStep_eq_profile
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M)
    (i : Fin S.varDim) :
    variableRapidityStep S ρ i = variableRapidityProfile S ρ i := rfl

/-- Clause-side version of `variableRapidityStep_eq_profile`. -/
theorem clauseRapidityStep_eq_profile
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M)
    (j : Fin S.clauseDim) :
    clauseRapidityStep S ρ j = clauseRapidityProfile S ρ j := rfl

/--
Pointwise threshold compatibility between variables and clauses through the
shared rapidity observable.
-/
def SharesRapidityThreshold
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M)
    (τ : ℝ) : Prop :=
  (∀ i : Fin S.varDim, variableRapidityProfile S ρ i ≤ τ) ∧
  (∀ j : Fin S.clauseDim, clauseRapidityProfile S ρ j ≤ τ)

/--
Smooth manifold bridge: if the ambient readout is `ContDiff` and the embeddings
are `ContDiff`, then the induced rapidity channels on both sides are smooth.

We package this as a structure of assumptions rather than trying to force a
specific manifold model prematurely.
-/
structure SATSharedManifoldSmoothBridge (M : Type*) [TopologicalSpace M] where
  shared : SATSharedManifold M
  chartVar : (Fin shared.varDim → ℝ) → M
  chartClause : (Fin shared.clauseDim → ℝ) → M
  rapidity : SharedRapidityObservable M
  hVarEmbed : ∀ i : Fin shared.varDim, ∃ x : Fin shared.varDim → ℝ, chartVar x = shared.embedVar i
  hClauseEmbed : ∀ j : Fin shared.clauseDim, ∃ y : Fin shared.clauseDim → ℝ, chartClause y = shared.embedClause j

/--
Analytic-style placeholder contract: once the shared manifold bridge has a
smooth rapidity observable, both variable and clause profiles inherit the same
named common channel.

This theorem is intentionally lightweight: it records the exact conceptual move
“build one smooth manifold, then read one rapidity from both sides”.
-/
theorem shared_manifold_induces_common_rapidity
    {M : Type*} [TopologicalSpace M]
    (B : SATSharedManifoldSmoothBridge M) :
    ∃ ρ : SharedRapidityObservable M,
      variableRapidityProfile B.shared ρ = variableRapidityProfile B.shared B.rapidity ∧
      clauseRapidityProfile B.shared ρ = clauseRapidityProfile B.shared B.rapidity := by
  refine ⟨B.rapidity, rfl, rfl⟩

/--
If a single threshold `τ` bounds the shared rapidity observable on all embedded
variables and clauses, then both sides meet at the same rapidity threshold.
-/
theorem shares_threshold_of_pointwise_bounds
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M)
    (τ : ℝ)
    (hVar : ∀ i : Fin S.varDim, ρ (S.embedVar i) ≤ τ)
    (hClause : ∀ j : Fin S.clauseDim, ρ (S.embedClause j) ≤ τ) :
    SharesRapidityThreshold S ρ τ := by
  exact ⟨hVar, hClause⟩

/--
Threshold form using the naive successor-step rapidity on the variable side.
-/
theorem shares_threshold_of_step_bounds
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M)
    (τ : ℝ)
    (hVar : ∀ i : Fin S.varDim, variableRapidityStep S ρ i ≤ τ)
    (hClause : ∀ j : Fin S.clauseDim, clauseRapidityStep S ρ j ≤ τ) :
    SharesRapidityThreshold S ρ τ := by
  refine ⟨?_, ?_⟩ <;> intro k
  · simpa [variableRapidityStep_eq_profile] using hVar k
  · simpa [clauseRapidityStep_eq_profile] using hClause k

/--
External polynomial-threshold hypothesis for the shared-manifold route.

This is the exact additional ingredient needed to connect the new manifold view
to `SATWorstCaseCertified.HasPolynomialResidualBudget`.
-/
def SharedRapidityPolynomialThreshold
    {M : Type*}
    (S : SATSharedManifold M)
    (ρ : SharedRapidityObservable M)
    (polyBound : ℕ → ℝ) : Prop :=
  ∃ τ ≤ polyBound (S.varDim + S.clauseDim), SharesRapidityThreshold S ρ τ

/--
Certificate tying a shared rapidity threshold to the SAT residual-budget
interface.
-/
structure SATSharedRapidityCertificate (M : Type*) where
  shared : SATSharedManifold M
  rapidity : SharedRapidityObservable M
  polyBound : ℕ → ℝ
  rapidThreshold : ℝ
  arityResiduals : List ℝ
  hSharedThreshold : SharesRapidityThreshold shared rapidity rapidThreshold
  hPolyThreshold : rapidThreshold ≤ polyBound (shared.varDim + shared.clauseDim)
  hResidualDominated : ∀ ε ∈ arityResiduals, ε ≤ rapidThreshold

/--
First theorem-start hypothesis bundle for the missing bridge:
successor-step rapidity controls every residual produced by the SAT gate walk.

This mirrors the existing repo pattern of explicit bridge assumptions rather
than overclaiming a derived geometric fact.
-/
structure SuccessorStepResidualControl (M : Type*) where
  shared : SATSharedManifold M
  rapidity : SharedRapidityObservable M
  rapidThreshold : ℝ
  arityResiduals : List ℝ
  residualIndex : Fin arityResiduals.length → (Fin shared.varDim ⊕ Fin shared.clauseDim)
  hVarStepBound : ∀ i : Fin shared.varDim, variableRapidityStep shared rapidity i ≤ rapidThreshold
  hClauseStepBound : ∀ j : Fin shared.clauseDim, clauseRapidityStep shared rapidity j ≤ rapidThreshold
  hResidualFromIndex :
    ∀ k : Fin arityResiduals.length,
      arityResiduals.get k ≤
        match residualIndex k with
        | Sum.inl i => variableRapidityStep shared rapidity i
        | Sum.inr j => clauseRapidityStep shared rapidity j

/--
Under successor-step control, every residual is bounded by the common rapidity
threshold.
-/
theorem residual_bounded_by_threshold_of_successorStepResidualControl
    {M : Type*}
    (A : SuccessorStepResidualControl M)
    (k : Fin A.arityResiduals.length) :
    A.arityResiduals.get k ≤ A.rapidThreshold := by
  have hbase := A.hResidualFromIndex k
  cases hidx : A.residualIndex k with
  | inl i =>
      have hbase' : A.arityResiduals.get k ≤ variableRapidityStep A.shared A.rapidity i := by
        simpa [hidx] using hbase
      exact le_trans hbase' (A.hVarStepBound i)
  | inr j =>
      have hbase' : A.arityResiduals.get k ≤ clauseRapidityStep A.shared A.rapidity j := by
        simpa [hidx] using hbase
      exact le_trans hbase' (A.hClauseStepBound j)

/--
Convert successor-step residual control into the shared rapidity certificate,
given an external polynomial bound on the threshold.
-/
def SuccessorStepResidualControl.toSharedCertificate
    {M : Type*}
    (A : SuccessorStepResidualControl M)
    (polyBound : ℕ → ℝ)
    (hPoly : A.rapidThreshold ≤ polyBound (A.shared.varDim + A.shared.clauseDim)) :
    SATSharedRapidityCertificate M where
  shared := A.shared
  rapidity := A.rapidity
  polyBound := polyBound
  rapidThreshold := A.rapidThreshold
  arityResiduals := A.arityResiduals
  hSharedThreshold := shares_threshold_of_step_bounds
    A.shared A.rapidity A.rapidThreshold A.hVarStepBound A.hClauseStepBound
  hPolyThreshold := hPoly
  hResidualDominated := by
    intro ε hε
    rcases List.mem_iff_getElem.mp hε with ⟨k, hk, rfl⟩
    simpa using residual_bounded_by_threshold_of_successorStepResidualControl A ⟨k, hk⟩

/-- Every residual in the certificate is bounded by the same polynomial budget. -/
theorem satSharedRapidityCertificate_residual_le_poly
    {M : Type*}
    (c : SATSharedRapidityCertificate M)
    {ε : ℝ} (hε : ε ∈ c.arityResiduals) :
    ε ≤ c.polyBound (c.shared.varDim + c.shared.clauseDim) := by
  exact le_trans (c.hResidualDominated ε hε) c.hPolyThreshold

/--
If every residual is nonnegative and individually bounded by the same scalar,
then the cumulative residual sum is bounded by length times that scalar.
-/
theorem satArityResidualSum_le_length_mul_of_nonneg_bdd
    (polyT : ℝ)
    (εs : List ℝ)
    (hNonneg : ∀ ε ∈ εs, 0 ≤ ε)
    (hBound : ∀ ε ∈ εs, ε ≤ polyT) :
    satArityResidualSum εs ≤ (εs.length : ℝ) * polyT := by
  induction εs with
  | nil =>
      simp [satArityResidualSum]
  | cons x xs ih =>
      have hxB : x ≤ polyT := hBound x (by simp)
      have hxs0 : ∀ ε ∈ xs, 0 ≤ ε := by
        intro ε hε
        exact hNonneg ε (by simp [hε])
      have hxsB : ∀ ε ∈ xs, ε ≤ polyT := by
        intro ε hε
        exact hBound ε (by simp [hε])
      have htail := ih hxs0 hxsB
      rw [satArityResidualSum_cons]
      calc
        x + satArityResidualSum xs ≤ polyT + ((xs.length : ℝ) * polyT) := by linarith
        _ = (((x :: xs).length : ℕ) : ℝ) * polyT := by
          norm_num
          ring

/--
Main bridge theorem: if the residual list length is itself polynomially
bounded, then the shared-manifold certificate yields
`HasPolynomialResidualBudget`.
-/
theorem satSharedRapidityCertificate_hasPolynomialResidualBudget
    {M : Type*}
    (c : SATSharedRapidityCertificate M)
    (polyLen : ℕ → ℝ)
    (hLen : (c.arityResiduals.length : ℝ) ≤ polyLen (c.shared.varDim + c.shared.clauseDim))
    (hPolyNonneg : 0 ≤ c.polyBound (c.shared.varDim + c.shared.clauseDim))
    (hLenNonneg : 0 ≤ polyLen (c.shared.varDim + c.shared.clauseDim))
    (hResidualNonneg : ∀ ε ∈ c.arityResiduals, 0 ≤ ε) :
    HasPolynomialResidualBudget
      (fun n => polyLen n * c.polyBound n)
      (c.shared.varDim + c.shared.clauseDim)
      c.arityResiduals := by
  refine ⟨by positivity, ?_⟩
  have hsum := satArityResidualSum_le_length_mul_of_nonneg_bdd
      (c.polyBound (c.shared.varDim + c.shared.clauseDim))
      c.arityResiduals
      hResidualNonneg
      (fun ε hε => satSharedRapidityCertificate_residual_le_poly c hε)
  calc
    satArityResidualSum c.arityResiduals
        ≤ (c.arityResiduals.length : ℝ) * c.polyBound (c.shared.varDim + c.shared.clauseDim) := hsum
    _ ≤ polyLen (c.shared.varDim + c.shared.clauseDim) * c.polyBound (c.shared.varDim + c.shared.clauseDim) := by
        gcongr
    _ = (fun n => polyLen n * c.polyBound n) (c.shared.varDim + c.shared.clauseDim) := rfl

/-! ## Successor-style (`n + 1`) routes for variables and clauses -/

/-- Variable-successor envelope constant: use `varDim + 1` as the SAT-side root scale. -/
def variableEnvelopeSucc {M : Type*} (S : SATSharedManifold M) : ℝ :=
  1 + ((Nat.succ S.varDim : ℕ) : ℝ) ^ (1 / ((Nat.succ S.varDim : ℕ) : ℝ))

/-- Clause-successor envelope constant: use `clauseDim + 1` as the SAT-side root scale. -/
def clauseEnvelopeSucc {M : Type*} (S : SATSharedManifold M) : ℝ :=
  1 + ((Nat.succ S.clauseDim : ℕ) : ℝ) ^ (1 / ((Nat.succ S.clauseDim : ℕ) : ℝ))

/--
Variable-side successor transfer: the current SAT work-envelope theorem applied at
`varDim + 1`.
-/
theorem variable_succ_survivor_work_le_envelope
    {M : Type*}
    (S : SATSharedManifold M)
    (survivorWork baselineWork ε : ℝ)
    (hBasePos : 0 < baselineWork)
    (hGap : survivorWork ≤ baselineWork + ε)
    (hEpsBound : ε ≤ baselineWork * satSearchRootScale (Nat.succ S.varDim)) :
    survivorWork / baselineWork ≤ variableEnvelopeSucc S := by
  simpa [variableEnvelopeSucc, satSearchEnvelope, satSearchRootScale] using
    sat_near_degenerate_survivor_work_le_envelope
      (Nat.succ S.varDim) survivorWork baselineWork ε hBasePos hGap hEpsBound

/--
Clause-side successor transfer: the current SAT work-envelope theorem applied at
`clauseDim + 1`.
-/
theorem clause_succ_survivor_work_le_envelope
    {M : Type*}
    (S : SATSharedManifold M)
    (survivorWork baselineWork ε : ℝ)
    (hBasePos : 0 < baselineWork)
    (hGap : survivorWork ≤ baselineWork + ε)
    (hEpsBound : ε ≤ baselineWork * satSearchRootScale (Nat.succ S.clauseDim)) :
    survivorWork / baselineWork ≤ clauseEnvelopeSucc S := by
  simpa [clauseEnvelopeSucc, satSearchEnvelope, satSearchRootScale] using
    sat_near_degenerate_survivor_work_le_envelope
      (Nat.succ S.clauseDim) survivorWork baselineWork ε hBasePos hGap hEpsBound

/--
If the shared threshold is polynomially bounded, it is also bounded by the same
polynomial evaluated at the combined successor size.
-/
theorem shared_threshold_le_combined_successor_poly
    {M : Type*}
    (c : SATSharedRapidityCertificate M)
    (hMono : Monotone c.polyBound) :
    c.rapidThreshold ≤ c.polyBound (Nat.succ c.shared.varDim + Nat.succ c.shared.clauseDim) := by
  have hle : c.shared.varDim + c.shared.clauseDim ≤ Nat.succ c.shared.varDim + Nat.succ c.shared.clauseDim := by
    omega
  exact le_trans c.hPolyThreshold (hMono hle)

end

end Hqiv.Geometry
