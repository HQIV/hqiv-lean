import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Hqiv.Geometry.ATSPWorstCaseCertified

/-!
# SAT oracle contract mirroring `ATSPWorstCaseCertified`

**ATSP story (informal):** pruning removes only suboptimal structure; near-degenerate additive gaps
stay inside the `1 + n^(1/n)` envelope.

**SAT analogue (this file):** a *sound* prune removes only assignments that cannot extend to a
satisfying assignment (equivalently: no satisfying assignment lies in the removed set). If the
survivor set is exactly `Finset.univ \\ removed` and we *exhaustively* evaluate every survivor and
find no model, then the formula has **no** models (`models = ∅`).

This does **not** prove that any particular geometric/heuristic prune implemented in Python is
sound — it is the **interface** against which such prunes must be discharged (compare
`OracleBridgeAssumptions` in `ATSPWorstCaseCertified.lean`).

Worst-case **work** bounds can be stated in the **same** root scale `n^(1/n)` as the ATSP envelope
via `satSearchRootScale` and `satSearchEnvelope`, matching the HQIV “near-degenerate” certificate
pattern.

**Arity gates:** `SoundRemovalChain` formalizes a finite list of feasible removals from an initial
survivor set; each step is `PruneSound`.  Composing gates preserves all models; see
`pruneSound_univ_of_soundRemovalChain` and `unsat_of_soundRemovalChain_univ_and_survivor_exhaust`.
Cumulative residual budgets `εᵢ` sum into `satArityResidualSum` and imply the same envelope via
`sat_cumulative_arity_residuals_le_envelope` and `SATArityGateChainCertificate`.
-/

noncomputable section

namespace Hqiv.Geometry

universe u

variable {α : Type u} [DecidableEq α] [Fintype α]

/-- Finite set of assignments that satisfy the formula (abstract `Finset` of models). -/
abbrev AssignmentSet (α : Type u) :=
  Finset α

/--
**Sound pruning:** removed assignments are disjoint from the model set — no satisfying assignment is
discarded. (Same logical content as “we do not prune valid tours” on the ATSP side, specialized to
a finite model set.)
-/
def PruneSound (models removed : Finset α) : Prop :=
  Disjoint models removed

theorem models_subset_survivor_of_pruneSound (models removed : Finset α)
    (h : PruneSound models removed) :
    models ⊆ Finset.univ \ removed := by
  classical
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  intro hr
  exact Finset.disjoint_left.mp h hx hr

/--
**Exhaustive search on the survivor set:** we evaluated exactly the assignments still in play after
pruning (the complement of `removed` in the finite universe).
-/
def SurvivorExhaustive (removed evaluated : Finset α) : Prop :=
  evaluated = Finset.univ \ removed

/--
If pruning is sound and we exhaust the survivor set but find no model anywhere on that set, then
there is no model at all — **UNSAT in the abstract finite sense** (`models` empty).
-/
theorem unsat_of_sound_prune_and_survivor_exhaust
    (models removed evaluated : Finset α)
    (hSound : PruneSound models removed)
    (hEx : SurvivorExhaustive removed evaluated)
    (hNone : ∀ x ∈ evaluated, x ∉ models) :
    models = ∅ := by
  classical
  refine Finset.ext ?_
  intro x
  apply Iff.intro
  · intro hm
    have hev : x ∈ evaluated := by
      rw [hEx]
      exact models_subset_survivor_of_pruneSound models removed hSound hm
    exact absurd hm (hNone x hev)
  · intro h
    exact False.elim (absurd h (Finset.notMem_empty x))

/-! ## Arity-by-arity gate prunes (finite removal chains from an initial survivor set)

Each **gate** removes a finset `r` from the current survivors `s`, yielding `s \\ r`.
**Soundness** at a step: `r ⊆ s` (only prune inside live region) and `PruneSound models r`
(no model is removed).  Composing gates in list order matches “fold from the initial survivor
set until no further arity removal” *when* those proof obligations hold at every step.

This does **not** certify any particular Python `flip_prune` — it is the interface a gate
implementation must discharge, analogous to `PruneSound` for a one-shot prune.
-/

/-- Survivor set after applying removals left-to-right from `start` (list head removed first). -/
def survivorsAfterRemovalsFrom (start : Finset α) (rems : List (Finset α)) : Finset α :=
  rems.foldl (fun s r => s \ r) start

@[simp]
theorem survivorsAfterRemovalsFrom_nil (start : Finset α) :
    survivorsAfterRemovalsFrom start [] = start :=
  rfl

theorem survivorsAfterRemovalsFrom_cons (start : Finset α) (r : Finset α) (rs : List (Finset α)) :
    survivorsAfterRemovalsFrom start (r :: rs) = survivorsAfterRemovalsFrom (start \ r) rs := by
  simp [survivorsAfterRemovalsFrom, List.foldl]

/--
Inductive **arity-gate chain**: from `start`, each removal is feasible and disjoint from `models`,
and the tail is sound from the updated survivors `start \\ r`.
-/
inductive SoundRemovalChain (models : Finset α) : Finset α → List (Finset α) → Prop
| nil (start : Finset α) : SoundRemovalChain models start []
| cons (start r : Finset α) (rs : List (Finset α))
    (hr : r ⊆ start) (hd : PruneSound models r)
    (hrest : SoundRemovalChain models (start \ r) rs) :
    SoundRemovalChain models start (r :: rs)

theorem models_subset_sdiff_of_pruneSound
    (models r start : Finset α) (hsub : models ⊆ start) (hd : PruneSound models r) :
    models ⊆ start \ r := by
  classical
  intro x hx
  simp only [Finset.mem_sdiff]
  refine ⟨hsub hx, ?_⟩
  intro hr
  exact Finset.disjoint_left.mp hd hx hr

theorem models_subset_survivorsAfter_sound_chain
    (models start : Finset α) (rems : List (Finset α))
    (hStart : models ⊆ start)
    (h : SoundRemovalChain models start rems) :
    models ⊆ survivorsAfterRemovalsFrom start rems := by
  revert hStart
  induction h with
  | nil start' =>
    intro hStart
    simpa [survivorsAfterRemovalsFrom]
  | cons start' r rs hr hd hrest ih =>
    intro hStart
    have hmodels' : models ⊆ start' \ r :=
      models_subset_sdiff_of_pruneSound models r start' hStart hd
    simpa [survivorsAfterRemovalsFrom_cons] using ih hmodels'

theorem pruneSound_iff_models_subset_survivors (models surv : Finset α) :
    PruneSound models (Finset.univ \ surv) ↔ models ⊆ surv := by
  classical
  constructor
  · intro h x hx
    by_contra hns
    have hxu : x ∈ Finset.univ \ surv := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hns
    exact Finset.disjoint_left.mp h hx hxu
  · intro hsub
    refine Finset.disjoint_left.mpr ?_
    intro x hm hx
    have xs : x ∈ surv := hsub hm
    exact (Finset.mem_sdiff.mp hx).2 xs

/--
One-shot aggregate prune from a sound removal chain starting at `univ`: removed mass is
`Finset.univ \\ survivorsAfter`, and **all** models survive in the final survivor set.
-/
theorem pruneSound_univ_of_soundRemovalChain
    (models : Finset α) (rems : List (Finset α))
    (h : SoundRemovalChain models Finset.univ rems) :
    PruneSound models (Finset.univ \ survivorsAfterRemovalsFrom Finset.univ rems) := by
  have hmodels :
      models ⊆ survivorsAfterRemovalsFrom Finset.univ rems :=
    models_subset_survivorsAfter_sound_chain models Finset.univ rems (Finset.subset_univ models) h
  exact (pruneSound_iff_models_subset_survivors models _).mpr hmodels

/--
**Composed arity gates + exhaustive final survivors ⇒ UNSAT** (same logical content as
`unsat_of_sound_prune_and_survivor_exhaust`, packaged for a removal chain from `univ`).
-/
theorem unsat_of_soundRemovalChain_univ_and_survivor_exhaust
    (models : Finset α) (rems : List (Finset α)) (evaluated : Finset α)
    (hChain : SoundRemovalChain models Finset.univ rems)
    (hEx : SurvivorExhaustive (Finset.univ \ survivorsAfterRemovalsFrom Finset.univ rems) evaluated)
    (hNone : ∀ x ∈ evaluated, x ∉ models) :
    models = ∅ := by
  have hSound := pruneSound_univ_of_soundRemovalChain models rems hChain
  exact unsat_of_sound_prune_and_survivor_exhaust
    models (Finset.univ \ survivorsAfterRemovalsFrom Finset.univ rems) evaluated hSound hEx hNone

/-! ## Same HQIV root envelope as ATSP (reinterpreted for search-work certificates) -/

/-- Abstract `n^(1/n)` scale (identical to the root term in `ATSPWorstCaseCertified.envelopeBound`). -/
def satSearchRootScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / (n : ℝ))

/-- Same `1 + n^(1/n)` envelope as `EnvelopeCertificate` / ATSP worst-case certificates. -/
def satSearchEnvelope (n : ℕ) : ℝ :=
  1 + satSearchRootScale n

/--
Abstract hook: external certificate that realized search work stays below the root scale (same
pattern as `random_poly_search_hits_nat_root_envelope_of_certificate`).
-/
theorem sat_search_work_hits_root_scale_of_certificate
    (n : ℕ) (work : ℝ)
    (hCert : work ≤ satSearchRootScale n) :
    work ≤ satSearchRootScale n :=
  hCert

/--
Multiplicative-style wrapper: if `work ≤ optimal * n^(1/n)` with `optimal > 0`, then
`work / optimal ≤ n^(1/n)` (parallel to `additive_gap_implies_ratio_bound` on the ATSP side).
-/
theorem sat_search_work_ratio_bound
    (n : ℕ) (work optimal : ℝ)
    (hOptPos : 0 < optimal)
    (h : work ≤ optimal * satSearchRootScale n) :
    work / optimal ≤ satSearchRootScale n := by
  have hinv : 0 ≤ optimal⁻¹ := by positivity
  calc
    work / optimal = work * optimal⁻¹ := by simp [div_eq_mul_inv]
    _ ≤ (optimal * satSearchRootScale n) * optimal⁻¹ :=
      mul_le_mul_of_nonneg_right h hinv
    _ = satSearchRootScale n := by field_simp [hOptPos.ne']

/-! ## SAT work/prune certificates posed in the ATSP style -/

/-- Concrete amount of work removed by a prune: cardinality of the pruned set. -/
def satRemovedWork (removed : Finset α) : ℝ :=
  (removed.card : ℝ)

/-- Concrete amount of survivor work after pruning. -/
def satSurvivorWork (removed : Finset α) : ℝ :=
  ((Finset.univ \ removed).card : ℝ)

/-- Total brute-force search work over the finite assignment universe. -/
def satTotalWork : ℝ :=
  (Fintype.card α : ℝ)

/-- Fraction of the search space pruned away. -/
def satPruneRatio (removed : Finset α) : ℝ :=
  satRemovedWork removed / satTotalWork (α := α)

/-- Fraction of the search space left alive after pruning. -/
def satSurvivorRatio (removed : Finset α) : ℝ :=
  satSurvivorWork (α := α) removed / satTotalWork (α := α)

/-- Improvement in search work relative to exhaustive search. -/
def satWorkGain (removed : Finset α) : ℝ :=
  satTotalWork (α := α) - satSurvivorWork (α := α) removed

theorem sat_removed_plus_survivor_eq_total (removed : Finset α) :
    satRemovedWork removed + satSurvivorWork (α := α) removed = satTotalWork (α := α) := by
  classical
  unfold satRemovedWork satSurvivorWork satTotalWork
  have hsub : removed ⊆ Finset.univ := by
    intro x hx
    simp
  have hcard : (Finset.univ \ removed).card = Fintype.card α - removed.card := by
    simpa using Finset.card_sdiff_of_subset hsub
  have hle : removed.card ≤ Fintype.card α := Finset.card_le_univ removed
  have hcard' : removed.card + (Finset.univ \ removed).card = Fintype.card α := by
    rw [hcard]
    exact Nat.add_sub_of_le hle
  exact_mod_cast hcard'

theorem sat_work_gain_eq_removed_work (removed : Finset α) :
    satWorkGain (α := α) removed = satRemovedWork removed := by
  unfold satWorkGain
  linarith [sat_removed_plus_survivor_eq_total (α := α) removed]

theorem sat_survivor_ratio_eq_one_sub_prune_ratio
    (removed : Finset α)
    (hTotPos : 0 < satTotalWork (α := α)) :
    satSurvivorRatio (α := α) removed = 1 - satPruneRatio (α := α) removed := by
  unfold satSurvivorRatio satPruneRatio satTotalWork satRemovedWork satSurvivorWork
  have hTotNe : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt (by simpa [satTotalWork] using hTotPos)
  have hcard :
      ((Finset.univ \ removed).card : ℝ) = (Fintype.card α : ℝ) - (removed.card : ℝ) := by
    have hnat :
        (Finset.univ \ removed).card = Fintype.card α - removed.card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ removed)
    rw [← Nat.cast_sub (Finset.card_le_univ removed)]
    exact_mod_cast hnat
  field_simp [hTotNe]
  linarith [hcard]

/--
ATSP-style additive-gap transfer, but for SAT survivor work:
if survivor work is within `ε` of a baseline work budget, then the normalized
survivor work is within `1 + ε / baseline`.
-/
theorem sat_additive_survivor_gap_implies_ratio_bound
    (survivorWork baselineWork ε : ℝ)
    (hBasePos : 0 < baselineWork)
    (hGap : survivorWork ≤ baselineWork + ε) :
    survivorWork / baselineWork ≤ 1 + ε / baselineWork := by
  exact additive_gap_implies_ratio_bound survivorWork baselineWork ε hBasePos hGap

/--
SAT near-degenerate work envelope:
if the survivor work is at most `baselineWork + ε` and `ε` is controlled by the
same root scale `baselineWork * n^(1/n)`, then the normalized survivor work is
inside the same `1 + n^(1/n)` envelope used on the ATSP side.

This is the more natural SAT framing: certify remaining search work rather than
an approximation ratio of objective values.
-/
theorem sat_near_degenerate_survivor_work_le_envelope
    (n : ℕ)
    (survivorWork baselineWork ε : ℝ)
    (hBasePos : 0 < baselineWork)
    (hGap : survivorWork ≤ baselineWork + ε)
    (hEpsBound : ε ≤ baselineWork * satSearchRootScale n) :
    survivorWork / baselineWork ≤ satSearchEnvelope n := by
  simpa [satSearchEnvelope, satSearchRootScale] using
    near_degenerate_ratio_le_nat_root_envelope
      n survivorWork baselineWork ε hBasePos hGap hEpsBound

/-- Strict version of the survivor-work envelope. -/
theorem sat_near_degenerate_survivor_work_lt_envelope
    (n : ℕ)
    (survivorWork baselineWork ε : ℝ)
    (hBasePos : 0 < baselineWork)
    (hGap : survivorWork ≤ baselineWork + ε)
    (hEpsBound : ε < baselineWork * satSearchRootScale n) :
    survivorWork / baselineWork < satSearchEnvelope n := by
  let r := satSearchRootScale n
  have hBase : survivorWork / baselineWork ≤ 1 + ε / baselineWork :=
    sat_additive_survivor_gap_implies_ratio_bound survivorWork baselineWork ε hBasePos hGap
  have hDiv : ε / baselineWork < r := by
    have hMul : ε < r * baselineWork := by simpa [r, mul_comm] using hEpsBound
    have hinv_pos : 0 < baselineWork⁻¹ := by positivity
    have hMulInv : ε * baselineWork⁻¹ < (r * baselineWork) * baselineWork⁻¹ :=
      mul_lt_mul_of_pos_right hMul hinv_pos
    calc
      ε / baselineWork = ε * baselineWork⁻¹ := by simp [div_eq_mul_inv]
      _ < (r * baselineWork) * baselineWork⁻¹ := hMulInv
      _ = r := by field_simp [hBasePos.ne']
  have hlt : 1 + ε / baselineWork < 1 + r := by linarith [hDiv]
  simpa [satSearchEnvelope, r] using lt_of_le_of_lt hBase hlt

/-! ### Cumulative per-arity residual budget (folds into one `ε` for the envelope) -/

/-- Sum of per-gate residual budgets `εᵢ` (additive slack attributed to each arity step). -/
noncomputable def satArityResidualSum (εs : List ℝ) : ℝ :=
  εs.foldl (· + ·) 0

/--
Polynomial-budget abstraction for a rapidity/arity schedule:
an external argument supplies a polynomial `polyBound` such that every gate
residual sum stays below that budget.

This does not itself prove the budget is polynomial; it packages the exact extra
hypothesis needed to turn the current envelope story into a genuine P-time style
search-work statement.
-/
def HasPolynomialResidualBudget (polyBound : ℕ → ℝ) (n : ℕ) (εs : List ℝ) : Prop :=
  0 ≤ polyBound n ∧ satArityResidualSum εs ≤ polyBound n

/--
If both the baseline work and the cumulative residual budget are bounded by the
same external polynomial budget, then the total survivor-work budget is bounded
by twice that polynomial budget.

This theorem isolates the missing bridge from the current root-envelope contract
to an actual polynomial worst-case work statement.
-/
theorem sat_polynomial_budget_of_baseline_and_residual
    (polyBound : ℕ → ℝ)
    (n : ℕ)
    (survivorWork baselineWork : ℝ)
    (εs : List ℝ)
    (hBase : baselineWork ≤ polyBound n)
    (hResidual : HasPolynomialResidualBudget polyBound n εs)
    (hGap : survivorWork ≤ baselineWork + satArityResidualSum εs) :
    survivorWork ≤ 2 * polyBound n := by
  rcases hResidual with ⟨hPolyNonneg, hResidualBound⟩
  have hLift : baselineWork + satArityResidualSum εs ≤ polyBound n + polyBound n := by
    linarith
  have h2 : polyBound n + polyBound n = 2 * polyBound n := by ring
  calc
    survivorWork ≤ baselineWork + satArityResidualSum εs := hGap
    _ ≤ polyBound n + polyBound n := hLift
    _ = 2 * polyBound n := h2

private theorem list_foldl_add_left (x : ℝ) (xs : List ℝ) :
    xs.foldl (· + ·) x = x + xs.foldl (· + ·) 0 := by
  induction xs generalizing x with
  | nil =>
    simp [List.foldl]
  | cons y ys ih =>
    simp [List.foldl]
    rw [ih (x + y), ih y]
    ring

@[simp]
theorem satArityResidualSum_nil : satArityResidualSum ([] : List ℝ) = 0 :=
  rfl

theorem satArityResidualSum_cons (x : ℝ) (xs : List ℝ) :
    satArityResidualSum (x :: xs) = x + satArityResidualSum xs := by
  simp [satArityResidualSum, List.foldl]
  exact list_foldl_add_left x xs

/--
If total survivor work is bounded by `baselineWork + ∑ εᵢ` and the **sum** of gate residuals
is within `baselineWork * n^(1/n)`, then `survivorWork / baselineWork ≤ 1 + n^(1/n)` — same
envelope as a single near-degenerate step (`sat_near_degenerate_survivor_work_le_envelope`).
-/
theorem sat_cumulative_arity_residuals_le_envelope
    (n : ℕ) (survivorWork baselineWork : ℝ) (εs : List ℝ)
    (hBasePos : 0 < baselineWork)
    (hGap : survivorWork ≤ baselineWork + satArityResidualSum εs)
    (hEpsSum : satArityResidualSum εs ≤ baselineWork * satSearchRootScale n) :
    survivorWork / baselineWork ≤ satSearchEnvelope n :=
  sat_near_degenerate_survivor_work_le_envelope
    n survivorWork baselineWork (satArityResidualSum εs) hBasePos hGap hEpsSum

/--
Certificate record for the SAT reformulation that best matches the ATSP theorem
shape: sound prune + exhaustive survivor semantics + bounded survivor work.
-/
structure SATPruneCertificate where
  n : ℕ
  models : Finset α
  removed : Finset α
  evaluated : Finset α
  baselineWork : ℝ
  survivorWork : ℝ

namespace SATPruneCertificate

/-- Predicate exposing the assumptions needed for the SAT work-envelope transfer. -/
def IsValid (c : SATPruneCertificate (α := α)) : Prop :=
  PruneSound c.models c.removed ∧
  SurvivorExhaustive c.removed c.evaluated ∧
  0 < c.baselineWork ∧
  c.survivorWork = satSurvivorWork (α := α) c.removed ∧
  c.survivorWork ≤ c.baselineWork * satSearchEnvelope c.n

theorem isValid_implies_survivor_work_envelope
    (c : SATPruneCertificate (α := α))
    (h : c.IsValid) :
    c.survivorWork / c.baselineWork ≤ satSearchEnvelope c.n := by
  rcases h with ⟨_, _, hBasePos, _, hEnvelope⟩
  have hinv : 0 ≤ c.baselineWork⁻¹ := by positivity
  calc
    c.survivorWork / c.baselineWork = c.survivorWork * c.baselineWork⁻¹ := by
      simp [div_eq_mul_inv]
    _ ≤ (c.baselineWork * satSearchEnvelope c.n) * c.baselineWork⁻¹ :=
      mul_le_mul_of_nonneg_right hEnvelope hinv
    _ = satSearchEnvelope c.n := by
      field_simp [hBasePos.ne']

theorem isValid_and_no_survivor_model_implies_unsat
    (c : SATPruneCertificate (α := α))
    (h : c.IsValid)
    (hNone : ∀ x ∈ c.evaluated, x ∉ c.models) :
    c.models = ∅ := by
  rcases h with ⟨hSound, hEx, _, _, _⟩
  exact unsat_of_sound_prune_and_survivor_exhaust
    c.models c.removed c.evaluated hSound hEx hNone

end SATPruneCertificate

/--
Certificate combining a **sound arity removal chain** from `Finset.univ`, survivor exhaustion,
and a **cumulative** residual budget `∑ εᵢ` feeding the same `1 + n^(1/n)` envelope.
-/
structure SATArityGateChainCertificate where
  n : ℕ
  models : Finset α
  rems : List (Finset α)
  evaluated : Finset α
  baselineWork : ℝ
  survivorWork : ℝ
  arityResiduals : List ℝ

namespace SATArityGateChainCertificate

/-- Aggregate removed set after the full chain: `Finset.univ \\ finalSurvivors`. -/
def aggregateRemoved (c : SATArityGateChainCertificate (α := α)) : Finset α :=
  Finset.univ \ survivorsAfterRemovalsFrom Finset.univ c.rems

/-- Predicate matching the Lean proof obligations for arity gates + envelope + UNSAT discharge. -/
def IsValid (c : SATArityGateChainCertificate (α := α)) : Prop :=
  SoundRemovalChain c.models Finset.univ c.rems ∧
  SurvivorExhaustive c.aggregateRemoved c.evaluated ∧
  0 < c.baselineWork ∧
  c.survivorWork = satSurvivorWork (α := α) c.aggregateRemoved ∧
  c.survivorWork ≤ c.baselineWork + satArityResidualSum c.arityResiduals ∧
  satArityResidualSum c.arityResiduals ≤ c.baselineWork * satSearchRootScale c.n

theorem isValid_implies_aggregate_pruneSound
    (c : SATArityGateChainCertificate (α := α)) (h : c.IsValid) :
    PruneSound c.models c.aggregateRemoved := by
  rcases h with ⟨hChain, _, _, _, _, _⟩
  simpa [aggregateRemoved] using pruneSound_univ_of_soundRemovalChain c.models c.rems hChain

theorem isValid_implies_survivor_work_le_envelope
    (c : SATArityGateChainCertificate (α := α)) (h : c.IsValid) :
    c.survivorWork / c.baselineWork ≤ satSearchEnvelope c.n := by
  rcases h with ⟨_, _, hBasePos, _, hGap, hEps⟩
  exact sat_cumulative_arity_residuals_le_envelope
    c.n c.survivorWork c.baselineWork c.arityResiduals hBasePos hGap hEps

theorem isValid_and_no_model_implies_unsat
    (c : SATArityGateChainCertificate (α := α)) (h : c.IsValid)
    (hNone : ∀ x ∈ c.evaluated, x ∉ c.models) :
    c.models = ∅ := by
  rcases h with ⟨hChain, hEx, _, _, _, _⟩
  rw [aggregateRemoved] at hEx
  exact unsat_of_soundRemovalChain_univ_and_survivor_exhaust
    c.models c.rems c.evaluated hChain hEx hNone

end SATArityGateChainCertificate

end Hqiv.Geometry

end
