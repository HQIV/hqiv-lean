import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.ModularForms.Basic

import Hqiv.Geometry.GeneralRiemannianRapidityOracle
import Hqiv.Geometry.TensorTruncationBounds
import Hqiv.Archive.Logic.CNF

/-!
# Generalized Geometric Oracle (Modular + SAT bridges)

This module reuses the `Candidate`/CSV/bounded-family engine from
`GeneralRiemannianRapidityOracle` and provides honest, hypothesis-driven bridge
APIs for:

- modular-form / L-function style targets;
- CNF-SAT style targets.

Theorems here intentionally remain scaffold-level unless the required analytic
or combinatorial coverage hypotheses are provided explicitly.
-/

namespace Hqiv.Geometry

noncomputable section

open Hqiv

namespace Nat

/-- Semiprime predicate used by symmetric-tip bridge statements. -/
def isSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p * q = n

end Nat

/-- Arc validity witness: arc slot itself is a divisor candidate for `n`. -/
def is_valid_intercept (a : ArcParameter) (n : ℕ) : Prop :=
  a ∣ n

/--
Symmetric S³/S⁴ tip-intersection witness:
`phi2` is the reflection of `phi1` across the binary arity pole `π/4`.
-/
structure SymmetricTipIntersection where
  phi1 : ℝ
  phi2 : ℝ
  arcParam1 : ArcParameter
  arcParam2 : ArcParameter
  derivedDivisors : Array ℕ

/--
Symmetric-tip search scaffold:
- returns `none` outside the semiprime channel;
- otherwise constructs the reflected pair witness from a semiprime factorization.
-/
noncomputable def symmetric_tip_search (m : ℕ) : Option SymmetricTipIntersection := by
  classical
  by_cases h : Nat.isSemiprime m
  ·
    have hPair : ∃ pq : ℕ × ℕ, pq.1 * pq.2 = m := by
      rcases h with ⟨p, q, _hp, _hq, hpq⟩
      exact ⟨(p, q), hpq⟩
    let pq : ℕ × ℕ := Classical.choose hPair
    exact some
      { phi1 := 0
        phi2 := Real.pi / 2
        arcParam1 := pq.1
        arcParam2 := pq.2
        derivedDivisors := #[pq.1, pq.2] }
  · exact none

/--
Existence bridge for symmetric-tip intersections on semiprimes.
-/
theorem symmetric_tip_intersection_exists (n : ℕ) (h : Nat.isSemiprime n) :
    ∃ i : SymmetricTipIntersection,
      i.derivedDivisors.size = 2 ∧
      i.derivedDivisors[0]! * i.derivedDivisors[1]! = n ∧
      is_valid_intercept i.arcParam1 n ∧
      is_valid_intercept i.arcParam2 n := by
  rcases h with ⟨p, q, hp, hq, hpq⟩
  refine ⟨
    { phi1 := 0
      phi2 := Real.pi / 2
      arcParam1 := p
      arcParam2 := q
      derivedDivisors := #[p, q] },
    ?_⟩
  refine ⟨by simp, ?_⟩
  refine ⟨by simp [hpq], ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨q, by simpa [Nat.mul_comm] using hpq.symm⟩
  · exact ⟨p, by simpa [Nat.mul_comm] using hpq.symm⟩

/--
Integrate symmetric-tip search into the candidate stream:
for semiprimes, emit the reflected pair directly; otherwise use the baseline list.
-/
noncomputable def candidateListWithSymmetricTip (n : ℕ) : List Candidate := by
  classical
  by_cases h : Nat.isSemiprime n
  ·
    match symmetric_tip_search n with
    | some i =>
        exact
          [ { step := 0
              seedIdx := ⟨0, by decide⟩
              arcParam := i.arcParam1
              derivedDivisor := some i.derivedDivisors[0]! },
            { step := 0
              seedIdx := ⟨0, by decide⟩
              arcParam := i.arcParam2
              derivedDivisor := some i.derivedDivisors[1]! } ]
    | none => exact candidateList n (fun _ => none)
  · exact candidateList n (fun _ => none)

/-! ## TSP bridge (n-arity root principle scaffold) -/

/-- Weighted complete graph instance for TSP. -/
structure TSPInstance where
  cityCount : ℕ
  edgeCost : Fin cityCount → Fin cityCount → ℕ

/-- Geometric specialization of a candidate to a Hamiltonian tour proposal. -/
structure TSPCandidate extends Candidate where
  tour : List ℕ := []
  rootDistance : ℕ := 0
  tourCost : ℕ := 0

/--
Root-priority ordering channel used by n-arity arc search:
smaller `rootDistance` means closer to n-arity root.
-/
def isRootCloser (c₁ c₂ : TSPCandidate) : Prop :=
  c₁.rootDistance ≤ c₂.rootDistance

/--
Hypothesis-driven bridge:
if root-closeness aligns with nonincreasing tour cost on the produced candidate
family, then every root-minimal candidate is tour-cost minimal.
-/
theorem root_closest_candidate_minimizes_tourCost
    (cs : List TSPCandidate)
    (hMono :
      ∀ c₁ ∈ cs, ∀ c₂ ∈ cs,
        isRootCloser c₁ c₂ → c₁.tourCost ≤ c₂.tourCost)
    (cStar : TSPCandidate)
    (hMem : cStar ∈ cs)
    (hRootMin : ∀ c ∈ cs, isRootCloser cStar c) :
    ∀ c ∈ cs, cStar.tourCost ≤ c.tourCost := by
  intro c hc
  exact hMono cStar hMem c hc (hRootMin c hc)

/--
Constructive running minimum over `tourCost` on a nonempty candidate list.
-/
def minByTourCostFromHead : TSPCandidate → List TSPCandidate → TSPCandidate
  | c, [] => c
  | c, d :: ds =>
      if d.tourCost < c.tourCost then
        minByTourCostFromHead d ds
      else
        minByTourCostFromHead c ds

theorem minByTourCostFromHead_mem
    (c : TSPCandidate) (cs : List TSPCandidate) :
    minByTourCostFromHead c cs ∈ c :: cs := by
  induction cs generalizing c with
  | nil =>
      simp [minByTourCostFromHead]
  | cons d ds ih =>
      by_cases hlt : d.tourCost < c.tourCost
      · have hmem : minByTourCostFromHead d ds ∈ d :: ds := ih d
        simp [minByTourCostFromHead, hlt, hmem]
      · have hmem : minByTourCostFromHead c ds ∈ c :: ds := ih c
        have hmem' : minByTourCostFromHead c ds = c ∨ minByTourCostFromHead c ds ∈ ds := by
          simpa using hmem
        have hgoal : minByTourCostFromHead c ds = c ∨
            minByTourCostFromHead c ds = d ∨
            minByTourCostFromHead c ds ∈ ds := by
          cases hmem' with
          | inl hc =>
              exact Or.inl hc
          | inr hds =>
              exact Or.inr (Or.inr hds)
        simpa [minByTourCostFromHead, hlt] using hgoal

theorem minByTourCostFromHead_le_all
    (c : TSPCandidate) (cs : List TSPCandidate) :
    ∀ d ∈ c :: cs, (minByTourCostFromHead c cs).tourCost ≤ d.tourCost := by
  induction cs generalizing c with
  | nil =>
      intro d hd
      simp [minByTourCostFromHead] at hd ⊢
      simp [hd]
  | cons x xs ih =>
      by_cases hlt : x.tourCost < c.tourCost
      · intro d hd
        have hsub : ∀ y ∈ x :: xs, (minByTourCostFromHead x xs).tourCost ≤ y.tourCost := ih x
        have hxle : (minByTourCostFromHead x xs).tourCost ≤ x.tourCost := hsub x (by simp)
        have hcle : (minByTourCostFromHead x xs).tourCost ≤ c.tourCost := le_trans hxle (Nat.le_of_lt hlt)
        have hmem : d = c ∨ d ∈ x :: xs := by
          simpa using hd
        have hmain : (minByTourCostFromHead x xs).tourCost ≤ d.tourCost := by
          cases hmem with
          | inl hdc =>
              simpa [hdc] using hcle
          | inr hdin =>
              exact hsub d hdin
        simpa [minByTourCostFromHead, hlt] using hmain
      · intro d hd
        have hsub : ∀ y ∈ c :: xs, (minByTourCostFromHead c xs).tourCost ≤ y.tourCost := ih c
        have hcle : (minByTourCostFromHead c xs).tourCost ≤ c.tourCost := hsub c (by simp)
        have hxle : (minByTourCostFromHead c xs).tourCost ≤ x.tourCost := by
          have hxc : x.tourCost ≥ c.tourCost := Nat.le_of_not_lt hlt
          exact le_trans hcle hxc
        have hmem : d = c ∨ d = x ∨ d ∈ xs := by
          simpa using hd
        have hmain : (minByTourCostFromHead c xs).tourCost ≤ d.tourCost := by
          cases hmem with
          | inl hdc =>
              simpa [hdc] using hcle
          | inr hrest =>
              cases hrest with
              | inl hdx =>
                  simpa [hdx] using hxle
              | inr hdin =>
                  exact hsub d (by simp [hdin])
        simpa [minByTourCostFromHead, hlt] using hmain

/--
Existence of an optimal (minimum `tourCost`) candidate in any nonempty finite
candidate list.
-/
theorem tsp_optimal_candidate_exists
    (cs : List TSPCandidate) (hNonempty : cs ≠ []) :
    ∃ c ∈ cs, ∀ d ∈ cs, c.tourCost ≤ d.tourCost := by
  rcases List.exists_cons_of_ne_nil hNonempty with ⟨head, tail, hcs⟩
  refine ⟨minByTourCostFromHead head tail, ?_, ?_⟩
  · simpa [hcs] using minByTourCostFromHead_mem head tail
  · intro d hd
    have hd' : d ∈ head :: tail := by simpa [hcs] using hd
    have hle : (minByTourCostFromHead head tail).tourCost ≤ d.tourCost :=
      minByTourCostFromHead_le_all head tail d hd'
    simpa [hcs] using hle

/--
`TourOptimalIn cs c` means `c` is a cost-minimal witness inside the finite family `cs`.
-/
def TourOptimalIn (cs : List TSPCandidate) (c : TSPCandidate) : Prop :=
  c ∈ cs ∧ ∀ d ∈ cs, c.tourCost ≤ d.tourCost

/-- Generic prune operator used by recursive ATSP families. -/
def pruneBy (keep : TSPCandidate → Bool) (cs : List TSPCandidate) : List TSPCandidate :=
  cs.filter keep

/-- Pruned family is a subset of the source family. -/
theorem pruneBy_subset
    (keep : TSPCandidate → Bool) (cs : List TSPCandidate) :
    ∀ c ∈ pruneBy keep cs, c ∈ cs := by
  intro c hc
  simpa [pruneBy] using (List.mem_of_mem_filter hc)

/-- Pruning preserves any compatibility predicate carried by the source family. -/
theorem prune_keeps_compatibility
    (keep : TSPCandidate → Bool)
    (compat : TSPCandidate → Prop)
    (cs : List TSPCandidate)
    (hCompat : ∀ c ∈ cs, compat c) :
    ∀ c ∈ pruneBy keep cs, compat c := by
  intro c hc
  exact hCompat c (pruneBy_subset keep cs c hc)

/--
Prune-safety invariant (OSHoracle-style transfer):
if a candidate is globally optimal in `cs` and survives pruning into `pruned ⊆ cs`,
then it remains optimal in `pruned`.
-/
theorem prune_preserves_optimal_if_witness_kept
    (cs pruned : List TSPCandidate)
    (c : TSPCandidate)
    (hSub : ∀ d : TSPCandidate, d ∈ pruned → d ∈ cs)
    (hOpt : TourOptimalIn cs c)
    (hKeep : c ∈ pruned) :
    TourOptimalIn pruned c := by
  refine ⟨hKeep, ?_⟩
  intro d hd
  exact hOpt.2 d (hSub d hd)

/--
Rapidity-dominated-edge safety predicate on a candidate (Boolean scaffold channel).
`isRapidDominated c = false` means the candidate survives the rapidity dominated-edge veto.
-/
def rapidityDominatedEdgeSafe
    (isRapidDominated : TSPCandidate → Bool)
    (c : TSPCandidate) : Prop :=
  isRapidDominated c = false

/--
Certified hybrid prune transfer:
extends `prune_preserves_optimal_if_witness_kept` with (i) a tensor residual gate
certificate and (ii) a rapidity-dominated-edge safety side condition on the pruned
family. These extra channels are carried explicitly while preserving the same
optimality transfer conclusion.
-/
theorem prune_preserves_optimal_if_witness_kept_hybrid
    (cs pruned : List TSPCandidate)
    (c : TSPCandidate)
    (hSub : ∀ d : TSPCandidate, d ∈ pruned → d ∈ cs)
    (hOpt : TourOptimalIn cs c)
    (hKeep : c ∈ pruned)
    (residual gate : ℝ)
    (hTensorGate : residual ≤ gate)
    (isRapidDominated : TSPCandidate → Bool)
    (hRapiditySafe : ∀ d ∈ pruned, rapidityDominatedEdgeSafe isRapidDominated d) :
    TourOptimalIn pruned c := by
  -- Side channels are explicit obligations for the certified hybrid pipeline.
  have _hTensorChannel : residual ≤ gate := hTensorGate
  have _hRapidityChannel :
      ∀ d ∈ pruned, rapidityDominatedEdgeSafe isRapidDominated d := hRapiditySafe
  -- The core witness-preservation transfer remains identical.
  exact prune_preserves_optimal_if_witness_kept cs pruned c hSub hOpt hKeep

/-! ## Degeneracy barrier for strict-cost pruning -/

/--
Uniform-cost degeneracy:
if every candidate in a finite family has the same `tourCost = k`,
then no strict cost separation witness exists inside that family.
-/
theorem uniform_cost_no_strict_separation
    (cs : List TSPCandidate)
    (k : ℕ)
    (hUniform : ∀ c ∈ cs, c.tourCost = k) :
    ¬ ∃ c ∈ cs, ∃ d ∈ cs, c.tourCost < d.tourCost := by
  intro hStrict
  rcases hStrict with ⟨c, hc, d, hd, hlt⟩
  have hcEq : c.tourCost = k := hUniform c hc
  have hdEq : d.tourCost = k := hUniform d hd
  have hNotLt : ¬ c.tourCost < d.tourCost := by
    simp [hcEq, hdEq]
  exact hNotLt hlt

/--
In a uniform-cost family, every member is a cost-minimal witness
(`TourOptimalIn`) for the family.
-/
theorem uniform_cost_member_is_optimal
    (cs : List TSPCandidate)
    (k : ℕ)
    (hUniform : ∀ c ∈ cs, c.tourCost = k)
    (c : TSPCandidate)
    (hc : c ∈ cs) :
    TourOptimalIn cs c := by
  refine ⟨hc, ?_⟩
  intro d hd
  have hcEq : c.tourCost = k := hUniform c hc
  have hdEq : d.tourCost = k := hUniform d hd
  simp [hcEq, hdEq]

/--
Family-level form of uniform-cost degeneracy:
every member of the family is optimal, so strict-cost pruning is not informative.
-/
theorem uniform_cost_all_members_optimal
    (cs : List TSPCandidate)
    (k : ℕ)
    (hUniform : ∀ c ∈ cs, c.tourCost = k) :
    ∀ c ∈ cs, TourOptimalIn cs c := by
  intro c hc
  exact uniform_cost_member_is_optimal cs k hUniform c hc

/--
Generic geometric tie-break channel in the degenerate boundary regime.
This channel is separate from the uniform `tourCost` term.
-/
def genericGeometricChannel (geom : TSPCandidate → ℤ) (c : TSPCandidate) : ℤ :=
  geom c

/-- Effective score model used for generic degenerate-boundary reasoning. -/
def genericEffectiveScore (geom : TSPCandidate → ℤ) (c : TSPCandidate) : ℤ :=
  Int.ofNat c.tourCost + genericGeometricChannel geom c

/--
In the uniform-cost regime (`tourCost = k` for all candidates), effective-score
ordering is equivalent to geometric-channel ordering.
-/
theorem uniform_cost_effective_order_iff_geometric_order
    (geom : TSPCandidate → ℤ)
    (cs : List TSPCandidate)
    (k : ℕ)
    (hUniform : ∀ c ∈ cs, c.tourCost = k)
    (c₁ c₂ : TSPCandidate)
    (hc₁ : c₁ ∈ cs)
    (hc₂ : c₂ ∈ cs) :
    genericEffectiveScore geom c₁ ≤ genericEffectiveScore geom c₂ ↔
      genericGeometricChannel geom c₁ ≤ genericGeometricChannel geom c₂ := by
  have hk₁ : c₁.tourCost = k := hUniform c₁ hc₁
  have hk₂ : c₂.tourCost = k := hUniform c₂ hc₂
  constructor <;> intro h
  · simpa [genericEffectiveScore, genericGeometricChannel, hk₁, hk₂, Int.add_assoc, Int.add_left_comm, Int.add_comm] using h
  · simpa [genericEffectiveScore, genericGeometricChannel, hk₁, hk₂, Int.add_assoc, Int.add_left_comm, Int.add_comm] using h

/--
Degenerate-boundary near-optimality (effective-score form):
if tour costs are uniform and a witness has geometric-channel gap at most `δ`,
then its effective score is within `δ` of every candidate in the family.
-/
theorem degenerate_uniform_cost_yields_near_optimal_tour
    (geom : TSPCandidate → ℤ)
    (cs : List TSPCandidate)
    (k : ℕ)
    (δ : ℤ)
    (hUniform : ∀ c ∈ cs, c.tourCost = k)
    (w : TSPCandidate)
    (hMem : w ∈ cs)
    (hGeomGap : ∀ c ∈ cs, genericGeometricChannel geom w ≤ genericGeometricChannel geom c + δ) :
    ∀ c ∈ cs, genericEffectiveScore geom w ≤ genericEffectiveScore geom c + δ := by
  intro c hc
  have hkW : w.tourCost = k := hUniform w hMem
  have hkC : c.tourCost = k := hUniform c hc
  have hGap : genericGeometricChannel geom w ≤ genericGeometricChannel geom c + δ := hGeomGap c hc
  have hGap' :
      (Int.ofNat w.tourCost + genericGeometricChannel geom w)
        ≤ (Int.ofNat c.tourCost + genericGeometricChannel geom c) + δ := by
    have hAdd : (Int.ofNat k + genericGeometricChannel geom w)
        ≤ (Int.ofNat k + genericGeometricChannel geom c) + δ := by
      simpa [Int.add_assoc, Int.add_left_comm, Int.add_comm] using
        (add_le_add_left hGap (Int.ofNat k))
    simpa [hkW, hkC, Int.add_assoc, Int.add_left_comm, Int.add_comm] using hAdd
  simpa [genericEffectiveScore, Int.add_assoc, Int.add_left_comm, Int.add_comm] using hGap'

/--
Real-valued form of `degenerate_uniform_cost_yields_near_optimal_tour`:
the same geometric witness gap can be consumed directly by the real-valued ATSP
approximation lemmas.
-/
theorem degenerate_uniform_cost_yields_near_optimal_tour_real
    (geom : TSPCandidate → ℤ)
    (cs : List TSPCandidate)
    (k : ℕ)
    (δ : ℤ)
    (hUniform : ∀ c ∈ cs, c.tourCost = k)
    (w : TSPCandidate)
    (hMem : w ∈ cs)
    (hGeomGap : ∀ c ∈ cs, genericGeometricChannel geom w ≤ genericGeometricChannel geom c + δ) :
    ∀ c ∈ cs, (genericEffectiveScore geom w : ℝ) ≤ (genericEffectiveScore geom c : ℝ) + (δ : ℝ) := by
  intro c hc
  have hInt :
      genericEffectiveScore geom w ≤ genericEffectiveScore geom c + δ :=
    degenerate_uniform_cost_yields_near_optimal_tour
      geom cs k δ hUniform w hMem hGeomGap c hc
  exact_mod_cast hInt

/--
Boolean keep-rule for a hard cost ceiling; used for proof-oriented prune boundaries.
-/
def keepAtMostCost (bound : ℕ) (c : TSPCandidate) : Bool :=
  decide (c.tourCost ≤ bound)

/--
Lower-bound optimality lemma:
if a witness has cost `n` and every candidate cost is at least `n`,
the witness is globally optimal in that finite family.
-/
theorem unit_witness_optimal_of_lower_bound
    (cs : List TSPCandidate)
    (w : TSPCandidate)
    (n : ℕ)
    (hMem : w ∈ cs)
    (hW : w.tourCost = n)
    (hLower : ∀ c ∈ cs, n ≤ c.tourCost) :
    TourOptimalIn cs w := by
  refine ⟨hMem, ?_⟩
  intro d hd
  have hdLower : n ≤ d.tourCost := hLower d hd
  simpa [hW] using hdLower

/--
The witness survives `keepAtMostCost n` whenever its cost is exactly `n`.
-/
theorem unit_witness_kept_by_keepAtMostCost
    (cs : List TSPCandidate)
    (w : TSPCandidate)
    (n : ℕ)
    (hMem : w ∈ cs)
    (hW : w.tourCost = n) :
    w ∈ pruneBy (keepAtMostCost n) cs := by
  have hKeep : keepAtMostCost n w = true := by
    simp [keepAtMostCost, hW]
  simpa [pruneBy] using List.mem_filter.mpr ⟨hMem, hKeep⟩

/--
Boundary-uniformity of the pruned family:
if every source candidate has cost at least `n`, then pruning by `tourCost ≤ n`
forces every survivor to have cost exactly `n`.
-/
theorem prune_boundary_uniform_cost
    (cs : List TSPCandidate)
    (n : ℕ)
    (hLower : ∀ c ∈ cs, n ≤ c.tourCost) :
    ∀ c ∈ pruneBy (keepAtMostCost n) cs, c.tourCost = n := by
  intro c hc
  have hcSource : c ∈ cs := pruneBy_subset (keepAtMostCost n) cs c hc
  have hKeep : keepAtMostCost n c = true := by
    simpa [pruneBy] using (List.mem_filter.mp hc).2
  have hLower' : n ≤ c.tourCost := hLower c hcSource
  have hUpper : c.tourCost ≤ n := by
    simp [keepAtMostCost] at hKeep
    exact hKeep
  exact Nat.le_antisymm hUpper hLower'

/--
Concrete pruned-family geometric-gap bridge:
at the unit prune boundary, the witness survives as optimal in the pruned family,
and the real-valued effective-score gap against any retained comparison witness is
controlled by the geometric channel slack `δ`.
-/
theorem prune_boundary_family_generates_seed_gap
    (geom : TSPCandidate → ℤ)
    (cs : List TSPCandidate)
    (w cOpt : TSPCandidate)
    (n : ℕ)
    (δ : ℤ)
    (seedCost optimalCost tensorResidualErr rapidityErr axisErr : ℝ)
    (hMem : w ∈ cs)
    (hW : w.tourCost = n)
    (hLower : ∀ c ∈ cs, n ≤ c.tourCost)
    (hGeomGap :
      ∀ c ∈ pruneBy (keepAtMostCost n) cs,
        genericGeometricChannel geom w ≤ genericGeometricChannel geom c + δ)
    (hOptMem : cOpt ∈ pruneBy (keepAtMostCost n) cs)
    (hOptScore : (genericEffectiveScore geom cOpt : ℝ) ≤ optimalCost)
    (hSeedLift :
      seedCost ≤
        (genericEffectiveScore geom w : ℝ) +
          tensorResidualErr + rapidityErr + axisErr) :
    TourOptimalIn (pruneBy (keepAtMostCost n) cs) w ∧
    seedCost ≤
      optimalCost + (δ : ℝ) + tensorResidualErr + rapidityErr + axisErr := by
  have hOpt : TourOptimalIn cs w :=
    unit_witness_optimal_of_lower_bound cs w n hMem hW hLower
  have hWPruned : w ∈ pruneBy (keepAtMostCost n) cs :=
    unit_witness_kept_by_keepAtMostCost cs w n hMem hW
  have hPrunedOpt : TourOptimalIn (pruneBy (keepAtMostCost n) cs) w :=
    prune_preserves_optimal_if_witness_kept
      cs (pruneBy (keepAtMostCost n) cs) w
      (pruneBy_subset (keepAtMostCost n) cs) hOpt hWPruned
  have hUniform :
      ∀ c ∈ pruneBy (keepAtMostCost n) cs, c.tourCost = n :=
    prune_boundary_uniform_cost cs n hLower
  have hScoreGap :
      (genericEffectiveScore geom w : ℝ) ≤
        (genericEffectiveScore geom cOpt : ℝ) + (δ : ℝ) :=
    degenerate_uniform_cost_yields_near_optimal_tour_real
      geom (pruneBy (keepAtMostCost n) cs) n δ hUniform w hWPruned hGeomGap cOpt hOptMem
  refine ⟨hPrunedOpt, ?_⟩
  linarith

/--
Degeneracy boundary prune theorem (proof-first version):

If a family has a witness at cost `n` and all candidate costs are bounded below by `n`,
then pruning by `tourCost ≤ n` is safe and preserves an optimal witness.
-/
theorem prune_boundary_safe_of_unit_witness
    (cs : List TSPCandidate)
    (w : TSPCandidate)
    (n : ℕ)
    (hMem : w ∈ cs)
    (hW : w.tourCost = n)
    (hLower : ∀ c ∈ cs, n ≤ c.tourCost) :
    TourOptimalIn (pruneBy (keepAtMostCost n) cs) w := by
  have hOpt : TourOptimalIn cs w :=
    unit_witness_optimal_of_lower_bound cs w n hMem hW hLower
  have hKeep : w ∈ pruneBy (keepAtMostCost n) cs :=
    unit_witness_kept_by_keepAtMostCost cs w n hMem hW
  exact prune_preserves_optimal_if_witness_kept
    cs (pruneBy (keepAtMostCost n) cs) w
    (pruneBy_subset (keepAtMostCost n) cs) hOpt hKeep

/--
Hybrid certified boundary theorem:
adds tensor residual gate and rapidity-dominated-edge conditions to the
proof-first boundary `tourCost ≤ n`, preserving the witness in the pruned family.
-/
theorem prune_boundary_safe_of_unit_witness_hybrid
    (cs : List TSPCandidate)
    (w : TSPCandidate)
    (n : ℕ)
    (hMem : w ∈ cs)
    (hW : w.tourCost = n)
    (hLower : ∀ c ∈ cs, n ≤ c.tourCost)
    (residual gate : ℝ)
    (hTensorGate : residual ≤ gate)
    (isRapidDominated : TSPCandidate → Bool)
    (hRapiditySafe : ∀ c ∈ pruneBy (keepAtMostCost n) cs, rapidityDominatedEdgeSafe isRapidDominated c) :
    TourOptimalIn (pruneBy (keepAtMostCost n) cs) w := by
  have hOpt : TourOptimalIn cs w :=
    unit_witness_optimal_of_lower_bound cs w n hMem hW hLower
  have hKeep : w ∈ pruneBy (keepAtMostCost n) cs :=
    unit_witness_kept_by_keepAtMostCost cs w n hMem hW
  exact prune_preserves_optimal_if_witness_kept_hybrid
    cs (pruneBy (keepAtMostCost n) cs) w
    (pruneBy_subset (keepAtMostCost n) cs) hOpt hKeep
    residual gate hTensorGate isRapidDominated hRapiditySafe

/--
Recursion-budget scaffold: closed-form upper bound used for bounded recursive
intercept searches (`topk` retained candidates, branching factor `beam`).
-/
def recursiveCandidateBudget (depth beam topk : ℕ) : ℕ :=
  topk * beam ^ depth

/--
If recursion level `0` is bounded by `topk` and each next level is at most
`beam` times the previous level, then level `depth` is bounded by
`topk * beam^depth`.
-/
theorem recursive_candidate_count_bounded_of_step
    (levels : ℕ → List TSPCandidate)
    (topk beam : ℕ)
    (h0 : (levels 0).length ≤ topk)
    (hStep : ∀ l : ℕ, (levels (l + 1)).length ≤ beam * (levels l).length) :
    ∀ depth : ℕ, (levels depth).length ≤ recursiveCandidateBudget depth beam topk := by
  intro depth
  induction depth with
  | zero =>
      simpa [recursiveCandidateBudget] using h0
  | succ d ih =>
      have hstep := hStep d
      calc
        (levels (d + 1)).length ≤ beam * (levels d).length := hstep
        _ ≤ beam * (topk * beam ^ d) := Nat.mul_le_mul_left beam ih
        _ = topk * beam ^ (d + 1) := by
              simp [Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm]

/--
One-line specialization helper when per-level bounds are already available.
-/
theorem recursive_candidate_count_bounded
    (levels : ℕ → List TSPCandidate)
    (topk beam depth : ℕ)
    (hBound : ∀ l : ℕ, (levels l).length ≤ recursiveCandidateBudget l beam topk) :
    (levels depth).length ≤ recursiveCandidateBudget depth beam topk :=
  hBound depth

/-- Recursive level constructor from an initial family and one step operator. -/
def recursiveLevel
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate) : ℕ → List TSPCandidate
  | 0 => initial
  | n + 1 => stepOp (recursiveLevel stepOp initial n)

/-- Pipeline determinism: same operator/initial family gives identical levels. -/
theorem recursive_pipeline_deterministic
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (depth : ℕ) :
    recursiveLevel stepOp initial depth = recursiveLevel stepOp initial depth := by
  rfl

/--
If one recursive step satisfies a multiplicative beam bound, all recursive levels
inherit the global `topk * beam^depth` candidate budget.
-/
theorem recursive_level_count_bounded
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (topk beam : ℕ)
    (h0 : initial.length ≤ topk)
    (hStep : ∀ cs : List TSPCandidate, (stepOp cs).length ≤ beam * cs.length) :
    ∀ depth : ℕ,
      (recursiveLevel stepOp initial depth).length ≤ recursiveCandidateBudget depth beam topk := by
  have hStep' : ∀ l : ℕ,
      (recursiveLevel stepOp initial (l + 1)).length ≤
        beam * (recursiveLevel stepOp initial l).length := by
    intro l
    simpa [recursiveLevel] using hStep (recursiveLevel stepOp initial l)
  exact recursive_candidate_count_bounded_of_step
    (levels := recursiveLevel stepOp initial) topk beam h0 hStep'

/--
Subfactorial explored-search transfer:
if the certified recursive budget `topk * beam^depth` lies strictly below the
factorial baseline for the ambient tour arity, then the explored level itself is
strictly subfactorial.
-/
theorem recursive_level_count_lt_factorial_of_budget
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (topk beam depth tourArity : ℕ)
    (h0 : initial.length ≤ topk)
    (hStep : ∀ cs : List TSPCandidate, (stepOp cs).length ≤ beam * cs.length)
    (hBudgetLt : recursiveCandidateBudget depth beam topk < Nat.factorial tourArity) :
    (recursiveLevel stepOp initial depth).length < Nat.factorial tourArity := by
  have hBudget :
      (recursiveLevel stepOp initial depth).length ≤
        recursiveCandidateBudget depth beam topk :=
    recursive_level_count_bounded stepOp initial topk beam h0 hStep depth
  exact lt_of_le_of_lt hBudget hBudgetLt

/--
Certificate packaging for the subfactorial search regime.

`geometricGap > 0` records departure from exact degeneracy. The actual algorithm-
specific argument turning that departure into concrete `topk` / `beam` controls is
kept external; this structure stores the resulting certified recursive budget.
-/
structure DepartedDegeneracySearchCertificate where
  tourArity : ℕ
  depth : ℕ
  topk : ℕ
  beam : ℕ
  geometricGap : ℝ
  hDeparture : 0 < geometricGap
  hBudgetLtFactorial : recursiveCandidateBudget depth beam topk < Nat.factorial tourArity

/--
Departure-from-degeneracy certificate implies subfactorial explored search.
-/
theorem departed_degeneracy_certificate_implies_subfactorial_search
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (cert : DepartedDegeneracySearchCertificate)
    (h0 : initial.length ≤ cert.topk)
    (hStep : ∀ cs : List TSPCandidate, (stepOp cs).length ≤ cert.beam * cs.length) :
    (recursiveLevel stepOp initial cert.depth).length < Nat.factorial cert.tourArity := by
  exact recursive_level_count_lt_factorial_of_budget
    stepOp initial cert.topk cert.beam cert.depth cert.tourArity
    h0 hStep cert.hBudgetLtFactorial

/--
Reduced-frontier profile extracted from a positive departure from exact
degeneracy.

The geometric gap itself does not directly count candidates; instead it certifies
that the search can be restricted to a smaller frontier arity together with
bounded `topk` and `beam`.
-/
structure ReducedFrontierDegeneracyProfile where
  tourArity : ℕ
  frontierArity : ℕ
  depth : ℕ
  topk : ℕ
  beam : ℕ
  geometricGap : ℝ
  hDeparture : 0 < geometricGap
  hFrontierPos : 1 ≤ frontierArity
  hFrontierLeTour : frontierArity ≤ tourArity
  hTopkLt : topk < Nat.factorial frontierArity
  hBeamPos : 0 < beam
  hBeamLe : beam ≤ frontierArity
  hDepthLe : depth ≤ tourArity - frontierArity

/--
Concrete budget derivation:
a reduced-frontier departure profile forces the certified recursive budget below
the factorial baseline of the ambient tour arity.
-/
theorem reduced_frontier_profile_budget_lt_factorial
    (p : ReducedFrontierDegeneracyProfile) :
    recursiveCandidateBudget p.depth p.beam p.topk < Nat.factorial p.tourArity := by
  have hTopkMul :
      p.topk * p.beam ^ p.depth < Nat.factorial p.frontierArity * p.beam ^ p.depth := by
    exact Nat.mul_lt_mul_of_pos_right p.hTopkLt (Nat.pow_pos p.hBeamPos)
  have hBeamPowLe : p.beam ^ p.depth ≤ p.frontierArity ^ p.depth := by
    exact Nat.pow_le_pow_left p.hBeamLe _
  have hDepthPowLe :
      p.frontierArity ^ p.depth ≤ p.frontierArity ^ (p.tourArity - p.frontierArity) := by
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt p.hFrontierPos) p.hDepthLe
  have hFrontierToFactorial :
      Nat.factorial p.frontierArity * p.frontierArity ^ p.depth ≤ Nat.factorial p.tourArity := by
    calc
      Nat.factorial p.frontierArity * p.frontierArity ^ p.depth
          ≤ Nat.factorial p.frontierArity * p.frontierArity ^ (p.tourArity - p.frontierArity) := by
            exact Nat.mul_le_mul_left _ hDepthPowLe
      _ ≤ Nat.factorial p.tourArity := by
            exact Nat.factorial_mul_pow_sub_le_factorial p.hFrontierLeTour
  calc
    recursiveCandidateBudget p.depth p.beam p.topk
        = p.topk * p.beam ^ p.depth := by
          simp [recursiveCandidateBudget]
    _ < Nat.factorial p.frontierArity * p.beam ^ p.depth := hTopkMul
    _ ≤ Nat.factorial p.frontierArity * p.frontierArity ^ p.depth := by
          exact Nat.mul_le_mul_left _ hBeamPowLe
    _ ≤ Nat.factorial p.tourArity := hFrontierToFactorial

/-- Reduced-frontier profile canonically yields a subfactorial search certificate. -/
def ReducedFrontierDegeneracyProfile.toSearchCertificate
    (p : ReducedFrontierDegeneracyProfile) : DepartedDegeneracySearchCertificate where
  tourArity := p.tourArity
  depth := p.depth
  topk := p.topk
  beam := p.beam
  geometricGap := p.geometricGap
  hDeparture := p.hDeparture
  hBudgetLtFactorial := reduced_frontier_profile_budget_lt_factorial p

/--
Positive departure from degeneracy plus a reduced-frontier profile implies
subfactorial explored search.
-/
theorem reduced_frontier_profile_implies_subfactorial_search
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (p : ReducedFrontierDegeneracyProfile)
    (h0 : initial.length ≤ p.topk)
    (hStep : ∀ cs : List TSPCandidate, (stepOp cs).length ≤ p.beam * cs.length) :
    (recursiveLevel stepOp initial p.depth).length < Nat.factorial p.tourArity := by
  exact departed_degeneracy_certificate_implies_subfactorial_search
    stepOp initial p.toSearchCertificate h0 hStep

/--
Sharper explored-search transfer with beam slack:
if departure from degeneracy forces the effective branching factor below the
frontier by a certified slack `slack`, the explored level is bounded by the
smaller exponential base `(frontierArity - slack)^depth`.
-/
theorem recursive_level_count_le_of_beam_slack
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (topk beam depth frontierArity slack : ℕ)
    (h0 : initial.length ≤ topk)
    (hStep : ∀ cs : List TSPCandidate, (stepOp cs).length ≤ beam * cs.length)
    (hBeamSlack : beam + slack ≤ frontierArity) :
    (recursiveLevel stepOp initial depth).length ≤
      topk * (frontierArity - slack) ^ depth := by
  have hBudget :
      (recursiveLevel stepOp initial depth).length ≤
        recursiveCandidateBudget depth beam topk :=
    recursive_level_count_bounded stepOp initial topk beam h0 hStep depth
  have hBeamLe : beam ≤ frontierArity - slack :=
    Nat.le_sub_of_add_le hBeamSlack
  have hPowLe : beam ^ depth ≤ (frontierArity - slack) ^ depth := by
    exact Nat.pow_le_pow_left hBeamLe _
  calc
    (recursiveLevel stepOp initial depth).length
        ≤ recursiveCandidateBudget depth beam topk := hBudget
    _ = topk * beam ^ depth := by simp [recursiveCandidateBudget]
    _ ≤ topk * (frontierArity - slack) ^ depth := by
          exact Nat.mul_le_mul_left _ hPowLe

/--
Profile form of the beam-slack sharpening.
-/
theorem reduced_frontier_profile_implies_explicit_search_bound
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (p : ReducedFrontierDegeneracyProfile)
    (slack : ℕ)
    (h0 : initial.length ≤ p.topk)
    (hStep : ∀ cs : List TSPCandidate, (stepOp cs).length ≤ p.beam * cs.length)
    (hBeamSlack : p.beam + slack ≤ p.frontierArity) :
    (recursiveLevel stepOp initial p.depth).length ≤
      p.topk * (p.frontierArity - slack) ^ p.depth := by
  exact recursive_level_count_le_of_beam_slack
    stepOp initial p.topk p.beam p.depth p.frontierArity slack
    h0 hStep hBeamSlack

/--
Canonical slack extracted from degeneracy departure:
the usable slack is the smaller of the available frontier margin and the integer
gap quanta carried by `δ`.
-/
def slackFromGap (frontierArity beam : ℕ) (δ : ℤ) : ℕ :=
  min (frontierArity - beam) (Int.toNat δ)

/-- The slack extracted from `δ` never exceeds the available frontier margin. -/
theorem slackFromGap_le_margin
    (frontierArity beam : ℕ)
    (δ : ℤ) :
    slackFromGap frontierArity beam δ ≤ frontierArity - beam := by
  exact min_le_left _ _

/-- The slack extracted from `δ` never exceeds the integer gap quanta. -/
theorem slackFromGap_le_gapNat
    (frontierArity beam : ℕ)
    (δ : ℤ) :
    slackFromGap frontierArity beam δ ≤ Int.toNat δ := by
  exact min_le_right _ _

/--
The canonical gap slack automatically satisfies the beam-slack admissibility
constraint.
-/
theorem beam_add_slackFromGap_le_frontier
    (frontierArity beam : ℕ)
    (δ : ℤ)
    (hBeamLe : beam ≤ frontierArity) :
    beam + slackFromGap frontierArity beam δ ≤ frontierArity := by
  have hSlackLe : slackFromGap frontierArity beam δ ≤ frontierArity - beam :=
    slackFromGap_le_margin frontierArity beam δ
  calc
    beam + slackFromGap frontierArity beam δ ≤ beam + (frontierArity - beam) := by
      exact Nat.add_le_add_left hSlackLe beam
    _ = frontierArity := Nat.add_sub_of_le hBeamLe

/--
Gap-quantized beam-slack refinement:
the search bound can be stated using the canonical slack extracted directly from
`δ`, with no separate slack hypothesis.
-/
theorem reduced_frontier_profile_implies_gap_slack_search_bound
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (p : ReducedFrontierDegeneracyProfile)
    (δ : ℤ)
    (h0 : initial.length ≤ p.topk)
    (hStep : ∀ cs : List TSPCandidate, (stepOp cs).length ≤ p.beam * cs.length) :
    (recursiveLevel stepOp initial p.depth).length ≤
      p.topk * (p.frontierArity - slackFromGap p.frontierArity p.beam δ) ^ p.depth := by
  have hBeamSlack :
      p.beam + slackFromGap p.frontierArity p.beam δ ≤ p.frontierArity :=
    beam_add_slackFromGap_le_frontier p.frontierArity p.beam δ p.hBeamLe
  exact reduced_frontier_profile_implies_explicit_search_bound
    stepOp initial p (slackFromGap p.frontierArity p.beam δ) h0 hStep hBeamSlack

/--
Canonical reduced-frontier profile extracted from a concrete pruned near-
degenerate family.

The retained frontier size is the pruned family length itself; the geometric gap
is the real lift of the integer slack `δ`.
-/
def pruneBoundaryFamilyReducedFrontierProfile
    (cs : List TSPCandidate)
    (n : ℕ)
    (δ : ℤ)
    (tourArity frontierArity depth beam : ℕ)
    (hδpos : 0 < (δ : ℝ))
    (hFrontierPos : 1 ≤ frontierArity)
    (hFrontierLeTour : frontierArity ≤ tourArity)
    (hTopkLt : (pruneBy (keepAtMostCost n) cs).length < Nat.factorial frontierArity)
    (hBeamPos : 0 < beam)
    (hBeamLe : beam ≤ frontierArity)
    (hDepthLe : depth ≤ tourArity - frontierArity) :
    ReducedFrontierDegeneracyProfile where
  tourArity := tourArity
  frontierArity := frontierArity
  depth := depth
  topk := (pruneBy (keepAtMostCost n) cs).length
  beam := beam
  geometricGap := (δ : ℝ)
  hDeparture := hδpos
  hFrontierPos := hFrontierPos
  hFrontierLeTour := hFrontierLeTour
  hTopkLt := hTopkLt
  hBeamPos := hBeamPos
  hBeamLe := hBeamLe
  hDepthLe := hDepthLe

/--
Concrete refinement:
a pruned near-degenerate family with positive gap `δ` both yields the seed-gap
bound from the witness theorem and induces a reduced-frontier profile, hence a
subfactorial explored-search bound for any recursion matching the certified
`topk` / `beam` / `depth` controls.
-/
theorem prune_boundary_family_departure_implies_seed_gap_and_subfactorial_search
    (geom : TSPCandidate → ℤ)
    (cs : List TSPCandidate)
    (w cOpt : TSPCandidate)
    (n : ℕ)
    (δ : ℤ)
    (seedCost optimalCost tensorResidualErr rapidityErr axisErr : ℝ)
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (tourArity frontierArity depth beam : ℕ)
    (hMem : w ∈ cs)
    (hW : w.tourCost = n)
    (hLower : ∀ c ∈ cs, n ≤ c.tourCost)
    (hGeomGap :
      ∀ c ∈ pruneBy (keepAtMostCost n) cs,
        genericGeometricChannel geom w ≤ genericGeometricChannel geom c + δ)
    (hOptMem : cOpt ∈ pruneBy (keepAtMostCost n) cs)
    (hOptScore : (genericEffectiveScore geom cOpt : ℝ) ≤ optimalCost)
    (hSeedLift :
      seedCost ≤
        (genericEffectiveScore geom w : ℝ) +
          tensorResidualErr + rapidityErr + axisErr)
    (hδpos : 0 < (δ : ℝ))
    (hFrontierPos : 1 ≤ frontierArity)
    (hFrontierLeTour : frontierArity ≤ tourArity)
    (hTopkLt : (pruneBy (keepAtMostCost n) cs).length < Nat.factorial frontierArity)
    (hBeamPos : 0 < beam)
    (hBeamLe : beam ≤ frontierArity)
    (hDepthLe : depth ≤ tourArity - frontierArity)
    (h0 : initial.length ≤ (pruneBy (keepAtMostCost n) cs).length)
    (hStep : ∀ xs : List TSPCandidate, (stepOp xs).length ≤ beam * xs.length) :
    TourOptimalIn (pruneBy (keepAtMostCost n) cs) w ∧
    seedCost ≤
      optimalCost + (δ : ℝ) + tensorResidualErr + rapidityErr + axisErr ∧
    (recursiveLevel stepOp initial depth).length < Nat.factorial tourArity := by
  have hFamily :
      TourOptimalIn (pruneBy (keepAtMostCost n) cs) w ∧
      seedCost ≤
        optimalCost + (δ : ℝ) + tensorResidualErr + rapidityErr + axisErr :=
    prune_boundary_family_generates_seed_gap
      geom cs w cOpt n δ
      seedCost optimalCost tensorResidualErr rapidityErr axisErr
      hMem hW hLower hGeomGap hOptMem hOptScore hSeedLift
  let p : ReducedFrontierDegeneracyProfile :=
    pruneBoundaryFamilyReducedFrontierProfile
      cs n δ tourArity frontierArity depth beam
      hδpos hFrontierPos hFrontierLeTour hTopkLt hBeamPos hBeamLe hDepthLe
  have hSearch :
      (recursiveLevel stepOp initial depth).length < Nat.factorial tourArity := by
    simpa [p] using
      reduced_frontier_profile_implies_subfactorial_search
        stepOp initial p h0 hStep
  exact ⟨hFamily.1, hFamily.2, hSearch⟩

/--
Sharper concrete refinement with beam slack:
the same pruned near-degenerate family yields the witness/seed-gap conclusions and
an explicit explored-search bound with reduced base `(frontierArity - slack)^depth`.
-/
theorem prune_boundary_family_departure_implies_explicit_search_bound
    (geom : TSPCandidate → ℤ)
    (cs : List TSPCandidate)
    (w cOpt : TSPCandidate)
    (n : ℕ)
    (δ : ℤ)
    (seedCost optimalCost tensorResidualErr rapidityErr axisErr : ℝ)
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (tourArity frontierArity depth beam slack : ℕ)
    (hMem : w ∈ cs)
    (hW : w.tourCost = n)
    (hLower : ∀ c ∈ cs, n ≤ c.tourCost)
    (hGeomGap :
      ∀ c ∈ pruneBy (keepAtMostCost n) cs,
        genericGeometricChannel geom w ≤ genericGeometricChannel geom c + δ)
    (hOptMem : cOpt ∈ pruneBy (keepAtMostCost n) cs)
    (hOptScore : (genericEffectiveScore geom cOpt : ℝ) ≤ optimalCost)
    (hSeedLift :
      seedCost ≤
        (genericEffectiveScore geom w : ℝ) +
          tensorResidualErr + rapidityErr + axisErr)
    (hδpos : 0 < (δ : ℝ))
    (hFrontierPos : 1 ≤ frontierArity)
    (hFrontierLeTour : frontierArity ≤ tourArity)
    (hTopkLt : (pruneBy (keepAtMostCost n) cs).length < Nat.factorial frontierArity)
    (hBeamPos : 0 < beam)
    (hBeamLe : beam ≤ frontierArity)
    (hDepthLe : depth ≤ tourArity - frontierArity)
    (h0 : initial.length ≤ (pruneBy (keepAtMostCost n) cs).length)
    (hStep : ∀ xs : List TSPCandidate, (stepOp xs).length ≤ beam * xs.length)
    (hBeamSlack : beam + slack ≤ frontierArity) :
    TourOptimalIn (pruneBy (keepAtMostCost n) cs) w ∧
    seedCost ≤
      optimalCost + (δ : ℝ) + tensorResidualErr + rapidityErr + axisErr ∧
    (recursiveLevel stepOp initial depth).length ≤
      (pruneBy (keepAtMostCost n) cs).length * (frontierArity - slack) ^ depth := by
  have hFamily :
      TourOptimalIn (pruneBy (keepAtMostCost n) cs) w ∧
      seedCost ≤
        optimalCost + (δ : ℝ) + tensorResidualErr + rapidityErr + axisErr :=
    prune_boundary_family_generates_seed_gap
      geom cs w cOpt n δ
      seedCost optimalCost tensorResidualErr rapidityErr axisErr
      hMem hW hLower hGeomGap hOptMem hOptScore hSeedLift
  let p : ReducedFrontierDegeneracyProfile :=
    pruneBoundaryFamilyReducedFrontierProfile
      cs n δ tourArity frontierArity depth beam
      hδpos hFrontierPos hFrontierLeTour hTopkLt hBeamPos hBeamLe hDepthLe
  have hSearch :
      (recursiveLevel stepOp initial depth).length ≤
        (pruneBy (keepAtMostCost n) cs).length * (frontierArity - slack) ^ depth := by
    simpa [p, pruneBoundaryFamilyReducedFrontierProfile] using
      reduced_frontier_profile_implies_explicit_search_bound
        stepOp initial p slack h0 hStep hBeamSlack
  exact ⟨hFamily.1, hFamily.2, hSearch⟩

/--
Gap-to-slack concrete refinement:
the beam slack is extracted canonically from the degeneracy departure `δ`, so the
explicit explored-search bound no longer needs a separate slack hypothesis.
-/
theorem prune_boundary_family_departure_implies_gap_slack_search_bound
    (geom : TSPCandidate → ℤ)
    (cs : List TSPCandidate)
    (w cOpt : TSPCandidate)
    (n : ℕ)
    (δ : ℤ)
    (seedCost optimalCost tensorResidualErr rapidityErr axisErr : ℝ)
    (stepOp : List TSPCandidate → List TSPCandidate)
    (initial : List TSPCandidate)
    (tourArity frontierArity depth beam : ℕ)
    (hMem : w ∈ cs)
    (hW : w.tourCost = n)
    (hLower : ∀ c ∈ cs, n ≤ c.tourCost)
    (hGeomGap :
      ∀ c ∈ pruneBy (keepAtMostCost n) cs,
        genericGeometricChannel geom w ≤ genericGeometricChannel geom c + δ)
    (hOptMem : cOpt ∈ pruneBy (keepAtMostCost n) cs)
    (hOptScore : (genericEffectiveScore geom cOpt : ℝ) ≤ optimalCost)
    (hSeedLift :
      seedCost ≤
        (genericEffectiveScore geom w : ℝ) +
          tensorResidualErr + rapidityErr + axisErr)
    (hδpos : 0 < (δ : ℝ))
    (hFrontierPos : 1 ≤ frontierArity)
    (hFrontierLeTour : frontierArity ≤ tourArity)
    (hTopkLt : (pruneBy (keepAtMostCost n) cs).length < Nat.factorial frontierArity)
    (hBeamPos : 0 < beam)
    (hBeamLe : beam ≤ frontierArity)
    (hDepthLe : depth ≤ tourArity - frontierArity)
    (h0 : initial.length ≤ (pruneBy (keepAtMostCost n) cs).length)
    (hStep : ∀ xs : List TSPCandidate, (stepOp xs).length ≤ beam * xs.length) :
    TourOptimalIn (pruneBy (keepAtMostCost n) cs) w ∧
    seedCost ≤
      optimalCost + (δ : ℝ) + tensorResidualErr + rapidityErr + axisErr ∧
    (recursiveLevel stepOp initial depth).length ≤
      (pruneBy (keepAtMostCost n) cs).length *
        (frontierArity - slackFromGap frontierArity beam δ) ^ depth := by
  have hFamily :
      TourOptimalIn (pruneBy (keepAtMostCost n) cs) w ∧
      seedCost ≤
        optimalCost + (δ : ℝ) + tensorResidualErr + rapidityErr + axisErr :=
    prune_boundary_family_generates_seed_gap
      geom cs w cOpt n δ
      seedCost optimalCost tensorResidualErr rapidityErr axisErr
      hMem hW hLower hGeomGap hOptMem hOptScore hSeedLift
  let p : ReducedFrontierDegeneracyProfile :=
    pruneBoundaryFamilyReducedFrontierProfile
      cs n δ tourArity frontierArity depth beam
      hδpos hFrontierPos hFrontierLeTour hTopkLt hBeamPos hBeamLe hDepthLe
  have hSearch :
      (recursiveLevel stepOp initial depth).length ≤
        (pruneBy (keepAtMostCost n) cs).length *
          (frontierArity - slackFromGap frontierArity beam δ) ^ depth := by
    simpa [p, pruneBoundaryFamilyReducedFrontierProfile] using
      reduced_frontier_profile_implies_gap_slack_search_bound
        stepOp initial p δ h0 hStep
  exact ⟨hFamily.1, hFamily.2, hSearch⟩

/-- Recursive specialization of prune-safety optimality transfer. -/
theorem recursive_prune_preserves_optimal_if_kept
    (keep : TSPCandidate → Bool)
    (cs : List TSPCandidate)
    (c : TSPCandidate)
    (hOpt : TourOptimalIn cs c)
    (hKeep : c ∈ pruneBy keep cs) :
    TourOptimalIn (pruneBy keep cs) c := by
  exact prune_preserves_optimal_if_witness_kept cs (pruneBy keep cs) c
    (pruneBy_subset keep cs) hOpt hKeep

/--
Lightweight annulus-anchor compatibility predicate for a candidate:
both anchor endpoints occur somewhere in the tour list.
-/
def annulusAnchorCompatible (anchorCity anchorNext : ℕ) (c : TSPCandidate) : Prop :=
  anchorCity ∈ c.tour ∧ anchorNext ∈ c.tour

/--
Annulus candidate theorem:
for any nonempty anchor-compatible annulus candidate family, there exists a
tour-cost-minimal candidate in that family, and that witness remains
anchor-compatible.
-/
theorem annulus_candidate_optimal_exists
    (anchorCity anchorNext : ℕ)
    (annulusCandidates : List TSPCandidate)
    (hNonempty : annulusCandidates ≠ [])
    (hCompat :
      ∀ c ∈ annulusCandidates, annulusAnchorCompatible anchorCity anchorNext c) :
    ∃ c ∈ annulusCandidates,
      annulusAnchorCompatible anchorCity anchorNext c ∧
      ∀ d ∈ annulusCandidates, c.tourCost ≤ d.tourCost := by
  rcases tsp_optimal_candidate_exists annulusCandidates hNonempty with ⟨c, hcMem, hcMin⟩
  refine ⟨c, hcMem, ?_⟩
  exact ⟨hCompat c hcMem, hcMin⟩

/--
Pairwise anchored-intercept compatibility:
the anchor city and both anchor-next cities appear in the decoded tour.
-/
def interceptAnchorCompatible
    (anchorCity leftNext rightNext : ℕ) (c : TSPCandidate) : Prop :=
  anchorCity ∈ c.tour ∧ leftNext ∈ c.tour ∧ rightNext ∈ c.tour

/--
Intercept candidate theorem:
for any nonempty pairwise-intercept candidate family satisfying the intercept
compatibility channel, there exists a tour-cost-minimal witness in that family.
-/
theorem intercept_candidate_optimal_exists
    (anchorCity leftNext rightNext : ℕ)
    (interceptCandidates : List TSPCandidate)
    (hNonempty : interceptCandidates ≠ [])
    (hCompat :
      ∀ c ∈ interceptCandidates,
        interceptAnchorCompatible anchorCity leftNext rightNext c) :
    ∃ c ∈ interceptCandidates,
      interceptAnchorCompatible anchorCity leftNext rightNext c ∧
      ∀ d ∈ interceptCandidates, c.tourCost ≤ d.tourCost := by
  rcases tsp_optimal_candidate_exists interceptCandidates hNonempty with ⟨c, hcMem, hcMin⟩
  refine ⟨c, hcMem, ?_⟩
  exact ⟨hCompat c hcMem, hcMin⟩

/-! ## Directed torus ATSP bridge (arbitrary asymmetric costs) -/

/-- Directed-torus candidate carrying a matrix-aware non-associative correction. -/
structure DirectedTorusATSPCandidate extends TSPCandidate where
  associatorTerm : ℤ := 0
  effectiveScore : ℤ := 0

/--
Effective directed score channel:
`rootDistance + tourCost + associatorTerm` (integer scaffold form).
-/
def directedEffectiveScore (c : DirectedTorusATSPCandidate) : ℤ :=
  (Int.ofNat c.rootDistance) + (Int.ofNat c.tourCost) + c.associatorTerm

/--
If the chosen directed effective score is monotone with true tour cost over the
finite candidate family, then minimizing effective score also minimizes tour cost.
-/
theorem directed_torus_effective_minimizes_tourCost
    (cs : List DirectedTorusATSPCandidate)
    (hMono :
      ∀ c₁ ∈ cs, ∀ c₂ ∈ cs,
        directedEffectiveScore c₁ ≤ directedEffectiveScore c₂ →
          c₁.tourCost ≤ c₂.tourCost)
    (cStar : DirectedTorusATSPCandidate)
    (hMem : cStar ∈ cs)
    (hMin : ∀ c ∈ cs, directedEffectiveScore cStar ≤ directedEffectiveScore c) :
    ∀ c ∈ cs, cStar.tourCost ≤ c.tourCost := by
  intro c hc
  exact hMono cStar hMem c hc (hMin c hc)

/-! ## Modular bridge -/

/-- Lightweight modular-form interface used by the geometric oracle bridge. -/
structure ModularFormLike where
  coefficients : ℕ → ℂ

/-- Lightweight L-function interface for zero-location bridge statements. -/
structure LFunctionLike where
  hasZeroAt : ℕ → Prop

/-- Upper-half-plane lift from the discrete arc parameter. -/
def upperHalfFromArc (a : ArcParameter) : UpperHalfPlane :=
  ⟨(a : ℂ) + Complex.I, by simp⟩

/-- Modular specialization of a geometric candidate. -/
structure ModularCandidate extends Candidate where
  tau : UpperHalfPlane
  fourierMode : ℕ
  lValue : Option ℂ := none

/-- Modular candidate stream induced from the bounded geometric list. -/
def modularCandidateList (f : ModularFormLike) (n : ℕ) : List ModularCandidate :=
  (candidateListWithSymmetricTip n).map (fun c =>
    { toCandidate := c
      tau := upperHalfFromArc c.arcParam
      fourierMode := n * c.step + c.seedIdx.1
      lValue := some (f.coefficients (n + c.step)) })

/-- Placeholder crossing functional for modular candidates (scaffold slot). -/
def netInterceptCrossingsModular (_cs : List ModularCandidate) : ℂ := 0

/--
Bridge theorem: once a chosen modular crossing functional is identified with the
target coefficient, the geometric list recovers that coefficient.
-/
theorem modular_spiral_recovers_fourier_coefficients
    (f : ModularFormLike) (n : ℕ)
    (hCoeff : f.coefficients n = netInterceptCrossingsModular (modularCandidateList f n)) :
    f.coefficients n = netInterceptCrossingsModular (modularCandidateList f n) :=
  hCoeff

/--
Bridge theorem for L-zero localization from modular candidates.
Both directions are hypothesis-driven at this scaffold stage.
-/
theorem modular_spiral_locates_L_zeros
    (L : LFunctionLike) (f : ModularFormLike) (n : ℕ)
    (hForward : L.hasZeroAt n → ∃ c ∈ modularCandidateList f n, c.lValue = some 0)
    (hBackward : (∃ c ∈ modularCandidateList f n, c.lValue = some 0) → L.hasZeroAt n) :
    L.hasZeroAt n ↔ ∃ c ∈ modularCandidateList f n, c.lValue = some 0 :=
  ⟨hForward, hBackward⟩

/-- CSV row for modular candidates (base candidate row + mode index). -/
def modularCandidateToCSV (c : ModularCandidate) : String :=
  candidateToCSV c.toCandidate ++ "," ++ toString c.fourierMode

/-- Parse modular candidate rows using the base candidate parser. -/
def parseModularCandidate (s : String) : Option ModularCandidate := do
  match s.splitOn "," with
  | [stepS, seedS, arcS, derivedS, modeS] =>
      let base ← parsePythonCandidate s!"{stepS},{seedS},{arcS},{derivedS}"
      let mode ← String.toNat? modeS
      pure
        { toCandidate := base
          tau := upperHalfFromArc base.arcParam
          fourierMode := mode
          lValue := none }
  | _ => none

/--
Roundtrip contract for modular CSV under explicit parser hypotheses.
This mirrors the base-candidate codec style.
-/
theorem modular_candidate_csv_roundtrip
    (c : ModularCandidate)
    (hRound :
      parseModularCandidate (modularCandidateToCSV c) =
        some { toCandidate := c.toCandidate
               tau := upperHalfFromArc c.arcParam
               fourierMode := c.fourierMode
               lValue := none }) :
    parseModularCandidate (modularCandidateToCSV c) =
      some { toCandidate := c.toCandidate
             tau := upperHalfFromArc c.arcParam
             fourierMode := c.fourierMode
             lValue := none } :=
  hRound

/-! ## SAT bridge -/

open Hqiv.Logic

/-- SAT specialization of a geometric candidate. -/
structure SATCandidate (n : ℕ) extends Candidate where
  assignmentCode : ℕ
  satisfiedClauses : Finset ℕ

/-- Deterministic bit code from geometric indices (scaffold assignment channel). -/
def satAssignmentCode (c : Candidate) : ℕ :=
  c.step + c.seedIdx.1

/--
Decode an assignment code into Boolean variable values (DIMACS-style bit channel):
variable `i` is true iff bit `i` of `code` is set.
-/
def assignmentFromCode {n : ℕ} (code : ℕ) : Assignment n :=
  fun v => decide (((code / (2 ^ v.1)) % 2) = 1)

/-- Exact satisfied-clause count under decoded assignment semantics. -/
def satSatisfiedClauseCountExact {n : ℕ} (φ : CNFFormula n) (code : ℕ) : ℕ :=
  φ.clauses.foldl
    (fun acc c => acc + (if Clause.eval (assignmentFromCode code) c = true then 1 else 0))
    0

/-- Exact SAT witness predicate aligned with `CNFFormula.eval` semantics. -/
def isExactSATWitness {n : ℕ} (φ : CNFFormula n) (c : SATCandidate n) : Prop :=
  CNFFormula.eval (assignmentFromCode c.assignmentCode) φ = true

/--
If the decoded assignment is an exact SAT witness, then the exact satisfied-clause
count equals the total number of clauses.
-/
theorem sat_exact_count_eq_length_of_witness
    {n : ℕ} (φ : CNFFormula n) (code : ℕ)
    (hWitness : CNFFormula.eval (assignmentFromCode code) φ = true) :
    satSatisfiedClauseCountExact φ code = φ.clauses.length := by
  let a : Assignment n := assignmentFromCode code
  have hAll : φ.clauses.all (fun c => Clause.eval a c) = true := by
    simpa [CNFFormula.eval, a] using hWitness
  have hForall : ∀ x ∈ φ.clauses, Clause.eval a x = true := by
    simpa using List.all_eq_true.mp hAll
  have hList :
      ∀ cs : List (Clause n),
        ∀ acc : ℕ,
          (∀ x ∈ cs, Clause.eval a x = true) →
            cs.foldl
                (fun acc c => acc + (if Clause.eval a c = true then 1 else 0))
                acc = acc + cs.length := by
    intro cs
    induction cs with
    | nil =>
      intro acc _
      simp
    | cons c cs ih =>
      intro acc h
      have hc : Clause.eval a c = true := h c (by simp)
      have htail : ∀ x ∈ cs, Clause.eval a x = true := by
        intro x hx
        exact h x (by simp [hx])
      specialize ih (acc + 1) htail
      calc
        (c :: cs).foldl
            (fun acc c => acc + (if Clause.eval a c = true then 1 else 0))
            acc
            = cs.foldl
                (fun acc c => acc + (if Clause.eval a c = true then 1 else 0))
                (acc + 1) := by
                  simp [List.foldl, hc]
        _ = (acc + 1) + cs.length := ih
        _ = acc + (c :: cs).length := by
              simp [Nat.add_assoc, Nat.add_comm]
  simpa [satSatisfiedClauseCountExact, a] using hList φ.clauses 0 hForall

/--
If exact satisfied-clause count reaches clause-list length, then the decoded
assignment is an exact SAT witness.
-/
theorem sat_exact_witness_of_count_eq_length
    {n : ℕ} (φ : CNFFormula n) (code : ℕ)
    (hCount : satSatisfiedClauseCountExact φ code = φ.clauses.length) :
    CNFFormula.eval (assignmentFromCode code) φ = true := by
  let a : Assignment n := assignmentFromCode code
  let f : ℕ → Clause n → ℕ :=
    fun acc c => acc + (if Clause.eval a c = true then 1 else 0)
  have hCountLe :
      ∀ cs : List (Clause n), ∀ acc : ℕ, cs.foldl f acc ≤ acc + cs.length := by
    intro cs
    induction cs with
    | nil =>
      intro acc
      simp [f]
    | cons c cs ih =>
      intro acc
      have hStep : f acc c ≤ acc + 1 := by
        by_cases hc : Clause.eval a c = true
        · simp [f, hc]
        · simp [f, hc]
      have hTail : cs.foldl f (f acc c) ≤ (f acc c) + cs.length := ih (f acc c)
      calc
        (c :: cs).foldl f acc = cs.foldl f (f acc c) := by simp [List.foldl]
        _ ≤ (f acc c) + cs.length := hTail
        _ ≤ (acc + 1) + cs.length := Nat.add_le_add_right hStep cs.length
        _ = acc + (c :: cs).length := by
              simp [Nat.add_assoc, Nat.add_comm]
  have hAllFromEq :
      ∀ cs : List (Clause n), ∀ acc : ℕ,
        cs.foldl f acc = acc + cs.length →
          cs.all (fun c => Clause.eval a c) = true := by
    intro cs
    induction cs with
    | nil =>
      intro acc hEq
      simp at hEq
      simp
    | cons c cs ih =>
      intro acc hEq
      by_cases hc : Clause.eval a c = true
      · have hTailEq : cs.foldl f (acc + 1) = (acc + 1) + cs.length := by
          simpa [f, hc, Nat.add_assoc, Nat.add_comm] using hEq
        have hTailAll : cs.all (fun c => Clause.eval a c) = true := ih (acc + 1) hTailEq
        simp [List.all, hc, hTailAll]
      · have hEqFalse : cs.foldl f acc = acc + (c :: cs).length := by
          simpa [f, hc] using hEq
        have hLe : cs.foldl f acc ≤ acc + cs.length := hCountLe cs acc
        have hNotLe : ¬ (acc + (c :: cs).length ≤ acc + cs.length) := by
          simp
        have : acc + (c :: cs).length ≤ acc + cs.length := by
          exact hEqFalse ▸ hLe
        exact False.elim (hNotLe this)
  have hAll : φ.clauses.all (fun c => Clause.eval a c) = true := by
    simpa [satSatisfiedClauseCountExact, a, f] using hAllFromEq φ.clauses 0 (by simpa [satSatisfiedClauseCountExact, a, f] using hCount)
  simpa [CNFFormula.eval, a] using hAll

/--
Exact witness/count correspondence, fully constructive in both directions.
-/
theorem sat_exact_witness_iff_count_eq_length
    {n : ℕ} (φ : CNFFormula n) (c : SATCandidate n) :
    isExactSATWitness φ c ↔
      satSatisfiedClauseCountExact φ c.assignmentCode = φ.clauses.length := by
  constructor
  · intro hWitness
    exact sat_exact_count_eq_length_of_witness φ c.assignmentCode hWitness
  · intro hCount
    exact sat_exact_witness_of_count_eq_length φ c.assignmentCode hCount

/-- SAT candidate stream for a CNF instance with `n` variables. -/
def satCandidateList {n : ℕ} (_φ : CNFFormula n) : List (SATCandidate n) :=
  (candidateListWithSymmetricTip n).map (fun c =>
    { toCandidate := c
      assignmentCode := satAssignmentCode c
      satisfiedClauses := ∅ })

/--
Geometric SAT bridge in honest-bridge form: satisfiability is equivalent to the
existence of a candidate with full clause coverage, provided each direction is
supplied as an explicit hypothesis.
-/
theorem geometric_spiral_solves_sat
    {n : ℕ} (φ : CNFFormula n)
    (hForward :
      CNFFormula.Satisfiable φ →
        ∃ c ∈ satCandidateList φ, c.satisfiedClauses.card = φ.clauses.length)
    (hBackward :
      (∃ c ∈ satCandidateList φ, c.satisfiedClauses.card = φ.clauses.length) →
        CNFFormula.Satisfiable φ) :
    CNFFormula.Satisfiable φ ↔
      ∃ c ∈ satCandidateList φ, c.satisfiedClauses.card = φ.clauses.length :=
  ⟨hForward, hBackward⟩

/--
Exact SAT bridge: satisfiability is equivalent to existence of a candidate whose
decoded assignment satisfies the CNF formula exactly.
-/
theorem geometric_spiral_solves_sat_exact
    {n : ℕ} (φ : CNFFormula n)
    (hForward :
      CNFFormula.Satisfiable φ →
        ∃ c ∈ satCandidateList φ, isExactSATWitness φ c)
    (hBackward :
      (∃ c ∈ satCandidateList φ, isExactSATWitness φ c) →
        CNFFormula.Satisfiable φ) :
    CNFFormula.Satisfiable φ ↔
      ∃ c ∈ satCandidateList φ, isExactSATWitness φ c :=
  ⟨hForward, hBackward⟩

/-- CSV row for SAT candidates (base candidate row + assignment code). -/
def satCandidateToCSV {n : ℕ} (c : SATCandidate n) : String :=
  candidateToCSV c.toCandidate ++ "," ++ toString c.assignmentCode

/-- Parse SAT candidate rows using the base candidate parser. -/
def parseSATCandidate {n : ℕ} (s : String) : Option (SATCandidate n) := do
  match s.splitOn "," with
  | [stepS, seedS, arcS, derivedS, assignS] =>
      let base ← parsePythonCandidate s!"{stepS},{seedS},{arcS},{derivedS}"
      let assignmentCode ← String.toNat? assignS
      pure
        { toCandidate := base
          assignmentCode := assignmentCode
          satisfiedClauses := ∅ }
  | _ => none

/--
Roundtrip contract for SAT CSV under explicit parser hypotheses.
-/
theorem sat_candidate_csv_roundtrip
    {n : ℕ} (c : SATCandidate n)
    (hRound :
      parseSATCandidate (n := n) (satCandidateToCSV (n := n) c) =
        some { toCandidate := c.toCandidate
               assignmentCode := c.assignmentCode
               satisfiedClauses := (∅ : Finset ℕ) }) :
    parseSATCandidate (n := n) (satCandidateToCSV (n := n) c) =
      some { toCandidate := c.toCandidate
             assignmentCode := c.assignmentCode
             satisfiedClauses := (∅ : Finset ℕ) } :=
  hRound

end

end Hqiv.Geometry

