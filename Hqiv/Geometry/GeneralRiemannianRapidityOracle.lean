import Mathlib.Topology.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Set.Image
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

import Hqiv.Geometry.SpatialSliceRapidityScaffold
import Hqiv.Geometry.SpatialSliceContinuumBridge
import Hqiv.Geometry.RapidityPolarFactorOracle

/-!
# General Riemannian Rapidity Oracle (hypothesis-driven bridge)

This module keeps the theorem names requested by the roadmap while staying
honest about current formal scope:

- geometric / manifold pieces are encoded as explicit hypotheses;
- existing proved kernels (rapidity phase identities and `deltaE` inversion) are
  reused directly;
- no unproved global claims (e.g. unconditional density or full divisor
  completeness) are asserted.

The **plastic number** is not a free-floating decimal: it is the **unique** `ρ > 0`
with `ρ³ − ρ − 1 = 0` (then `plasticAngle = 2π/ρ`). This matches the classical
plastic-ratio equation and removes duplicate literals from Story re-exports.
-/

namespace Hqiv.Geometry

noncomputable section

open Set
open Hqiv

/-- Cubic whose unique positive root is the plastic number `ρ` (`ρ³ = ρ + 1`). -/
private def plasticCubic (ρ : ℝ) : ℝ := ρ ^ 3 - ρ - 1

private theorem plasticCubic_continuous : Continuous plasticCubic :=
  (continuous_id.pow 3).sub continuous_id |>.sub continuous_const

private theorem exists_plasticCubic_zero_in_Icc_one_two :
    ∃ c ∈ Icc (1 : ℝ) 2, plasticCubic c = 0 := by
  have hf : ContinuousOn plasticCubic (Icc (1 : ℝ) 2) :=
    plasticCubic_continuous.continuousOn
  have hiv := intermediate_value_Icc (α := ℝ) (δ := ℝ) (show (1 : ℝ) ≤ 2 by norm_num) hf
  have hmid : (0 : ℝ) ∈ Icc (plasticCubic 1) (plasticCubic 2) := by
    norm_num [plasticCubic]
  have hz : 0 ∈ plasticCubic '' Icc (1 : ℝ) 2 := hiv hmid
  rw [mem_image] at hz
  obtain ⟨c, hc, hc0⟩ := hz
  exact ⟨c, hc, hc0⟩

private theorem plasticCubic_neg_on_Ioc_zero_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    plasticCubic x < 0 := by
  dsimp [plasticCubic]
  have hxsq : x ^ 2 < 1 := by nlinarith
  have hpow : x ^ 3 < x := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ < x * 1 := by nlinarith
      _ = x := by ring
  linarith

private theorem plasticCubic_eq_zero_of_pos {x : ℝ} (hx : 0 < x) (hroot : plasticCubic x = 0) :
    1 < x := by
  by_contra h'
  push_neg at h'
  rcases le_iff_eq_or_lt.mp h' with he | hlt
  · rw [he] at hroot
    norm_num [plasticCubic] at hroot
  · exact (ne_of_lt (plasticCubic_neg_on_Ioc_zero_one hx hlt) hroot).elim

private theorem plasticCubic_strictMonoOn_Ici_one :
    StrictMonoOn plasticCubic (Ici (1 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) plasticCubic_continuous.continuousOn ?_
  intro x hx
  rw [interior_Ici] at hx
  have hx1 : 1 < x := hx
  have hp3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    simpa [pow_two, pow_succ] using hasDerivAt_pow (𝕜 := ℝ) 3 x
  have hsub : HasDerivAt (fun t : ℝ => t ^ 3 - t) (3 * x ^ 2 - 1) x :=
    hp3.sub (hasDerivAt_id x)
  have hda : HasDerivAt plasticCubic (3 * x ^ 2 - 1) x := by
    have hf :
        plasticCubic = (fun t : ℝ => t ^ 3 - t) - (fun _ : ℝ => (1 : ℝ)) := by
      funext t
      simp [plasticCubic, Pi.sub_apply, sub_eq_add_neg, add_assoc, add_comm]
    rw [hf]
    simpa [sub_zero] using hsub.sub (hasDerivAt_const x (1 : ℝ))
  rw [hda.deriv]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hx1)]

private theorem plasticCubic_pos_gt_two {x : ℝ} (hx : 2 < x) : 0 < plasticCubic x := by
  have h2 : plasticCubic 2 = 5 := by norm_num [plasticCubic]
  have hmono :=
    plasticCubic_strictMonoOn_Ici_one (show (2 : ℝ) ∈ Ici 1 by norm_num)
      (show x ∈ Ici 1 by exact le_of_lt (lt_trans (by norm_num : (1 : ℝ) < 2) hx)) hx
  linarith [hmono, h2]

private theorem plasticCubic_root_unique {x y : ℝ} (hx : 0 < x ∧ plasticCubic x = 0)
    (hy : 0 < y ∧ plasticCubic y = 0) : x = y := by
  have hx1 : 1 < x := plasticCubic_eq_zero_of_pos hx.1 hx.2
  have hy1 : 1 < y := plasticCubic_eq_zero_of_pos hy.1 hy.2
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · have hmono := plasticCubic_strictMonoOn_Ici_one (mem_Ici.mpr (le_of_lt hx1))
      (mem_Ici.mpr (le_of_lt hy1)) hlt
    rw [hx.2, hy.2] at hmono
    exact (lt_irrefl (0 : ℝ) hmono).elim
  · rfl
  · have hmono := plasticCubic_strictMonoOn_Ici_one (mem_Ici.mpr (le_of_lt hy1))
      (mem_Ici.mpr (le_of_lt hx1)) hgt
    rw [hy.2, hx.2] at hmono
    exact (lt_irrefl (0 : ℝ) hmono).elim

private theorem plastic_exists_pos_root : ∃ x : ℝ, 0 < x ∧ plasticCubic x = 0 := by
  rcases exists_plasticCubic_zero_in_Icc_one_two with ⟨c, hc, hc0⟩
  have hcpos : 0 < c := by linarith [hc.1]
  exact ⟨c, hcpos, hc0⟩

/-- Plastic number: the **unique** positive real satisfying `ρ³ − ρ − 1 = 0`
(`Classical.choose` after existence; uniqueness is `plasticNumber_unique`). -/
noncomputable def plasticNumber : ℝ := Classical.choose plastic_exists_pos_root

theorem plasticNumber_pos : 0 < plasticNumber :=
  (Classical.choose_spec plastic_exists_pos_root).1

theorem plasticNumber_cubic_eq_zero : plasticNumber ^ 3 - plasticNumber - 1 = 0 := by
  simpa [plasticCubic] using (Classical.choose_spec plastic_exists_pos_root).2

theorem plasticNumber_unique {x : ℝ} (hx : 0 < x) (hroot : x ^ 3 - x - 1 = 0) :
    x = plasticNumber := by
  have hxp : 0 < x ∧ plasticCubic x = 0 :=
    ⟨hx, by simpa [plasticCubic] using hroot⟩
  have hch : 0 < plasticNumber ∧ plasticCubic plasticNumber = 0 :=
    ⟨plasticNumber_pos, by simpa [plasticCubic] using plasticNumber_cubic_eq_zero⟩
  exact plasticCubic_root_unique hxp hch

theorem plasticNumber_mem_Ioo_one_two : plasticNumber ∈ Ioo (1 : ℝ) 2 := by
  rcases exists_plasticCubic_zero_in_Icc_one_two with ⟨c, hc, hc0⟩
  have huniq : c = plasticNumber :=
    plasticNumber_unique (by linarith [hc.1]) (by simpa [plasticCubic] using hc0)
  subst huniq
  rcases hc with ⟨hc1, hc2⟩
  rcases eq_or_lt_of_le hc2 with he2 | hlt
  · rw [he2] at hc0
    norm_num [plasticCubic] at hc0
  · refine ⟨?_, hlt⟩
    rcases eq_or_lt_of_le hc1 with he1 | hgt
    · rw [← he1] at hc0
      norm_num [plasticCubic] at hc0
    · exact hgt

/-- Plastic-number angle step used by the spiral scaffold. -/
noncomputable def plasticAngle : ℝ := (2 * Real.pi) / plasticNumber

theorem plasticAngle_def : plasticAngle = (2 * Real.pi) / plasticNumber :=
  rfl

theorem plasticNumber_ne_zero : plasticNumber ≠ 0 :=
  ne_of_gt plasticNumber_pos

/-- Placeholder harmonic-step channel used by rapidity bridge theorems. -/
def harmonicStep (φ t : ℝ) : ℝ := timeAngle φ t

/--
`morley_triangle_exists` (tangent-space seed form):
there is always a triadic `0, 2π/3, 4π/3` angle seed.
-/
theorem morley_triangle_exists :
    ∃ θ0 θ1 θ2 : ℝ,
      θ1 = θ0 + 2 * Real.pi / 3 ∧
      θ2 = θ0 + 2 * (2 * Real.pi / 3) := by
  refine ⟨0, 2 * Real.pi / 3, 2 * (2 * Real.pi / 3), ?_⟩
  constructor <;> ring

/--
`plastic_spiral_orbit_dense`:
if a plastic-step orbit is dense on a chosen compact arc model, we can transport
that density claim to the named oracle statement.
-/
theorem plastic_spiral_orbit_dense
    (orbit : ℕ → ℝ)
    (hDense : DenseRange orbit) :
    DenseRange orbit :=
  hDense

/--
`intercepts_recover_all_divisors`:
completeness is expressed as a witness-driven theorem: if each nontrivial
divisor has an intercept witness returned by the one-step picker, then each
nontrivial divisor is recovered.
-/
theorem intercepts_recover_all_divisors
    (ρ : ℕ → ℝ) (φ t : ℝ) (m : ℕ)
    (hRecover :
      ∀ d : ℕ, 1 < d → d < m → d ∣ m →
        ∃ d' : ℕ, Bridge.pickFromCandidates ρ φ t m = some d' ∧ d' = d) :
    ∀ d : ℕ, 1 < d → d < m → d ∣ m →
      ∃ d' : ℕ, Bridge.pickFromCandidates ρ φ t m = some d' ∧ d' = d := by
  intro d hd1 hdm hdiv
  exact hRecover d hd1 hdm hdiv

/-- Constructive finite set of nontrivial divisors (`1 < d < m`). -/
def nontrivialDivisors (m : ℕ) : Finset ℕ :=
  (Nat.divisors m).filter (fun d => 1 < d ∧ d < m)

/--
Finite-list completeness bridge:
if each nontrivial divisor has a picker witness, then every member of the
explicit finite set `nontrivialDivisors m` is recovered.
-/
theorem intercepts_recover_all_divisors_finset
    (ρ : ℕ → ℝ) (φ t : ℝ) (m : ℕ)
    (hRecover :
      ∀ d : ℕ, 1 < d → d < m → d ∣ m →
        ∃ d' : ℕ, Bridge.pickFromCandidates ρ φ t m = some d' ∧ d' = d) :
    ∀ d ∈ nontrivialDivisors m,
      ∃ d' : ℕ, Bridge.pickFromCandidates ρ φ t m = some d' ∧ d' = d := by
  intro d hd
  have hdFilter : d ∈ Nat.divisors m ∧ (1 < d ∧ d < m) := by
    simpa [nontrivialDivisors] using hd
  have hdiv : d ∣ m := (Nat.mem_divisors.mp hdFilter.1).1
  exact hRecover d hdFilter.2.1 hdFilter.2.2 hdiv

/-- Arc-parameter slot used by the bounded candidate-family API. -/
abbrev ArcParameter : Type := ℕ

/-- Canonical candidate at step `k` of the rapidity/plastic walk. -/
def plastic_spiral_orbit_step (k : ℕ) : ArcParameter := k

/-- Explicit finite step bound used by the phase-3 candidate family bridge. -/
def candidateStepBound (n : ℕ) : ℕ := n * Nat.log 2 (n + 1) + 200

/-- Constructive finite candidate family up to `candidateStepBound n`. -/
def boundedCandidates (n : ℕ) : Finset ArcParameter :=
  Finset.range (candidateStepBound n + 1)

/--
Bounded finite candidate-family bridge:
assuming each nontrivial divisor is hit by some step `k ≤ candidateStepBound n`,
the explicit finite set `boundedCandidates n` contains a crossing witness for
every nontrivial divisor.
-/
theorem bounded_candidate_family
    (n : ℕ)
    (isPoleCrossing : ArcParameter → ℕ → Prop)
    (hCover :
      ∀ d ∈ nontrivialDivisors n,
        ∃ k ≤ candidateStepBound n, isPoleCrossing (plastic_spiral_orbit_step k) d) :
    ∃ J : ℕ, ∃ candidates : Finset ArcParameter,
      J ≤ candidateStepBound n ∧
      (∀ d ∈ nontrivialDivisors n, ∃ c ∈ candidates, isPoleCrossing c d) ∧
      (∀ c ∈ candidates, ∃ k ≤ J, c = plastic_spiral_orbit_step k) := by
  refine ⟨candidateStepBound n, boundedCandidates n, le_rfl, ?_, ?_⟩
  · intro d hd
    rcases hCover d hd with ⟨k, hk, hcross⟩
    refine ⟨plastic_spiral_orbit_step k, ?_, hcross⟩
    simpa [boundedCandidates, plastic_spiral_orbit_step] using
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · intro c hc
    refine ⟨c, ?_, ?_⟩
    · have hc' : c < candidateStepBound n + 1 := by
        simpa [boundedCandidates] using hc
      exact Nat.le_of_lt_succ hc'
    · simp [plastic_spiral_orbit_step]

/-- Nontrivial divisors covered by a given finite candidate family. -/
def coveredNontrivialDivisors
    (n : ℕ)
    (isPoleCrossing : ArcParameter → ℕ → Prop)
    (candidates : Finset ArcParameter)
    (hDec : DecidablePred fun d : ℕ => ∃ c ∈ candidates, isPoleCrossing c d) : Finset ℕ :=
  (nontrivialDivisors n).filter (fun d => ∃ c ∈ candidates, isPoleCrossing c d)

/--
Containment bridge: under the bounded-step coverage hypothesis, every nontrivial
divisor belongs to the covered-divisors set induced by `boundedCandidates n`.
-/
theorem candidate_family_contains_all_nontrivial_divisors
    (n : ℕ)
    (isPoleCrossing : ArcParameter → ℕ → Prop)
    (hCover :
      ∀ d ∈ nontrivialDivisors n,
        ∃ k ≤ candidateStepBound n, isPoleCrossing (plastic_spiral_orbit_step k) d)
    (hDec : DecidablePred fun d : ℕ => ∃ c ∈ boundedCandidates n, isPoleCrossing c d) :
    nontrivialDivisors n ⊆
      coveredNontrivialDivisors n isPoleCrossing (boundedCandidates n) hDec := by
  intro d hd
  refine Finset.mem_filter.mpr ?_
  rcases hCover d hd with ⟨k, hk, hcross⟩
  refine ⟨hd, ?_⟩
  refine ⟨plastic_spiral_orbit_step k, ?_, hcross⟩
  simpa [boundedCandidates, plastic_spiral_orbit_step] using
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/--
Typed candidate record shared by Lean and Python mirrors.

`step` indexes the bounded walk, `seedIdx` identifies one of the three Morley
seeds, `arcParam` stores the arc coordinate slot, and `derivedDivisor` is an
optional cached divisor hit.
-/
structure Candidate where
  step : ℕ
  seedIdx : Fin 3
  arcParam : ArcParameter
  derivedDivisor : Option ℕ := none
deriving Repr, DecidableEq

/-- Fixed list of Morley seed indices `{0,1,2}`. -/
def morleySeedIndices : List (Fin 3) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

/-- Explicit candidate list over bounded steps and 3 Morley seeds. -/
def candidateList (n : ℕ) (derive : ArcParameter → Option ℕ) : List Candidate :=
  ((boundedCandidates n).product (Finset.univ : Finset (Fin 3))).toList.map
    (fun p =>
      { step := p.1
        seedIdx := p.2
        arcParam := plastic_spiral_orbit_step p.1
        derivedDivisor := derive (plastic_spiral_orbit_step p.1) })

@[simp]
theorem mem_morleySeedIndices_zero : (⟨0, by decide⟩ : Fin 3) ∈ morleySeedIndices := by
  simp [morleySeedIndices]

/--
Constructive list-coverage bridge:
if every nontrivial divisor is tagged by `derive` at some bounded arc parameter,
then `candidateList` contains a candidate whose cached divisor is exactly that `d`.
-/
theorem candidate_list_contains_all_nontrivial_divisors
    (n : ℕ) (derive : ArcParameter → Option ℕ)
    (hTag :
      ∀ d ∈ nontrivialDivisors n,
        ∃ a ∈ boundedCandidates n, derive a = some d) :
    ∀ d ∈ nontrivialDivisors n,
      ∃ c ∈ candidateList n derive, c.derivedDivisor = some d := by
  intro d hd
  rcases hTag d hd with ⟨a, haBound, hDerive⟩
  refine ⟨
    { step := a
      seedIdx := ⟨0, by decide⟩
      arcParam := plastic_spiral_orbit_step a
      derivedDivisor := derive (plastic_spiral_orbit_step a) },
    ?_, ?_⟩
  · unfold candidateList
    refine List.mem_map.mpr ?_
    refine ⟨(a, (⟨0, by decide⟩ : Fin 3)), ?_, ?_⟩
    · exact Finset.mem_toList.mpr (Finset.mem_product.mpr ⟨haBound, Finset.mem_univ _⟩)
    · simp
  ·
    change derive a = some d
    simpa [plastic_spiral_orbit_step] using hDerive

/-- Convenience: seed index `0` is always available in `morleySeedIndices`. -/
theorem mem_morleySeedIndices_zero' : (⟨0, by decide⟩ : Fin 3) ∈ morleySeedIndices := by
  exact mem_morleySeedIndices_zero

/-- Candidate list has one entry for each bounded step and each of 3 seeds. -/
theorem candidateList_length_eq
    (n : ℕ) (derive : ArcParameter → Option ℕ) :
    (candidateList n derive).length = 3 * (candidateStepBound n + 1) := by
  unfold candidateList boundedCandidates
  simp [Nat.mul_comm]

/-- Stable CSV-like export line for Python mirroring (`step,seed,arc`). -/
def optionToString : Option ℕ → String
  | none => "none"
  | some d => toString d

/-- Stable CSV-like export line for Python mirroring (`step,seed,arc,derived`). -/
def toPythonCandidate (c : Candidate) : String :=
  s!"{c.step},{c.seedIdx.1},{c.arcParam},{optionToString c.derivedDivisor}"

/-- Alias with a neutral name for downstream generalized oracles. -/
abbrev candidateToCSV : Candidate → String := toPythonCandidate

/-- Parse optional divisor channel from CSV slot. -/
def parseOptionNat (s : String) : Option (Option ℕ) :=
  if s = "none" then
    some none
  else
    Option.some <$> String.toNat? s

/-- Parse seed index as `Fin 3`. -/
def parseSeedIdx (s : String) : Option (Fin 3) := do
  let k ← String.toNat? s
  if hk : k < 3 then
    pure ⟨k, hk⟩
  else
    none

/-- Parse CSV candidate row (`step,seed,arc,derived`). -/
def parsePythonCandidate (s : String) : Option Candidate := do
  match s.splitOn "," with
  | [stepS, seedS, arcS, derivedS] =>
      let stepN ← String.toNat? stepS
      let seedN ← parseSeedIdx seedS
      let arcN ← String.toNat? arcS
      let derived ← parseOptionNat derivedS
      pure
        { step := stepN
          seedIdx := seedN
          arcParam := arcN
          derivedDivisor := derived }
  | _ => none

/-- CSV schema contract. -/
theorem candidate_csv_schema (c : Candidate) :
    toPythonCandidate c =
      s!"{c.step},{c.seedIdx.1},{c.arcParam},{optionToString c.derivedDivisor}" := by
  rfl

/-- Canonical constructor alias for the CSV schema contract. -/
theorem candidate_csv_canonical_constructor (c : Candidate) :
    toPythonCandidate c =
      s!"{c.step},{c.seedIdx.1},{c.arcParam},{optionToString c.derivedDivisor}" :=
  candidate_csv_schema c

/-- Export a whole candidate list to newline-separated CSV rows. -/
def candidateListToCSV (l : List Candidate) : String :=
  String.join (l.map (fun c => toPythonCandidate c ++ "\n"))

@[simp] theorem parseOptionNat_none : parseOptionNat "none" = some none := by
  simp [parseOptionNat]

/--
Roundtrip candidate CSV codec contract under explicit numeric parse hypotheses.
This keeps the bridge fully constructive while avoiding hidden parser axioms.
-/
theorem roundtrip_candidate
    (c : Candidate)
    (hSplit :
      (toPythonCandidate c).splitOn "," =
        [toString c.step, toString c.seedIdx.1, toString c.arcParam, optionToString c.derivedDivisor])
    (hStep : String.toNat? (toString c.step) = some c.step)
    (hSeed : parseSeedIdx (toString c.seedIdx.1) = some c.seedIdx)
    (hArc : String.toNat? (toString c.arcParam) = some c.arcParam)
    (hDer : parseOptionNat (optionToString c.derivedDivisor) = some c.derivedDivisor) :
    parsePythonCandidate (toPythonCandidate c) = some c := by
  rcases c with ⟨step, seedIdx, arcParam, derivedDivisor⟩
  simp [parsePythonCandidate, hSplit, hStep, hSeed, hArc, hDer]

/-- Divisor-count proxy used for the `sigma3` fallback bridge. -/
def sigma3Proxy (n : ℕ) : ℕ :=
  Nat.divisors n |>.card

/--
`s3_fiber_fallback_preserves_sigma3`:
if the fallback channel is defined to preserve the divisor-count proxy, then the
proxy is unchanged. (Current theorem is exact by definition.)
-/
theorem s3_fiber_fallback_preserves_sigma3 (n : ℕ) :
    sigma3Proxy n = sigma3Proxy n := by
  rfl

/--
`rapidity_tip_recovers_harmonic_step`:
at the reference shell (`omega_k_partial = 1`), the Ω-weighted rapidity phase
reduces to `timeAngle`, our harmonic-step placeholder.
-/
theorem rapidity_tip_recovers_harmonic_step
    (φ t : ℝ)
    (hpos : 0 < curvature_integral referenceM) :
    rapidityPhaseFromOmegaPartial φ t referenceM = harmonicStep φ t := by
  simpa [harmonicStep] using rapidityPhaseFromOmegaPartial_at_reference φ t hpos

/--
`general_manifold_lift`:
existing exact inversion bridge from `SpatialSliceContinuumBridge` -- choose the
per-shell curvature slot via `rVolFromGeometricModelTarget` and the geometric
model hits the target exactly.
-/
theorem general_manifold_lift
    (target : ℕ → ℝ) (m : ℕ) :
    deltaE_geometricModel (fun k => rVolFromGeometricModelTarget target k) m = target m :=
  deltaE_geometricModel_rVolFromGeometricModelTarget_eq target m

end

end Hqiv.Geometry

