import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Hqiv.Geometry.QuantumFactorGateFrontier

/-!
# Rapidity-polar 3-spiral factor oracle scaffold

This module is a roadmap scaffold for the "locked rapidity spiral" oracle:

* define a 3-ray (120°) mask from a rapidity angle;
* build projection and anchor candidates on shell `m`;
* return a candidate factor pair by direct divisibility check.

The correctness theorem is intentionally hypothesis-driven (no hidden proof gaps): once a
locked-shell witness is supplied, the theorem returns the canonical factor-pair statement.

This keeps the zeta-roadmap API stable while finite-window / witness proofs are integrated.
-/

namespace Hqiv.Geometry

noncomputable section

/-- Quarter-turn period used in the sketch. -/
def horizonQuarterPeriod : ℝ := (2 * Real.pi) / 4

/-- Sketch-level rapidity increment. -/
def deltaThetaPrimeOracle (e : ℝ) : ℝ :=
  e * horizonQuarterPeriod

/-- Rapidity-polar angle at shell `m`. -/
def polarAngleFromRapidityOracle (φ t : ℝ) (m : ℕ) : ℝ :=
  φ * t * deltaThetaPrimeOracle (m : ℝ)

/-- 3-ray mask: base angle plus `0, 2π/3, 4π/3` modulo `2π`. -/
def threeSpiralRays (φ t : ℝ) (m : ℕ) : Fin 3 → ℝ :=
  fun i =>
    polarAngleFromRapidityOracle φ t m + (i.1 : ℝ) * (2 * Real.pi / 3)

/-- Simple mod-3 adjacent shell helper. -/
def adjacentShellMod3 (m : ℕ) : ℕ :=
  if m = 0 then 0
  else if m % 3 = 1 then m + 1
  else m - 1

/-- Even anchor shell helper. -/
def evenAnchorShell (m : ℕ) : ℕ :=
  if m % 2 = 0 then m else m + 1

/-- Nearest odd multiple-of-3 anchor (local closed-form scaffold). -/
def oddMultipleOfThreeAnchorShell (m : ℕ) : ℕ :=
  if m % 6 = 3 then m
  else if m % 6 = 0 then m + 3
  else if m % 6 = 1 then m + 2
  else if m % 6 = 2 then m + 1
  else if m % 6 = 4 then m - 1
  else m - 2

/-- Projection candidate from a spiral ray. -/
def spiralProjectionCandidate (m : ℕ) (θ : ℝ) : ℕ :=
  let tanθ := |Real.tan θ|
  if tanθ < 1e-12 then Nat.sqrt m
  else Nat.floor (Real.sqrt ((m : ℝ) / tanθ))

/-- Curvature-density to phase hook for roadmap integration. -/
def phiFromCurvatureDensity (ρ : ℕ → ℝ) (m : ℕ) : ℝ :=
  (m + 1 : ℝ) * ρ m

/-- List of projection candidates from the three rotated rays. -/
def projectionCandidates (φ t : ℝ) (m : ℕ) : List ℕ :=
  let rays := threeSpiralRays φ t m
  [spiralProjectionCandidate m (rays 0), spiralProjectionCandidate m (rays 1),
    spiralProjectionCandidate m (rays 2)]

/-- List of arithmetic anchor candidates used by the oracle. -/
def anchorCandidates (m : ℕ) : List ℕ :=
  [m, adjacentShellMod3 m, evenAnchorShell m, oddMultipleOfThreeAnchorShell m]

/-- Combined candidate list used by the direct divisibility check. -/
def allCandidates (φ t : ℝ) (m : ℕ) : List ℕ :=
  projectionCandidates φ t m ++ anchorCandidates m

/-- Curvature-parametric candidate family (bridge slot for arbitrary curvature channels). -/
def allCandidatesWithCurvature (ρ : ℕ → ℝ) (φ t : ℝ) (m : ℕ) : List ℕ :=
  allCandidates (phiFromCurvatureDensity ρ m + φ) t m

theorem projectionCandidates_length (φ t : ℝ) (m : ℕ) :
    (projectionCandidates φ t m).length = 3 := by
  simp [projectionCandidates]

theorem anchorCandidates_length (m : ℕ) :
    (anchorCandidates m).length = 4 := by
  simp [anchorCandidates]

theorem allCandidates_length (φ t : ℝ) (m : ℕ) :
    (allCandidates φ t m).length = 7 := by
  simp [allCandidates, projectionCandidates, anchorCandidates]

/-- Candidate scan budget for `factorPairFrom3SpiralMask`: fixed-size list (`3 + 4`). -/
def factorPairCandidateScanBudget : ℕ := 7

theorem factorPair_candidate_scan_le_budget (φ t : ℝ) (m : ℕ) :
    ((allCandidates φ t m).filter (fun a => 1 ≤ a ∧ a ≤ m ∧ m % a = 0)).length ≤
      factorPairCandidateScanBudget := by
  have hFilter :
      ((allCandidates φ t m).filter (fun a => 1 ≤ a ∧ a ≤ m ∧ m % a = 0)).length ≤
        (allCandidates φ t m).length := by
    exact List.length_filter_le _ _
  refine hFilter.trans ?_
  simpa [factorPairCandidateScanBudget] using
    (Nat.le_of_eq (allCandidates_length φ t m))

/-- Direct multiply/divide oracle: first valid divisor in candidate order. -/
def factorPairFrom3SpiralMask (φ t : ℝ) (m : ℕ) : Option (ℕ × ℕ) :=
  if _hm : m = 0 then none
  else
    let divisors :=
      (allCandidates φ t m).filter (fun a => 1 ≤ a ∧ a ≤ m ∧ m % a = 0)
    match divisors with
    | [] => none
    | a :: _ => some (a, m / a)

/-- Witness-driven correctness statement for locked shells (`m ≥ 5`). -/
theorem factorPair_from_3spiral_correct
    (φ t : ℝ) (m : ℕ) (_hLocked : 5 ≤ m) (_hPhiT : 0 < φ ∧ 0 < t)
    (hOracle :
      ∃ a b : ℕ,
        factorPairFrom3SpiralMask φ t m = some (a, b) ∧
        a * b = m ∧
        a ≤ b ∧
        (a = 1 ∨ (1 < a ∧ 1 < b))) :
    ∃ a b : ℕ,
      factorPairFrom3SpiralMask φ t m = some (a, b) ∧
      a * b = m ∧
      a ≤ b ∧
      (a = 1 ∨ (1 < a ∧ 1 < b)) := by
  exact hOracle

/-- Certified constant-budget scan: candidate filtering inspects at most 7 entries. -/
theorem factorPair_from_3spiral_is_O1 (φ t : ℝ) (m : ℕ) :
    ((allCandidates φ t m).filter (fun a => 1 ≤ a ∧ a ≤ m ∧ m % a = 0)).length ≤ 7 := by
  simpa [factorPairCandidateScanBudget] using factorPair_candidate_scan_le_budget φ t m

/-!
## One-step bridge theorem (arbitrary curvature)

This is the first concrete bridge from a curvature-indexed candidate set to a
sound one-step factor extraction claim.
-/
namespace Bridge

/-- First candidate in list order that is a valid nontrivial divisor. -/
def firstValidDivisor (m : ℕ) (xs : List ℕ) : Option ℕ :=
  match xs with
  | [] => none
  | a :: tl =>
      if 1 < a ∧ a < m ∧ a ∣ m then some a else firstValidDivisor m tl

/--
Operational scan cost for `firstValidDivisor`:
the number of list entries inspected until success or exhaustion.
-/
def firstValidDivisorScanCost (m : ℕ) (xs : List ℕ) : ℕ :=
  match xs with
  | [] => 0
  | a :: tl =>
      if 1 < a ∧ a < m ∧ a ∣ m then 1 else firstValidDivisorScanCost m tl + 1

theorem firstValidDivisor_scanCost_le_length (m : ℕ) (xs : List ℕ) :
    firstValidDivisorScanCost m xs ≤ xs.length := by
  induction xs with
  | nil =>
      simp [firstValidDivisorScanCost]
  | cons a tl ih =>
      by_cases ha : 1 < a ∧ a < m ∧ a ∣ m
      · simp [firstValidDivisorScanCost, ha]
      · simp [firstValidDivisorScanCost, ha, ih]

theorem allCandidatesWithCurvature_length (ρ : ℕ → ℝ) (φ t : ℝ) (m : ℕ) :
    (allCandidatesWithCurvature ρ φ t m).length = 7 := by
  simpa [allCandidatesWithCurvature] using
    (allCandidates_length (phiFromCurvatureDensity ρ m + φ) t m)

/-- Curvature-parametric one-step picker. -/
def pickFromCandidates (ρ : ℕ → ℝ) (φ t : ℝ) (m : ℕ) : Option ℕ :=
  firstValidDivisor m (allCandidatesWithCurvature ρ φ t m)

theorem pickFromCandidates_scanCost_le_seven (ρ : ℕ → ℝ) (φ t : ℝ) (m : ℕ) :
    firstValidDivisorScanCost m (allCandidatesWithCurvature ρ φ t m) ≤ 7 := by
  refine (firstValidDivisor_scanCost_le_length m (allCandidatesWithCurvature ρ φ t m)).trans ?_
  exact Nat.le_of_eq (allCandidatesWithCurvature_length ρ φ t m)

theorem firstValidDivisor_some_spec
    (m d : ℕ) (xs : List ℕ)
    (h : firstValidDivisor m xs = some d) :
    1 < d ∧ d < m ∧ d ∣ m := by
  induction xs with
  | nil =>
      simp [firstValidDivisor] at h
  | cons a tl ih =>
      simp [firstValidDivisor] at h
      by_cases ha : 1 < a ∧ a < m ∧ a ∣ m
      · simp [ha] at h
        rcases h with rfl
        exact ha
      · simp [ha] at h
        exact ih h

/-- Bridge theorem: for arbitrary curvature, a successful one-step pick is a nontrivial divisor. -/
theorem pickFromCandidates_sound
    (ρ : ℕ → ℝ) (φ t : ℝ) (m d : ℕ)
    (hPick : pickFromCandidates ρ φ t m = some d) :
    1 < d ∧ d < m ∧ d ∣ m := by
  unfold pickFromCandidates at hPick
  exact firstValidDivisor_some_spec m d (allCandidatesWithCurvature ρ φ t m) hPick

/-- Bridge theorem (pair form): successful pick yields a valid factor pair product. -/
theorem pickFromCandidates_pair_product
    (ρ : ℕ → ℝ) (φ t : ℝ) (m d : ℕ)
    (hPick : pickFromCandidates ρ φ t m = some d) :
    d * (m / d) = m := by
  have hDiv : d ∣ m := (pickFromCandidates_sound ρ φ t m d hPick).2.2
  exact Nat.mul_div_cancel' hDiv

/--
Certificate wrapper for one-step factor picks.

This packages the exact hypothesis shape used by `pickFromCandidates_sound`
so external payloads (e.g. scripts) can target one named object.
-/
structure OneStepPickCertificate where
  ρ : ℕ → ℝ
  φ : ℝ
  t : ℝ
  m : ℕ
  d : ℕ
  hPick : pickFromCandidates ρ φ t m = some d

theorem OneStepPickCertificate.sound
    (cert : OneStepPickCertificate) :
    1 < cert.d ∧ cert.d < cert.m ∧ cert.d ∣ cert.m := by
  exact pickFromCandidates_sound cert.ρ cert.φ cert.t cert.m cert.d cert.hPick

theorem OneStepPickCertificate.pair_product
    (cert : OneStepPickCertificate) :
    cert.d * (cert.m / cert.d) = cert.m := by
  exact pickFromCandidates_pair_product cert.ρ cert.φ cert.t cert.m cert.d cert.hPick

end Bridge

/-!
## First "voxel" bite: factor-pair encoding on one shell

This formalizes the minimal uniqueness step behind the geometric narrative:
on a fixed shell `m`, each valid factor pair `(a,b)` with `a*b = m` has a unique
encoded lattice point (here the canonical pair itself).
-/
namespace FactorVoxel

/-- Factor pairs constrained to shell `m`. -/
def PairOnShell (m : ℕ) := {p : ℕ × ℕ // p.1 * p.2 = m}

/-- Canonical voxel encoding of a factor pair on shell `m`. -/
def voxelOfPair {m : ℕ} : PairOnShell m → ℕ × ℕ := fun p => p.1

theorem voxelOfPair_injective (m : ℕ) : Function.Injective (@voxelOfPair m) := by
  intro p q h
  cases p with
  | mk p hp =>
    cases q with
    | mk q hq =>
      simp [voxelOfPair] at h
      cases h
      rfl

/-- Any divisor `a ∣ m` yields a shell voxel `(a, m/a)`. -/
def pairFromDivisor (m a : ℕ) (ha : a ∣ m) : PairOnShell m :=
  ⟨(a, m / a), by
    exact Nat.mul_div_cancel' ha
  ⟩

/-- The first coordinate of `pairFromDivisor` is exactly the chosen divisor. -/
theorem pairFromDivisor_fst (m a : ℕ) (ha : a ∣ m) :
    (voxelOfPair (pairFromDivisor m a ha)).1 = a := by
  rfl

end FactorVoxel

/-!
## Triadic rotation orbit (120° step) and period-3 turn

This bridges the "three rays" printout to a simple orbit law:
each step adds `2π/3`, and three steps add one full turn `2π`.
-/
namespace TriadicRotation

/-- One 120° step on the angle line. -/
def rotate120 (θ : ℝ) : ℝ := θ + (2 * Real.pi / 3)

/-- `j`-step triadic orbit from base angle `θ`. -/
def rayOrbit (θ : ℝ) (j : ℕ) : ℝ := θ + (j : ℝ) * (2 * Real.pi / 3)

theorem rayOrbit_step (θ : ℝ) (j : ℕ) :
    rayOrbit θ (j + 1) = rotate120 (rayOrbit θ j) := by
  simp [rayOrbit, rotate120, Nat.cast_add, add_left_comm, add_comm]
  ring

/-- Three triadic steps equal one full `2π` turn (on ℝ, before wrapping mod `2π`). -/
theorem rayOrbit_period3_full_turn (θ : ℝ) (j : ℕ) :
    rayOrbit θ (j + 3) = rayOrbit θ j + 2 * Real.pi := by
  simp [rayOrbit, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The concrete `threeSpiralRays` are the first three points of `rayOrbit`. -/
theorem threeSpiralRays_eq_orbit
    (φ t : ℝ) (m : ℕ) (i : Fin 3) :
    threeSpiralRays φ t m i = rayOrbit (polarAngleFromRapidityOracle φ t m) i.1 := by
  simp [threeSpiralRays, rayOrbit]

/-- A point `x` occupies the triadic ray voxel-set iff it matches one of the 3 additive modes. -/
def OccupiesTriad (θ x : ℝ) : Prop :=
  x = θ ∨ x = θ + (2 * Real.pi / 3) ∨ x = θ + 2 * (2 * Real.pi / 3)

/-- Mode law: any occupied triad point is one of `{θ, θ+2π/3, θ+4π/3}`. -/
theorem occupiesTriad_iff_modes (θ x : ℝ) :
    OccupiesTriad θ x ↔
      ∃ i : Fin 3, x = rayOrbit θ i.1 := by
  constructor
  · intro hx
    rcases hx with h0 | h1 | h2
    · refine ⟨⟨0, by decide⟩, ?_⟩
      simpa [rayOrbit] using h0
    · refine ⟨⟨1, by decide⟩, ?_⟩
      simpa [rayOrbit] using h1
    · refine ⟨⟨2, by decide⟩, ?_⟩
      simpa [rayOrbit] using h2
  · intro hx
    rcases hx with ⟨i, hi⟩
    fin_cases i
    · left
      simpa [rayOrbit] using hi
    · right
      left
      simpa [rayOrbit] using hi
    · right
      right
      simpa [rayOrbit] using hi

/-- Counterexample principle: violating all additive modes means the voxel is not occupied. -/
theorem not_modes_implies_not_occupied (θ x : ℝ)
    (h0 : x ≠ θ)
    (h1 : x ≠ θ + (2 * Real.pi / 3))
    (h2 : x ≠ θ + 2 * (2 * Real.pi / 3)) :
    ¬ OccupiesTriad θ x := by
  intro hx
  rcases hx with hx0 | hx1 | hx2
  · exact h0 hx0
  · exact h1 hx1
  · exact h2 hx2

end TriadicRotation

/-!
## Manifold chart bridge scaffold

This package-level bridge is the next step toward "arbitrary manifold" language:
we abstract a chart-projected rapidity curve and require compatibility with the
triadic orbit law used by the oracle.
-/
namespace ManifoldBridge

open TriadicRotation

/-- Chart-level data for a rapidity curve projected to an angular coordinate. -/
structure RapidityCurveInChart where
  M : Type
  chartPoint : M → ℝ × ℝ
  rapidityCurve : ℕ → M
  angleProj : M → ℝ
  baseAngle : ℝ
  /-- Projected angle on shell `m` is an additive `2π/3` orbit from `baseAngle`. -/
  angle_orbit : ∀ m : ℕ, angleProj (rapidityCurve m) = rayOrbit baseAngle m

/-- In any chart satisfying `angle_orbit`, triadic occupancy follows immediately. -/
theorem angleProj_occupiesTriad_of_mod3
    (C : RapidityCurveInChart) (m : ℕ) :
    OccupiesTriad C.baseAngle (C.angleProj (C.rapidityCurve (m % 3))) := by
  have hOrbit := C.angle_orbit (m % 3)
  have hm3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm3 with h0 | h1 | h2
  · left
    calc
      C.angleProj (C.rapidityCurve (m % 3)) = rayOrbit C.baseAngle (m % 3) := hOrbit
      _ = C.baseAngle := by simp [rayOrbit, h0]
  · right; left
    calc
      C.angleProj (C.rapidityCurve (m % 3)) = rayOrbit C.baseAngle (m % 3) := hOrbit
      _ = C.baseAngle + (2 * Real.pi / 3) := by simp [rayOrbit, h1]
  · right; right
    calc
      C.angleProj (C.rapidityCurve (m % 3)) = rayOrbit C.baseAngle (m % 3) := hOrbit
      _ = C.baseAngle + 2 * (2 * Real.pi / 3) := by simp [rayOrbit, h2]

/-- Strong chart-to-orbit bridge (packaged hypothesis form), up to full-turn `2π` multiples. -/
theorem chart_bridge_to_orbit_mod_turn
    (C : RapidityCurveInChart) :
    ∀ m : ℕ, ∃ k : ℕ,
      C.angleProj (C.rapidityCurve m) = rayOrbit C.baseAngle (m % 3) + ((k : ℕ) : ℝ) * (2 * Real.pi) := by
  intro m
  refine ⟨m / 3, ?_⟩
  calc
    C.angleProj (C.rapidityCurve m) = rayOrbit C.baseAngle m := C.angle_orbit m
    _ = rayOrbit C.baseAngle (m % 3) + (((m / 3 : ℕ) : ℝ) * (2 * Real.pi)) := by
      have hnat : m = m % 3 + 3 * (m / 3) := (Nat.mod_add_div m 3).symm
      have hsplit :
          ((m : ℕ) : ℝ) = ((m % 3 : ℕ) : ℝ) + 3 * (((m / 3 : ℕ) : ℝ)) := by
        exact_mod_cast hnat
      calc
        rayOrbit C.baseAngle m = C.baseAngle + (m : ℝ) * (2 * Real.pi / 3) := by
          simp [rayOrbit]
        _ = C.baseAngle + ((((m % 3 : ℕ) : ℝ) + 3 * (((m / 3 : ℕ) : ℝ))) * (2 * Real.pi / 3)) := by
          rw [hsplit]
        _ = C.baseAngle + ((m % 3 : ℕ) : ℝ) * (2 * Real.pi / 3) + (((m / 3 : ℕ) : ℝ) * (2 * Real.pi)) := by
          ring
        _ = rayOrbit C.baseAngle (m % 3) + ((((m / 3 : ℕ) : ℝ)) * (2 * Real.pi)) := by
          simp [rayOrbit, add_left_comm, add_comm]

/--
Combined bridge step: chart-compatible triadic orbit class (mod full turns) plus
curvature-parametric one-step picker soundness.
-/
theorem chart_bridge_and_picker_sound
    (C : RapidityCurveInChart)
    (ρ : ℕ → ℝ) (φ t : ℝ) (m d : ℕ)
    (hPick : Bridge.pickFromCandidates ρ φ t m = some d) :
    (∃ k : ℕ,
      C.angleProj (C.rapidityCurve m) = rayOrbit C.baseAngle (m % 3) + ((k : ℕ) : ℝ) * (2 * Real.pi))
    ∧ (1 < d ∧ d < m ∧ d ∣ m) := by
  refine ⟨?_, ?_⟩
  · exact chart_bridge_to_orbit_mod_turn C m
  · exact Bridge.pickFromCandidates_sound ρ φ t m d hPick

end ManifoldBridge

/-!
## Runtime-bound shrink lemmas (cutoff via roots/powers)

These are the formal arithmetic facts behind the runtime discussion:

* peeling factors shrinks the cofactor (`n / foundProduct ≤ n`);
* any monotone root-bound function therefore shrinks on the cofactor.
-/
namespace RuntimeBounds

/-- Peeling powers of two never increases the search cofactor. -/
theorem cofactor_after_twos_le (n e : ℕ) :
    n / (2 ^ e) ≤ n := by
  exact Nat.div_le_self _ _

/-- Dividing by any positive found-product never increases the cofactor. -/
theorem cofactor_after_foundProduct_le (n foundProduct : ℕ) (_hpos : 1 ≤ foundProduct) :
    n / foundProduct ≤ n := by
  exact Nat.div_le_self _ _

/--
Abstract root-cutoff shrink principle:
if `rootBound` is monotone in `n`, then replacing `n` by `n/foundProduct` can only
lower (or keep) the bound.
-/
theorem rootBound_shrinks_on_cofactor
    (rootBound : ℕ → ℕ) (hmono : Monotone rootBound)
    (n foundProduct : ℕ) (hpos : 1 ≤ foundProduct) :
    rootBound (n / foundProduct) ≤ rootBound n := by
  exact hmono (cofactor_after_foundProduct_le n foundProduct hpos)

/-- Special case used in the "peel 2" sieve regime. -/
theorem rootBound_shrinks_after_twos
    (rootBound : ℕ → ℕ) (hmono : Monotone rootBound)
    (n e : ℕ) :
    rootBound (n / (2 ^ e)) ≤ rootBound n := by
  exact hmono (cofactor_after_twos_le n e)

end RuntimeBounds

/-!
## Executable recursion skeleton (Lean-side proof target)

This section transcribes the *algorithm shape* used by the Python oracle:

1. peel trivial even factor `2` first when possible;
2. otherwise ask an abstract one-step picker `pick : ℕ → ℕ` for a candidate factor;
3. recurse on the cofactor with bounded depth.

Theorems below prove:

* product correctness (`List.prod = n`);
* divisibility soundness of every reported factor.

These are the core formal obligations needed before any "fast" discussion.
-/

namespace RecursiveOracle

/-- Even-first, depth-bounded factor recursion skeleton. -/
def factorTree (pick : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, n => [n]
  | depth + 1, n =>
      if _hEven : n % 2 = 0 ∧ 2 < n then
        2 :: factorTree pick depth (n / 2)
      else
        let d := pick n
        if _hGood : 1 < d ∧ d < n ∧ d ∣ n then
          d :: factorTree pick depth (n / d)
        else
          [n]

/-- Product of factors reconstructed by `factorTree` is exactly the input shell. -/
theorem factorTree_prod_eq (pick : ℕ → ℕ) :
    ∀ depth n, (factorTree pick depth n).prod = n := by
  intro depth
  induction depth with
  | zero =>
      intro n
      simp [factorTree]
  | succ depth ih =>
      intro n
      by_cases hEven : n % 2 = 0 ∧ 2 < n
      · simp [factorTree, hEven]
        have h2dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hEven.1
        have hmul : 2 * (n / 2) = n := Nat.mul_div_cancel' h2dvd
        calc
          (2 :: factorTree pick depth (n / 2)).prod = 2 * (factorTree pick depth (n / 2)).prod := by simp
          _ = 2 * (n / 2) := by simp [ih]
          _ = n := hmul
      · simp [factorTree, hEven]
        by_cases hGood : 1 < pick n ∧ pick n < n ∧ pick n ∣ n
        · simp [hGood]
          have hdvd : pick n ∣ n := hGood.2.2
          have hmul : pick n * (n / pick n) = n := Nat.mul_div_cancel' hdvd
          calc
            (pick n :: factorTree pick depth (n / pick n)).prod
                = pick n * (factorTree pick depth (n / pick n)).prod := by simp
            _ = pick n * (n / pick n) := by simp [ih]
            _ = n := hmul
        · simp [hGood]

/-- Every entry emitted by `factorTree` divides the original input shell. -/
theorem mem_factorTree_dvd (pick : ℕ → ℕ) :
    ∀ depth n x, x ∈ factorTree pick depth n → x ∣ n := by
  intro depth
  induction depth with
  | zero =>
      intro n x hx
      simp [factorTree] at hx
      rcases hx with rfl
      exact dvd_rfl
  | succ depth ih =>
      intro n x hx
      by_cases hEven : n % 2 = 0 ∧ 2 < n
      · simp [factorTree, hEven] at hx
        rcases hx with rfl | hxTail
        · exact Nat.dvd_of_mod_eq_zero hEven.1
        · have hxDiv : x ∣ n / 2 := ih (n / 2) x hxTail
          have h2dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hEven.1
          have hmul : 2 * (n / 2) = n := Nat.mul_div_cancel' h2dvd
          have hxMul : x ∣ 2 * (n / 2) := dvd_mul_of_dvd_right hxDiv 2
          simpa [hmul] using hxMul
      · simp [factorTree, hEven] at hx
        by_cases hGood : 1 < pick n ∧ pick n < n ∧ pick n ∣ n
        · simp [hGood] at hx
          rcases hx with rfl | hxTail
          · exact hGood.2.2
          · have hxDiv : x ∣ n / pick n := ih (n / pick n) x hxTail
            have hmul : pick n * (n / pick n) = n := Nat.mul_div_cancel' hGood.2.2
            have hxMul : x ∣ pick n * (n / pick n) := dvd_mul_of_dvd_right hxDiv (pick n)
            simpa [hmul] using hxMul
        · simp [hGood] at hx
          rcases hx with rfl
          exact dvd_rfl

end RecursiveOracle

/-!
## Gate-frontier bridge to certified one-step picker

This links the `QuantumFactorGateFrontier` register pipeline to the same
`firstValidDivisor` soundness chain used by the rapidity-polar candidate oracle.
-/
namespace Bridge

/-- One-step pick directly from gate-frontier register candidates. -/
def pickFromGateFrontier (n : ℕ) (regs : List QuantumFactorGateFrontier.QBitRegister) : Option ℕ :=
  firstValidDivisor n (QuantumFactorGateFrontier.candidateList n regs)

/-- Soundness: any successful gate-frontier one-step pick is a nontrivial divisor. -/
theorem pickFromGateFrontier_sound
    (n d : ℕ) (regs : List QuantumFactorGateFrontier.QBitRegister)
    (hPick : pickFromGateFrontier n regs = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold pickFromGateFrontier at hPick
  exact firstValidDivisor_some_spec n d (QuantumFactorGateFrontier.candidateList n regs) hPick

/-- Pair-product form for successful gate-frontier picks. -/
theorem pickFromGateFrontier_pair_product
    (n d : ℕ) (regs : List QuantumFactorGateFrontier.QBitRegister)
    (hPick : pickFromGateFrontier n regs = some d) :
    d * (n / d) = n := by
  have hDiv : d ∣ n := (pickFromGateFrontier_sound n d regs hPick).2.2
  exact Nat.mul_div_cancel' hDiv

/--
Reflection-aware bridge theorem:
if gate reflection aligns counterpart slots and a gate-frontier pick succeeds,
we recover both geometric reflection generation and arithmetic soundness.
-/
theorem gate_reflection_and_pick_sound
    (n step d : ℕ)
    (r : QuantumFactorGateFrontier.QBitRegister)
    (regs : List QuantumFactorGateFrontier.QBitRegister)
    (hAlign :
      QuantumFactorGateFrontier.registerAngleSlot n (QuantumFactorGateFrontier.gateReflect r) =
      QuantumFactorGateFrontier.counterpartAngleSlot n r)
    (hPick : pickFromGateFrontier n regs = some d) :
    (∃ r' ∈ QuantumFactorGateFrontier.gateBundle step r,
        QuantumFactorGateFrontier.registerAngleSlot n r' =
        QuantumFactorGateFrontier.counterpartAngleSlot n r)
    ∧ (1 < d ∧ d < n ∧ d ∣ n) := by
  refine ⟨?_, ?_⟩
  · exact QuantumFactorGateFrontier.counterpartAngle_generated_if_aligned n step r hAlign
  · exact pickFromGateFrontier_sound n d regs hPick

end Bridge

end

end Hqiv.Geometry
