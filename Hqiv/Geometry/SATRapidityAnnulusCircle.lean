import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Ring

import Hqiv.Algebra.OctonionAxisAngles

/-!
# Annulus lattice, unit-circle shell intersections (planar model)

## Geometry narrative (factoring oracle / analytical sphere)

On the higher-dimensional **analytical sphere**, the distinguished locus between the
pole and a \(k\)-arity pole is still a **one-dimensional analytical arc** \(\gamma\).
The SAT rapidity plane here is the **osculating** `ℝ²` model where:

- the target shell is the circle `C_M` about the origin (rapidity radius `M`);
- that circle contains the planar trace of the distinguished arc;
- a **tubular neighborhood** (“ribbon”) around the arc — points within distance
  `ε` of some `γ t` — is where discrete lattice candidates live when they are
  “pulled” toward the shell.

**Moiré** (in this sense): a lattice point can lie in the ribbon near the arc
while **not** lying on the arc itself (`offAnalyticalArc`). Most admissible
candidates are near-misses of the continuous 1D locus; the annulus `A_M(τ)` is the
radial thickening that captures these near-arc points once `ε ≤ τ`.

**Proved bridge:** `inAnnulus_of_shell_arc_ribbon` — ribbon-inclusion implies
`inAnnulus` via the triangle inequality (no number theory).

**Arithmetic ↔ plane (imported):** `Hqiv.Algebra.OctonionAxisAngles` proves the
`π/(2k)` axis from `Ω m = k`, that two steps span `π/k`, and existence of shells with
any `Ω = k`. This file embeds that story in `Plane` via `planeCirclePoint` /
`intrinsicKShellPlaneArc` (`AGENTS/THEOREMS.md` indexes the algebra module).

## Formal objects

- `Plane` is the physical rapidity plane `ℝ²` as `EuclideanSpace ℝ (Fin 2)`.
- `PlaneArc` / `inArcRibbon` / `offAnalyticalArc` / `IsMoireNearArc` spell out the
  arc–ribbon–moiré picture.
- `inAnnulus M τ q` is the radial annulus around the shell of radius `M`.
- `Q` is any finite family of lattice points in that annulus (`AnnulusLatticeFamily`).
- `planeLocalShellIntersections` models `C_q ∩ C_M` as simultaneous distance equations.

**Circle–circle bound:** at most two intersection points (`Finset.card_le_two_of_plane_circle_circle`).

**Counting `#Q`** polynomially in `(varDim, clauseDim, τ)` is a separate encoding input;
`ArcRibbonLatticeCardBound` is the hypothesis bundle (discharged by the SAT/ATSP
problem-size layer or a factoring-oracle arc construction, not necessarily the
archive moiré-search scripts).
-/

namespace Hqiv.Geometry

noncomputable section

open EuclideanGeometry
open PiLp EuclideanSpace

/-- Physical rapidity plane `ℝ²` for the osculating unit-circle model. -/
abbrev Plane :=
  EuclideanSpace ℝ (Fin 2)

theorem finrank_plane_two : Module.finrank ℝ Plane = 2 := by
  simp

/--
Analytical arc in the plane (e.g. the trace between a pole and a \(k\)-arity pole on
the osculating circle, still 1D as `t ↦ γ(t)`).
-/
structure PlaneArc where
  γ : ℝ → Plane

/-!
### Osculating circle ↔ `OctonionAxisAngles` (`Ω`, `π/(2k)`)

Embedding of the analytical-sphere polar step into the rapidity plane: radius `M`,
angle `θ`.  See `Hqiv.Algebra.OctonionAxisAngles` and `AGENTS/archive/OCTONION_SPHERE_PATCH.md` §2.
-/

/-- Point on the circle of radius `|M|` at polar angle `θ` (standard coordinates in `Plane`). -/
noncomputable def planeCirclePoint (M θ : ℝ) : Plane :=
  WithLp.toLp 2 ![M * Real.cos θ, M * Real.sin θ]

theorem norm_sq_planeCirclePoint (M θ : ℝ) : ‖planeCirclePoint M θ‖ ^ 2 = M ^ 2 := by
  unfold planeCirclePoint
  rw [norm_sq_eq_of_L2]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← mul_add, Real.cos_sq_add_sin_sq θ]
  ring

theorem norm_planeCirclePoint (M θ : ℝ) : ‖planeCirclePoint M θ‖ = |M| := by
  have h2 := norm_sq_planeCirclePoint M θ
  have habs := (sq_eq_sq_iff_abs_eq_abs _ _).1 h2
  simpa [abs_of_nonneg (norm_nonneg _)] using habs

theorem dist_planeCirclePoint_origin (M θ : ℝ) :
    dist (planeCirclePoint M θ) (0 : Plane) = |M| := by
  simp [dist_eq_norm, sub_zero, norm_planeCirclePoint]

theorem dist_planeCirclePoint_origin_nonneg {M θ : ℝ} (hM : 0 ≤ M) :
    dist (planeCirclePoint M θ) (0 : Plane) = M := by
  rw [dist_planeCirclePoint_origin, abs_of_nonneg hM]

/--
Parametrization of the target shell circle at radius `M`. The `k` tag records the
narrative arity (`π/(2k)` steps from `OctonionAxisAngles`); the map is the full
circle `θ ↦ planeCirclePoint M θ`.
-/
noncomputable def intrinsicKShellPlaneArc (M : ℝ) (k : ℕ) (_hk : 0 < k) : PlaneArc :=
  ⟨fun θ => planeCirclePoint M θ⟩

theorem intrinsicKShellPlaneArc_shell (M : ℝ) {k : ℕ} (hk : 0 < k) (θ : ℝ) :
    dist ((intrinsicKShellPlaneArc M k hk).γ θ) (0 : Plane) = |M| :=
  dist_planeCirclePoint_origin M θ

theorem intrinsicKShellPlaneArc_shell_nonneg {M : ℝ} (hM : 0 ≤ M) {k : ℕ} (hk : 0 < k) (θ : ℝ) :
    dist ((intrinsicKShellPlaneArc M k hk).γ θ) (0 : Plane) = M :=
  dist_planeCirclePoint_origin_nonneg hM

section
open scoped ArithmeticFunction.Omega
open ArithmeticFunction Hqiv.Algebra

/-- Some shell `m > 1` has `Ω m = k` and intrinsic angle `π/(2k)` (factoring-oracle / shell ladder). -/
theorem exists_shell_pi_over_two_k_axis (k : ℕ) (hk : 1 ≤ k) :
    ∃ (m : ℕ) (hm : 1 < m), intrinsicShellAxisAngle m hm = Real.pi / (2 * k) ∧ Ω m = k :=
  exists_one_lt_intrinsicShellAxisAngle_eq_pi_div_two_k k hk

/-- Two `π/(2k)` axis-angle steps span central angle `π/k` on the circle. -/
theorem axisAngle_two_step_span_pi_div_k (k : ℕ) (hk : 0 < k) :
    2 * axisAngle k hk = Real.pi / k :=
  two_mul_axisAngle_eq_pi_div_k k hk

end

/-- Tubular neighborhood / “ribbon” of radius `ε` around the arc: some point of the
arc lies within `ε` of `q`. -/
def inArcRibbon (A : PlaneArc) (ε : ℝ) (q : Plane) : Prop :=
  ∃ t : ℝ, dist q (A.γ t) ≤ ε

/--
**Moiré offset:** `q` does not lie exactly on the analytical arc (no `t` with `q = γ t`).
Typical lattice points in a ribbon satisfy this.
-/
def offAnalyticalArc (A : PlaneArc) (q : Plane) : Prop :=
  ∀ t : ℝ, q ≠ A.γ t

/-- Ribbon + off-arc: the standard “near the 1D locus but not on it” configuration. -/
def IsMoireNearArc (A : PlaneArc) (ε : ℝ) (q : Plane) : Prop :=
  inArcRibbon A ε q ∧ offAnalyticalArc A q

/-- Target shell `C_M` modeled as the circle of radius `M` about the origin. -/
def onTargetShell (M : ℝ) (p : Plane) : Prop :=
  dist p 0 = M

/-- Thin annulus `A_M(τ)` around the shell: radial distance to the origin lies in
`[M - τ, M + τ]` (requires side conditions `0 ≤ τ`, `τ ≤ M` in applications). -/
def inAnnulus (M τ : ℝ) (q : Plane) : Prop :=
  M - τ ≤ dist q 0 ∧ dist q 0 ≤ M + τ

/--
If the arc lies on the target shell (`dist (γ t) 0 = M` for all `t`) and `ε ≤ τ`, then
every point in the `ε`-ribbon lies in the radial annulus `A_M(τ)`.

So: **lattice points chosen within `ε` of the analytical arc are automatically
annulus candidates** once the threshold width `τ` dominates the ribbon thickness.

Proof: triangle inequality only.
-/
theorem inAnnulus_of_shell_arc_ribbon (M τ ε : ℝ) (A : PlaneArc)
    (hShell : ∀ t, dist (A.γ t) (0 : Plane) = M)
    (hε : ε ≤ τ) (q : Plane) (hrib : inArcRibbon A ε q) :
    inAnnulus M τ q := by
  rcases hrib with ⟨t, ht⟩
  constructor
  · -- Lower: `M - τ ≤ dist q 0`
    have hlo : M - ε ≤ dist q (0 : Plane) := by
      have h := dist_triangle (A.γ t) q (0 : Plane)
      rw [hShell t, dist_comm (A.γ t) q] at h
      linarith [ht]
    have hτ_le : M - τ ≤ M - ε := sub_le_sub (le_refl M) hε
    exact le_trans hτ_le hlo
  · -- Upper: `dist q 0 ≤ M + τ`
    have := dist_triangle q (A.γ t) (0 : Plane)
    rw [hShell t] at this
    linarith [ht]

/--
If `q` is moiré-near-arc (ribbon + off-arc) and the arc lies on the shell, then `q`
lies in the annulus once `ε ≤ τ`.
-/
theorem inAnnulus_of_isMoireNearArc (M τ ε : ℝ) (A : PlaneArc)
    (hShell : ∀ t, dist (A.γ t) (0 : Plane) = M)
    (hε : ε ≤ τ) (q : Plane) (h : IsMoireNearArc A ε q) :
    inAnnulus M τ q :=
  inAnnulus_of_shell_arc_ribbon M τ ε A hShell hε q h.1

/--
Finite family `Q` of candidate lattice points together with the annulus membership
witness. In applications, `carrier` is the formal `Q := L ∩ A_M(τ)` after fixing an
embedding `L → Plane`.
-/
structure AnnulusLatticeFamily (M τ : ℝ) where
  carrier : Finset Plane
  /-- Every point of `carrier` lies in the annulus around the shell of radius `M`. -/
  mem_annulus : ∀ q ∈ carrier, inAnnulus M τ q

/--
Abstract “intersection set” for the unit circle at `q` with the target shell: any
finite set of points that lie on **both** the shell circle (center `0`, radius `M`)
and the unit circle (center `q`, radius `1`), i.e. the standard formalization of
`C_q ∩ C_M` as a distance locus in the plane.
-/
def isPlaneShellIntersection (M : ℝ) (q : Plane) (I : Finset Plane) : Prop :=
  ∀ p ∈ I, dist p 0 = M ∧ dist p q = 1

/-- Same as `isPlaneShellIntersection`: a finite model of `C_q ∩ C_M` (two circle loci).

Named `planeLocalShellIntersections` so `SATRapidityDirectionSelection.localShellIntersections`
(the abstract `Finset ℕ` scaffold) can coexist in the same import graph.
-/
abbrev planeLocalShellIntersections (M : ℝ) (q : Plane) (I : Finset Plane) : Prop :=
  isPlaneShellIntersection M q I

/--
If a finite set lies on two distinct circles in the plane (here: shell about `0`
and unit circle about `q`), it has at most two points.

This is exactly the “0 / 1 / 2 intersection points” geometry: the annulus width
enters only when **constructing** admissible `q` (so that the intersection is
non-empty / non-degenerate); the cardinality bound `≤ 2` is pure circle–circle
geometry in `finrank = 2`.
-/
theorem Finset.card_le_two_of_plane_circle_circle
    (M : ℝ) (q : Plane) (I : Finset Plane)
    (hq : q ≠ 0) (h : planeLocalShellIntersections M q I) :
    I.card ≤ 2 := by
  classical
  let c₁ : Plane := 0
  let c₂ : Plane := q
  let r₁ : ℝ := M
  let r₂ : ℝ := 1
  have hc : c₁ ≠ c₂ := by simpa [c₁, c₂] using (Ne.symm hq)
  have h' : ∀ p ∈ I, dist p c₁ = r₁ ∧ dist p c₂ = r₂ := by
    intro p hp
    simpa [c₁, c₂, r₁, r₂, planeLocalShellIntersections, isPlaneShellIntersection] using h p hp
  clear h hq
  by_contra hcard
  have h2 : 2 < I.card := Nat.not_le.mp hcard
  rcases Finset.two_lt_card.mp h2 with ⟨a, ha, b, hb, p₃, hp₃, hab, hap₃, hbp₃⟩
  have ha' := h' a ha
  have hb' := h' b hb
  have hp₃' := h' p₃ hp₃
  have hE :=
    eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (V := Plane) (P := Plane) finrank_plane_two
      hc hab ha'.1 hb'.1 hp₃'.1 ha'.2 hb'.2 hp₃'.2
  cases hE with
  | inl h₁ => exact absurd (Eq.symm h₁) hap₃
  | inr h₂ => exact absurd (Eq.symm h₂) hbp₃

/-!
### Polynomial counting slot for `#Q`

Interface for “`#Q` is polynomial in `(varDim, clauseDim, τ)`”: supply an explicit
numeric `countBound` from the **problem encoding** (SAT/ATSP size, factoring-oracle
arc parameters, etc.).
-/

/--
Hypothesis bundle: an explicit bound `countBound varDim clauseDim τBits` majorizes
`#Q` for an `AnnulusLatticeFamily`.

`τBits` stands for discrete resolution of the threshold (bit-length, numerator of
rational `τ`, …) — align with `SATWorstCaseCertified` / ATSP envelopes as needed.
-/
structure ArcRibbonLatticeCardBound (M τ : ℝ) where
  family : AnnulusLatticeFamily M τ
  varDim : ℕ
  clauseDim : ℕ
  τBits : ℕ
  countBound : ℕ → ℕ → ℕ → ℕ
  /-- `#Q` is bounded by the supplied explicit function of `(varDim, clauseDim, τBits)`. -/
  hCard :
    family.carrier.card ≤ (countBound varDim clauseDim τBits)

/-- Convenience constructor from an explicit cardinality witness (the structure already has `.mk`). -/
def ArcRibbonLatticeCardBound.ofCardLe (M τ : ℝ) (family : AnnulusLatticeFamily M τ)
    (varDim clauseDim τBits : ℕ) (countBound : ℕ → ℕ → ℕ → ℕ)
    (hCard : family.carrier.card ≤ countBound varDim clauseDim τBits) :
    ArcRibbonLatticeCardBound M τ where
  family := family
  varDim := varDim
  clauseDim := clauseDim
  τBits := τBits
  countBound := countBound
  hCard := hCard

theorem annulus_lattice_card_le_of_arc_ribbon_bound (M τ : ℝ)
    (C : ArcRibbonLatticeCardBound M τ) :
    C.family.carrier.card ≤ C.countBound C.varDim C.clauseDim C.τBits :=
  C.hCard

/-- Deprecated alias for `ArcRibbonLatticeCardBound` (older moiré-lattice naming). -/
abbrev MoireLatticePolynomialCount (M τ : ℝ) :=
  ArcRibbonLatticeCardBound M τ

theorem annulus_lattice_card_le_of_moire_hypothesis (M τ : ℝ)
    (C : ArcRibbonLatticeCardBound M τ) :
    C.family.carrier.card ≤ C.countBound C.varDim C.clauseDim C.τBits :=
  annulus_lattice_card_le_of_arc_ribbon_bound M τ C

end

end Hqiv.Geometry
