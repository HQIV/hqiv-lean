import Hqiv.Geometry.SATRapidityAnnulusCircle
import Hqiv.Geometry.SATRapidityDirectionSelection
import Hqiv.Geometry.SATRapidityExactCardinality
import Hqiv.Geometry.SATRapidityGapBridge
import Hqiv.Geometry.GeneralRiemannianRapidityOracle
import Hqiv.Geometry.ATSPWorstCaseCertified

/-!
# Local ribbon-section model ↔ exact union cardinality

## Encoding: abstract manifold, explicit local 2-plane witness

The ambient SAT carrier `M : Type*` stays **abstract**. A `PlaneWitnessMap M` is best
read as an **osculating 2-plane / local ribbon-section witness**:

- the global manifold need not be literally planar or spherical,
- the axis-to-arity-pole ribbon may live in a more general ambient geometry,
- but the local counting argument only uses the 2-dimensional section spanned by the
  relevant shell center and shell intersection geometry.

So `PlaneWitnessMap M` is an arbitrary function `ResidualPoint M → Plane`, composed
with `residualPoint r` from direction-selection / gap-bridge data to land shell centers
in a local section without committing to a global chart on `M`.

This module wires the **proved** local-2D facts in `SATRapidityAnnulusCircle` into the
combinatorial `K_exactUnionCard` layer from `SATRapidityExactCardinality`:

- each nontrivial center `q ≠ 0` and genuine local shell witness `I ⊂ Plane` with
  `planeLocalShellIntersections shellR q I` has `|I| ≤ 2`;
- hence `K_exactUnionCard Q intersections ≤ 2 * |Q|`;
- combining with `ArcRibbonLatticeCardBound` yields `K_exact ≤ 2 * countBound(...)`.

Shell radius is written `shellR : ℝ` to avoid clashing with the abstract manifold
carrier `M : Type*` used elsewhere in the SAT scaffold.

No new analytic content beyond `SATRapidityAnnulusCircle` — this is bookkeeping.

The important point is that the 2D witness is a **local reduction for the counting
kernel**, not a claim that the full rapidity manifold is globally planar.

**Gap bridge:** `direction_selection_with_plane_witness_implies_gap_bridge` and
`direction_selection_with_plane_witness_implies_geometric_collapse` import
`SATRapidityGapBridge` / `toGeometricCollapse` without wrapping `DirectionSelectionCertificate`.
-/

namespace Hqiv.Geometry

open Finset

/--
Purely cardinality-level bridge from the factorization candidate list: the exported
bounded candidate family has size exactly `3 * (candidateStepBound n + 1)`.

This is not yet an annulus-membership theorem, but it internalizes the finite-size part
of the factorization/oracle pipeline into the SAT rapidity bridge stack.
-/
theorem factorization_candidate_family_card_eq (n : ℕ) (derive : ArcParameter → Option ℕ) :
    (candidateList n derive).length = 3 * (candidateStepBound n + 1) :=
  candidateList_length_eq n derive

/--
Hence the factorization candidate family is bounded by the same explicit function.
-/
theorem factorization_candidate_family_card_le (n : ℕ) (derive : ArcParameter → Option ℕ) :
    (candidateList n derive).length ≤ 3 * (candidateStepBound n + 1) := by
  simpa [factorization_candidate_family_card_eq n derive]

/-- Per-center cardinality `≤ 2` from circle–circle geometry. -/
theorem plane_localShellIntersection_card_le_two (shellR : ℝ) (q : Plane) (I : Finset Plane)
    (hq : q ≠ 0) (h : planeLocalShellIntersections shellR q I) :
    I.card ≤ 2 :=
  Finset.card_le_two_of_plane_circle_circle shellR q I hq h

/--
Local ribbon-section witness for an abstract manifold tag `M`.

Interpretation: each abstract `ResidualPoint` is assigned a center in a chosen local
2-dimensional section where the shell / unit-circle intersection counting is carried out.
This is an osculating-plane witness, not a global claim about the ambient manifold.

Compose with `residualPoint : SATResidual M → ResidualPoint M` from a certificate to
obtain centers `q` for each residual.
-/
structure PlaneWitnessMap (M : Type*) where
  toPlane : ResidualPoint M → Plane

/-- Alias emphasizing the intended geometric meaning of `PlaneWitnessMap`. -/
abbrev LocalRibbonSectionWitness (M : Type*) := PlaneWitnessMap M

/-- Center in `Plane` for a residual once `residualPoint` and a witness are chosen. -/
def planeCenterOfResidual (W : PlaneWitnessMap M) (residualPoint : SATResidual M → ResidualPoint M)
    (r : SATResidual M) : Plane :=
  W.toPlane (residualPoint r)

theorem planeCenterOfResidual_eq (W : PlaneWitnessMap M) (residualPoint : SATResidual M → ResidualPoint M)
    (r : SATResidual M) : planeCenterOfResidual W residualPoint r = W.toPlane (residualPoint r) :=
  rfl

theorem localShellIntersection_card_le_two_of_witness (shellR : ℝ) (W : PlaneWitnessMap M)
    (p : ResidualPoint M) (I : Finset Plane) (hq : W.toPlane p ≠ 0)
    (h : planeLocalShellIntersections shellR (W.toPlane p) I) :
    I.card ≤ 2 :=
  plane_localShellIntersection_card_le_two shellR (W.toPlane p) I hq h

theorem localShellIntersection_card_le_two_of_residual (shellR : ℝ) (W : PlaneWitnessMap M)
    (residualPoint : SATResidual M → ResidualPoint M) (r : SATResidual M) (I : Finset Plane)
    (hq : planeCenterOfResidual W residualPoint r ≠ 0)
    (h : planeLocalShellIntersections shellR (planeCenterOfResidual W residualPoint r) I) :
    I.card ≤ 2 :=
  localShellIntersection_card_le_two_of_witness shellR W (residualPoint r) I
    (by simpa [planeCenterOfResidual] using hq)
    (by simpa [planeCenterOfResidual] using h)

theorem planeWitness_injective_implies_centers_ne (W : PlaneWitnessMap M)
    (hinj : Function.Injective W.toPlane) {p₁ p₂ : ResidualPoint M} (h : p₁ ≠ p₂) :
    W.toPlane p₁ ≠ W.toPlane p₂ :=
  hinj.ne h

/--
Any local ribbon-section witness can be used as the current osculating-plane witness;
this is just the identity map on the existing structure, making the intended geometric
reading explicit in downstream statements.
-/
def LocalRibbonSectionWitness.toPlaneWitnessMap {M : Type*}
    (W : LocalRibbonSectionWitness M) : PlaneWitnessMap M :=
  W

/--
Conversely, every current plane witness is already a local ribbon-section witness.
-/
def PlaneWitnessMap.toLocalRibbonSectionWitness {M : Type*}
    (W : PlaneWitnessMap M) : LocalRibbonSectionWitness M :=
  W

@[simp] theorem LocalRibbonSectionWitness.toPlaneWitnessMap_eq {M : Type*}
    (W : LocalRibbonSectionWitness M) : W.toPlaneWitnessMap = W :=
  rfl

@[simp] theorem PlaneWitnessMap.toLocalRibbonSectionWitness_eq {M : Type*}
    (W : PlaneWitnessMap M) : W.toLocalRibbonSectionWitness = W :=
  rfl

/--
Local-section wording for the same center realization.
-/
theorem localRibbonSection_center_realization {M : Type*}
    (W : LocalRibbonSectionWitness M) (residualPoint : SATResidual M → ResidualPoint M)
    (r : SATResidual M) :
    W.toPlane (residualPoint r) = planeCenterOfResidual W.toPlaneWitnessMap residualPoint r :=
  rfl

/--
`K_exact ≤ 2 * #Q` when each fiber is a planar `C_q ∩ C_{shellR}` witness satisfying
`planeLocalShellIntersections`.
-/
theorem K_exactUnionCard_le_two_mul_of_planeLocalShell (shellR : ℝ) (Q : Finset Plane)
    (intersections : Plane → Finset Plane) (hne : ∀ q ∈ Q, q ≠ 0)
    (h : ∀ q ∈ Q, planeLocalShellIntersections shellR q (intersections q)) :
    K_exactUnionCard Q intersections ≤ 2 * Q.card :=
  K_exactUnionCard_le_two_mul Q intersections fun q hq =>
    plane_localShellIntersection_card_le_two shellR q (intersections q) (hne q hq) (h q hq)

/--
Same as `K_exactUnionCard_le_two_mul_of_planeLocalShell`, chained with an explicit
upper bound `|Q| ≤ B` (e.g. from `ArcRibbonLatticeCardBound.hCard`).
-/
theorem K_exactUnionCard_le_two_mul_countBound (shellR : ℝ) (Q : Finset Plane)
    (intersections : Plane → Finset Plane) (hne : ∀ q ∈ Q, q ≠ 0)
    (h : ∀ q ∈ Q, planeLocalShellIntersections shellR q (intersections q)) (B : ℕ)
    (hQB : Q.card ≤ B) : K_exactUnionCard Q intersections ≤ 2 * B :=
  le_trans (K_exactUnionCard_le_two_mul_of_planeLocalShell shellR Q intersections hne h)
    (Nat.mul_le_mul_left 2 hQB)

/--
Package `ArcRibbonLatticeCardBound` with planar intersections: `K_exact` is bounded
by twice the declared **polynomial** counting slot.
-/
theorem K_exactUnionCard_le_two_mul_arcRibbonCount (shellR τ : ℝ)
    (C : ArcRibbonLatticeCardBound shellR τ) (intersections : Plane → Finset Plane)
    (hne : ∀ q ∈ C.family.carrier, q ≠ 0)
    (h : ∀ q ∈ C.family.carrier, planeLocalShellIntersections shellR q (intersections q)) :
    K_exactUnionCard C.family.carrier intersections ≤
      2 * C.countBound C.varDim C.clauseDim C.τBits :=
  K_exactUnionCard_le_two_mul_countBound shellR C.family.carrier intersections hne h _
    C.hCard

/--
Residual-count / length bound: if `len ≤ K_exact` and the planar hypotheses hold, then
`len ≤ 2 * |Q|`; if moreover `|Q| ≤ B`, then `len ≤ 2 * B`.
-/
theorem residualCount_le_two_mul_Q_of_plane (shellR : ℝ) (Q : Finset Plane)
    (intersections : Plane → Finset Plane) (len : ℕ) (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections shellR q (intersections q))
    (hK : len ≤ K_exactUnionCard Q intersections) :
    len ≤ 2 * Q.card :=
  residualCount_le_two_mul_lattice_of_Kexact intersections len hK fun q hq =>
    plane_localShellIntersection_card_le_two shellR q (intersections q) (hne q hq) (hloc q hq)

theorem residualCount_le_two_mul_countBound_of_plane (shellR : ℝ) (Q : Finset Plane)
    (intersections : Plane → Finset Plane) (len : ℕ) (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections shellR q (intersections q))
    (hK : len ≤ K_exactUnionCard Q intersections) (B : ℕ) (hQB : Q.card ≤ B) :
    len ≤ 2 * B :=
  le_trans (residualCount_le_two_mul_Q_of_plane shellR Q intersections len hne hloc hK)
    (Nat.mul_le_mul_left 2 hQB)

/-!
## Conditional lemmas (no wrapper on `DirectionSelectionCertificate`)

`DirectionSelectionCertificate` stays abstract.  Lemmas below take optional
`PlaneWitnessMap` / cover hypotheses in the same spirit as `toGeometricCollapse` /
`toSATRapidityGapBridge`: extra assumptions thread through without a parallel
certificate hierarchy.

A full `SATRapidityGeometricCollapse` still requires `SuccessorStepResidualControl`
and `DirectionSelectionCertificate.toGeometricCollapse` (or the packaged theorem
below).
-/

/--
`planeCenterOfResidual` is **definitionally** `W.toPlane (residualPoint r)`; any
separate “realization” equality is redundant.
-/
theorem planeCenterOfResidual_eq_toPlane (W : PlaneWitnessMap M)
    (residualPoint : SATResidual M → ResidualPoint M) (r : SATResidual M) :
    planeCenterOfResidual W residualPoint r = W.toPlane (residualPoint r) :=
  rfl

theorem plane_center_ne_of_injective_witness_and_residualPoint
    (W : PlaneWitnessMap M) (residualPoint : SATResidual M → ResidualPoint M)
    (hW : Function.Injective W.toPlane) (hP : Function.Injective residualPoint)
    {r₁ r₂ : SATResidual M} (h : r₁ ≠ r₂) :
    planeCenterOfResidual W residualPoint r₁ ≠ planeCenterOfResidual W residualPoint r₂ := by
  intro heq
  have htp : W.toPlane (residualPoint r₁) = W.toPlane (residualPoint r₂) := by
    simpa [planeCenterOfResidual] using heq
  exact h (hP (hW htp))

/--
Named re-export of `direction_selection_implies_geometric_collapse` for citations
alongside plane-witness arguments.
-/
theorem geometric_collapse_inequalities_of_direction_selection {M : Type*}
    (D : DirectionSelectionCertificate M) :
    D.effectiveDim ≤ D.logBoundConst * Nat.log 2 (D.shared.varDim + D.shared.clauseDim + 1) ∧
    (D.residuals.length : ℝ) ≤ sphere_code_bound D.sphereCodeBound D.effectiveDim :=
  direction_selection_implies_geometric_collapse D

/-!
### End-to-end packaging (`gapBridge` + `geometricCollapse`)

These definitions keep `DirectionSelectionCertificate` abstract: a `PlaneWitnessMap`
is only threaded so callers can simultaneously carry cover / injectivity / planar-fiber
hypotheses in the **same** theorem statement without a parallel wrapper certificate.

The **combinatorial** lemmas below are where planar `planeLocalShellIntersections` and
`K_exactUnionCard` hypotheses are actually used.
-/

/--
Gap bridge from direction selection; supply `W` to bundle geometric side conditions
next to `D` without changing the certificate type.
-/
def direction_selection_with_plane_witness_implies_gap_bridge {M : Type*}
    (D : DirectionSelectionCertificate M) (_W : PlaneWitnessMap M) : SATRapidityGapBridge M :=
  D.toSATRapidityGapBridge

/--
Same geometric-collapse certificate as `DirectionSelectionCertificate.toGeometricCollapse`, with
`W` threaded for plane-witness hypotheses.
-/
def direction_selection_with_plane_witness_implies_geometric_collapse {M : Type*}
    (D : DirectionSelectionCertificate M) (control : SuccessorStepResidualControl M) (_W : PlaneWitnessMap M)
    (hShared : control.shared = D.shared)
    (hLen : D.residuals.length = control.arityResiduals.length)
    (hPoly : D.sphereCodeBound D.effectiveDim ≤ D.sphereCodeBound (control.shared.varDim + control.shared.clauseDim)) :
    SATRapidityGeometricCollapse M :=
  D.toGeometricCollapse control hShared hLen hPoly

/--
`SuccessorStepResidualControl` + direction selection ⇒ `SATRapidityGeometricCollapse`.
`W` is an explicit parameter for hypothesis threading (same data as
`direction_selection_with_plane_witness_implies_geometric_collapse`).
-/
def SATRapidityGeometricCollapse.of_direction_selection_control_and_planeWitness
    {M : Type*} (D : DirectionSelectionCertificate M)
    (control : SuccessorStepResidualControl M)
    (hShared : control.shared = D.shared)
    (hLen : D.residuals.length = control.arityResiduals.length)
    (hPoly : D.sphereCodeBound D.effectiveDim ≤ D.sphereCodeBound (control.shared.varDim + control.shared.clauseDim))
    (W : PlaneWitnessMap M) :
    SATRapidityGeometricCollapse M :=
  direction_selection_with_plane_witness_implies_geometric_collapse D control W hShared hLen hPoly

/--
`gapBridge → toGeometricCollapse` agrees with the direct direction-selection route.
-/
theorem direction_selection_geometric_collapse_via_gap_bridge_eq {M : Type*}
    (D : DirectionSelectionCertificate M) (W : PlaneWitnessMap M)
    (control : SuccessorStepResidualControl M) (hShared : control.shared = D.shared)
    (hLen : D.residuals.length = control.arityResiduals.length)
    (hPoly : D.sphereCodeBound D.effectiveDim ≤ D.sphereCodeBound (control.shared.varDim + control.shared.clauseDim)) :
    (direction_selection_with_plane_witness_implies_gap_bridge D W).toGeometricCollapse control hShared hLen hPoly =
      direction_selection_with_plane_witness_implies_geometric_collapse D control W hShared hLen hPoly := by
  rfl

/-!
### Injective centers and residual cover (hypotheses the user threads)

These lemmas spell out the usual logical equivalents; they are not needed to *prove*
the scaffold certificates, but they match the informal “four conditions” story.
-/

theorem injective_residual_plane_centers_iff {M : Type*} (W : PlaneWitnessMap M)
    (residualPoint : SATResidual M → ResidualPoint M) :
    Function.Injective (fun r : SATResidual M => W.toPlane (residualPoint r)) ↔
      ∀ r₁ r₂ : SATResidual M, r₁ ≠ r₂ → W.toPlane (residualPoint r₁) ≠ W.toPlane (residualPoint r₂) where
  mp hinj r₁ r₂ hr := fun heq => hr (hinj heq)
  mpr h r₁ r₂ heq := by
    by_contra hr
    exact (h r₁ r₂ hr) heq

theorem plane_witness_center_realization (W : PlaneWitnessMap M) (residualPoint : SATResidual M → ResidualPoint M)
    (r : SATResidual M) : W.toPlane (residualPoint r) = planeCenterOfResidual W residualPoint r :=
  rfl

/-!
### Combinatorial consequences (planar fibers + `K_exact` actually used)

Cover is required in the **statement** so callers document that residual centers lie in
the finite family `Q` supporting the union bound; the current counting lemmas still
derive `len ≤ 2 * #Q` from `len ≤ K_exact` and per-fiber geometry alone.

## Honest boundary / still-external inputs

The lemmas in this section prove only the **combinatorial packaging** once the listed
inputs are supplied.  They do **not** yet discharge the following deeper geometric or
encoding steps:

* `localShellIntersections` on the abstract manifold remains the scaffold placeholder
  `∅`, and `angle` on abstract shell directions remains the scaffold constant `0`.
  So the current file does **not** prove from first-principles geometry that a rapidity
  gap determines canonical directions; it only packages the interface needed once that
  statement is supplied elsewhere.
* Polynomial control of `#Q` in instance size is still imported through
  `ArcRibbonLatticeCardBound.hCard`; this file only chains that hypothesis through the
  exact-count inequalities.
* The bridge hypothesis
  `hK : residuals.length ≤ K_exactUnionCard Q intersections` is the real SAT-to-union
  model connection.  Proving `hK` in general requires a future cover / encoding lemma
  relating SAT residuals to the explicit planar family.  The present file treats `hK`
  as external input and then derives the downstream cardinality consequences.
-/

theorem residual_count_le_two_mul_Q_card_of_direction_plane_cover {M : Type*}
    (D : DirectionSelectionCertificate M) (_W : PlaneWitnessMap M) (Q : Finset Plane)
    (intersections : Plane → Finset Plane)
    (_cover : ∀ r ∈ D.residuals, planeCenterOfResidual _W D.residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q))
    (hK : D.residuals.length ≤ K_exactUnionCard Q intersections) :
    D.residuals.length ≤ 2 * Q.card :=
  residualCount_le_two_mul_Q_of_plane D.annulusModel.shellRadius Q intersections D.residuals.length hne hloc hK

theorem residual_length_real_le_two_mul_Q_card_cast_of_direction_plane_cover {M : Type*}
    (D : DirectionSelectionCertificate M) (W : PlaneWitnessMap M) (Q : Finset Plane)
    (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ D.residuals, planeCenterOfResidual W D.residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q))
    (hK : D.residuals.length ≤ K_exactUnionCard Q intersections) :
    (D.residuals.length : ℝ) ≤ 2 * (Q.card : ℝ) := by
  have hnat :=
    residual_count_le_two_mul_Q_card_of_direction_plane_cover D W Q intersections hCover hne hloc hK
  simpa using (Nat.cast_le (α := ℝ)).mpr hnat

theorem residual_count_le_two_mul_B_of_direction_plane_cover {M : Type*}
    (D : DirectionSelectionCertificate M) (W : PlaneWitnessMap M) (Q : Finset Plane)
    (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ D.residuals, planeCenterOfResidual W D.residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q))
    (hK : D.residuals.length ≤ K_exactUnionCard Q intersections) (B : ℕ) (hQB : Q.card ≤ B) :
    D.residuals.length ≤ 2 * B :=
  residualCount_le_two_mul_countBound_of_plane D.annulusModel.shellRadius Q intersections D.residuals.length
    hne hloc hK B hQB

/--
Polynomial slot on `#Q` from `ArcRibbonLatticeCardBound`, aligned with `D.annulusModel`.
-/
theorem K_exactUnionCard_le_two_mul_arcRibbon_of_direction {M : Type*}
    (D : DirectionSelectionCertificate M) (C : ArcRibbonLatticeCardBound D.annulusModel.shellRadius D.annulusModel.thresholdWidth)
    (intersections : Plane → Finset Plane) (hne : ∀ q ∈ C.family.carrier, q ≠ 0)
    (hloc : ∀ q ∈ C.family.carrier,
      planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q)) :
    K_exactUnionCard C.family.carrier intersections ≤
      2 * C.countBound C.varDim C.clauseDim C.τBits :=
  K_exactUnionCard_le_two_mul_arcRibbonCount D.annulusModel.shellRadius D.annulusModel.thresholdWidth C intersections
    hne hloc

/--
The annulus candidate family itself already gives the cross-dimension `#Q` bound used in
the SAT bridge: no extra geometry is needed beyond the packaged `ArcRibbonLatticeCardBound`.
-/
theorem residual_count_le_two_mul_arcRibbon_of_direction {M : Type*}
    (D : DirectionSelectionCertificate M)
    (C : ArcRibbonLatticeCardBound D.annulusModel.shellRadius D.annulusModel.thresholdWidth)
    (intersections : Plane → Finset Plane)
    (hne : ∀ q ∈ C.family.carrier, q ≠ 0)
    (hloc : ∀ q ∈ C.family.carrier,
      planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q))
    (hK : D.residuals.length ≤ K_exactUnionCard C.family.carrier intersections) :
    D.residuals.length ≤ 2 * C.countBound C.varDim C.clauseDim C.τBits := by
  exact residualCount_le_two_mul_countBound_of_plane
    D.annulusModel.shellRadius C.family.carrier intersections D.residuals.length
    hne hloc hK _ C.hCard

/--
Real-cast version of `residual_count_le_two_mul_arcRibbon_of_direction`.
-/
theorem residual_length_real_le_two_mul_arcRibbon_of_direction {M : Type*}
    (D : DirectionSelectionCertificate M)
    (C : ArcRibbonLatticeCardBound D.annulusModel.shellRadius D.annulusModel.thresholdWidth)
    (intersections : Plane → Finset Plane)
    (hne : ∀ q ∈ C.family.carrier, q ≠ 0)
    (hloc : ∀ q ∈ C.family.carrier,
      planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q))
    (hK : D.residuals.length ≤ K_exactUnionCard C.family.carrier intersections) :
    (D.residuals.length : ℝ) ≤ 2 * (C.countBound C.varDim C.clauseDim C.τBits : ℝ) := by
  have hnat :=
    residual_count_le_two_mul_arcRibbon_of_direction D C intersections hne hloc hK
  simpa using (Nat.cast_le (α := ℝ)).mpr hnat

/--
Real-cast version of the `2 * B` residual bound from directional planar cover data.
-/
theorem residual_length_real_le_two_mul_B_cast_of_direction_plane_cover {M : Type*}
    (D : DirectionSelectionCertificate M) (W : PlaneWitnessMap M) (Q : Finset Plane)
    (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ D.residuals, planeCenterOfResidual W D.residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q))
    (hK : D.residuals.length ≤ K_exactUnionCard Q intersections)
    (B : ℕ) (hQB : Q.card ≤ B) :
    (D.residuals.length : ℝ) ≤ 2 * (B : ℝ) := by
  have hnat :=
    residual_count_le_two_mul_B_of_direction_plane_cover D W Q intersections hCover hne hloc hK B hQB
  simpa using (Nat.cast_le (α := ℝ)).mpr hnat

/--
Frontier comparison step: once the combinatorial cover route gives `len ≤ 2 * B`, any
separate comparison `2 * B ≤ sphereCodeBound effectiveDim` discharges `hSphereLen`.
-/
theorem sphere_len_of_residual_real_le_two_mul_B {M : Type*}
    (D : DirectionSelectionCertificate M) (B : ℕ)
    (hLen : (D.residuals.length : ℝ) ≤ 2 * (B : ℝ))
    (hCompare : 2 * (B : ℝ) ≤ D.sphereCodeBound D.effectiveDim) :
    (D.residuals.length : ℝ) ≤ D.sphereCodeBound D.effectiveDim :=
  le_trans hLen hCompare

/--
Exact-count / plane-cover route to the `hSphereLen` inequality required by direction
selection certificates.
-/
theorem hSphereLen_of_direction_plane_cover_bound {M : Type*}
    (D : DirectionSelectionCertificate M) (W : PlaneWitnessMap M) (Q : Finset Plane)
    (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ D.residuals, planeCenterOfResidual W D.residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q))
    (hK : D.residuals.length ≤ K_exactUnionCard Q intersections)
    (B : ℕ) (hQB : Q.card ≤ B)
    (hBoundAtDim : 2 * (B : ℝ) ≤ D.sphereCodeBound D.effectiveDim) :
    (D.residuals.length : ℝ) ≤ D.sphereCodeBound D.effectiveDim := by
  have hLen : (D.residuals.length : ℝ) ≤ 2 * (B : ℝ) :=
    residual_length_real_le_two_mul_B_cast_of_direction_plane_cover
      D W Q intersections hCover hne hloc hK B hQB
  exact sphere_len_of_residual_real_le_two_mul_B D B hLen hBoundAtDim

/--
Constructor helper: build a direction-selection certificate from the usual data plus
the exact-count / planar-cover route to `hSphereLen`.
-/
def DirectionSelectionCertificate.of_plane_cover_bound {M : Type*}
    (shared : SATSharedManifold M)
    (residuals : List (SATResidual M))
    (threshold : ℝ)
    (annulusModel : LocalShellAnnulusModel)
    (residualPoint : SATResidual M → ResidualPoint M)
    (canonicalDir : SATResidual M → UnitVector shared.rapiditySphere)
    (distinctDirs : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ → canonicalDir r₁ ≠ canonicalDir r₂)
    (minAngleFromTip : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ →
      angle shared (canonicalDir r₁) (canonicalDir r₂) ≥ 0)
    (effectiveDim logBoundConst : ℕ)
    (hEffectiveDim : effectiveDim ≤ logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1))
    (sphereCodeBound : ℕ → ℝ)
    (W : PlaneWitnessMap M) (Q : Finset Plane) (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ residuals, planeCenterOfResidual W residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections annulusModel.shellRadius q (intersections q))
    (hK : residuals.length ≤ K_exactUnionCard Q intersections)
    (B : ℕ) (hQB : Q.card ≤ B)
    (hBoundAtDim : 2 * (B : ℝ) ≤ sphereCodeBound effectiveDim) :
    DirectionSelectionCertificate M where
  shared := shared
  residuals := residuals
  threshold := threshold
  annulusModel := annulusModel
  residualPoint := residualPoint
  canonicalDir := canonicalDir
  distinctDirs := distinctDirs
  minAngleFromTip := minAngleFromTip
  effectiveDim := effectiveDim
  logBoundConst := logBoundConst
  hEffectiveDim := hEffectiveDim
  sphereCodeBound := sphereCodeBound
  hSphereLen := by
    have hLen : ((residuals.length : ℕ) : ℝ) ≤ sphereCodeBound effectiveDim := by
      have hLen2B : ((residuals.length : ℕ) : ℝ) ≤ 2 * (B : ℝ) := by
        have hnat : residuals.length ≤ 2 * B :=
          residualCount_le_two_mul_countBound_of_plane annulusModel.shellRadius Q intersections residuals.length
            hne hloc hK B hQB
        simpa using (Nat.cast_le (α := ℝ)).mpr hnat
      exact le_trans hLen2B hBoundAtDim
    simpa using hLen

/--
Gap-bridge helper: build `SATRapidityGapBridge` directly from the standard gap data plus
the plane-cover / exact-count route to the packing field.
-/
def SATRapidityGapBridge.of_plane_cover_bound {M : Type*}
    (shared : SATSharedManifold M)
    (residuals : List (SATResidual M))
    (threshold : ℝ)
    (annulusModel : LocalShellAnnulusModel)
    (residualPoint : SATResidual M → ResidualPoint M)
    (canonicalDir : SATResidual M → UnitVector shared.rapiditySphere)
    (effectiveDim logBoundConst : ℕ)
    (sphereCodeBound : ℕ → ℝ)
    (hDirRealization : ∀ r : SATResidual M,
      ∃ I : ShellIntersectionSet M,
        I = localShellIntersections shared annulusModel (residualPoint r))
    (hDistinctDir : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ → canonicalDir r₁ ≠ canonicalDir r₂)
    (hMinAngle : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ →
      angle shared (canonicalDir r₁) (canonicalDir r₂) ≥ 0)
    (hEffectiveDim : effectiveDim ≤ logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1))
    (W : PlaneWitnessMap M) (Q : Finset Plane) (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ residuals, planeCenterOfResidual W residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections annulusModel.shellRadius q (intersections q))
    (hK : residuals.length ≤ K_exactUnionCard Q intersections)
    (B : ℕ) (hQB : Q.card ≤ B)
    (hBoundAtDim : 2 * (B : ℝ) ≤ sphereCodeBound effectiveDim) :
    SATRapidityGapBridge M where
  shared := shared
  residuals := residuals
  threshold := threshold
  annulusModel := annulusModel
  residualPoint := residualPoint
  canonicalDir := canonicalDir
  effectiveDim := effectiveDim
  logBoundConst := logBoundConst
  sphereCodeBound := sphereCodeBound
  hDirRealization := hDirRealization
  hDistinctDir := hDistinctDir
  hMinAngle := hMinAngle
  hEffectiveDim := hEffectiveDim
  hSphereLen := by
    let D : DirectionSelectionCertificate M :=
      DirectionSelectionCertificate.of_plane_cover_bound
        shared residuals threshold annulusModel residualPoint canonicalDir
        hDistinctDir hMinAngle effectiveDim logBoundConst hEffectiveDim sphereCodeBound
        W Q intersections hCover hne hloc hK B hQB hBoundAtDim
    simpa [D] using D.hSphereLen

/--
Plane-cover route all the way to `SATRapidityGeometricCollapse` once the successor-step
control equalities and polynomial comparison are supplied.
-/
def SATRapidityGeometricCollapse.of_plane_cover_bound {M : Type*}
    (shared : SATSharedManifold M)
    (residuals : List (SATResidual M))
    (threshold : ℝ)
    (annulusModel : LocalShellAnnulusModel)
    (residualPoint : SATResidual M → ResidualPoint M)
    (canonicalDir : SATResidual M → UnitVector shared.rapiditySphere)
    (effectiveDim logBoundConst : ℕ)
    (sphereCodeBound : ℕ → ℝ)
    (hDirRealization : ∀ r : SATResidual M,
      ∃ I : ShellIntersectionSet M,
        I = localShellIntersections shared annulusModel (residualPoint r))
    (hDistinctDir : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ → canonicalDir r₁ ≠ canonicalDir r₂)
    (hMinAngle : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ →
      angle shared (canonicalDir r₁) (canonicalDir r₂) ≥ 0)
    (hEffectiveDim : effectiveDim ≤ logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1))
    (W : PlaneWitnessMap M) (Q : Finset Plane) (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ residuals, planeCenterOfResidual W residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections annulusModel.shellRadius q (intersections q))
    (hK : residuals.length ≤ K_exactUnionCard Q intersections)
    (B : ℕ) (hQB : Q.card ≤ B)
    (hBoundAtDim : 2 * (B : ℝ) ≤ sphereCodeBound effectiveDim)
    (control : SuccessorStepResidualControl M)
    (hShared : control.shared = shared)
    (hLen : residuals.length = control.arityResiduals.length)
    (hPoly : sphereCodeBound effectiveDim ≤ sphereCodeBound (control.shared.varDim + control.shared.clauseDim)) :
    SATRapidityGeometricCollapse M :=
  (SATRapidityGapBridge.of_plane_cover_bound
    shared residuals threshold annulusModel residualPoint canonicalDir effectiveDim logBoundConst sphereCodeBound
    hDirRealization hDistinctDir hMinAngle hEffectiveDim
    W Q intersections hCover hne hloc hK B hQB hBoundAtDim).toGeometricCollapse control hShared hLen hPoly

/--
`K_exact ≤ 2 * #Q` using `D.annulusModel.shellRadius` and planar witnesses on `Q`.

The witness map and cover hypothesis are **documentation-only** (unused in proof):
they record the intended linkage “residual centers lie in `Q`” for a chosen
`PlaneWitnessMap` and residual list.
-/
theorem K_exactUnionCard_le_two_mul_of_direction_annulus
    {M : Type*} (D : DirectionSelectionCertificate M)
    (_W : PlaneWitnessMap M) (Q : Finset Plane) (intersections : Plane → Finset Plane)
    (_cover : ∀ r ∈ D.residuals, planeCenterOfResidual _W D.residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q)) :
    K_exactUnionCard Q intersections ≤ 2 * Q.card :=
  K_exactUnionCard_le_two_mul_of_planeLocalShell D.annulusModel.shellRadius Q intersections hne hloc

/--
If `|Q| ≤ B` and the same hypotheses as `K_exactUnionCard_le_two_mul_of_direction_annulus` hold on fibers,
then `K_exact ≤ 2 * B` (polynomial slot on `#Q` when `B` comes from `ArcRibbonLatticeCardBound`).
-/
theorem K_exactUnionCard_le_two_mul_bound_of_direction_annulus
    {M : Type*} (D : DirectionSelectionCertificate M)
    (_W : PlaneWitnessMap M) (Q : Finset Plane) (intersections : Plane → Finset Plane)
    (_cover : ∀ r ∈ D.residuals, planeCenterOfResidual _W D.residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q))
    (B : ℕ) (hQB : Q.card ≤ B) :
    K_exactUnionCard Q intersections ≤ 2 * B :=
  K_exactUnionCard_le_two_mul_countBound D.annulusModel.shellRadius Q intersections hne hloc B hQB

/--
If the exact-count frontier itself is chosen as the sphere-code slot, then the
plane-cover route discharges `hSphereLen` immediately.
-/
theorem hSphereLen_of_direction_plane_cover_exact_frontier {M : Type*}
    (D : DirectionSelectionCertificate M) (W : PlaneWitnessMap M) (Q : Finset Plane)
    (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ D.residuals, planeCenterOfResidual W D.residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q))
    (hK : D.residuals.length ≤ K_exactUnionCard Q intersections)
    (B : ℕ) (hQB : Q.card ≤ B)
    (hFrontier : D.sphereCodeBound D.effectiveDim = 2 * (B : ℝ)) :
    (D.residuals.length : ℝ) ≤ D.sphereCodeBound D.effectiveDim := by
  have hLen : (D.residuals.length : ℝ) ≤ 2 * (B : ℝ) :=
    residual_length_real_le_two_mul_B_cast_of_direction_plane_cover
      D W Q intersections hCover hne hloc hK B hQB
  simpa [hFrontier] using hLen

/--
Specialized constructor when the sphere-code slot is instantiated exactly by the planar
count frontier `2 * B` at `effectiveDim`.
-/
def DirectionSelectionCertificate.of_plane_cover_exact_frontier {M : Type*}
    (shared : SATSharedManifold M)
    (residuals : List (SATResidual M))
    (threshold : ℝ)
    (annulusModel : LocalShellAnnulusModel)
    (residualPoint : SATResidual M → ResidualPoint M)
    (canonicalDir : SATResidual M → UnitVector shared.rapiditySphere)
    (distinctDirs : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ → canonicalDir r₁ ≠ canonicalDir r₂)
    (minAngleFromTip : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ →
      angle shared (canonicalDir r₁) (canonicalDir r₂) ≥ 0)
    (effectiveDim logBoundConst : ℕ)
    (hEffectiveDim : effectiveDim ≤ logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1))
    (sphereCodeBound : ℕ → ℝ)
    (W : PlaneWitnessMap M) (Q : Finset Plane) (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ residuals, planeCenterOfResidual W residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections annulusModel.shellRadius q (intersections q))
    (hK : residuals.length ≤ K_exactUnionCard Q intersections)
    (B : ℕ) (hQB : Q.card ≤ B)
    (hFrontier : sphereCodeBound effectiveDim = 2 * (B : ℝ)) :
    DirectionSelectionCertificate M where
  shared := shared
  residuals := residuals
  threshold := threshold
  annulusModel := annulusModel
  residualPoint := residualPoint
  canonicalDir := canonicalDir
  distinctDirs := distinctDirs
  minAngleFromTip := minAngleFromTip
  effectiveDim := effectiveDim
  logBoundConst := logBoundConst
  hEffectiveDim := hEffectiveDim
  sphereCodeBound := sphereCodeBound
  hSphereLen := by
    have hLen : ((residuals.length : ℕ) : ℝ) ≤ sphereCodeBound effectiveDim := by
      have hLen2B : ((residuals.length : ℕ) : ℝ) ≤ 2 * (B : ℝ) := by
        have hnat : residuals.length ≤ 2 * B :=
          residualCount_le_two_mul_countBound_of_plane annulusModel.shellRadius Q intersections residuals.length
            hne hloc hK B hQB
        simpa using (Nat.cast_le (α := ℝ)).mpr hnat
      simpa [hFrontier] using hLen2B
    simpa using hLen

/--
Exact-frontier specialization at the gap-bridge level: if the sphere-code slot equals
`2 * B` at `effectiveDim`, the gap bridge can be built directly from the plane-cover
route with no separate comparison inequality.
-/
def SATRapidityGapBridge.of_plane_cover_exact_frontier {M : Type*}
    (shared : SATSharedManifold M)
    (residuals : List (SATResidual M))
    (threshold : ℝ)
    (annulusModel : LocalShellAnnulusModel)
    (residualPoint : SATResidual M → ResidualPoint M)
    (canonicalDir : SATResidual M → UnitVector shared.rapiditySphere)
    (effectiveDim logBoundConst : ℕ)
    (sphereCodeBound : ℕ → ℝ)
    (hDirRealization : ∀ r : SATResidual M,
      ∃ I : ShellIntersectionSet M,
        I = localShellIntersections shared annulusModel (residualPoint r))
    (hDistinctDir : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ → canonicalDir r₁ ≠ canonicalDir r₂)
    (hMinAngle : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ →
      angle shared (canonicalDir r₁) (canonicalDir r₂) ≥ 0)
    (hEffectiveDim : effectiveDim ≤ logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1))
    (W : PlaneWitnessMap M) (Q : Finset Plane) (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ residuals, planeCenterOfResidual W residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections annulusModel.shellRadius q (intersections q))
    (hK : residuals.length ≤ K_exactUnionCard Q intersections)
    (B : ℕ) (hQB : Q.card ≤ B)
    (hFrontier : sphereCodeBound effectiveDim = 2 * (B : ℝ)) :
    SATRapidityGapBridge M where
  shared := shared
  residuals := residuals
  threshold := threshold
  annulusModel := annulusModel
  residualPoint := residualPoint
  canonicalDir := canonicalDir
  effectiveDim := effectiveDim
  logBoundConst := logBoundConst
  sphereCodeBound := sphereCodeBound
  hDirRealization := hDirRealization
  hDistinctDir := hDistinctDir
  hMinAngle := hMinAngle
  hEffectiveDim := hEffectiveDim
  hSphereLen := by
    let D : DirectionSelectionCertificate M :=
      DirectionSelectionCertificate.of_plane_cover_exact_frontier
        shared residuals threshold annulusModel residualPoint canonicalDir
        hDistinctDir hMinAngle effectiveDim logBoundConst hEffectiveDim sphereCodeBound
        W Q intersections hCover hne hloc hK B hQB hFrontier
    simpa [D] using D.hSphereLen

/--
Exact-frontier specialization all the way to geometric collapse.
-/
def SATRapidityGeometricCollapse.of_plane_cover_exact_frontier {M : Type*}
    (shared : SATSharedManifold M)
    (residuals : List (SATResidual M))
    (threshold : ℝ)
    (annulusModel : LocalShellAnnulusModel)
    (residualPoint : SATResidual M → ResidualPoint M)
    (canonicalDir : SATResidual M → UnitVector shared.rapiditySphere)
    (effectiveDim logBoundConst : ℕ)
    (sphereCodeBound : ℕ → ℝ)
    (hDirRealization : ∀ r : SATResidual M,
      ∃ I : ShellIntersectionSet M,
        I = localShellIntersections shared annulusModel (residualPoint r))
    (hDistinctDir : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ → canonicalDir r₁ ≠ canonicalDir r₂)
    (hMinAngle : ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ →
      angle shared (canonicalDir r₁) (canonicalDir r₂) ≥ 0)
    (hEffectiveDim : effectiveDim ≤ logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1))
    (W : PlaneWitnessMap M) (Q : Finset Plane) (intersections : Plane → Finset Plane)
    (hCover : ∀ r ∈ residuals, planeCenterOfResidual W residualPoint r ∈ Q)
    (hne : ∀ q ∈ Q, q ≠ 0)
    (hloc : ∀ q ∈ Q, planeLocalShellIntersections annulusModel.shellRadius q (intersections q))
    (hK : residuals.length ≤ K_exactUnionCard Q intersections)
    (B : ℕ) (hQB : Q.card ≤ B)
    (hFrontier : sphereCodeBound effectiveDim = 2 * (B : ℝ))
    (control : SuccessorStepResidualControl M)
    (hShared : control.shared = shared)
    (hLen : residuals.length = control.arityResiduals.length)
    (hPoly : sphereCodeBound effectiveDim ≤ sphereCodeBound (control.shared.varDim + control.shared.clauseDim)) :
    SATRapidityGeometricCollapse M :=
  (SATRapidityGapBridge.of_plane_cover_exact_frontier
    shared residuals threshold annulusModel residualPoint canonicalDir effectiveDim logBoundConst sphereCodeBound
    hDirRealization hDistinctDir hMinAngle hEffectiveDim
    W Q intersections hCover hne hloc hK B hQB hFrontier).toGeometricCollapse control hShared hLen hPoly

/--
Single conservative hypothesis collapsing the remaining downstream bridge steps:
a ribbon-section cover identifies the residual frontier with a concrete annulus family,
supplies the exact-count domination, and gives the polynomial cardinality slot.

This does **not** replace the separate geometric task of constructing the local ribbon
section itself; rather, it packages the strongest currently reachable theorem once that
single cover witness is supplied.
-/
structure RibbonCoverCollapseData (M : Type*)
    (D : DirectionSelectionCertificate M) (control : SuccessorStepResidualControl M) where
  witness : LocalRibbonSectionWitness M
  family : AnnulusLatticeFamily D.annulusModel.shellRadius D.annulusModel.thresholdWidth
  intersections : Plane → Finset Plane
  hCover : ∀ r ∈ D.residuals, planeCenterOfResidual witness.toPlaneWitnessMap D.residualPoint r ∈ family.carrier
  hne : ∀ q ∈ family.carrier, q ≠ 0
  hloc : ∀ q ∈ family.carrier,
    planeLocalShellIntersections D.annulusModel.shellRadius q (intersections q)
  hK : D.residuals.length ≤ K_exactUnionCard family.carrier intersections
  varDim : ℕ
  clauseDim : ℕ
  τBits : ℕ
  countBound : ℕ → ℕ → ℕ → ℕ
  hCard : family.carrier.card ≤ countBound varDim clauseDim τBits
  hShared : control.shared = D.shared
  hLen : D.residuals.length = control.arityResiduals.length
  hCountFrontier : 2 * (countBound varDim clauseDim τBits : ℝ) ≤ D.sphereCodeBound D.effectiveDim
  hPoly : D.sphereCodeBound D.effectiveDim ≤
    D.sphereCodeBound (control.shared.varDim + control.shared.clauseDim)

/--
From one ribbon-cover collapse witness, the remaining steps 2–5 all follow:

* `hK` and local fibers give the exact-count bound,
* `hCard` gives polynomial control of `#Q`,
* `hCountFrontier` discharges `hSphereLen`,
* `hShared`/`hLen`/`hPoly` finish the geometric-collapse packaging.
-/
def RibbonCoverCollapseData.toGeometricCollapse {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control) :
    SATRapidityGeometricCollapse M :=
  direction_selection_with_plane_witness_implies_geometric_collapse D control
    R.witness.toPlaneWitnessMap R.hShared R.hLen R.hPoly

/--
The same ribbon-cover collapse witness automatically supplies the exact-count-driven
`hSphereLen` bound for `D`.
-/
theorem RibbonCoverCollapseData.hSphereLen {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control) :
    (D.residuals.length : ℝ) ≤ D.sphereCodeBound D.effectiveDim := by
  have hLen : (D.residuals.length : ℝ) ≤
      2 * (R.countBound R.varDim R.clauseDim R.τBits : ℝ) :=
    residual_length_real_le_two_mul_arcRibbon_of_direction D
      { family := R.family
        varDim := R.varDim
        clauseDim := R.clauseDim
        τBits := R.τBits
        countBound := R.countBound
        hCard := R.hCard }
      R.intersections R.hne R.hloc R.hK
  exact le_trans hLen R.hCountFrontier

/--
Repackage direction selection itself through the single ribbon-cover collapse datum.
-/
def RibbonCoverCollapseData.toDirectionSelectionCertificate {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control) : DirectionSelectionCertificate M :=
  { D with hSphereLen := R.hSphereLen }

/--
Gap-bridge packaging through the same single ribbon-cover collapse datum.
-/
def RibbonCoverCollapseData.toGapBridge {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control) : SATRapidityGapBridge M :=
  (R.toDirectionSelectionCertificate).toSATRapidityGapBridge

/--
Lightweight wiring theorem for the final ribbon-cover collapse packaging already present
in this file.

This theorem is the direct formal landing zone for the proposed “annulus family `Q`
plus exact-count domination plus polynomial cardinality” route: once a caller has
already assembled the ambient direction-selection certificate `D`, successor-step
control `control`, and the single bundled witness `RibbonCoverCollapseData`, the full
geometric collapse follows immediately.

It intentionally performs no new geometric construction internally; the geometric work
is exactly the production of `R`.  The theorem exists so downstream files can cite one
named entry point matching the ribbon-cover-collapse narrative.
-/
def ribbon_cover_collapse {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control) :
    SATRapidityGeometricCollapse M :=
  R.toGeometricCollapse

/--
The same ribbon-cover witness also yields the gap bridge directly.
-/
def ribbon_cover_collapse_to_gap_bridge {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control) :
    SATRapidityGapBridge M :=
  R.toGapBridge

/--
And it upgrades the original direction-selection certificate by supplying the exact-count
driven sphere-length bound.
-/
def ribbon_cover_collapse_to_direction_selection {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control) :
    DirectionSelectionCertificate M :=
  R.toDirectionSelectionCertificate

/--
The ribbon-cover collapse witness also yields the sphere-code certificate sitting one
step downstream in the existing SAT rapidity pipeline.
-/
def ribbon_cover_collapse_to_sphere_code {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control) :
    SATRapiditySphereCodeCertificate M :=
  (R.toGeometricCollapse).toSphereCodeCertificate

/--
Fully packaged closure into the existing polynomial residual-budget endpoint.

This is the strongest end-to-end theorem currently justified by the repository’s proved
bridge stack:

`RibbonCoverCollapseData`
→ `SATRapidityGeometricCollapse`
→ `SATRapiditySphereCodeCertificate`
→ `SATRapidityPackingCertificate`
→ `HasPolynomialResidualBudget`.

The remaining side conditions are exactly the already-existing nonnegativity and
threshold-frontier comparison hypotheses required by the downstream bridge lemmas.
-/
theorem ribbon_cover_collapse_hasPolynomialResidualBudget {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control)
    (polyBound : ℕ → ℝ)
    (hPolyThreshold : control.rapidThreshold ≤
      polyBound (control.shared.varDim + control.shared.clauseDim))
    (hPolyNonneg : 0 ≤ polyBound (control.shared.varDim + control.shared.clauseDim))
    (hCodeNonneg : 0 ≤ D.sphereCodeBound (control.shared.varDim + control.shared.clauseDim))
    (hResidualNonneg : ∀ ε ∈ control.arityResiduals, 0 ≤ ε) :
    HasPolynomialResidualBudget
      (fun n => D.sphereCodeBound n * polyBound n)
      (control.shared.varDim + control.shared.clauseDim)
      control.arityResiduals := by
  simpa [ribbon_cover_collapse_to_sphere_code] using
    sphereCodeCertificate_hasPolynomialResidualBudget
      (C := (R.toGeometricCollapse).toSphereCodeCertificate)
      (polyBound := polyBound)
      hPolyThreshold hPolyNonneg hCodeNonneg hResidualNonneg

/--
ATSP/oracle-style single-entry bridge: a ribbon-cover collapse witness supplies the
geometric slack term, while any additional certified tensor/rapidity/axis channels can
be summed exactly as in `ATSPWorstCaseCertified.geometric_oracle_bridge_implies_nat_root_envelope`.

This theorem does not construct those auxiliary channels; it packages the fact that once
the SAT rapidity ribbon witness has collapsed the residual frontier to a polynomial budget,
the remaining worst-case envelope statement is the already-proved ATSP-style additive-gap
transfer.
-/
theorem ribbon_cover_collapse_implies_nat_root_envelope
    {M : Type*}
    {D : DirectionSelectionCertificate M} {control : SuccessorStepResidualControl M}
    (R : RibbonCoverCollapseData M D control)
    (n : ℕ)
    (oracleWork seedWork baselineWork ε : ℝ)
    (tensorResidualErr rapidityErr axisErr : ℝ)
    (hBasePos : 0 < baselineWork)
    (hSeedGap :
      seedWork ≤ baselineWork +
        (satArityResidualSum control.arityResiduals + tensorResidualErr + rapidityErr + axisErr))
    (hOracleMono : oracleWork ≤ seedWork)
    (hResidualEnvelope :
      satArityResidualSum control.arityResiduals + tensorResidualErr + rapidityErr + axisErr ≤ ε)
    (hEpsEnvelope : ε ≤ baselineWork * satSearchRootScale n) :
    oracleWork / baselineWork ≤ satSearchEnvelope n := by
  have hGlobalGap : oracleWork ≤ baselineWork + ε := by
    have hSeedGap' : seedWork ≤ baselineWork + ε := by
      linarith
    exact le_trans hOracleMono hSeedGap'
  exact sat_near_degenerate_survivor_work_le_envelope
    n oracleWork baselineWork ε hBasePos hGlobalGap hEpsEnvelope

end Hqiv.Geometry
