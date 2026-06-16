import Hqiv.Story.S3DBNDiscreteContinuumComparison

/-!
# The de Bruijn–Newman constant, ported as a concrete Lean definition

`S3DBNLatticeInheritance` carried the classical constant `Λ` as an *abstract
field* of the `DBNLatticeInheritance` structure.  This module ports the
constant itself to a concrete Mathlib-style definition built from the repo's
`dbnHeatFamily`, and states the two classical imports as named, precisely
typed statements about *that* constant — the form required for an actual
Mathlib contribution.

## The definitions

* `dbnRealZerosAt t` — the deformed family `H_t` is **hyperbolic**: every
  zero of `dbnHeatFamily t` is real.
* `dbnRealZerosSet` — the hyperbolicity locus `{t | H_t hyperbolic}`.
* `dbnLambda` — **the de Bruijn–Newman constant**, `Λ = inf` of the locus
  (conditionally complete `sInf`; the classical facts that the locus is a
  nonempty upper ray pinned below are the named statements that follow).

## The classical statements (named, not yet proved)

* `DBNUpwardClosure` — de Bruijn (1950): heat flow preserves hyperbolicity,
  so the locus is an upper ray.  *Analytic content: the backward heat
  equation cannot create non-real zeros.*
* `DBNXiBridge` — the normalization fact `H₀(z) = (1/8)·ξ(1/2 + iz/2)` (up to
  a nonzero constant, stated normalization-robustly): the `t = 0` member of
  the family *is* the completed zeta on the critical line coordinate.
* `RodgersTaoStatement` — Rodgers–Tao (Annals 2020): `0 ≤ Λ`.
* `NewmanDBNStatement` — Newman (1976) + de Bruijn (1950) + the `ξ`-bridge:
  `RH ↔ Λ ≤ 0`.

Porting the *proofs* of the last two is a major formalization programme
(Laguerre–Pólya theory, heat-flow zero dynamics); this module ports the
*objects and statements* so the programme has a precise Lean target, and so
the repo's inheritance bridge speaks about the genuine constant rather than
an abstract real.

## What is proved unconditionally here

* `dbnHeatFamily_ne_zero_at_anchor` — for every `t ≤ 0` the family is
  nondegenerate: `H_t(0) ≠ 0` (from the strict positivity proved in
  `S3DBNDiscreteContinuumComparison`).  The backward family never collapses
  at the anchor; the hyperbolicity question is about *off-axis* zeros only.
* `dbnLambda_le_of_realZerosAt` / `le_dbnLambda_of_forall` — the `sInf`
  interface for the concrete constant.
* `dbnRealZerosAt_mono_of_upwardClosure` — the locus is an upper set, given
  de Bruijn's closure.
* `dbnLambda_eq_zero_iff_RH` — given the two classical statements, `Λ = 0 ↔ RH`.
* `concrete_lattice_dominates_iff_RiemannHypothesis` — the honesty theorem of
  `S3DBNLatticeInheritance`, instantiated at the **concrete** constant: the
  inheritance bound `dbnLambda ≤ lambdaHQIV` is equivalent to RH.
* `concrete_dbnLatticeInheritance_iff_RiemannHypothesis` — likewise for the
  bundled bridge.
-/

namespace Hqiv.Story

open Hqiv.Physics

noncomputable section

/-! ## The hyperbolicity locus and the constant -/

/-- The deformed dBN family at time `t` is **hyperbolic**: all zeros of
`H_t` are real.  This is the property whose threshold defines `Λ`. -/
def dbnRealZerosAt (t : ℝ) : Prop :=
  ∀ z : ℂ, dbnHeatFamily t z = 0 → z.im = 0

/-- The hyperbolicity locus `{t | H_t has only real zeros}`. -/
def dbnRealZerosSet : Set ℝ :=
  {t : ℝ | dbnRealZerosAt t}

/-- **The de Bruijn–Newman constant**, as a concrete Lean term:
`Λ = inf {t | H_t has only real zeros}`.

This replaces the abstract `Lambda : ℝ` field of `DBNLatticeInheritance`
with the genuine classical object, defined from the same `dbnHeatFamily`
whose Gaussian factor was proved identical to the repo's discrete heat
kernel (`dbnGaussianFactor_eq_discreteHeatKernelWeight`). -/
def dbnLambda : ℝ :=
  sInf dbnRealZerosSet

theorem dbnLambda_def : dbnLambda = sInf {t : ℝ | ∀ z : ℂ, dbnHeatFamily t z = 0 → z.im = 0} :=
  rfl

/-! ## The classical statements, as precise Lean targets -/

/-- **de Bruijn upward closure** (de Bruijn 1950): forward heat flow preserves
hyperbolicity, so the locus is an upper ray.  Equivalently: backward flow
cannot *create* reality of zeros — the analytic mirror of the lattice
no-backprojection dichotomy (`backprojection_weight_unbounded`). -/
def DBNUpwardClosure : Prop :=
  ∀ ⦃t t' : ℝ⦄, t ≤ t' → dbnRealZerosAt t → dbnRealZerosAt t'

/-- **The `ξ`-bridge** (classical normalization, stated
normalization-robustly): the undeformed member `H₀` of the family is the
completed zeta `ξ(s) = s(s−1)·Λ(s)` read in the critical-line coordinate
`s = 1/2 + iz/2`, up to a nonzero constant.  (`completedRiemannZeta` is
Mathlib's `Λ(s) = π^{−s/2}Γ(s/2)ζ(s)`.) -/
def DBNXiBridge : Prop :=
  ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
    dbnHeatFamily 0 z =
      C * ((1 / 2 + Complex.I * z / 2) * (1 / 2 + Complex.I * z / 2 - 1) *
        completedRiemannZeta (1 / 2 + Complex.I * z / 2))

/-- **Rodgers–Tao statement** (Annals of Mathematics 191 (2020), 913–954:
"The de Bruijn–Newman constant is non-negative"): `0 ≤ Λ`.  Now a statement
about the *concrete* `dbnLambda`. -/
def RodgersTaoStatement : Prop :=
  0 ≤ dbnLambda

/-- **Newman / de Bruijn statement** (Newman 1976; de Bruijn 1950): the
Riemann Hypothesis is equivalent to `Λ ≤ 0`.  Now a statement about the
*concrete* `dbnLambda`, with Mathlib's `RiemannHypothesis` on the left. -/
def NewmanDBNStatement : Prop :=
  RiemannHypothesis ↔ dbnLambda ≤ 0

/-! ## Unconditional structure -/

/-- **The backward family is nondegenerate at the anchor**: for every
`t ≤ 0`, `H_t(0) ≠ 0`.  Strict positivity of the weighted dBN integral
(proved in `S3DBNDiscreteContinuumComparison`) means the hyperbolicity
question for the backward family concerns off-axis zeros only — the anchor
itself never vanishes. -/
theorem dbnHeatFamily_ne_zero_at_anchor {t : ℝ} (ht : t ≤ 0) :
    dbnHeatFamily t 0 ≠ 0 := by
  rw [dbnHeatFamily_at_zero]
  exact_mod_cast (dbnWeightedIntegral_pos ht).ne'

/-- `sInf` interface: any hyperbolic time bounds `Λ` from above (given the
locus is pinned below, which Rodgers–Tao supplies classically). -/
theorem dbnLambda_le_of_realZerosAt {t : ℝ} (hbdd : BddBelow dbnRealZerosSet)
    (ht : dbnRealZerosAt t) : dbnLambda ≤ t :=
  csInf_le hbdd ht

/-- `sInf` interface: a uniform lower bound on the locus bounds `Λ` from
below (given the locus is nonempty, which de Bruijn supplies classically). -/
theorem le_dbnLambda_of_forall {a : ℝ} (hne : dbnRealZerosSet.Nonempty)
    (h : ∀ t ∈ dbnRealZerosSet, a ≤ t) : a ≤ dbnLambda :=
  le_csInf hne h

/-- Given de Bruijn's upward closure, the hyperbolicity locus is an upper
set: membership propagates forward in deformation time. -/
theorem dbnRealZerosAt_mono_of_upwardClosure (h : DBNUpwardClosure)
    {t t' : ℝ} (hle : t ≤ t') (ht : t ∈ dbnRealZerosSet) :
    t' ∈ dbnRealZerosSet :=
  h hle ht

/-- Given the two classical statements, the constant is pinned to zero
exactly on RH. -/
theorem dbnLambda_eq_zero_iff_RH (hRT : RodgersTaoStatement)
    (hN : NewmanDBNStatement) :
    dbnLambda = 0 ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact hN.mpr h.le
  · intro h
    exact le_antisymm (hN.mp h) hRT

/-! ## The inheritance bridge at the concrete constant -/

/--
**Honesty theorem at the concrete constant.**  The inheritance bound
`dbnLambda ≤ lambdaHQIV` — with `dbnLambda` now the genuine de Bruijn–Newman
constant of `dbnHeatFamily`, not an abstract field — is equivalent to the
Riemann Hypothesis, given the two classical statements.  This is
`lattice_dominates_iff_RiemannHypothesis` with the abstract `Λ`
discharged onto the ported definition.
-/
theorem concrete_lattice_dominates_iff_RiemannHypothesis
    (hRT : RodgersTaoStatement) (hN : NewmanDBNStatement)
    (W : TempLadderFiniteWindowConcrete) :
    dbnLambda ≤ (W.toLambdaHQIVZero).lambdaHQIV ↔ RiemannHypothesis :=
  lattice_dominates_iff_RiemannHypothesis dbnLambda hRT hN W

/-- The bundled inheritance bridge, instantiated at the concrete constant:
inhabited iff RH. -/
theorem concrete_dbnLatticeInheritance_iff_RiemannHypothesis
    (hRT : RodgersTaoStatement) (hN : NewmanDBNStatement)
    (W : TempLadderFiniteWindowConcrete) :
    Nonempty (DBNLatticeInheritance W) ↔ RiemannHypothesis :=
  dbnLatticeInheritance_iff_RiemannHypothesis dbnLambda hRT hN W

/-- Constructor: the two classical statements plus RH produce the concrete
inheritance bridge (with `Lambda := dbnLambda`). -/
def DBNLatticeInheritance.ofConcrete
    (hRT : RodgersTaoStatement) (hN : NewmanDBNStatement)
    (W : TempLadderFiniteWindowConcrete) (hRH : RiemannHypothesis) :
    DBNLatticeInheritance W where
  Lambda := dbnLambda
  rodgers_tao := hRT
  newman_iff := hN
  lattice_dominates := by
    rw [lambdaHQIV_eq_zero_of_finiteWindowConcrete W]
    exact hN.mp hRH

end

end Hqiv.Story
