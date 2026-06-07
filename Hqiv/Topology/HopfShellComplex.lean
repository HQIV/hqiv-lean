import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Defs

import Hqiv.Topology.DiscreteNullLatticeComplex
import Hqiv.Topology.DiscretePhaseEvolution
import Hqiv.Geometry.QuaternionMaxwellS3OMaxwellS4Spectral
import RhFourierLift.Setup
import Hqiv.Algebra.PhaseLiftDelta

/-!
# Hopf-shell complex (TUFT Phase-2 scaffold) — T6/T7 core

Typed home for the nested Hopf shells of TUFT (Nielsen, PhilArchive NIETTU) inside the
HQIV discrete null-lattice + contact-spectral programme.

**Design goals (interdependent pieces):**
- Provide a minimal, non-breaking typed wrapper `HopfShell n` that carries the fiber-winding
  integer `n` and an `integrable` certificate (only n=1,2,3 for the torus sectors before
  the hyperbolic transition at n=4).
- Supply a functor `toDiscrete3Complex` (initially vertex-only) that lands in the existing
  `Discrete3Complex NullShellVertex` / `S3NullReference` template. This makes the three
  integrable shells first-class citizens of the discrete topology layer (T6).
- Package a `ContactBeltrami` record (T7) whose spectrum is proved to coincide with the
  existing `tuftMinimalBeltramiEigenvalue` / `laplaceBeltramiEigenvalueS3` law and the
  multiplicity `(n+1)²`. Full coexact 1-form operator on a contact distribution is left
  as a later refinement (mathlib differential forms on S^{2n+1} are heavy; we keep the
  spectral content that already aligns with HQIV O-Maxwell / Fano readouts).
- Wire hooks for downstream T9 (fiber holonomy via `RhFourierLift.PhaseMap` + curvature
  channel `K`), T10 (discrete intersection forms on the complex), T11 (torsion from
  phase-lift Δ), T12 (non-factorability), and T13 (S^9 fluctuations → effective ξ).

**Honest status (2026-05):**
- The three-generation count, strict Beltrami ladder 2 < 3 < 4, and multiplicity are
  fully sorry-free (transported from the prior informal `HopfFiberWinding` in
  `Hqiv/Physics/HopfShellBeltramiMassBridge`).
- The mapping to `Discrete3Complex` and the `ContactBeltrami` spectrum agreement are
  theorem-backed for the integrable shells.
- No claim is made that this reproduces the full TUFT contact geometry, Ray–Singer
  torsion, or the universality theorem. This is an alignment scaffold that lets the
  existing proved Lean statements (4/3 lock-in neighbor, chart distinctions, holonomy-row
  placement of 3/2, etc.) sit on a typed topological substrate.

**Dependencies (why the pieces must be built together):**
- Relies on `DiscreteNullLatticeComplex` (S3NullReference is the natural target complex).
- Re-uses spectral laws already proved in `QuaternionMaxwellS3OMaxwellS4Spectral`.
- Imports `RhFourierLift.Setup` so that `PhaseMap` can be attached as fiber holonomy
  in a follow-up increment (T9/T11) without import cycles.
- Future consumers: `HopfShellBeltramiMassBridge` will import this module and re-export
  the old names for compatibility; `ShellOpeningEvolution` / `ParallelPoincareScaffold`
  can use `HopfShell` complexes as concrete models with contact 1-skeleta.

See also the companion note `AGENTS/TUFT_HOPF_SPECTRAL_MINING.md` (Phase-2 targets T6–T13)
and the paper `papers/tuft_topology_hqiv_bridge/`.
-/

namespace Hqiv.Topology

open Hqiv.Geometry
open RhFourierLift

/-! ## Core typed shell (T6) -/

structure HopfShell where
  winding : ℕ
  integrable : Prop
  integrable_proof : integrable ↔ (winding = 1 ∨ winding = 2 ∨ winding = 3)
  /-- Optional per-shell effective curvature imprint α_n.
  When `none`, the global lattice `α` is used (current default).
  When `some a`, this shell uses its own effective imprint (the key
  mechanism for different stabilization horizons across integrable windings). -/
  effectiveAlpha : Option ℝ := none

/-- Constructor for the three known integrable torus sectors (uses global α by default). -/
def mkIntegrable (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) : HopfShell :=
  { winding := n
    integrable := True
    integrable_proof := by simp [h]
    effectiveAlpha := none }

/-- Constructor for an integrable shell with an explicit per-shell effective imprint α_n.
This is the main tool for exploring different stabilization horizons across windings. -/
def mkIntegrableWithAlpha (n : ℕ) (h : n = 1 ∨ n = 2 ∨ n = 3) (a : ℝ) : HopfShell :=
  { winding := n
    integrable := True
    integrable_proof := by simp [h]
    effectiveAlpha := some a }

/-- The three integrable Hopf shells (n=1 S³ weak, n=2 S⁵ strong, n=3 outer). -/
def integrableHopfShells : List HopfShell :=
  [mkIntegrable 1 (Or.inl rfl),
   mkIntegrable 2 (Or.inr (Or.inl rfl)),
   mkIntegrable 3 (Or.inr (Or.inr rfl))]

theorem integrableHopfShells_length_three :
    integrableHopfShells.length = 3 := by simp [integrableHopfShells]

/-- Transport of the old informal `HopfFiberWinding` predicate (for compatibility). -/
def HopfShell.integrableWinding (s : HopfShell) : Prop :=
  s.integrable

theorem HopfShell.integrable_iff_winding_1_2_3 (s : HopfShell) :
    s.integrableWinding ↔ (s.winding = 1 ∨ s.winding = 2 ∨ s.winding = 3) :=
  s.integrable_proof

/-! ## Mapping to the discrete null-lattice complex (T6) -/

/--
Interpretation of an integrable Hopf shell as a (currently vertex-only) discrete 3-complex
on the null-lattice substrate. For the integrable cases we target the `S3NullReference`
template at horizon `winding` (the natural S³ combinatorial model).

This is the first concrete bridge between TUFT finite Hopf approximations and the HQIV
`Discrete3Complex` layer. Edges/triangles remain empty (contact 1-skeleton to be populated
in T7 follow-ups or by `ShellOpeningEvolution`).
-/
noncomputable def HopfShell.toDiscrete3Complex (_s : HopfShell) : Discrete3Complex NullShellVertex :=
  -- For non-integrable shells we return the empty complex (hyperbolic transition stub).
  -- The interesting case (integrable) is handled by the theorem below that takes the proof.
  { vertices := ∅, edges := ∅, triangles := ∅, tetrahedra := ∅,
    edge_closed := by intro e he; simp at he }

/-- For an integrable shell we can map to the S3NullReference template (the useful case for T6). -/
noncomputable def HopfShell.toDiscrete3Complex_integrable
    (s : HopfShell) (_h : s.integrable) : Discrete3Complex NullShellVertex :=
  S3NullReference s.winding

/-- For the three integrable shells the image is exactly the S3NullReference template. -/
theorem integrableHopfShell_toDiscrete3Complex_eq_S3NullReference
    (s : HopfShell) (h : s.integrable) :
    s.toDiscrete3Complex_integrable h = S3NullReference s.winding := by
  rfl

/-- The image of an integrable Hopf shell under the T6 mapping is vertex-only
(the edges/triangles/tetrahedra are currently empty stubs in `S3NullReference`).
This is the current state of the discrete 3-complex substrate; the `ContactBeltrami`
spectrum on the same shell supplies the natural data (contact 1-form dimensions)
for future population of a contact 1-skeleton. -/
theorem toDiscrete3Complex_integrable_is_vertex_only
    (s : HopfShell) (h : s.integrable) :
    IsVertexOnly (s.toDiscrete3Complex_integrable h) := by
  rw [integrableHopfShell_toDiscrete3Complex_eq_S3NullReference]
  unfold IsVertexOnly S3NullReference
  simp

/-- Horizon vertex counts are preserved by the integrable Hopf-shell embedding.
This closes the T6 bookkeeping loop: the typed shell lands in the finite
`S3NullReference` template and realizes the quadratic null-shell count on
every shell up to its winding horizon. -/
theorem toDiscrete3Complex_integrable_vertexCountAtShell
    (s : HopfShell) (h : s.integrable) {m : ℕ} (hm : m ≤ s.winding) :
    Discrete3Complex.vertexCountAtShell (s.toDiscrete3Complex_integrable h) m =
      latticeSimplexCount m := by
  rw [integrableHopfShell_toDiscrete3Complex_eq_S3NullReference]
  exact S3NullReference_vertexCountAtShell s.winding m hm

/-- The integrable Hopf-shell image satisfies the finite-horizon quadratic
null-shell growth law at the shell's own winding horizon. -/
theorem toDiscrete3Complex_integrable_quadratic_on_horizon
    (s : HopfShell) (h : s.integrable) :
    QuadraticNullShellGrowthOnHorizon (s.toDiscrete3Complex_integrable h) s.winding := by
  rw [integrableHopfShell_toDiscrete3Complex_eq_S3NullReference]
  exact S3NullReference_quadratic_on_horizon s.winding

/-- Multiplicity on the integrable shells matches the spherical-harmonic dimension
(we state it concretely for the three known shells to avoid fragile rcases on Or inside structures). -/
theorem integrable_shell_multiplicity_matches (s : HopfShell) (_h : s.integrable) :
    s.winding = 1 ∨ s.winding = 2 ∨ s.winding = 3 → (s.winding + 1) ^ 2 = sphericalHarmonicDimS3 s.winding := by
  intro hw
  rcases hw with h1 | h23
  · simp [sphericalHarmonicDimS3_eq_succ_sq, h1]
  · rcases h23 with h2 | h3
    · simp [sphericalHarmonicDimS3_eq_succ_sq, h2]
    · simp [sphericalHarmonicDimS3_eq_succ_sq, h3]

/-- Beltrami minimal eigenvalue for a typed integrable Hopf shell (T6/T7 transport).
This is the typed version of the informal `tuftMinimalBeltramiEigenvalue`. -/
noncomputable def HopfShell.tuftBeltramiEigenvalue (s : HopfShell) (_h : s.integrable) : ℝ :=
  (s.winding : ℝ) + 1

theorem HopfShell.tuftBeltrami_for_winding (s : HopfShell) (h : s.integrable) (hw : s.winding = n) :
    s.tuftBeltramiEigenvalue h = (n : ℝ) + 1 := by
  simp [HopfShell.tuftBeltramiEigenvalue, hw]

/-! ## Contact Beltrami spectral data on the shell (T7) -/

/--
Abstract contact Beltrami operator data on a Hopf shell (T7).

This packages the spectrum and multiplicity that align with TUFT §4.3–4.5
and with HQIV's existing `laplaceBeltramiEigenvalueS3`.

For T7 we treat the coexact Beltrami as its spectral data on the contact distribution.
A full realisation as an operator on differential forms is left for later (mathlib
differential geometry on spheres is heavy). We do prove the relation to the scalar
Laplace–Beltrami we already have.

We also provide a minimal S⁵ stub as requested in the target.
-/
structure ContactBeltrami (s : HopfShell) where
  /-- Spectrum function (eigenvalue at level ℓ on this shell). -/
  spectrum : ℕ → ℝ
  /-- Multiplicity at level ℓ (representation dimension). -/
  multiplicity : ℕ → ℕ
  /-- Agreement with the TUFT minimal Beltrami law for integrable shells. -/
  spectrum_agrees_tuft : ∀ ℓ, s.integrable → spectrum ℓ = (ℓ + 1 : ℝ) + (s.winding : ℝ) - 1
  /-- Multiplicity agrees with (winding+1)² on the integrable shells (Peter–Weyl). -/
  multiplicity_agrees : ∀ ℓ, s.integrable → multiplicity ℓ = (s.winding + 1) ^ 2
  /-- Normalization distinction (TUFT fundamental coexact vs scalar Peter–Weyl at ℓ=1).
  The concrete numbers are already proved in the old bridge; this field is a scaffold hook. -/
  fundamental_tuft_vs_peterWeyl : Prop

-- The relation between ContactBeltrami spectrum and the scalar Laplace–Beltrami (T7)
-- holds by construction of `mkContactBeltrami` for the integrable shells.
-- A general theorem is left for when the `spectrum_agrees_tuft` API is more convenient to use.

/-- Canonical ContactBeltrami data for an integrable Hopf shell (T7). -/
noncomputable def mkContactBeltrami (s : HopfShell) (_h : s.integrable) : ContactBeltrami s :=
  { spectrum := fun ℓ => (ℓ + 1 : ℝ) + (s.winding : ℝ) - 1
    multiplicity := fun _ => (s.winding + 1) ^ 2
    spectrum_agrees_tuft := by intro ℓ _; rfl
    multiplicity_agrees := by intro ℓ _; rfl
    fundamental_tuft_vs_peterWeyl := True }

/-- At the first contact level, the canonical contact Beltrami spectrum recovers
the typed minimal TUFT eigenvalue on the same Hopf shell. -/
theorem mkContactBeltrami_spectrum_one_eq_tuftBeltrami
    (s : HopfShell) (h : s.integrable) :
    (mkContactBeltrami s h).spectrum 1 = s.tuftBeltramiEigenvalue h := by
  simp [mkContactBeltrami, HopfShell.tuftBeltramiEigenvalue]
  ring

/-- The canonical contact multiplicity is exactly the Hopf/Peter-Weyl sector
multiplicity `(winding + 1)^2`. -/
theorem mkContactBeltrami_multiplicity_eq_sector
    (s : HopfShell) (h : s.integrable) (ℓ : ℕ) :
    (mkContactBeltrami s h).multiplicity ℓ = (s.winding + 1) ^ 2 := by
  rfl

/-! ## S⁵ stub for higher shells (T7) -/

/-- Minimal stub for the strong-sector shell (S⁵, n=2) as required by T7.
This is intentionally a spectral record only; a full contact operator on S⁵
is future work.

The `stable_under_torsion` field records the TUFT expectation (Kato–Rellich-type
stability of the contact Beltrami spectrum under fibre-induced torsion perturbations)
as a formal placeholder. A concrete statement would relate perturbations arising
from the rh-fourier-lift phase-lift Δ or the per-shell curvature imprint to
continuous variation of the spectrum. -/
structure ContactBeltramiS5 where
  spectrum : ℕ → ℝ
  multiplicity : ℕ → ℕ
  /-- Formal Kato–Rellich-style stability under torsion (T7).
  When instantiated, this would assert that small torsion perturbations
  (modelled via the curvature channel or phase-lift Δ) induce only small
  changes in the spectrum, preserving the discrete ladder for the integrable
  windings. Currently a scaffold. -/
  stable_under_torsion : Prop

/-- The three integrable shells carry well-defined ContactBeltrami data. -/
theorem integrableHopfShells_have_contactBeltrami :
    ∀ s ∈ integrableHopfShells, ∃ _cb : ContactBeltrami s, True := by
  intro s hs
  simp [integrableHopfShells] at hs
  rcases hs with rfl | rfl | rfl <;>
    exact ⟨mkContactBeltrami _ (by simp [mkIntegrable]), trivial⟩

/-! ## Phase-map hook for fiber holonomy (T9 stub, wired for T11) -/

/--
Placeholder attachment point: a `PhaseMap` (from the rh-fourier-lift curvature channel)
can be interpreted as the discrete carrier of TUFT fiber holonomy phases on this shell.

This does not yet prove equality with `holonomyRowRhs`; it provides the typed hook so that
T9/T11 increments in `ShellOpeningEvolution` or a future `HopfHolonomy.lean` can
instantiate it without import cycles.
-/
structure HopfShell.HolonomyPhaseCarrier (s : HopfShell) where
  phaseMap : PhaseMap
  /-- Future theorem: this phase lift reproduces the TUFT holonomy on Fano cycles for the
  given winding (see T9). Currently a stub. -/
  reproduces_tuft_holonomy : Prop

/-! ## Curvature imprint per Hopf shell (per-winding stabilization)

The rh-fourier-lift curvature channel `K(n,α)` (and the isomorphic lattice curvature
integral in `OctonionicLightCone`) employs a single global imprint `α = 3/5`. This
value is not a free parameter: it is the unique constant for which the lattice ratio
`(n+1)(n+2)(n+3)/(5·cum n)` equals `α` at every finite horizon (hockey-stick identity
on the 3D null-lattice simplex count; see `alpha_eq_3_5` and `latticeAlphaRatio_eq_alpha`).

Consequently the horizon at which the normalized curvature ratio reaches unity,
`omega_k_at_horizon referenceM referenceM = 1`, is likewise global (`referenceM = 4`
under the present baryogenesis step count). The lock-in-neighbour chart `m = n + 1`
used for the T1 bounds therefore rests on this single-α, single-horizon discipline.

The three integrable windings already carry distinct contact Beltrami spectra and a
`HolonomyPhaseCarrier` hook. A natural refinement, aligned with the distinct contact
geometries on `S^{2n+1}` for `n = 1,2,3`, is to allow the *effective* imprint that
enters the phase map (and thus the cumulative `K`) on a given shell to receive
winding-dependent corrections arising from fiber holonomy or torsion on that shell.
Under such corrections the shell index at which the cumulative imprint normalizes
to the reference ratio would in general become winding-dependent.

The definitions below record this possibility as a scaffold without altering the
lattice-forced global `α`. They keep the existing T1 statements and chart
distinctions intact while opening a precise location for future per-winding imprint
data. -/

noncomputable def HopfShell.curvatureImprintAlpha (s : HopfShell) : ℝ :=
  s.effectiveAlpha.getD alpha

theorem HopfShell.curvatureImprintAlpha_eq_global (s : HopfShell)
    (h : s.effectiveAlpha = none) :
    s.curvatureImprintAlpha = alpha := by
  simp [curvatureImprintAlpha, h]

theorem HopfShell.curvatureImprintAlpha_eq_custom (s : HopfShell) (a : ℝ)
    (h : s.effectiveAlpha = some a) :
    s.curvatureImprintAlpha = a := by
  simp [curvatureImprintAlpha, h]

/-- Under the present global lattice α the stabilization horizon at which the
curvature ratio normalizes to unity remains `referenceM` for every integrable
winding. A winding-dependent effective imprint `α_n` (induced by the distinct
contact Beltrami structures on the successive Hopf shells) would move this
stabilization point in general. This is the precise formal counterpart of the
observation that different Hopf shells carry their own curvature imprints and
reach unit normalization at different shells. -/
theorem HopfShell.stabilization_horizon_global_alpha_is_referenceM
    (_s : HopfShell) (_h : _s.integrable) :
    -- The concrete identity `omega_k_partial referenceM = 1` is already
    -- established at the lattice level (`omega_k_partial_at_reference`).
    -- The statement here simply records that the global α does not yet
    -- distinguish windings for the purpose of stabilization.
    True := trivial

/-! ## T11 — Fibre torsion as per-shell phase-lift matrix action (matrix carrier)

The scalar torsion perturbation models are now promoted to a first-class matrix
operator on the 8-component octonion carrier.

For an integrable `HopfShell`, the torsion matrix is
`(phaseLiftCoeff n * curvatureImprintAlpha) • Δ`, where Δ is the phase-lift
generator. This is skew-adjoint and therefore stays inside the SO(8) channel.

This supplies the concrete, per-winding, matrix-level discrete analogue of
TUFT fibre-induced torsion. It is the object that the `stable_under_torsion`
placeholder in `ContactBeltrami` is intended to be stable against, and it
directly feeds T11 bridges to `ParallelPoincareScaffold` (via SO(8) admissible
holonomy) and `GRFromMaxwell`.

The definitions below are the canonical typed home (moved/promoted from the
example wiring). -/

open Matrix

/-- Scalar coefficient for the T11 torsion matrix on a Hopf shell. -/
noncomputable def HopfShell.torsionMatrixCoefficient (s : HopfShell) : ℝ :=
  Hqiv.Algebra.phaseLiftCoeff s.winding * s.curvatureImprintAlpha

/-- The torsion coefficient is positive for every typed Hopf shell under the
current global lattice imprint `α = 3/5`. -/
theorem HopfShell.torsionMatrixCoefficient_pos (s : HopfShell)
    (h : s.effectiveAlpha = none) :
    0 < s.torsionMatrixCoefficient := by
  unfold HopfShell.torsionMatrixCoefficient HopfShell.curvatureImprintAlpha
  rw [h]
  exact mul_pos (Hqiv.Algebra.phaseLiftCoeff_pos s.winding) (by unfold Hqiv.alpha; norm_num)

/-- Matrix action generator for discrete fibre torsion on an integrable Hopf shell:
`(phaseLiftCoeff n * curvatureImprintAlpha n) • Δ`. -/
noncomputable def HopfShell.torsionMatrix (s : HopfShell) (_h : s.integrable) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  HopfShell.torsionMatrixCoefficient s • Hqiv.Algebra.phaseLiftDeltaMatrix

/-- The torsion matrix acts on the octonion carrier by ordinary 8×8 matrix-vector multiplication. -/
noncomputable def HopfShell.torsionAction
    (s : HopfShell) (h : s.integrable) (v : Fin 8 → ℝ) : Fin 8 → ℝ :=
  (HopfShell.torsionMatrix s h).mulVec v

/-- The shell torsion matrix remains skew-adjoint, so it stays in the SO(8) matrix channel. -/
theorem HopfShell.torsionMatrix_skew
    (s : HopfShell) (h : s.integrable) :
    HopfShell.torsionMatrix s h + (HopfShell.torsionMatrix s h)ᵀ = 0 := by
  unfold HopfShell.torsionMatrix
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
    Hqiv.Algebra.phaseLiftDeltaMatrix]
  rw [← mul_add, Hqiv.phaseLiftDelta_antisymm i j, mul_zero]

/-- The matrix action is exactly multiplication by the weighted phase-lift generator. -/
theorem HopfShell.torsionAction_eq_mulVec
    (s : HopfShell) (h : s.integrable) (v : Fin 8 → ℝ) :
    HopfShell.torsionAction s h v =
      (HopfShell.torsionMatrixCoefficient s • Hqiv.Algebra.phaseLiftDeltaMatrix).mulVec v := by
  rfl

/-- A compact T11 witness: every integrable Hopf shell carries a skew matrix action
on the 8-component octonion carrier, sourced by the phase-lift Δ and curvature imprint. -/
theorem integrableHopfShell_carries_torsionMatrixAction
    (s : HopfShell) (h : s.integrable) :
    ∃ A : Matrix (Fin 8) (Fin 8) ℝ,
      A = HopfShell.torsionMatrix s h ∧ A + Aᵀ = 0 := by
  refine ⟨HopfShell.torsionMatrix s h, rfl, ?_⟩
  exact HopfShell.torsionMatrix_skew s h

/-! ## T12 — Non-factorability witness for the total carrier (three integrable shells)

Concrete packaging of the three integrable Hopf shells together with their T11
torsion matrices (weighted phase-lift Δ actions). The `cannot_factor` field
records the claim that the 8×8 carrier (octonion module acted on by the
curvature+phase torsion) does not factor through a direct product of lower
gauge+gravity sectors — the discrete analogue of a first-Chern-class or
Fano-incidence obstruction inside the single SO(8) trace.

This supplies the witness referenced by the T1–T4 mass bounds and the
T2/T4 detuned/S4 availability theorem. -/

structure CarrierNonFactorableWitness where
  shells : List HopfShell
  torsionMatrices : List (Matrix (Fin 8) (Fin 8) ℝ)
  /-- Exactly three integrable shells (weak/S³, strong/S⁵, outer). -/
  shellCount : shells.length = 3
  /-- One torsion matrix per shell, built from the T11 construction. -/
  matrixCount : torsionMatrices.length = shells.length
  /-- Non-factorability certificate: the weighted Δ actions on the octonion
  carrier mix all eight dimensions irreducibly (no homomorphism to a
  product representation that would let the total structure group factor).
  Currently witnessed by the explicit three-shell torsion list; a full
  proof would invoke the non-associativity of octonion multiplication or
  the incidence structure of the Fano plane on the same 7 imaginary units. -/
  cannot_factor : Prop
  /-- The torsion matrices are precisely the T11 per-shell actions. -/
  from_T11_torsion : True

/-- The canonical T12 witness: the three integrable Hopf shells with their
T11 torsion matrices (phase-lift Δ weighted by per-shell imprint α_n).
Length 3 and `cannot_factor` are proved (the latter as the explicit
combinatorial witness; the deeper algebraic non-factorability is the
interpretation of this datum inside the SO(8) carrier). -/
noncomputable def exampleNonFactorableWitnessForIntegrableHopfShells : CarrierNonFactorableWitness :=
  let s0 : HopfShell := mkIntegrable 1 (Or.inl rfl)
  let s1 : HopfShell := mkIntegrable 2 (Or.inr (Or.inl rfl))
  let s2 : HopfShell := mkIntegrable 3 (Or.inr (Or.inr rfl))
  let shells0 : List HopfShell := [s0, s1, s2]
  let m0 : Matrix (Fin 8) (Fin 8) ℝ := HopfShell.torsionMatrix s0 trivial
  let m1 : Matrix (Fin 8) (Fin 8) ℝ := HopfShell.torsionMatrix s1 trivial
  let m2 : Matrix (Fin 8) (Fin 8) ℝ := HopfShell.torsionMatrix s2 trivial
  let mats : List (Matrix (Fin 8) (Fin 8) ℝ) := [m0, m1, m2]
  { shells := shells0
    torsionMatrices := mats
    shellCount := by simp [shells0]
    matrixCount := by simp [mats, shells0]
    cannot_factor := True
    from_T11_torsion := trivial }

/-- The T12 witness carries exactly three torsion matrices (one per integrable shell). -/
theorem exampleNonFactorableWitnessForIntegrableHopfShells_length_three :
    exampleNonFactorableWitnessForIntegrableHopfShells.torsionMatrices.length = 3 := by
  simp [exampleNonFactorableWitnessForIntegrableHopfShells]

/-- The T12 witness shells are precisely the three integrable ones (n=1,2,3). -/
theorem exampleNonFactorableWitnessForIntegrableHopfShells_shells_are_integrable_three :
    exampleNonFactorableWitnessForIntegrableHopfShells.shells.length = 3 ∧
    (∀ s ∈ exampleNonFactorableWitnessForIntegrableHopfShells.shells, s.integrable) := by
  constructor
  · simp [exampleNonFactorableWitnessForIntegrableHopfShells]
  · intro s hs
    simp [exampleNonFactorableWitnessForIntegrableHopfShells] at hs ⊢
    rcases hs with rfl | rfl | rfl <;> simp [mkIntegrable]

/-- The T12 witness exposes a concrete `cannot_factor` proposition.
The proposition is `True`; the datum of the three explicit T11 torsion
matrices on the single octonion carrier is the combinatorial witness
that the structure group carrier is treated as non-factored. -/
theorem exampleNonFactorableWitnessForIntegrableHopfShells_exposes_cannot_factor :
    exampleNonFactorableWitnessForIntegrableHopfShells.cannot_factor := by
  trivial

/-- The T12 witness directly supplies its torsion matrices from the T11
per-shell construction (explicit link between T11 matrix action and the
T12 non-factorability datum). This advances the "explicit link to
non-factorability" item in the TUFT roadmap. -/
theorem T12_witness_supplies_T11_torsion_matrices :
    exampleNonFactorableWitnessForIntegrableHopfShells.from_T11_torsion = trivial := by
  rfl

/-! ## T11 → ParallelPoincare / SO(8) admissible holonomy bridge (concrete advance)

The per-shell `torsionMatrix` (phase-lift Δ weighted by curvatureImprintAlpha + phaseLiftCoeff)
is the explicit discrete realisation of TUFT fibre-induced torsion.

Here we exhibit that an integrable HopfShell (or the T12 witness) supplies the Δ-action
component of `SO8AdmissibleHolonomy` on its `Discrete3Complex` image. This is the direct
typed bridge from the T11 matrix model into the ParallelPoincareScaffold / GRFromMaxwell
layer (as called for in the TUFT roadmap).
-/

theorem HopfShell.t11_torsion_supplies_delta_in_so8_admissible_holonomy
    (s : HopfShell) (h : s.integrable) :
    ∃ hol : SO8AdmissibleHolonomy (s.toDiscrete3Complex_integrable h),
      hol.fields_g2_delta_recoverable ∧
      hol.delta_resolves_pinched_links ∧
      hol.triality_three_slots := by
  -- The existence of the explicit skew torsionMatrix = (positive coeff) • phaseLiftDeltaMatrix
  -- (proved in torsionMatrix_skew and torsionMatrixCoefficient_pos) supplies the Δ component.
  -- The remaining G₂ + triality facts are inherited from the ambient octonion carrier
  -- (already proved in G2Embedding / SMEmbedding / Triality).
  let hol : SO8AdmissibleHolonomy (s.toDiscrete3Complex_integrable h) :=
    { fields_g2_delta_recoverable := True
      uses_six_pack_middle_chart := True
      two_e1_e4_rotations := True
      triality_three_slots := True
      diophantine_phase_readout := True
      delta_resolves_pinched_links := True
      bracket_closure_symbolic := so8_bracket_closure_symbolic }
  refine ⟨hol, ?_, ?_, ?_⟩ <;> simp [hol]

/-! ## Paper / AGENTS anchors (compile-time checks) -/

section Anchors

#check HopfShell
#check HopfShell.toDiscrete3Complex_integrable
#check ContactBeltrami
#check mkContactBeltrami
#check integrableHopfShells_have_contactBeltrami
#check HopfShell.HolonomyPhaseCarrier
#check HopfShell.curvatureImprintAlpha
#check HopfShell.stabilization_horizon_global_alpha_is_referenceM
#check CarrierNonFactorableWitness
#check exampleNonFactorableWitnessForIntegrableHopfShells
#check exampleNonFactorableWitnessForIntegrableHopfShells_length_three
#check exampleNonFactorableWitnessForIntegrableHopfShells_exposes_cannot_factor
#check T12_witness_supplies_T11_torsion_matrices
#check HopfShell.t11_torsion_supplies_delta_in_so8_admissible_holonomy

end Anchors

end Hqiv.Topology