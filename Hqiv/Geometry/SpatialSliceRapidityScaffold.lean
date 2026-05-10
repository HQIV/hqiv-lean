import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Path
import Mathlib.Data.Fin.Basic

import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.ModifiedMaxwell

/-!
# Spatial slice, shell families, and rapidity **probe** (Millennium roadmaps)

**Purpose:** coherent **types** and **hypothesis bundles** for probing the narratives in
`AGENTS/MANIFOLD_ZETA_ROADMAP.md`, `AGENTS/MILLENNIUM_UNIFIED_NARRATIVE.md`,
`AGENTS/NAVIER_STOKES_HQIV_NARRATIVE.md`, and `AGENTS/HODGE_HQIV_NARRATIVE.md` — without claiming
proofs of NS, Hodge, or Ricci integral identities.

**What is here**

* `ShellFamily` — subsets of a spatial type `M` tagged by the **same** discrete shell index `m : ℕ`
  as `effCorrected` / lattice zeta.
* `LatticeContinuumRapidityCoincidence` — pairs a **lattice** rapidity surrogate `φ·t` with a declared
  **continuum** scalar (e.g. a path functional value); includes the trivial diagonal instance.
  **Design intent (not proved):** rapidity should **select / align with** discrete lattice-ray
  coordinates (marginal “prime” steps in `LatticeFirstQuadrantEdgeCount` / `Lattice3DAxisPrimeStep`),
  reducing reliance on exhaustive angular search for composite structure at large `m` (classical
  territory: ray scans up to roughly `√m`-scale — still open as a formal bridge).
* `PhiContourFunctional` — abstract evaluator `Path a b → ℝ` (placeholder for future `∫_γ φ`).
* `GeometricScalarCurvatureSlot`, `agreesWithCombinatorialDeltaE` — numeric per-shell slot vs
  combinatorial `Hqiv.deltaE` as an **explicit** `Prop` bridge.
* `deltaE_geometricModel` — **3-manifold narrative slot**: per-shell scalar `R_vol m` (stand-in for an
  integrated scalar-curvature contribution) enters
  \(\frac{1}{m+1}(1+\alpha\,R_{\mathrm{vol}}(m))\times\) `curvature_norm_combinatorial`. **Not** an
  automatic equality with `Hqiv.deltaE` unless you prove a matching identity for `R_vol`.
* `fanoContourPeriodSum`, `fanoContourPeriodSum_eq_seven_mul` — sum of abstract contour values over the
  seven Fano vertices; constant-per-vertex case.
* `SpherePackingInfo`, `spherePackingAtShell` — discrete **probe** for “blocky \(S^2\)” bookkeeping at
  shell `m`: effective-surface proxy, divisor count of `m+1`, and fixed outer cyclic order `7` (Fano
  residue partition). **Not** a sphere-packing theorem.
* `FanoPeriodRapidityCoincidence` — hypothesis bundle identifying `timeAngle φ t` with that sum;
  `FanoPeriodRapidityCoincidence.phi_t_eq_sum` rewrites `φ * t`. With the same `(φ,t)` as in
  `zetaHQIVTerm`, see `Hqiv.Physics.HodgeRapidityZetaBridge` (`zetaHQIVTerm_eq_eff_mul_cexp_polarAngle_of_coincident_rapidity`).
* **Polar / spiral scaffold:** `polarAngleFromRapidity`, `polarRadiusShellSucc`, `polarRadiusReciprocal`,
  `rapidityPolarPoint` — discrete `(r, θ)` from `m` using the **same** `δθ'(m)` as `zetaHQIVTerm`
  (`ModifiedMaxwell.delta_theta_prime`). **Proved zeta identification:** `Hqiv.Physics.RapidityZetaPhaseBridge`
  rewrites `zetaHQIVTerm`’s phase as `cexp (I * polarAngleFromRapidity …)`. Not a chart onto `S³`; a
  projection target for slice/ray proofs.

**What is not here (still):** a full Riemannian metric tensor as a single `PseudoMetricSpace` on spacetime,
volume forms on curved `g`, a **constructed** `∫ R √g` from `g`, simply connected `π₁ = 1`, motives,
L-functions, or Navier–Stokes PDE.

**Where Euclidean shells + Lebesgue volume live:** `Hqiv.Geometry.SpatialSliceManifold` — concrete
`ShellFamily` on `SpatialSliceEuclidean3`, measurability, boundedness, and `volume < ⊤` for each shell.

Any “global functional” statement beyond that remains **conditional** on explicit `Prop` / structure fields
above — not forced by topology alone.
-/

namespace Hqiv.Geometry

open Finset
open scoped BigOperators

open Hqiv Hqiv.Physics

variable {M : Type u} [TopologicalSpace M]

/-- Subsets of `M` indexed by the discrete shell `m : ℕ` (horizon-patch narrative). -/
def ShellFamily (M : Type u) : Type u :=
  ℕ → Set M

/-- Shell regions are pairwise disjoint (typical local-chart hypothesis). -/
def ShellFamilyPairwiseDisjoint {M : Type u} (U : ShellFamily M) : Prop :=
  ∀ m n : ℕ, m ≠ n → Disjoint (U m) (U n)

/-- Auxiliary scalar field on the spatial slice (continuum `φ(x)` narrative). -/
def AuxiliaryScalarField (M : Type u) : Type u :=
  M → ℝ

/-- Abstract “contour functional” for pairing paths with `φ` (realize as integral when measures are fixed). -/
structure PhiContourFunctional (M : Type u) [TopologicalSpace M] where
  eval {a b : M} : Path a b → ℝ

/-- Lattice rapidity surrogate agrees with a declared continuum scalar. -/
structure LatticeContinuumRapidityCoincidence where
  latticeValue : ℝ
  continuumValue : ℝ
  eq : latticeValue = continuumValue

/-- Diagonal bridge: lattice and continuum values are **defined** to agree. -/
def LatticeContinuumRapidityCoincidence.refl (r : ℝ) : LatticeContinuumRapidityCoincidence where
  latticeValue := r
  continuumValue := r
  eq := rfl

theorem LatticeContinuumRapidityCoincidence.eq_timeAngle_of_refl (φ t : ℝ) :
    (LatticeContinuumRapidityCoincidence.refl (timeAngle φ t)).latticeValue = timeAngle φ t :=
  rfl

/-- Per-shell numeric slot standing in for geometric scalar-curvature data (not constructed from `g` here). -/
def GeometricScalarCurvatureSlot : Type :=
  ℕ → ℝ

/-- Integrated scalar-curvature data slot (narrative: explicit `∫ R(g) √g d^3x` contribution per shell).

In this scaffold we keep the integral abstract as a user-supplied function `m ↦ Rint(m)`.
-/
abbrev IntegratedScalarCurvatureSlot : Type :=
  GeometricScalarCurvatureSlot

/-- Explicit bridge to combinatorial `δ_E` from `OctonionicLightCone`. -/
def agreesWithCombinatorialDeltaE (geom : GeometricScalarCurvatureSlot) (m : ℕ) : Prop :=
  geom m = deltaE m

theorem agreesWithCombinatorialDeltaE_deltaE (m : ℕ) :
    agreesWithCombinatorialDeltaE deltaE m := rfl

/-- **Geometric δ_E slot:** `R_vol m` is real data per shell (narrative: integrated scalar curvature
contribution on the patch tagged by `m`). Uses canonical `Hqiv.alpha` and `curvature_norm_combinatorial`. -/
noncomputable def deltaE_geometricModel (R_vol : GeometricScalarCurvatureSlot) (m : ℕ) : ℝ :=
  (1 / (m + 1 : ℝ)) * (1 + alpha * R_vol m) * curvature_norm_combinatorial

theorem deltaE_geometricModel_eq (R_vol : GeometricScalarCurvatureSlot) (m : ℕ) :
    deltaE_geometricModel R_vol m =
      (1 / (m + 1 : ℝ)) * (1 + alpha * R_vol m) * curvature_norm_combinatorial :=
  rfl

theorem agreesWithCombinatorialDeltaE_geometricModel_iff (R_vol : GeometricScalarCurvatureSlot) (m : ℕ) :
    agreesWithCombinatorialDeltaE (fun k => deltaE_geometricModel R_vol k) m ↔
      deltaE_geometricModel R_vol m = deltaE m := by
  rfl

/-- 3-manifold narrative version of `deltaE_geometricModel` taking explicit integrated
scalar-curvature data `Rint(m)` (abstractly provided as a function). -/
noncomputable def deltaE_geometricModel_fromIntegratedScalarCurvature
    (Rint : IntegratedScalarCurvatureSlot) (m : ℕ) : ℝ :=
  deltaE_geometricModel Rint m

@[simp]
theorem deltaE_geometricModel_fromIntegratedScalarCurvature_eq
    (Rint : IntegratedScalarCurvatureSlot) (m : ℕ) :
    deltaE_geometricModel_fromIntegratedScalarCurvature Rint m =
      deltaE_geometricModel Rint m := by
  rfl

/-!
### Blocky \(S^2\) packing probe (combinatorial only)
-/

/-- Discrete data attached to shell `m`: “pixel” proxy = `effCorrected`, divisor count, Fano outer order. -/
structure SpherePackingInfo where
  eff_pixel : ℝ
  mode_divisor_count : ℕ
  /-- Fixed `7` for the mod‑7 / Fano residue story (not computed from `m`). -/
  cyclic_outer_order : ℕ

/-- Combinatorial probe at shell `m` using the same `effCorrected` ladder as zeta / detuning. -/
noncomputable def spherePackingAtShell (m : ℕ) (δ : ℝ) (_hden : RindlerDenDeltaPos δ m) : SpherePackingInfo where
  eff_pixel := effCorrected δ m
  mode_divisor_count := Finset.card (Nat.divisors (m + 1))
  cyclic_outer_order := 7

@[simp]
theorem spherePackingAtShell_eff_pixel (m : ℕ) (δ : ℝ) (_hden : RindlerDenDeltaPos δ m) :
    (spherePackingAtShell m δ _hden).eff_pixel = effCorrected δ m :=
  rfl

@[simp]
theorem spherePackingAtShell_mode_divisor_count (m : ℕ) (δ : ℝ) (_hden : RindlerDenDeltaPos δ m) :
    (spherePackingAtShell m δ _hden).mode_divisor_count = Finset.card (Nat.divisors (m + 1)) :=
  rfl

@[simp]
theorem spherePackingAtShell_cyclic_outer_order (m : ℕ) (δ : ℝ) (_hden : RindlerDenDeltaPos δ m) :
    (spherePackingAtShell m δ _hden).cyclic_outer_order = 7 :=
  rfl

/-- Packing probe is independent of step-wise rapidity: only `m` and `δ` enter. -/
theorem spherePackingAtShell_eq_of_shell_delta (m : ℕ) (δ : ℝ) (hden : RindlerDenDeltaPos δ m) :
    spherePackingAtShell m δ hden = spherePackingAtShell m δ hden :=
  rfl

/-- Cumulative lattice rapidity `φ·t` equals `timeAngle` (HQVM lapse narrative). -/
theorem latticeRapidity_eq_timeAngle (φ t : ℝ) : φ * t = timeAngle φ t := by
  simp [timeAngle]

/-!
### Polar coordinates from shell index (wave-spiral / slice projection)

Same angular factor as `Hqiv.Physics.zetaHQIVTerm` phase: `φ·t·δθ'(m)` with `δθ'` from
`ModifiedMaxwell.delta_theta_prime`. Radius choices: `m+1` (shell successor) or `1/(m+1)` (reciprocal
coordinate, same as `shellReciprocalCoord` in `DivisionAlgebraZetaScaffold`).
-/

/-- Rapidity phase weighted by a shell-indexed curvature ratio slot `ω`.

This lets the phase be defined "with respect to Ω" rather than only `φ·t`:
`δθ_Ω(m) = (φ·t) * ω(m)`. -/
noncomputable def rapidityPhaseFromOmega (φ t : ℝ) (ω : ℕ → ℝ) (m : ℕ) : ℝ :=
  timeAngle φ t * ω m

/-- Canonical choice: use the first-principles shell curvature ratio `omega_k_partial`. -/
noncomputable def rapidityPhaseFromOmegaPartial (φ t : ℝ) (m : ℕ) : ℝ :=
  rapidityPhaseFromOmega φ t omega_k_partial m

@[simp]
theorem rapidityPhaseFromOmega_eq (φ t : ℝ) (ω : ℕ → ℝ) (m : ℕ) :
    rapidityPhaseFromOmega φ t ω m = timeAngle φ t * ω m :=
  rfl

@[simp]
theorem rapidityPhaseFromOmegaPartial_eq (φ t : ℝ) (m : ℕ) :
    rapidityPhaseFromOmegaPartial φ t m = timeAngle φ t * omega_k_partial m := by
  rfl

/-- At the reference horizon (`referenceM`), `omega_k_partial = 1`, so Ω-weighted phase
reduces to the baseline time-angle `φ·t`. -/
theorem rapidityPhaseFromOmegaPartial_at_reference (φ t : ℝ)
    (hpos : 0 < curvature_integral referenceM) :
    rapidityPhaseFromOmegaPartial φ t referenceM = timeAngle φ t := by
  simp [rapidityPhaseFromOmegaPartial, rapidityPhaseFromOmega, omega_k_partial_at_reference, hpos]

/-- HQIV monogamy-locked phase channel: first-order `φ·t`. -/
noncomputable def rapidityPhaseMonogamyLocked (φ t : ℝ) : ℝ :=
  timeAngle φ t

/-- General math extension: allow integer periodicity multiplier `k`. -/
noncomputable def rapidityPhasePeriodic (φ t : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * timeAngle φ t

theorem rapidityPhasePeriodic_eq_locked_of_k_one (φ t : ℝ) :
    rapidityPhasePeriodic φ t 1 = rapidityPhaseMonogamyLocked φ t := by
  simp [rapidityPhasePeriodic, rapidityPhaseMonogamyLocked]

/-- Ω-weighted phase with integer periodicity `k`. -/
noncomputable def rapidityPhaseFromOmegaPeriodic (φ t : ℝ) (ω : ℕ → ℝ) (k m : ℕ) : ℝ :=
  (k : ℝ) * rapidityPhaseFromOmega φ t ω m

theorem rapidityPhaseFromOmegaPeriodic_eq_of_k_one (φ t : ℝ) (ω : ℕ → ℝ) (m : ℕ) :
    rapidityPhaseFromOmegaPeriodic φ t ω 1 m = rapidityPhaseFromOmega φ t ω m := by
  simp [rapidityPhaseFromOmegaPeriodic]

/-- Unit-circle point at angle `θ`. -/
noncomputable def unitCirclePoint (θ : ℝ) : ℝ × ℝ :=
  (Real.cos θ, Real.sin θ)

/-- Squared norm identity for unit-circle points. -/
theorem unitCirclePoint_normSq (θ : ℝ) :
    (unitCirclePoint θ).1 ^ 2 + (unitCirclePoint θ).2 ^ 2 = 1 := by
  simp [unitCirclePoint, Real.cos_sq_add_sin_sq]

/-- `k`-periodic match angle indexed by `j`. -/
noncomputable def periodicMatchAngle (k : ℕ) (j : Fin k) : ℝ :=
  (2 * Real.pi) * (j.val : ℝ) / (k : ℝ)

/-- `k`-periodic match point on the unit circle (roots-of-unity geometry). -/
noncomputable def periodicMatchPoint (k : ℕ) (j : Fin k) : ℝ × ℝ :=
  unitCirclePoint (periodicMatchAngle k j)

theorem periodicMatchPoint_on_unitCircle (k : ℕ) (_hk : 0 < k) (j : Fin k) :
    (periodicMatchPoint k j).1 ^ 2 + (periodicMatchPoint k j).2 ^ 2 = 1 := by
  simpa [periodicMatchPoint] using unitCirclePoint_normSq (periodicMatchAngle k j)

/-- Three-way periodic matching (`k = 3`) gives three unit-circle slots. -/
theorem periodicMatchPoint_k3_on_unitCircle (j : Fin 3) :
    (periodicMatchPoint 3 j).1 ^ 2 + (periodicMatchPoint 3 j).2 ^ 2 = 1 := by
  exact periodicMatchPoint_on_unitCircle 3 (by decide) j

/-- Four-way periodic matching (`k = 4`) gives four unit-circle slots. -/
theorem periodicMatchPoint_k4_on_unitCircle (j : Fin 4) :
    (periodicMatchPoint 4 j).1 ^ 2 + (periodicMatchPoint 4 j).2 ^ 2 = 1 := by
  exact periodicMatchPoint_on_unitCircle 4 (by decide) j

/-- Root-scale search radius for target factor arity `k` (analytic scaffold: `n^(1/k)`). -/
noncomputable def multiFactorRootScale (n k : ℕ) : ℝ :=
  (n : ℝ) ^ ((k : ℝ)⁻¹)

/-- Prime-step shell set up to the root-scale budget for arity `k`. -/
def primeStepsUpToRootScale (n k : ℕ) : Set ℕ :=
  { p : ℕ | Nat.Prime p ∧ (p : ℝ) ≤ multiFactorRootScale n k }

/-- Candidate slots tracked by a `k`-periodic rapidity phase on shell `m`. -/
noncomputable def periodicRapidityCandidateSlots (φ t : ℝ) (ω : ℕ → ℝ) (k m : ℕ) : Fin k → ℝ :=
  fun j => rapidityPhaseFromOmegaPeriodic φ t ω k m + periodicMatchAngle k j

/-- For every arity slot, the corresponding unit-circle match point is on `S¹`. -/
theorem periodicRapidityCandidateSlots_on_unitCircle (φ t : ℝ) (ω : ℕ → ℝ) (k : ℕ)
    (_hk : 0 < k) (m : ℕ) (j : Fin k) :
    (unitCirclePoint (periodicRapidityCandidateSlots φ t ω k m j)).1 ^ 2 +
      (unitCirclePoint (periodicRapidityCandidateSlots φ t ω k m j)).2 ^ 2 = 1 := by
  exact unitCirclePoint_normSq (periodicRapidityCandidateSlots φ t ω k m j)

/-- Arity-2 root-scale specialization (`√n` analytic scale). -/
theorem multiFactorRootScale_k2 (n : ℕ) :
    multiFactorRootScale n 2 = (n : ℝ) ^ ((2 : ℝ)⁻¹) := rfl

/-- Arity-3 root-scale specialization (`∛n` analytic scale). -/
theorem multiFactorRootScale_k3 (n : ℕ) :
    multiFactorRootScale n 3 = (n : ℝ) ^ ((3 : ℝ)⁻¹) := rfl

/-- Analytic domain descriptor for a rapidity class living on a `k`-sphere model. -/
structure RapidityKSphereDomain where
  /-- Sphere dimension `k` in `S^k`. -/
  kSphereDim : ℕ
  /-- Domain-active predicate for shell/class coordinates. -/
  domainActive : ℕ → Bool

/-- Class-indexed family of analytic `k`-sphere domains. -/
abbrev RapidityClassDomains : Type :=
  ℕ → RapidityKSphereDomain

/-- Rapidity phase for class `c` evaluated in its own analytic `k`-sphere domain. -/
noncomputable def rapidityPhaseFromOmegaPeriodicOnDomain
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k m : ℕ) : ℝ :=
  if (domains c).domainActive m then
    rapidityPhaseFromOmegaPeriodic φ t ω k m
  else 0

/-- Class-local periodic candidate slots on the class domain. -/
noncomputable def periodicRapidityCandidateSlotsOnDomain
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k m : ℕ) : Fin k → ℝ :=
  fun j => rapidityPhaseFromOmegaPeriodicOnDomain φ t ω domains c k m + periodicMatchAngle k j

/-- If shell `m` is active in class `c`'s domain, domain-phase agrees with global phase. -/
theorem rapidityPhaseFromOmegaPeriodicOnDomain_eq_of_active
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k m : ℕ) (hactive : (domains c).domainActive m = true) :
    rapidityPhaseFromOmegaPeriodicOnDomain φ t ω domains c k m =
      rapidityPhaseFromOmegaPeriodic φ t ω k m := by
  simp [rapidityPhaseFromOmegaPeriodicOnDomain, hactive]

/-- If shell `m` is not active in class `c`'s domain, domain-phase is zero. -/
theorem rapidityPhaseFromOmegaPeriodicOnDomain_eq_zero_of_inactive
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k m : ℕ) (hinactive : (domains c).domainActive m = false) :
    rapidityPhaseFromOmegaPeriodicOnDomain φ t ω domains c k m = 0 := by
  simp [rapidityPhaseFromOmegaPeriodicOnDomain, hinactive]

/-- Class-local candidate slots are still unit-circle points (phase shift preserves unit norm). -/
theorem periodicRapidityCandidateSlotsOnDomain_on_unitCircle
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (_hk : 0 < k) (m : ℕ) (j : Fin k) :
    (unitCirclePoint (periodicRapidityCandidateSlotsOnDomain φ t ω domains c k m j)).1 ^ 2 +
      (unitCirclePoint (periodicRapidityCandidateSlotsOnDomain φ t ω domains c k m j)).2 ^ 2 = 1 := by
  exact unitCirclePoint_normSq (periodicRapidityCandidateSlotsOnDomain φ t ω domains c k m j)

/-- Domain-local rapidity rotation action by angle increment `Δθ` (class `c`, shell `m`). -/
noncomputable def rapidityRotateOnDomain
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k m : ℕ) (Δθ : ℝ) : ℝ :=
  rapidityPhaseFromOmegaPeriodicOnDomain φ t ω domains c k m + Δθ

/-- A single periodic orbit step is a domain-local rapidity rotation by `periodicMatchAngle k j`. -/
theorem periodicRapidityCandidateSlotsOnDomain_eq_rotate
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k m : ℕ) (j : Fin k) :
    periodicRapidityCandidateSlotsOnDomain φ t ω domains c k m j =
      rapidityRotateOnDomain φ t ω domains c k m (periodicMatchAngle k j) := by
  simp [periodicRapidityCandidateSlotsOnDomain, rapidityRotateOnDomain]

/-- Cleaner additive law on raw phase values (rotation is affine by angle addition). -/
theorem rapidityRotateValue_add (θ a b : ℝ) :
    (θ + a) + b = θ + (a + b) := by ring

/-- Locked-vs-free witness: `k=1` recovers monogamy-locked phase on active domain shells. -/
theorem rapidityRotateOnDomain_locked_k1
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c m : ℕ) (hactive : (domains c).domainActive m = true) :
    rapidityPhaseFromOmegaPeriodicOnDomain φ t ω domains c 1 m = rapidityPhaseFromOmega φ t ω m := by
  simp [rapidityPhaseFromOmegaPeriodicOnDomain, rapidityPhaseFromOmegaPeriodic, hactive]

/-- Higher-order periodicity (`k ≥ 2`) is the free-rotation channel beyond the locked `k=1` slice. -/
theorem rapidityPhaseFromOmegaPeriodicOnDomain_eq_k_mul_locked
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k m : ℕ) (hactive : (domains c).domainActive m = true) :
    rapidityPhaseFromOmegaPeriodicOnDomain φ t ω domains c k m =
      (k : ℝ) * rapidityPhaseFromOmega φ t ω m := by
  simp [rapidityPhaseFromOmegaPeriodicOnDomain, rapidityPhaseFromOmegaPeriodic, hactive]

/-- `1/k`-spiral phase law on class/domain shells (`k`-sphere local scaling). -/
noncomputable def rapidityPhaseFromOmegaOneOverKOnDomain
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k m : ℕ) : ℝ :=
  if (domains c).domainActive m then
    ((k : ℝ)⁻¹) * rapidityPhaseFromOmega φ t ω m
  else 0

/-- Candidate slots for the `1/k`-spiral phase law on class/domain shells. -/
noncomputable def periodicOneOverKSpiralSlotsOnDomain
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k m : ℕ) : Fin k → ℝ :=
  fun j => rapidityPhaseFromOmegaOneOverKOnDomain φ t ω domains c k m + periodicMatchAngle k j

/-- `1/k`-spiral slots still lie on the unit-circle intersection manifold. -/
theorem periodicOneOverKSpiralSlotsOnDomain_on_unitCircle
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (_hk : 0 < k) (m : ℕ) (j : Fin k) :
    (unitCirclePoint (periodicOneOverKSpiralSlotsOnDomain φ t ω domains c k m j)).1 ^ 2 +
      (unitCirclePoint (periodicOneOverKSpiralSlotsOnDomain φ t ω domains c k m j)).2 ^ 2 = 1 := by
  exact unitCirclePoint_normSq (periodicOneOverKSpiralSlotsOnDomain φ t ω domains c k m j)

/-- Existence of an intersection slot for the `1/k`-spiral law on every nonempty class domain (`k>0`). -/
theorem periodicOneOverKSpiralSlotsOnDomain_intersection_exists
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (hk : 0 < k) (m : ℕ) :
    ∃ j : Fin k,
      (unitCirclePoint (periodicOneOverKSpiralSlotsOnDomain φ t ω domains c k m j)).1 ^ 2 +
        (unitCirclePoint (periodicOneOverKSpiralSlotsOnDomain φ t ω domains c k m j)).2 ^ 2 = 1 := by
  refine ⟨⟨0, hk⟩, ?_⟩
  exact periodicOneOverKSpiralSlotsOnDomain_on_unitCircle φ t ω domains c k hk m ⟨0, hk⟩

/-- Ω-weighted polar angle: combine curvature-ratio phase and tipping-angle channel.

`θ_Ω(m) = (φ·t * ω(m)) * δθ'(m)`. -/
noncomputable def polarAngleFromRapidityOmega (φ t : ℝ) (ω : ℕ → ℝ) (m : ℕ) : ℝ :=
  rapidityPhaseFromOmega φ t ω m * delta_theta_prime (m : ℝ)

/-- Canonical Ω-weighted polar angle using `omega_k_partial`. -/
noncomputable def polarAngleFromRapidityOmegaPartial (φ t : ℝ) (m : ℕ) : ℝ :=
  polarAngleFromRapidityOmega φ t omega_k_partial m

@[simp]
theorem polarAngleFromRapidityOmega_eq (φ t : ℝ) (ω : ℕ → ℝ) (m : ℕ) :
    polarAngleFromRapidityOmega φ t ω m =
      rapidityPhaseFromOmega φ t ω m * delta_theta_prime (m : ℝ) := rfl

@[simp]
theorem polarAngleFromRapidityOmega_eq_timeAngle_mul (φ t : ℝ) (ω : ℕ → ℝ) (m : ℕ) :
    polarAngleFromRapidityOmega φ t ω m =
      (timeAngle φ t * ω m) * delta_theta_prime (m : ℝ) := by
  rfl

theorem polarAngleFromRapidityOmega_eq_of_unitOmega (φ t : ℝ) (ω : ℕ → ℝ) (m : ℕ)
    (hω : ω m = 1) :
    polarAngleFromRapidityOmega φ t ω m = φ * t * delta_theta_prime (m : ℝ) := by
  simp [polarAngleFromRapidityOmega, rapidityPhaseFromOmega, timeAngle, hω]

theorem polarAngleFromRapidityOmegaPartial_at_reference (φ t : ℝ) (m : ℕ)
    (hpos : 0 < curvature_integral referenceM)
    (hm : m = referenceM) :
    polarAngleFromRapidityOmegaPartial φ t m = φ * t * delta_theta_prime (m : ℝ) := by
  subst hm
  have homega : omega_k_partial referenceM = 1 := omega_k_partial_at_reference hpos
  simp [polarAngleFromRapidityOmegaPartial, polarAngleFromRapidityOmega, rapidityPhaseFromOmega,
    timeAngle, homega]

/-- Polar angle `θ(m) = φ·t·δθ'(m)` — matches the real argument of the `zetaHQIVTerm` phase channel. -/
noncomputable def polarAngleFromRapidity (φ t : ℝ) (m : ℕ) : ℝ :=
  φ * t * delta_theta_prime (m : ℝ)

@[simp]
theorem polarAngleFromRapidity_eq (φ t : ℝ) (m : ℕ) :
    polarAngleFromRapidity φ t m = φ * t * delta_theta_prime (m : ℝ) :=
  rfl

/-- `m ↦ δθ'(m)` along the shell index is monotone: nonnegative casts `ℕ → ℝ` and `delta_theta_prime`
monotone on `ℝ` (`ModifiedMaxwell.delta_theta_prime_monotone`). -/
theorem monotone_delta_theta_prime_natCast : Monotone (fun m : ℕ => delta_theta_prime (m : ℝ)) :=
  delta_theta_prime_monotone.comp Nat.mono_cast

/--
Polar angle along shells is monotone when the rapidity scalar `φ * t` is nonnegative: scale a
monotone shell curve by a nonnegative constant.

When `φ * t < 0`, the same data is **antitone** in `m` (scale reverses order); use
`MonotonePatchParameter` only in the nonnegative regime or with a decreasing `idx`.
-/
theorem polarAngleFromRapidity_monotone_of_mul_nonneg (φ t : ℝ) (hφt : 0 ≤ φ * t) :
    Monotone (fun m : ℕ => polarAngleFromRapidity φ t m) := by
  intro m n hmn
  simp only [polarAngleFromRapidity_eq]
  exact mul_le_mul_of_nonneg_left (monotone_delta_theta_prime_natCast hmn) hφt

theorem polarAngleFromRapidityOmega_eq_polarAngleFromRapidity_of_unitOmega
    (φ t : ℝ) (ω : ℕ → ℝ) (m : ℕ) (hω : ω m = 1) :
    polarAngleFromRapidityOmega φ t ω m = polarAngleFromRapidity φ t m := by
  simpa [polarAngleFromRapidity_eq] using
    polarAngleFromRapidityOmega_eq_of_unitOmega φ t ω m hω

theorem polarAngleFromRapidityOmegaPartial_at_reference_eq_polarAngleFromRapidity (φ t : ℝ) (m : ℕ)
    (hpos : 0 < curvature_integral referenceM) (hm : m = referenceM) :
    polarAngleFromRapidityOmegaPartial φ t m = polarAngleFromRapidity φ t m := by
  simpa [polarAngleFromRapidity_eq] using
    polarAngleFromRapidityOmegaPartial_at_reference φ t m hpos hm

theorem polarAngleFromRapidity_zero (φ t : ℝ) : polarAngleFromRapidity φ t 0 = 0 := by
  simp [polarAngleFromRapidity, tipping_delta_theta_zero]

/-- Radial coordinate `r = m+1` (same scale as `tempLadderConserved` denominator). -/
noncomputable def polarRadiusShellSucc (m : ℕ) : ℝ :=
  (m + 1 : ℝ)

/-- Radial coordinate `r = 1/(m+1)` (dimensionless reciprocal shell; same as `shellReciprocalCoord`). -/
noncomputable def polarRadiusReciprocal (m : ℕ) : ℝ :=
  (1 : ℝ) / (m + 1 : ℝ)

/-- Discrete polar point `(r, θ)` with `r = m+1` (spiral in the `(r, θ)` plane). -/
noncomputable def rapidityPolarPoint (φ t : ℝ) (m : ℕ) : ℝ × ℝ :=
  (polarRadiusShellSucc m, polarAngleFromRapidity φ t m)

/-- Same spiral with reciprocal radius `1/(m+1)`. -/
noncomputable def rapidityPolarPointReciprocal (φ t : ℝ) (m : ℕ) : ℝ × ℝ :=
  (polarRadiusReciprocal m, polarAngleFromRapidity φ t m)

/-- User-facing alias for the spiral angle. -/
noncomputable abbrev rapidityWaveSpiralAngle (φ t : ℝ) (m : ℕ) : ℝ :=
  polarAngleFromRapidity φ t m

/-- Bundle for a future theorem: polar data + a chosen slice chart maps `(r, θ)` to a point on `M`. -/
structure RapiditiesPolarSliceTarget (M : Type u) [TopologicalSpace M] where
  φ : ℝ
  t : ℝ
  /-- Chart from polar coordinates into the spatial slice (supplied when a geometry is fixed). -/
  polarToSlice : ℝ × ℝ → M

/-- Sum of contour evaluations along seven Fano-indexed paths (period-map scaffold). -/
noncomputable def fanoContourPeriodSum (Φ : PhiContourFunctional M) {a b : M}
    (γ : FanoVertex → Path a b) : ℝ :=
  ∑ f : FanoVertex, Φ.eval (γ f)

theorem fanoContourPeriodSum_eq_seven_mul (Φ : PhiContourFunctional M) {a b : M}
    (γ : FanoVertex → Path a b) (r : ℝ) (h : ∀ f : FanoVertex, Φ.eval (γ f) = r) :
    fanoContourPeriodSum Φ γ = 7 * r := by
  classical
  simp [fanoContourPeriodSum, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Hypothesis: lattice `timeAngle` equals the Fano-summed contour functional (period pairing story). -/
structure FanoPeriodRapidityCoincidence (M : Type u) [TopologicalSpace M] where
  φ : ℝ
  t : ℝ
  contour : PhiContourFunctional M
  a : M
  b : M
  γ : FanoVertex → Path a b
  eq_timeAngle : timeAngle φ t = fanoContourPeriodSum contour γ

theorem FanoPeriodRapidityCoincidence.phi_t_eq_fanoContourPeriodSum
    {M : Type u} [TopologicalSpace M] (c : FanoPeriodRapidityCoincidence M) :
    c.φ * c.t = fanoContourPeriodSum c.contour c.γ := by
  simpa [latticeRapidity_eq_timeAngle] using c.eq_timeAngle

/-- “Period map” pairing: `φ·t` equals the pairing of the auxiliary field with the
Fano-indexed cycle family (here, Fano-indexed paths `γ : FanoVertex → Path a b`).

This is a re-labelling of `fanoContourPeriodSum` for the period-map narrative.
-/
theorem FanoPeriodRapidityCoincidence.phi_t_eq_periodMap_pairing
    {M : Type u} [TopologicalSpace M] (c : FanoPeriodRapidityCoincidence M) :
    c.φ * c.t = fanoContourPeriodSum c.contour c.γ := by
  exact c.phi_t_eq_fanoContourPeriodSum

/-- Probe value for a (would-be) Hodge class: in this scaffold it is exactly the
period-map pairing obtained by summing the auxiliary-field contour values over the
Fano-indexed cycle family `γ`. -/
noncomputable def HodgeClassProbe
    {M : Type u} [TopologicalSpace M] (c : FanoPeriodRapidityCoincidence M) : ℝ :=
  fanoContourPeriodSum c.contour c.γ

theorem FanoPeriodRapidityCoincidence.phi_t_eq_hodgeClassProbe
    {M : Type u} [TopologicalSpace M] (c : FanoPeriodRapidityCoincidence M) :
    c.φ * c.t = HodgeClassProbe c := by
  simpa [HodgeClassProbe] using c.phi_t_eq_periodMap_pairing

/-- Package: shell family + scalar field + contour functional (all data, no axioms). -/
structure SpatialRapidityProbe (M : Type u) [TopologicalSpace M] where
  shells : ShellFamily M
  phi : AuxiliaryScalarField M
  contour : PhiContourFunctional M

/-!
### Rapidity-normalized covariant jet bridge (discrete manifold → chart readout)

The **fixed** null lattice supplies shell index `m : ℕ`. The continuum-side object is a **readout**
after applying the same rapidity phase factor as `polarAngleFromRapidity`:
`φ·t·δθ'(m)` with `δθ' = delta_theta_prime` from `Hqiv.Physics.ModifiedMaxwell` (phase-horizon tipping).

This matches the zeta/spiral channel already packaged in this file (`polarAngleFromRapidity`,
`rapidityWaveSpiralAngle`). **Observer-side** shell normalization of φ-response along transport
(`rapidityNormalizedShellPhiIncrement` in `Hqiv.Physics.HQIVPerturbationScaffold`) is a complementary
bridge; here we normalize **tensor jets** feeding `covariant_div_F_O_HQVM_Christoffel` in
`Hqiv.Physics.CovariantSolution`.

A raw discrete jet `dRaw` (e.g. frozen-index packaging of `∂_κ F^{μν}`) is scaled by that scalar
before entering the Christoffel-form divergence.
-/

/-- Scalar coefficient: same shell rapidity phase as `polarAngleFromRapidity` (tipping × time angle).
Aligned with `Hqiv.Physics.OMaxwellAlgebraSeed` / `Hqiv.Physics.ModifiedMaxwell` (`delta_theta_prime` in the
spiral channel). Complementary observer-side shell φ-increment normalization lives in
`Hqiv.Physics.HQIVPerturbationScaffold.rapidityNormalizedShellPhiIncrement` (transport story vs. tensor jet scaling here). -/
noncomputable def rapidityNormalizedJetCoeff (φ t : ℝ) (m : ℕ) : ℝ :=
  polarAngleFromRapidity φ t m

/-- Scale every component of a raw jet by the rapidity normalization (continuum operator on discrete readout). -/
noncomputable def rapidityNormalizedJet (φ t : ℝ) (m : ℕ)
    (dRaw : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ) : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun a κ μ ρ => rapidityNormalizedJetCoeff φ t m * dRaw a κ μ ρ

theorem rapidityNormalizedJetCoeff_eq_polarAngle (φ t : ℝ) (m : ℕ) :
    rapidityNormalizedJetCoeff φ t m = polarAngleFromRapidity φ t m :=
  rfl

/-- Bridge: chart-level jet equals rapidity-normalized discrete raw jet. -/
structure RapidityNormalizedCovariantJetBridge where
  φ : ℝ
  t : ℝ
  m : ℕ
  dRaw : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ
  dChart : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ
  eq : dChart = rapidityNormalizedJet φ t m dRaw

/-- Diagonal bridge when the normalization coefficient is `1`: chart equals raw. -/
def RapidityNormalizedCovariantJetBridge.of_unit_coeff {φ t : ℝ} {m : ℕ}
    (dRaw : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hc : rapidityNormalizedJetCoeff φ t m = 1) :
    RapidityNormalizedCovariantJetBridge where
  φ := φ
  t := t
  m := m
  dRaw := dRaw
  dChart := dRaw
  eq := by
    funext a κ μ ρ
    simp [rapidityNormalizedJet, hc, one_mul]

end Hqiv.Geometry
