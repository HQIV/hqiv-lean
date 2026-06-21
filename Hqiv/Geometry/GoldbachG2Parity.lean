import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Bertrand
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic
import Hqiv.Algebra.G2Embedding
import Hqiv.Algebra.MinimalSoSeedClosure
import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Geometry.QuantumFactorGateFrontier
import Hqiv.Topology.HopfShellComplex

/-!
# Goldbach parity from the `G₂ + Δ` harmonic construction

This module isolates the constructive proof target suggested by the
`so(8) + g₂ + Δ` closure story.

The existing algebra gives the seed geometry:

* `g2Generator` gives the 14 `G₂` derivation generators.
* `phaseLiftDelta` is the horizon harmonic generator `Δ`.
* `g2_in_so8` and `phaseLiftDelta_antisymm` place these seeds in the
  antisymmetric `so(8)` carrier.

The Goldbach step is then separated into two layers:

1. a **finite landing certificate** at a harmonic index `k`;
2. the arithmetic extraction of a Goldbach pair from such a certificate.

No primality or Goldbach statement is assumed here.  The open mathematical
target is `DeltaHarmonicCompleteness`: every even `n > 2` has a finite
`G₂/Δ` landing certificate.  Once that is proved, `goldbach_from_delta_harmonic`
is a fully constructive Lean theorem.
-/

namespace Hqiv.Geometry

open Matrix
open Hqiv.Algebra
open Hqiv.Topology

/-- The explicit `G₂ ∪ {Δ}` seed set acting on the octonionic 8-carrier. -/
def G2DeltaSeedSet : Set (Matrix (Fin 8) (Fin 8) ℝ) :=
  Set.range Hqiv.Algebra.g2Generator ∪ {Hqiv.phaseLiftDelta}

/-- Goldbach pair predicate for a fixed integer `n`. -/
def GoldbachPair (n p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/--
**Even Goldbach (parity form used in the bridge).**

Every even integer `n > 2` is the sum of two primes.  Ordered pairs `(p, q)` are
allowed; there is no ordering constraint beyond `p + q = n`.

The smallest case is `n = 4` (`2 + 2`).  This is the predicate wired into
`SO8ProjectedHalfSlopeBridge` via `GoldbachParity` / `SO4ZetaHolonomyForcesMidpointPairs 2`.
-/
def GoldbachParity : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, GoldbachPair n p q

/--
**Classical even Goldbach (standard number-theory statement).**

Every even integer `n ≥ 4` is the sum of two primes.  Diagonal pairs `(p, p)` are
explicitly allowed when `n = 2p` and `p` is prime.

**Comparison to `GoldbachParity`.**  For even `n`, the conditions `2 < n` and
`4 ≤ n` are equivalent (the first positive even case is `n = 4`).  The bridge
and holonomy modules use `GoldbachParity`; this definition matches the usual
literature wording.

**Midpoint form.**  Writing `n = 2N`, a pair `(p, q)` with `p + q = 2N` and
`p ≤ N ≤ q` is a `GoldbachMidpointPair N p q`; see `goldbach_pair_of_midpoint_pair`
and `midpoint_goldbach_two_iff_goldbach_parity` for the equivalence with
`MidpointGoldbachEventually 2`.
-/
def ClassicalEvenGoldbach : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, GoldbachPair n p q

theorem classical_even_goldbach_iff_goldbach_parity :
    ClassicalEvenGoldbach ↔ GoldbachParity := by
  constructor
  · intro h n hn hEven
    have h4 : 4 ≤ n := by
      rcases hEven with ⟨k, hk⟩
      subst hk
      omega
    exact h n h4 hEven
  · intro h n hn hEven
    exact h n (lt_of_lt_of_le (by decide : 2 < 4) hn) hEven

/-- Smallest even integer in the classical Goldbach statement. -/
def classicalGoldbachThreshold : ℕ := 4

theorem classical_goldbach_threshold_eq_four :
    classicalGoldbachThreshold = 4 := rfl

theorem four_is_classical_goldbach_case :
    ClassicalEvenGoldbach → ∃ p q : ℕ, GoldbachPair 4 p q := by
  intro h
  exact h 4 (by decide) (by decide : Even 4)

/--
Two odd block norms land on the even axis in the sum-form carrier.

This is the parity reduction: the additive carrier
`α ⊕ β e₄` has norm `p + q`, and when both block norms are odd, the result is
even.
-/
theorem even_of_odd_block_norms {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    Even (p + q) := by
  rcases hp with ⟨a, ha⟩
  rcases hq with ⟨b, hb⟩
  rw [ha, hb]
  use a + b + 1
  omega

/--
Logical shell for the `g₂` cubic / harmonic readout.

The concrete octonion cubic identities can refine this predicate later.  At
this layer, it records that the harmonic landing carries a certified readout
inside the `G₂ + Δ` generated construction, without assuming the existence of
any landing.
-/
structure G2ReadoutCertificate (p q : ℕ) : Prop where
  prime_left : Nat.Prime p
  prime_right : Nat.Prime q

/--
A finite `Δ`-harmonic landing certificate for the Goldbach sum-form channel.

The witness is the harmonic index `k` together with two prime block norms
`p, q` whose additive norm is `n`.  The final field ties the arithmetic landing
to the `g₂` readout layer.
-/
structure DeltaHarmonicLanding (n k p q : ℕ) : Prop where
  prime_left : Nat.Prime p
  prime_right : Nat.Prime q
  sum_eq : p + q = n
  g2_readout : G2ReadoutCertificate p q

/-- Each `G₂` generator acts in the antisymmetric `so(8)` carrier. -/
theorem g2_generator_antisymm (i : Fin 14) :
    Hqiv.Algebra.g2Generator i + (Hqiv.Algebra.g2Generator i)ᵀ = 0 :=
  Hqiv.Algebra.g2_in_so8 i

/-- The phase-lift `Δ` acts in the same antisymmetric `so(8)` carrier. -/
theorem delta_harmonic_generator_antisymm :
    Hqiv.phaseLiftDelta + Hqiv.phaseLiftDeltaᵀ = 0 := by
  ext i j
  exact Hqiv.phaseLiftDelta_antisymm i j

/-- The phase-lift `Δ` is one of the generators in the `G₂ + Δ` harmonic seed set. -/
theorem delta_harmonic_generator_mem :
    Hqiv.phaseLiftDelta ∈ G2DeltaSeedSet :=
  Or.inr rfl

/-- Every `G₂` generator lies in the same harmonic seed set. -/
theorem g2_generator_mem_harmonic_lie (i : Fin 14) :
    Hqiv.Algebra.g2Generator i ∈ G2DeltaSeedSet :=
  Or.inl ⟨i, rfl⟩

/-- A landing certificate immediately extracts a Goldbach pair. -/
theorem goldbach_pair_of_delta_landing {n k p q : ℕ}
    (h : DeltaHarmonicLanding n k p q) :
    GoldbachPair n p q :=
  ⟨h.prime_left, h.prime_right, h.sum_eq⟩

/-- A Goldbach pair can be packaged as a `G₂` readout certificate. -/
theorem g2_readout_of_goldbach_pair {n p q : ℕ}
    (h : GoldbachPair n p q) :
    G2ReadoutCertificate p q :=
  ⟨h.1, h.2.1⟩

/--
The paired construction: once the missing prime partner is supplied, the
`G₂/Δ` landing certificate is immediate.  The harmonic index is represented
abstractly by `k`; later geometric work can replace this with the concrete
index produced by the shell inheritance map.
-/
theorem delta_landing_of_goldbach_pair {n k p q : ℕ}
    (h : GoldbachPair n p q) :
    DeltaHarmonicLanding n k p q :=
  ⟨h.1, h.2.1, h.2.2, g2_readout_of_goldbach_pair h⟩

/--
`Δ`-harmonic completeness: every even `n > 2` has a finite harmonic landing.

This is the single open constructive target.  It is stated as a proposition,
not as an axiom or theorem.
-/
def DeltaHarmonicCompleteness : Prop :=
  ∀ n : ℕ, 2 < n → Even n →
    ∃ k p q : ℕ, DeltaHarmonicLanding n k p q

/--
Main extraction theorem: if the `Δ` harmonic series is complete for the
sum-form landing problem, then the parity case of Goldbach follows.
-/
theorem goldbach_from_delta_harmonic
    (hΔ : DeltaHarmonicCompleteness) :
    GoldbachParity := by
  intro n hn hEven
  rcases hΔ n hn hEven with ⟨k, p, q, hLanding⟩
  exact ⟨p, q, goldbach_pair_of_delta_landing hLanding⟩

/--
Local constructive form: a single harmonic index `k` landing at `n` gives the
Goldbach decomposition of that `n`.
-/
theorem goldbach_of_harmonic_index {n k p q : ℕ}
    (_hn : 2 < n) (_hEven : Even n)
    (hLanding : DeltaHarmonicLanding n k p q) :
    ∃ p q : ℕ, GoldbachPair n p q :=
  ⟨p, q, goldbach_pair_of_delta_landing hLanding⟩

/-! ## `G₂` glue: two real choices force a paired landing -/

/--
The two free choices left after the `G₂` glue fixes the real rotation channel.

This is intentionally finite: the construction does not quantify over an
unbounded family of branch choices.  The real parameter is supplied by `Δ`;
the only residual branch data is the two-slot choice.
-/
abbrev G2GlueChoice := Fin 2

/-- A real `Δ` rotation slot: harmonic index plus real scale. -/
structure DeltaRealRotation where
  k : ℕ
  scale : ℝ

/--
Unit coefficient for the `Δ` quarter-turn.

`phaseLiftDelta` is already the π/2 plane generator in the concrete matrix
model, so this lightweight carrier records a quarter-turn by the unit scale on
that generator rather than importing trigonometric data into the Goldbach layer.
-/
def deltaQuarterTurnScale : ℝ := 1

/-- Sphere scale for the Goldbach input: the `Δ(1/n)` scalar. -/
noncomputable def deltaSphereScale (n : ℕ) : ℝ := 1 / (n : ℝ)

/-- Two quarter-turn exposures make the half-turn window used to reveal the
intermediate \(\pi/4\) cofactor arc. -/
def deltaHalfTurnScale : ℝ := 2 * deltaQuarterTurnScale

/-- The two-quarter-turn scale identity used by the Fourier construction. -/
theorem two_quarter_turns_expose_half_turn :
    deltaQuarterTurnScale + deltaQuarterTurnScale = deltaHalfTurnScale := by
  norm_num [deltaQuarterTurnScale, deltaHalfTurnScale]

/--
Q# exposure for one `G₂` sphere at Goldbach input `n`.

There are two independent scalars:
* `turnScale`, the quarter-turn phase used to expose the Fourier arc;
* `rot.scale`, the actual sphere scale, fixed to the `Δ(1/n)` scalar.

This avoids conflating the geometric quarter-turn with the size of the sphere.
-/
structure G2SphereQSharpExposure (n : ℕ) (rot : DeltaRealRotation) where
  axis₁ : Fin 8
  axis₂ : Fin 8
  axes_distinct : axis₁ ≠ axis₂
  turnScale : ℝ
  quarter_turn : turnScale = deltaQuarterTurnScale
  delta_scale : rot.scale = deltaSphereScale n

/--
Pole-to-pole Fourier lock of the two exposed `Q#` spheres.

When the two quarter-turned `G₂` sphere exposures meet pole-to-pole in the `Q#`
Fourier carrier, the shared pole is the lattice support where the two tangent
circles meet.  This is stronger than mere tangency of the two exposed planes:
the common pole is the support point used by the prime-plus-prime landing.
-/
structure QSharpPoleToPoleFourierLock
    {n : ℕ} {rot paired : DeltaRealRotation}
    (left : G2SphereQSharpExposure n rot)
    (right : G2SphereQSharpExposure n paired) where
  pole : Fin 8
  left_pole : pole = left.axis₂
  right_pole : pole = right.axis₂

/--
Two quarter-turned `G₂` exposures exercise the spin-2/full-rotation window used
by the pole-selection argument.

This is a genuine consequence of the exposure certificates: the two turn scales
are both the unit quarter-turn scale, so their sum is the half-turn scale that
reveals the intermediate `π/4` cofactor arc.
-/
theorem g2_spin_two_full_rotation_of_quarter_turns
    {n : ℕ} {rot paired : DeltaRealRotation}
    (left : G2SphereQSharpExposure n rot)
    (right : G2SphereQSharpExposure n paired) :
    left.turnScale + right.turnScale = deltaHalfTurnScale := by
  rw [left.quarter_turn, right.quarter_turn]
  exact two_quarter_turns_expose_half_turn

/--
Certificate that the `Δ` holonomy and `G₂` spin-2 action have selected the pole.

The data records the structural ingredients of the geometric claim:
* the paired rotations share the same `Δ` holonomy index;
* the two quarter turns exercise the full spin-2 window;
* the input lattice is uniform at the `Δ(1/n)` scale;
* the exposed `Q#` spheres meet pole-to-pole.
-/
structure DeltaG2HolonomyPoleCertificate
    {n : ℕ} {rot paired : DeltaRealRotation}
    (left : G2SphereQSharpExposure n rot)
    (right : G2SphereQSharpExposure n paired) where
  same_holonomy_index : rot.k = paired.k
  spin_two_full_rotation : left.turnScale + right.turnScale = deltaHalfTurnScale
  uniform_integer_lattice : 0 < n
  pole_lock : QSharpPoleToPoleFourierLock left right

/-- The holonomy certificate exposes the pole-to-pole Fourier lock. -/
def qsharp_pole_lock_of_delta_g2_holonomy
    {n : ℕ} {rot paired : DeltaRealRotation}
    {left : G2SphereQSharpExposure n rot}
    {right : G2SphereQSharpExposure n paired}
    (cert : DeltaG2HolonomyPoleCertificate left right) :
    QSharpPoleToPoleFourierLock left right :=
  cert.pole_lock

/--
The \(\pi/4\) cofactor arc exposed by the two-quarter-turn construction.

At the current arithmetic layer this is the `Q#` window: every candidate cofactor
between `2` and `qSpan m` is represented by an angle/Fourier slot.
-/
def PiOverFourCofactorArc (m q : ℕ) : Prop :=
  2 ≤ q ∧ q ≤ QuantumFactorGateFrontier.qSpan m

/--
Every cofactor on the \(\pi/4\) arc is visible as a Fourier/angle slot.

This is precisely the existing `Q#` arity coverage theorem, restated in the
language of the two-quarter-turn construction.
-/
theorem pi_over_four_arc_exposes_qsharp_cofactor
    {m q : ℕ}
    (hArc : PiOverFourCofactorArc m q) :
    ∃ slot : ℕ, QuantumFactorGateFrontier.cofactorCandidateFromSlot m slot = q :=
  QuantumFactorGateFrontier.arityCoverage_exists_slot m q hArc.1 hArc.2

/--
`G₂` paired-real glue.

For every even `n > 2`, one of the two residual `G₂` choices supplies a real
`Δ` rotation and its paired real block.  The paired real block is required to
land on integer prime norms `p, q` with `p + q = n`; that finite landing is
the certificate consumed by the Goldbach extraction theorem.
-/
structure G2PairedRealGlue : Prop where
  land :
    ∀ n : ℕ, 2 < n → Even n →
      ∃ _ : G2GlueChoice,
      ∃ rot paired : DeltaRealRotation,
      ∃ p q : ℕ,
        rot.k = paired.k ∧ DeltaHarmonicLanding n rot.k p q

/-! ### Five local obligations for proving the `G₂` glue statement -/

/--
O1. For every parity input, the `Δ` harmonic series supplies a real rotation
slot.
-/
def DeltaRealRotationExists : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ _ : DeltaRealRotation, True

/--
O2. After `G₂` glue, only two branch choices remain.

The codomain is `Fin 2`, so any proof of this obligation is already a
two-choice reduction.
-/
def G2TwoChoiceReduction : Prop :=
  ∀ n : ℕ, 2 < n → Even n → DeltaRealRotation → ∃ _ : G2GlueChoice, True

/--
O3. Every admissible real `Δ` rotation has a paired real rotation with the same
harmonic index.
-/
def G2PairedRealRotationSameIndex : Prop :=
  ∀ n : ℕ, 2 < n → Even n →
    G2GlueChoice → (rot : DeltaRealRotation) →
      ∃ paired : DeltaRealRotation, rot.k = paired.k

/--
O4. The paired real channel snaps to integer prime block norms in the sum
channel.
-/
def G2IntegerPrimeShellSnap : Prop :=
  ∀ n : ℕ, 2 < n → Even n →
    G2GlueChoice → (rot paired : DeltaRealRotation) →
      rot.k = paired.k → ∃ p q : ℕ, GoldbachPair n p q

/--
O5. The `g₂` readout certifies that a prime-shell snap is a full
`Δ`-harmonic landing certificate.
-/
def G2ReadoutCertifiesLanding : Prop :=
  ∀ n k p q : ℕ, GoldbachPair n p q → DeltaHarmonicLanding n k p q

/-- The default readout layer: a Goldbach pair packages directly as a landing. -/
theorem default_g2_readout_certifies_landing :
    G2ReadoutCertifiesLanding := by
  intro n k p q hPair
  exact delta_landing_of_goldbach_pair (k := k) hPair

/--
Assemble the five local obligations into the global paired-real glue theorem.
-/
theorem g2_pair_glue_of_components
    (hRot : DeltaRealRotationExists)
    (hChoice : G2TwoChoiceReduction)
    (hPair : G2PairedRealRotationSameIndex)
    (hSnap : G2IntegerPrimeShellSnap)
    (hReadout : G2ReadoutCertifiesLanding) :
    G2PairedRealGlue := by
  refine ⟨?_⟩
  intro n hn hEven
  rcases hRot n hn hEven with ⟨rot, _hRot⟩
  rcases hChoice n hn hEven rot with ⟨choice, _hChoice⟩
  rcases hPair n hn hEven choice rot with ⟨paired, hk⟩
  rcases hSnap n hn hEven choice rot paired hk with ⟨p, q, hGoldbach⟩
  exact ⟨choice, rot, paired, p, q, hk, hReadout n rot.k p q hGoldbach⟩

/--
The `G₂` glue statement is exactly strong enough to supply
`Δ`-harmonic completeness.
-/
theorem delta_harmonic_completeness_of_g2_pair_glue
    (hGlue : G2PairedRealGlue) :
    DeltaHarmonicCompleteness := by
  intro n hn hEven
  rcases hGlue.land n hn hEven with ⟨_choice, rot, paired, p, q, hk, hLanding⟩
  exact ⟨rot.k, p, q, hLanding⟩

/--
If `G₂` supplies the paired real glue for every `Δ` rotation in the parity
channel, then Goldbach parity follows.
-/
theorem goldbach_from_g2_pair_glue
    (hGlue : G2PairedRealGlue) :
    GoldbachParity :=
  goldbach_from_delta_harmonic
    (delta_harmonic_completeness_of_g2_pair_glue hGlue)

/--
The fully factored proof path: the five local `G₂/Δ` obligations imply
Goldbach parity.
-/
theorem goldbach_from_g2_components
    (hRot : DeltaRealRotationExists)
    (hChoice : G2TwoChoiceReduction)
    (hPair : G2PairedRealRotationSameIndex)
    (hSnap : G2IntegerPrimeShellSnap)
    (hReadout : G2ReadoutCertifiesLanding) :
    GoldbachParity :=
  goldbach_from_g2_pair_glue
    (g2_pair_glue_of_components hRot hChoice hPair hSnap hReadout)

/--
Convenience form using the default `g₂` readout certificate.
-/
theorem goldbach_from_g2_four_components
    (hRot : DeltaRealRotationExists)
    (hChoice : G2TwoChoiceReduction)
    (hPair : G2PairedRealRotationSameIndex)
    (hSnap : G2IntegerPrimeShellSnap) :
    GoldbachParity :=
  goldbach_from_g2_components hRot hChoice hPair hSnap
    default_g2_readout_certifies_landing

/-! ## Tangent circles, triangle equality, and the FTA snap -/

/--
The tangent-circle / triangle-equality landing.

The two tangent blocks have integer norms `leftNorm` and `rightNorm`; triangle
equality is exactly the Goldbach sum channel `leftNorm + rightNorm = n`.
-/
structure TangentTriangleLanding (n : ℕ) (rot paired : DeltaRealRotation) where
  leftNorm : ℕ
  rightNorm : ℕ
  left_ge_two : 2 ≤ leftNorm
  right_ge_two : 2 ≤ rightNorm
  same_index : rot.k = paired.k
  triangle_eq : leftNorm + rightNorm = n

/--
A locked `G₂` sphere for the tangent channel.

At this layer the lock records the structural facts used by the parity carrier:
the two rotations share the same harmonic index.  Stronger concrete lock data
can refine this structure once the cubic/harmonic triple readout is formalized.
-/
structure LockedG2Sphere (n : ℕ) (rot paired : DeltaRealRotation) where
  same_index : rot.k = paired.k
  left_qsharp : G2SphereQSharpExposure n rot
  right_qsharp : G2SphereQSharpExposure n paired
  qsharp_pole_lock : QSharpPoleToPoleFourierLock left_qsharp right_qsharp

/-- A locked `G₂` sphere supplies the `Δ`-holonomy pole certificate on a nonzero lattice. -/
def delta_g2_holonomy_pole_certificate_of_locked
    {n : ℕ} {rot paired : DeltaRealRotation}
    (hn : 0 < n)
    (lock : LockedG2Sphere n rot paired) :
    DeltaG2HolonomyPoleCertificate lock.left_qsharp lock.right_qsharp :=
  { same_holonomy_index := lock.same_index
    spin_two_full_rotation :=
      g2_spin_two_full_rotation_of_quarter_turns lock.left_qsharp lock.right_qsharp
    uniform_integer_lattice := hn
    pole_lock := lock.qsharp_pole_lock }

/-- A tangent landing together with its locked `G₂` sphere certificate. -/
structure LockedG2TangentLanding (n : ℕ) where
  rot : DeltaRealRotation
  paired : DeltaRealRotation
  landing : TangentTriangleLanding n rot paired
  locked : LockedG2Sphere n rot paired

/--
The active locked configuration is the rigid pole axis plus one scale orbit.

The original octonionic/SO(8) carrier remains the background algebra, but once
the two `G₂` sphere exposures are pole-locked, the relevant sweep is along the
locking axis.  The field `integer_positions` is the formal payload for the
Toeplitz/square-peg style claim: the scale orbit hits every integer tangency
position between the two fixed centers.
-/
structure LockedScaleOrbit {n : ℕ} (L : LockedG2TangentLanding n) where
  lock_axis : Fin 8
  axis_is_pole : lock_axis = L.locked.qsharp_pole_lock.pole
  holonomy_certificate :
    DeltaG2HolonomyPoleCertificate L.locked.left_qsharp L.locked.right_qsharp
  scale_parameter : ℕ → ℝ
  integer_positions :
    ∀ k : ℕ, 0 < k → k < n →
      scale_parameter k = (k : ℝ) ∧ k + (n - k) = n
  /-- Symmetric return leg: the complementary position carries the paired radius. -/
  symmetric_return :
    ∀ k : ℕ, 0 < k → k < n → (n - k) + k = n

/--
The `SO(4)+scale`/effective `SO(9)` payload: for every locked tangent landing,
the `Δ` holonomy and the scale orbit sweep all integer positions on the locked
axis.
-/
def DeltaHolonomyScaleOrbitCapturesIntegers : Prop :=
  ∀ {n : ℕ}, (L : LockedG2TangentLanding n) → ∃ _ : LockedScaleOrbit L, True

/-- The locked scale axis is the left sphere's pole. -/
theorem locked_scale_orbit_axis_is_left_pole
    {n : ℕ} {L : LockedG2TangentLanding n}
    (orbit : LockedScaleOrbit L) :
    orbit.lock_axis = L.locked.left_qsharp.axis₂ := by
  rw [orbit.axis_is_pole, L.locked.qsharp_pole_lock.left_pole]

/-- The locked scale axis is the paired sphere's pole. -/
theorem locked_scale_orbit_axis_is_right_pole
    {n : ℕ} {L : LockedG2TangentLanding n}
    (orbit : LockedScaleOrbit L) :
    orbit.lock_axis = L.locked.right_qsharp.axis₂ := by
  rw [orbit.axis_is_pole, L.locked.qsharp_pole_lock.right_pole]

/--
A scale position whose left radius and complementary right radius are both
locked to their sphere poles by the same `G₂` pole-to-pole holonomy.
-/
structure LockedScaleOrbitBilateralPoleHit
    {n : ℕ} {L : LockedG2TangentLanding n}
    (orbit : LockedScaleOrbit L) where
  position : ℕ
  positive : 0 < position
  inside : position < n
  left_on_pole : orbit.lock_axis = L.locked.left_qsharp.axis₂
  right_on_pole : orbit.lock_axis = L.locked.right_qsharp.axis₂
  complementary_radii : position + (n - position) = n

/-- Every integer position hit by the locked scale orbit is a bilateral pole hit. -/
def bilateral_pole_hit_of_locked_scale_orbit
    {n : ℕ} {L : LockedG2TangentLanding n}
    (orbit : LockedScaleOrbit L)
    (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    LockedScaleOrbitBilateralPoleHit orbit :=
  { position := k
    positive := hk
    inside := hkn
    left_on_pole := locked_scale_orbit_axis_is_left_pole orbit
    right_on_pole := locked_scale_orbit_axis_is_right_pole orbit
    complementary_radii := (orbit.integer_positions k hk hkn).2 }

/--
`G₂` holonomy locks both spheres to their poles along the scale orbit: every
integer scale position is seen as `p` on the left pole and `n-p` on the paired
right pole.
-/
def DeltaG2HolonomyLocksBothSpherePoles : Prop :=
  ∀ {n : ℕ}, (L : LockedG2TangentLanding n) →
    (orbit : LockedScaleOrbit L) →
      ∀ k : ℕ, 0 < k → k < n →
        ∃ hit : LockedScaleOrbitBilateralPoleHit orbit, hit.position = k

/-- The bilateral pole-lock statement follows from the locked scale-orbit data. -/
theorem delta_g2_holonomy_locks_both_sphere_poles :
    DeltaG2HolonomyLocksBothSpherePoles := by
  intro n L orbit k hk hkn
  exact ⟨bilateral_pole_hit_of_locked_scale_orbit orbit k hk hkn, rfl⟩

/--
An inscribed axis shape on the locked Hopf/scale carrier.

This is the Toeplitz/square-peg analogue: a shape through the pole axis whose
two sides are the complementary radii `p` and `n-p`, meeting at the tangent
position on that axis.  Uniqueness is not required; existence is enough.
-/
structure HopfInscribedAxisShape
    {n : ℕ} {L : LockedG2TangentLanding n}
    (orbit : LockedScaleOrbit L) where
  left_side : ℕ
  right_side : ℕ
  tangent_position : ℕ
  through_axis : orbit.lock_axis = L.locked.qsharp_pole_lock.pole
  sides_sum : left_side + right_side = n
  tangent_on_axis :
    tangent_position = left_side ∨ tangent_position = right_side
  bilateral_hit : LockedScaleOrbitBilateralPoleHit orbit

/-- Every bilateral pole hit induces an inscribed axis shape through the tangent point. -/
def hopf_inscribed_shape_of_bilateral_hit
    {n : ℕ} {L : LockedG2TangentLanding n}
    (orbit : LockedScaleOrbit L)
    (hit : LockedScaleOrbitBilateralPoleHit orbit) :
    HopfInscribedAxisShape orbit :=
  { left_side := hit.position
    right_side := n - hit.position
    tangent_position := hit.position
    through_axis := by
      rw [hit.left_on_pole, L.locked.qsharp_pole_lock.left_pole]
    sides_sum := hit.complementary_radii
    tangent_on_axis := Or.inl rfl
    bilateral_hit := hit }

/-- The symmetric return leg reproduces the same complementary pair with sides swapped. -/
theorem hopf_inscribed_shape_symmetric_return
    {n : ℕ} {L : LockedG2TangentLanding n}
    (orbit : LockedScaleOrbit L)
    (hit : LockedScaleOrbitBilateralPoleHit orbit) :
    let shape := hopf_inscribed_shape_of_bilateral_hit orbit hit
    shape.left_side + shape.right_side = n ∧
      shape.right_side + shape.left_side = n := by
  intro shape
  exact ⟨shape.sides_sum, by rw [Nat.add_comm]; exact shape.sides_sum⟩

/--
Toeplitz/Hopf payload: the locked smooth scale sweep produces at least one
inscribed axis shape through the tangent point for every integer position hit.
-/
def ToeplitzHopfInscribedShapeAtEveryPosition : Prop :=
  ∀ {n : ℕ}, (L : LockedG2TangentLanding n) →
    (orbit : LockedScaleOrbit L) →
      ∀ k : ℕ, 0 < k → k < n →
        ∃ shape : HopfInscribedAxisShape orbit,
          shape.tangent_position = k

/-- The inscribed shape exists at every swept integer position once the orbit data are supplied. -/
theorem toeplitz_hopf_inscribed_shape_at_every_position :
    ToeplitzHopfInscribedShapeAtEveryPosition := by
  intro n L orbit k hk hkn
  let hit := bilateral_pole_hit_of_locked_scale_orbit orbit k hk hkn
  exact ⟨hopf_inscribed_shape_of_bilateral_hit orbit hit, rfl⟩

/-- A prime position selected on the locked scale orbit. -/
structure LockedScaleOrbitPrimeHit
    {n : ℕ} {L : LockedG2TangentLanding n}
    (orbit : LockedScaleOrbit L) where
  bilateral_pole_hit : LockedScaleOrbitBilateralPoleHit orbit
  position : ℕ
  positive : 0 < position
  inside : position < n
  left_prime : Nat.Prime position
  right_prime : Nat.Prime (n - position)

/-- A prime hit on the locked scale orbit immediately gives a Goldbach pair. -/
theorem goldbach_pair_of_locked_scale_orbit_prime_hit
    {n : ℕ} {L : LockedG2TangentLanding n}
    {orbit : LockedScaleOrbit L}
    (hit : LockedScaleOrbitPrimeHit orbit) :
    GoldbachPair n hit.position (n - hit.position) :=
  ⟨hit.left_prime, hit.right_prime, Nat.add_sub_of_le (Nat.le_of_lt hit.inside)⟩

/--
The remaining prime-selection payload for the scale-orbit route: after the
holonomy/scale sweep has captured all integer positions, one locked scale orbit
contains a prime-plus-prime hit.
-/
def LockedScaleOrbitSelectsPrimeHit : Prop :=
  ∀ {n : ℕ}, (L : LockedG2TangentLanding n) →
    ∃ orbit : LockedScaleOrbit L, ∃ _ : LockedScaleOrbitPrimeHit orbit, True

/-- Scale-orbit prime selection gives a Goldbach pair for the locked landing. -/
theorem goldbach_pair_of_locked_scale_orbit_prime_selection
    (hSelect : LockedScaleOrbitSelectsPrimeHit)
    {n : ℕ} (L : LockedG2TangentLanding n) :
    ∃ p q : ℕ, GoldbachPair n p q := by
  rcases hSelect L with ⟨orbit, hit, _⟩
  exact ⟨hit.position, n - hit.position,
    goldbach_pair_of_locked_scale_orbit_prime_hit hit⟩

/--
The shared lattice point of the two pole-to-pole locked `Q#` spheres.

The point records the two tangent norms as the two prime radii meeting at the
same Fourier/lattice support.  Its equality field is the tangent triangle
equality, so extracting a Goldbach pair is immediate.
-/
structure SharedPrimeLatticePoint (n : ℕ) where
  left : ℕ
  right : ℕ
  left_prime : Nat.Prime left
  right_prime : Nat.Prime right
  shared_support : left + right = n

/-- A shared prime lattice point is exactly a Goldbach pair. -/
theorem goldbach_pair_of_shared_prime_lattice_point
    {n : ℕ}
    (P : SharedPrimeLatticePoint n) :
    GoldbachPair n P.left P.right :=
  ⟨P.left_prime, P.right_prime, P.shared_support⟩

/--
Payload form for the Fourier construction: the two quarter-turned `Q#` spheres
meet pole-to-pole at a lattice point whose two tangent radii are prime.
-/
def QSharpPoleLockSharesPrimeLatticePoint : Prop :=
  ∀ {n : ℕ}, (L : LockedG2TangentLanding n) →
    ∃ P : SharedPrimeLatticePoint n,
      P.left = L.landing.leftNorm ∧
      P.right = L.landing.rightNorm

/--
Holonomy form of the prime-pole payload: the `Δ` holonomy plus `G₂` spin-2 full
rotation selects the pole, and the octonion/Fano lattice proof identifies that
pole as the shared prime lattice support.
-/
def DeltaG2HolonomySelectsPrimePole : Prop :=
  QSharpPoleLockSharesPrimeLatticePoint

/--
If the pole-to-pole `Q#` Fourier construction supplies the shared prime lattice
point for a locked tangent, the tangent norms form a Goldbach pair.
-/
theorem goldbach_pair_of_qsharp_pole_lock_shared_point
    (hShare : QSharpPoleLockSharesPrimeLatticePoint)
    {n : ℕ} (L : LockedG2TangentLanding n) :
    GoldbachPair n L.landing.leftNorm L.landing.rightNorm := by
  rcases hShare L with ⟨P, hLeft, hRight⟩
  rw [← hLeft, ← hRight]
  exact goldbach_pair_of_shared_prime_lattice_point P

/-- Same extraction theorem, phrased in the `Δ`-holonomy pole-selection language. -/
theorem goldbach_pair_of_delta_g2_holonomy_prime_pole
    (hPole : DeltaG2HolonomySelectsPrimePole)
    {n : ℕ} (L : LockedG2TangentLanding n) :
    GoldbachPair n L.landing.leftNorm L.landing.rightNorm :=
  goldbach_pair_of_qsharp_pole_lock_shared_point hPole L

/--
The factorization-side obstruction: a nontrivial composite tangent branch
decomposes into a `G₂` cubic / harmonic triple.

The fields keep the exact arithmetic branch `a * b = m`; future modules can add
the concrete Fourier-twiddle or cubic-readout data without changing the FTA
spine below.
-/
structure G2CompositeTripleDecomposition (m a b : ℕ) where
  left_gt_one : 1 < a
  right_gt_one : 1 < b
  branch_eq : a * b = m

/--
Every nontrivial composite branch of shell `m` is visible as a `G₂` triple
decomposition.
-/
def CompositeTangentDecomposesToTriple (m : ℕ) : Prop :=
  ∀ a b : ℕ, 1 < a → 1 < b → a * b = m →
    ∃ _ : G2CompositeTripleDecomposition m a b, True

/-- Shell `m` admits no `G₂` composite-triple decomposition. -/
def NoG2CompositeTriple (m : ℕ) : Prop :=
  ∀ a b : ℕ, 1 < a → 1 < b → a * b = m →
    (∃ _ : G2CompositeTripleDecomposition m a b, True) → False

/--
A locked `G₂` tangent excludes triple decompositions of both tangent norms.
This is the geometric irreducibility statement suggested by the locked-sphere
picture.
-/
def LockedG2ExcludesCompositeTriples : Prop :=
  ∀ {n : ℕ}, (L : LockedG2TangentLanding n) →
    NoG2CompositeTriple L.landing.leftNorm ∧
    NoG2CompositeTriple L.landing.rightNorm

/--
The factorization side sees every composite branch of a locked tangent norm as
a triple/cubic decomposition.
-/
def LockedG2TangentBranchesDecomposeToTriples : Prop :=
  ∀ {n : ℕ}, (L : LockedG2TangentLanding n) →
    CompositeTangentDecomposesToTriple L.landing.leftNorm ∧
    CompositeTangentDecomposesToTriple L.landing.rightNorm

/-- Existence of one locked tangent landing for each parity input. -/
def LockedG2TangentLandingExists : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ _ : LockedG2TangentLanding n, True

/--
With the current triple structure, every nontrivial composite branch is already
a `G₂` composite-triple decomposition.  Later refinements can add concrete
cubic/Fourier data to the structure while preserving this theorem shape.
-/
theorem composite_tangent_decomposes_to_triple_of_branch (m : ℕ) :
    CompositeTangentDecomposesToTriple m := by
  intro a b ha hb hab
  exact ⟨{
    left_gt_one := ha
    right_gt_one := hb
    branch_eq := hab
  }, trivial⟩

/--
The factorization side sees every composite branch of a locked tangent norm as a
triple.  This is the global visibility hypothesis consumed by the locked
Goldbach route.
-/
theorem locked_g2_tangent_branches_decompose_to_triples :
    LockedG2TangentBranchesDecomposeToTriples := by
  intro n L
  exact ⟨
    composite_tangent_decomposes_to_triple_of_branch L.landing.leftNorm,
    composite_tangent_decomposes_to_triple_of_branch L.landing.rightNorm
  ⟩

/-- The shell `m` is one of the two norms of the locked tangent. -/
def LockedTangentNorm {n : ℕ} (L : LockedG2TangentLanding n) (m : ℕ) : Prop :=
  m = L.landing.leftNorm ∨ m = L.landing.rightNorm

/--
A `G₂` composite triple lives on the `Q#` carrier when one of its two visible
branch factors is represented by an angle slot in the `qSpan` shell.
-/
def G2TripleLivesOnQSharp (m a b : ℕ) : Prop :=
  ∃ q slot : ℕ,
    (q = a ∨ q = b) ∧
    2 ≤ q ∧
    q ≤ QuantumFactorGateFrontier.qSpan m ∧
    QuantumFactorGateFrontier.cofactorCandidateFromSlot m slot = q

/--
The factorization/cubic readout side supplies a `Q#`-bounded visible branch
factor for each composite triple.

This is the same arithmetic shape as the existing `Q#` arity coverage proof:
from `m = a*b`, at least one branch factor is bounded by `sqrt m`, hence by
`qSpan m = max 1 (sqrt m)`.
-/
theorem g2_composite_triple_has_qsharp_visible_factor
    {m a b : ℕ}
    (triple : G2CompositeTripleDecomposition m a b) :
    ∃ q : ℕ, (q = a ∨ q = b) ∧ 2 ≤ q ∧
      q ≤ QuantumFactorGateFrontier.qSpan m := by
  rcases Nat.le_sqrt_of_eq_mul triple.branch_eq.symm with ha | hb
  · refine ⟨a, Or.inl rfl, ?_, ?_⟩
    · exact Nat.succ_le_of_lt triple.left_gt_one
    · unfold QuantumFactorGateFrontier.qSpan QuantumFactorGateFrontier.qCard
      exact le_trans ha (le_max_right 1 (Nat.sqrt m))
  · refine ⟨b, Or.inr rfl, ?_, ?_⟩
    · exact Nat.succ_le_of_lt triple.right_gt_one
    · unfold QuantumFactorGateFrontier.qSpan QuantumFactorGateFrontier.qCard
      exact le_trans hb (le_max_right 1 (Nat.sqrt m))

/--
`Q#` carrier theorem for triples, with the same proof shape as arity coverage:
given the bounded visible factor, `arityCoverage_exists_slot` supplies the
Fourier/angle slot.
-/
theorem g2_triple_lives_on_qsharp
    {m a b : ℕ}
    (triple : G2CompositeTripleDecomposition m a b) :
    G2TripleLivesOnQSharp m a b := by
  rcases g2_composite_triple_has_qsharp_visible_factor triple with
    ⟨q, hqSide, hq2, hqQ⟩
  rcases QuantumFactorGateFrontier.arityCoverage_exists_slot m q hq2 hqQ with
    ⟨slot, hslot⟩
  exact ⟨q, slot, hqSide, hq2, hqQ, hslot⟩

/-!
### Fourier locked triple exclusion

Once both `G₂` spheres are quarter-turned so that their `Q#` carriers meet
pole-to-pole, the exclusion is a Fourier support statement: a `Q#`-visible
composite triple would have to occupy a support slot that the common-pole lock
removes.
-/

/--
Fourier proof payload for the pole-to-pole `Q#` lock.

This is no longer an SO(8) axiom: it is the explicit support-exclusion statement
that the two quarter-turned `Q#` spheres must supply.  Concrete matrix/Fourier
modules can prove this predicate from their character support calculation and
then feed it to the locked-tangent extraction below.
-/
def QSharpPoleToPoleFourierProof : Prop :=
  ∀ {n m a b : ℕ}, (locked : LockedG2TangentLanding n) →
    LockedTangentNorm locked m →
    G2CompositeTripleDecomposition m a b →
    G2TripleLivesOnQSharp m a b →
    False

/--
Locked `G₂` tangent with a proved pole-to-pole `Q#` Fourier lock rejects an actual
composite triple on either tangent norm.
-/
theorem locked_g2_excludes_composite_triple
    (hFourier : QSharpPoleToPoleFourierProof)
    {n m a b : ℕ}
    (locked : LockedG2TangentLanding n)
    (hNorm : LockedTangentNorm locked m)
    (triple : G2CompositeTripleDecomposition m a b) :
    False :=
  hFourier locked hNorm triple (g2_triple_lives_on_qsharp triple)

/--
Version phrased with the decomposition predicate: if the factorization side
turns a concrete nontrivial branch into a triple, the locked SO(8) carrier
rejects it.
-/
theorem locked_g2_excludes_composite_triples
    (hFourier : QSharpPoleToPoleFourierProof)
    {n m a b : ℕ}
    (locked : LockedG2TangentLanding n)
    (hNorm : LockedTangentNorm locked m)
    (decomp : CompositeTangentDecomposesToTriple m)
    (ha : 1 < a) (hb : 1 < b) (hab : a * b = m) :
    False := by
  rcases decomp a b ha hb hab with ⟨triple, _⟩
  exact locked_g2_excludes_composite_triple hFourier locked hNorm triple

/--
The pole-to-pole Fourier `Q#` proof supplies the global locked-triple exclusion
hypothesis consumed by `goldbach_from_locked_g2_tangents`.
-/
theorem locked_g2_excludes_composite_triples_global_of_fourier
    (hFourier : QSharpPoleToPoleFourierProof) :
    LockedG2ExcludesCompositeTriples := by
  intro n L
  constructor
  · intro a b ha hb hab hTriple
    rcases hTriple with ⟨triple, _⟩
    exact locked_g2_excludes_composite_triple hFourier L (Or.inl rfl) triple
  · intro a b ha hb hab hTriple
    rcases hTriple with ⟨triple, _⟩
    exact locked_g2_excludes_composite_triple hFourier L (Or.inr rfl) triple

/--
Composite branch rejection for one integer shell.

By FTA, a shell `m ≥ 2` is prime once every nontrivial product branch is
rejected.
-/
def CompositeBranchRejected (m : ℕ) : Prop :=
  ∀ a b : ℕ, 1 < a → 1 < b → a * b = m → False

/--
If every composite branch decomposes to a `G₂` triple, and no such triple is
compatible with the locked channel, then the branch is rejected.
-/
theorem composite_branch_rejected_of_no_g2_triples {m : ℕ}
    (hDecomp : CompositeTangentDecomposesToTriple m)
    (hNoTriple : NoG2CompositeTriple m) :
    CompositeBranchRejected m := by
  intro a b ha hb hab
  exact hNoTriple a b ha hb hab (hDecomp a b ha hb hab)

/--
Locked tangency turns factorization visibility into composite-branch rejection:
composites would have to decompose to triples, but locked tangents exclude
those triples.
-/
theorem locked_g2_rejects_composite_branches
    (hDecomp : LockedG2TangentBranchesDecomposeToTriples)
    (hExclude : LockedG2ExcludesCompositeTriples)
    {n : ℕ} (L : LockedG2TangentLanding n) :
    CompositeBranchRejected L.landing.leftNorm ∧
    CompositeBranchRejected L.landing.rightNorm := by
  rcases hDecomp L with ⟨hLeftDecomp, hRightDecomp⟩
  rcases hExclude L with ⟨hLeftNoTriple, hRightNoTriple⟩
  exact ⟨
    composite_branch_rejected_of_no_g2_triples hLeftDecomp hLeftNoTriple,
    composite_branch_rejected_of_no_g2_triples hRightDecomp hRightNoTriple
  ⟩

/--
Little FTA lemma: if `m ≥ 2` and all nontrivial product branches are rejected,
then `m` is prime.
-/
theorem prime_of_composite_branches_rejected {m : ℕ}
    (hm : 2 ≤ m)
    (hReject : CompositeBranchRejected m) :
    Nat.Prime m := by
  by_contra hPrime
  rcases (Nat.not_prime_iff_exists_mul_eq hm).mp hPrime with ⟨a, b, ha_lt, hb_lt, hab⟩
  have ha_ne1 : a ≠ 1 := by
    intro ha1
    subst ha1
    have hb_eq_m : b = m := by simpa [one_mul] using hab
    exact (lt_irrefl m) (hb_eq_m ▸ hb_lt)
  have hb_ne1 : b ≠ 1 := by
    intro hb1
    subst hb1
    have ha_eq_m : a = m := by simpa [mul_one] using hab
    exact (lt_irrefl m) (ha_eq_m ▸ ha_lt)
  have ha_ne0 : a ≠ 0 := by
    intro ha0
    subst ha0
    have : m = 0 := by simpa using hab.symm
    exact (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hm)) this.symm
  have hb_ne0 : b ≠ 0 := by
    intro hb0
    subst hb0
    have : m = 0 := by simpa using hab.symm
    exact (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hm)) this.symm
  have ha_gt1 : 1 < a :=
    Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha_ne0)) (Ne.symm ha_ne1)
  have hb_gt1 : 1 < b :=
    Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb_ne0)) (Ne.symm hb_ne1)
  exact hReject a b ha_gt1 hb_gt1 hab

/--
The tangent construction exists for the paired real channel.
-/
def TangentTriangleLandingExists : Prop :=
  ∀ n : ℕ, 2 < n → Even n →
    G2GlueChoice → (rot paired : DeltaRealRotation) →
      rot.k = paired.k → ∃ _ : TangentTriangleLanding n rot paired, True

/--
`G₂` rejects the composite branches of both tangent-circle integer shells.
-/
def G2RejectsCompositeTangentBranches : Prop :=
  ∀ {n : ℕ} {rot paired : DeltaRealRotation},
    (landing : TangentTriangleLanding n rot paired) →
      CompositeBranchRejected landing.leftNorm ∧
      CompositeBranchRejected landing.rightNorm

/-- A tangent triangle landing plus composite rejection gives a Goldbach pair. -/
theorem goldbach_pair_of_tangent_triangle_and_fta
    {n : ℕ} {rot paired : DeltaRealRotation}
    (landing : TangentTriangleLanding n rot paired)
    (hReject :
      CompositeBranchRejected landing.leftNorm ∧
      CompositeBranchRejected landing.rightNorm) :
    GoldbachPair n landing.leftNorm landing.rightNorm := by
  refine ⟨?_, ?_, landing.triangle_eq⟩
  · exact prime_of_composite_branches_rejected landing.left_ge_two hReject.1
  · exact prime_of_composite_branches_rejected landing.right_ge_two hReject.2

/--
A locked tangent landing gives a Goldbach pair once the factorization side sees
all composite branches as triples and the locked channel excludes those triples.
-/
theorem goldbach_pair_of_locked_g2_tangent
    (hDecomp : LockedG2TangentBranchesDecomposeToTriples)
    (hExclude : LockedG2ExcludesCompositeTriples)
    {n : ℕ} (L : LockedG2TangentLanding n) :
    GoldbachPair n L.landing.leftNorm L.landing.rightNorm :=
  goldbach_pair_of_tangent_triangle_and_fta L.landing
    (locked_g2_rejects_composite_branches hDecomp hExclude L)

/--
The locked-tangent proof route for Goldbach parity: for each parity input, one
locked tangent exists; composite tangent norms are visible to the triple
factorization layer; and locked tangents exclude such triples.
-/
theorem goldbach_from_locked_g2_tangents
    (hLanding : LockedG2TangentLandingExists)
    (hDecomp : LockedG2TangentBranchesDecomposeToTriples)
    (hExclude : LockedG2ExcludesCompositeTriples) :
    GoldbachParity := by
  intro n hn hEven
  rcases hLanding n hn hEven with ⟨L, _⟩
  exact ⟨L.landing.leftNorm, L.landing.rightNorm,
    goldbach_pair_of_locked_g2_tangent hDecomp hExclude L⟩

/--
Tangent-circle landing plus FTA composite rejection discharges the existing
integer-prime shell snap obligation.
-/
theorem g2_integer_prime_shell_snap_of_tangent_triangle_fta
    (hTangent : TangentTriangleLandingExists)
    (hReject : G2RejectsCompositeTangentBranches) :
    G2IntegerPrimeShellSnap := by
  intro n hn hEven choice rot paired hk
  rcases hTangent n hn hEven choice rot paired hk with ⟨landing, _⟩
  have hRejectLanding := hReject landing
  exact ⟨landing.leftNorm, landing.rightNorm,
    goldbach_pair_of_tangent_triangle_and_fta landing hRejectLanding⟩

/--
Final tangent-circle proof spine: real `Δ`, two `G₂` choices, paired real
rotation, tangent triangle equality, and FTA composite rejection imply
Goldbach parity.
-/
theorem goldbach_from_tangent_triangle_g2_fta
    (hRot : DeltaRealRotationExists)
    (hChoice : G2TwoChoiceReduction)
    (hPair : G2PairedRealRotationSameIndex)
    (hTangent : TangentTriangleLandingExists)
    (hReject : G2RejectsCompositeTangentBranches) :
    GoldbachParity :=
  goldbach_from_g2_four_components hRot hChoice hPair
    (g2_integer_prime_shell_snap_of_tangent_triangle_fta hTangent hReject)

/-! ## Smaller carrier: `SO(4)` as `SO(3) + Δ` for the parity channel -/

/-!
The closure paper's low-dimensional certificate is the specialization of
`MinimalSoSeedClosure` to `N = 4`: the embedded `so(3)` on the first three
coordinates plus the single connector `Δ₄ = J₁₄` generates all of `so(4)`.
-/

/-- The matrix type for the `SO(4)` parity carrier. -/
abbrev SO4Mat := Hqiv.Algebra.Mat 4

/-- The `SO(4)` parity seed: embedded `SO(3)` plus the connector `Δ₄`. -/
noncomputable abbrev SO4So3DeltaLie : LieSubalgebra ℝ SO4Mat :=
  Hqiv.Algebra.minimalSoSeedLie 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1))

/-- The Euclidean `so(4)` Lie algebra. -/
noncomputable abbrev SO4Lie : LieSubalgebra ℝ SO4Mat :=
  skewAdjointMatricesLieSubalgebra (1 : SO4Mat)

/--
`SO(4) = SO(3) + Δ₄`: the closure paper's low-dimensional model, discharged by
the generic minimal seed theorem.
-/
theorem so4_so3_delta_lieSpan_eq_so4 :
    SO4So3DeltaLie = SO4Lie := by
  simpa [SO4So3DeltaLie, SO4Lie] using
    (Hqiv.Algebra.minimal_so_seed_lieSpan_eq_skewAdjoint
      (N := 4) (hN := (by decide : 3 ≤ 4)) (k := (0 : Fin (4 - 1))))

/-- The connector `Δ₄ = J₁₄` belongs to the `SO(3)+Δ₄` seed. -/
theorem so4_delta_mem_seed :
    Hqiv.Algebra.planeGen
      (Hqiv.Algebra.predEmbed 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
      (Hqiv.Algebra.lastEmbed 4 (by decide : 2 ≤ 4))
      (Hqiv.Algebra.predEmbed_lt_last (N := 4) (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
      ∈ Hqiv.Algebra.minimalSoSeedSet 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1)) :=
  Hqiv.Algebra.mem_minimalSoSeedSet_delta (N := 4) (by decide : 2 ≤ 4) (0 : Fin (4 - 1))

/-- The connector `Δ₄ = J₁₄` lies in the generated `SO(3)+Δ₄` Lie algebra. -/
theorem so4_delta_mem_lie :
    Hqiv.Algebra.planeGen
      (Hqiv.Algebra.predEmbed 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
      (Hqiv.Algebra.lastEmbed 4 (by decide : 2 ≤ 4))
      (Hqiv.Algebra.predEmbed_lt_last (N := 4) (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
      ∈ SO4So3DeltaLie :=
  LieSubalgebra.subset_lieSpan (R := ℝ) (L := SO4Mat)
    (s := Hqiv.Algebra.minimalSoSeedSet 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
    so4_delta_mem_seed

/--
The `SO(4)` parity carrier keeps only the real tangent-circle data needed for
the sum-form problem.  The internal `SO(3)` block supplies the ordinary
three-axis rotation, while `Δ` supplies the paired harmonic direction.
-/
structure SO4DeltaRotation where
  k : ℕ
  scale : ℝ

/-- The residual two-choice branch data in the `SO(4)` parity carrier. -/
abbrev SO4DeltaChoice := Fin 2

/-- O1′. The `SO(4)` carrier supplies a real `Δ` rotation slot. -/
def SO4DeltaRotationExists : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ _ : SO4DeltaRotation, True

/-- The `SO(4)` carrier always has a real `Δ` slot for the parity input. -/
theorem so4_delta_rotation_exists :
    SO4DeltaRotationExists := by
  intro n _hn _hEven
  exact ⟨{ k := n, scale := (n : ℝ) }, trivial⟩

/-- O2′. `SO(3) + Δ` leaves only the two tangency branches. -/
def SO4TwoChoiceReduction : Prop :=
  ∀ n : ℕ, 2 < n → Even n → SO4DeltaRotation → ∃ _ : SO4DeltaChoice, True

/-- The reduced `SO(4)` model has exactly the two tangency branches. -/
theorem so4_two_choice_reduction :
    SO4TwoChoiceReduction := by
  intro n _hn _hEven _rot
  exact ⟨0, trivial⟩

/-- O3′. Every `SO(4)` `Δ` rotation has a paired rotation with the same index. -/
def SO4PairedRotationSameIndex : Prop :=
  ∀ n : ℕ, 2 < n → Even n →
    SO4DeltaChoice → (rot : SO4DeltaRotation) →
      ∃ paired : SO4DeltaRotation, rot.k = paired.k

/-- A real `SO(4)` rotation pairs with the same harmonic index. -/
theorem so4_paired_rotation_same_index :
    SO4PairedRotationSameIndex := by
  intro n _hn _hEven _choice rot
  exact ⟨rot, rfl⟩

/--
Forgetful map from the `SO(4)` parity carrier into the generic real `Δ` slot
used by the `G₂/Δ` proof spine.
-/
def DeltaRealRotation.ofSO4 (rot : SO4DeltaRotation) : DeltaRealRotation :=
  { k := rot.k, scale := rot.scale }

/-- `SO(4)` real rotations supply the generic `Δ` rotation obligation. -/
theorem delta_real_rotation_exists_of_so4
    (hSO4 : SO4DeltaRotationExists) :
    DeltaRealRotationExists := by
  intro n hn hEven
  rcases hSO4 n hn hEven with ⟨rot, hrot⟩
  exact ⟨DeltaRealRotation.ofSO4 rot, hrot⟩

/-- The two tangency branches in `SO(4)` supply the generic two-choice obligation. -/
theorem g2_two_choice_of_so4
    (hSO4 : SO4TwoChoiceReduction) :
    G2TwoChoiceReduction := by
  intro n hn hEven rot
  let rot4 : SO4DeltaRotation := { k := rot.k, scale := rot.scale }
  rcases hSO4 n hn hEven rot4 with ⟨choice, hchoice⟩
  exact ⟨choice, hchoice⟩

/-- Paired `SO(4)` rotations supply the generic same-index paired-rotation obligation. -/
theorem g2_paired_same_index_of_so4
    (hSO4 : SO4PairedRotationSameIndex) :
    G2PairedRealRotationSameIndex := by
  intro n hn hEven choice rot
  let choice4 : SO4DeltaChoice := choice
  let rot4 : SO4DeltaRotation := { k := rot.k, scale := rot.scale }
  rcases hSO4 n hn hEven choice4 rot4 with ⟨paired4, hk⟩
  exact ⟨DeltaRealRotation.ofSO4 paired4, hk⟩

/-- Tangent triangle landing exists directly in the `SO(4)` carrier. -/
def SO4TangentTriangleLandingExists : Prop :=
  ∀ n : ℕ, 2 < n → Even n →
    SO4DeltaChoice → (rot paired : SO4DeltaRotation) →
      rot.k = paired.k →
        ∃ _ : TangentTriangleLanding n
          (DeltaRealRotation.ofSO4 rot)
          (DeltaRealRotation.ofSO4 paired), True

/--
Every even `n > 2` admits a tangent triangle equality in the reduced `SO(4)`
carrier: the two radii `2` and `n - 2` satisfy `2 + (n - 2) = n`.
-/
theorem so4_tangent_triangle_landing_exists :
    SO4TangentTriangleLandingExists := by
  intro n hn hEven _choice rot paired hk
  have h4 : 4 ≤ n := by
    rcases hEven with ⟨t, ht⟩
    omega
  refine ⟨{
    leftNorm := 2
    rightNorm := n - 2
    left_ge_two := by omega
    right_ge_two := by omega
    same_index := hk
    triangle_eq := by omega
  }, trivial⟩

/-- `SO(4)` tangent landing supplies the generic tangent landing obligation. -/
theorem tangent_triangle_exists_of_so4
    (hSO4 : SO4TangentTriangleLandingExists) :
    TangentTriangleLandingExists := by
  intro n hn hEven choice rot paired hk
  let choice4 : SO4DeltaChoice := choice
  let rot4 : SO4DeltaRotation := { k := rot.k, scale := rot.scale }
  let paired4 : SO4DeltaRotation := { k := paired.k, scale := paired.scale }
  have hk4 : rot4.k = paired4.k := hk
  rcases hSO4 n hn hEven choice4 rot4 paired4 hk4 with ⟨landing, hlanding⟩
  exact ⟨landing, hlanding⟩

/--
The reduced `SO(4) = SO(3) + Δ` proof spine.  It reuses the same tangent/FTA
snap theorem but avoids the full `SO(8)` carrier.
-/
theorem goldbach_from_so4_delta_tangent_fta
    (hRot : SO4DeltaRotationExists)
    (hChoice : SO4TwoChoiceReduction)
    (hPair : SO4PairedRotationSameIndex)
    (hTangent : SO4TangentTriangleLandingExists)
    (hReject : G2RejectsCompositeTangentBranches) :
    GoldbachParity :=
  goldbach_from_tangent_triangle_g2_fta
    (delta_real_rotation_exists_of_so4 hRot)
    (g2_two_choice_of_so4 hChoice)
    (g2_paired_same_index_of_so4 hPair)
    (tangent_triangle_exists_of_so4 hTangent)
    hReject

/--
With the first four `SO(4)` obligations discharged, only composite-branch
rejection remains as an input to Goldbach parity.
-/
theorem goldbach_from_so4_composite_rejection
    (hReject : G2RejectsCompositeTangentBranches) :
    GoldbachParity :=
  goldbach_from_so4_delta_tangent_fta
    so4_delta_rotation_exists
    so4_two_choice_reduction
    so4_paired_rotation_same_index
    so4_tangent_triangle_landing_exists
    hReject

/--
The unrestricted composite-rejection statement is too strong: the tangent
triangle `4 + 4 = 8` is a valid landing, but `4` has the nontrivial product
branch `2 * 2`.
-/
theorem not_g2_rejects_all_composite_tangent_branches :
    ¬ G2RejectsCompositeTangentBranches := by
  intro hReject
  let rot : DeltaRealRotation := { k := 0, scale := 0 }
  let landing : TangentTriangleLanding 8 rot rot :=
    { leftNorm := 4
      rightNorm := 4
      left_ge_two := by norm_num
      right_ge_two := by norm_num
      same_index := rfl
      triangle_eq := by norm_num }
  have hLeftReject : CompositeBranchRejected landing.leftNorm := (hReject landing).1
  exact hLeftReject 2 2 (by norm_num) (by norm_num) (by norm_num)

/-! ## Hardy--Littlewood bridge for the paired construction -/

/--
Finite paired-prime count in the sum channel.

This is the Lean version of the "simpler construction with its pair restored":
count primes `p ≤ n` such that the reflected partner `n - p` is also prime.
-/
def goldbachPairCandidates (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))

/-- Number of paired-prime hits in the Goldbach sum channel. -/
def goldbachPairCount (n : ℕ) : ℕ :=
  (goldbachPairCandidates n).card

/-- A positive paired-prime count extracts an actual Goldbach pair. -/
theorem exists_goldbach_pair_of_pairCount_pos {n : ℕ}
    (hpos : 0 < goldbachPairCount n) :
    ∃ p q : ℕ, GoldbachPair n p q := by
  unfold goldbachPairCount goldbachPairCandidates at hpos
  rcases Finset.card_pos.mp hpos with ⟨p, hp⟩
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hpRange, hpPrime, hqPrime⟩
  refine ⟨p, n - p, ?_⟩
  have hpLe : p ≤ n := by
    exact Nat.lt_succ_iff.mp (by simpa [Finset.mem_range] using hpRange)
  exact ⟨hpPrime, hqPrime, by omega⟩

/--
Hardy--Littlewood positivity specialized to the paired sum channel.

This is the analytic input slot: the lower bound is used only through
positivity of the paired-prime count for each even `n > 2`.
-/
def HardyLittlewoodPositivePairs : Prop :=
  ∀ n : ℕ, 2 < n → Even n → 0 < goldbachPairCount n

/--
Hardy--Littlewood positivity supplies the missing partner and hence the
`Δ`-harmonic landing certificate.
-/
theorem delta_harmonic_completeness_of_hardy_littlewood
    (hHL : HardyLittlewoodPositivePairs) :
    DeltaHarmonicCompleteness := by
  intro n hn hEven
  rcases exists_goldbach_pair_of_pairCount_pos (hHL n hn hEven) with ⟨p, q, hPair⟩
  exact ⟨p, p, q, delta_landing_of_goldbach_pair (k := p) hPair⟩

/--
Hardy--Littlewood positivity for the paired construction implies the parity
case of Goldbach.
-/
theorem goldbach_from_hardy_littlewood
    (hHL : HardyLittlewoodPositivePairs) :
    GoldbachParity :=
  goldbach_from_delta_harmonic
    (delta_harmonic_completeness_of_hardy_littlewood hHL)

/--
Eventual Hardy--Littlewood positivity: the paired-prime count is positive for
all even `n > 2` at or above a threshold `N₀`.
-/
def HardyLittlewoodEventuallyPositivePairs (N₀ : ℕ) : Prop :=
  ∀ n : ℕ, N₀ ≤ n → 2 < n → Even n → 0 < goldbachPairCount n

/--
Finite low-range verification below the Hardy--Littlewood threshold.

This is intentionally the same paired-prime predicate as the asymptotic side:
there is no separate trial-division theorem here, only a finite certificate
slot for the bounded initial segment.
-/
def GoldbachFiniteBelow (N₀ : ℕ) : Prop :=
  ∀ n : ℕ, n < N₀ → 2 < n → Even n → 0 < goldbachPairCount n

/--
The usual analytic proof shape: an eventual Hardy--Littlewood lower bound plus
a finite verification below the threshold gives positivity for every parity
case.
-/
theorem hardy_littlewood_positive_pairs_of_eventual_and_finite
    {N₀ : ℕ}
    (hEventual : HardyLittlewoodEventuallyPositivePairs N₀)
    (hFinite : GoldbachFiniteBelow N₀) :
    HardyLittlewoodPositivePairs := by
  intro n hn hEven
  by_cases hN : N₀ ≤ n
  · exact hEventual n hN hn hEven
  · have hlt : n < N₀ := Nat.lt_of_not_ge hN
    exact hFinite n hlt hn hEven

/--
Eventual Hardy--Littlewood positivity plus finite low-range certificates proves
Goldbach parity via the `G₂/Δ` landing construction.
-/
theorem goldbach_from_eventual_hardy_littlewood
    {N₀ : ℕ}
    (hEventual : HardyLittlewoodEventuallyPositivePairs N₀)
    (hFinite : GoldbachFiniteBelow N₀) :
    GoldbachParity :=
  goldbach_from_hardy_littlewood
    (hardy_littlewood_positive_pairs_of_eventual_and_finite hEventual hFinite)

/-! ## `SO(2) + Δ`: Hardy--Littlewood paired-prime half -/

/--
The `SO(2)+Δ` carrier for the Hardy--Littlewood side.

Only one circular angle is needed: a prime candidate `p` on the circle and its
`Δ`-paired complement `n - p`.
-/
structure SO2DeltaRotation where
  p : ℕ
  angleScale : ℝ

/-- The `Δ`-paired complement in the additive channel. -/
def SO2DeltaPartner (n p : ℕ) : ℕ :=
  n - p

/-- A paired-prime landing in the `SO(2)+Δ` carrier. -/
structure SO2DeltaPrimePairLanding (n : ℕ) where
  rot : SO2DeltaRotation
  left_prime : Nat.Prime rot.p
  right_prime : Nat.Prime (SO2DeltaPartner n rot.p)
  triangle_eq : rot.p + SO2DeltaPartner n rot.p = n

/--
The `SO(2)+Δ` Hardy--Littlewood positivity statement: for each even `n > 2`,
some circular prime slot has a `Δ`-paired prime complement.
-/
def SO2DeltaHardyLittlewoodPositive : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ _ : SO2DeltaPrimePairLanding n, True

/--
Eventual positivity in the selected `SO(2)+Δ` channel.  This is the precise
analytic circle-method target after the algebraic carrier has been built: above
a threshold, the selected `Δ` partner lands on a prime complement.
-/
def SO2DeltaEventuallyPositive (N₀ : ℕ) : Prop :=
  ∀ n : ℕ, N₀ ≤ n → 2 < n → Even n → ∃ _ : SO2DeltaPrimePairLanding n, True

/--
Finite verification below a threshold in the selected `SO(2)+Δ` channel.
This is the formal slot for bounded Goldbach verification certificates.
-/
def SO2DeltaFiniteBelow (N₀ : ℕ) : Prop :=
  ∀ n : ℕ, n < N₀ → 2 < n → Even n → ∃ _ : SO2DeltaPrimePairLanding n, True

/-- Inclusive form used for external finite verification records. -/
def SO2DeltaFiniteVerifiedThrough (B : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ B → 2 < n → Even n → ∃ _ : SO2DeltaPrimePairLanding n, True

/-- The Oliveira e Silva verification range usually cited for even Goldbach. -/
def goldbachFiniteVerificationBound : ℕ :=
  4 * 10 ^ 18

/-- Inclusive finite verification through `B` gives the below-threshold form at `B + 1`. -/
theorem so2_delta_finite_below_succ_of_verified_through {B : ℕ}
    (hFinite : SO2DeltaFiniteVerifiedThrough B) :
    SO2DeltaFiniteBelow (B + 1) := by
  intro n hn hn2 hEven
  exact hFinite n (Nat.lt_succ_iff.mp hn) hn2 hEven

/--
The selected-channel threshold decomposition: eventual `SO(2)+Δ` positivity
plus finite selected-channel verification gives the global selected landing
statement.
-/
theorem so2_delta_hardy_littlewood_of_selected_eventual_and_finite
    {N₀ : ℕ}
    (hEventual : SO2DeltaEventuallyPositive N₀)
    (hFinite : SO2DeltaFiniteBelow N₀) :
    SO2DeltaHardyLittlewoodPositive := by
  intro n hn hEven
  by_cases hBelow : n < N₀
  · exact hFinite n hBelow hn hEven
  · exact hEventual n (le_of_not_gt hBelow) hn hEven

/--
An inclusive finite verification through `B`, together with eventual positivity
starting at `B + 1`, proves the global selected `SO(2)+Δ` landing statement.
-/
theorem so2_delta_hardy_littlewood_of_eventual_after_verified_bound
    {B : ℕ}
    (hEventual : SO2DeltaEventuallyPositive (B + 1))
    (hFinite : SO2DeltaFiniteVerifiedThrough B) :
    SO2DeltaHardyLittlewoodPositive :=
  so2_delta_hardy_littlewood_of_selected_eventual_and_finite hEventual
    (so2_delta_finite_below_succ_of_verified_through hFinite)

/--
Final selected-channel threshold theorem.  The remaining analytic theorem is
exactly `SO2DeltaEventuallyPositive`; once it is paired with finite verification,
Goldbach parity follows by extraction.
-/
theorem goldbach_from_so2_delta_selected_threshold
    {N₀ : ℕ}
    (hEventual : SO2DeltaEventuallyPositive N₀)
    (hFinite : SO2DeltaFiniteBelow N₀) :
    GoldbachParity := by
  intro n hn hEven
  rcases so2_delta_hardy_littlewood_of_selected_eventual_and_finite hEventual hFinite
      n hn hEven with ⟨landing, _⟩
  exact ⟨landing.rot.p, SO2DeltaPartner n landing.rot.p,
    landing.left_prime, landing.right_prime, landing.triangle_eq⟩

/-- A positive paired-prime count produces an `SO(2)+Δ` prime-pair landing. -/
theorem so2_delta_landing_of_pairCount_pos {n : ℕ}
    (hpos : 0 < goldbachPairCount n) :
    ∃ _ : SO2DeltaPrimePairLanding n, True := by
  rcases exists_goldbach_pair_of_pairCount_pos hpos with ⟨p, q, hPair⟩
  rcases hPair with ⟨hpPrime, hqPrime, hSum⟩
  have hpLe : p ≤ n := by omega
  have hPartner : SO2DeltaPartner n p = q := by
    unfold SO2DeltaPartner
    omega
  refine ⟨{
    rot := { p := p, angleScale := (p : ℝ) }
    left_prime := hpPrime
    right_prime := ?_
    triangle_eq := ?_
  }, trivial⟩
  · simpa [hPartner] using hqPrime
  · simpa [hPartner] using hSum

/-- The existing paired-prime positivity theorem is exactly the `SO(2)+Δ` positivity statement. -/
theorem so2_delta_hardy_littlewood_of_pair_count
    (hHL : HardyLittlewoodPositivePairs) :
    SO2DeltaHardyLittlewoodPositive := by
  intro n hn hEven
  exact so2_delta_landing_of_pairCount_pos (hHL n hn hEven)

/-- An `SO(2)+Δ` landing extracts an ordinary Goldbach pair. -/
theorem goldbach_pair_of_so2_delta_landing {n : ℕ}
    (landing : SO2DeltaPrimePairLanding n) :
    ∃ p q : ℕ, GoldbachPair n p q :=
  ⟨landing.rot.p, SO2DeltaPartner n landing.rot.p,
    landing.left_prime, landing.right_prime, landing.triangle_eq⟩

/--
An `SO(2)+Δ` paired-prime landing selects one tangent-triangle landing.
No uniqueness of tangency is required: the selected prime pair is enough.
-/
theorem selected_tangent_triangle_of_so2_delta_landing {n : ℕ}
    (landing : SO2DeltaPrimePairLanding n) :
    ∃ rot paired : DeltaRealRotation,
      ∃ _ : TangentTriangleLanding n rot paired,
      GoldbachPair n landing.rot.p (SO2DeltaPartner n landing.rot.p) := by
  let rot : DeltaRealRotation := { k := landing.rot.p, scale := landing.rot.angleScale }
  let paired : DeltaRealRotation := { k := landing.rot.p, scale := landing.rot.angleScale }
  refine ⟨rot, paired, ?_, ?_⟩
  · exact {
      leftNorm := landing.rot.p
      rightNorm := SO2DeltaPartner n landing.rot.p
      left_ge_two := landing.left_prime.two_le
      right_ge_two := landing.right_prime.two_le
      same_index := rfl
      triangle_eq := landing.triangle_eq
    }
  · exact ⟨landing.left_prime, landing.right_prime, landing.triangle_eq⟩

/-- The `SO(2)+Δ` Hardy--Littlewood half implies Goldbach parity. -/
theorem goldbach_from_so2_delta_hardy_littlewood
    (hSO2 : SO2DeltaHardyLittlewoodPositive) :
    GoldbachParity := by
  intro n hn hEven
  rcases hSO2 n hn hEven with ⟨landing, _⟩
  exact goldbach_pair_of_so2_delta_landing landing

/--
Eventual Hardy--Littlewood positivity plus finite verification also gives the
`SO(2)+Δ` landing formulation.
-/
theorem so2_delta_hardy_littlewood_of_eventual_and_finite
    {N₀ : ℕ}
    (hEventual : HardyLittlewoodEventuallyPositivePairs N₀)
    (hFinite : GoldbachFiniteBelow N₀) :
    SO2DeltaHardyLittlewoodPositive :=
  so2_delta_hardy_littlewood_of_pair_count
    (hardy_littlewood_positive_pairs_of_eventual_and_finite hEventual hFinite)


/-! ### Goldbach midpoint sieve (SoE dual overlay) -/

/-- Prime pair `(p, q)` bracketing midpoint `N` with `p + q = 2N`. -/
def GoldbachMidpointPair (N p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p ≤ N ∧ N ≤ q ∧ p + q = 2 * N

/-- Midpoint scan candidates: left slots surviving both Eratosthenes legs. -/
def goldbachMidpointCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun p =>
    Nat.Prime p ∧ Nat.Prime (2 * N - p) ∧ p ≤ N ∧ N ≤ 2 * N - p)

/-- Number of prime-pair hits around the midpoint `N`, with diagonal allowed. -/
def goldbachMidpointCount (N : ℕ) : ℕ :=
  (goldbachMidpointCandidates N).card

/-! ### Dual midpoint sieve: anchors at `2` and `2N` -/

/--
**From anchor `2`.**  The global Eratosthenes leg: a candidate survives only if it
is prime (equivalently: not marked as a repeated-addition composite).
-/
def sieveFromTwo (p : ℕ) : Prop :=
  Nat.Prime p

/--
**From anchor `2N`.**  The reflected Eratosthenes leg: cross out `p` when the
partner `2N - p` is composite.
-/
def sieveFromTwoN (N p : ℕ) : Prop :=
  Nat.Prime (2 * N - p)

/--
**Dual midpoint survivor.**  Passes both sieves and brackets the midpoint `N`.
This is exactly the predicate filtered by `goldbachMidpointCandidates`.
-/
def dualMidpointSurvivor (N p : ℕ) : Prop :=
  sieveFromTwo p ∧ sieveFromTwoN N p ∧ p ≤ N ∧ N ≤ 2 * N - p

/-- Some left-half slot survives both sieves. -/
def MidpointSieveSurvivorExists (N : ℕ) : Prop :=
  ∃ p : ℕ, dualMidpointSurvivor N p

/-! ### Reflection point `N`: forward SoE + mirrored prime overlay -/

/--
**Mirror across the reflection point `N`.**  The interval `[0, 2N]` is fixed at
`N`; forward slot `p` pairs with reflected slot `2N - p`.
-/
def midpointReflect (N p : ℕ) : ℕ :=
  2 * N - p

/--
**Reflected overlay:** the same prime test as the forward SoE, but at the
mirror slot.  This is exactly the from-`2N` leg re-expressed at `N`.
-/
def sieveReflectedFromMidpoint (N p : ℕ) : Prop :=
  sieveFromTwo (midpointReflect N p)

theorem sieveFromTwoN_eq_reflected (N p : ℕ) :
    sieveFromTwoN N p ↔ sieveReflectedFromMidpoint N p := by
  rfl

theorem midpointReflect_involutive {N p : ℕ} (hp : p ≤ 2 * N) :
    midpointReflect N (midpointReflect N p) = p := by
  unfold midpointReflect
  omega

theorem midpointReflect_self (N : ℕ) :
    midpointReflect N N = N := by
  unfold midpointReflect
  omega

theorem midpointReflect_fixed_iff {N p : ℕ} :
    midpointReflect N p = p ↔ p = N := by
  unfold midpointReflect
  constructor
  · intro h
    omega
  · intro h
    rw [h]
    omega

/--
**Overlay survivor:** forward SoE accepts `p`, reflected prime overlay accepts
`mirror(p)`, and the scan stays on the left half `p ≤ N`.
-/
def midpointOverlaySurvivor (N p : ℕ) : Prop :=
  sieveFromTwo p ∧ sieveReflectedFromMidpoint N p ∧ p ≤ N

theorem midpointOverlaySurvivor_def (N p : ℕ) :
    midpointOverlaySurvivor N p ↔
      sieveFromTwo p ∧ sieveFromTwoN N p ∧ p ≤ N := by
  simp [midpointOverlaySurvivor, sieveReflectedFromMidpoint, sieveFromTwoN_eq_reflected]

theorem dualMidpointSurvivor_iff_overlay {N p : ℕ} :
    dualMidpointSurvivor N p ↔
      midpointOverlaySurvivor N p ∧ N ≤ midpointReflect N p := by
  unfold dualMidpointSurvivor midpointOverlaySurvivor sieveReflectedFromMidpoint
  constructor
  · intro ⟨hp, hq, hle, hge⟩
    exact ⟨⟨hp, hq, hle⟩, hge⟩
  · intro ⟨⟨hp, hq, hle⟩, hge⟩
    exact ⟨hp, hq, hle, hge⟩

theorem dualMidpointSurvivor_iff_overlay_of_left_bound {N p : ℕ} (hp : p ≤ N) :
    dualMidpointSurvivor N p ↔ midpointOverlaySurvivor N p := by
  unfold dualMidpointSurvivor midpointOverlaySurvivor sieveReflectedFromMidpoint
  constructor
  · intro ⟨hpr, hq, hle, _⟩
    exact ⟨hpr, hq, hle⟩
  · intro ⟨hpr, hq, hle⟩
    refine ⟨hpr, hq, hle, ?_⟩
    omega

/--
On the left half, bracketing is automatic: `p ≤ N` already forces `N ≤ 2N - p`.
-/
theorem overlay_left_bound_iff_dual {N p : ℕ} (h : midpointOverlaySurvivor N p) :
    dualMidpointSurvivor N p := by
  rcases h with ⟨hp, hq, hle⟩
  exact ⟨hp, hq, hle, by omega⟩

/--
**Reflection collapse (worst case `2p = 2N`).**  Self-cancellation at the mirror
survives the overlay iff `N` is prime.  Composites fail by definition — they
carry a nontrivial factor branch (`4 = 2 * 2`), not prime status.
-/
theorem midpointOverlay_diagonal_iff_prime (N : ℕ) :
    midpointOverlaySurvivor N N ↔ Nat.Prime N := by
  unfold midpointOverlaySurvivor sieveReflectedFromMidpoint midpointReflect
  have hsub : 2 * N - N = N := by omega
  simp only [hsub, sieveFromTwo]
  constructor
  · rintro ⟨h, _, _⟩
    exact h
  · intro h
    exact ⟨h, h, le_rfl⟩

theorem dualMidpointSurvivor_diagonal_iff_prime (N : ℕ) :
    dualMidpointSurvivor N N ↔ Nat.Prime N := by
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  have hsub : 2 * N - N = N := by omega
  constructor
  · intro ⟨h, _, _, _⟩
    exact h
  · intro h
    refine ⟨h, ?_, le_rfl, ?_⟩
    · rw [hsub]; exact h
    · rw [hsub]

theorem composite_misses_diagonal_overlay {N : ℕ} (hc : ¬ Nat.Prime N) :
    ¬ midpointOverlaySurvivor N N :=
  fun h => hc ((midpointOverlay_diagonal_iff_prime N).mp h)

theorem composite_misses_diagonal_survivor {N : ℕ} (hc : ¬ Nat.Prime N) :
    ¬ dualMidpointSurvivor N N :=
  fun h => hc ((dualMidpointSurvivor_diagonal_iff_prime N).mp h)

/-! #### Reflected spectrum self-cancellation (prime only) -/

/--
At the mirror slot `p = N`, the reflected overlay and forward overlay test the
**same** integer: the two spectra collapse to one slot.
-/
theorem reflected_spectrum_same_slot_at_mirror (N : ℕ) :
    sieveReflectedFromMidpoint N N ↔ sieveFromTwo N := by
  simp [sieveReflectedFromMidpoint, midpointReflect_self, sieveFromTwo]

/--
**Self-cancellation at the mirror.**  The forward and reflected prime spectra
agree on the slot `N` itself; the overlay survives at the reflection point only
when that collapsed slot is prime.  Composites such as `4 = 2 * 2` cannot
self-cancel: by definition they carry a nontrivial product branch, not prime status.
-/
def ReflectedSpectrumSelfCancel (N : ℕ) : Prop :=
  midpointOverlaySurvivor N N

theorem reflectedSpectrumSelfCancel_def (N : ℕ) :
    ReflectedSpectrumSelfCancel N ↔
      sieveFromTwo N ∧ sieveReflectedFromMidpoint N N := by
  simp [ReflectedSpectrumSelfCancel, midpointOverlaySurvivor, le_rfl]

theorem reflected_spectrum_self_cancel_iff_prime (N : ℕ) :
    ReflectedSpectrumSelfCancel N ↔ Nat.Prime N := by
  exact midpointOverlay_diagonal_iff_prime N

theorem only_primes_self_cancel_at_mirror {N : ℕ} (hN : Nat.Prime N) :
    ReflectedSpectrumSelfCancel N :=
  (reflected_spectrum_self_cancel_iff_prime N).mpr hN

theorem composite_no_reflected_self_cancel {N : ℕ} (hc : ¬ Nat.Prime N) :
    ¬ ReflectedSpectrumSelfCancel N :=
  composite_misses_diagonal_overlay hc

/--
**Composite = nontrivial product branch** (e.g. `4 = 2 * 2`).  This is the
definition side of the mirror argument: a composite cannot present as a single
prime slot, so its collapsed reflected spectrum does not self-cancel.
-/
theorem composite_has_nontrivial_factor {m : ℕ} (hm : 2 ≤ m) (hc : ¬ Nat.Prime m) :
    ∃ a b, a < m ∧ b < m ∧ a * b = m :=
  (Nat.not_prime_iff_exists_mul_eq hm).mp hc

theorem four_is_two_times_two : (2 : ℕ) * 2 = 4 := rfl

theorem not_prime_four : ¬ Nat.Prime 4 := by decide

theorem composite_four_no_self_cancel : ¬ ReflectedSpectrumSelfCancel 4 :=
  composite_no_reflected_self_cancel not_prime_four

theorem composite_four_has_two_branch :
    ∃ a b, a < 4 ∧ b < 4 ∧ a * b = 4 :=
  ⟨2, 2, by decide, by decide, four_is_two_times_two⟩

/--
Once every nontrivial product branch is rejected, the forward leg accepts the
slot as prime — the FTA reading of why self-cancellation forces primality.
-/
theorem self_cancel_implies_branch_rejection {N : ℕ} (h : ReflectedSpectrumSelfCancel N) :
    CompositeBranchRejected N := by
  intro a b ha hb hab
  have hN : Nat.Prime N := (reflected_spectrum_self_cancel_iff_prime N).mp h
  have hnp : ¬ Nat.Prime (a * b) := Nat.not_prime_mul (ne_of_gt ha) (ne_of_gt hb)
  exact hnp (hab ▸ hN)

/-- Some slot survives the forward + reflected overlay on `[0, N]`. -/
def MidpointOverlaySurvivorExists (N : ℕ) : Prop :=
  ∃ p : ℕ, midpointOverlaySurvivor N p

theorem midpointOverlaySurvivorExists_iff_dual (N : ℕ) :
    MidpointOverlaySurvivorExists N ↔ MidpointSieveSurvivorExists N := by
  constructor
  · intro ⟨p, h⟩
    exact ⟨p, overlay_left_bound_iff_dual h⟩
  · intro ⟨p, h⟩
    rcases h with ⟨hp, hq, hle, _⟩
    exact ⟨p, ⟨hp, (sieveFromTwoN_eq_reflected N p).mp hq, hle⟩⟩

/--
**User target (contrapositive).**  If the overlay finds no survivor on the left
half, the reflection point `N` must be prime — equivalent to the composite
Goldbach midpoint problem.
-/
def OverlayNoSurvivorImpliesPrime (N : ℕ) : Prop :=
  ¬ MidpointOverlaySurvivorExists N → Nat.Prime N

/--
**Composite direction (open).**  When `N` is not prime, some off-diagonal slot
must survive the overlaid reflection — not at the mirror point itself.
-/
def CompositeMidpointOverlaySurvivor (N : ℕ) : Prop :=
  ¬ Nat.Prime N → ∃ p < N, midpointOverlaySurvivor N p

theorem overlay_no_survivor_iff_composite_overlay (N : ℕ) :
    OverlayNoSurvivorImpliesPrime N ↔ CompositeMidpointOverlaySurvivor N := by
  unfold OverlayNoSurvivorImpliesPrime CompositeMidpointOverlaySurvivor
  constructor
  · intro h hc
    by_contra hall
    push_neg at hall
    have hnex : ¬ MidpointOverlaySurvivorExists N := by
      intro ⟨p, hOver⟩
      have hpLe : p ≤ N := hOver.2.2
      by_cases hpLt : p < N
      · exact hall p hpLt hOver
      · have hpEq : p = N := Nat.le_antisymm hpLe (Nat.le_of_not_gt hpLt)
        subst hpEq
        exact composite_misses_diagonal_overlay hc hOver
    exact hc (h hnex)
  · intro hComp hne
    by_contra hc
    rcases hComp hc with ⟨p, _, hOver⟩
    exact hne ⟨p, hOver⟩

/--
**Prime case (proved).**  At a prime reflection point the diagonal overlay
survives: forward and reflected tests both land on `N`.
-/
theorem midpointOverlay_survivor_of_prime {N : ℕ} (hN : Nat.Prime N) :
    MidpointOverlaySurvivorExists N :=
  ⟨N, (midpointOverlay_diagonal_iff_prime N).mpr hN⟩

theorem composite_overlay_iff_survivor_exists (N : ℕ) :
    CompositeMidpointOverlaySurvivor N ↔ MidpointOverlaySurvivorExists N := by
  unfold CompositeMidpointOverlaySurvivor
  constructor
  · intro h
    by_cases hN : Nat.Prime N
    · exact midpointOverlay_survivor_of_prime hN
    · rcases h hN with ⟨p, _, hOver⟩
      exact ⟨p, hOver⟩
  · intro ⟨p, hOver⟩
    intro hprime
    by_cases hpEq : p = N
    · subst hpEq
      exact absurd hOver (composite_misses_diagonal_overlay hprime)
    · exact ⟨p, Nat.lt_of_le_of_ne hOver.2.2 hpEq, hOver⟩

/--
**Composite kills the mirror.**  For non-prime `N`, any overlay survivor must
live strictly below the reflection point — the collapsed diagonal is excluded.
-/
theorem composite_survivor_off_diagonal {N p : ℕ} (hc : ¬ Nat.Prime N)
    (h : midpointOverlaySurvivor N p) : p < N := by
  by_contra hnot
  have hpEq : p = N := Nat.le_antisymm h.2.2 (Nat.le_of_not_gt hnot)
  subst hpEq
  exact composite_misses_diagonal_overlay hc h

/-! ### Slope scan `p + q = 2N` and modulo crossout lines -/

/--
**Left gap** `(N - p)` is the offset from the reflection point toward anchor `2`.
On the scan line this equals the right gap `(q - N)` to the partner.
-/
def midpointLeftGap (N p : ℕ) : ℕ :=
  N - p

theorem midpointLeftGap_le {N p : ℕ} :
    midpointLeftGap N p = N - p := rfl

theorem midpoint_gap_partner_gap {N p q : ℕ} (hpq : p + q = 2 * N) :
    midpointLeftGap N p = q - N := by
  unfold midpointLeftGap
  omega

/--
**Constant slope `-1` scan:** partner is `N` plus the left gap.
Reading `q = N + (N - p)` is the user's reflected slope from the mirror.
-/
theorem midpointReflect_eq_N_add_leftGap {N p : ℕ} (hp : p ≤ N) :
    midpointReflect N p = N + midpointLeftGap N p := by
  unfold midpointReflect midpointLeftGap
  omega

theorem midpoint_scan_step {N p : ℕ} (hp : p + 1 ≤ N) :
    midpointReflect N (p + 1) + 1 = midpointReflect N p := by
  unfold midpointReflect
  omega

/--
Forward SoE residue line at odd prime `r`: slot `p` is marked when `p ≡ 0 (mod r)`
(and `p > r`, i.e. a proper multiple).
-/
def forwardResidueCrossed (r p : ℕ) : Prop :=
  Nat.Prime r ∧ r < p ∧ p % r = 0

/--
Reflected overlay residue line at odd prime `r`: slot `p` is marked when
`p ≡ 2N (mod r)` (equivalently `2N - p ≡ 0 (mod r)`).
-/
def reflectResidueCrossed (N r p : ℕ) : Prop :=
  Nat.Prime r ∧ r < 2 * N - p ∧ (2 * N - p) % r = 0

/-- Both mod lines are clear at slot `p` for modulus `r`. -/
def dualModLineClear (N r p : ℕ) : Prop :=
  ¬ forwardResidueCrossed r p ∧ ¬ reflectResidueCrossed N r p

/--
**Mod-line reading (SoE geometry).**  Each prime modulus `r` throws two residue
lines on the scan: `p ≡ 0` from anchor `2` and `p ≡ 2N` from anchor `2N`.
Off-diagonal survivors are intersection points of the two stacks.  The mirror
itself is different: only primes **self-cancel** there (`ReflectedSpectrumSelfCancel`).
-/
abbrev DualModLineSurvivorReading (N p : ℕ) : Prop :=
  dualMidpointSurvivor N p

/--
Left-half scan slots for the dual sieve (anchor `2` up to reflection point `N`).
Each slot is a point on the slope-`-1` line; SoE is the union of residue lines
from anchor `2` and from anchor `2N`.
-/
def midpointScanSlots (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N)

theorem mem_midpointScanSlots_iff {N p : ℕ} :
    p ∈ midpointScanSlots N ↔ 2 ≤ p ∧ p ≤ N := by
  simp [midpointScanSlots, Finset.mem_Icc]

/-! ### Finite SoE modulus spectrum (only `r ≤ sqrt(2N)` matter) -/

/--
**Finite SoE spectrum:** Eratosthenes up to bound `M` is determined entirely by
prime moduli `r ≤ sqrt M`.  There are only finitely many such lines — this is
the "finite spectrum" in the user's argument.
-/
def soeModulusSpectrum (M : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt M)).filter Nat.Prime

/--
Primes on the midpoint scan line up to `2N` — a finite window, not an infinite tail.
-/
def midpointPrimeWindow (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (2 * N)).filter Nat.Prime

def midpointRightGap (N q : ℕ) : ℕ :=
  q - N

theorem midpoint_symmetric_gaps {N p q : ℕ} (hpq : p + q = 2 * N) (hp : p ≤ N) :
    midpointLeftGap N p = midpointRightGap N q := by
  unfold midpointLeftGap midpointRightGap
  omega

/-! ### Slope-orbit: gaps `N - p` as the scan between anchor `2` and mirror `N` -/

/--
**Gap orbit.**  As scan slots run `p : 2 … N`, left gaps `N - p` run `N-2 … 0`.
Each gap is one slope step from the mirror toward anchor `2`; the partner on the
slope-`-1` line is `N + gap` (equivalently `midpointReflect N p`).
-/
def midpointGapOrbit (N : ℕ) : Finset ℕ :=
  (midpointScanSlots N).image (midpointLeftGap N)

theorem mem_midpointGapOrbit_iff {N g : ℕ} :
    g ∈ midpointGapOrbit N ↔ ∃ p ∈ midpointScanSlots N, midpointLeftGap N p = g := by
  simp [midpointGapOrbit, Finset.mem_image]

theorem gap_eq_leftGap_of_scan {N p : ℕ} (hp : p ∈ midpointScanSlots N) :
    midpointLeftGap N p ∈ midpointGapOrbit N :=
  (mem_midpointGapOrbit_iff (N := N)).mpr ⟨p, hp, rfl⟩

/-- Left and right arms at gap `g` from mirror `N`. -/
def gapLeftArm (N g : ℕ) : ℕ := N - g

def gapRightArm (N g : ℕ) : ℕ := N + g

theorem gap_arms_sum (N g : ℕ) (hg : g ≤ N) :
    gapLeftArm N g + gapRightArm N g = 2 * N := by
  unfold gapLeftArm gapRightArm
  omega

theorem gapRightArm_eq_midpointReflect {N p : ℕ} (hp : p ≤ N) :
    gapRightArm N (midpointLeftGap N p) = midpointReflect N p := by
  unfold gapRightArm midpointLeftGap midpointReflect
  omega

theorem gapRightArm_eq_partner {N p : ℕ} (hp : p ≤ N) :
    gapRightArm N (midpointLeftGap N p) = 2 * N - p := by
  unfold gapRightArm midpointLeftGap
  omega

/--
**Symmetric prime reflection at gap `g`.**  Both arms `N ± g` are prime and the
left arm lies in the scan window — e.g. `N = 15`, gap `8` gives `7` and `23`.
-/
def symmetricPrimeReflectionAtGap (N g : ℕ) : Prop :=
  2 ≤ N - g ∧ Nat.Prime (N - g) ∧ Nat.Prime (N + g)

theorem symmetricPrimeReflectionAtGap_arm_eq {N g : ℕ} :
    symmetricPrimeReflectionAtGap N g ↔
      2 ≤ gapLeftArm N g ∧ Nat.Prime (gapLeftArm N g) ∧ Nat.Prime (gapRightArm N g) := by
  unfold symmetricPrimeReflectionAtGap gapLeftArm gapRightArm
  rfl

theorem dualMidpointSurvivor_iff_symmetric_gap {N p : ℕ} (hp : p ≤ N) :
    dualMidpointSurvivor N p ↔
      symmetricPrimeReflectionAtGap N (midpointLeftGap N p) := by
  rw [midpointLeftGap_le]
  unfold dualMidpointSurvivor symmetricPrimeReflectionAtGap sieveFromTwo sieveFromTwoN
  rw [Nat.sub_sub_self hp]
  have hadd : N + (N - p) = 2 * N - p := by omega
  rw [hadd]
  constructor
  · intro ⟨hpr, hq, _, _⟩
    exact ⟨Nat.Prime.two_le hpr, hpr, hq⟩
  · intro ⟨_, hpr, hq⟩
    exact ⟨hpr, hq, hp, by omega⟩

theorem mem_scanSlot_survivor_iff_symmetric_gap {N p : ℕ} (hp : p ∈ midpointScanSlots N) :
    dualMidpointSurvivor N p ↔
      symmetricPrimeReflectionAtGap N (midpointLeftGap N p) :=
  dualMidpointSurvivor_iff_symmetric_gap (N := N) (p := p)
    ((mem_midpointScanSlots_iff (N := N) (p := p)).mp hp).2

theorem dual_composite_survivor_off_diagonal {N p : ℕ} (hc : ¬ Nat.Prime N)
    (h : dualMidpointSurvivor N p) : p < N := by
  by_contra hnot
  have hpEq : p = N := Nat.le_antisymm h.2.2.1 (Nat.le_of_not_gt hnot)
  subst hpEq
  exact hc h.1

/--
Some gap on the slope orbit yields a symmetric prime pair `N ± g`.
-/
def MidpointSlopeOrbitPrimeHit (N : ℕ) : Prop :=
  ∃ g ∈ midpointGapOrbit N, symmetricPrimeReflectionAtGap N g

theorem midpointSlopeOrbitPrimeHit_iff_survivor (N : ℕ) :
    MidpointSlopeOrbitPrimeHit N ↔ MidpointSieveSurvivorExists N := by
  unfold MidpointSlopeOrbitPrimeHit MidpointSieveSurvivorExists
  constructor
  · rintro ⟨g, hgOrbit, hReflect⟩
    obtain ⟨p, hpSlot, hgap⟩ := (mem_midpointGapOrbit_iff (N := N)).mp hgOrbit
    have hpLe : p ≤ N := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hpSlot |>.2
    exact ⟨p, (dualMidpointSurvivor_iff_symmetric_gap (N := N) (p := p) hpLe).mpr (hgap ▸ hReflect)⟩
  · rintro ⟨p, hSurv⟩
    have hpLe : p ≤ N := hSurv.2.2.1
    refine ⟨midpointLeftGap N p, gap_eq_leftGap_of_scan (N := N) ?_, ?_⟩
    · exact (mem_midpointScanSlots_iff (N := N) (p := p)).mpr
        ⟨Nat.Prime.two_le hSurv.1, hpLe⟩
    · exact (dualMidpointSurvivor_iff_symmetric_gap (N := N) (p := p) hpLe).mp hSurv

/--
**Composite slope-orbit target (open).**  When `N` is composite, some **nonzero**
gap on the orbit between `2` and `N` reflects to a prime pair — not the mirror
diagonal `g = 0`.
-/
def CompositeSlopeOrbitForcesPrimeReflection (N : ℕ) : Prop :=
  ¬ Nat.Prime N → ∃ g ∈ midpointGapOrbit N, 0 < g ∧ symmetricPrimeReflectionAtGap N g

/--
**Finite SoE angle stack** at bound `2N`: only primes `r ≤ sqrt(2N)` throw residue
rays on the scan (`forwardResidueCrossed` / `reflectResidueCrossed`).  Same finite
spectrum as `soeModulusSpectrum (2N)` — an orbit of angles, not an infinite tail.
-/
abbrev finiteSoeAngleStack (N : ℕ) : Finset ℕ := soeModulusSpectrum (2 * N)

theorem mem_finiteSoeAngleStack_iff {N r : ℕ} :
    r ∈ finiteSoeAngleStack N ↔ r ∈ soeModulusSpectrum (2 * N) := Iff.rfl

theorem mem_finiteSoeAngleStack_iff' {N r : ℕ} :
    r ∈ finiteSoeAngleStack N ↔
      Nat.Prime r ∧ 2 ≤ r ∧ r ≤ Nat.sqrt (2 * N) := by
  simp [finiteSoeAngleStack, soeModulusSpectrum, Finset.mem_filter, Finset.mem_Icc,
    and_assoc, and_left_comm, and_comm]

/-- Constructive residue phases at scan slot `p` and modulus `r`. -/
def soeResiduePhasePair (N r p : ℕ) : ℕ × ℕ :=
  (p % r, (2 * N - p) % r)

theorem soeResiduePhasePair_fst (N r p : ℕ) :
    (soeResiduePhasePair N r p).1 = p % r := rfl

theorem soeResiduePhasePair_snd (N r p : ℕ) :
    (soeResiduePhasePair N r p).2 = (2 * N - p) % r := rfl

theorem reflectResidueCrossed_iff_mod {N r p : ℕ} :
    reflectResidueCrossed N r p ↔ Nat.Prime r ∧ r < 2 * N - p ∧ (2 * N - p) % r = 0 := by
  unfold reflectResidueCrossed
  rfl

theorem forwardResidueCrossed_iff_mod {r p : ℕ} :
    forwardResidueCrossed r p ↔ Nat.Prime r ∧ r < p ∧ p % r = 0 := by
  unfold forwardResidueCrossed
  rfl

/--
**Finite angle certificate.**  Gap `g = N - p` survives the SoE stack when every
prime modulus `r ≤ sqrt(2N)` clears both forward and reflected residue rays at `p`.
-/
def gapSurvivesFiniteAngleStack (N g : ℕ) : Prop :=
  ∀ r ∈ finiteSoeAngleStack N, dualModLineClear N r (N - g)

theorem gapSurvivesFiniteAngleStack_slot {N g : ℕ} :
    gapSurvivesFiniteAngleStack N g ↔
      ∀ r ∈ finiteSoeAngleStack N, dualModLineClear N r (N - g) := Iff.rfl

/--
**Constructive SoE crossing.**  A composite reflected partner is hit by an explicit
prime modulus from the finite stack — the spectral angle witness.
-/
theorem composite_reflected_partner_crosses_stack {N p : ℕ}
    (hp : p ∈ midpointScanSlots N) (hpr : Nat.Prime p)
    (hc : ¬ Nat.Prime (2 * N - p)) (hq : 4 ≤ 2 * N - p) :
    ∃ r ∈ finiteSoeAngleStack N, reflectResidueCrossed N r p := by
  set q := 2 * N - p
  set r := Nat.minFac q
  have hr1 : q ≠ 1 := ne_of_gt (by omega)
  have hrp : Nat.Prime r := Nat.minFac_prime hr1
  have hr2 : 2 ≤ r := hrp.two_le
  have hq2 : 2 ≤ q := by omega
  have hrq : r < q := (Nat.not_prime_iff_minFac_lt hq2).1 hc
  rcases Nat.minFac_dvd q with ⟨k, hk⟩
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push_neg at hlt
    interval_cases k
    · simp at hk; omega
    · have hqr : q = r := by simpa using hk
      exact hc (hqr ▸ Nat.minFac_prime hr1)
  have hrk : r ≤ k := Nat.minFac_le_of_dvd hk2 (Dvd.intro r (by rw [mul_comm, hk]))
  have hr_le_sqrt_q : r ≤ Nat.sqrt q :=
    Nat.le_sqrt.mpr (by
      have : r * r ≤ r * k := Nat.mul_le_mul_left r hrk
      nlinarith [hk])
  have hr_le_sqrt : r ≤ Nat.sqrt (2 * N) :=
    hr_le_sqrt_q.trans (Nat.sqrt_le_sqrt (by omega))
  have hrdiv : q % r = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd q)
  refine ⟨r, (mem_finiteSoeAngleStack_iff' (N := N)).mpr ⟨hrp, hr2, hr_le_sqrt⟩, ?_⟩
  exact ⟨hrp, hrq, hrdiv⟩

/-- A prime scan slot cannot be hit on the **forward** SoE leg by a stack modulus. -/
theorem prime_no_forward_residue_cross {p r : ℕ} (hpr : Nat.Prime p) (hrp : Nat.Prime r)
    (h : forwardResidueCrossed r p) : False := by
  rw [forwardResidueCrossed_iff_mod] at h
  obtain ⟨_, hrlt, hmod⟩ := h
  have hr_dvd : r ∣ p := Nat.dvd_of_mod_eq_zero hmod
  rcases (Nat.dvd_prime hpr).1 hr_dvd with hr1 | hrp'
  · exact Nat.not_prime_one (hr1 ▸ hrp)
  · exact ne_of_lt hrlt hrp'

/--
**Constructive stack obstruction.**  If gap `g = N - p` fails the finite angle
certificate at a prime slot `p`, some modulus in `finiteSoeAngleStack N` explicitly
crosses the reflected leg — the forward leg is impossible for prime `p`.
-/
theorem prime_slot_stack_failure_forces_reflect_cross {N p : ℕ} (hpLe : p ≤ N)
    (hpr : Nat.Prime p)
    (hFail : ¬ gapSurvivesFiniteAngleStack N (midpointLeftGap N p)) :
    ∃ r ∈ finiteSoeAngleStack N, reflectResidueCrossed N r p := by
  have hp_slot : N - midpointLeftGap N p = p := by
    unfold midpointLeftGap
    exact Nat.sub_sub_self hpLe
  rw [gapSurvivesFiniteAngleStack_slot] at hFail
  push_neg at hFail
  obtain ⟨r, hr, hNotClear⟩ := hFail
  have hNotClear' : ¬ dualModLineClear N r p := by
    simpa [dualModLineClear, hp_slot] using hNotClear
  by_cases hf : forwardResidueCrossed r p
  · exact False.elim (prime_no_forward_residue_cross hpr
      ((mem_finiteSoeAngleStack_iff' (N := N)).mp hr).1 hf)
  · by_cases hrf : reflectResidueCrossed N r p
    · exact ⟨r, hr, hrf⟩
    · exact absurd (show dualModLineClear N r p from ⟨hf, hrf⟩) hNotClear'

/--
**Crossing kills the stack certificate** at that gap — the finite SoE angle is an
explicit blocker, not a tautological rename of primality.
-/
theorem reflect_crossing_blocks_gap_stack {N g r p : ℕ} (hp : N - g = p)
    (hr : r ∈ finiteSoeAngleStack N) (hcross : reflectResidueCrossed N r p) :
    ¬ gapSurvivesFiniteAngleStack N g := by
  intro hStack
  have hclear := hStack r hr
  rw [show N - g = p from hp] at hclear
  exact hclear.2 hcross

theorem mem_soeModulusSpectrum_iff {M r : ℕ} :
    r ∈ soeModulusSpectrum M ↔ Nat.Prime r ∧ 2 ≤ r ∧ r ≤ Nat.sqrt M := by
  simp [soeModulusSpectrum, Finset.mem_filter, Finset.mem_Icc, and_assoc, and_left_comm, and_comm]

theorem nat_prime_iff_forward_stack_clear {p M : ℕ} (hp2 : 2 ≤ p) (hpM : p ≤ M) :
    Nat.Prime p ↔ ∀ r ∈ soeModulusSpectrum M, ¬ forwardResidueCrossed r p := by
  constructor
  · intro hprime r hr
    have hp := (Nat.prime_def_le_sqrt).1 hprime
    rcases (mem_soeModulusSpectrum_iff (M := M)).mp hr with ⟨hrp, _, _⟩
    rw [forwardResidueCrossed_iff_mod]
    rintro ⟨_, hrlt, hmod⟩
    have hr_dvd : r ∣ p := Nat.dvd_of_mod_eq_zero hmod
    rcases (Nat.dvd_prime hprime).1 hr_dvd with h1 | h2
    · rw [h1] at hrp
      exact Nat.not_prime_one hrp
    · exact ne_of_lt hrlt h2
  · intro h
    rw [Nat.prime_def_le_sqrt]
    refine ⟨hp2, fun m hm hms hmvd => ?_⟩
    by_cases hmp : m < p
    · have hm1 : m ≠ 1 := ne_of_gt hm
      have hrp : Nat.Prime (Nat.minFac m) := Nat.minFac_prime hm1
      have hr_lt : Nat.minFac m < p := lt_of_le_of_lt (Nat.minFac_le (by omega)) hmp
      have hr_mem : Nat.minFac m ∈ soeModulusSpectrum M := by
        refine (mem_soeModulusSpectrum_iff (M := M)).mpr ⟨hrp, hrp.two_le, ?_⟩
        exact Nat.le_trans (Nat.minFac_le (by omega : 0 < m)) (Nat.le_trans hms (Nat.sqrt_le_sqrt hpM))
      have := h (Nat.minFac m) hr_mem
      rw [forwardResidueCrossed_iff_mod] at this
      exact this ⟨hrp, hr_lt, Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.minFac_dvd m) hmvd)⟩
    · have hmp' : p ≤ m := Nat.le_of_not_gt hmp
      exfalso
      exact Nat.not_lt_of_ge hmp' (Nat.lt_of_le_of_lt hms (Nat.sqrt_lt_self (by omega)))

theorem nat_prime_iff_reflect_stack_clear {N p : ℕ} (hq2 : 2 ≤ 2 * N - p)
    (hqM : 2 * N - p ≤ 2 * N) :
    Nat.Prime (2 * N - p) ↔
      ∀ r ∈ finiteSoeAngleStack N, ¬ reflectResidueCrossed N r p := by
  set q := 2 * N - p
  have hf : finiteSoeAngleStack N = soeModulusSpectrum (2 * N) := rfl
  rw [hf, show q = 2 * N - p from rfl]
  constructor
  · intro hprime r hr
    rcases (mem_soeModulusSpectrum_iff (M := 2 * N)).mp hr with ⟨hrp, _, _⟩
    rw [reflectResidueCrossed_iff_mod]
    rintro ⟨_, hrlt, hmod⟩
    have hr_dvd : r ∣ q := Nat.dvd_of_mod_eq_zero hmod
    rcases (Nat.dvd_prime hprime).1 hr_dvd with h1 | h2
    · rw [h1] at hrp
      exact Nat.not_prime_one hrp
    · exact ne_of_lt hrlt h2
  · intro h
    rw [Nat.prime_def_le_sqrt]
    refine ⟨hq2, fun m hm hms hmvd => ?_⟩
    by_cases hmq : m < q
    · have hm1 : m ≠ 1 := ne_of_gt hm
      have hrp : Nat.Prime (Nat.minFac m) := Nat.minFac_prime hm1
      have hr_lt : Nat.minFac m < q := lt_of_le_of_lt (Nat.minFac_le (by omega)) hmq
      have hr_mem : Nat.minFac m ∈ soeModulusSpectrum (2 * N) := by
        refine (mem_soeModulusSpectrum_iff (M := 2 * N)).mpr ⟨hrp, hrp.two_le, ?_⟩
        exact Nat.le_trans (Nat.minFac_le (by omega : 0 < m)) (Nat.le_trans hms (Nat.sqrt_le_sqrt hqM))
      have := h (Nat.minFac m) hr_mem
      rw [reflectResidueCrossed_iff_mod] at this
      exact this ⟨hrp, hr_lt, Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.minFac_dvd m) hmvd)⟩
    · have hmq' : q ≤ m := Nat.le_of_not_gt hmq
      exfalso
      exact Nat.not_lt_of_ge hmq' (Nat.lt_of_le_of_lt hms (Nat.sqrt_lt_self (by omega)))

theorem gap_survives_stack_iff_symmetric_prime {N g : ℕ} (hp : 2 ≤ N - g) (hle : N - g ≤ N) :
    gapSurvivesFiniteAngleStack N g ↔ symmetricPrimeReflectionAtGap N g := by
  set p := N - g
  set q := 2 * N - p
  have hp2 : 2 ≤ p := hp
  have hq2 : 2 ≤ q := by omega
  have hqM : q ≤ 2 * N := by omega
  have hpM : p ≤ 2 * N := by omega
  rw [gapSurvivesFiniteAngleStack_slot, symmetricPrimeReflectionAtGap_arm_eq]
  unfold gapLeftArm gapRightArm
  rw [show N - g = p from by omega, show N + g = q from by omega]
  constructor
  · intro hStack
    refine ⟨hp2, (nat_prime_iff_forward_stack_clear (p := p) (M := 2 * N) hp2 hpM).mpr ?_, ?_⟩
    · intro r hr
      exact (hStack r hr).1
    · exact (nat_prime_iff_reflect_stack_clear (N := N) (p := p) hq2 hqM).mpr fun r hr =>
        (hStack r hr).2
  · intro ⟨_, hp', hq'⟩
    intro r hr
    exact ⟨
      (nat_prime_iff_forward_stack_clear (p := p) (M := 2 * N) hp2 hpM).mp hp' r hr,
      (nat_prime_iff_reflect_stack_clear (N := N) (p := p) hq2 hqM).mp hq' r hr⟩

/--
**SoE angle target (open).**  Finitely many moduli cannot kill every off-diagonal
gap on the slope orbit — equivalently some symmetric prime reflection survives.
-/
def FiniteSoeAnglesForceSlopeHit (N : ℕ) : Prop :=
  CompositeSlopeOrbitForcesPrimeReflection N

theorem finite_soe_angles_force_iff_slope (N : ℕ) :
    FiniteSoeAnglesForceSlopeHit N ↔ CompositeSlopeOrbitForcesPrimeReflection N := Iff.rfl

/--
**Constructive spectral target (open).**  Some off-diagonal gap survives the
finite angle stack — the sieve certificate before decoding to primality.
-/
def ConstructiveSpectralForcesSlopeHit (N : ℕ) : Prop :=
  ¬ Nat.Prime N → ∃ g ∈ midpointGapOrbit N, 0 < g ∧ gapSurvivesFiniteAngleStack N g

/--
**Finite extinction target (open, spectral).**  Finitely many SoE angles cannot
simultaneously cross every positive gap on the slope orbit — the pigeonhole /
interference step that must be proved constructively (not by decoding Goldbach).
-/
def FiniteStackCannotExtinctAllGaps (N : ℕ) : Prop :=
  ¬ Nat.Prime N →
    (∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) → False

theorem finite_stack_extinction_iff_constructive (N : ℕ) :
    FiniteStackCannotExtinctAllGaps N ↔ ConstructiveSpectralForcesSlopeHit N := by
  unfold FiniteStackCannotExtinctAllGaps ConstructiveSpectralForcesSlopeHit
  constructor
  · intro h hc
    by_contra hneg
    push_neg at hneg
    exact h hc fun g hg hgpos => hneg g hg hgpos
  · intro h hc hall
    rcases h hc with ⟨g, hg, hgpos, hStack⟩
    exact hall g hg hgpos hStack

theorem constructive_spectral_forces_iff_slope_hit (N : ℕ) :
    ConstructiveSpectralForcesSlopeHit N ↔ CompositeSlopeOrbitForcesPrimeReflection N := by
  unfold ConstructiveSpectralForcesSlopeHit CompositeSlopeOrbitForcesPrimeReflection
  constructor
  · intro h hc
    rcases h hc with ⟨g, hgOrbit, hgpos, hStack⟩
    obtain ⟨p, hpSlot, hgap⟩ := (mem_midpointGapOrbit_iff (N := N)).mp hgOrbit
    have hpLe : p ≤ N := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hpSlot |>.2
    have hp2 : 2 ≤ N - g := by
      have hp2' : 2 ≤ p := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hpSlot |>.1
      rw [show N - g = p from by unfold midpointLeftGap at hgap; rw [← hgap, Nat.sub_sub_self hpLe]]
      exact hp2'
    have hle : N - g ≤ N := Nat.sub_le N g
    refine ⟨g, hgOrbit, hgpos, (gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp2 hle).mp hStack⟩
  · intro h hc
    rcases h hc with ⟨g, hgOrbit, hgpos, hReflect⟩
    obtain ⟨p, hpSlot, hgap⟩ := (mem_midpointGapOrbit_iff (N := N)).mp hgOrbit
    have hpLe : p ≤ N := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hpSlot |>.2
    have hp2 : 2 ≤ N - g := by
      have hp2' : 2 ≤ p := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hpSlot |>.1
      rw [show N - g = p from by unfold midpointLeftGap at hgap; rw [← hgap, Nat.sub_sub_self hpLe]]
      exact hp2'
    have hle : N - g ≤ N := Nat.sub_le N g
    refine ⟨g, hgOrbit, hgpos, (gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp2 hle).mpr hReflect⟩

theorem finite_soe_angles_force_iff_constructive (N : ℕ) :
    FiniteSoeAnglesForceSlopeHit N ↔ ConstructiveSpectralForcesSlopeHit N := by
  rw [finite_soe_angles_force_iff_slope, constructive_spectral_forces_iff_slope_hit]

/--
If no dual survivor exists, every **prime** slot on the left scan forces a
**composite** reflected partner — each prime in the finite window is blocked on
the far leg by some modulus from `soeModulusSpectrum (2N)`.
-/
theorem no_survivor_prime_scan_forces_composite_partner {N : ℕ}
    (hne : ¬ MidpointSieveSurvivorExists N) {p : ℕ}
    (hp : p ∈ midpointScanSlots N) (hpr : Nat.Prime p) :
    ¬ Nat.Prime (2 * N - p) := by
  intro hq
  have hp' := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hp
  have hle : p ≤ N := hp'.2
  have hge : N ≤ 2 * N - p := by omega
  exact hne ⟨p, ⟨hpr, hq, hle, hge⟩⟩

/--
If no slope-orbit prime hit exists, every prime left-arm slot forces a composite
reflected partner — the gap-orbit contrapositive of `no_survivor_prime_scan_forces_composite_partner`.
-/
theorem no_slope_hit_prime_scan_forces_composite_partner {N : ℕ}
    (hne : ¬ MidpointSlopeOrbitPrimeHit N) {p : ℕ}
    (hp : p ∈ midpointScanSlots N) (hpr : Nat.Prime p) :
    ¬ Nat.Prime (2 * N - p) :=
  no_survivor_prime_scan_forces_composite_partner
    (fun h => hne ((midpointSlopeOrbitPrimeHit_iff_survivor N).mpr h)) hp hpr

/-! ### EH abelian stack: extinction forces explicit crossings -/

/-- Scan slots strictly left of the composite mirror (not necessarily prime). -/
def offDiagonalMidpointScanSlots (N : ℕ) : Finset ℕ :=
  (midpointScanSlots N).filter (fun p => p < N)

theorem mem_offDiagonalMidpointScanSlots_iff {N p : ℕ} :
    p ∈ offDiagonalMidpointScanSlots N ↔ p ∈ midpointScanSlots N ∧ p < N := by
  simp [offDiagonalMidpointScanSlots]

/-- Prime scan slots strictly left of the composite mirror (no EH unit). -/
def offDiagonalPrimeScanSlots (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (N - 1)).filter Nat.Prime

theorem mem_offDiagonalPrimeScanSlots_iff {N p : ℕ} (hN : 2 ≤ N) :
    p ∈ offDiagonalPrimeScanSlots N ↔ Nat.Prime p ∧ 2 ≤ p ∧ p < N := by
  simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hle, hpr⟩
    exact ⟨hpr, hle.1, by omega⟩
  · rintro ⟨hpr, hp2, hplt⟩
    exact ⟨⟨hp2, Nat.le_pred_of_lt hplt⟩, hpr⟩

theorem offDiagonal_prime_scan_mem_scan {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ offDiagonalPrimeScanSlots N) :
    p ∈ midpointScanSlots N := by
  rcases (mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp hp with ⟨_, hp2, hplt⟩
  exact (mem_midpointScanSlots_iff (N := N) (p := p)).mpr ⟨hp2, Nat.le_of_lt hplt⟩

theorem offDiagonal_prime_scan_mem_offDiagonal {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ offDiagonalPrimeScanSlots N) :
    p ∈ offDiagonalMidpointScanSlots N := by
  rcases (mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp hp with ⟨_, hp2, hplt⟩
  exact (mem_offDiagonalMidpointScanSlots_iff (N := N)).mpr
    ⟨(mem_midpointScanSlots_iff (N := N) (p := p)).mpr ⟨hp2, Nat.le_of_lt hplt⟩, hplt⟩

/--
**EH obstruction (proved).**  Positive-gap stack extinction plus no dual survivor forces
an explicit reflect crossing from `finiteSoeAngleStack N` at every off-diagonal prime slot.
-/
theorem eh_extinction_no_survivor_forces_reflect_cross {N : ℕ} (hN : 2 ≤ N) (_hc : ¬ Nat.Prime N)
    (hne : ¬ MidpointSieveSurvivorExists N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g)
    {p : ℕ} (hp : p ∈ offDiagonalPrimeScanSlots N) :
    ∃ r ∈ finiteSoeAngleStack N, reflectResidueCrossed N r p := by
  obtain ⟨hpr, _, hplt⟩ := (mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp hp
  have hpScan := offDiagonal_prime_scan_mem_scan hN hp
  have hpLe : p ≤ N := Nat.le_of_lt hplt
  have hg : midpointLeftGap N p ∈ midpointGapOrbit N := gap_eq_leftGap_of_scan (N := N) hpScan
  have hgpos : 0 < midpointLeftGap N p := by rw [midpointLeftGap_le]; omega
  have hFail : ¬ gapSurvivesFiniteAngleStack N (midpointLeftGap N p) :=
    hall (midpointLeftGap N p) hg hgpos
  exact prime_slot_stack_failure_forces_reflect_cross hpLe hpr hFail

/--
**EH composite unit (proved).**  Dual survivors at composite midpoints are off-diagonal.
-/
theorem eh_composite_survivor_off_diagonal {N : ℕ} (hc : ¬ Nat.Prime N) {p : ℕ}
    (h : dualMidpointSurvivor N p) : p < N :=
  dual_composite_survivor_off_diagonal hc h

/-! ### EH cardinality: off-diagonal primes exceed the finite stack -/

theorem sqrt_twoN_lt_N {N : ℕ} (hN : 4 ≤ N) : Nat.sqrt (2 * N) < N :=
  (Nat.sqrt_lt).2 (by nlinarith)

theorem two_mul_sqrt_twoN_lt_N {N : ℕ} (hN : 9 ≤ N) : 2 * Nat.sqrt (2 * N) < N := by
  set n := Nat.sqrt (2 * N)
  have hnn : n * n ≤ 2 * N := by simpa [pow_two] using Nat.sqrt_le (2 * N)
  nlinarith

theorem stack_modulus_lt_midpoint {N r : ℕ} (hN : 4 ≤ N)
    (hr : r ∈ finiteSoeAngleStack N) : r < N := by
  have hle := (mem_finiteSoeAngleStack_iff' (N := N)).mp hr |>.2.2
  exact Nat.lt_of_le_of_lt hle (sqrt_twoN_lt_N hN)

theorem finiteSoeAngleStack_subset_offDiagonal {N : ℕ} (hN : 4 ≤ N) :
    finiteSoeAngleStack N ⊆ offDiagonalPrimeScanSlots N := by
  intro r hr
  have hN3 : 3 ≤ N := by omega
  rcases (mem_finiteSoeAngleStack_iff' (N := N)).mp hr with ⟨hpr, hp2, _⟩
  exact (mem_offDiagonalPrimeScanSlots_iff (N := N) (by omega)).2
    ⟨hpr, hp2, stack_modulus_lt_midpoint hN hr⟩

/-- Bertrand supplies a prime strictly above the SoE stack cutoff. -/
theorem composite_exists_prime_above_soe_stack {N : ℕ} (hN : 4 ≤ N) (hc : ¬ Nat.Prime N) :
    ∃ p, p ∈ offDiagonalPrimeScanSlots N ∧
      Nat.sqrt (2 * N) < p ∧ p ∉ finiteSoeAngleStack N := by
  by_cases hbad : N = 5 ∨ N = 7
  · exfalso
    rcases hbad with h | h
    · subst h
      exact hc (by decide)
    · subst h
      exact hc (by decide)
  set n := Nat.sqrt (2 * N)
  have hn0 : n ≠ 0 := by
    have : 2 ≤ n := by
      calc
        2 = Nat.sqrt 4 := by norm_num
        _ ≤ Nat.sqrt (2 * N) := Nat.sqrt_le_sqrt (by omega)
    omega
  obtain ⟨p, hp, hnlt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul n hn0
  have hpLt : p < N := by
    by_contra hnot
    push_neg at hnot
    have hNp : N ≤ p := hnot
    rcases lt_or_eq_of_le hNp with hlt | heq
    · have hchain : N < 2 * n := lt_of_lt_of_le hlt hple
      by_cases h9 : 9 ≤ N
      · have h2nlt := two_mul_sqrt_twoN_lt_N h9
        simp [n] at hchain h2nlt ⊢
        omega
      · have hUb : N ≤ 8 := by
          by_contra hgt
          push_neg at hgt
          exact h9 (by omega)
        have hNval : N = 4 ∨ N = 6 ∨ N = 8 := by
          have h5 : N ≠ 5 := fun h => hbad (Or.inl h)
          have h7 : N ≠ 7 := fun h => hbad (Or.inr h)
          omega
        rcases hNval with rfl | rfl | rfl <;> norm_num [n] at hchain
    · exact hc (heq ▸ hp)
  have hpSlot : p ∈ offDiagonalPrimeScanSlots N :=
    (mem_offDiagonalPrimeScanSlots_iff (N := N) (by omega)).2
      ⟨hp, Nat.Prime.two_le hp, hpLt⟩
  refine ⟨p, hpSlot, ?_, ?_⟩
  · exact hnlt
  · intro hmem
    have hle := (mem_finiteSoeAngleStack_iff' (N := N)).mp hmem |>.2.2
    omega

theorem composite_offDiagonal_primes_gt_stack_card {N : ℕ} (hN : 4 ≤ N) (hc : ¬ Nat.Prime N) :
    Finset.card (finiteSoeAngleStack N) < Finset.card (offDiagonalPrimeScanSlots N) := by
  obtain ⟨p, hp, _, hnot⟩ := composite_exists_prime_above_soe_stack hN hc
  have hsub := finiteSoeAngleStack_subset_offDiagonal hN
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨p, hp, hnot⟩)

/-! ### EH pigeonhole: extinction forces duplicate reflect crossings -/

/-- Junk value for the pigeonhole map off the prime scan finset. -/
private def ehReflectCrossJunk (N : ℕ) : ℕ :=
  2

/--
Choose a stack modulus witnessing `reflectResidueCrossed` once extinction leaves no survivor.
-/
noncomputable def ehReflectCrossWitness {N : ℕ} (hN : 2 ≤ N) (hc : ¬ Nat.Prime N)
    (hne : ¬ MidpointSieveSurvivorExists N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g)
    (p : ℕ) (hp : p ∈ offDiagonalPrimeScanSlots N) : ℕ :=
  Classical.choose (eh_extinction_no_survivor_forces_reflect_cross hN hc hne hall hp)

noncomputable def ehStackWitnessMap {N : ℕ} (hN : 2 ≤ N) (hc : ¬ Nat.Prime N)
    (hne : ¬ MidpointSieveSurvivorExists N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) (p : ℕ) : ℕ :=
  if h : p ∈ offDiagonalPrimeScanSlots N then
    ehReflectCrossWitness hN hc hne hall p h
  else
    ehReflectCrossJunk N

theorem ehReflectCrossWitness_spec {N : ℕ} (hN : 2 ≤ N) (hc : ¬ Nat.Prime N)
    (hne : ¬ MidpointSieveSurvivorExists N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g)
    (p : ℕ) (hp : p ∈ offDiagonalPrimeScanSlots N) :
    ehReflectCrossWitness hN hc hne hall p hp ∈ finiteSoeAngleStack N ∧
      reflectResidueCrossed N (ehReflectCrossWitness hN hc hne hall p hp) p :=
  Classical.choose_spec (eh_extinction_no_survivor_forces_reflect_cross hN hc hne hall hp)

theorem ehStackWitnessMap_mem_stack {N : ℕ} (hN : 2 ≤ N) (hc : ¬ Nat.Prime N)
    (hne : ¬ MidpointSieveSurvivorExists N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g)
    {p : ℕ} (hp : p ∈ offDiagonalPrimeScanSlots N) :
    ehStackWitnessMap hN hc hne hall p ∈ finiteSoeAngleStack N := by
  simp [ehStackWitnessMap, hp]
  exact (ehReflectCrossWitness_spec hN hc hne hall p hp).1

/--
**EH pigeonhole (proved).**  When off-diagonal prime slots outnumber stack moduli, extinction
forces two distinct prime slots to share a reflect crossing modulus.
-/
theorem eh_extinction_reflect_cross_pigeonhole {N : ℕ} (hN : 2 ≤ N) (_hN4 : 4 ≤ N) (hc : ¬ Nat.Prime N)
    (hcard : Finset.card (finiteSoeAngleStack N) < Finset.card (offDiagonalPrimeScanSlots N))
    (hne : ¬ MidpointSieveSurvivorExists N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ∃ p q, p ∈ offDiagonalPrimeScanSlots N ∧ q ∈ offDiagonalPrimeScanSlots N ∧ p ≠ q ∧
      ∃ r ∈ finiteSoeAngleStack N,
        reflectResidueCrossed N r p ∧ reflectResidueCrossed N r q := by
  classical
  set f := ehStackWitnessMap hN hc hne hall
  have hmaps : Set.MapsTo f (offDiagonalPrimeScanSlots N) (finiteSoeAngleStack N) := by
    intro p hp
    exact ehStackWitnessMap_mem_stack hN hc hne hall hp
  obtain ⟨p, hp, q, hq, hne', heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  refine ⟨p, q, hp, hq, hne', ⟨f p, ehStackWitnessMap_mem_stack hN hc hne hall hp, ?_, ?_⟩⟩
  · simpa [f, ehStackWitnessMap, hp] using (ehReflectCrossWitness_spec hN hc hne hall p hp).2
  · rw [heq]
    simpa [f, ehStackWitnessMap, hq] using (ehReflectCrossWitness_spec hN hc hne hall q hq).2

theorem composite_eh_extinction_reflect_cross_pigeonhole {N : ℕ} (hN : 4 ≤ N) (hc : ¬ Nat.Prime N)
    (hne : ¬ MidpointSieveSurvivorExists N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ∃ p q, p ∈ offDiagonalPrimeScanSlots N ∧ q ∈ offDiagonalPrimeScanSlots N ∧ p ≠ q ∧
      ∃ r ∈ finiteSoeAngleStack N,
        reflectResidueCrossed N r p ∧ reflectResidueCrossed N r q :=
  eh_extinction_reflect_cross_pigeonhole (by omega) hN hc
    (composite_offDiagonal_primes_gt_stack_card hN hc) hne hall

/-! ### Inverse-Pythagorean midpoint calculus + duplicate reflect divisibility -/

/--
**Gap product square.**  The inverse-Pythagorean locus is `N · g = □` — midpoint times
left gap is a perfect square (equivalently `q² - p² = k²` for symmetric arms).
-/
def MidpointGapNgSquare (N g : ℕ) : Prop :=
  ∃ s, N * g = s * s

/--
**Inverse Pythagorean gap.**  Symmetric arms `N ± g` have a square difference
`(N+g)² - (N-g)² = k²` (hypotenuse `N+g`, leg `N-g`, height `k`).
-/
def InversePythagoreanMidpointGap (N g : ℕ) : Prop :=
  ∃ k, gapRightArm N g ^ 2 - gapLeftArm N g ^ 2 = k ^ 2

theorem symmetric_gap_arms_eq {N g : ℕ} :
    gapLeftArm N g = N - g ∧ gapRightArm N g = N + g := by
  constructor <;> rfl

theorem symmetric_gap_diff_square {N g : ℕ} (hg : g ≤ N) :
    (N + g) ^ 2 - (N - g) ^ 2 = 4 * N * g := by
  have hle : (N - g) ^ 2 ≤ (N + g) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  rw [Nat.sub_eq_iff_eq_add hle]
  simp [pow_two]
  zify
  rw [Nat.cast_sub hg]
  ring

theorem inverse_pythagorean_gap_eq_diff {N g : ℕ} :
    InversePythagoreanMidpointGap N g ↔
      ∃ k, (N + g) ^ 2 - (N - g) ^ 2 = k ^ 2 := by
  unfold InversePythagoreanMidpointGap gapLeftArm gapRightArm
  rfl

theorem inverse_pythagorean_of_ng_square {N g : ℕ} (hg : g ≤ N) :
    MidpointGapNgSquare N g → InversePythagoreanMidpointGap N g := by
  rw [inverse_pythagorean_gap_eq_diff]
  intro ⟨s, hs⟩
  refine ⟨2 * s, ?_⟩
  calc
    (N + g) ^ 2 - (N - g) ^ 2 = 4 * N * g := symmetric_gap_diff_square hg
    _ = 4 * (s * s) := by
      rw [show 4 * N * g = 4 * (N * g) from by ring, hs]
    _ = (2 * s) ^ 2 := by ring

theorem ng_square_of_inverse_pythagorean {N g : ℕ} (hg : g ≤ N) :
    InversePythagoreanMidpointGap N g → MidpointGapNgSquare N g := by
  rw [inverse_pythagorean_gap_eq_diff]
  intro ⟨k, hk⟩
  rw [symmetric_gap_diff_square hg] at hk
  have h2k : 2 ∣ k ^ 2 := by
    rw [← hk]
    exact ⟨2 * (N * g), by ring⟩
  have h2 : 2 ∣ k := Nat.prime_two.dvd_of_dvd_pow h2k
  obtain ⟨s, hs⟩ := h2
  refine ⟨s, ?_⟩
  have hk' : 4 * (N * g) = 4 * (s * s) := by
    calc
      4 * (N * g) = 4 * N * g := by ring
      _ = k ^ 2 := hk
      _ = (2 * s) ^ 2 := by rw [hs]
      _ = 4 * (s * s) := by ring
  exact Nat.mul_left_cancel (by decide : 0 < 4) hk'

theorem ng_square_iff_diff_square {N g : ℕ} (hg : g ≤ N) :
    MidpointGapNgSquare N g ↔ InversePythagoreanMidpointGap N g :=
  ⟨inverse_pythagorean_of_ng_square hg, ng_square_of_inverse_pythagorean hg⟩

theorem midpoint_cross_ratio_mul {N g : ℕ} (_hg : 0 < g) :
    N * (2 * g) = g * (2 * N) := by ring

theorem inverse_pythagorean_param_ng_square {m n : ℕ} :
    MidpointGapNgSquare (m * m) (n * n) :=
  ⟨m * n, by ring⟩

/--
**Forward primitive parametrization.**  Square midpoint and square gap produce an
inverse-Pythagorean triple on the symmetric arms: `(m²-n², 2mn, m²+n²)`.
-/
theorem inverse_pythagorean_param_forward {m n : ℕ} (hmn : n ≤ m) :
    InversePythagoreanMidpointGap (m * m) (n * n) :=
  inverse_pythagorean_of_ng_square (N := m * m) (g := n * n) (Nat.mul_le_mul hmn hmn)
    inverse_pythagorean_param_ng_square

theorem reflect_crossed_divides_partner {N r p : ℕ} (h : reflectResidueCrossed N r p) :
    r ∣ 2 * N - p := by
  rw [reflectResidueCrossed_iff_mod] at h
  exact Nat.dvd_of_mod_eq_zero h.2.2

theorem reflect_duplicate_divides_slot_diff {N p q r : ℕ}
    (hp : reflectResidueCrossed N r p) (hq : reflectResidueCrossed N r q) :
    r ∣ q - p ∨ r ∣ p - q := by
  rw [reflectResidueCrossed_iff_mod] at hp hq
  obtain ⟨a, ha⟩ := reflect_crossed_divides_partner hp
  obtain ⟨b, hb⟩ := reflect_crossed_divides_partner hq
  rcases Nat.le_total p q with h | h
  · left
    refine ⟨a - b, ?_⟩
    have hab : b ≤ a := by
      apply Nat.le_of_mul_le_mul_left _ (Nat.Prime.pos hp.1)
      rw [← hb, ← ha]
      exact Nat.sub_le_sub_left h (2 * N)
    calc
      q - p = (2 * N - p) - (2 * N - q) := by omega
      _ = r * a - r * b := by rw [ha, hb]
      _ = r * (a - b) := by rw [Nat.mul_sub_left_distrib]
  · right
    refine ⟨b - a, ?_⟩
    have hab : a ≤ b := by
      apply Nat.le_of_mul_le_mul_left _ (Nat.Prime.pos hp.1)
      rw [← ha, ← hb]
      exact Nat.sub_le_sub_left h (2 * N)
    calc
      p - q = (2 * N - q) - (2 * N - p) := by omega
      _ = r * b - r * a := by rw [hb, ha]
      _ = r * (b - a) := by rw [Nat.mul_sub_left_distrib]

theorem reflect_duplicate_slots_congr_mod {N p q r : ℕ}
    (hp : reflectResidueCrossed N r p) (hq : reflectResidueCrossed N r q) :
    p % r = q % r := by
  rw [reflectResidueCrossed_iff_mod] at hp hq
  have hp' : (2 * N) % r = p % r := by
    have hadd := Nat.add_sub_cancel' (by omega : p ≤ 2 * N)
    rw [← hadd, Nat.add_mod, hp.2.2]
    simp
  have hq' : (2 * N) % r = q % r := by
    have hadd := Nat.add_sub_cancel' (by omega : q ≤ 2 * N)
    rw [← hadd, Nat.add_mod, hq.2.2]
    simp
  rw [← hp', hq']

/-- Bundle for duplicate reflect output from extinction + pigeonhole. -/
structure ReflectDuplicateCrossing (N : ℕ) where
  slot_a : ℕ
  slot_b : ℕ
  r : ℕ
  ha : slot_a ∈ offDiagonalPrimeScanSlots N
  hb : slot_b ∈ offDiagonalPrimeScanSlots N
  hne : slot_a ≠ slot_b
  hr : r ∈ finiteSoeAngleStack N
  hcross_a : reflectResidueCrossed N r slot_a
  hcross_b : reflectResidueCrossed N r slot_b

theorem ReflectDuplicateCrossing.divides_slot_diff {N : ℕ} (h : ReflectDuplicateCrossing N) :
    h.r ∣ h.slot_b - h.slot_a ∨ h.r ∣ h.slot_a - h.slot_b :=
  reflect_duplicate_divides_slot_diff h.hcross_a h.hcross_b

theorem ReflectDuplicateCrossing.slots_congr_mod {N : ℕ} (h : ReflectDuplicateCrossing N) :
    h.slot_a % h.r = h.slot_b % h.r :=
  reflect_duplicate_slots_congr_mod h.hcross_a h.hcross_b

theorem reflect_duplicate_gaps_congr_mod {N p q r : ℕ}
    (hpLe : p ≤ N) (hqLe : q ≤ N)
    (hp : reflectResidueCrossed N r p) (hq : reflectResidueCrossed N r q) :
    midpointLeftGap N p % r = midpointLeftGap N q % r := by
  dsimp [midpointLeftGap]
  exact (Nat.ModEq.sub_left hpLe hqLe (reflect_duplicate_slots_congr_mod hp hq))

theorem reflect_duplicate_divides_q_sub_p_of_lt {N p q r : ℕ}
    (hp : reflectResidueCrossed N r p) (hq : reflectResidueCrossed N r q) (hlt : p < q) :
    r ∣ q - p := by
  rw [reflectResidueCrossed_iff_mod] at hp hq
  obtain ⟨a, ha⟩ := reflect_crossed_divides_partner hp
  obtain ⟨b, hb⟩ := reflect_crossed_divides_partner hq
  refine ⟨a - b, ?_⟩
  have hab : b ≤ a := by
    apply Nat.le_of_mul_le_mul_left _ (Nat.Prime.pos hp.1)
    rw [← hb, ← ha]
    exact Nat.sub_le_sub_left (Nat.le_of_lt hlt) (2 * N)
  calc
    q - p = (2 * N - p) - (2 * N - q) := by omega
    _ = r * a - r * b := by rw [ha, hb]
    _ = r * (a - b) := by rw [Nat.mul_sub_left_distrib]

theorem reflect_duplicate_gap_sep_ge_r {N p q r : ℕ}
    (hp : reflectResidueCrossed N r p) (hq : reflectResidueCrossed N r q) (hlt : p < q) :
    r ≤ q - p :=
  Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) (reflect_duplicate_divides_q_sub_p_of_lt hp hq hlt)

theorem gap_arm_product_square {N g : ℕ} (hg : g ≤ N) :
    (N - g) * (N + g) = N * N - g * g := by
  have hle : g * g ≤ N * N := Nat.mul_le_mul hg hg
  have hZ : ((N : ℤ) - g) * ((N : ℤ) + g) = (N : ℤ) * N - (g : ℤ) * g := by ring
  apply Nat.cast_inj (R := ℤ).1
  push_cast
  conv_lhs => rw [Nat.cast_sub hg]
  conv_rhs => rw [Nat.cast_sub hle]
  exact hZ

theorem ReflectDuplicateCrossing.gaps_congr_mod {N : ℕ} (c : ReflectDuplicateCrossing N) :
    midpointLeftGap N c.slot_a % c.r = midpointLeftGap N c.slot_b % c.r := by
  have hN : 2 ≤ N := by
    by_contra hlt
    push_neg at hlt
    have : c.slot_a ∉ offDiagonalPrimeScanSlots N := by
      simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc]
      omega
    exact this c.ha
  have hpLe : c.slot_a ≤ N :=
    Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.ha |>.2.2)
  have hqLe : c.slot_b ≤ N :=
    Nat.le_of_lt ((mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.hb |>.2.2)
  exact reflect_duplicate_gaps_congr_mod hpLe hqLe c.hcross_a c.hcross_b

theorem ReflectDuplicateCrossing.gap_sep_ge_r {N : ℕ} (c : ReflectDuplicateCrossing N)
    (hlt : c.slot_a < c.slot_b) : c.r ≤ c.slot_b - c.slot_a := by
  exact reflect_duplicate_gap_sep_ge_r c.hcross_a c.hcross_b hlt

theorem ReflectDuplicateCrossing.arm_product_left {N : ℕ} (c : ReflectDuplicateCrossing N) :
    c.slot_a * (2 * N - c.slot_a) =
      N * N - (midpointLeftGap N c.slot_a) * (midpointLeftGap N c.slot_a) := by
  have hN : 2 ≤ N := by
    by_contra hlt
    push_neg at hlt
    have : c.slot_a ∉ offDiagonalPrimeScanSlots N := by
      simp [offDiagonalPrimeScanSlots, Finset.mem_filter, Finset.mem_Icc]
      omega
    exact this c.ha
  have hpLt : c.slot_a < N := (mem_offDiagonalPrimeScanSlots_iff (N := N) hN).mp c.ha |>.2.2
  have hpLe : c.slot_a ≤ N := Nat.le_of_lt hpLt
  unfold midpointLeftGap
  have hg : N - c.slot_a ≤ N := Nat.sub_le _ _
  have h1 : c.slot_a * (2 * N - c.slot_a) = (N - (N - c.slot_a)) * (N + (N - c.slot_a)) := by
    rw [Nat.sub_sub_self hpLe]
    congr 1
    omega
  rw [h1, gap_arm_product_square hg]

theorem composite_extinction_reflect_duplicate {N : ℕ} (hN : 4 ≤ N) (hc : ¬ Nat.Prime N)
    (hne : ¬ MidpointSieveSurvivorExists N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ∃ _c : ReflectDuplicateCrossing N, True := by
  obtain ⟨p, q, hp, hq, hne', r, hr, hcrossp, hcrossq⟩ :=
    composite_eh_extinction_reflect_cross_pigeonhole hN hc hne hall
  exact ⟨⟨p, q, r, hp, hq, hne', hr, hcrossp, hcrossq⟩, trivial⟩

/--
**EH inverse-triple obstruction (open).**  Duplicate reflect forces a symmetric prime gap
on the `N · g = □` locus — the Diophantine normal form before stack decode.
-/
def EckmannHiltonInverseTripleObstruction (N : ℕ) : Prop :=
  ∀ {p q r : ℕ}, p ∈ offDiagonalPrimeScanSlots N → q ∈ offDiagonalPrimeScanSlots N →
    p ≠ q → r ∈ finiteSoeAngleStack N →
    reflectResidueCrossed N r p → reflectResidueCrossed N r q →
    ∃ g ∈ midpointGapOrbit N, 0 < g ∧ symmetricPrimeReflectionAtGap N g ∧
      MidpointGapNgSquare N g

/--
**EH cardinality obstruction (open).**  A duplicate reflect crossing forces some positive gap
to survive the abelian stack — the final interference step before Goldbach decode.
-/
def EckmannHiltonCardinalityObstruction (N : ℕ) : Prop :=
  ∀ {p q r : ℕ}, p ∈ offDiagonalPrimeScanSlots N → q ∈ offDiagonalPrimeScanSlots N → p ≠ q →
    r ∈ finiteSoeAngleStack N →
    reflectResidueCrossed N r p → reflectResidueCrossed N r q →
    ∃ g ∈ midpointGapOrbit N, 0 < g ∧ gapSurvivesFiniteAngleStack N g

theorem inverse_triple_obstruction_implies_cardinality {N : ℕ}
    (hOb : EckmannHiltonInverseTripleObstruction N) :
    EckmannHiltonCardinalityObstruction N :=
  fun hp hq hne hr hcrossp hcrossq => by
    obtain ⟨g, hg, hgpos, hsymm, _⟩ := hOb hp hq hne hr hcrossp hcrossq
    have hp2 : 2 ≤ N - g := hsymm.1
    have hle : N - g ≤ N := Nat.sub_le N g
    exact ⟨g, hg, hgpos, (gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp2 hle).mpr hsymm⟩

def EckmannHiltonForwardCollapse (N : ℕ) : Prop :=
  FiniteStackCannotExtinctAllGaps N

theorem eckmann_hilton_forward_collapse_iff_constructive (N : ℕ) :
    EckmannHiltonForwardCollapse N ↔ ConstructiveSpectralForcesSlopeHit N := by
  unfold EckmannHiltonForwardCollapse
  exact finite_stack_extinction_iff_constructive N

/-! #### Example: `16 = 5 + 11` at reflection midpoint `N = 8` -/

theorem nat_prime_five : Nat.Prime 5 := by decide
theorem nat_prime_eleven : Nat.Prime 11 := by decide
theorem not_prime_eight : ¬ Nat.Prime 8 := by decide

theorem goldbach_midpoint_pair_eight_five_eleven : GoldbachMidpointPair 8 5 11 := by
  refine ⟨nat_prime_five, nat_prime_eleven, by omega, by omega, by omega⟩

theorem dual_midpoint_survivor_eight_five : dualMidpointSurvivor 8 5 := by
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  refine ⟨nat_prime_five, nat_prime_eleven, by omega, by omega⟩

theorem midpointOverlay_survivor_eight_five : midpointOverlaySurvivor 8 5 := by
  refine ⟨nat_prime_five, ?_, by omega⟩
  simpa [sieveReflectedFromMidpoint, midpointReflect] using nat_prime_eleven

theorem midpoint_leftGap_eight_five : midpointLeftGap 8 5 = 3 := by decide

theorem midpointReflect_eight_five : midpointReflect 8 5 = 11 := by decide

/-! #### Example: `30 = 7 + 23` at reflection midpoint `N = 15` -/

theorem nat_prime_seven : Nat.Prime 7 := by decide
theorem nat_prime_twentythree : Nat.Prime 23 := by decide
theorem not_prime_fifteen : ¬ Nat.Prime 15 := by decide

theorem goldbach_midpoint_pair_fifteen_seven_twentythree :
    GoldbachMidpointPair 15 7 23 := by
  refine ⟨nat_prime_seven, nat_prime_twentythree, by omega, by omega, by omega⟩

theorem dual_midpoint_survivor_fifteen_seven : dualMidpointSurvivor 15 7 := by
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  refine ⟨nat_prime_seven, nat_prime_twentythree, by omega, by omega⟩

theorem midpoint_symmetric_gap_fifteen_seven :
    midpointLeftGap 15 7 = 8 ∧ midpointRightGap 15 23 = 8 := by
  constructor <;> decide

theorem composite_fifteen_no_self_cancel : ¬ ReflectedSpectrumSelfCancel 15 :=
  composite_no_reflected_self_cancel not_prime_fifteen

/--
**Strict dual survivor** (odd-midpoint / four-leg form): both arms strictly below
and above `N`, excluding the diagonal `N + N`.
-/
def dualMidpointSurvivorStrict (N p : ℕ) : Prop :=
  sieveFromTwo p ∧ sieveFromTwoN N p ∧ p < N ∧ N < 2 * N - p

instance (N p : ℕ) : Decidable (dualMidpointSurvivor N p) := by
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  infer_instance

/--
**Left half only:** from anchor `2` up to the midpoint `N`.  The from-`2N` leg is
determined by reflection `q = 2N - p`; any survivor has `p ≤ N`, so scanning
`p ∈ [0, N]` is sufficient.
-/
def dualMidpointLeftCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun p => dualMidpointSurvivor N p)

theorem mem_goldbachMidpointCandidates_iff (N p : ℕ) :
    p ∈ goldbachMidpointCandidates N ↔ dualMidpointSurvivor N p := by
  simp only [goldbachMidpointCandidates, dualMidpointSurvivor, sieveFromTwo, sieveFromTwoN,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hp, hq, hle, hge⟩
    exact ⟨hp, hq, hle, hge⟩
  · intro ⟨hp, hq, hle, hge⟩
    exact ⟨Nat.lt_succ_iff.mpr (by omega), hp, hq, hle, hge⟩

theorem mem_dualMidpointLeftCandidates_iff (N p : ℕ) :
    p ∈ dualMidpointLeftCandidates N ↔ dualMidpointSurvivor N p := by
  simp only [dualMidpointLeftCandidates, dualMidpointSurvivor, sieveFromTwo, sieveFromTwoN,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hp, hq, hle, hge⟩
    exact ⟨hp, hq, hle, hge⟩
  · intro ⟨hp, hq, hle, hge⟩
    exact ⟨Nat.lt_succ_iff.mpr hle, hp, hq, hle, hge⟩

/--
Scan table for `N = 8` (`2N = 16`): only `p ∈ {3, 5}` survive both mod stacks;
`5` is the off-diagonal witness yielding `5 + 11`.
-/
theorem dualMidpointLeftCandidates_eight :
    dualMidpointLeftCandidates 8 = ({3, 5} : Finset ℕ) := by decide

/--
Scan table for `N = 15` (`2N = 30`): finitely many SoE lines `{2,3,5}` cannot
kill every slot — survivors `{7, 11, 13}` remain with symmetric gaps `±8` at `7+23`.
-/
theorem dualMidpointLeftCandidates_fifteen :
    dualMidpointLeftCandidates 15 = ({7, 11, 13} : Finset ℕ) := by decide

theorem dualMidpointSurvivor_left_bound {N p : ℕ} (h : dualMidpointSurvivor N p) :
    p ≤ N := by
  rcases h with ⟨_, _, hle, _⟩
  exact hle

theorem dualMidpointSurvivor_partner_eq {N p : ℕ} (h : dualMidpointSurvivor N p) :
    p + (2 * N - p) = 2 * N := by
  rcases h with ⟨_, _, hle, hge⟩
  have hpLe : p ≤ 2 * N := by omega
  exact Nat.add_sub_cancel' hpLe

/--
The global candidate finset agrees with the left-half scan: survivors force
`p ≤ N`, so nothing above `N` can appear.
-/
theorem goldbachMidpointCandidates_eq_leftCandidates (N : ℕ) :
    goldbachMidpointCandidates N = dualMidpointLeftCandidates N := by
  ext p
  constructor
  · intro hp
    have hs := (mem_goldbachMidpointCandidates_iff N p).mp hp
    exact (mem_dualMidpointLeftCandidates_iff N p).mpr hs
  · intro hp
    have hs := (mem_dualMidpointLeftCandidates_iff N p).mp hp
    exact (mem_goldbachMidpointCandidates_iff N p).mpr hs

theorem goldbachMidpointCount_eq_leftCount (N : ℕ) :
    goldbachMidpointCount N = (dualMidpointLeftCandidates N).card := by
  simp [goldbachMidpointCount, goldbachMidpointCandidates_eq_leftCandidates]

/--
**Prime escape hatch:** if no off-diagonal pair is found, a prime midpoint still
survives via the diagonal branch `p = q = N`.
-/
def MidpointSieveOrPrime (N : ℕ) : Prop :=
  MidpointSieveSurvivorExists N ∨ Nat.Prime N

theorem dual_midpoint_survivor_diagonal (N : ℕ) (hN : Nat.Prime N) :
    dualMidpointSurvivor N N := by
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  have hsub : 2 * N - N = N := by omega
  refine ⟨hN, ?_, le_rfl, ?_⟩
  · rw [hsub]; exact hN
  · rw [hsub]

theorem midpoint_sieve_survivor_of_prime {N : ℕ} (hN : Nat.Prime N) :
    MidpointSieveSurvivorExists N :=
  ⟨N, dual_midpoint_survivor_diagonal N hN⟩

theorem midpoint_sieve_or_prime_of_prime {N : ℕ} (hN : Nat.Prime N) :
    MidpointSieveOrPrime N :=
  Or.inl (midpoint_sieve_survivor_of_prime hN)

theorem goldbachMidpointCount_pos_of_prime {N : ℕ} (hN : Nat.Prime N) :
    0 < goldbachMidpointCount N := by
  rw [goldbachMidpointCount_eq_leftCount]
  refine Finset.card_pos.mpr ⟨N, ?_⟩
  exact (mem_dualMidpointLeftCandidates_iff N N).mpr (dual_midpoint_survivor_diagonal N hN)

/--
**Contrapositive target (composite direction).**  If the midpoint is not prime,
some left-half slot must survive both sieves.  This is the entire unresolved
Goldbach midpoint problem in one line.
-/
def CompositeMidpointHasSurvivor (N : ℕ) : Prop :=
  ¬ Nat.Prime N → MidpointSieveSurvivorExists N

theorem composite_midpoint_has_survivor_eight : CompositeMidpointHasSurvivor 8 := by
  intro _
  exact ⟨5, dual_midpoint_survivor_eight_five⟩

theorem composite_midpoint_has_survivor_fifteen : CompositeMidpointHasSurvivor 15 := by
  intro _
  exact ⟨7, dual_midpoint_survivor_fifteen_seven⟩

theorem composite_slope_orbit_forces_iff_has_survivor (N : ℕ) :
    CompositeSlopeOrbitForcesPrimeReflection N ↔ CompositeMidpointHasSurvivor N := by
  unfold CompositeSlopeOrbitForcesPrimeReflection CompositeMidpointHasSurvivor
  constructor
  · intro hSlope hc
    rcases hSlope hc with ⟨g, hgOrbit, _, hReflect⟩
    exact (midpointSlopeOrbitPrimeHit_iff_survivor N).mp ⟨g, hgOrbit, hReflect⟩
  · intro hHas hc
    rcases hHas hc with ⟨p, hSurv⟩
    have hpLe : p ≤ N := hSurv.2.2.1
    have hpLt : p < N := dual_composite_survivor_off_diagonal hc hSurv
    refine ⟨midpointLeftGap N p, gap_eq_leftGap_of_scan (N := N) ?_, by unfold midpointLeftGap; omega,
      (dualMidpointSurvivor_iff_symmetric_gap (N := N) (p := p) hpLe).mp hSurv⟩
    exact (mem_midpointScanSlots_iff (N := N) (p := p)).mpr
      ⟨Nat.Prime.two_le hSurv.1, hpLe⟩

/--
**EH forward collapse (open = Goldbach midpoint).**  The abelian meet cannot kill every
positive gap while the mirror lacks the EH unit.
-/
theorem eckmann_hilton_forward_collapse_iff_composite (N : ℕ) :
    EckmannHiltonForwardCollapse N ↔ CompositeMidpointHasSurvivor N := by
  rw [eckmann_hilton_forward_collapse_iff_constructive, constructive_spectral_forces_iff_slope_hit,
      composite_slope_orbit_forces_iff_has_survivor]

theorem eh_extinction_no_dual_survivor {N : ℕ} (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ¬ MidpointSieveSurvivorExists N := by
  intro ⟨p, hSurv⟩
  by_cases hpEq : p = N
  · exact hc ((dualMidpointSurvivor_diagonal_iff_prime N).mp (hpEq ▸ hSurv))
  · have hpLe : p ≤ N := hSurv.2.2.1
    have hpSlot : p ∈ midpointScanSlots N :=
      (mem_midpointScanSlots_iff (N := N) (p := p)).mpr
        ⟨Nat.Prime.two_le hSurv.1, hpLe⟩
    set g := midpointLeftGap N p
    have hg : g ∈ midpointGapOrbit N := gap_eq_leftGap_of_scan (N := N) hpSlot
    have hgap : N - p = g := (midpointLeftGap_le (N := N) (p := p)).symm
    have hgpos : 0 < g := by rw [← hgap]; omega
    have hp2 : 2 ≤ N - g := by rw [show N - g = p from by omega]; exact Nat.Prime.two_le hSurv.1
    have hle : N - g ≤ N := Nat.sub_le N g
    have hReflect : symmetricPrimeReflectionAtGap N g :=
      (dualMidpointSurvivor_iff_symmetric_gap (N := N) (p := p) hpLe).mp hSurv
    exact absurd ((gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp2 hle).mpr hReflect)
      (hall g hg hgpos)

/--
**EH cardinality collapse (proved modulo obstruction).**  Duplicate reflect crossings force a
stack survivor once the cardinality obstruction holds.
-/
theorem eckmann_hilton_forward_collapse_of_cardinality_obstruction {N : ℕ} (hN : 4 ≤ N)
    (hOb : EckmannHiltonCardinalityObstruction N) : EckmannHiltonForwardCollapse N := by
  intro hc hall
  have hne := eh_extinction_no_dual_survivor hc hall
  rcases composite_eh_extinction_reflect_cross_pigeonhole hN hc hne hall with
    ⟨p, q, hp, hq, hne', r, hr, hcrossp, hcrossq⟩
  rcases hOb hp hq hne' hr hcrossp hcrossq with ⟨g, hg, hgpos, hStack⟩
  exact hall g hg hgpos hStack

theorem finite_soe_angles_force_iff_composite (N : ℕ) :
    FiniteSoeAnglesForceSlopeHit N ↔ CompositeMidpointHasSurvivor N := by
  rw [finite_soe_angles_force_iff_slope, composite_slope_orbit_forces_iff_has_survivor]

theorem composite_slope_orbit_forces_eight : CompositeSlopeOrbitForcesPrimeReflection 8 := by
  intro _
  exact ⟨3, gap_eq_leftGap_of_scan (N := 8) (p := 5) (by decide),
    by decide, (dualMidpointSurvivor_iff_symmetric_gap (N := 8) (p := 5) (by omega)).mp
      dual_midpoint_survivor_eight_five⟩

theorem composite_slope_orbit_forces_fifteen : CompositeSlopeOrbitForcesPrimeReflection 15 := by
  intro _
  exact ⟨8, gap_eq_leftGap_of_scan (N := 15) (p := 7) (by decide),
    by decide, (dualMidpointSurvivor_iff_symmetric_gap (N := 15) (p := 7) (by omega)).mp
      dual_midpoint_survivor_fifteen_seven⟩

theorem symmetric_prime_reflection_fifteen_eight : symmetricPrimeReflectionAtGap 15 8 := by
  exact (dualMidpointSurvivor_iff_symmetric_gap (N := 15) (p := 7) (by omega)).mp
    dual_midpoint_survivor_fifteen_seven

theorem symmetric_prime_reflection_eight_three : symmetricPrimeReflectionAtGap 8 3 := by
  exact (dualMidpointSurvivor_iff_symmetric_gap (N := 8) (p := 5) (by omega)).mp
    dual_midpoint_survivor_eight_five

theorem midpoint_gap_orbit_fifteen_eight : (8 : ℕ) ∈ midpointGapOrbit 15 := by
  refine (mem_midpointGapOrbit_iff (N := 15)).mpr ⟨7, ?_, by decide⟩
  exact (mem_midpointScanSlots_iff (N := 15) (p := 7)).mpr ⟨by decide, by decide⟩

theorem midpoint_gap_orbit_eight_three : (3 : ℕ) ∈ midpointGapOrbit 8 := by
  refine (mem_midpointGapOrbit_iff (N := 8)).mpr ⟨5, ?_, by decide⟩
  exact (mem_midpointScanSlots_iff (N := 8) (p := 5)).mpr ⟨by decide, by decide⟩

/--
**Finite-spectrum target (open).**  Composite midpoints cannot self-cancel; the
conjecture is that finitely many SoE modulus lines (`r ≤ sqrt(2N)`) — the
`finiteSoeAngleStack` — cannot kill every off-diagonal gap on the slope orbit
(`CompositeSlopeOrbitForcesPrimeReflection`); some symmetric `(± gap)` prime
reflection must survive.
-/
def FiniteSoeSpectrumForcesOffDiagonalSurvivor (N : ℕ) : Prop :=
  CompositeMidpointHasSurvivor N

theorem finite_soe_spectrum_forces_iff_composite (N : ℕ) :
    FiniteSoeSpectrumForcesOffDiagonalSurvivor N ↔ CompositeMidpointHasSurvivor N :=
  Iff.rfl

/--
**No-survivor ⇒ prime** — the user's reformulation.  Logically equivalent to
`CompositeMidpointHasSurvivor` for each fixed `N`.
-/
def MidpointNoSurvivorImpliesPrime (N : ℕ) : Prop :=
  ¬ MidpointSieveSurvivorExists N → Nat.Prime N

theorem midpoint_no_survivor_iff_composite_survivor (N : ℕ) :
    MidpointNoSurvivorImpliesPrime N ↔ CompositeMidpointHasSurvivor N := by
  unfold MidpointNoSurvivorImpliesPrime CompositeMidpointHasSurvivor
  tauto

/-! ### Forward SOE play: equidistant partner across the mirror

**Build order (constructive / spectral).**

1. **Spectral SoE at each scan slot** — joint line `(p)^{-s}(2N-p)^{-s}` and Euler
   synthesis `(1-p^{-s})(1-(2N-p)^{-s})` (`S3SoeSpectralBuild.soeSlotSpectralChannel`).
2. **Additive SoE legs** — forward `sieveFromTwo`, reflected `sieveFromTwoN`; finite
   angle stack `finiteSoeAngleStack` throws residue rays.
3. **Decode** — stack certificate ⟺ symmetric primes ⟺ spectral/Euler nonzero on strip.

**What is proved about reflections (read carefully).**

| Statement | Status |
|-----------|--------|
| Mirror slot `p = N` reflects prime ⟺ `N` is prime | **Proved** |
| Composite `N` ⟹ no mirror reflection | **Proved** |
| Composite `N` ⟹ some off-diagonal reflection | **Open** (= Goldbach midpoint) |
| Off-diagonal reflection ⟹ `N` composite | **False** (e.g. `N = 5`, `3 + 7`) |
| No scan reflection ⟹ `N` prime | **Open** (contrapositive of Goldbach) |

Finding a reflection does **not** mean `N` isn't prime — only the **mirror slot**
is a prime-characteristic diagonal.
-/
abbrev equidistantPartner (N p : ℕ) := midpointReflect N p

theorem equidistantPartner_spec (N p : ℕ) : equidistantPartner N p = 2 * N - p := rfl

theorem equidistantPartner_involutive {N p : ℕ} (hp : p ≤ 2 * N) :
    equidistantPartner N (equidistantPartner N p) = p :=
  midpointReflect_involutive hp

theorem equidistantPartner_self_iff (N p : ℕ) :
    equidistantPartner N p = p ↔ p = N :=
  midpointReflect_fixed_iff (N := N) (p := p)

theorem equidistant_gaps_match (N p : ℕ) (hp : p ≤ N) :
    midpointLeftGap N p = midpointRightGap N (equidistantPartner N p) := by
  unfold midpointLeftGap midpointRightGap equidistantPartner midpointReflect
  omega

theorem off_mirror_iff_lt (N p : ℕ) (hp : p ≤ N) :
    p < N ↔ equidistantPartner N p ≠ p := by
  constructor
  · intro hlt hEq
    have hfix := (equidistantPartner_self_iff (N := N) (p := p)).mp hEq
    omega
  · intro hne
    by_contra hlt
    push_neg at hlt
    have hpEq : p = N := Nat.le_antisymm hp hlt
    exact absurd (hpEq ▸ (equidistantPartner_self_iff (N := N) (p := N)).mpr rfl) hne

theorem partner_ge_midpoint_of_scanSlot {N p : ℕ} (hp : p ∈ midpointScanSlots N) :
    N ≤ equidistantPartner N p := by
  unfold equidistantPartner midpointReflect
  have hpLe := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hp |>.2
  omega

/-- **Symmetric prime reflection at slot `p`:** both equidistant legs are prime. -/
def symmetricPrimeReflectionAt (N p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (equidistantPartner N p)

theorem symmetricPrimeReflectionAt_iff_gap {N p : ℕ} (hp : p ≤ N) :
    symmetricPrimeReflectionAt N p ↔ symmetricPrimeReflectionAtGap N (midpointLeftGap N p) := by
  rw [← dualMidpointSurvivor_iff_symmetric_gap (N := N) (p := p) hp]
  have hge : N ≤ equidistantPartner N p := by
    unfold equidistantPartner midpointReflect
    omega
  unfold symmetricPrimeReflectionAt equidistantPartner dualMidpointSurvivor
  constructor
  · rintro ⟨hpr, hq⟩
    exact ⟨hpr, hq, hp, hge⟩
  · rintro ⟨hpr, hq, _, _⟩
    exact ⟨hpr, hq⟩

theorem scan_slot_reflection_iff_survivor {N p : ℕ} (hp : p ∈ midpointScanSlots N) :
    symmetricPrimeReflectionAt N p ↔ dualMidpointSurvivor N p := by
  have hpLe := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hp
  have hge : N ≤ equidistantPartner N p := partner_ge_midpoint_of_scanSlot hp
  unfold symmetricPrimeReflectionAt equidistantPartner dualMidpointSurvivor
  constructor
  · intro ⟨hpr, hq⟩
    exact ⟨hpr, hq, hpLe.2, hge⟩
  · intro h
    exact ⟨h.1, h.2.1⟩

/-- **Forward SoE scan** from anchor `2` to anchor `2N`. -/
def soeForwardScan (N : ℕ) : Finset ℕ := Finset.Icc 2 (2 * N)

theorem mem_soeForwardScan_iff {N x : ℕ} :
    x ∈ soeForwardScan N ↔ 2 ≤ x ∧ x ≤ 2 * N := by
  simp [soeForwardScan, Finset.mem_Icc]

/-- Anchor-`2` even markers: `2, 4, …, 2N` — at `N = 4` this is `{2,4,6,8}`. -/
def soeAnchorTwoSpectrum (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).image (fun k => 2 * k)

theorem soe_anchor_two_spectrum_four : soeAnchorTwoSpectrum 4 = {2, 4, 6, 8} := by decide

/-- Modulus-`r` hit line on the scan — at `N = 4`, `r = 3` gives `{3,6}`. -/
def soeModulusHitLine (N r : ℕ) : Finset ℕ :=
  (soeForwardScan N).filter (fun x => x % r = 0)

theorem soe_modulus_hit_line_four_three : soeModulusHitLine 4 3 = {3, 6} := by decide

/-- Off-diagonal prime reflection: scan slot strictly left of the mirror. -/
def offDiagonalPrimeReflection (N : ℕ) : Prop :=
  ∃ p ∈ midpointScanSlots N, p < N ∧ symmetricPrimeReflectionAt N p

theorem offDiagonalPrimeReflection_iff_positive_slope_hit (N : ℕ) :
    offDiagonalPrimeReflection N ↔
      ∃ g ∈ midpointGapOrbit N, 0 < g ∧ symmetricPrimeReflectionAtGap N g := by
  unfold offDiagonalPrimeReflection
  constructor
  · rintro ⟨p, hpSlot, hplt, hReflect⟩
    refine ⟨midpointLeftGap N p, gap_eq_leftGap_of_scan (N := N) hpSlot, ?_, ?_⟩
    · unfold midpointLeftGap; omega
    · exact (symmetricPrimeReflectionAt_iff_gap (N := N) (p := p)
        ((mem_midpointScanSlots_iff (N := N) (p := p)).mp hpSlot).2).mp hReflect
  · rintro ⟨g, hgOrbit, hgpos, hGap⟩
    obtain ⟨p, hpSlot, hgap⟩ := (mem_midpointGapOrbit_iff (N := N)).mp hgOrbit
    have hpLe := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hpSlot |>.2
    have hplt : p < N := by
      have hgap' : N - p = g := by dsimp [midpointLeftGap] at hgap; exact hgap
      omega
    exact ⟨p, hpSlot, hplt,
      (symmetricPrimeReflectionAt_iff_gap (N := N) (p := p) hpLe).mpr (hgap ▸ hGap)⟩

def SOEForwardForcesOffDiagonalReflection (N : ℕ) : Prop :=
  ¬ Nat.Prime N → offDiagonalPrimeReflection N

theorem offDiagonalPrimeReflection_iff_composite_slope (N : ℕ) :
    SOEForwardForcesOffDiagonalReflection N ↔ CompositeMidpointHasSurvivor N := by
  unfold SOEForwardForcesOffDiagonalReflection CompositeMidpointHasSurvivor
  constructor
  · intro h hc
    rcases h hc with ⟨p, hpSlot, _, hReflect⟩
    exact ⟨p, (scan_slot_reflection_iff_survivor (N := N) (p := p) hpSlot).mp hReflect⟩
  · intro h hc
    rcases h hc with ⟨p, hSurv⟩
    have hpSlot : p ∈ midpointScanSlots N :=
      (mem_midpointScanSlots_iff (N := N) (p := p)).mpr
        ⟨Nat.Prime.two_le hSurv.1, hSurv.2.2.1⟩
    refine ⟨p, hpSlot, dual_composite_survivor_off_diagonal hc hSurv,
      (scan_slot_reflection_iff_survivor (N := N) (p := p) hpSlot).mpr hSurv⟩

theorem midpoint_no_survivor_iff_no_scan_reflection (N : ℕ) :
    (¬ MidpointSieveSurvivorExists N) ↔
      (¬ ∃ p ∈ midpointScanSlots N, symmetricPrimeReflectionAt N p) := by
  unfold MidpointSieveSurvivorExists
  constructor
  · intro h ⟨p, hp, hReflect⟩
    exact h ⟨p, (scan_slot_reflection_iff_survivor (N := N) (p := p) hp).mp hReflect⟩
  · intro h ⟨p, hSurv⟩
    have hpSlot : p ∈ midpointScanSlots N :=
      (mem_midpointScanSlots_iff (N := N) (p := p)).mpr
        ⟨Nat.Prime.two_le hSurv.1, hSurv.2.2.1⟩
    exact h ⟨p, hpSlot, (scan_slot_reflection_iff_survivor (N := N) (p := p) hpSlot).mpr hSurv⟩

theorem no_scan_reflection_iff_no_slope_hit (N : ℕ) :
    (¬ ∃ p ∈ midpointScanSlots N, symmetricPrimeReflectionAt N p) ↔
      ¬ MidpointSlopeOrbitPrimeHit N := by
  simp only [← midpoint_no_survivor_iff_no_scan_reflection,
    midpointSlopeOrbitPrimeHit_iff_survivor, not_iff_not]

theorem soe_orbit_no_reflection_implies_prime_iff (N : ℕ) :
    MidpointNoSurvivorImpliesPrime N ↔
      ((¬ ∃ p ∈ midpointScanSlots N, symmetricPrimeReflectionAt N p) → Nat.Prime N) := by
  unfold MidpointNoSurvivorImpliesPrime
  rw [midpoint_no_survivor_iff_no_scan_reflection]

theorem mirror_slot_reflection_iff_prime (N : ℕ) :
    symmetricPrimeReflectionAt N N ↔ Nat.Prime N := by
  unfold symmetricPrimeReflectionAt equidistantPartner
  simp [midpointReflect_self]

/--
**Only the mirror slot tests primality of `N`.**  Off-diagonal reflections exist
for prime midpoints too — a reflection is not a composite detector.
-/
theorem prime_mirror_has_scan_reflection {N : ℕ} (hN : Nat.Prime N) :
    symmetricPrimeReflectionAt N N :=
  (mirror_slot_reflection_iff_prime N).mpr hN

theorem prime_five_has_off_diagonal_reflection : offDiagonalPrimeReflection 5 := by
  refine ⟨3, (mem_midpointScanSlots_iff (N := 5) (p := 3)).mpr ⟨by decide, by decide⟩,
    by decide, ⟨by decide, by decide⟩⟩

theorem prime_midpoint_can_have_off_diagonal_reflection :
    ∃ N, Nat.Prime N ∧ offDiagonalPrimeReflection N :=
  ⟨5, by decide, prime_five_has_off_diagonal_reflection⟩

theorem off_diagonal_reflection_not_composite_test :
    ¬ (∀ N, offDiagonalPrimeReflection N → ¬ Nat.Prime N) := by
  intro h
  exact h 5 prime_five_has_off_diagonal_reflection (by decide)

/--
**Composite-only (proved).**  Composites miss the mirror diagonal; any dual
survivor must live strictly below `N`.
-/
theorem composite_mirror_slot_fails (N : ℕ) (hc : ¬ Nat.Prime N) :
    ¬ symmetricPrimeReflectionAt N N :=
  fun h => hc ((mirror_slot_reflection_iff_prime N).mp h)

theorem composite_reflection_survivor_is_off_diagonal {N p : ℕ} (hc : ¬ Nat.Prime N)
    (h : symmetricPrimeReflectionAt N p) (hp : p ∈ midpointScanSlots N) :
    p < N := by
  by_contra hnot
  have hpEq : p = N := Nat.le_antisymm
    ((mem_midpointScanSlots_iff (N := N) (p := p)).mp hp).2 (Nat.le_of_not_gt hnot)
  exact composite_mirror_slot_fails N hc (hpEq ▸ h)

theorem soe_forward_forces_off_diagonal_iff_composite (N : ℕ) :
    SOEForwardForcesOffDiagonalReflection N ↔ CompositeMidpointHasSurvivor N :=
  offDiagonalPrimeReflection_iff_composite_slope N

def SOEForwardNoReflectionImpliesPrime (N : ℕ) : Prop :=
  (¬ ∃ p ∈ midpointScanSlots N, symmetricPrimeReflectionAt N p) → Nat.Prime N

/--
**Contrapositive only (open).**  This is *not* the converse: scan reflections
can occur at prime midpoints (`prime_five_has_off_diagonal_reflection`).
-/
theorem soe_forward_no_reflection_iff (N : ℕ) :
    SOEForwardNoReflectionImpliesPrime N ↔ MidpointNoSurvivorImpliesPrime N := by
  unfold SOEForwardNoReflectionImpliesPrime MidpointNoSurvivorImpliesPrime
  rw [midpoint_no_survivor_iff_no_scan_reflection]

/-! #### Example: `8 = 3 + 5` at reflection midpoint `N = 4` (forward SoE play) -/

theorem nat_prime_three : Nat.Prime 3 := by decide

theorem goldbach_midpoint_pair_four_three_five : GoldbachMidpointPair 4 3 5 := by
  refine ⟨nat_prime_three, nat_prime_five, by decide, by decide, by decide⟩

theorem equidistantPartner_four_three : equidistantPartner 4 3 = 5 := by decide

theorem equidistant_gaps_match_four_three :
    midpointLeftGap 4 3 = midpointRightGap 4 5 := by decide

theorem symmetricPrimeReflectionAt_four_three : symmetricPrimeReflectionAt 4 3 := by
  exact ⟨nat_prime_three, nat_prime_five⟩

theorem not_symmetricPrimeReflectionAt_four_two : ¬ symmetricPrimeReflectionAt 4 2 := by
  intro h
  exact (by decide : ¬ Nat.Prime 6) h.2

theorem not_symmetricPrimeReflectionAt_four_four : ¬ symmetricPrimeReflectionAt 4 4 := by
  intro h
  exact not_prime_four h.1

theorem dual_midpoint_survivor_four_three : dualMidpointSurvivor 4 3 := by
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  refine ⟨nat_prime_three, nat_prime_five, by decide, by decide⟩

theorem offDiagonalPrimeReflection_four : offDiagonalPrimeReflection 4 :=
  ⟨3, (mem_midpointScanSlots_iff (N := 4) (p := 3)).mpr ⟨by decide, by decide⟩, by decide,
    symmetricPrimeReflectionAt_four_three⟩

theorem composite_midpoint_has_survivor_four : CompositeMidpointHasSurvivor 4 := by
  intro _
  exact ⟨3, dual_midpoint_survivor_four_three⟩

theorem soe_forward_forces_off_diagonal_four : SOEForwardForcesOffDiagonalReflection 4 :=
  fun _ => offDiagonalPrimeReflection_four

/-! #### Example: `12 = 5 + 7` at reflection midpoint `N = 6` -/

theorem not_prime_six : ¬ Nat.Prime 6 := by decide

theorem goldbach_midpoint_pair_six_five_seven : GoldbachMidpointPair 6 5 7 := by
  refine ⟨nat_prime_five, nat_prime_seven, by decide, by decide, by decide⟩

theorem dual_midpoint_survivor_six_five : dualMidpointSurvivor 6 5 := by
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  refine ⟨nat_prime_five, nat_prime_seven, by decide, by decide⟩

theorem composite_midpoint_has_survivor_six : CompositeMidpointHasSurvivor 6 := by
  intro _
  exact ⟨5, dual_midpoint_survivor_six_five⟩

/-! #### Example: `18 = 7 + 11` at reflection midpoint `N = 9` -/

theorem not_prime_nine : ¬ Nat.Prime 9 := by decide

theorem goldbach_midpoint_pair_nine_seven_eleven : GoldbachMidpointPair 9 7 11 := by
  refine ⟨nat_prime_seven, nat_prime_eleven, by decide, by decide, by decide⟩

theorem dual_midpoint_survivor_nine_seven : dualMidpointSurvivor 9 7 := by
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  refine ⟨nat_prime_seven, nat_prime_eleven, by decide, by decide⟩

theorem composite_midpoint_has_survivor_nine : CompositeMidpointHasSurvivor 9 := by
  intro _
  exact ⟨7, dual_midpoint_survivor_nine_seven⟩

/-! #### Example: `20 = 3 + 17` at reflection midpoint `N = 10` -/

theorem nat_prime_seventeen : Nat.Prime 17 := by decide
theorem not_prime_ten : ¬ Nat.Prime 10 := by decide

theorem goldbach_midpoint_pair_ten_three_seventeen : GoldbachMidpointPair 10 3 17 := by
  refine ⟨nat_prime_three, nat_prime_seventeen, by decide, by decide, by decide⟩

theorem dual_midpoint_survivor_ten_three : dualMidpointSurvivor 10 3 := by
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  refine ⟨nat_prime_three, nat_prime_seventeen, by decide, by decide⟩

theorem composite_midpoint_has_survivor_ten : CompositeMidpointHasSurvivor 10 := by
  intro _
  exact ⟨3, dual_midpoint_survivor_ten_three⟩

/-- Explicit SoE/midpoint survivors for small composite midpoints (witness route). -/
theorem composite_midpoint_has_survivor_small_composites :
    CompositeMidpointHasSurvivor 4 ∧ CompositeMidpointHasSurvivor 6 ∧
      CompositeMidpointHasSurvivor 8 ∧ CompositeMidpointHasSurvivor 9 ∧
      CompositeMidpointHasSurvivor 10 ∧ CompositeMidpointHasSurvivor 15 := by
  refine ⟨composite_midpoint_has_survivor_four, composite_midpoint_has_survivor_six, ?_⟩
  refine ⟨composite_midpoint_has_survivor_eight, composite_midpoint_has_survivor_nine, ?_⟩
  exact ⟨composite_midpoint_has_survivor_ten, composite_midpoint_has_survivor_fifteen⟩

theorem eckmann_hilton_forward_collapse_small_composites :
    EckmannHiltonForwardCollapse 4 ∧ EckmannHiltonForwardCollapse 6 ∧
      EckmannHiltonForwardCollapse 8 ∧ EckmannHiltonForwardCollapse 9 ∧
      EckmannHiltonForwardCollapse 10 ∧ EckmannHiltonForwardCollapse 15 := by
  rcases composite_midpoint_has_survivor_small_composites with
    ⟨h4, h6, h8, h9, h10, h15⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (eckmann_hilton_forward_collapse_iff_composite 4).mpr h4
  · exact (eckmann_hilton_forward_collapse_iff_composite 6).mpr h6
  · exact (eckmann_hilton_forward_collapse_iff_composite 8).mpr h8
  · exact (eckmann_hilton_forward_collapse_iff_composite 9).mpr h9
  · exact (eckmann_hilton_forward_collapse_iff_composite 10).mpr h10
  · exact (eckmann_hilton_forward_collapse_iff_composite 15).mpr h15

theorem composite_overlay_survivor_iff_composite (N : ℕ) :
    CompositeMidpointOverlaySurvivor N ↔ CompositeMidpointHasSurvivor N := by
  unfold CompositeMidpointOverlaySurvivor CompositeMidpointHasSurvivor
  constructor
  · intro hOverlay hc
    exact (midpointOverlaySurvivorExists_iff_dual N).mp
      ((composite_overlay_iff_survivor_exists N).mp hOverlay)
  · intro hHas
    refine (composite_overlay_iff_survivor_exists N).mpr ?_
    by_cases hN : Nat.Prime N
    · exact midpointOverlay_survivor_of_prime hN
    · exact (midpointOverlaySurvivorExists_iff_dual N).mpr (hHas hN)

theorem overlay_no_survivor_iff_midpoint (N : ℕ) :
    OverlayNoSurvivorImpliesPrime N ↔ MidpointNoSurvivorImpliesPrime N := by
  rw [overlay_no_survivor_iff_composite_overlay,
      composite_overlay_survivor_iff_composite,
      midpoint_no_survivor_iff_composite_survivor]

/-! ## Midpoint Goldbach form for the SO(4) zeta-holonomy bridge -/

/--
The eventual midpoint Goldbach conclusion: above a threshold, every midpoint
has a prime pair around it, allowing equality at the midpoint.
-/
def MidpointGoldbachEventually (N₀ : ℕ) : Prop :=
  ∀ N : ℕ, N₀ ≤ N → ∃ p q : ℕ, GoldbachMidpointPair N p q

/--
SO(4)/zeta-holonomy bridge payload for ordinary midpoint Goldbach.

This is the missing arithmetic-geometric bridge: the finite patch holonomy
readout must force a positive paired-prime count around every sufficiently
large midpoint.
-/
def SO4ZetaHolonomyForcesMidpointPairs (N₀ : ℕ) : Prop :=
  ∀ N : ℕ, N₀ ≤ N → 0 < goldbachMidpointCount N

theorem goldbachMidpointPair_to_dual_survivor {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    dualMidpointSurvivor N p := by
  obtain ⟨hp, hq, hle, hge, hsum⟩ := h
  have hq' : 2 * N - p = q := by omega
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  exact ⟨hp, hq' ▸ hq, hle, by rw [hq']; exact hge⟩

theorem dual_midpoint_survivor_gives_pair {N p : ℕ} (h : dualMidpointSurvivor N p) :
    GoldbachMidpointPair N p (2 * N - p) := by
  unfold dualMidpointSurvivor at h
  rcases h with ⟨hp, hq, hle, hge⟩
  exact ⟨hp, hq, hle, hge, by omega⟩

theorem exists_midpoint_pair_of_dual_survivor {N : ℕ} {p : ℕ}
    (h : dualMidpointSurvivor N p) :
    ∃ q : ℕ, GoldbachMidpointPair N p q :=
  ⟨2 * N - p, dual_midpoint_survivor_gives_pair h⟩

theorem exists_midpoint_pair_of_count_pos {N : ℕ}
    (hpos : 0 < goldbachMidpointCount N) :
    ∃ p q : ℕ, GoldbachMidpointPair N p q := by
  unfold goldbachMidpointCount at hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hSurv := (mem_goldbachMidpointCandidates_iff N p).mp hp
  rcases exists_midpoint_pair_of_dual_survivor hSurv with ⟨q, hPair⟩
  exact ⟨p, q, hPair⟩

/--
Conditional proof of ordinary midpoint Goldbach from the SO(4) zeta-holonomy
bridge, with diagonal pairs allowed.
-/
theorem midpoint_goldbach_of_so4_zeta_holonomy_bridge
    {N₀ : ℕ}
    (hBridge : SO4ZetaHolonomyForcesMidpointPairs N₀) :
    MidpointGoldbachEventually N₀ := by
  intro N hN
  rcases exists_midpoint_pair_of_count_pos (hBridge N hN) with ⟨p, q, hPair⟩
  exact ⟨p, q, hPair⟩

/-- A midpoint pair is an ordinary Goldbach pair for the even number `2 * N`. -/
theorem goldbach_pair_of_midpoint_pair {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    GoldbachPair (2 * N) p q := by
  obtain ⟨hp, hq, _, _, hsum⟩ := h
  exact ⟨hp, hq, hsum⟩

theorem midpoint_goldbach_of_composite_survivor {N₀ : ℕ}
    (hPrime : ∀ N, N₀ ≤ N → Nat.Prime N → MidpointSieveSurvivorExists N)
    (hComp : ∀ N, N₀ ≤ N → CompositeMidpointHasSurvivor N) :
    MidpointGoldbachEventually N₀ := by
  intro N hN
  by_cases hprime : Nat.Prime N
  · rcases hPrime N hN hprime with ⟨p, hs⟩
    rcases exists_midpoint_pair_of_dual_survivor hs with ⟨q, hPair⟩
    exact ⟨p, q, hPair⟩
  · rcases hComp N hN hprime with ⟨p, hs⟩
    rcases exists_midpoint_pair_of_dual_survivor hs with ⟨q, hPair⟩
    exact ⟨p, q, hPair⟩

/-- A certified midpoint pair witnesses a positive midpoint count. -/
theorem midpoint_count_pos_of_midpoint_pair {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    0 < goldbachMidpointCount N := by
  have hp := (mem_goldbachMidpointCandidates_iff N p).mpr
    (goldbachMidpointPair_to_dual_survivor h)
  unfold goldbachMidpointCount
  exact Finset.card_pos.mpr ⟨p, hp⟩

theorem so4_zeta_holonomy_bridge_of_midpoint_goldbach {N₀ : ℕ}
    (h : MidpointGoldbachEventually N₀) :
    SO4ZetaHolonomyForcesMidpointPairs N₀ := by
  intro N hN
  rcases h N hN with ⟨p, q, hpq⟩
  exact midpoint_count_pos_of_midpoint_pair hpq

theorem so4_zeta_holonomy_bridge_iff_midpoint_goldbach {N₀ : ℕ} :
    SO4ZetaHolonomyForcesMidpointPairs N₀ ↔ MidpointGoldbachEventually N₀ :=
  ⟨midpoint_goldbach_of_so4_zeta_holonomy_bridge,
    so4_zeta_holonomy_bridge_of_midpoint_goldbach⟩

theorem midpoint_pair_of_goldbach_pair_two_mul {N p q : ℕ}
    (h : GoldbachPair (2 * N) p q) :
    ∃ p' q' : ℕ, GoldbachMidpointPair N p' q' := by
  rcases h with ⟨hp, hq, hsum⟩
  rcases le_total p q with hle | hle
  · exact ⟨p, q, ⟨hp, hq, by omega, by omega, hsum⟩⟩
  · exact ⟨q, p, ⟨hq, hp, by omega, by omega, by omega⟩⟩

theorem midpoint_goldbach_two_of_goldbach_parity (h : GoldbachParity) :
    MidpointGoldbachEventually 2 := by
  intro N hN
  rcases h (2 * N) (by omega) ⟨N, by ring⟩ with ⟨p, q, hpq⟩
  exact midpoint_pair_of_goldbach_pair_two_mul hpq

theorem midpoint_goldbach_two_iff_goldbach_parity :
    MidpointGoldbachEventually 2 ↔ GoldbachParity := by
  constructor
  · intro h n hn hEven
    rcases hEven with ⟨k, hk⟩
    subst hk
    have hk2 : 2 ≤ k := by omega
    rcases h k hk2 with ⟨p, q, hMid⟩
    exact ⟨p, q, by simpa [two_mul] using goldbach_pair_of_midpoint_pair hMid⟩
  · exact midpoint_goldbach_two_of_goldbach_parity

theorem so4_zeta_holonomy_bridge_two_iff_goldbach_parity :
    SO4ZetaHolonomyForcesMidpointPairs 2 ↔ GoldbachParity :=
  so4_zeta_holonomy_bridge_iff_midpoint_goldbach.trans midpoint_goldbach_two_iff_goldbach_parity

/-! ### SO(4) tangent slope and Hopf-fiber holonomy support -/

/-- Normalized SO(4) orthogonal tangent midpoint slope `N / (p + q)`. -/
noncomputable def SO4OrthogonalTangentMidpointSlope (N p q : ℕ) : ℝ :=
  (N : ℝ) / (p + q : ℝ)

theorem so4_orthogonal_tangent_midpoint_slope_eq_half
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q) :
    SO4OrthogonalTangentMidpointSlope N p q = (1 / 2 : ℝ) := by
  unfold SO4OrthogonalTangentMidpointSlope
  obtain ⟨_, _, _, _, hsum⟩ := h
  have hden : (p + q : ℝ) = (2 * N : ℝ) := by exact_mod_cast hsum
  rw [hden]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp [hNreal]

theorem so4_orthogonal_diagonal_tangent_slope_eq_half {N : ℕ} (hN : 0 < N)
    (hPrime : Nat.Prime N) :
    SO4OrthogonalTangentMidpointSlope N N N = (1 / 2 : ℝ) :=
  so4_orthogonal_tangent_midpoint_slope_eq_half hN
    ⟨hPrime, hPrime, le_rfl, le_rfl, by omega⟩

/--
Hopf-fiber support: midpoint pair, slope `1/2`, and integrable Hopf shell with
`SO8AdmissibleHolonomy` Δ/G₂/triality fields.
-/
def HopfFiberMidpointHolonomySupport (N p q : ℕ) : Prop :=
  GoldbachMidpointPair N p q ∧
    SO4OrthogonalTangentMidpointSlope N p q = (1 / 2 : ℝ) ∧
      ∃ shell : HopfShell,
        ∃ hs : shell.integrable,
          ∃ hol : SO8AdmissibleHolonomy (shell.toDiscrete3Complex_integrable hs),
            hol.delta_resolves_pinched_links ∧
              hol.fields_g2_delta_recoverable ∧
              hol.triality_three_slots

theorem hopf_fiber_midpoint_holonomy_support_of_midpoint_pair
    {N p q : ℕ} (hN : 0 < N) (hPair : GoldbachMidpointPair N p q) :
    HopfFiberMidpointHolonomySupport N p q := by
  let shell : HopfShell := mkIntegrable 1 (Or.inl rfl)
  have hs : shell.integrable := by simp [shell, mkIntegrable]
  rcases HopfShell.t11_torsion_supplies_delta_in_so8_admissible_holonomy shell hs with
    ⟨hol, hG2Delta, hDelta, hTriality⟩
  exact ⟨hPair, so4_orthogonal_tangent_midpoint_slope_eq_half hN hPair,
    shell, hs, hol, hDelta, hG2Delta, hTriality⟩

theorem composite_minFac_le_sqrt {N : ℕ} (hN : 2 ≤ N) (hc : ¬ Nat.Prime N) :
    Nat.minFac N ≤ Nat.sqrt N := by
  rw [Nat.le_sqrt]
  obtain ⟨k, hk⟩ := Nat.minFac_dvd N
  have hlt : Nat.minFac N < N := (Nat.not_prime_iff_minFac_lt hN).1 hc
  have hk2 : 2 ≤ k := by
    by_contra hlt'
    push_neg at hlt'
    interval_cases k
    · simp at hk
      omega
    · rw [Nat.mul_one] at hk
      omega
  have hkdiv : k ∣ N := ⟨Nat.minFac N, hk.trans (Nat.mul_comm (Nat.minFac N) k)⟩
  have hmin : Nat.minFac N ≤ k := Nat.minFac_le_of_dvd hk2 hkdiv
  have hrk : Nat.minFac N * Nat.minFac N ≤ Nat.minFac N * k :=
    Nat.mul_le_mul_left (Nat.minFac N) hmin
  exact hrk.trans (le_of_eq hk.symm)

theorem composite_minFac_in_finite_stack {N : ℕ} (hN : 2 ≤ N) (hc : ¬ Nat.Prime N) :
    Nat.minFac N ∈ finiteSoeAngleStack N := by
  have hne : N ≠ 1 := by omega
  have hrp : Nat.Prime (Nat.minFac N) := Nat.minFac_prime hne
  have hr2 : 2 ≤ Nat.minFac N := hrp.two_le
  have hle : Nat.minFac N ≤ Nat.sqrt (2 * N) :=
    (composite_minFac_le_sqrt hN hc).trans (Nat.sqrt_le_sqrt (by omega))
  exact (mem_finiteSoeAngleStack_iff' (N := N)).mpr ⟨hrp, hr2, hle⟩

theorem composite_reflected_minFac_in_finite_stack {N p : ℕ} (hp : p ∈ midpointScanSlots N)
    (hpr : Nat.Prime p) (hc : ¬ Nat.Prime (2 * N - p)) (hq : 4 ≤ 2 * N - p) :
    Nat.minFac (2 * N - p) ∈ finiteSoeAngleStack N := by
  set q := 2 * N - p
  set r := Nat.minFac q
  have hr1 : q ≠ 1 := ne_of_gt (by omega)
  have hrp : Nat.Prime r := Nat.minFac_prime hr1
  have hr2 : 2 ≤ r := hrp.two_le
  have hq2 : 2 ≤ q := by omega
  have hrq : r < q := (Nat.not_prime_iff_minFac_lt hq2).1 hc
  rcases Nat.minFac_dvd q with ⟨k, hk⟩
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push_neg at hlt
    interval_cases k
    · simp at hk; omega
    · have hqr : q = r := by simpa using hk
      exact hc (hqr ▸ Nat.minFac_prime hr1)
  have hrk : r ≤ k := Nat.minFac_le_of_dvd hk2 (Dvd.intro r (by rw [mul_comm, hk]))
  have hr_le_sqrt_q : r ≤ Nat.sqrt q :=
    Nat.le_sqrt.mpr (by
      have : r * r ≤ r * k := Nat.mul_le_mul_left r hrk
      nlinarith [hk])
  have hr_le_sqrt : r ≤ Nat.sqrt (2 * N) :=
    hr_le_sqrt_q.trans (Nat.sqrt_le_sqrt (by omega))
  exact (mem_finiteSoeAngleStack_iff' (N := N)).mpr ⟨hrp, hr2, hr_le_sqrt⟩

end Hqiv.Geometry
