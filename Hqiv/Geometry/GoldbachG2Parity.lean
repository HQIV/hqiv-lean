import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic
import Hqiv.Algebra.G2Embedding
import Hqiv.Algebra.MinimalSoSeedClosure
import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Geometry.QuantumFactorGateFrontier

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

/-- The explicit `G₂ ∪ {Δ}` seed set acting on the octonionic 8-carrier. -/
def G2DeltaSeedSet : Set (Matrix (Fin 8) (Fin 8) ℝ) :=
  Set.range Hqiv.Algebra.g2Generator ∪ {Hqiv.phaseLiftDelta}

/-- Goldbach pair predicate for a fixed integer `n`. -/
def GoldbachPair (n p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- The even Goldbach statement, restricted to the parity case `2 < n` and `Even n`. -/
def GoldbachParity : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, GoldbachPair n p q

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

end Hqiv.Geometry
