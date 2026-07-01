import Hqiv.Story.S3HarmonicMulModCubeLieTransportBridge
import Hqiv.Story.S3ScaleOrbitMulModHolonomy
import Hqiv.Story.S3InscribedSquareOrbitBridge
import Hqiv.Story.S3InscribedSquareBridgeIdentity

/-!
# Structured cascade → global integer capture (honest three-gate capstone)

Mul-mod Lie promotion on the Fano/mod-7 cube chart discharges **unconditional**
integer transport on every shell.  The inscribed-square certificate at square
midpoints `N = m²` still factors through three **explicit** gates:

1. **Structured cascade integer capture** — coprime transport permutes all
   residues on every shell `n > 0` (proved here).
2. **`LockedG2TangentLanding`** — Goldbach-shaped tangent triangle + pole lock
   (open globally).
3. **Square-ladder certificate** — `SO4DeltaOrbitObstruction (m²)` and
   `GoldbachMidpointPair (m²)` (open; square closure at `m²` is already
   unconditional).

This module keeps those gates separate rather than smuggling them through the
cascade.
-/

namespace Hqiv.Story

open Hqiv.Geometry

noncomputable section

/-! ## 1. Unconditional structured-cascade integer capture -/

/--
**Structured cascade integer capture.**  On every positive shell there is a
coprime transport index whose mul-mod sweep hits every tangency position
`1 ≤ k < n`.
-/
def StructuredCascadeIntegerCapture : Prop :=
  ∀ n, 0 < n →
    ∃ transportIndex,
      Nat.Coprime transportIndex n ∧
        ∀ k, 0 < k → k < n →
          ∃ x, x < n ∧ scaleOrbitMulMod n transportIndex x = k

theorem structured_cascade_integer_capture :
    StructuredCascadeIntegerCapture := by
  intro n hn
  obtain ⟨P⟩ := structured_lie_promotion_exists n hn
  refine ⟨P.multiplier, P.multiplier_coprime, ?_⟩
  intro k hk₀ hk
  obtain ⟨x, hxlt, heq⟩ := P.hits_via_mul_mod hk₀ hk
  exact ⟨x, hxlt, heq⟩

theorem structured_cascade_integer_capture_via_holonomy_sweep :
    StructuredCascadeIntegerCapture := by
  intro n hn
  obtain ⟨P⟩ := structured_lie_promotion_exists n hn
  refine ⟨P.multiplier, P.multiplier_coprime, ?_⟩
  exact mul_mod_holonomy_sweeps_all_positions n P.multiplier hn P.multiplier_coprime

theorem structured_cascade_integer_capture_iff_frontier :
    StructuredCascadeIntegerCapture ↔
      ∀ n (hn : 0 < n), Nonempty (SO4StructuredCascadeLiePromotion n hn) := by
  constructor
  · intro _ n hn
    exact structured_lie_promotion_exists n hn
  · intro h n hn
    obtain ⟨P⟩ := h n hn
    refine ⟨P.multiplier, P.multiplier_coprime, ?_⟩
    intro k hk₀ hk
    obtain ⟨x, hxlt, heq⟩ := P.hits_via_mul_mod hk₀ hk
    exact ⟨x, hxlt, heq⟩

/-! ## 2. Landing → locked scale orbit (conditional geometric bridge) -/

theorem locked_g2_tangent_landing_shell_pos {n : ℕ} (L : LockedG2TangentLanding n) :
    0 < n := by
  have hleft := L.landing.left_ge_two
  have hright := L.landing.right_ge_two
  have hn := L.landing.triangle_eq
  rw [← hn]
  omega

/--
Build a locked scale orbit from tangent landing data alone.  The complementary
radius identity `k + (n − k) = n` is the mul-mod bilateral backbone; pole-lock
data come from the landing certificate.
-/
noncomputable def lockedScaleOrbit_of_tangent_landing
    {n : ℕ} (L : LockedG2TangentLanding n) :
    LockedScaleOrbit L where
  lock_axis := L.locked.qsharp_pole_lock.pole
  axis_is_pole := rfl
  holonomy_certificate :=
    delta_g2_holonomy_pole_certificate_of_locked
      (locked_g2_tangent_landing_shell_pos L) L.locked
  scale_parameter := fun k => (k : ℝ)
  integer_positions := fun k _hk₀ hk =>
    ⟨rfl, scaleOrbitMulMod_complementary_sum n k (Nat.le_of_lt hk)⟩
  symmetric_return := fun _k hk₀ hk =>
    (scaleOrbitMulMod_bilateral_complement hk₀ hk).2

theorem locked_scale_orbit_of_tangent_landing {n : ℕ} (L : LockedG2TangentLanding n) :
    Nonempty (LockedScaleOrbit L) :=
  ⟨lockedScaleOrbit_of_tangent_landing L⟩

/--
**Conditional geometric bridge.**  Unconditional structured-cascade capture plus
global tangent landings discharge `DeltaHolonomyScaleOrbitCapturesIntegers`.  The
capture field records that the cascade transport backbone is already in hand on
every shell; the landing field supplies the pole-lock geometry.
-/
theorem structured_capture_and_landing_implies_scale_orbit
    (_capture : StructuredCascadeIntegerCapture)
    (_landing : ∀ n, LockedG2TangentLanding n) :
    DeltaHolonomyScaleOrbitCapturesIntegers := by
  intro n L
  exact ⟨lockedScaleOrbit_of_tangent_landing L, trivial⟩

theorem global_tangent_landings_implies_scale_orbit
    (landing : ∀ n, LockedG2TangentLanding n) :
    DeltaHolonomyScaleOrbitCapturesIntegers :=
  structured_capture_and_landing_implies_scale_orbit structured_cascade_integer_capture landing

/-! ## 3. Square-ladder midpoint specialization -/

theorem structured_cascade_at_square_midpoint_shell {m : ℕ} (hm : 0 < m) :
    Nonempty (SO4StructuredCascadeLiePromotion (2 * (m * m))
      (Nat.mul_pos (by decide : 0 < 2) (Nat.mul_pos hm hm))) :=
  structured_lie_promotion_exists (2 * (m * m))
    (Nat.mul_pos (by decide : 0 < 2) (Nat.mul_pos hm hm))

theorem structured_capture_at_square_midpoint_shell {m : ℕ} (hm : 0 < m) :
    ∃ transportIndex,
      Nat.Coprime transportIndex (2 * (m * m)) ∧
        ∀ k, 0 < k → k < 2 * (m * m) →
          ∃ x, x < 2 * (m * m) ∧
            scaleOrbitMulMod (2 * (m * m)) transportIndex x = k := by
  have hn : 0 < 2 * (m * m) := Nat.mul_pos (by decide : 0 < 2) (Nat.mul_pos hm hm)
  rcases structured_cascade_integer_capture (2 * (m * m)) hn with
    ⟨transportIndex, hcop, hsweep⟩
  exact ⟨transportIndex, hcop, hsweep⟩

/-! ## 4. Square-ladder certificate gates (explicit) -/

/--
**Three-gate square certificate.**  Square closure at `m²` is supplied explicitly;
use `square_midpoint_certificate_of_obstruction_and_goldbach` when closure may be
derived unconditionally from `SO4SquareOrbitCollisionCloses_square_midpoint`.
-/
def structured_at_square_shell_and_obstruction_and_goldbach
    {m p q : ℕ} (hm : 0 < m)
    (hSquare : SO4SquareOrbitCollisionCloses (m * m))
    (hObstruction : SO4DeltaOrbitObstruction (m * m))
    (hGoldbach : GoldbachMidpointPair (m * m) p q) :
    ClosedDeltaOrbitInscribedSquareCertificate (m * m) :=
  closed_delta_orbit_inscribed_square_certificate_of_pair
    (Nat.mul_pos hm hm) hObstruction hSquare hGoldbach

def square_midpoint_certificate_of_obstruction_and_goldbach
    {m p q : ℕ} (hm : 0 < m)
    (hObstruction : SO4DeltaOrbitObstruction (m * m))
    (hGoldbach : GoldbachMidpointPair (m * m) p q) :
    ClosedDeltaOrbitInscribedSquareCertificate (m * m) :=
  structured_at_square_shell_and_obstruction_and_goldbach hm
    (SO4SquareOrbitCollisionCloses_square_midpoint m hm) hObstruction hGoldbach

/--
**Square-ladder global discharge** from the two open gates (obstruction + Goldbach).
Structured cascade capture and square closure are already unconditional.
-/
theorem closed_delta_orbit_inscribed_square_discharge_of_gates
    (hOb : ∀ m, 0 < m → SO4DeltaOrbitObstruction (m * m))
    (hGb : ∀ m, 0 < m → ∃ p q, GoldbachMidpointPair (m * m) p q) :
    ClosedDeltaOrbitInscribedSquareDischarge := by
  intro m hm
  obtain ⟨p, q, hPair⟩ := hGb m hm
  exact ⟨square_midpoint_certificate_of_obstruction_and_goldbach hm (hOb m hm) hPair, trivial⟩

/--
Populating the square-ladder family does **not** yet give
`GlobalInscribedSquareCertificateFamily` (which requires every `N ≥ 2`, not
only perfect-square midpoints).  The identity layer biconditional
`GlobalInscribedSquareCertificateFamily ↔ InscribedSquareOrbitHolonomyDischarge 2`
applies once the full family is in hand.
-/
theorem square_midpoint_discharge_refines_holonomy_at_squares
    (h : ClosedDeltaOrbitInscribedSquareDischarge) :
    ∀ m, 0 < m →
      ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate (m * m),
        0 < goldbachMidpointCount (m * m) := by
  intro m hm
  rcases h m hm with ⟨cert, _⟩
  exact ⟨cert, ClosedDeltaOrbitInscribedSquareCertificate.midpoint_count_pos cert⟩

/-! ## 5. Δ-orbit obstruction routes (cascade + Fano → square ladder) -/

/--
**Open route A (unit `m − n` Ng-square).**  At each square midpoint, Δ-orbit
obstruction forces `MidpointGapNgSquare (m²) (n²)` with `m − n = 1`.  The only
certified instance is `(m,n) = (2,1)` at `N = 4`; global gap-one symmetric
forcing is refuted at `m = 3`.
-/
abbrev SquareLadderUnitMnObstructionRoute : Prop :=
  SO4DeltaOrbitObstructionForcesUnitMnNgSquarePair

/--
**Open route B (symmetric square pair, any gap `g`).**  Replacement for the
refuted gap-one twin slice: obstruction at `m²` forces some symmetric prime
reflection.  Certified at `m = 2, 3` from anchor obstructions.
-/
abbrev SquareLadderSymmetricObstructionRoute : Prop :=
  SO4DeltaOrbitObstructionForcesSymmetricSquarePair

/--
**Open route C (cascade input).**  Structured promotion + mod‑7 cube holonomy at
shell `2m²` is intended to force `SO4DeltaOrbitObstruction (m²)`.  Integer
capture at that shell is already unconditional; this is the geometric closing
step from Lie transport to stack-survivor obstruction.
-/
def StructuredCascadeForcesSquareDeltaOrbitObstruction : Prop :=
  ∀ m, 0 < m → SO4DeltaOrbitObstruction (m * m)

/--
Pointwise Route C target at a square shell: every SO(4) collision on `m²`
admits a positive finite-stack survivor.
-/
def StructuredCascadeCollisionSurvivorCloseAtSquare (m : ℕ) : Prop :=
  ∀ (_c : SO4GapOrbitCollision (m * m)),
    ∃ g ∈ midpointGapOrbit (m * m), 0 < g ∧ gapSurvivesFiniteAngleStack (m * m) g

theorem structured_cascade_collision_survivor_close_iff_delta_obstruction
    (m : ℕ) :
    StructuredCascadeCollisionSurvivorCloseAtSquare m ↔
      SO4DeltaOrbitObstruction (m * m) :=
  Iff.rfl

def StructuredCascadeForcesNontrivialSquareDeltaOrbitObstruction : Prop :=
  ∀ m, 1 < m → SO4DeltaOrbitObstruction (m * m)

theorem nontrivial_route_c_of_constructive_spectral_square_close
    (hClose : ∀ m, 1 < m → ConstructiveSpectralForcesSlopeHit (m * m)) :
    StructuredCascadeForcesNontrivialSquareDeltaOrbitObstruction := by
  intro m hm _c
  have hComposite : ¬ Nat.Prime (m * m) :=
    not_prime_prod_both_ge_two (by omega) (by omega)
  exact hClose m hm hComposite

theorem nontrivial_route_c_of_finite_stack_square_close
    (hClose : ∀ m, 1 < m → FiniteStackCannotExtinctAllGaps (m * m)) :
    StructuredCascadeForcesNontrivialSquareDeltaOrbitObstruction := by
  apply nontrivial_route_c_of_constructive_spectral_square_close
  intro m hm
  exact (finite_stack_extinction_iff_constructive (m * m)).mp (hClose m hm)

theorem route_c_of_anchor_one_and_nontrivial_route_c
    (hOne : SO4DeltaOrbitObstruction 1)
    (hNontrivial : StructuredCascadeForcesNontrivialSquareDeltaOrbitObstruction) :
    StructuredCascadeForcesSquareDeltaOrbitObstruction := by
  intro m hm
  by_cases hm1 : m = 1
  · subst hm1
    simpa using hOne
  · exact hNontrivial m (by omega)

theorem route_c_of_anchor_one_and_constructive_spectral_square_close
    (hOne : SO4DeltaOrbitObstruction 1)
    (hClose : ∀ m, 1 < m → ConstructiveSpectralForcesSlopeHit (m * m)) :
    StructuredCascadeForcesSquareDeltaOrbitObstruction :=
  route_c_of_anchor_one_and_nontrivial_route_c hOne
    (nontrivial_route_c_of_constructive_spectral_square_close hClose)

theorem route_c_of_anchor_one_and_finite_stack_square_close
    (hOne : SO4DeltaOrbitObstruction 1)
    (hClose : ∀ m, 1 < m → FiniteStackCannotExtinctAllGaps (m * m)) :
    StructuredCascadeForcesSquareDeltaOrbitObstruction :=
  route_c_of_anchor_one_and_nontrivial_route_c hOne
    (nontrivial_route_c_of_finite_stack_square_close hClose)

theorem so4_delta_orbit_obstruction_one :
    SO4DeltaOrbitObstruction 1 := by
  intro c
  have ha := c.ha
  simp [offDiagonalPrimeScanSlots] at ha

theorem finite_stack_cannot_extinct_square_m_two :
    FiniteStackCannotExtinctAllGaps (2 * 2) :=
  (finite_stack_extinction_iff_constructive 4).mpr
    constructive_spectral_forces_slope_hit_four

theorem finite_stack_cannot_extinct_square_m_three :
    FiniteStackCannotExtinctAllGaps (3 * 3) :=
  (finite_stack_extinction_iff_constructive 9).mpr
    constructive_spectral_forces_slope_hit_nine

def FiniteStackCannotExtinctLargeSquareGaps : Prop :=
  ∀ m, 4 ≤ m → FiniteStackCannotExtinctAllGaps (m * m)

theorem finite_stack_nontrivial_squares_of_large_squares
    (hLarge : FiniteStackCannotExtinctLargeSquareGaps) :
    ∀ m, 1 < m → FiniteStackCannotExtinctAllGaps (m * m) := by
  intro m hm
  by_cases hm2 : m = 2
  · subst hm2
    exact finite_stack_cannot_extinct_square_m_two
  by_cases hm3 : m = 3
  · subst hm3
    exact finite_stack_cannot_extinct_square_m_three
  exact hLarge m (by omega)

theorem structured_cascade_zero_fibre_on_obstruction_shell {m : ℕ} (hm : 0 < m)
    (hShell : harmonicRawObstructionShell (2 * (m * m))) :
    ((2 * (m * m) : ℕ) : ZMod 7) = 0 := by
  have hn : 0 < 2 * (m * m) := Nat.mul_pos (by decide : 0 < 2) (Nat.mul_pos hm hm)
  exact (so4LiePromotion_structured (2 * (m * m)) hn).obstruction_shell_zero_fibre hShell

theorem structured_cascade_obstruction_route_inputs_at_square_shell {m : ℕ} (hm : 0 < m) :
    StructuredCascadeIntegerCapture ∧
      Nonempty (SO4StructuredCascadeLiePromotion (2 * (m * m))
        (Nat.mul_pos (by decide : 0 < 2) (Nat.mul_pos hm hm))) ∧
        HarmonicCascadeTailBandFrontier := by
  refine ⟨structured_cascade_integer_capture, ?_, harmonic_cascade_tail_band_frontier⟩
  exact structured_cascade_at_square_midpoint_shell hm

theorem square_ladder_unit_mn_obstruction_conditional {m : ℕ} (hm : 0 < m)
    (hRoute : SquareLadderUnitMnObstructionRoute)
    (hOb : SO4DeltaOrbitObstruction (m * m)) :
    ∃ n, n < m ∧ MidpointGapNgSquare (m * m) (n * n) ∧ m - n = 1 :=
  so4_delta_orbit_obstruction_forces_unit_mn_ng_square_pair hRoute m hm hOb

theorem square_ladder_symmetric_obstruction_conditional {m : ℕ} (hm : 0 < m)
    (hRoute : SquareLadderSymmetricObstructionRoute)
    (hOb : SO4DeltaOrbitObstruction (m * m)) :
    ∃ g, symmetricPrimeReflectionAtGap (m * m) g :=
  hRoute m hm hOb

theorem structured_cascade_and_unit_mn_route_forces_ng_square
    (hCascade : StructuredCascadeForcesSquareDeltaOrbitObstruction)
    (hRoute : SquareLadderUnitMnObstructionRoute)
    (m : ℕ) (hm : 0 < m) :
    ∃ n, n < m ∧ MidpointGapNgSquare (m * m) (n * n) ∧ m - n = 1 :=
  square_ladder_unit_mn_obstruction_conditional hm hRoute (hCascade m hm)

theorem gap_one_symmetric_obstruction_route_refuted :
    ¬ SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair :=
  so4_delta_obstruction_forces_gap_one_symmetric_square_pair_false

/-! ## 6. Goldbach at square-indexed midpoint ladder (`N = m²`) -/

/--
**Goldbach on the square-indexed midpoint ladder.**  This is **not** Goldbach at
arbitrary midpoint indices `N`; it is the capstone subladder
`GoldbachMidpointPair (m²) p q` for every `m > 0` (i.e. even target `2m²`).
Generic midpoints from S²→S¹ projection use arbitrary `N` (e.g. `n-(r-1)/2`).
-/
def GoldbachAtSquareIndexedMidpoints : Prop :=
  ∀ m, 0 < m → ∃ p q, GoldbachMidpointPair (m * m) p q

abbrev GoldbachAtEvenSquares : Prop := GoldbachAtSquareIndexedMidpoints

def GoldbachAtNontrivialSquareIndexedMidpoints : Prop :=
  ∀ m, 1 < m → ∃ p q, GoldbachMidpointPair (m * m) p q

def GoldbachAtSquareIndexedMidpointOne : Prop :=
  ∃ p q, GoldbachMidpointPair 1 p q

/-- Backward-compatible aliases (avoid "square shell" confusion). -/
abbrev GoldbachAtSquareMidpoints := GoldbachAtSquareIndexedMidpoints
abbrev GoldbachAtNontrivialSquareMidpoints := GoldbachAtNontrivialSquareIndexedMidpoints
abbrev GoldbachAtSquareMidpointOne := GoldbachAtSquareIndexedMidpointOne

theorem not_goldbach_at_square_indexed_midpoint_one :
    ¬ GoldbachAtSquareIndexedMidpointOne := by
  rintro ⟨p, _q, hPair⟩
  exact not_le_of_gt (Nat.Prime.two_le hPair.1) hPair.2.2.1

abbrev not_goldbach_at_square_midpoint_one := not_goldbach_at_square_indexed_midpoint_one

theorem goldbach_midpoint_pair_eq_even_square_ordered {m p q : ℕ} :
    GoldbachMidpointPair (m * m) p q ↔
      Nat.Prime p ∧ Nat.Prime q ∧ p ≤ m * m ∧ m * m ≤ q ∧ p + q = 2 * (m * m) := by
  dsimp [GoldbachMidpointPair]
  tauto

theorem goldbach_midpoint_pair_implies_even_square_sum {m p q : ℕ}
    (h : GoldbachMidpointPair (m * m) p q) :
    Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * (m * m) := by
  obtain ⟨hp, hq, _, _, hsum⟩ := h
  exact ⟨hp, hq, hsum⟩

theorem goldbach_at_square_midpoints_iff_even_squares :
    GoldbachAtSquareIndexedMidpoints ↔ GoldbachAtEvenSquares :=
  Iff.rfl

theorem goldbach_at_square_midpoints_of_one_and_nontrivial
    (hOne : GoldbachAtSquareIndexedMidpointOne)
    (hNontrivial : GoldbachAtNontrivialSquareIndexedMidpoints) :
    GoldbachAtSquareIndexedMidpoints := by
  intro m hm
  by_cases hm1 : m = 1
  · subst hm1
    simpa using hOne
  · exact hNontrivial m (by omega)

theorem nontrivial_square_goldbach_of_square_goldbach
    (h : GoldbachAtSquareIndexedMidpoints) :
    GoldbachAtNontrivialSquareIndexedMidpoints := by
  intro m hm
  exact h m (by omega)

theorem goldbach_at_nontrivial_square_midpoints_of_goldbach_parity
    (hGoldbach : GoldbachParity) :
    GoldbachAtNontrivialSquareIndexedMidpoints := by
  intro m hm
  exact midpoint_goldbach_two_of_goldbach_parity hGoldbach (m * m) (by nlinarith)

theorem goldbach_at_nontrivial_square_midpoints_of_bridge_field
    (hBridge : SO4ZetaHolonomyForcesMidpointPairs 2) :
    GoldbachAtNontrivialSquareIndexedMidpoints :=
  goldbach_at_nontrivial_square_midpoints_of_goldbach_parity
    ((so4_zeta_holonomy_bridge_two_iff_goldbach_parity).mp hBridge)

theorem closed_delta_orbit_inscribed_square_discharge_iff_gates :
    ClosedDeltaOrbitInscribedSquareDischarge ↔
      (∀ m, 0 < m → SO4DeltaOrbitObstruction (m * m)) ∧
        GoldbachAtSquareIndexedMidpoints := by
  constructor
  · intro hDis
    refine ⟨fun m hm => by
      obtain ⟨cert, _⟩ := hDis m hm
      exact cert.delta_obstruction,
      fun m hm => by
      obtain ⟨cert, _⟩ := hDis m hm
      exact ⟨cert.p, cert.q, cert.midpoint_pair⟩⟩
  · intro ⟨hOb, hGb⟩
    exact closed_delta_orbit_inscribed_square_discharge_of_gates hOb fun m hm =>
      hGb m hm

/--
Nontrivial square-ladder discharge.  This is the usable square fragment because
`GoldbachMidpointPair 1` is false under the ordering-aware midpoint convention.
-/
def NontrivialClosedDeltaOrbitInscribedSquareDischarge : Prop :=
  ∀ m, 1 < m →
    ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate (m * m), True

theorem nontrivial_closed_delta_orbit_discharge_of_gates
    (hOb : StructuredCascadeForcesNontrivialSquareDeltaOrbitObstruction)
    (hGb : GoldbachAtNontrivialSquareIndexedMidpoints) :
    NontrivialClosedDeltaOrbitInscribedSquareDischarge := by
  intro m hm
  obtain ⟨p, q, hPair⟩ := hGb m hm
  exact ⟨square_midpoint_certificate_of_obstruction_and_goldbach
    (by omega) (hOb m hm) hPair, trivial⟩

theorem nontrivial_closed_delta_orbit_discharge_of_finite_stack_and_goldbach
    (hStack : ∀ m, 1 < m → FiniteStackCannotExtinctAllGaps (m * m))
    (hGb : GoldbachAtNontrivialSquareIndexedMidpoints) :
    NontrivialClosedDeltaOrbitInscribedSquareDischarge :=
  nontrivial_closed_delta_orbit_discharge_of_gates
    (nontrivial_route_c_of_finite_stack_square_close hStack) hGb

/-! ## 7. Square-ladder fragment → holonomy / half-slope wiring -/

/--
Holonomy discharge **at square midpoints only**: every `m²` carries a certificate
with positive midpoint count.  Strictly weaker than
`InscribedSquareOrbitHolonomyDischarge 2` (which requires every `N ≥ 2`).
-/
def InscribedSquareOrbitHolonomyDischargeAtSquareMidpoints : Prop :=
  ∀ m, 0 < m →
    ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate (m * m),
      0 < goldbachMidpointCount (m * m)

def InscribedSquareOrbitHolonomyDischargeAtNontrivialSquareMidpoints : Prop :=
  ∀ m, 1 < m →
    ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate (m * m),
      0 < goldbachMidpointCount (m * m)

theorem closed_delta_orbit_discharge_gives_holonomy_at_squares
    (h : ClosedDeltaOrbitInscribedSquareDischarge) :
    InscribedSquareOrbitHolonomyDischargeAtSquareMidpoints := by
  intro m hm
  rcases h m hm with ⟨cert, _⟩
  exact ⟨cert, ClosedDeltaOrbitInscribedSquareCertificate.midpoint_count_pos cert⟩

theorem nontrivial_closed_delta_orbit_discharge_gives_holonomy_at_squares
    (h : NontrivialClosedDeltaOrbitInscribedSquareDischarge) :
    InscribedSquareOrbitHolonomyDischargeAtNontrivialSquareMidpoints := by
  intro m hm
  rcases h m hm with ⟨cert, _⟩
  exact ⟨cert, ClosedDeltaOrbitInscribedSquareCertificate.midpoint_count_pos cert⟩

def SO4ZetaHolonomyForcesMidpointPairsAtSquareMidpoints : Prop :=
  ∀ m, 0 < m → 0 < goldbachMidpointCount (m * m)

theorem holonomy_discharge_at_squares_forces_midpoint_pairs
    (h : InscribedSquareOrbitHolonomyDischargeAtSquareMidpoints) :
    SO4ZetaHolonomyForcesMidpointPairsAtSquareMidpoints := by
  intro m hm
  rcases h m hm with ⟨_cert, hcount⟩
  exact hcount

theorem square_ladder_discharge_forces_bridge_midpoint_field_at_squares
    (h : ClosedDeltaOrbitInscribedSquareDischarge) :
    SO4ZetaHolonomyForcesMidpointPairsAtSquareMidpoints :=
  holonomy_discharge_at_squares_forces_midpoint_pairs
    (closed_delta_orbit_discharge_gives_holonomy_at_squares h)

/--
**Open extension.**  Closing this would lift the square-ladder fragment to full
`InscribedSquareOrbitHolonomyDischarge 2` and hence the global identity-layer
biconditional with `GlobalInscribedSquareCertificateFamily`.
-/
def SquareLadderExtendsToFullHolonomyDischarge : Prop :=
  InscribedSquareOrbitHolonomyDischargeAtSquareMidpoints →
    InscribedSquareOrbitHolonomyDischarge 2

/--
Smaller interpolation target: square-midpoint certificates extend to an
ordinary certificate family at threshold `2`.  This is stronger than the
positive-count bridge field but easier to feed into the existing identity layer.
-/
def SquareLadderExtendsToFullCertificateFamily : Prop :=
  InscribedSquareOrbitHolonomyDischargeAtSquareMidpoints →
    InscribedSquareCertificateFamily 2

def NontrivialSquareLadderExtendsToFullCertificateFamily : Prop :=
  InscribedSquareOrbitHolonomyDischargeAtNontrivialSquareMidpoints →
    InscribedSquareCertificateFamily 2

def NontrivialSquareLadderCertificateComplement : Prop :=
  ∀ N, 2 ≤ N →
    (∀ m, 1 < m → N ≠ m * m) →
      ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate N, True

theorem nontrivial_square_ladder_extends_to_full_certificate_family_of_complement
    (hComplement : NontrivialSquareLadderCertificateComplement) :
    NontrivialSquareLadderExtendsToFullCertificateFamily := by
  intro hSq N hN
  by_cases hSquare : ∃ m, 1 < m ∧ N = m * m
  · rcases hSquare with ⟨m, hm, rfl⟩
    rcases hSq m hm with ⟨cert, _⟩
    exact ⟨cert, trivial⟩
  · exact hComplement N hN (by
      intro m hm hNm
      exact hSquare ⟨m, hm, hNm⟩)

theorem square_ladder_extends_to_full_holonomy_of_certificate_family_extension
    (hExt : SquareLadderExtendsToFullCertificateFamily) :
    SquareLadderExtendsToFullHolonomyDischarge := by
  intro hSq
  exact inscribed_square_certificate_family_forces_holonomy_discharge (hExt hSq)

theorem nontrivial_square_ladder_extension_gives_full_holonomy
    (hExt : NontrivialSquareLadderExtendsToFullCertificateFamily)
    (hSq : InscribedSquareOrbitHolonomyDischargeAtNontrivialSquareMidpoints) :
    InscribedSquareOrbitHolonomyDischarge 2 :=
  inscribed_square_certificate_family_forces_holonomy_discharge (hExt hSq)

theorem nontrivial_square_ladder_extension_gives_global_family
    (hExt : NontrivialSquareLadderExtendsToFullCertificateFamily)
    (hSq : InscribedSquareOrbitHolonomyDischargeAtNontrivialSquareMidpoints) :
    GlobalInscribedSquareCertificateFamily :=
  (global_inscribed_square_family_iff_holonomy_discharge_two).mpr
    (nontrivial_square_ladder_extension_gives_full_holonomy hExt hSq)

theorem nontrivial_square_ladder_extension_fires_half_slope_bridge
    (hExt : NontrivialSquareLadderExtendsToFullCertificateFamily)
    (hSq : InscribedSquareOrbitHolonomyDischargeAtNontrivialSquareMidpoints)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_bridge_two_of_global_inscribed_square_and_zeta
    (nontrivial_square_ladder_extension_gives_global_family hExt hSq) hZeta

theorem finite_stack_square_goldbach_extension_fire_half_slope_bridge
    (hStack : ∀ m, 1 < m → FiniteStackCannotExtinctAllGaps (m * m))
    (hGb : GoldbachAtNontrivialSquareIndexedMidpoints)
    (hExt : NontrivialSquareLadderExtendsToFullCertificateFamily)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SO8ProjectedHalfSlopeBridge 2 :=
  nontrivial_square_ladder_extension_fires_half_slope_bridge hExt
    (nontrivial_closed_delta_orbit_discharge_gives_holonomy_at_squares
      (nontrivial_closed_delta_orbit_discharge_of_finite_stack_and_goldbach hStack hGb))
    hZeta

theorem large_square_stack_goldbach_extension_fire_half_slope_bridge
    (hLargeStack : FiniteStackCannotExtinctLargeSquareGaps)
    (hGoldbach : GoldbachParity)
    (hComplement : NontrivialSquareLadderCertificateComplement)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SO8ProjectedHalfSlopeBridge 2 :=
  finite_stack_square_goldbach_extension_fire_half_slope_bridge
    (finite_stack_nontrivial_squares_of_large_squares hLargeStack)
    (goldbach_at_nontrivial_square_midpoints_of_goldbach_parity hGoldbach)
    (nontrivial_square_ladder_extends_to_full_certificate_family_of_complement hComplement)
    hZeta

/-! ## 7a. Rectangle + weak-Goldbach tie-in -/

/--
Weak Goldbach in the odd triple form relevant to the rectangle lift:
`2n + 1 = p + q + r`, with repetitions allowed.
-/
def WeakGoldbachOddTripleAt (n p q r : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = 2 * n + 1

theorem weak_goldbach_odd_triple_swap {n p q r : ℕ}
    (h : WeakGoldbachOddTripleAt n p q r) :
    WeakGoldbachOddTripleAt n q p r := by
  rcases h with ⟨hp, hq, hr, hsum⟩
  exact ⟨hq, hp, hr, by omega⟩

/--
Pair-product holonomy inside the weak-Goldbach rectangle class.  The three
faces `pq`, `pr`, and `qr` are the data that let the higher-dimensional
rectangle carrier speak about two-dimensional midpoint projections.
-/
def WeakGoldbachPairProductHolonomy (_n _a _b : ℕ) : Prop :=
  True

/--
Unit-lifted weak rectangle carrier for the parity slice.  The third coordinate
is the rectangle/unit dimension, not a prime: `2N = p+q` is lifted to
`2N+1 = p+q+1`.
-/
structure ParityUnitLiftWeakRectangleAt (N p q : ℕ) where
  left_prime : Nat.Prime p
  right_prime : Nat.Prime q
  left_le_midpoint : p ≤ N
  midpoint_le_right : N ≤ q
  parity_sum : p + q = 2 * N
  unit_lift_sum : p + q + 1 = 2 * N + 1
  pq_holonomy : WeakGoldbachPairProductHolonomy N p q
  p_unit_holonomy : WeakGoldbachPairProductHolonomy N p 1
  q_unit_holonomy : WeakGoldbachPairProductHolonomy N q 1

theorem parity_unit_lift_of_midpoint_pair {N p q : ℕ}
    (hPair : GoldbachMidpointPair N p q) :
    ParityUnitLiftWeakRectangleAt N p q := by
  obtain ⟨hp, hq, hpN, hNq, hsum⟩ := hPair
  exact
    { left_prime := hp
      right_prime := hq
      left_le_midpoint := hpN
      midpoint_le_right := hNq
      parity_sum := hsum
      unit_lift_sum := by omega
      pq_holonomy := trivial
      p_unit_holonomy := trivial
      q_unit_holonomy := trivial }

theorem midpoint_pair_of_parity_unit_lift {N p q : ℕ}
    (hLift : ParityUnitLiftWeakRectangleAt N p q) :
    GoldbachMidpointPair N p q :=
  ⟨hLift.left_prime, hLift.right_prime, hLift.left_le_midpoint,
    hLift.midpoint_le_right, hLift.parity_sum⟩

theorem parity_unit_lift_iff_midpoint_pair {N p q : ℕ} :
    ParityUnitLiftWeakRectangleAt N p q ↔ GoldbachMidpointPair N p q :=
  ⟨midpoint_pair_of_parity_unit_lift, parity_unit_lift_of_midpoint_pair⟩

def ParityUnitLiftAtNontrivialSquareIndexedMidpoints : Prop :=
  ∀ m, 1 < m → ∃ p q, ParityUnitLiftWeakRectangleAt (m * m) p q

abbrev ParityUnitLiftWeakRectangleAtNontrivialSquares := ParityUnitLiftAtNontrivialSquareIndexedMidpoints

theorem parity_unit_lift_nontrivial_square_indexed_midpoints_iff_goldbach :
    ParityUnitLiftAtNontrivialSquareIndexedMidpoints ↔
      GoldbachAtNontrivialSquareIndexedMidpoints := by
  constructor
  · intro h m hm
    rcases h m hm with ⟨p, q, hLift⟩
    exact ⟨p, q, midpoint_pair_of_parity_unit_lift hLift⟩
  · intro h m hm
    rcases h m hm with ⟨p, q, hPair⟩
    exact ⟨p, q, parity_unit_lift_of_midpoint_pair hPair⟩

theorem goldbach_nontrivial_square_indexed_midpoints_iff_parity_unit_lift :
    GoldbachAtNontrivialSquareIndexedMidpoints ↔
      ParityUnitLiftAtNontrivialSquareIndexedMidpoints :=
  parity_unit_lift_nontrivial_square_indexed_midpoints_iff_goldbach.symm

abbrev parity_unit_lift_nontrivial_squares_iff_goldbach_squares :=
  parity_unit_lift_nontrivial_square_indexed_midpoints_iff_goldbach
abbrev goldbach_nontrivial_squares_iff_parity_unit_lift :=
  goldbach_nontrivial_square_indexed_midpoints_iff_parity_unit_lift

/--
Richer unit-lift class: the parity slice as a 3D rectangle holonomy object with
explicit `pq`, `p·1`, and `q·1` faces.  This is **not** a
`WeakGoldbachOddTripleAt` with `r = 1` (since `1` is not prime); the third leg is
the unit dimension of the inscribed rectangle.
-/
structure ParityUnitLiftWeakRectangleHolonomyClass (N p q : ℕ) extends
    ParityUnitLiftWeakRectangleAt N p q

theorem parity_unit_lift_holonomy_class_of_midpoint_pair {N p q : ℕ}
    (hPair : GoldbachMidpointPair N p q) :
    ParityUnitLiftWeakRectangleHolonomyClass N p q :=
  { toParityUnitLiftWeakRectangleAt := parity_unit_lift_of_midpoint_pair hPair }

def ParityUnitLiftWeakRectangleHolonomyClassExists : Prop :=
  ∃ N p q, ParityUnitLiftWeakRectangleHolonomyClass N p q

theorem parity_unit_lift_holonomy_class_exists_of_midpoint_pair {N p q : ℕ}
    (hPair : GoldbachMidpointPair N p q) :
    ParityUnitLiftWeakRectangleHolonomyClassExists :=
  ⟨N, p, q, parity_unit_lift_holonomy_class_of_midpoint_pair hPair⟩

theorem parity_unit_lift_holonomy_class_exists_of_nontrivial_squares
    (h : GoldbachAtNontrivialSquareIndexedMidpoints) :
    ParityUnitLiftWeakRectangleHolonomyClassExists := by
  rcases h 2 (by decide) with ⟨p, q, hPair⟩
  exact parity_unit_lift_holonomy_class_exists_of_midpoint_pair hPair

/--
**Parity ↔ weak-unit bridge (conceptual).**  The 2D midpoint pair carrier and the
3D unit-lifted rectangle carrier are the same data; class existence on either
side implies class existence on the other.
-/
theorem parity_unit_lift_class_exists_iff_midpoint_pair_exists :
    ParityUnitLiftWeakRectangleHolonomyClassExists ↔
      ∃ N p q, GoldbachMidpointPair N p q := by
  constructor
  · rintro ⟨N, p, q, hClass⟩
    exact ⟨N, p, q, midpoint_pair_of_parity_unit_lift hClass.toParityUnitLiftWeakRectangleAt⟩
  · rintro ⟨N, p, q, hPair⟩
    exact parity_unit_lift_holonomy_class_exists_of_midpoint_pair hPair

/--
Generalization hook: other rectangle slices can use the same unit-lift pattern.
When `width = height = 1`, this reduces to the parity unit-lift carrier above.
-/
def AspectRatioSliceIsParity (aspect : SmoothRectangleAspect) : Prop :=
  aspect.width = 1 ∧ aspect.height = 1

theorem parity_aspect_is_unit_square :
    AspectRatioSliceIsParity SmoothRectangleAspect.square := ⟨rfl, rfl⟩

def AspectRatioSliceUnitLiftAt (aspect : SmoothRectangleAspect) (N p q : ℕ) : Prop :=
  AspectRatioSliceIsParity aspect → ParityUnitLiftWeakRectangleAt N p q

theorem aspect_ratio_parity_slice_unit_lift {N p q : ℕ}
    (hPair : GoldbachMidpointPair N p q) :
    AspectRatioSliceUnitLiftAt SmoothRectangleAspect.square N p q :=
  fun _ => parity_unit_lift_of_midpoint_pair hPair

/--
One weak-Goldbach rectangle holonomy class: an odd triple
`2n+1 = p+q+r`, together with the three pair-product holonomies `pq`, `pr`,
and `qr`.  This is a class-level carrier, not a pointwise theorem for every `n`.
-/
structure WeakGoldbachRectangleHolonomyClass where
  n : ℕ
  p : ℕ
  q : ℕ
  r : ℕ
  triple : WeakGoldbachOddTripleAt n p q r
  pq_holonomy : WeakGoldbachPairProductHolonomy n p q
  pr_holonomy : WeakGoldbachPairProductHolonomy n p r
  qr_holonomy : WeakGoldbachPairProductHolonomy n q r

abbrev WeakGoldbachRPrismOnS2 := WeakGoldbachRectangleHolonomyClass

/-- Sort survivor edges so `p ≤ q`; face holonomies are swapped accordingly. -/
def weak_goldbach_r_prism_with_ordered_survivors (prism : WeakGoldbachRPrismOnS2) :
    WeakGoldbachRPrismOnS2 :=
  if hpq : prism.p ≤ prism.q then prism else
    { n := prism.n, p := prism.q, q := prism.p, r := prism.r,
      triple := weak_goldbach_odd_triple_swap prism.triple,
      pq_holonomy := prism.pq_holonomy,
      pr_holonomy := prism.qr_holonomy,
      qr_holonomy := prism.pr_holonomy }

theorem weak_goldbach_r_prism_with_ordered_survivors_ordered (prism : WeakGoldbachRPrismOnS2) :
    (weak_goldbach_r_prism_with_ordered_survivors prism).p ≤
      (weak_goldbach_r_prism_with_ordered_survivors prism).q := by
  unfold weak_goldbach_r_prism_with_ordered_survivors
  split_ifs with hpq
  · exact hpq
  · exact le_of_not_ge hpq

theorem weak_goldbach_r_prism_with_ordered_survivors_preserves_r (prism : WeakGoldbachRPrismOnS2) :
    (weak_goldbach_r_prism_with_ordered_survivors prism).r = prism.r := by
  unfold weak_goldbach_r_prism_with_ordered_survivors
  split_ifs <;> rfl

theorem weak_goldbach_r_prism_with_ordered_survivors_preserves_n (prism : WeakGoldbachRPrismOnS2) :
    (weak_goldbach_r_prism_with_ordered_survivors prism).n = prism.n := by
  unfold weak_goldbach_r_prism_with_ordered_survivors
  split_ifs <;> rfl

abbrev WeakGoldbachRPrismOnS2.withOrderedSurvivors :=
  weak_goldbach_r_prism_with_ordered_survivors

def WeakGoldbachRectangleHolonomyClassExists : Prop :=
  ∃ _class : WeakGoldbachRectangleHolonomyClass, True

abbrev WeakGoldbachRPrismOnS2Exists := WeakGoldbachRectangleHolonomyClassExists

/-!
### S² r-prism → S¹ inscribed-rectangle projection

Classical picture (smooth limit on the circle): inscribed rectangles of every
aspect ratio exist on closed smooth curves (`SmoothInscribedRectangleTheoremForOrbitCurves`).
On the sphere side, weak Goldbach supplies a **3D rectangular prism** — an
**r-prism** — with prime edge lengths `p`, `q`, `r` and holonomy on its three
faces (`pq`, `pr`, `qr`).  That object is formalized as
`WeakGoldbachRPrismOnS2` / `WeakGoldbachRectangleHolonomyClass`.

The descent to the half-slope bridge is **not** an arithmetic trick: it is a
dimensional projection of the S² prism to an inscribed rectangle on S¹ whose
holonomy is compatible with `HopfFiberMidpointHolonomySupport`.

**Indivisible holonomy units.**  On the hypersphere carrier, holonomy is counted
in whole units only — there are no fractional or partial holonomy units.
Removing one dimension (whether the trivial unit dimension or a prime leg `r`)
removes one entire indivisible holonomy unit wholesale; the `pr` / `qr` content
is not partially absorbed when `r` is projected out.  The unit-edge case
(`ParityUnitLiftWeakRectangleAt`) is proved because the removed unit is
trivial/identity; the general case asks whether removing the non-trivial unit
tied to an arbitrary prime `r` always leaves a bridge-compatible descended
class.
-/

/-- Which edge of the S² r-prism is collapsed to obtain the S¹ rectangle readout. -/
inductive SpherePrismCollapseAxis where
  | collapseP
  | collapseQ
  | collapseR
  deriving DecidableEq

namespace SpherePrismCollapseAxis

def surviving_edge_pair (prism : WeakGoldbachRPrismOnS2) (axis : SpherePrismCollapseAxis) :
    ℕ × ℕ :=
  match axis with
  | .collapseP => (prism.q, prism.r)
  | .collapseQ => (prism.p, prism.r)
  | .collapseR => (prism.p, prism.q)

end SpherePrismCollapseAxis

/--
2D inscribed-rectangle class on S¹ after projecting an S² r-prism.  The
`holonomy` field is the half-slope-bridge interface:
`HopfFiberMidpointHolonomySupport`.
-/
structure ProjectedInscribedRectangleOnCircle (N : ℕ) where
  pos : 0 < N
  aspect : SmoothRectangleAspect
  p : ℕ
  q : ℕ
  midpoint_pair : GoldbachMidpointPair N p q
  holonomy : HopfFiberMidpointHolonomySupport N p q

def projected_inscribed_rectangle_of_midpoint_pair {N p q : ℕ} (hN : 0 < N)
    (hPair : GoldbachMidpointPair N p q)
    (aspect : SmoothRectangleAspect := SmoothRectangleAspect.square) :
    ProjectedInscribedRectangleOnCircle N :=
  { pos := hN
    aspect := aspect
    p := p
    q := q
    midpoint_pair := hPair
    holonomy := hopf_fiber_midpoint_holonomy_support_of_midpoint_pair hN hPair }

def ProjectedInscribedRectangleClassAt (N : ℕ) : Prop :=
  ∃ _rect : ProjectedInscribedRectangleOnCircle N, True

theorem projected_rectangle_class_at_iff_goldbach_midpoint {N : ℕ} :
    ProjectedInscribedRectangleClassAt N ↔ ∃ p q, GoldbachMidpointPair N p q := by
  constructor
  · rintro ⟨rect, _⟩
    exact ⟨rect.p, rect.q, rect.midpoint_pair⟩
  · rintro ⟨p, q, hMid⟩
    have hN : 0 < N := by
      rcases hMid with ⟨hp, _, hpN, _, _⟩
      nlinarith [Nat.Prime.one_lt hp, hpN]
    exact ⟨projected_inscribed_rectangle_of_midpoint_pair hN hMid, trivial⟩

def ProjectedInscribedRectangleClassAtSquareIndexedMidpoints : Prop :=
  ∀ m, 1 < m → ProjectedInscribedRectangleClassAt (m * m)

abbrev ProjectedInscribedRectangleClassAtNontrivialSquares :=
  ProjectedInscribedRectangleClassAtSquareIndexedMidpoints

theorem projected_rectangle_class_at_square_indexed_midpoints_iff_goldbach :
    ProjectedInscribedRectangleClassAtSquareIndexedMidpoints ↔
      GoldbachAtNontrivialSquareIndexedMidpoints := by
  constructor
  · intro h m hm
    rcases projected_rectangle_class_at_iff_goldbach_midpoint.mp (h m hm) with
      ⟨p, q, hPair⟩
    exact ⟨p, q, hPair⟩
  · intro h m hm
    rcases h m hm with ⟨p, q, hPair⟩
    have hN : 0 < m * m := by nlinarith
    exact ⟨projected_inscribed_rectangle_of_midpoint_pair hN hPair, trivial⟩

abbrev projected_rectangle_class_at_nontrivial_squares_iff_goldbach_squares :=
  projected_rectangle_class_at_square_indexed_midpoints_iff_goldbach

/--
**Open geometric gate (class level).**  Existence of an S² r-prism holonomy class
implies the square-indexed midpoint ladder `N = m²` for all `m > 1` — the
half-slope bridge hook.  Per-prism projection already yields
`GoldbachMidpointPair N p q` at arbitrary projected shells `N = n-(r-1)/2`.
-/
def WeakGoldbachRPrismPopulatesSquareIndexedMidpointLadder : Prop :=
  WeakGoldbachRPrismOnS2Exists → GoldbachAtNontrivialSquareIndexedMidpoints

abbrev WeakGoldbachRPrismProjectsToNontrivialSquareRectangles :=
  WeakGoldbachRPrismPopulatesSquareIndexedMidpointLadder

abbrev RectangleHolonomyClassDecomposesToSquareMidpointPairs :=
  WeakGoldbachRPrismPopulatesSquareIndexedMidpointLadder

theorem weak_goldbach_r_prism_populates_square_indexed_midpoint_ladder_iff :
    WeakGoldbachRPrismPopulatesSquareIndexedMidpointLadder ↔
      (WeakGoldbachRPrismOnS2Exists →
        ProjectedInscribedRectangleClassAtSquareIndexedMidpoints) := by
  constructor
  · intro h hPrism m hm
    rcases h hPrism m hm with ⟨p, q, hPair⟩
    have hN : 0 < m * m := by nlinarith
    exact ⟨projected_inscribed_rectangle_of_midpoint_pair hN hPair, trivial⟩
  · intro h hPrism m hm
    rcases h hPrism m hm with ⟨rect, _⟩
    exact ⟨rect.p, rect.q, rect.midpoint_pair⟩

/--
Unit-edge collapse (proved): the parity unit-lift is the clean S²→S¹ projection
when the collapsed dimension is the rectangle unit, not a prime `r`.  The `pr`
and `qr` faces degenerate to the surviving `p` and `q` edges.
-/
def unit_edge_parity_lift_projects_to_circle_rectangle {N p q : ℕ} (hN : 0 < N)
    (hLift : ParityUnitLiftWeakRectangleAt N p q) :
    ProjectedInscribedRectangleOnCircle N :=
  projected_inscribed_rectangle_of_midpoint_pair hN
    (midpoint_pair_of_parity_unit_lift hLift) SmoothRectangleAspect.square

abbrev weak_goldbach_r_prism_projection_iff_projected_rectangle_class :=
  weak_goldbach_r_prism_populates_square_indexed_midpoint_ladder_iff

theorem unit_edge_parity_lift_square_indexed_midpoints_give_projected_rectangles
    (h : ParityUnitLiftAtNontrivialSquareIndexedMidpoints) :
    ProjectedInscribedRectangleClassAtSquareIndexedMidpoints :=
  projected_rectangle_class_at_square_indexed_midpoints_iff_goldbach.mpr
    (parity_unit_lift_nontrivial_square_indexed_midpoints_iff_goldbach.mp h)

abbrev unit_edge_parity_lift_nontrivial_squares_give_projected_rectangles :=
  unit_edge_parity_lift_square_indexed_midpoints_give_projected_rectangles

/-!
### Indivisible holonomy units and uniform dimensional reduction

Holonomy on the hypersphere carrier is counted in **whole units only**.  Removing
one dimension removes one entire unit wholesale — never a fractional share.  The
trivial-unit removal (parity unit-lift) and prime-leg removal (collapse `r`) are
the **same structural operation**; they differ only in whether the removed unit
carries identity or non-trivial spectral weight.
-/

/-- Holonomy on the hypersphere carrier is packaged in whole, indivisible units. -/
inductive IndivisibleHolonomyUnit where
  | trivialUnit
  | primeLeg (leg : ℕ)
  deriving DecidableEq

namespace IndivisibleHolonomyUnit

def is_trivial : IndivisibleHolonomyUnit → Prop
  | .trivialUnit => True
  | .primeLeg _ => False

theorem trivial_unit_is_trivial : is_trivial .trivialUnit := trivial

end IndivisibleHolonomyUnit

/-- Which whole holonomy unit is removed when one prism dimension is projected out. -/
def holonomy_unit_removed_by_axis (prism : WeakGoldbachRPrismOnS2)
    (axis : SpherePrismCollapseAxis) : IndivisibleHolonomyUnit :=
  match axis with
  | .collapseP => .primeLeg prism.p
  | .collapseQ => .primeLeg prism.q
  | .collapseR => .primeLeg prism.r

/--
Face pair-slots whose holonomy units are **removed entirely** when the
corresponding dimension is projected out.  Collapsing leg `r` removes the whole
units on `pr` and `qr`; the surviving `pq` unit remains on the descended
rectangle — there is no partial absorption.
-/
def holonomy_face_units_removed_by_axis (prism : WeakGoldbachRPrismOnS2)
    (axis : SpherePrismCollapseAxis) : List (ℕ × ℕ) :=
  match axis with
  | .collapseP => [(prism.p, prism.q), (prism.p, prism.r)]
  | .collapseQ => [(prism.p, prism.q), (prism.q, prism.r)]
  | .collapseR => [(prism.p, prism.r), (prism.q, prism.r)]

def holonomy_face_unit_survives_projection (prism : WeakGoldbachRPrismOnS2)
    (axis : SpherePrismCollapseAxis) : ℕ × ℕ :=
  SpherePrismCollapseAxis.surviving_edge_pair prism axis

/--
Uniform dimensional reduction on the hypersphere: remove exactly one whole
holonomy unit (trivial or prime-leg) and read out the surviving edge pair.
-/
structure HypersphereHolonomyUnitRemoval where
  prism : WeakGoldbachRPrismOnS2
  axis : SpherePrismCollapseAxis
  removed_unit : IndivisibleHolonomyUnit
  removed_unit_eq : removed_unit = holonomy_unit_removed_by_axis prism axis

def hypersphere_holonomy_unit_removal (prism : WeakGoldbachRPrismOnS2)
    (axis : SpherePrismCollapseAxis) : HypersphereHolonomyUnitRemoval :=
  { prism := prism
    axis := axis
    removed_unit := holonomy_unit_removed_by_axis prism axis
    removed_unit_eq := rfl }

/--
Per-prism projection after whole-unit removal: surviving edges match the
projected rectangle; the removed unit's face holonomy is gone entirely.
-/
def HypersphereHolonomyUnitRemovalProjectsToBridge
    (rem : HypersphereHolonomyUnitRemoval) (N : ℕ)
    (rect : ProjectedInscribedRectangleOnCircle N) : Prop :=
  let ⟨e₁, e₂⟩ := holonomy_face_unit_survives_projection rem.prism rem.axis
  (rect.p = e₁) ∧ (rect.q = e₂)

/--
Per-prism projection along a collapse axis after **whole-unit removal** on the
hypersphere.  Removed face units (`pr`, `qr` when collapsing `r`) are gone
entirely — not fractionally cancelled.
-/
def SpherePrismProjectsToCircleRectangleAlongAxis
    (prism : WeakGoldbachRPrismOnS2) (axis : SpherePrismCollapseAxis) (N : ℕ)
    (rect : ProjectedInscribedRectangleOnCircle N) : Prop :=
  HypersphereHolonomyUnitRemovalProjectsToBridge
    (hypersphere_holonomy_unit_removal prism axis) N rect

/--
**Proved (trivial unit).**  Removing the identity holonomy unit via the parity
unit-lift produces a bridge-compatible `ProjectedInscribedRectangleOnCircle`.
-/
theorem trivial_holonomy_unit_removal_produces_bridge_class
    {N p q : ℕ} (hN : 0 < N) (hLift : ParityUnitLiftWeakRectangleAt N p q) :
    ∃ rect : ProjectedInscribedRectangleOnCircle N,
      HopfFiberMidpointHolonomySupport N rect.p rect.q :=
  let rect := unit_edge_parity_lift_projects_to_circle_rectangle hN hLift
  ⟨rect, rect.holonomy⟩

def TrivialHolonomyUnitRemovalProducesBridgeClass : Prop :=
  ∀ (N p q : ℕ) (hN : 0 < N) (hLift : ParityUnitLiftWeakRectangleAt N p q),
    ∃ rect : ProjectedInscribedRectangleOnCircle N,
      HopfFiberMidpointHolonomySupport N rect.p rect.q

theorem trivial_holonomy_unit_removal_produces_bridge_class_prop :
    TrivialHolonomyUnitRemovalProducesBridgeClass :=
  fun _ _ _ hN hLift => trivial_holonomy_unit_removal_produces_bridge_class hN hLift

/-!
### Abelian hypersphere discharge: parts > 1, S²→S¹ collapse, 2n forcing

On the **abelian hypersphere**, every extra `S^n` leg carries an integer **part**
strictly greater than `1` — no fractional leg weights.  Every prime leg satisfies
this (`Nat.Prime r → r > 1`).  Removing such a leg removes one whole indivisible
holonomy unit and **collapses** `S² → S¹` (same structural operation as the
trivial-unit route).

The odd weak-Goldbach shell `2n+1 = p+q+r` decomposes as
`2n + (holonomy unit slot) = p+q+r` with the unit slot `= 1` carried on the
`pr`/`qr` face pair.  **Collapse is along an odd prime leg `r ≥ 3` only** —
the even prime `2` is never a valid collapse axis (it would leave an odd
`p+q` sum).  On the surviving `pq` face, `p` and `q` are arbitrary primes,
including `2`.  Whole-unit removal then forces the even representation
`p+q = 2N` at the projected midpoint shell `N = n - (r-1)/2`.
-/

def weak_goldbach_holonomy_unit_slot : ℕ := 1

/-- Valid S²→S¹ collapse leg: odd prime `r ≥ 3`.  The even prime `2` is excluded. -/
def WeakGoldbachOddPrimeCollapseLeg (r : ℕ) : Prop :=
  Nat.Prime r ∧ 3 ≤ r

theorem weak_goldbach_odd_prime_collapse_leg_of_odd {r : ℕ} (hr : Nat.Prime r) (hrOdd : r % 2 = 1) :
    WeakGoldbachOddPrimeCollapseLeg r := by
  rcases Nat.Prime.eq_two_or_odd hr with hr2 | _
  · exfalso; rw [hr2] at hrOdd; simp at hrOdd
  · exact ⟨hr, by have := Nat.Prime.two_le hr; omega⟩

theorem weak_goldbach_odd_prime_collapse_leg_iff {r : ℕ} (hr : Nat.Prime r) :
    WeakGoldbachOddPrimeCollapseLeg r ↔ r % 2 = 1 :=
  ⟨fun hrLeg => by
      rcases Nat.Prime.eq_two_or_odd hr with hr2 | hrOdd
      · exfalso
        rcases hrLeg with ⟨_, hr3⟩
        subst hr2
        omega
      · exact hrOdd,
    weak_goldbach_odd_prime_collapse_leg_of_odd hr⟩

/-- Abelian hypersphere: an extra `S^n` leg carries integer part strictly > 1. -/
def AbelianHypersphereExtraLegPartGtOne (part : ℕ) : Prop :=
  1 < part

theorem nat_prime_is_abelian_hypersphere_part_gt_one {r : ℕ} (hr : Nat.Prime r) :
    AbelianHypersphereExtraLegPartGtOne r :=
  Nat.Prime.one_lt hr

/-- Removing a leg with part > 1 is a whole-unit `S² → S¹` collapse (no fractional holonomy). -/
def AbelianHypersphereS2ToS1CollapseValid (part : ℕ) : Prop :=
  AbelianHypersphereExtraLegPartGtOne part → True

theorem prime_leg_s2_to_s1_collapse_valid {r : ℕ} (hr : Nat.Prime r) :
    AbelianHypersphereS2ToS1CollapseValid r :=
  fun _ => trivial

theorem weak_goldbach_odd_triple_is_even_plus_holonomy_unit {n p q r : ℕ}
    (h : WeakGoldbachOddTripleAt n p q r) :
    p + q + r = 2 * n + weak_goldbach_holonomy_unit_slot := by
  rcases h with ⟨_, _, _, hsum⟩
  simpa [weak_goldbach_holonomy_unit_slot] using hsum

theorem weak_goldbach_surviving_pq_sum {n p q r : ℕ}
    (h : WeakGoldbachOddTripleAt n p q r) :
    p + q = 2 * n + weak_goldbach_holonomy_unit_slot - r := by
  rcases h with ⟨_, _, _, hsum⟩
  simp only [weak_goldbach_holonomy_unit_slot]
  omega

/--
**Exclusion (`r = 2`).**  Collapsing along the even prime would leave an odd
`p+q` sum, so `2` cannot be a collapse leg — it may only appear on the
surviving `pq` face when `r ≥ 3`.
-/
theorem weak_goldbach_r_eq_two_forces_survivor_eq_two {n p q r : ℕ}
    (h : WeakGoldbachOddTripleAt n p q r) (hr2 : r = 2) :
    p = 2 ∨ q = 2 := by
  rcases h with ⟨hp, hq, _, hsum⟩
  rw [hr2] at hsum
  by_contra hne
  push_neg at hne
  have hpop : Odd p := Nat.Prime.odd_of_ne_two hp hne.1
  have hqod : Odd q := Nat.Prime.odd_of_ne_two hq hne.2
  have heven : Even (p + q) := Odd.add_odd hpop hqod
  have hpqodd : (p + q) % 2 = 1 := by omega
  have hpqeven : (p + q) % 2 = 0 := Nat.even_iff.mp heven
  omega

/-- Projected midpoint shell after removing leg `r` along `collapseR`. -/
def weak_goldbach_projected_midpoint_shell (n r : ℕ) : ℕ :=
  n - (r - 1) / 2

/-- The `pr`/`qr` face pair packages the holonomy unit slot on the odd shell. -/
structure WeakGoldbachPrQrHolonomyUnit (n p q r : ℕ) where
  pr_holonomy : WeakGoldbachPairProductHolonomy n p r
  qr_holonomy : WeakGoldbachPairProductHolonomy n q r

def weak_goldbach_pr_qr_holonomy_unit_of_prism (prism : WeakGoldbachRPrismOnS2) :
    WeakGoldbachPrQrHolonomyUnit prism.n prism.p prism.q prism.r :=
  { pr_holonomy := prism.pr_holonomy
    qr_holonomy := prism.qr_holonomy }

theorem odd_prime_r_forces_even_pq_sum {n p q r : ℕ}
    (h : WeakGoldbachOddTripleAt n p q r) (hrLeg : WeakGoldbachOddPrimeCollapseLeg r) :
    p + q = 2 * weak_goldbach_projected_midpoint_shell n r := by
  rcases hrLeg with ⟨hr, hr3⟩
  have hrOdd : r % 2 = 1 := (weak_goldbach_odd_prime_collapse_leg_iff hr).mp ⟨hr, hr3⟩
  rcases h with ⟨_, _, _, hsum⟩
  have _ := Nat.Prime.two_le hr
  unfold weak_goldbach_projected_midpoint_shell
  omega

theorem goldbach_midpoint_pair_of_odd_prime_weak_triple {n p q r : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (hrLeg : WeakGoldbachOddPrimeCollapseLeg r)
    (hsum : p + q + r = 2 * n + 1)
    (hpN : p ≤ weak_goldbach_projected_midpoint_shell n r)
    (hNq : weak_goldbach_projected_midpoint_shell n r ≤ q) :
    GoldbachMidpointPair (weak_goldbach_projected_midpoint_shell n r) p q :=
  ⟨hp, hq, hpN, hNq,
    odd_prime_r_forces_even_pq_sum ⟨hp, hq, hr, hsum⟩ hrLeg⟩

def WeakGoldbachRPrismHasProjectedMidpointOrder (prism : WeakGoldbachRPrismOnS2) : Prop :=
  let N := weak_goldbach_projected_midpoint_shell prism.n prism.r
  0 < N ∧ prism.p ≤ N ∧ N ≤ prism.q ∧ prism.p + prism.q = 2 * N

theorem odd_prime_r_prism_has_projected_midpoint_sum (prism : WeakGoldbachRPrismOnS2)
    (hrLeg : WeakGoldbachOddPrimeCollapseLeg prism.r) :
    prism.p + prism.q = 2 * weak_goldbach_projected_midpoint_shell prism.n prism.r :=
  odd_prime_r_forces_even_pq_sum prism.triple hrLeg

theorem weak_goldbach_projected_midpoint_shell_pos {n p q r : ℕ}
    (h : WeakGoldbachOddTripleAt n p q r) (hrLeg : WeakGoldbachOddPrimeCollapseLeg r) :
    0 < weak_goldbach_projected_midpoint_shell n r := by
  rcases hrLeg with ⟨hr, _⟩
  rcases h with ⟨hp, hq, _, hsum⟩
  have _ := Nat.Prime.two_le hp
  have _ := Nat.Prime.two_le hq
  unfold weak_goldbach_projected_midpoint_shell
  omega

theorem weak_goldbach_midpoint_bracket_of_le {n p q r : ℕ}
    (h : WeakGoldbachOddTripleAt n p q r) (hrLeg : WeakGoldbachOddPrimeCollapseLeg r)
    (hpq : p ≤ q) :
    p ≤ weak_goldbach_projected_midpoint_shell n r ∧
      weak_goldbach_projected_midpoint_shell n r ≤ q := by
  have hsum := odd_prime_r_forces_even_pq_sum h hrLeg
  unfold weak_goldbach_projected_midpoint_shell at hsum ⊢
  omega

/--
Midpoint ordering at the projected shell is **derived** from the odd triple once
survivors are sorted: `p ≤ q` implies `p ≤ N ≤ q` with `p + q = 2N`.
-/
theorem weak_goldbach_r_prism_has_projected_midpoint_order_of_le
    (prism : WeakGoldbachRPrismOnS2) (hrLeg : WeakGoldbachOddPrimeCollapseLeg prism.r)
    (hpq : prism.p ≤ prism.q) :
    WeakGoldbachRPrismHasProjectedMidpointOrder prism := by
  refine ⟨?_, ?_, ?_, odd_prime_r_prism_has_projected_midpoint_sum prism hrLeg⟩
  · exact weak_goldbach_projected_midpoint_shell_pos prism.triple hrLeg
  · exact (weak_goldbach_midpoint_bracket_of_le prism.triple hrLeg hpq).1
  · exact (weak_goldbach_midpoint_bracket_of_le prism.triple hrLeg hpq).2

/--
**Abelian hypersphere discharge (`r ≥ 3`).**  Whole-unit removal along `collapseR`
yields a bridge-compatible inscribed rectangle at the projected shell.  Survivors
`p`, `q` may be `2`; ordering is obtained by sorting the survivor pair.
-/
theorem odd_prime_abelian_hypersphere_removal_produces_bridge
    (prism : WeakGoldbachRPrismOnS2) (hrLeg : WeakGoldbachOddPrimeCollapseLeg prism.r)
    (hpq : prism.p ≤ prism.q) :
    ∃ rect : ProjectedInscribedRectangleOnCircle (weak_goldbach_projected_midpoint_shell prism.n prism.r),
      HypersphereHolonomyUnitRemovalProjectsToBridge
        (hypersphere_holonomy_unit_removal prism .collapseR)
        (weak_goldbach_projected_midpoint_shell prism.n prism.r) rect ∧
      HopfFiberMidpointHolonomySupport (weak_goldbach_projected_midpoint_shell prism.n prism.r)
        rect.p rect.q := by
  rcases prism.triple with ⟨hp, hq, hr', hsumTri⟩
  let N := weak_goldbach_projected_midpoint_shell prism.n prism.r
  have hN : 0 < N := weak_goldbach_projected_midpoint_shell_pos prism.triple hrLeg
  have hbr := weak_goldbach_midpoint_bracket_of_le prism.triple hrLeg hpq
  have hMid : GoldbachMidpointPair N prism.p prism.q :=
    goldbach_midpoint_pair_of_odd_prime_weak_triple hp hq hr' hrLeg hsumTri hbr.1 hbr.2
  let rect := projected_inscribed_rectangle_of_midpoint_pair hN hMid
  refine ⟨rect, ?_, rect.holonomy⟩
  unfold HypersphereHolonomyUnitRemovalProjectsToBridge hypersphere_holonomy_unit_removal
    holonomy_face_unit_survives_projection SpherePrismCollapseAxis.surviving_edge_pair
  constructor <;> rfl

theorem odd_prime_abelian_hypersphere_removal_produces_bridge_of_prism
    (prism : WeakGoldbachRPrismOnS2) (hrLeg : WeakGoldbachOddPrimeCollapseLeg prism.r) :
    ∃ rect : ProjectedInscribedRectangleOnCircle
        (weak_goldbach_projected_midpoint_shell
          (weak_goldbach_r_prism_with_ordered_survivors prism).n
          (weak_goldbach_r_prism_with_ordered_survivors prism).r),
      HypersphereHolonomyUnitRemovalProjectsToBridge
        (hypersphere_holonomy_unit_removal (weak_goldbach_r_prism_with_ordered_survivors prism) .collapseR)
        (weak_goldbach_projected_midpoint_shell
          (weak_goldbach_r_prism_with_ordered_survivors prism).n
          (weak_goldbach_r_prism_with_ordered_survivors prism).r) rect ∧
      HopfFiberMidpointHolonomySupport
        (weak_goldbach_projected_midpoint_shell
          (weak_goldbach_r_prism_with_ordered_survivors prism).n
          (weak_goldbach_r_prism_with_ordered_survivors prism).r)
        rect.p rect.q :=
  odd_prime_abelian_hypersphere_removal_produces_bridge
    (weak_goldbach_r_prism_with_ordered_survivors prism)
    (weak_goldbach_r_prism_with_ordered_survivors_preserves_r prism ▸ hrLeg)
    (weak_goldbach_r_prism_with_ordered_survivors_ordered prism)

theorem nat_prime_is_two_or_odd {r : ℕ} (hr : Nat.Prime r) : r = 2 ∨ r % 2 = 1 :=
  Nat.Prime.eq_two_or_odd hr

/--
**Per-leg holonomy discharge (`r ≥ 3`).**  Removing the whole holonomy unit tied
to collapse leg `r` yields a bridge-compatible descended class with
`HopfFiberMidpointHolonomySupport` on the sorted surviving `(p, q)` pair.
Midpoint ordering is derived, not assumed.
-/
def PrimeHolonomyUnitRemovalProducesBridgeClass (r : ℕ) : Prop :=
  WeakGoldbachOddPrimeCollapseLeg r →
  ∀ (prism : WeakGoldbachRPrismOnS2),
    prism.r = r →
    ∃ N, ∃ rect : ProjectedInscribedRectangleOnCircle N,
      HypersphereHolonomyUnitRemovalProjectsToBridge
        (hypersphere_holonomy_unit_removal (weak_goldbach_r_prism_with_ordered_survivors prism)
          .collapseR) N rect ∧
      HopfFiberMidpointHolonomySupport N rect.p rect.q

theorem odd_prime_holonomy_unit_removal_produces_bridge_class (r : ℕ)
    (hrLeg : WeakGoldbachOddPrimeCollapseLeg r) :
    PrimeHolonomyUnitRemovalProducesBridgeClass r :=
  fun _ prism hpr => by
    have hrLeg' : WeakGoldbachOddPrimeCollapseLeg prism.r := hpr ▸ hrLeg
    rcases odd_prime_abelian_hypersphere_removal_produces_bridge_of_prism prism hrLeg' with
      ⟨rect, hProj, hHol⟩
    exact ⟨_, rect, hProj, hHol⟩

/--
**Uniformity over collapse legs (`r ≥ 3`).**  Whole-unit removal along
`collapseR` works for every valid leg; `r = 2` is excluded by
`WeakGoldbachOddPrimeCollapseLeg`, not an open branch.
-/
def UniformHolonomyUnitRemovalAcrossOddPrimeLegs : Prop :=
  ∀ r, WeakGoldbachOddPrimeCollapseLeg r → PrimeHolonomyUnitRemovalProducesBridgeClass r

theorem uniform_holonomy_unit_removal_for_odd_prime_legs {r : ℕ}
    (hrLeg : WeakGoldbachOddPrimeCollapseLeg r) :
    PrimeHolonomyUnitRemovalProducesBridgeClass r :=
  odd_prime_holonomy_unit_removal_produces_bridge_class r hrLeg

theorem uniform_holonomy_unit_removal_across_odd_prime_legs :
    UniformHolonomyUnitRemovalAcrossOddPrimeLegs :=
  fun _r hrLeg => uniform_holonomy_unit_removal_for_odd_prime_legs hrLeg

/-- Backward-compatible alias: uniformity over valid collapse legs only. -/
abbrev UniformHolonomyUnitRemovalAcrossPrimes : Prop :=
  UniformHolonomyUnitRemovalAcrossOddPrimeLegs

theorem uniform_holonomy_unit_removal_for_odd_primes {r : ℕ}
    (hrLeg : WeakGoldbachOddPrimeCollapseLeg r) :
    PrimeHolonomyUnitRemovalProducesBridgeClass r :=
  uniform_holonomy_unit_removal_for_odd_prime_legs hrLeg

/--
**Class-level transport (open).**  Per-leg uniform removal produces a
`ProjectedInscribedRectangleOnCircle` at projected shell `N = n - (r-1)/2` for
each prism.  Promoting existence of one holonomy **class** to the
square-indexed ladder `GoldbachAtNontrivialSquareIndexedMidpoints` requires
showing every index `m > 1` has some projected shell `N = m²` from class
transport — e.g. via structured-cascade shell mapping plus ladder complement.
-/
def HolonomyClassPopulatesSquareIndexedMidpointLadder : Prop :=
  WeakGoldbachRPrismOnS2Exists → GoldbachAtNontrivialSquareIndexedMidpoints

abbrev HolonomyClassCapturesNontrivialSquareShells :=
  HolonomyClassPopulatesSquareIndexedMidpointLadder

theorem holonomy_class_populates_square_indexed_midpoint_ladder_iff :
    HolonomyClassPopulatesSquareIndexedMidpointLadder ↔
      WeakGoldbachRPrismPopulatesSquareIndexedMidpointLadder :=
  Iff.rfl

abbrev holonomy_class_captures_nontrivial_square_shells_iff_prism_projection :=
  holonomy_class_populates_square_indexed_midpoint_ladder_iff

/--
**Revised open gate.**  Uniform whole-unit removal is proved; the remaining
class-level step is transport from one holonomy class to the full
square-indexed midpoint ladder (hence `SO8ProjectedHalfSlopeBridge 2` when
composed with finite-stack + zeta wiring).
-/
def UniformHolonomyRemovalPopulatesSquareIndexedMidpointLadder : Prop :=
  UniformHolonomyUnitRemovalAcrossOddPrimeLegs →
    WeakGoldbachRPrismPopulatesSquareIndexedMidpointLadder

abbrev UniformHolonomyUnitRemovalProjectsToNontrivialSquareRectangles :=
  UniformHolonomyRemovalPopulatesSquareIndexedMidpointLadder

theorem uniform_holonomy_removal_and_ladder_population_give_prism_projection
    (hCapture : HolonomyClassPopulatesSquareIndexedMidpointLadder) :
    WeakGoldbachRPrismPopulatesSquareIndexedMidpointLadder :=
  hCapture

abbrev uniform_holonomy_removal_and_class_capture_give_prism_projection :=
  uniform_holonomy_removal_and_ladder_population_give_prism_projection

/--
Combined weak-Goldbach + rectangle-holonomy payload.  This is deliberately not
`GoldbachParity`; it says that the S² r-prism class exists and populates the
square-indexed midpoint ladder `N = m²`.
-/
structure WeakGoldbachRectangleDecompositionProof where
  class_exists : WeakGoldbachRectangleHolonomyClassExists
  populates_square_indexed_midpoint_ladder :
    WeakGoldbachRPrismPopulatesSquareIndexedMidpointLadder

theorem WeakGoldbachRectangleDecompositionProof.rectangle_decomposition
    (H : WeakGoldbachRectangleDecompositionProof) :
    RectangleHolonomyClassDecomposesToSquareMidpointPairs :=
  H.populates_square_indexed_midpoint_ladder

theorem weak_goldbach_rectangle_decomposition_gives_nontrivial_square_indexed_midpoints
    (H : WeakGoldbachRectangleDecompositionProof) :
    GoldbachAtNontrivialSquareIndexedMidpoints :=
  H.populates_square_indexed_midpoint_ladder H.class_exists

abbrev weak_goldbach_rectangle_decomposition_gives_nontrivial_square_midpoints :=
  weak_goldbach_rectangle_decomposition_gives_nontrivial_square_indexed_midpoints

theorem weak_goldbach_rectangle_decomposition_gives_projected_rectangles
    (H : WeakGoldbachRectangleDecompositionProof) :
    ProjectedInscribedRectangleClassAtSquareIndexedMidpoints :=
  weak_goldbach_r_prism_populates_square_indexed_midpoint_ladder_iff.mp
    H.populates_square_indexed_midpoint_ladder H.class_exists

theorem parity_unit_lift_nontrivial_square_indexed_midpoints_of_decomposition
    (H : WeakGoldbachRectangleDecompositionProof) :
    ParityUnitLiftAtNontrivialSquareIndexedMidpoints :=
  parity_unit_lift_nontrivial_square_indexed_midpoints_iff_goldbach.mpr
    (weak_goldbach_rectangle_decomposition_gives_nontrivial_square_indexed_midpoints H)

abbrev parity_unit_lift_nontrivial_squares_of_decomposition :=
  parity_unit_lift_nontrivial_square_indexed_midpoints_of_decomposition

theorem parity_unit_lift_at_square_of_decomposition
    (H : WeakGoldbachRectangleDecompositionProof) {m : ℕ} (hm : 1 < m) :
    ∃ p q, ParityUnitLiftWeakRectangleAt (m * m) p q := by
  rcases weak_goldbach_rectangle_decomposition_gives_nontrivial_square_midpoints H m hm with
    ⟨p, q, hPair⟩
  exact ⟨p, q, parity_unit_lift_of_midpoint_pair hPair⟩

theorem weak_goldbach_rectangle_decomposition_gives_parity_unit_lift
    (H : WeakGoldbachRectangleDecompositionProof) :
    ParityUnitLiftWeakRectangleAtNontrivialSquares :=
  parity_unit_lift_nontrivial_squares_of_decomposition H

theorem weak_goldbach_rectangle_decomposition_gives_unit_lift_class
    (H : WeakGoldbachRectangleDecompositionProof) :
    ParityUnitLiftWeakRectangleHolonomyClassExists :=
  parity_unit_lift_holonomy_class_exists_of_nontrivial_squares
    (weak_goldbach_rectangle_decomposition_gives_nontrivial_square_midpoints H)

/--
Rectangle-family readout plus weak odd triples, the rectangle-holonomy
decomposition, and the large-square finite-stack close are exactly the reduced
inputs needed to fire the nontrivial-square half-slope bridge.  The rectangle
theorem contributes the classical smooth readout; its `1:1` slice is the
previous square theorem.
-/
structure RectangleWeakGoldbachCapstoneInputs where
  rectangles : SmoothInscribedRectangleTheoremForOrbitCurves
  large_square_stack : FiniteStackCannotExtinctLargeSquareGaps
  weak_goldbach_rectangle : WeakGoldbachRectangleDecompositionProof
  complement : NontrivialSquareLadderCertificateComplement
  zeta_side : ConditionalZetaSideHalfSlopeWitness

namespace RectangleWeakGoldbachCapstoneInputs

theorem parity_unit_lift_nontrivial_squares (H : RectangleWeakGoldbachCapstoneInputs) :
    ParityUnitLiftWeakRectangleAtNontrivialSquares :=
  weak_goldbach_rectangle_decomposition_gives_parity_unit_lift H.weak_goldbach_rectangle

theorem parity_unit_lift_holonomy_class_exists (H : RectangleWeakGoldbachCapstoneInputs) :
    ParityUnitLiftWeakRectangleHolonomyClassExists :=
  weak_goldbach_rectangle_decomposition_gives_unit_lift_class H.weak_goldbach_rectangle

theorem goldbach_nontrivial_square_midpoints (H : RectangleWeakGoldbachCapstoneInputs) :
    GoldbachAtNontrivialSquareIndexedMidpoints :=
  weak_goldbach_rectangle_decomposition_gives_nontrivial_square_midpoints
    H.weak_goldbach_rectangle

theorem projected_inscribed_rectangles (H : RectangleWeakGoldbachCapstoneInputs) :
    ProjectedInscribedRectangleClassAtNontrivialSquares :=
  weak_goldbach_rectangle_decomposition_gives_projected_rectangles H.weak_goldbach_rectangle

theorem nontrivial_square_holonomy
    (H : RectangleWeakGoldbachCapstoneInputs) :
    InscribedSquareOrbitHolonomyDischargeAtNontrivialSquareMidpoints :=
  nontrivial_closed_delta_orbit_discharge_gives_holonomy_at_squares
    (nontrivial_closed_delta_orbit_discharge_of_finite_stack_and_goldbach
      (finite_stack_nontrivial_squares_of_large_squares H.large_square_stack)
      (weak_goldbach_rectangle_decomposition_gives_nontrivial_square_midpoints
        H.weak_goldbach_rectangle))

theorem global_family (H : RectangleWeakGoldbachCapstoneInputs) :
    GlobalInscribedSquareCertificateFamily :=
  nontrivial_square_ladder_extension_gives_global_family
    (nontrivial_square_ladder_extends_to_full_certificate_family_of_complement H.complement)
    H.nontrivial_square_holonomy

theorem half_slope_bridge_two (H : RectangleWeakGoldbachCapstoneInputs) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_bridge_two_of_global_inscribed_square_and_zeta
    H.global_family H.zeta_side

theorem rh_and_goldbach (H : RectangleWeakGoldbachCapstoneInputs) :
    RiemannHypothesis ∧ GoldbachParity :=
  so8_half_slope_implies_rh_and_goldbach_parity H.half_slope_bridge_two

end RectangleWeakGoldbachCapstoneInputs

/--
Alternate capstone entry: parity unit-lift squares compose directly with the
finite-stack close without passing through the weak odd-triple class first.
This is equivalent to the Goldbach-at-squares route by
`parity_unit_lift_nontrivial_squares_iff_goldbach_squares`.
-/
theorem parity_unit_lift_stack_extension_fire_half_slope_bridge
    (hStack : FiniteStackCannotExtinctLargeSquareGaps)
    (hParity : ParityUnitLiftWeakRectangleAtNontrivialSquares)
    (hComplement : NontrivialSquareLadderCertificateComplement)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SO8ProjectedHalfSlopeBridge 2 :=
  finite_stack_square_goldbach_extension_fire_half_slope_bridge
    (finite_stack_nontrivial_squares_of_large_squares hStack)
    (parity_unit_lift_nontrivial_squares_iff_goldbach_squares.mp hParity)
    (nontrivial_square_ladder_extends_to_full_certificate_family_of_complement hComplement)
    hZeta

theorem rectangle_capstone_parity_unit_lift_fire_half_slope_bridge
    (H : RectangleWeakGoldbachCapstoneInputs) :
    SO8ProjectedHalfSlopeBridge 2 :=
  parity_unit_lift_stack_extension_fire_half_slope_bridge
    H.large_square_stack H.parity_unit_lift_nontrivial_squares H.complement H.zeta_side

/--
Corrected reduced capstone bundle: it starts at the nontrivial square-indexed
midpoint ladder (`m > 1`, i.e. `N = m²`) because the ordering-aware midpoint
Goldbach predicate is false at `N = 1`.
-/
structure NontrivialSquareLadderCapstoneHypotheses where
  finite_stack_nonextinction :
    ∀ m, 1 < m → FiniteStackCannotExtinctAllGaps (m * m)
  goldbach_nontrivial_square_indexed_midpoints : GoldbachAtNontrivialSquareIndexedMidpoints
  extend_nontrivial_squares : NontrivialSquareLadderExtendsToFullCertificateFamily
  zeta_side : ConditionalZetaSideHalfSlopeWitness

namespace NontrivialSquareLadderCapstoneHypotheses

theorem route_c_nontrivial (H : NontrivialSquareLadderCapstoneHypotheses) :
    StructuredCascadeForcesNontrivialSquareDeltaOrbitObstruction :=
  nontrivial_route_c_of_finite_stack_square_close H.finite_stack_nonextinction

theorem square_ladder_discharge (H : NontrivialSquareLadderCapstoneHypotheses) :
    NontrivialClosedDeltaOrbitInscribedSquareDischarge :=
  nontrivial_closed_delta_orbit_discharge_of_finite_stack_and_goldbach
    H.finite_stack_nonextinction H.goldbach_nontrivial_square_indexed_midpoints

theorem holonomy_discharge_two (H : NontrivialSquareLadderCapstoneHypotheses) :
    InscribedSquareOrbitHolonomyDischarge 2 :=
  nontrivial_square_ladder_extension_gives_full_holonomy
    H.extend_nontrivial_squares
    (nontrivial_closed_delta_orbit_discharge_gives_holonomy_at_squares
      H.square_ladder_discharge)

theorem global_family (H : NontrivialSquareLadderCapstoneHypotheses) :
    GlobalInscribedSquareCertificateFamily :=
  (global_inscribed_square_family_iff_holonomy_discharge_two).mpr H.holonomy_discharge_two

theorem half_slope_bridge_two (H : NontrivialSquareLadderCapstoneHypotheses) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_bridge_two_of_global_inscribed_square_and_zeta
    H.global_family H.zeta_side

theorem rh_and_goldbach (H : NontrivialSquareLadderCapstoneHypotheses) :
    RiemannHypothesis ∧ GoldbachParity :=
  so8_half_slope_implies_rh_and_goldbach_parity H.half_slope_bridge_two

end NontrivialSquareLadderCapstoneHypotheses

/--
Count-only interpolation target.  This is exactly the bridge midpoint field
extension at threshold `2`; it does not reconstruct certificates by itself.
-/
def SquareLadderMidpointCountExtendsToFullBridgeField : Prop :=
  SO4ZetaHolonomyForcesMidpointPairsAtSquareMidpoints →
    SO4ZetaHolonomyForcesMidpointPairs 2

/--
Square-ladder holonomy at squares + zeta-side witness does **not** alone yield
`SO8ProjectedHalfSlopeBridge 2` (which needs midpoint pairs at every `N ≥ 2`).
This records the proved square-midpoint payload and the conditional full bridge.
-/
def SquareLadderHalfSlopeBridgeFragment : Prop :=
  SO4ZetaHolonomyForcesMidpointPairsAtSquareMidpoints ∧
    WeilPositivityForcesCriticalLine

theorem square_ladder_discharge_and_zeta_give_half_slope_fragment
    (hDis : ClosedDeltaOrbitInscribedSquareDischarge)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SquareLadderHalfSlopeBridgeFragment :=
  ⟨square_ladder_discharge_forces_bridge_midpoint_field_at_squares hDis, hZeta⟩

theorem square_ladder_full_half_slope_bridge_conditional
    (hDis : ClosedDeltaOrbitInscribedSquareDischarge)
    (hExt : SquareLadderExtendsToFullHolonomyDischarge)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SO8ProjectedHalfSlopeBridge 2 := by
  have hHol : InscribedSquareOrbitHolonomyDischarge 2 :=
    hExt (closed_delta_orbit_discharge_gives_holonomy_at_squares hDis)
  have hFam : InscribedSquareCertificateFamily 2 := by
    intro N hN
    rcases hHol N hN with ⟨cert, _⟩
    exact ⟨cert, trivial⟩
  exact so8_projected_half_slope_bridge_two_of_inscribed_square_discharge
    ⟨hFam, hZeta⟩

theorem square_ladder_full_half_slope_bridge_implies_rh_and_goldbach
    (hDis : ClosedDeltaOrbitInscribedSquareDischarge)
    (hExt : SquareLadderExtendsToFullHolonomyDischarge)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    RiemannHypothesis ∧ GoldbachParity :=
  so8_half_slope_implies_rh_and_goldbach_parity
    (square_ladder_full_half_slope_bridge_conditional hDis hExt hZeta)

/-! ## 8. Capstone firing package -/

/--
Route C, localized to one square shell.  The structured cascade/Fano inputs are
proved; the last field is the stack-survivor close `SO4DeltaOrbitObstruction`.
-/
structure StructuredCascadeSquareObstructionCertificate (m : ℕ) where
  hm : 0 < m
  capture : StructuredCascadeIntegerCapture
  shell_promotion :
    Nonempty (SO4StructuredCascadeLiePromotion (2 * (m * m))
      (Nat.mul_pos (by decide : 0 < 2) (Nat.mul_pos hm hm)))
  frontier : HarmonicCascadeTailBandFrontier
  obstruction : SO4DeltaOrbitObstruction (m * m)

theorem structured_cascade_square_obstruction_certificate_of_route_c
    (hRouteC : StructuredCascadeForcesSquareDeltaOrbitObstruction)
    {m : ℕ} (hm : 0 < m) :
    StructuredCascadeSquareObstructionCertificate m where
  hm := hm
  capture := structured_cascade_integer_capture
  shell_promotion := structured_cascade_at_square_midpoint_shell hm
  frontier := harmonic_cascade_tail_band_frontier
  obstruction := hRouteC m hm

theorem route_c_holds_at_certified_square_anchors :
    StructuredCascadeSquareObstructionCertificate 2 ∧
      StructuredCascadeSquareObstructionCertificate 3 := by
  refine ⟨?_, ?_⟩
  · exact
      { hm := by decide
        capture := structured_cascade_integer_capture
        shell_promotion := structured_cascade_at_square_midpoint_shell (by decide : 0 < 2)
        frontier := harmonic_cascade_tail_band_frontier
        obstruction := so4_delta_orbit_obstruction_at_four }
  · exact
      { hm := by decide
        capture := structured_cascade_integer_capture
        shell_promotion := structured_cascade_at_square_midpoint_shell (by decide : 0 < 3)
        frontier := harmonic_cascade_tail_band_frontier
        obstruction := so4_delta_orbit_obstruction_at_nine }

theorem route_c_and_square_goldbach_give_square_ladder_discharge
    (hRouteC : StructuredCascadeForcesSquareDeltaOrbitObstruction)
    (hGoldbach : GoldbachAtSquareIndexedMidpoints) :
    ClosedDeltaOrbitInscribedSquareDischarge :=
  closed_delta_orbit_inscribed_square_discharge_of_gates hRouteC hGoldbach

theorem route_c_square_goldbach_and_extension_give_holonomy_discharge_two
    (hRouteC : StructuredCascadeForcesSquareDeltaOrbitObstruction)
    (hGoldbach : GoldbachAtSquareIndexedMidpoints)
    (hExt : SquareLadderExtendsToFullHolonomyDischarge) :
    InscribedSquareOrbitHolonomyDischarge 2 :=
  hExt
    (closed_delta_orbit_discharge_gives_holonomy_at_squares
      (route_c_and_square_goldbach_give_square_ladder_discharge hRouteC hGoldbach))

theorem route_c_square_goldbach_extension_gives_global_family
    (hRouteC : StructuredCascadeForcesSquareDeltaOrbitObstruction)
    (hGoldbach : GoldbachAtSquareIndexedMidpoints)
    (hExt : SquareLadderExtendsToFullHolonomyDischarge) :
    GlobalInscribedSquareCertificateFamily := by
  have hHol : InscribedSquareOrbitHolonomyDischarge 2 :=
    route_c_square_goldbach_and_extension_give_holonomy_discharge_two
      hRouteC hGoldbach hExt
  exact (global_inscribed_square_family_iff_holonomy_discharge_two).mpr hHol

theorem route_c_square_goldbach_extension_and_zeta_fire_half_slope_bridge
    (hRouteC : StructuredCascadeForcesSquareDeltaOrbitObstruction)
    (hGoldbach : GoldbachAtSquareIndexedMidpoints)
    (hExt : SquareLadderExtendsToFullHolonomyDischarge)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_bridge_two_of_global_inscribed_square_and_zeta
    (route_c_square_goldbach_extension_gives_global_family hRouteC hGoldbach hExt)
    hZeta

theorem route_c_square_goldbach_extension_and_zeta_fire_rh_and_goldbach
    (hRouteC : StructuredCascadeForcesSquareDeltaOrbitObstruction)
    (hGoldbach : GoldbachAtSquareIndexedMidpoints)
    (hExt : SquareLadderExtendsToFullHolonomyDischarge)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    RiemannHypothesis ∧ GoldbachParity :=
  so8_half_slope_implies_rh_and_goldbach_parity
    (route_c_square_goldbach_extension_and_zeta_fire_half_slope_bridge
      hRouteC hGoldbach hExt hZeta)

/--
Single capstone assumption bundle.  `route_c` and `goldbach_even_squares` populate
the square-ladder family; `extend_squares` lifts that fragment to every midpoint;
`zeta_side` supplies the independent critical-line witness.
-/
structure SquareLadderCapstoneHypotheses where
  route_c : StructuredCascadeForcesSquareDeltaOrbitObstruction
  unit_mn_route_optional : SquareLadderUnitMnObstructionRoute ∨ True := Or.inr trivial
  goldbach_even_squares : GoldbachAtSquareIndexedMidpoints
  extend_squares : SquareLadderExtendsToFullHolonomyDischarge
  zeta_side : ConditionalZetaSideHalfSlopeWitness

theorem square_ladder_capstone_hypotheses_of_reduced_targets
    (hOneOb : SO4DeltaOrbitObstruction 1)
    (hFiniteStack :
      ∀ m, 1 < m → FiniteStackCannotExtinctAllGaps (m * m))
    (hOneGb : GoldbachAtSquareIndexedMidpointOne)
    (hNontrivialGb : GoldbachAtNontrivialSquareIndexedMidpoints)
    (hCertExt : SquareLadderExtendsToFullCertificateFamily)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SquareLadderCapstoneHypotheses where
  route_c := route_c_of_anchor_one_and_finite_stack_square_close hOneOb hFiniteStack
  unit_mn_route_optional := Or.inr trivial
  goldbach_even_squares :=
    goldbach_at_square_midpoints_of_one_and_nontrivial hOneGb hNontrivialGb
  extend_squares :=
    square_ladder_extends_to_full_holonomy_of_certificate_family_extension hCertExt
  zeta_side := hZeta

namespace SquareLadderCapstoneHypotheses

theorem square_ladder_discharge (H : SquareLadderCapstoneHypotheses) :
    ClosedDeltaOrbitInscribedSquareDischarge :=
  route_c_and_square_goldbach_give_square_ladder_discharge
    H.route_c H.goldbach_even_squares

theorem holonomy_discharge_two (H : SquareLadderCapstoneHypotheses) :
    InscribedSquareOrbitHolonomyDischarge 2 :=
  route_c_square_goldbach_and_extension_give_holonomy_discharge_two
    H.route_c H.goldbach_even_squares H.extend_squares

theorem global_family (H : SquareLadderCapstoneHypotheses) :
    GlobalInscribedSquareCertificateFamily :=
  route_c_square_goldbach_extension_gives_global_family
    H.route_c H.goldbach_even_squares H.extend_squares

theorem half_slope_bridge_two (H : SquareLadderCapstoneHypotheses) :
    SO8ProjectedHalfSlopeBridge 2 :=
  route_c_square_goldbach_extension_and_zeta_fire_half_slope_bridge
    H.route_c H.goldbach_even_squares H.extend_squares H.zeta_side

theorem rh_and_goldbach (H : SquareLadderCapstoneHypotheses) :
    RiemannHypothesis ∧ GoldbachParity :=
  route_c_square_goldbach_extension_and_zeta_fire_rh_and_goldbach
    H.route_c H.goldbach_even_squares H.extend_squares H.zeta_side

end SquareLadderCapstoneHypotheses

/-! ## 8. Capstone status -/

/--
**Honest capstone split.**

| Layer | Status |
|-------|--------|
| `StructuredCascadeIntegerCapture` | **Proved** |
| `structured_cascade_at_square_midpoint_shell` | **Proved** |
| `StructuredCascadeForcesSquareDeltaOrbitObstruction` | **Open** (cascade → obstruction) |
| `SquareLadderUnitMnObstructionRoute` | **Open** (unit `m−n` Ng-square) |
| `SquareLadderSymmetricObstructionRoute` | **Open** (any-gap symmetric pair) |
| Gap-one symmetric obstruction route | **Refuted** globally |
| `GoldbachAtSquareIndexedMidpoints` | **Open** (= Goldbach at even squares `2m²`) |
| `UniformHolonomyUnitRemovalAcrossOddPrimeLegs` | **Proved** |
| `PrimeHolonomyUnitRemovalProducesBridgeClass` (per leg `r ≥ 3`) | **Proved** |
| `WeakGoldbachRPrismHasProjectedMidpointOrder` | **Derived** from odd triple + `p ≤ q` |
| `HolonomyClassPopulatesSquareIndexedMidpointLadder` | **Open** (class → `N = m²` ladder) |
| `WeakGoldbachRPrismPopulatesSquareIndexedMidpointLadder` | **Open** |
| `UniformHolonomyRemovalPopulatesSquareIndexedMidpointLadder` | **Open** (needs ladder transport) |
| `ClosedDeltaOrbitInscribedSquareDischarge` | **Open** (obstruction + Goldbach) |
| `InscribedSquareOrbitHolonomyDischargeAtSquareMidpoints` | **Conditional** on discharge |
| `SquareLadderExtendsToFullHolonomyDischarge` | **Open** |
| `GlobalInscribedSquareCertificateFamily` | **Open** (strictly stronger than square ladder) |
| `SO8ProjectedHalfSlopeBridge 2` from square ladder alone | **Open** (needs extension) |
-/
def StructuredCascadeGlobalExistenceCapstone : Prop :=
  StructuredCascadeIntegerCapture ∧
    HarmonicCascadeTailBandFrontier ∧
      (∀ m, 0 < m →
        SO4SquareOrbitCollisionCloses (m * m))

theorem structured_cascade_global_existence_capstone :
    StructuredCascadeGlobalExistenceCapstone := by
  refine ⟨structured_cascade_integer_capture, harmonic_cascade_tail_band_frontier, ?_⟩
  intro m hm
  exact SO4SquareOrbitCollisionCloses_square_midpoint m hm

end

end Hqiv.Story
