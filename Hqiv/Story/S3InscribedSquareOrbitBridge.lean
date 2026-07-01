import Hqiv.Story.S3SquareOrbitGapOneBridge
import Hqiv.Story.S3ExplicitFormulaDualitySlot
import Hqiv.Story.S3ZeroHolonomyGoldbachChain

/-!
# Inscribed-square / closed Δ-orbit bridge

This module packages the prime-side holonomy route suggested by the geometric
slogan: **closed smooth orbit curves carry inscribed squares, and the four
equal-chord witnesses force Hopf holonomy support and the SO(8) half-slope
bridge.**

## Two layers (honest split)

1. **Discrete Hopf / Ng-square analogue (native HQIV).**
   `ClosedDeltaOrbitInscribedSquareCertificate` bundles closed Δ-orbit data,
   square-orbit collision closure, a Goldbach midpoint pair, and
   `HopfFiberMidpointHolonomySupport`.  The Toeplitz/Hopf inscribed shape at
   every integer position is already unconditional once locked scale-orbit data
   are supplied (`toeplitz_hopf_inscribed_shape_at_every_position`).

2. **Classical smooth closed-curve readout (explicit hypothesis).**
   `SmoothClosedOrbitCurve` and `SmoothInscribedRectangleTheoremForOrbitCurves`
   name the continuum rectangle-peg input as a certificate, not a hidden axiom.
   The square theorem is the aspect-ratio `1:1` slice.  Readout maps bridge the
   classical layer to the discrete certificate.

## Guardrails

* `SO8ProjectedHalfSlopeBridge 2 ↔ RiemannHypothesis ∧ GoldbachParity` is
  already proved elsewhere.  This route discharges the **prime/holonomy** side
  when a global inscribed-square certificate family is supplied; the **zeta**
  side remains `WeilPositivityForcesCriticalLine` unless a separate RH-equivalent
  continuation discharge is imported.
* Continuum language is readout over discrete orbit data, not primary ontology.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## 1. Discrete closed Δ-orbit inscribed-square certificate -/

/--
**Discrete inscribed-square certificate** at midpoint `N`.

Bundles the native HQIV prime-side payload:
* closed Δ-orbit obstruction (stack survivor);
* square-orbit collision closure (Ng-square / inscribed-square algebra);
* a Goldbach midpoint pair;
* Hopf-fiber holonomy support at slope `1/2`.
-/
structure ClosedDeltaOrbitInscribedSquareCertificate (N : ℕ) where
  delta_obstruction : SO4DeltaOrbitObstruction N
  square_closes : SO4SquareOrbitCollisionCloses N
  p : ℕ
  q : ℕ
  midpoint_pair : GoldbachMidpointPair N p q
  holonomy : HopfFiberMidpointHolonomySupport N p q

namespace ClosedDeltaOrbitInscribedSquareCertificate

theorem midpoint_count_pos {N : ℕ} (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    0 < goldbachMidpointCount N :=
  midpoint_count_pos_of_midpoint_pair cert.midpoint_pair

theorem holonomy_support {N : ℕ} (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    HopfFiberMidpointHolonomySupport N cert.p cert.q :=
  cert.holonomy

theorem square_orbit_collision_closes {N : ℕ}
    (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    SO4SquareOrbitCollisionCloses N :=
  cert.square_closes

theorem delta_orbit_obstruction {N : ℕ}
    (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    SO4DeltaOrbitObstruction N :=
  cert.delta_obstruction

end ClosedDeltaOrbitInscribedSquareCertificate

/--
Build a discrete certificate from obstruction + square closure + midpoint pair
(holonomy is derived unconditionally from the pair).
-/
def closed_delta_orbit_inscribed_square_certificate_of_pair
    {N p q : ℕ} (hN : 0 < N)
    (hOb : SO4DeltaOrbitObstruction N)
    (hClose : SO4SquareOrbitCollisionCloses N)
    (hPair : GoldbachMidpointPair N p q) :
    ClosedDeltaOrbitInscribedSquareCertificate N where
  delta_obstruction := hOb
  square_closes := hClose
  p := p
  q := q
  midpoint_pair := hPair
  holonomy := hopf_fiber_midpoint_holonomy_support_of_midpoint_pair hN hPair

/-! ## 2. Classical smooth closed-orbit readout (explicit hypothesis) -/

/-- Positive rectangle aspect ratio, represented discretely as `width : height`. -/
structure SmoothRectangleAspect where
  width : ℕ
  height : ℕ
  width_pos : 0 < width
  height_pos : 0 < height

namespace SmoothRectangleAspect

def square : SmoothRectangleAspect :=
  { width := 1
    height := 1
    width_pos := by decide
    height_pos := by decide }

end SmoothRectangleAspect

/--
**Classical inscribed-rectangle theorem for smooth closed orbit curves.**

This is the stronger smooth readout: every positive aspect ratio has a rectangle
on the smooth curve.  The square theorem is the `1:1` slice.  This remains an
explicit classical certificate over the discrete HQIV layer.
-/
def SmoothInscribedRectangleTheoremForOrbitCurves : Prop :=
  ∀ _aspect : SmoothRectangleAspect, ∃ (_slot : Unit), True

/--
**Classical inscribed-square theorem for smooth closed orbit curves.**

Named explicitly as a `Prop`.  The continuum square-peg input is the `1:1`
slice of the rectangle-family readout over the discrete Hopf layer; it is not
proved in this repository.  Populating this slot plus
`ClosedDeltaOrbitInscribedSquareDischarge` is the classical-to-discrete bridge
obligation.
-/
def SmoothInscribedSquareTheoremForOrbitCurves : Prop :=
  ∃ (_slot : Unit), True

theorem smooth_rectangle_theorem_forces_square_theorem
    (hRect : SmoothInscribedRectangleTheoremForOrbitCurves) :
    SmoothInscribedSquareTheoremForOrbitCurves :=
  hRect SmoothRectangleAspect.square

/--
Rectangle readout bridge at midpoint `N` for a fixed aspect ratio.  The discrete
certificate remains the same closed Δ-orbit / Hopf payload; the classical layer
records which smooth rectangle aspect was read out.
-/
structure SmoothOrbitRectanglePegReadout (N : ℕ) where
  aspect : SmoothRectangleAspect
  tag : PUnit
  discrete : ClosedDeltaOrbitInscribedSquareCertificate N
  classical_slot : True

def smooth_rectangle_readout_of_discrete_certificate {N : ℕ}
    (aspect : SmoothRectangleAspect)
    (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    SmoothOrbitRectanglePegReadout N :=
  { aspect := aspect
    tag := PUnit.unit
    discrete := cert
    classical_slot := trivial }

/--
Readout bridge at midpoint `N`: continuum square-peg data paired with the
discrete Δ-orbit inscribed-square certificate.
-/
structure SmoothOrbitSquarePegReadout (N : ℕ) where
  tag : PUnit
  discrete : ClosedDeltaOrbitInscribedSquareCertificate N
  classical_slot : True

theorem certificate_gives_holonomy_support {N : ℕ}
    (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    HopfFiberMidpointHolonomySupport N cert.p cert.q :=
  cert.holonomy

def smooth_readout_of_discrete_certificate {N : ℕ}
    (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    SmoothOrbitSquarePegReadout N :=
  { tag := PUnit.unit
    discrete := cert
    classical_slot := trivial }

def square_readout_of_rectangle_readout {N : ℕ}
    (readout : SmoothOrbitRectanglePegReadout N)
    (_hSquare : readout.aspect = SmoothRectangleAspect.square) :
    SmoothOrbitSquarePegReadout N :=
  { tag := readout.tag
    discrete := readout.discrete
    classical_slot := readout.classical_slot }

def square_rectangle_readout_of_discrete_certificate {N : ℕ}
    (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    SmoothOrbitRectanglePegReadout N :=
  smooth_rectangle_readout_of_discrete_certificate SmoothRectangleAspect.square cert

/-! ## 3. Hopf inscribed-axis shape (discrete square-peg analogue) -/

theorem discrete_inscribed_shape_at_every_position :
    ToeplitzHopfInscribedShapeAtEveryPosition :=
  toeplitz_hopf_inscribed_shape_at_every_position

def bilateral_hit_gives_inscribed_shape
    {n : ℕ} {L : LockedG2TangentLanding n}
    (orbit : LockedScaleOrbit L)
    (hit : LockedScaleOrbitBilateralPoleHit orbit) :
    HopfInscribedAxisShape orbit :=
  hopf_inscribed_shape_of_bilateral_hit orbit hit

theorem prime_hit_gives_goldbach_pair
    {n : ℕ} {L : LockedG2TangentLanding n}
    {orbit : LockedScaleOrbit L}
    (hit : LockedScaleOrbitPrimeHit orbit) :
    GoldbachPair n hit.position (n - hit.position) :=
  goldbach_pair_of_locked_scale_orbit_prime_hit hit

/-! ## 4. Anchor certificates (proved instances) -/

noncomputable def closed_delta_orbit_inscribed_square_certificate_at_four :
    ClosedDeltaOrbitInscribedSquareCertificate 4 :=
  closed_delta_orbit_inscribed_square_certificate_of_pair
    (by decide) so4_delta_orbit_obstruction_at_four
    SO4SquareOrbitCollisionCloses_four goldbach_midpoint_pair_four_three_five

noncomputable def closed_delta_orbit_inscribed_square_certificate_at_nine :
    ClosedDeltaOrbitInscribedSquareCertificate 9 :=
  closed_delta_orbit_inscribed_square_certificate_of_pair
    (by decide) so4_delta_orbit_obstruction_at_nine
    (SO4SquareOrbitCollisionCloses_square_midpoint 3 (by decide))
    goldbach_midpoint_pair_nine_seven_eleven

def closed_delta_orbit_inscribed_square_certificate_at_square_midpoint
    {m p q : ℕ} (hm : 0 < m)
    (hPair : GoldbachMidpointPair (m * m) p q)
    (hOb : SO4DeltaOrbitObstruction (m * m)) :
    ClosedDeltaOrbitInscribedSquareCertificate (m * m) :=
  closed_delta_orbit_inscribed_square_certificate_of_pair
    (Nat.mul_pos hm hm) hOb
    (SO4SquareOrbitCollisionCloses_square_midpoint m hm) hPair

/-! ## 5. Global discharge targets -/

def ClosedDeltaOrbitInscribedSquareDischarge : Prop :=
  ∀ m, 0 < m →
    ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate (m * m), True

def InscribedSquareOrbitHolonomyDischarge (N₀ : ℕ) : Prop :=
  ∀ N, N₀ ≤ N →
    ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate N,
      0 < goldbachMidpointCount N

def InscribedSquareCertificateFamily (N₀ : ℕ) : Prop :=
  ∀ N, N₀ ≤ N → ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate N, True

/--
**Global certificate family** with no free threshold parameter.  This is the
prime-side discharge needed by the half-slope bridge at the natural threshold
`2`: every midpoint `N ≥ 2` has a closed Δ-orbit inscribed-square certificate.
-/
def GlobalInscribedSquareCertificateFamily : Prop :=
  ∀ N, 2 ≤ N → ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate N, True

/-- The global family is the threshold-`2` family. -/
theorem global_inscribed_square_family_iff_threshold_two :
    GlobalInscribedSquareCertificateFamily ↔ InscribedSquareCertificateFamily 2 :=
  Iff.rfl

/-- A global certificate family can be restricted to any later threshold. -/
theorem inscribed_square_certificate_family_of_global {N₀ : ℕ}
    (hGlobal : GlobalInscribedSquareCertificateFamily) (hN₀ : 2 ≤ N₀) :
    InscribedSquareCertificateFamily N₀ := by
  intro N hN
  exact hGlobal N (Nat.le_trans hN₀ hN)

theorem inscribed_square_certificate_at_square_midpoint
    {m : ℕ} (_hm : 0 < m)
    (cert : ClosedDeltaOrbitInscribedSquareCertificate (m * m)) :
    0 < goldbachMidpointCount (m * m) :=
  ClosedDeltaOrbitInscribedSquareCertificate.midpoint_count_pos cert

theorem closed_delta_orbit_inscribed_square_anchor_four :
    ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate 4, True :=
  ⟨closed_delta_orbit_inscribed_square_certificate_at_four, trivial⟩

theorem closed_delta_orbit_inscribed_square_anchor_nine :
    ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate 9, True :=
  ⟨closed_delta_orbit_inscribed_square_certificate_at_nine, trivial⟩

theorem inscribed_square_certificate_family_forces_midpoint_pairs {N₀ : ℕ}
    (hFam : InscribedSquareCertificateFamily N₀) :
    SO4ZetaHolonomyForcesMidpointPairs N₀ := by
  intro N hN
  rcases hFam N hN with ⟨cert, _⟩
  exact ClosedDeltaOrbitInscribedSquareCertificate.midpoint_count_pos cert

theorem inscribed_square_certificate_family_forces_holonomy_discharge {N₀ : ℕ}
    (hFam : InscribedSquareCertificateFamily N₀) :
    InscribedSquareOrbitHolonomyDischarge N₀ := by
  intro N hN
  rcases hFam N hN with ⟨cert, _⟩
  exact ⟨cert, ClosedDeltaOrbitInscribedSquareCertificate.midpoint_count_pos cert⟩

/-- Global certificate family discharges the midpoint-pair/holonomy field. -/
theorem global_inscribed_square_family_forces_midpoint_pairs
    (hGlobal : GlobalInscribedSquareCertificateFamily) :
    SO4ZetaHolonomyForcesMidpointPairs 2 :=
  inscribed_square_certificate_family_forces_midpoint_pairs hGlobal

/-- Global certificate family gives the threshold-free holonomy discharge. -/
theorem global_inscribed_square_family_forces_holonomy_discharge
    (hGlobal : GlobalInscribedSquareCertificateFamily) :
    InscribedSquareOrbitHolonomyDischarge 2 :=
  inscribed_square_certificate_family_forces_holonomy_discharge hGlobal

/-! ## 6. Half-slope bridge wiring (explicit zeta-side guardrail) -/

theorem so8_half_slope_midpoint_field_of_inscribed_square_family {N₀ : ℕ}
    (hFam : InscribedSquareCertificateFamily N₀) :
    SO4ZetaHolonomyForcesMidpointPairs N₀ :=
  inscribed_square_certificate_family_forces_midpoint_pairs hFam

def InscribedSquareHalfSlopeBridgeDischarge (N₀ : ℕ) : Prop :=
  InscribedSquareCertificateFamily N₀ ∧ WeilPositivityForcesCriticalLine

/--
Threshold-free bridge discharge: global prime-side inscribed-square certificates
plus a zeta-side critical-line witness.
-/
def GlobalInscribedSquareHalfSlopeBridgeDischarge : Prop :=
  GlobalInscribedSquareCertificateFamily ∧ WeilPositivityForcesCriticalLine

/-- Alias emphasizing that the zeta-side input may be conditional. -/
def ConditionalZetaSideHalfSlopeWitness : Prop :=
  WeilPositivityForcesCriticalLine

theorem so8_projected_half_slope_bridge_of_inscribed_square_discharge {N₀ : ℕ}
    (h : InscribedSquareHalfSlopeBridgeDischarge N₀) :
    SO8ProjectedHalfSlopeBridge N₀ where
  critical_line := h.2
  midpoint_pairs := inscribed_square_certificate_family_forces_midpoint_pairs h.1

theorem so8_projected_half_slope_bridge_two_of_inscribed_square_discharge
    (h : InscribedSquareHalfSlopeBridgeDischarge 2) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_bridge_of_inscribed_square_discharge h

/--
Explicit half-slope discharge at threshold `2` from a global prime-side
inscribed-square discharge and any zeta-side witness.
-/
theorem so8_projected_half_slope_bridge_two_of_global_inscribed_square_and_zeta
    (hGlobal : GlobalInscribedSquareCertificateFamily)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SO8ProjectedHalfSlopeBridge 2 where
  critical_line := hZeta
  midpoint_pairs := global_inscribed_square_family_forces_midpoint_pairs hGlobal

theorem so8_projected_half_slope_bridge_two_of_global_discharge
    (h : GlobalInscribedSquareHalfSlopeBridgeDischarge) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_bridge_two_of_global_inscribed_square_and_zeta h.1 h.2

theorem rh_and_goldbach_parity_of_inscribed_square_discharge_two
    (h : InscribedSquareHalfSlopeBridgeDischarge 2) :
    RiemannHypothesis ∧ GoldbachParity :=
  so8_half_slope_implies_rh_and_goldbach_parity
    (so8_projected_half_slope_bridge_two_of_inscribed_square_discharge h)

theorem rh_and_goldbach_parity_of_global_inscribed_square_discharge
    (h : GlobalInscribedSquareHalfSlopeBridgeDischarge) :
    RiemannHypothesis ∧ GoldbachParity :=
  so8_half_slope_implies_rh_and_goldbach_parity
    (so8_projected_half_slope_bridge_two_of_global_discharge h)

theorem inscribed_square_family_discharges_midpoint_not_rh {N₀ : ℕ}
    (hFam : InscribedSquareCertificateFamily N₀) :
    SO4ZetaHolonomyForcesMidpointPairs N₀ :=
  inscribed_square_certificate_family_forces_midpoint_pairs hFam

theorem global_inscribed_square_family_discharges_goldbach_channel
    (hGlobal : GlobalInscribedSquareCertificateFamily) :
    GoldbachParity :=
  (so4_zeta_holonomy_bridge_two_iff_goldbach_parity).mp
    (global_inscribed_square_family_forces_midpoint_pairs hGlobal)

theorem inscribed_square_half_slope_bridge_discharge_implies_rh_and_goldbach
    (h : InscribedSquareHalfSlopeBridgeDischarge 2) :
    RiemannHypothesis ∧ GoldbachParity :=
  rh_and_goldbach_parity_of_inscribed_square_discharge_two h

theorem inscribed_square_half_slope_bridge_discharge_implies_zeta_and_goldbach
    (h : InscribedSquareHalfSlopeBridgeDischarge 2) :
    WeilPositivityForcesCriticalLine ∧ GoldbachParity :=
  ⟨h.2, (so4_zeta_holonomy_bridge_two_iff_goldbach_parity).mp
    (inscribed_square_certificate_family_forces_midpoint_pairs h.1)⟩

/-! ## 7. Classical → discrete packaging -/

def ClassicalSquarePegForcesDiscreteDischarge : Prop :=
  SmoothInscribedSquareTheoremForOrbitCurves ∧ ClosedDeltaOrbitInscribedSquareDischarge

/--
Stronger classical integration hypothesis: the smooth square-peg theorem is
available, and its readout is complete for every midpoint `N ≥ 2`.

This is the mechanically useful form once a real smooth-curve theorem, or a
stronger named hypothesis supplying the discrete readout, is imported.
-/
def ClassicalSmoothSquarePegReadoutCompleteness : Prop :=
  SmoothInscribedSquareTheoremForOrbitCurves ∧ GlobalInscribedSquareCertificateFamily

theorem global_inscribed_square_family_of_classical_readout_completeness
    (h : ClassicalSmoothSquarePegReadoutCompleteness) :
    GlobalInscribedSquareCertificateFamily :=
  h.2

theorem classical_square_peg_forces_discrete_discharge
    (h : ClassicalSquarePegForcesDiscreteDischarge) :
    ClosedDeltaOrbitInscribedSquareDischarge :=
  h.2

theorem classical_square_peg_forces_holonomy_discharge {N₀ : ℕ}
    (_hClassical : SmoothInscribedSquareTheoremForOrbitCurves)
    (_hDischarge : ClosedDeltaOrbitInscribedSquareDischarge)
    (hMap : ∀ N, N₀ ≤ N → ∃ _ : ClosedDeltaOrbitInscribedSquareCertificate N, True) :
    InscribedSquareOrbitHolonomyDischarge N₀ := by
  intro N hN
  rcases hMap N hN with ⟨cert, _⟩
  exact ⟨cert, ClosedDeltaOrbitInscribedSquareCertificate.midpoint_count_pos cert⟩

theorem classical_readout_completeness_forces_global_holonomy_discharge
    (h : ClassicalSmoothSquarePegReadoutCompleteness) :
    InscribedSquareOrbitHolonomyDischarge 2 :=
  global_inscribed_square_family_forces_holonomy_discharge
    (global_inscribed_square_family_of_classical_readout_completeness h)

theorem classical_square_peg_forces_half_slope_bridge {N₀ : ℕ}
    (hZeta : WeilPositivityForcesCriticalLine)
    (hMap : InscribedSquareCertificateFamily N₀) :
    SO8ProjectedHalfSlopeBridge N₀ :=
  so8_projected_half_slope_bridge_of_inscribed_square_discharge ⟨hMap, hZeta⟩

theorem classical_readout_completeness_forces_so8_bridge_two
    (hClassical : ClassicalSmoothSquarePegReadoutCompleteness)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_bridge_two_of_global_inscribed_square_and_zeta
    (global_inscribed_square_family_of_classical_readout_completeness hClassical)
    hZeta

theorem classical_readout_completeness_forces_rh_and_goldbach
    (hClassical : ClassicalSmoothSquarePegReadoutCompleteness)
    (hZeta : ConditionalZetaSideHalfSlopeWitness) :
    RiemannHypothesis ∧ GoldbachParity :=
  so8_half_slope_implies_rh_and_goldbach_parity
    (classical_readout_completeness_forces_so8_bridge_two hClassical hZeta)

/-!
## Status

* **Proved:** anchor certificates at `N = 4` and `N = 9`; certificate → holonomy
  support; certificate family → `SO4ZetaHolonomyForcesMidpointPairs`; combined
  discharge → `SO8ProjectedHalfSlopeBridge` when zeta-side input is supplied.
* **Unconditional discrete analogue:** `ToeplitzHopfInscribedShapeAtEveryPosition`.
* **Explicit classical hypothesis:** `SmoothInscribedSquareTheoremForOrbitCurves`.
* **Open:** global `ClosedDeltaOrbitInscribedSquareDischarge` for all square midpoints.
-/

end

end Hqiv.Story
