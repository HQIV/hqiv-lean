import Hqiv.Story.S3InscribedSquareOrbitBridge
import Hqiv.Story.S3ExplicitFormulaDualitySlot
import Hqiv.Story.S3ZeroHolonomyGoldbachChain

/-!
# Shared orbit identity: inscribed-square route ↔ bridge midpoint carrier

This module makes explicit that the Goldbach inscribed-square orbit route and
the SO(8) half-slope bridge share the **same midpoint holonomy carrier**:

* `GoldbachMidpointPair` / `goldbachMidpointCount`
* `HopfFiberMidpointHolonomySupport`
* `SO4ZetaHolonomyForcesMidpointPairs`

The inscribed-square certificate is a **strict refinement**: it bundles the
shared holonomy payload together with Δ-orbit obstruction and square-orbit
collision closure.  It is **not** claimed equivalent to the bridge midpoint
field alone.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## 1. Shared holonomy carrier -/

/-- The certificate holonomy field is definitionally the bridge holonomy predicate. -/
theorem certificate_holonomy_is_bridge_carrier {N : ℕ}
    (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    HopfFiberMidpointHolonomySupport N cert.p cert.q :=
  cert.holonomy

theorem certificate_holonomy_agrees_with_pair_construction {N p q : ℕ} (hN : 0 < N)
    (hOb : SO4DeltaOrbitObstruction N) (hClose : SO4SquareOrbitCollisionCloses N)
    (hPair : GoldbachMidpointPair N p q) :
    (closed_delta_orbit_inscribed_square_certificate_of_pair hN hOb hClose hPair).holonomy =
      hopf_fiber_midpoint_holonomy_support_of_midpoint_pair hN hPair :=
  rfl

theorem certificate_midpoint_count_is_bridge_field {N : ℕ}
    (cert : ClosedDeltaOrbitInscribedSquareCertificate N) :
    0 < goldbachMidpointCount N :=
  ClosedDeltaOrbitInscribedSquareCertificate.midpoint_count_pos cert

theorem certificate_discharges_bridge_midpoint_at {N₀ N : ℕ}
    (hFam : InscribedSquareCertificateFamily N₀) (hN : N₀ ≤ N) :
    0 < goldbachMidpointCount N := by
  rcases hFam N hN with ⟨cert, _⟩
  exact certificate_midpoint_count_is_bridge_field cert

/-- At a nontrivial zero, every certified pair is the same holonomy object used in
the zero–holonomy–Goldbach chain. -/
theorem zero_contains_inscribed_square_certificate_holonomy
    {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) {N : ℕ}
    (cert : ClosedDeltaOrbitInscribedSquareCertificate N)
    (hN : 0 < N) :
    HopfFiberMidpointHolonomySupport N cert.p cert.q ∧
      (((1 : ℂ) - (cert.p : ℂ) ^ (-ρ)) ≠ 0 ∧
        ((1 : ℂ) - (cert.q : ℂ) ^ (-ρ)) ≠ 0) :=
  ⟨cert.holonomy,
    (zero_contains_pair_holonomy hzz hN cert.midpoint_pair).1⟩

/-! ## 2. Certificate family ↔ holonomy discharge (internal identity) -/

theorem inscribed_square_holonomy_discharge_of_certificate_family {N₀ : ℕ}
    (hFam : InscribedSquareCertificateFamily N₀) :
    InscribedSquareOrbitHolonomyDischarge N₀ :=
  inscribed_square_certificate_family_forces_holonomy_discharge hFam

theorem inscribed_square_certificate_family_of_holonomy_discharge {N₀ : ℕ}
    (hHol : InscribedSquareOrbitHolonomyDischarge N₀) :
    InscribedSquareCertificateFamily N₀ := by
  intro N hN
  rcases hHol N hN with ⟨cert, _⟩
  exact ⟨cert, trivial⟩

theorem inscribed_square_certificate_family_iff_holonomy_discharge {N₀ : ℕ} :
    InscribedSquareCertificateFamily N₀ ↔
      InscribedSquareOrbitHolonomyDischarge N₀ :=
  ⟨inscribed_square_holonomy_discharge_of_certificate_family,
    inscribed_square_certificate_family_of_holonomy_discharge⟩

theorem global_inscribed_square_family_iff_holonomy_discharge_two :
    GlobalInscribedSquareCertificateFamily ↔
      InscribedSquareOrbitHolonomyDischarge 2 := by
  rw [global_inscribed_square_family_iff_threshold_two,
    inscribed_square_certificate_family_iff_holonomy_discharge]

/-! ## 3. Refinement into bridge midpoint field -/

/--
**Strict refinement.**  An inscribed-square certificate family implies the
bridge midpoint field, but the converse is not expected: orbit obstruction and
square closure are extra data not carried by positive midpoint count alone.
-/
theorem inscribed_square_family_refines_bridge_midpoint_field {N₀ : ℕ}
    (hFam : InscribedSquareCertificateFamily N₀) :
    SO4ZetaHolonomyForcesMidpointPairs N₀ :=
  inscribed_square_certificate_family_forces_midpoint_pairs hFam

theorem global_inscribed_square_family_refines_goldbach_parity
    (hGlobal : GlobalInscribedSquareCertificateFamily) :
    GoldbachParity :=
  global_inscribed_square_family_discharges_goldbach_channel hGlobal

theorem global_inscribed_square_family_refines_midpoint_goldbach
    (hGlobal : GlobalInscribedSquareCertificateFamily) :
    MidpointGoldbachEventually 2 :=
  midpoint_goldbach_of_so4_zeta_holonomy_bridge
    (global_inscribed_square_family_forces_midpoint_pairs hGlobal)

theorem global_inscribed_square_half_slope_discharge_refines_bridge
    (h : GlobalInscribedSquareHalfSlopeBridgeDischarge) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_bridge_two_of_global_discharge h

theorem global_inscribed_square_half_slope_discharge_refines_rh_and_goldbach
    (h : GlobalInscribedSquareHalfSlopeBridgeDischarge) :
    RiemannHypothesis ∧ GoldbachParity :=
  rh_and_goldbach_parity_of_global_inscribed_square_discharge h

/-! ## 4. Bridge carrier equivalences (re-export spine) -/

theorem bridge_midpoint_field_iff_midpoint_goldbach {N₀ : ℕ} :
    SO4ZetaHolonomyForcesMidpointPairs N₀ ↔ MidpointGoldbachEventually N₀ :=
  so4_zeta_holonomy_bridge_iff_midpoint_goldbach

theorem bridge_midpoint_field_at_two_iff_goldbach_parity :
    SO4ZetaHolonomyForcesMidpointPairs 2 ↔ GoldbachParity :=
  so4_zeta_holonomy_bridge_two_iff_goldbach_parity

theorem half_slope_bridge_at_two_iff_rh_and_goldbach :
    SO8ProjectedHalfSlopeBridge 2 ↔ (RiemannHypothesis ∧ GoldbachParity) :=
  so8_projected_half_slope_two_iff_rh_and_goldbach_parity

theorem global_inscribed_square_family_implies_goldbach_parity
    (hGlobal : GlobalInscribedSquareCertificateFamily) :
    GoldbachParity :=
  global_inscribed_square_family_refines_goldbach_parity hGlobal

/--
**Honesty:** Goldbach parity does not reconstruct the inscribed-square orbit
fields; only the shared bridge midpoint carrier is discharged in the
reverse direction of the capstone equivalence.
-/
theorem goldbach_parity_implies_bridge_midpoint_field (hG : GoldbachParity) :
    SO4ZetaHolonomyForcesMidpointPairs 2 :=
  (so4_zeta_holonomy_bridge_two_iff_goldbach_parity).mpr hG

theorem global_inscribed_square_half_slope_discharge_implies_bridge_at_two
    (h : GlobalInscribedSquareHalfSlopeBridgeDischarge) :
    SO8ProjectedHalfSlopeBridge 2 :=
  global_inscribed_square_half_slope_discharge_refines_bridge h

theorem bridge_at_two_implies_goldbach_parity (hBridge : SO8ProjectedHalfSlopeBridge 2) :
    GoldbachParity :=
  (so8_half_slope_implies_rh_and_goldbach_parity hBridge).2

/-!
## Status

* **Proved identity:** certificate family ↔ holonomy discharge; global family
  ↔ holonomy discharge at threshold `2`.
* **Proved refinement:** global family ⇒ bridge midpoint field ⇒ Goldbach parity;
  global half-slope discharge ⇒ `SO8ProjectedHalfSlopeBridge 2`.
* **Honesty:** no converse from bridge midpoint field to inscribed-square
  certificate family; orbit obstruction and square closure remain extra.
-/

end

end Hqiv.Story
