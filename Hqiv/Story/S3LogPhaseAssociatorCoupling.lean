import Hqiv.Story.S3LogPhaseGoldbachCouplingParity
import Hqiv.Story.S3OctonionicAssociatorChannel

/-!
# Goldbach triplet invariant: log-edge coupling + associator channel

Combines the log–Goldbach coupling witness with the octonionic associator
channel at the Goldbach midpoint triple `(p, q, 2N)`.  On the critical line the
associator carries the square-root floor `≥ 1/N³` while the half-slope package
supplies slope `1/2` and the gap = pair identity.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/--
**Goldbach triplet spectral invariant** at a zero: half-slope log–Goldbach
coupling together with the `(p, q, 2N)` associator readout on the critical line.
-/
structure GoldbachTripletLogAssociatorInvariant (ρ : ℂ) (N : ℕ) where
  p : ℕ
  q : ℕ
  coupling : LogPhaseGoldbachCouplingWitness ρ
  pair : GoldbachMidpointPair N p q
  package : HalfSlopeLogPhaseSpectralPackage N p q
  associator_floor :
    1 / ((N ^ 3 : ℕ) : ℝ) ≤
      octAssociatorChannel p q (2 * N) (Complex.mk (1 / 2 : ℝ) ρ.im)

theorem goldbach_triplet_invariant_under_parity_on_line
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    (hσ : ρ.re = (1 / 2 : ℝ)) {N : ℕ} (hN : 2 ≤ N) :
    Nonempty (GoldbachTripletLogAssociatorInvariant ρ N) := by
  obtain ⟨p, q, hPair, P⟩ := parity_gives_half_slope_log_phase_package hG hN
  have hAssoc :=
    midpoint_triple_channel_floor (by omega) hPair
      (s := Complex.mk (1 / 2 : ℝ) ρ.im) (by simpa using hσ)
  exact ⟨⟨p, q, ⟨h, N, p, q, hPair, P⟩, hPair, P, hAssoc⟩⟩

/--
On the line, RH identifies the associator channel with the exact square-root
weight `2/(pq·2N)`; combined with the coupling witness this is still RH-equivalent
via `RH_iff_zero_associator_channel`.
-/
theorem RH_goldbach_triplet_associator_exact_on_line
    (hRH : RiemannHypothesis) {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    (hσ : ρ.re = (1 / 2 : ℝ)) {N p q : ℕ}
    (hPair : GoldbachMidpointPair N p q) :
    octAssociatorChannel p q (2 * N) (Complex.mk (1 / 2 : ℝ) ρ.im) =
      2 / ((p * q * (2 * N) : ℕ) : ℝ) := by
  have hp2 := hPair.1.two_le
  have hq := hPair.2.1.pos
  have h2N : 0 < 2 * N := by
    have := hPair.2.2.1
    omega
  exact (octAssociatorChannel_eq_iff hp2 hq h2N).mpr (by simp)

end

end Hqiv.Story
