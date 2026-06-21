import Hqiv.Story.S3LogPhaseZetaCouplingFrontier
import Hqiv.Story.S3ZeroHolonomyGoldbachChain
import Hqiv.Geometry.GoldbachG2Parity

/-!
# Log–Goldbach coupling under `GoldbachParity`

The unconditional witness `N = p = q = 2` is minimal.  Under `GoldbachParity`
(even Goldbach in midpoint form) every midpoint `N ≥ 2` carries a full
`HalfSlopeLogPhaseSpectralPackage`, and every nontrivial zero admits coupling
witnesses tied to that additive data — without assuming RH.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Parity supplies half-slope packages at every midpoint -/

/--
Under `GoldbachParity`, every midpoint `N ≥ 2` admits a Goldbach midpoint pair
and the unconditional half-slope spectral–additive package.
-/
theorem parity_gives_half_slope_log_phase_package
    (hG : GoldbachParity) {N : ℕ} (hN : 2 ≤ N) :
    ∃ p q : ℕ, GoldbachMidpointPair N p q ∧
      HalfSlopeLogPhaseSpectralPackage N p q := by
  obtain ⟨p, q, hp, hq, hsum⟩ :=
    hG (2 * N) (by omega) ⟨N, by ring⟩
  rcases midpoint_pair_of_goldbach_pair_two_mul ⟨hp, hq, hsum⟩ with
    ⟨p', q', hPair⟩
  refine ⟨p', q', hPair, ?_⟩
  have hNpos : 0 < N := by omega
  exact halfSlope_log_phase_spectral_package_of_midpoint_pair hNpos hPair

theorem parity_gives_half_slope_package_at_even_goldbach
    (hG : GoldbachParity) {n : ℕ} (hn : 4 ≤ n) (heven : Even n) :
    ∃ N p q : ℕ, n = 2 * N ∧ GoldbachMidpointPair N p q ∧
      HalfSlopeLogPhaseSpectralPackage N p q := by
  obtain ⟨k, hk⟩ := heven
  have heven' : Even n := ⟨k, hk⟩
  have hk2 : 2 ≤ k := by
    rcases hk
    omega
  have hn2k : n = 2 * k := by simpa [Nat.two_mul] using hk
  obtain ⟨p, q, hp, hq, hsum⟩ := hG n (by omega) heven'
  rcases midpoint_pair_of_goldbach_pair_two_mul ⟨hp, hq, by simpa [hn2k] using hsum⟩ with
    ⟨p', q', hMid⟩
  refine ⟨k, p', q', hn2k, hMid, ?_⟩
  have hNpos : 0 < k := by omega
  exact halfSlope_log_phase_spectral_package_of_midpoint_pair hNpos hMid

/-! ## Coupling witnesses at every midpoint (additive side) -/

/--
At any nontrivial zero, `GoldbachParity` supplies a log–Goldbach coupling witness
using midpoint data at every `N ≥ 2` — not only the diagonal `2 + 2` shell.
-/
theorem log_phase_goldbach_coupling_witness_at_midpoint_under_parity
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) {N : ℕ}
    (hN : 2 ≤ N) :
    Nonempty (LogPhaseGoldbachCouplingWitness ρ) := by
  obtain ⟨p, q, hPair, P⟩ := parity_gives_half_slope_log_phase_package hG hN
  exact ⟨⟨h, N, p, q, hPair, P⟩⟩

theorem log_phase_goldbach_coupling_at_midpoint_under_parity
    (hG : GoldbachParity) {ρ : ℂ} (h : IsNontrivialZetaZero ρ) {N : ℕ}
    (hN : 2 ≤ N) :
    LogPhaseGoldbachZetaCouplingAt ρ :=
  log_phase_goldbach_coupling_witness_at_midpoint_under_parity hG h hN

/-! ## Certified small-midpoint packages (no parity hypothesis) -/

theorem half_slope_package_at_midpoint_four :
    HalfSlopeLogPhaseSpectralPackage 4 3 5 :=
  halfSlope_log_phase_spectral_package_of_midpoint_pair (by decide)
    goldbach_midpoint_pair_four_three_five

theorem half_slope_package_at_midpoint_six :
    HalfSlopeLogPhaseSpectralPackage 6 5 7 :=
  halfSlope_log_phase_spectral_package_of_midpoint_pair (by decide)
    goldbach_midpoint_pair_six_five_seven

theorem half_slope_package_at_midpoint_eight :
    HalfSlopeLogPhaseSpectralPackage 8 5 11 :=
  halfSlope_log_phase_spectral_package_of_midpoint_pair (by decide)
    goldbach_midpoint_pair_eight_five_eleven

theorem half_slope_package_at_midpoint_nine :
    HalfSlopeLogPhaseSpectralPackage 9 7 11 :=
  halfSlope_log_phase_spectral_package_of_midpoint_pair (by decide)
    goldbach_midpoint_pair_nine_seven_eleven

theorem half_slope_package_at_midpoint_ten :
    HalfSlopeLogPhaseSpectralPackage 10 3 17 :=
  halfSlope_log_phase_spectral_package_of_midpoint_pair (by decide)
    goldbach_midpoint_pair_ten_three_seventeen

theorem half_slope_package_at_midpoint_fifteen :
    HalfSlopeLogPhaseSpectralPackage 15 7 23 :=
  halfSlope_log_phase_spectral_package_of_midpoint_pair (by decide)
    goldbach_midpoint_pair_fifteen_seven_twentythree

/-! ## Additive half of the SO(8) bridge from parity alone -/

/--
**Additive bridge channel.** `GoldbachParity` alone fills the midpoint-pairs field of
`SO8ProjectedHalfSlopeBridge 2`; the zeta (`critical_line`) channel remains RH.
-/
theorem goldbach_parity_fills_midpoint_half_slope_bridge
    (hG : GoldbachParity) :
    SO4ZetaHolonomyForcesMidpointPairs 2 :=
  (so4_zeta_holonomy_bridge_two_iff_goldbach_parity.mpr hG)

theorem goldbach_parity_gives_holonomy_at_every_midpoint
    (hG : GoldbachParity) {N : ℕ} (hN : 2 ≤ N) :
    ∃ p q : ℕ, HopfFiberMidpointHolonomySupport N p q :=
  parity_gives_holonomy_support hG hN

end

end Hqiv.Story
