import Hqiv.Story.S3PolarProjectionCollapse
import Hqiv.Story.S3ExplicitFormulaDualitySlot

/-!
# Zero–holonomy–Goldbach chain: every zero activates every pair

This module formalizes: *since all zeros are comprised of all primes, they
contain holonomy — chained through the Goldbach parity bridge.*

## The chain, link by link (all proved)

1. **Every zero activates every Goldbach pair.**  Collectivity
   (`euler_factor_base_ne_zero_right_half`) means both prime lines of any
   midpoint pair `p + q = 2N` are nonvanishing participants in the
   cancellation at any nontrivial zero (`zero_activates_pair`), and the
   joint line factors multiplicatively through the pair
   (`so4SpectralLine_mul`).

2. **The additive midpoint bounds the multiplicative weight.**  AM–GM for a
   midpoint pair gives `p·q ≤ N²` (`midpoint_pair_product_le`), so on the
   critical line the joint pair weight obeys
   `‖(pq)^{−s}‖² = 1/(pq) ≥ 1/N²`
   (`midpoint_pair_joint_weight_bound`): the additive half-slope datum `N`
   caps the multiplicative spectral weight of its pairs.

3. **Every pair carries holonomy support.**  Each midpoint pair lifts to an
   integrable Hopf shell whose T11 torsion supplies the
   `SO8AdmissibleHolonomy` Δ/G₂/triality fields
   (`hopf_fiber_midpoint_holonomy_support_of_midpoint_pair`, proved in
   `GoldbachG2Parity`).  The capstone `zero_contains_pair_holonomy`
   packages: at any nontrivial zero, any midpoint pair has both prime lines
   active, multiplicative factorization, slope `1/2`, and the Hopf holonomy
   certificate — *every zero contains the holonomy of every pair*.

4. **Chained through the parity bridge.**  Under `GoldbachParity`, every
   midpoint `N ≥ 2` admits a holonomy-supported pair
   (`parity_gives_holonomy_support`).  And the SO(8) half-slope bridge
   rewrites into pure geometric-channel language:
   * `bridge_iff_spectral_weights_and_parity`:
     bridge `⟺` (square-root spectral weights at every zero) `∧` parity;
   * `bridge_iff_polar_collapse_and_parity`:
     bridge `⟺` (single-point polar projection at every zero) `∧` parity.

## Honest scope

Links 1–3 are unconditional: activation, the AM–GM weight cap, slope, and
holonomy support hold at every zero for every pair, *regardless of RH*.
What the chain does **not** do is discharge either side of the bridge: the
bridge remains exactly RH `∧` Goldbach (zero slack), now expressed with the
zeta side as a polar/spectral collapse statement and the prime side as
holonomy-supported midpoint pairs.
-/

namespace Hqiv.Story

open Complex Hqiv.Geometry

noncomputable section

/-! ## 1. Every zero activates every pair -/

/-- **Activation.**  At any nontrivial zero, both prime lines of any prime
pair are nonvanishing participants in the collective cancellation. -/
theorem zero_activates_pair {ρ : ℂ} (h : IsNontrivialZetaZero ρ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ((1 : ℂ) - (p : ℂ) ^ (-ρ)) ≠ 0 ∧ ((1 : ℂ) - (q : ℂ) ^ (-ρ)) ≠ 0 := by
  have h0 : 0 < ρ.re := (nontrivial_zero_open_strip ρ h).1
  exact ⟨euler_factor_base_ne_zero_right_half h0 ⟨p, hp⟩,
    euler_factor_base_ne_zero_right_half h0 ⟨q, hq⟩⟩

/-! ## 2. The additive midpoint caps the multiplicative weight -/

/-- AM–GM for midpoint pairs: `p ≤ N ≤ q` with `p + q = 2N` gives
`p·q ≤ N²`. -/
theorem midpoint_pair_product_le {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) : p * q ≤ N ^ 2 := by
  obtain ⟨_, _, hpN, hNq, hsum⟩ := h
  nlinarith

/-- **Joint pair weight on the critical line**: the pair line factors
multiplicatively, carries exactly weight `1/(pq)`, and the additive midpoint
caps it from below by `1/N²`. -/
theorem midpoint_pair_joint_weight_bound {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) :
    so4SpectralLine (p * q) s = so4SpectralLine p s * so4SpectralLine q s ∧
      ‖so4SpectralLine (p * q) s‖ ^ 2 = ((p * q : ℕ) : ℝ)⁻¹ ∧
      ((N : ℝ) ^ 2)⁻¹ ≤ ‖so4SpectralLine (p * q) s‖ ^ 2 := by
  have hp2 := h.1.two_le
  have hq2 := h.2.1.two_le
  have hpq2 : 2 ≤ p * q := le_trans hp2 (Nat.le_mul_of_pos_right p h.2.1.pos)
  have hw : ‖so4SpectralLine (p * q) s‖ ^ 2 = ((p * q : ℕ) : ℝ)⁻¹ :=
    (so4SpectralLine_sq_weight hpq2).mpr hs
  refine ⟨so4SpectralLine_mul p q s, hw, ?_⟩
  rw [hw]
  have hle : ((p * q : ℕ) : ℝ) ≤ ((N : ℝ)) ^ 2 := by
    exact_mod_cast midpoint_pair_product_le h
  have hpqpos : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by
    have := h.1.pos
    have := h.2.1.pos
    positivity
  gcongr

/-! ## 3. Every zero contains the holonomy of every pair -/

/--
**Capstone chain.**  At any nontrivial zero `ρ` and for any midpoint pair
`p + q = 2N`: both prime lines are active in the cancellation at `ρ`; the
joint line factors through the pair; the SO(4) midpoint slope is `1/2`; and
the pair carries a Hopf-fiber holonomy support certificate (integrable shell
with `SO8AdmissibleHolonomy` Δ/G₂/triality fields).  Every zero contains the
holonomy of every Goldbach pair — unconditionally.
-/
theorem zero_contains_pair_holonomy {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ)
    {N p q : ℕ} (hN : 0 < N) (hPair : GoldbachMidpointPair N p q) :
    (((1 : ℂ) - (p : ℂ) ^ (-ρ)) ≠ 0 ∧ ((1 : ℂ) - (q : ℂ) ^ (-ρ)) ≠ 0) ∧
      so4SpectralLine (p * q) ρ = so4SpectralLine p ρ * so4SpectralLine q ρ ∧
      SO4OrthogonalTangentMidpointSlope N p q = (1 / 2 : ℝ) ∧
      HopfFiberMidpointHolonomySupport N p q :=
  ⟨zero_activates_pair hzz hPair.1 hPair.2.1,
    so4SpectralLine_mul p q ρ,
    so4_orthogonal_tangent_midpoint_slope_eq_half hN hPair,
    hopf_fiber_midpoint_holonomy_support_of_midpoint_pair hN hPair⟩

/-! ## 4. Chained through the parity bridge -/

/-- Under `GoldbachParity`, every midpoint `N ≥ 2` admits a
holonomy-supported midpoint pair. -/
theorem parity_gives_holonomy_support (hG : GoldbachParity)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ p q : ℕ, HopfFiberMidpointHolonomySupport N p q := by
  obtain ⟨p, q, hp, hq, hsum⟩ := hG (2 * N) (by omega) ⟨N, by omega⟩
  rcases le_total p q with hle | hle
  · have hPair : GoldbachMidpointPair N p q :=
      ⟨hp, hq, by omega, by omega, hsum⟩
    exact ⟨p, q,
      hopf_fiber_midpoint_holonomy_support_of_midpoint_pair (by omega) hPair⟩
  · have hPair : GoldbachMidpointPair N q p :=
      ⟨hq, hp, by omega, by omega, by omega⟩
    exact ⟨q, p,
      hopf_fiber_midpoint_holonomy_support_of_midpoint_pair (by omega) hPair⟩

/-- **The parity bridge in spectral language**: the SO(8) half-slope bridge
holds iff every zero carries square-root spectral weights *and* Goldbach
parity holds. -/
theorem bridge_iff_spectral_weights_and_parity :
    SO8ProjectedHalfSlopeBridge 2 ↔
      ((∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ n : ℕ, 2 ≤ n →
          ‖so4SpectralLine n ρ‖ ^ 2 = (n : ℝ)⁻¹) ∧ GoldbachParity) := by
  rw [so8_projected_half_slope_two_iff_rh_and_goldbach_parity,
    RH_iff_zero_spectral_weights]

/-- **The parity bridge in polar language**: the SO(8) half-slope bridge
holds iff every zero's polar pair projects to a single point *and* Goldbach
parity holds. -/
theorem bridge_iff_polar_collapse_and_parity :
    SO8ProjectedHalfSlopeBridge 2 ↔
      (PolarProjectionCollapsesOnZeros ∧ GoldbachParity) := by
  rw [so8_projected_half_slope_two_iff_rh_and_goldbach_parity,
    ← polar_collapse_iff_RH]

end

end Hqiv.Story
