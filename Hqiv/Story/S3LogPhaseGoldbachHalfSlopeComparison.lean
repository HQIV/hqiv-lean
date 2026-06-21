import Hqiv.Story.S3LogPhaseEdge
import Hqiv.Story.S3MidpointConstructiveSpectralSlope
import Hqiv.Story.S3ZeroHolonomyGoldbachChain

/-!
# Half-slope log-edge comparison: additive phase cap ↔ multiplicative spectral weight

At a Goldbach midpoint pair `p + q = 2N` the library already proves:

* normalized slope `N/(p+q) = 1/2` (`so4_orthogonal_tangent_midpoint_slope_eq_half`);
* additive phase-speed cap `log(pq) ≤ 2 log N` with saturation at the diagonal
  (`pair_phase_speed_max`);
* on `Re s = 1/2`, joint pair weight `‖(pq)^{−s}‖² = 1/(pq)` capped below by
  `1/N²` (`midpoint_pair_joint_weight_bound`).

This module packages the **unconditional intersection**: saturation of the additive
phase-speed cap coincides with square-root joint weight hitting the AM–GM floor,
and the symmetric gap channel `gapSpectralChannel` equals the midpoint pair line
`p^{−s} · q^{−s}`.

**Honesty.** These are σ–t comparison lemmas at the shared half-slope geometry;
they do not couple σ to t at zeros without an identification hypothesis (see
`S3LogPhaseZetaCouplingFrontier`).
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Midpoint gap channel = pair product line -/

/-- Gap index for a Goldbach midpoint pair: `g = N − p`. -/
def goldbachMidpointGap (N p : ℕ) : ℕ :=
  N - p

theorem goldbach_midpoint_gap_arm_left {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    N - (N - p) = p := by
  obtain ⟨_, _, hpN, _, _⟩ := h
  omega

theorem goldbach_midpoint_gap_arm_right {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    N + (N - p) = q := by
  obtain ⟨_, _, _, _, hsum⟩ := h
  omega

@[simp] theorem goldbachMidpointGap_eq (N p : ℕ) : goldbachMidpointGap N p = N - p := rfl

theorem gapSpectralChannel_eq_midpoint_pair_lines
    {N p q : ℕ} (h : GoldbachMidpointPair N p q) (s : ℂ) :
    gapSpectralChannel N (goldbachMidpointGap N p) s =
      so4SpectralLine p s * so4SpectralLine q s := by
  unfold gapSpectralChannel goldbachMidpointGap
  rw [goldbach_midpoint_gap_arm_left h, goldbach_midpoint_gap_arm_right h]

/-! ## Phase-speed saturation ↔ diagonal pair -/

theorem midpoint_phase_speed_saturated_iff_diagonal
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q) :
    Real.log ((p * q : ℕ) : ℝ) = 2 * Real.log N ↔ p = N ∧ q = N :=
  (pair_phase_speed_max hN h).2

theorem midpoint_phase_speed_saturated_of_diagonal
    {N : ℕ} (hN : 0 < N) (hp : Nat.Prime N) :
    Real.log ((N * N : ℕ) : ℝ) = 2 * Real.log N := by
  have hPair : GoldbachMidpointPair N N N :=
    ⟨hp, hp, le_rfl, le_rfl, by omega⟩
  exact (midpoint_phase_speed_saturated_iff_diagonal hN hPair).mpr ⟨rfl, rfl⟩

/-! ## Saturation meets the spectral-weight floor on the critical line -/

theorem midpoint_saturation_on_line_sq_weight_eq
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q) {s : ℂ}
    (hs : s.re = (1 / 2 : ℝ))
    (hsat : Real.log ((p * q : ℕ) : ℝ) = 2 * Real.log N) :
    ‖so4SpectralLine (p * q) s‖ ^ 2 = ((N : ℝ) ^ 2)⁻¹ ∧
      p = N ∧ q = N := by
  obtain ⟨hpN, hqN⟩ := (midpoint_phase_speed_saturated_iff_diagonal hN h).mp hsat
  have hp2 := h.1.two_le
  have hpq2 : 2 ≤ p * q := le_trans hp2 (Nat.le_mul_of_pos_right p h.2.1.pos)
  have hw : ‖so4SpectralLine (p * q) s‖ ^ 2 = ((p * q : ℕ) : ℝ)⁻¹ :=
    (so4SpectralLine_sq_weight hpq2).mpr hs
  exact And.intro (by
    rw [hw, show (p * q : ℕ) = N ^ 2 by rw [hpN, hqN, Nat.pow_two]]
    push_cast
    ring) ⟨hpN, hqN⟩

/-- On the line, phase-speed saturation forces the joint pair weight to equal the
AM–GM floor `1/N²`. -/
theorem midpoint_saturation_on_line_hits_weight_floor
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q) {s : ℂ}
    (hs : s.re = (1 / 2 : ℝ))
    (hsat : Real.log ((p * q : ℕ) : ℝ) = 2 * Real.log N) :
    ‖gapSpectralChannel N (goldbachMidpointGap N p) s‖ ^ 2 = ((N : ℝ) ^ 2)⁻¹ := by
  calc
    ‖gapSpectralChannel N (goldbachMidpointGap N p) s‖ ^ 2
        = ‖so4SpectralLine p s * so4SpectralLine q s‖ ^ 2 := by
      rw [← gapSpectralChannel_eq_midpoint_pair_lines h]
    _ = ‖so4SpectralLine (p * q) s‖ ^ 2 := by
      rw [(so4SpectralLine_mul p q s).symm]
    _ = ((N : ℝ) ^ 2)⁻¹ :=
      (midpoint_saturation_on_line_sq_weight_eq hN h hs hsat).1

/-! ## Half-slope packaging -/

/--
**Half-slope spectral–additive package** at a Goldbach midpoint pair: slope
`1/2`, phase-speed cap, and on the critical line the joint spectral identity.
-/
structure HalfSlopeLogPhaseSpectralPackage (N p q : ℕ) where
  hN : 0 < N
  pair : GoldbachMidpointPair N p q
  slope_half : SO4OrthogonalTangentMidpointSlope N p q = (1 / 2 : ℝ)
  phase_speed_le : Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log N
  gap_eq_pair :
    ∀ s : ℂ,
      gapSpectralChannel N (goldbachMidpointGap N p) s =
        so4SpectralLine p s * so4SpectralLine q s

theorem halfSlope_log_phase_spectral_package_of_midpoint_pair
    {N p q : ℕ} (hN : 0 < N) (h : GoldbachMidpointPair N p q) :
    HalfSlopeLogPhaseSpectralPackage N p q :=
  { hN := hN
    pair := h
    slope_half := so4_orthogonal_tangent_midpoint_slope_eq_half hN h
    phase_speed_le := (pair_phase_speed_max hN h).1
    gap_eq_pair := fun s => gapSpectralChannel_eq_midpoint_pair_lines h s }

theorem halfSlope_package_saturation_iff_diagonal
    {N p q : ℕ} (P : HalfSlopeLogPhaseSpectralPackage N p q) :
    Real.log ((p * q : ℕ) : ℝ) = 2 * Real.log N ↔ p = N ∧ q = N :=
  midpoint_phase_speed_saturated_iff_diagonal P.hN P.pair

theorem halfSlope_package_on_line_weight_floor
    {N p q : ℕ} (P : HalfSlopeLogPhaseSpectralPackage N p q) {s : ℂ}
    (hs : s.re = (1 / 2 : ℝ))
    (hsat : Real.log ((p * q : ℕ) : ℝ) = 2 * Real.log N) :
    ‖gapSpectralChannel N (goldbachMidpointGap N p) s‖ ^ 2 = ((N : ℝ) ^ 2)⁻¹ :=
  midpoint_saturation_on_line_hits_weight_floor P.hN P.pair hs hsat

end

end Hqiv.Story
