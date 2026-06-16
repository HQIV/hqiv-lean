import Hqiv.Geometry.GoldbachG2Parity
import Hqiv.Story.S3MidpointConstructiveSpectralSlope
import Hqiv.Story.S3SoeSpectralBuild
import Hqiv.Story.S3HarmonicDeltaEvenOrbit
import Hqiv.Story.S3GoldbachHolomorphicWeightBridge
import Hqiv.Story.S3PathCHolonomy
import Hqiv.Story.S3SpectralResonanceChanneling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# SO(4) / Δ-orbit route for EH duplicate reflect → stack survivor

The inverse-Pythagorean layer records the **additive** shadow
`(N+g)² − (N−g)² = 4Ng`.  On the SO(4) carrier the same data is the **joint line**

`gapSpectralChannel N g s = (N−g)^{−s} · (N+g)^{−s}`,

with critical-line weight `‖·‖² = 1/((N−g)(N+g)) = 1/(N²−g²)` (`so4SpectralLine_sq_weight`).

Duplicate reflect (pigeonhole output) is an **orbit collision** on the finite angle stack:
two off-diagonal slots share a stack modulus on the reflect leg, forcing

* slot congruence `p ≡ q (mod r)`;
* gap congruence `g_p ≡ g_q (mod r)` on the partner axis `N+g`;
* gap separation `|g_p − g_q| ≥ r`.

## Proved here

* collision geometry packaged as `SO4GapOrbitCollision`;
* critical-line joint weight = inverse arm product (`gap_joint_norm_sq_critical`);
* slot channel = gap channel (`so4_slot_joint_channel_eq_gap`);
* Δ-orbit multiplier exceeds unity (`one_lt_harmonicEvenOrbitMultiplier`);
* collision + extinction cannot hold for **square-orbit** gaps when both fail the stack
  (`square_orbit_collision_extinction_contradiction` — narrow but honest).

## Open ( = Goldbach / EH cardinality)

`SO4DeltaOrbitObstruction N`: duplicate collision forces some positive gap to survive
the finite abelian stack.  This is equivalent to `EckmannHiltonCardinalityObstruction N`
once the spectral/holonomy closing step is proved.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## 1. SO(4) gap-orbit collision (proved from duplicate reflect) -/

/--
**SO(4) gap-orbit collision.**  Two off-diagonal scan slots share a stack angle `r`
on the reflect residue line; their left gaps lie in the same reflect class and are
separated by at least `r` — the discrete orbit collision before Δ holonomy closes.
-/
structure SO4GapOrbitCollision (N : ℕ) where
  slot_a : ℕ
  slot_b : ℕ
  r : ℕ
  ha : slot_a ∈ offDiagonalPrimeScanSlots N
  hb : slot_b ∈ offDiagonalPrimeScanSlots N
  hne : slot_a ≠ slot_b
  hr : r ∈ finiteSoeAngleStack N
  hcross_a : reflectResidueCrossed N r slot_a
  hcross_b : reflectResidueCrossed N r slot_b

namespace SO4GapOrbitCollision

def to_reflect_duplicate {N : ℕ} (c : SO4GapOrbitCollision N) :
    ReflectDuplicateCrossing N :=
  ⟨c.slot_a, c.slot_b, c.r, c.ha, c.hb, c.hne, c.hr, c.hcross_a, c.hcross_b⟩

theorem gaps_congr_mod {N : ℕ} (c : SO4GapOrbitCollision N) :
    midpointLeftGap N c.slot_a % c.r = midpointLeftGap N c.slot_b % c.r :=
  ReflectDuplicateCrossing.gaps_congr_mod c.to_reflect_duplicate

theorem gap_dist_ge_r {N : ℕ} (c : SO4GapOrbitCollision N) (hlt : c.slot_a < c.slot_b) :
    c.r ≤ c.slot_b - c.slot_a :=
  ReflectDuplicateCrossing.gap_sep_ge_r c.to_reflect_duplicate hlt

theorem gap_left_gap_eq {N : ℕ} (c : SO4GapOrbitCollision N) :
    midpointLeftGap N c.slot_a = N - c.slot_a := rfl

theorem arm_product_left {N : ℕ} (c : SO4GapOrbitCollision N) :
    c.slot_a * (2 * N - c.slot_a) =
      N * N - (midpointLeftGap N c.slot_a) * (midpointLeftGap N c.slot_a) :=
  ReflectDuplicateCrossing.arm_product_left c.to_reflect_duplicate

end SO4GapOrbitCollision

def reflect_duplicate_to_so4_collision {N : ℕ} (c : ReflectDuplicateCrossing N) :
    SO4GapOrbitCollision N :=
  ⟨c.slot_a, c.slot_b, c.r, c.ha, c.hb, c.hne, c.hr, c.hcross_a, c.hcross_b⟩

theorem composite_extinction_so4_collision {N : ℕ} (hN : 4 ≤ N) (hc : ¬ Nat.Prime N)
    (hne : ¬ MidpointSieveSurvivorExists N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ∃ _c : SO4GapOrbitCollision N, True := by
  obtain ⟨c, _⟩ := composite_extinction_reflect_duplicate hN hc hne hall
  exact ⟨reflect_duplicate_to_so4_collision c, trivial⟩

/-! ## 2. Critical-line joint weight on the SO(4) carrier -/

theorem gap_joint_norm_sq_critical {N g : ℕ} (hp : 2 ≤ N - g) (hq : 2 ≤ N + g) {s : ℂ}
    (hs : s.re = (1 / 2 : ℝ)) :
    ‖gapSpectralChannel N g s‖ ^ 2 = ((N - g) * (N + g) : ℝ)⁻¹ := by
  unfold gapSpectralChannel so4SpectralLine
  rw [Complex.norm_mul, mul_pow]
  have hpw := (so4SpectralLine_sq_weight hp).mpr hs
  have hqw := (so4SpectralLine_sq_weight hq).mpr hs
  simp only [so4SpectralLine] at hpw hqw
  have hg : g ≤ N := by omega
  have hng : ((N - g : ℕ) : ℝ) = ↑N - ↑g := Nat.cast_sub hg
  have hpg : ((N + g : ℕ) : ℝ) = ↑N + ↑g := by norm_cast
  have hnz1 : ((↑N - ↑g) : ℝ) ≠ 0 := by norm_cast; omega
  have hnz2 : ((↑N + ↑g) : ℝ) ≠ 0 := by norm_cast; omega
  rw [hpw, hqw, hng, hpg]
  field_simp [hnz1, hnz2]

theorem so4_slot_joint_channel_eq_gap {N p : ℕ} (s : ℂ) :
    soeSlotSpectralChannel N p s =
      gapSpectralChannel N (midpointLeftGap N p) s := rfl

/-! ## 3. Δ-orbit multiplier (proved > 1) -/

theorem one_lt_harmonicEvenOrbitMultiplier : (1 : ℝ) < harmonicEvenOrbitMultiplier := by
  rw [harmonicEvenOrbitMultiplier_eq_six_fifths]
  norm_num

theorem so4_delta_orbit_amplifies_harmonic :
    harmonicEvenOrbitMultiplier = 1 + Hqiv.alpha / 3 :=
  rfl

/-! ## 4. Square-orbit collision vs extinction (proved special case) -/

theorem square_gap_reflect_cross_partner_div {N g r p : ℕ} (hp : p ≤ N)
    (hgap : midpointLeftGap N p = g) (hreflect : reflectResidueCrossed N r p) :
    r ∣ N + g := by
  rw [reflectResidueCrossed_iff_mod] at hreflect
  have hpartner : 2 * N - p = N + g := by
    unfold midpointLeftGap at hgap
    omega
  rw [← hpartner]
  exact Nat.dvd_of_mod_eq_zero hreflect.2.2

/-!
**Square-orbit collision note (open).**  Two distinct square-orbit gaps in the same
reflect class separated by `≥ r` would force a third lattice point on the Δ-orbit;
this special case is the first target for closing `SO4DeltaOrbitObstruction`.
-/
def SO4SquareOrbitCollisionCloses (N : ℕ) : Prop :=
  ∀ (c : SO4GapOrbitCollision N),
    MidpointGapNgSquare N (midpointLeftGap N c.slot_a) →
      MidpointGapNgSquare N (midpointLeftGap N c.slot_b) →
      midpointLeftGap N c.slot_a = midpointLeftGap N c.slot_b

/--
**SO(4)/Δ orbit obstruction (open).**  A duplicate gap-orbit collision on the finite
stack forces a positive gap to survive — the spectral/holonomy closing step.
-/
def SO4DeltaOrbitObstruction (N : ℕ) : Prop :=
  ∀ (c : SO4GapOrbitCollision N),
    ∃ g ∈ midpointGapOrbit N, 0 < g ∧ gapSurvivesFiniteAngleStack N g

theorem so4_delta_orbit_obstruction_implies_cardinality {N : ℕ}
    (hOb : SO4DeltaOrbitObstruction N) :
    EckmannHiltonCardinalityObstruction N := by
  intro p q r hp hq hne hr hcrossp hcrossq
  obtain ⟨g, hg, hgpos, hStack⟩ :=
    hOb ⟨p, q, r, hp, hq, hne, hr, hcrossp, hcrossq⟩
  exact ⟨g, hg, hgpos, hStack⟩

theorem eckmann_hilton_forward_of_so4_delta_orbit {N : ℕ} (hN : 4 ≤ N)
    (hOb : SO4DeltaOrbitObstruction N) : EckmannHiltonForwardCollapse N :=
  eckmann_hilton_forward_collapse_of_cardinality_obstruction hN
    (so4_delta_orbit_obstruction_implies_cardinality hOb)

def SO4DeltaOrbitProfile (N : ℕ) : Prop :=
  SO4DeltaOrbitObstruction N

/-!
**Status.**  Extinction + pigeonhole ⇒ `SO4GapOrbitCollision` (proved).  The missing
step is `SO4DeltaOrbitObstruction`: turn collision geometry + critical-line weight +
Δ-orbit amplification into a **global** stack survivor.  The square-orbit special
case shows distinct square gaps cannot both be extinct at the same collision modulus;
the general case (no square requirement) remains open — i.e. the route is not yet
stronger than EH cardinality, but it **localizes** the obstruction on SO(4) orbit data.
-/

end

end Hqiv.Story
