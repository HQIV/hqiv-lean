import Hqiv.Story.S3SO4SquareOrbitCollision
import Hqiv.Story.S3GoldbachGapOneActivationBudget

/-!
# Square-orbit / Ng-square geometry → gap-one twin activation

Bridges the SO(4) square-orbit collision layer (`S3SO4SquareOrbitCollision`) to the
gap-one twin sub-budget (`S3GoldbachGapOneActivationBudget`).

## Honest split

* **Square diff prime ⇒ unit factor in `m − n`.**  At midpoint `N = m²`, a symmetric
  Ng-square pair with prime left arm `m² − n²` forces `m − n = 1`
  (`square_diff_prime_forces_unit_mn_at_square_midpoint`).  This is the proved
  square-orbit algebra — it constrains the **slot** factorization, not arbitrary gaps.

* **Gap-one activation fires when `g = 1`.**  A symmetric Goldbach pair at arms
  `N ± 1` is exactly a twin pair; activation mass is strictly positive
  (`square_diff_prime_forces_twin_annulus_sweep`).

* **Certified square instance `N = 4`.**  The only square midpoint where
  `g = 1` and Ng-square coincide with a twin is `m = 2` (`square_midpoint_twin_at_four`).

* **Δ-orbit obstruction discharge (anchor `N = 4` proved).**  `so4_delta_orbit_obstruction_at_four`
  witnesses global stack survivor `g = 1`; combined with certified gap-one geometry this
  yields unconditional anchor discharge (`so4_delta_orbit_anchor_four_discharge`).
  The global forcing Props remain open for general `m`.

Twin midpoints are usually **not** Ng-square (e.g. `N = 6`, twins `(5,7)`).  The
multiplicative square-orbit channel feeds the additive twin sub-budget when the
geometry lands on the `g = 1` slice — not for every twin.
-/

namespace Hqiv.Story

open Hqiv.Geometry Real Complex

noncomputable section

/-! ## Ng-square symmetric pair packaging -/

/--
**Ng-square symmetric pair** at midpoint `N` with left gap `g`: both arms `N ± g` are
prime and `N · g` is a perfect square (`MidpointGapNgSquare`).
-/
def IsNgSquareSymmetricPair (N g : ℕ) : Prop :=
  MidpointGapNgSquare N g ∧ symmetricPrimeReflectionAtGap N g

/-- Alias for square-orbit collision readouts. -/
abbrev IsNgSquareCollision (N g : ℕ) : Prop :=
  IsNgSquareSymmetricPair N g

theorem isNgSquareSymmetricPair_iff {N g : ℕ} :
    IsNgSquareSymmetricPair N g ↔
      MidpointGapNgSquare N g ∧ symmetricPrimeReflectionAtGap N g :=
  Iff.rfl

theorem isNgSquareCollision_iff {N g : ℕ} :
    IsNgSquareCollision N g ↔ IsNgSquareSymmetricPair N g :=
  Iff.rfl

theorem ng_square_symmetric_pair_of_midpoint_gap {N g : ℕ}
    (hNg : MidpointGapNgSquare N g) (hSym : symmetricPrimeReflectionAtGap N g) :
    IsNgSquareSymmetricPair N g :=
  ⟨hNg, hSym⟩

/-! ## Symmetric gap ↔ Goldbach midpoint pair -/

theorem goldbach_midpoint_pair_of_symmetric_gap {N g : ℕ} (hg : g ≤ N)
    (h : symmetricPrimeReflectionAtGap N g) :
    GoldbachMidpointPair N (N - g) (N + g) := by
  rcases h with ⟨h2, hp, hq⟩
  refine ⟨hp, hq, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

theorem goldbach_midpoint_pair_iff_symmetric_gap {N g : ℕ} (hg : g ≤ N) :
    GoldbachMidpointPair N (N - g) (N + g) ↔ symmetricPrimeReflectionAtGap N g := by
  constructor
  · intro ⟨hp, hq, hpLe, hNle, hsum⟩
    refine ⟨Nat.Prime.two_le hp, hp, hq⟩
  · exact goldbach_midpoint_pair_of_symmetric_gap hg

theorem symmetric_gap_of_goldbach_midpoint_pair {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    ∃ g ≤ N, symmetricPrimeReflectionAtGap N g ∧
      p = N - g ∧ q = N + g := by
  rcases h with ⟨hp, hq, hpLe, _, hsum⟩
  have hg : N - p ≤ N := by omega
  have hp' : p = N - (N - p) := (Nat.sub_sub_self hpLe).symm
  have hq' : q = N + (N - p) := by omega
  have hpair : GoldbachMidpointPair N (N - (N - p)) (N + (N - p)) := by
    refine ⟨hp' ▸ hp, hq' ▸ hq, ?_, ?_, ?_⟩
    all_goals omega
  refine ⟨N - p, ?_, ?_⟩
  · omega
  · exact ⟨(goldbach_midpoint_pair_iff_symmetric_gap hg).mp hpair, hp', hq'⟩

theorem nat_sub_one_add_two {N : ℕ} (hN : 1 ≤ N) : N - 1 + 2 = N + 1 := by omega

/-! ## Gap-one ⇒ twin support ⇒ activation -/

theorem symmetric_gap_one_iff_twin {N : ℕ} :
    symmetricPrimeReflectionAtGap N 1 ↔
      3 ≤ N ∧ TwinPrimePair (N - 1) := by
  constructor
  · intro h
    rcases h with ⟨h2, hp, hq⟩
    constructor
    · omega
    · refine ⟨hp, ?_⟩
      have h1 : 1 ≤ N := by omega
      simpa [nat_sub_one_add_two h1] using hq
  · intro ⟨hN, htwin⟩
    refine ⟨by omega, htwin.1, ?_⟩
    have h1 : 1 ≤ N := by omega
    simpa [nat_sub_one_add_two h1] using htwin.2

theorem symmetric_gap_one_implies_twin_support {N : ℕ}
    (h : symmetricPrimeReflectionAtGap N 1) :
    goldbachMidpointSupportsTwinPrime N := by
  rcases symmetric_gap_one_iff_twin.mp h with ⟨hN3, htwin⟩
  exact ⟨by omega, htwin⟩

theorem goldbach_gap_one_activation_mass_pos_of_twin_support {N : ℕ}
    (h : goldbachMidpointSupportsTwinPrime N) :
    0 < goldbachGapOneActivationMass N := by
  dsimp [goldbachGapOneActivationMass, goldbachMidpointSupportsTwinPrime]
  rcases h with ⟨hN, htwin⟩
  rw [if_pos ⟨hN, htwin⟩]
  positivity

theorem goldbach_gap_one_activation_mass_pos_of_symmetric_gap_one {N : ℕ}
    (h : symmetricPrimeReflectionAtGap N 1) :
    0 < goldbachGapOneActivationMass N :=
  goldbach_gap_one_activation_mass_pos_of_twin_support
    (symmetric_gap_one_implies_twin_support h)

/-! ## Square-orbit: prime square diff ⇒ unit `m − n` -/

theorem square_midpoint_left_arm_is_square_diff {m n : ℕ} (_hn : n ≤ m) :
    gapLeftArm (m * m) (n * n) = m * m - n * n := rfl

theorem square_midpoint_symmetric_pair_slot_prime {m n : ℕ} (hn : n < m)
    (hSym : symmetricPrimeReflectionAtGap (m * m) (n * n)) :
    Nat.Prime (m * m - n * n) := by
  have hnle : n ≤ m := Nat.le_of_lt hn
  have hslot := square_midpoint_left_arm_is_square_diff hnle
  rcases hSym with ⟨_, hp, _⟩
  simpa [hslot] using hp

/--
**Square diff prime forces unit factor.**  At `N = m²`, a symmetric Ng-square pair with
prime slot `m² − n²` forces `m − n = 1` (proved square-orbit algebra).
-/
theorem square_diff_prime_forces_unit_mn_at_square_midpoint {m n : ℕ} (hn : n < m)
    (hSym : symmetricPrimeReflectionAtGap (m * m) (n * n)) :
    m - n = 1 :=
  prime_of_square_diff_forces_unit_gap hn
    (square_midpoint_symmetric_pair_slot_prime hn hSym)

theorem square_midpoint_ng_square_symmetric_forces_unit_mn {m n : ℕ} (hn : n < m)
    (_hNg : MidpointGapNgSquare (m * m) (n * n))
    (hSym : symmetricPrimeReflectionAtGap (m * m) (n * n)) :
    m - n = 1 :=
  square_diff_prime_forces_unit_mn_at_square_midpoint hn hSym

theorem square_midpoint_unit_mn_forces_gap_eq_square {m n : ℕ} (hn : n < m)
    (hunit : m - n = 1) :
    n * n = (m - 1) * (m - 1) := by
  have hn' : n = m - 1 := by omega
  simpa [hn', pow_two] using rfl

/-! ## Main bridge: `g = 1` ⇒ gap-one activation -/

/--
**Square-orbit → gap-one activation (conditional on `g = 1`).**

A symmetric Goldbach pair at arms `N ± g` together with Ng-square data activates the
twin sub-budget once `g = 1` (twin primes).  The square-orbit layer supplies
`m − n = 1` at square midpoints; landing on `g = 1` is the additive twin slice.
-/
theorem square_diff_prime_forces_twin_annulus_sweep {N g : ℕ} (hg : g ≤ N)
    (_hPair : GoldbachMidpointPair N (N - g) (N + g))
    (_hNg : MidpointGapNgSquare N g) (hg1 : g = 1) :
    0 < goldbachGapOneActivationMass N := by
  subst hg1
  exact goldbach_gap_one_activation_mass_pos_of_symmetric_gap_one
    (goldbach_midpoint_pair_iff_symmetric_gap hg |>.mp _hPair)

theorem square_diff_prime_forces_twin_sweep_package {N : ℕ}
    (h : symmetricPrimeReflectionAtGap N 1) :
    GoldbachTwinGapOneSweepPackage (N - 1)
      (symmetric_gap_one_iff_twin.mp h).2 := by
  rcases symmetric_gap_one_iff_twin.mp h with ⟨_, htwin⟩
  exact goldbach_twin_gap_one_sweep_package (N - 1) htwin

theorem isNgSquare_collision_forces_twin_annulus_sweep {N g : ℕ} (hg : g ≤ N)
    (h : IsNgSquareCollision N g) (hg1 : g = 1) :
    0 < goldbachGapOneActivationMass N :=
  square_diff_prime_forces_twin_annulus_sweep hg
    (goldbach_midpoint_pair_of_symmetric_gap hg h.2) h.1 hg1

/-! ## Certified square midpoint twin (`N = 4`) -/

theorem square_midpoint_gap_one_is_ng_square {m : ℕ} :
    MidpointGapNgSquare (m * m) 1 ↔ ∃ s, m * m = s * s := by
  constructor
  · intro ⟨s, hs⟩
    exact ⟨s, by simpa [one_mul] using hs⟩
  · intro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    simpa using hs

theorem square_midpoint_twin_at_four :
    symmetricPrimeReflectionAtGap 4 1 ∧
      MidpointGapNgSquare 4 1 ∧
      0 < goldbachGapOneActivationMass 4 ∧
      GoldbachTwinGapOneSweepPackage 3 ⟨nat_prime_three, nat_prime_five⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨by decide, nat_prime_three, nat_prime_five⟩
  · exact ⟨2, by decide⟩
  · exact goldbach_gap_one_activation_mass_pos_of_symmetric_gap_one
      ⟨by decide, nat_prime_three, nat_prime_five⟩
  · exact goldbach_twin_gap_one_sweep_package 3 ⟨nat_prime_three, nat_prime_five⟩

/-! ## Converse: twin + Ng-square at `g = 1` ⇒ square midpoint -/

theorem twin_support_ng_square_gap_one_forces_square_midpoint {N : ℕ}
    (_h : goldbachMidpointSupportsTwinPrime N)
    (hNg : MidpointGapNgSquare N 1) :
    ∃ m, N = m * m := by
  rcases hNg with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  simpa [one_mul] using hs

theorem twin_ng_square_gap_one_characterization {N : ℕ}
    (h : goldbachMidpointSupportsTwinPrime N)
    (hNg : MidpointGapNgSquare N 1) :
    ∃ m, N = m * m ∧ symmetricPrimeReflectionAtGap (m * m) 1 ∧
      0 < goldbachGapOneActivationMass (m * m) := by
  rcases twin_support_ng_square_gap_one_forces_square_midpoint h hNg with ⟨m, hm⟩
  subst hm
  have h3 : 3 ≤ m * m := by
    rcases h with ⟨_, htwin⟩
    have := Nat.Prime.two_le htwin.1
    omega
  refine ⟨m, rfl, ?_, ?_⟩
  · exact symmetric_gap_one_iff_twin.mpr ⟨h3, h.2⟩
  · exact goldbach_gap_one_activation_mass_pos_of_twin_support h

/-! ## Square-orbit collision closure (re-export link) -/

theorem ng_square_collision_contradiction_when_square_orbit_closes {N : ℕ}
    (hClose : SO4SquareOrbitCollisionCloses N) (c : SO4GapOrbitCollision N)
    (hNg_a : MidpointGapNgSquare N (midpointLeftGap N c.slot_a))
    (hNg_b : MidpointGapNgSquare N (midpointLeftGap N c.slot_b)) :
    False :=
  square_orbit_collision_extinction_contradiction hClose c hNg_a hNg_b

/-! ## Square ladder: unit `m − n` Ng-square pairs -/

/--
A **unit-`m−n` Ng-square pair** on the square ladder: gap `g = n²` at midpoint `m²`
with `m − n = 1`.
-/
def SquareLadderUnitMnNgSquarePair : Prop :=
  ∃ m n, n < m ∧ MidpointGapNgSquare (m * m) (n * n) ∧ m - n = 1

/--
A **gap-one symmetric Ng-square pair** at square midpoint `m²`: arms `m² ± 1` prime
and `m² · 1` is a square.
-/
def SquareLadderGapOneSymmetricSquarePair : Prop :=
  ∃ m, 0 < m ∧
    symmetricPrimeReflectionAtGap (m * m) 1 ∧ MidpointGapNgSquare (m * m) 1

theorem square_ladder_unit_mn_ng_square_certified :
    SquareLadderUnitMnNgSquarePair :=
  ⟨2, 1, by omega, ⟨2, by decide⟩, by omega⟩

theorem square_ladder_gap_one_symmetric_square_pair_certified :
    SquareLadderGapOneSymmetricSquarePair :=
  ⟨2, by decide, square_midpoint_twin_at_four.1, square_midpoint_twin_at_four.2.1⟩

theorem square_ladder_unit_mn_gap_one_forces_two_one {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    (hunit : m - n = 1) (hg1 : n * n = 1) :
    m = 2 ∧ n = 1 := by
  have hn1 : n = 1 := by
    rcases n with (_ | _ | n)
    · simp at hn
    · rfl
    · simp at hg1
  subst hn1
  omega

theorem not_prime_prod_both_ge_two {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ¬ Nat.Prime (a * b) := by
  intro hp
  have ha0 : 0 < a := by omega
  rcases Nat.Prime.eq_one_or_self_of_dvd hp a ⟨b, rfl⟩ with h1 | haself
  · omega
  · have heq : a * b = a * 1 := by rw [Nat.mul_one, ← haself]
    have hb1 : b = 1 := Nat.mul_left_cancel ha0 heq
    omega

theorem square_ladder_unit_mn_ng_square_gap_one_is_certified
    {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    (hunit : m - n = 1) (hNg : MidpointGapNgSquare (m * m) (n * n))
    (hg1 : n * n = 1) :
    m = 2 ∧ n = 1 ∧ MidpointGapNgSquare 4 1 := by
  rcases square_ladder_unit_mn_gap_one_forces_two_one hn hnm hunit hg1 with ⟨hm, hn1⟩
  subst hm hn1
  exact ⟨rfl, rfl, ⟨2, by decide⟩⟩

/--
At a square midpoint `N = m²`, a symmetric gap-one pair forces `m ≤ 2` — twins at
`m² ± 1` require `m² − 1` prime, which fails for `m ≥ 3` since `(m−1)(m+1)` splits.
-/
theorem square_midpoint_symmetric_gap_one_forces_m_le_two {m : ℕ} (hm : 0 < m)
    (h : symmetricPrimeReflectionAtGap (m * m) 1) : m ≤ 2 := by
  rcases symmetric_gap_one_iff_twin.mp h with ⟨_, htwin⟩
  by_contra hm2
  push_neg at hm2
  have hm3 : 3 ≤ m := by omega
  have hprime : Nat.Prime (m * m - 1) := htwin.1
  have h1 : 1 ≤ m := Nat.one_le_of_lt hm
  have hfac : (m - 1) * (m + 1) = m * m - 1 := by
    rw [← square_diff_eq_gap_arms (n := 1) h1]
  have ha : 2 ≤ m - 1 := by omega
  have hb : 2 ≤ m + 1 := by omega
  have hnot : ¬ Nat.Prime (m * m - 1) := by
    rw [← hfac]
    exact not_prime_prod_both_ge_two ha hb
  exact hnot hprime

theorem square_ladder_gap_one_symmetric_unique_at_m_two :
    ∀ m, 0 < m → symmetricPrimeReflectionAtGap (m * m) 1 → m = 2 := by
  intro m hm h
  have hle := square_midpoint_symmetric_gap_one_forces_m_le_two hm h
  have hm1 : m ≠ 1 := by
    intro hm1
    subst hm1
    rcases symmetric_gap_one_iff_twin.mp h with ⟨hN, _⟩
    omega
  omega

/-! ## Square-ladder gap-one negative identity (machine-checked) -/

/--
**No twins on square midpoints for `m > 2`.**  The only square index carrying a
symmetric gap-one (twin) pair is `m = 2` (`N = 4`).  Reusable one-line contradiction.
-/
theorem no_twin_on_square_midpoint_for_m_gt_two {m : ℕ} (hm : m > 2)
    (h : symmetricPrimeReflectionAtGap (m * m) 1) : False := by
  have hm2 : m = 2 := square_ladder_gap_one_symmetric_unique_at_m_two m (by omega) h
  omega

theorem no_twin_on_square_midpoint_for_m_ne_two {m : ℕ} (hm : m ≠ 2)
    (h : symmetricPrimeReflectionAtGap (m * m) 1) : False := by
  by_cases hmgt : m > 2
  · exact no_twin_on_square_midpoint_for_m_gt_two hmgt h
  · have hmle : m ≤ 2 := by omega
    interval_cases m <;> simp [symmetric_gap_one_iff_twin] at h <;> omega

theorem no_ng_square_symmetric_gap_one_on_square_for_m_gt_two {m : ℕ} (hm : m > 2)
    (h : IsNgSquareSymmetricPair (m * m) 1) : False :=
  no_twin_on_square_midpoint_for_m_gt_two hm h.2

theorem no_ng_square_symmetric_gap_one_on_square_for_m_ne_two {m : ℕ} (hm : m ≠ 2)
    (h : IsNgSquareSymmetricPair (m * m) 1) : False :=
  no_twin_on_square_midpoint_for_m_ne_two hm h.2

/--
Twin support on a square midpoint forces the anchor index `m = 2` (`N = 4`).
Stronger than the symmetric-gap formulation — no Ng-square hypothesis needed.
-/
theorem goldbach_midpoint_twin_on_square_forces_m_two {m : ℕ}
    (htwin : goldbachMidpointSupportsTwinPrime (m * m)) :
    m = 2 := by
  rcases htwin with ⟨hN, htwinPair⟩
  match m with
  | 0 => omega
  | 1 => omega
  | 2 => rfl
  | m' + 3 =>
    exfalso
    have hmgt : 2 < m' + 3 := by
      have : 3 ≤ m' + 3 := Nat.le_add_left 3 m'
      exact Nat.lt_of_lt_of_le (by decide : 2 < 3) this
    have h3 : 3 ≤ (m' + 3) * (m' + 3) := by
      have hpos : 3 ≤ m' + 3 := Nat.le_add_left 3 m'
      have : 9 ≤ (m' + 3) * (m' + 3) := Nat.mul_le_mul hpos hpos
      omega
    exact no_twin_on_square_midpoint_for_m_gt_two hmgt
      (symmetric_gap_one_iff_twin.mpr ⟨h3, htwinPair⟩)

theorem goldbach_midpoint_twin_on_square_midpoint_eq_four {m : ℕ}
    (htwin : goldbachMidpointSupportsTwinPrime (m * m)) :
    m * m = 4 := by
  have hm2 := goldbach_midpoint_twin_on_square_forces_m_two htwin
  subst hm2
  rfl

theorem goldbach_midpoint_is_square_twin_index_eq_four {N : ℕ}
    (hSq : ∃ m, N = m * m) (htwin : goldbachMidpointSupportsTwinPrime N) :
    N = 4 := by
  rcases hSq with ⟨m, hm⟩
  subst hm
  exact goldbach_midpoint_twin_on_square_midpoint_eq_four
    ⟨htwin.1, htwin.2⟩

theorem twin_ng_square_gap_one_only_at_four {N : ℕ}
    (htwin : goldbachMidpointSupportsTwinPrime N) (hNg : MidpointGapNgSquare N 1) :
    N = 4 :=
  goldbach_midpoint_is_square_twin_index_eq_four
    (twin_support_ng_square_gap_one_forces_square_midpoint htwin hNg) htwin

/-! ## Anchor `N = 4`: obstruction, stack survivor, gap-one symmetric pair -/

theorem midpoint_left_gap_four_three : midpointLeftGap 4 3 = 1 := by decide

theorem midpoint_gap_orbit_four_one : (1 : ℕ) ∈ midpointGapOrbit 4 := by
  refine (mem_midpointGapOrbit_iff (N := 4)).mpr ⟨3, ?_, ?_⟩
  · exact (mem_midpointScanSlots_iff (N := 4) (p := 3)).mpr ⟨by decide, by decide⟩
  · exact midpoint_left_gap_four_three

theorem symmetricPrimeReflectionAtGap_four_one :
    symmetricPrimeReflectionAtGap 4 1 :=
  square_midpoint_twin_at_four.1

theorem gapSurvivesFiniteAngleStack_four_one :
    gapSurvivesFiniteAngleStack 4 1 := by
  rw [gap_survives_stack_iff_symmetric_prime (N := 4) (g := 1) (by omega) (by omega)]
  exact symmetricPrimeReflectionAtGap_four_one

theorem constructive_spectral_forces_slope_hit_four :
    ConstructiveSpectralForcesSlopeHit 4 := by
  intro _hc
  refine ⟨1, midpoint_gap_orbit_four_one, by decide, gapSurvivesFiniteAngleStack_four_one⟩

theorem eckmann_hilton_forward_collapse_four :
    EckmannHiltonForwardCollapse 4 :=
  (eckmann_hilton_forward_collapse_iff_constructive 4).mpr constructive_spectral_forces_slope_hit_four

/--
**Proved at the anchor.**  Every SO(4) gap-orbit collision at `N = 4` admits the
global stack survivor `g = 1` on the slope orbit — not merely an open target.
-/
theorem so4_delta_orbit_obstruction_at_four :
    SO4DeltaOrbitObstruction 4 := by
  intro _c
  refine ⟨1, midpoint_gap_orbit_four_one, by decide, gapSurvivesFiniteAngleStack_four_one⟩

theorem so4_delta_obstruction_four_implies_eh_forward :
    EckmannHiltonForwardCollapse 4 :=
  eckmann_hilton_forward_of_so4_delta_orbit (N := 4) (by decide) so4_delta_orbit_obstruction_at_four

/--
**Anchor discharge (`m = 2`).**  Δ-orbit obstruction at `N = 4` yields the certified
gap-one symmetric Ng-square pair — the geometric input was independent; obstruction
now matches it at the smallest square midpoint.
-/
theorem so4_delta_obstruction_forces_gap_one_symmetric_square_pair_at_anchor
    (_hOb : SO4DeltaOrbitObstruction 4) :
    symmetricPrimeReflectionAtGap 4 1 ∧ MidpointGapNgSquare 4 1 :=
  ⟨symmetricPrimeReflectionAtGap_four_one, square_midpoint_twin_at_four.2.1⟩

theorem so4_delta_obstruction_forces_gap_one_symmetric_square_pair_at_m_two
    (_hm : 0 < 2) (hOb : SO4DeltaOrbitObstruction 4) :
    symmetricPrimeReflectionAtGap 4 1 ∧ MidpointGapNgSquare 4 1 :=
  so4_delta_obstruction_forces_gap_one_symmetric_square_pair_at_anchor hOb

/--
**Established (not conditional).**  Obstruction + gap-one symmetric pair coexist at
`N = 4`; activation on the twin sub-budget follows without extra hypotheses.
-/
theorem so4_delta_orbit_anchor_four_established :
    SO4DeltaOrbitObstruction 4 ∧
      symmetricPrimeReflectionAtGap 4 1 ∧
      MidpointGapNgSquare 4 1 ∧
      0 < goldbachGapOneActivationMass 4 :=
  ⟨so4_delta_orbit_obstruction_at_four,
    symmetricPrimeReflectionAtGap_four_one,
    square_midpoint_twin_at_four.2.1,
    square_midpoint_twin_at_four.2.2.1⟩

theorem so4_delta_obstruction_forces_gap_one_symmetric_square_pair_when_m_eq_two
    {m : ℕ} (hm : m = 2) (_hpos : 0 < m) (hOb : SO4DeltaOrbitObstruction (m * m)) :
    symmetricPrimeReflectionAtGap (m * m) 1 ∧ MidpointGapNgSquare (m * m) 1 := by
  subst hm
  exact so4_delta_obstruction_forces_gap_one_symmetric_square_pair_at_anchor hOb

/-! ## Anchor `N = 9` (`m = 3`): obstruction + symmetric pair at `g = 2` -/

theorem midpoint_left_gap_nine_seven : midpointLeftGap 9 7 = 2 := by decide

theorem symmetricPrimeReflectionAtGap_nine_two :
    symmetricPrimeReflectionAtGap 9 2 :=
  (dualMidpointSurvivor_iff_symmetric_gap (N := 9) (p := 7) (by omega)).mp
    dual_midpoint_survivor_nine_seven

theorem midpoint_gap_orbit_nine_two : (2 : ℕ) ∈ midpointGapOrbit 9 := by
  refine (mem_midpointGapOrbit_iff (N := 9)).mpr ⟨7, ?_, ?_⟩
  · exact (mem_midpointScanSlots_iff (N := 9) (p := 7)).mpr ⟨by decide, by decide⟩
  · exact midpoint_left_gap_nine_seven

theorem gapSurvivesFiniteAngleStack_nine_two :
    gapSurvivesFiniteAngleStack 9 2 := by
  rw [gap_survives_stack_iff_symmetric_prime (N := 9) (g := 2) (by omega) (by omega)]
  exact symmetricPrimeReflectionAtGap_nine_two

theorem constructive_spectral_forces_slope_hit_nine :
    ConstructiveSpectralForcesSlopeHit 9 := by
  intro _hc
  refine ⟨2, midpoint_gap_orbit_nine_two, by decide, gapSurvivesFiniteAngleStack_nine_two⟩

theorem eckmann_hilton_forward_collapse_nine :
    EckmannHiltonForwardCollapse 9 :=
  (eckmann_hilton_forward_collapse_iff_constructive 9).mpr constructive_spectral_forces_slope_hit_nine

theorem so4_delta_orbit_obstruction_at_nine :
    SO4DeltaOrbitObstruction 9 := by
  intro _c
  refine ⟨2, midpoint_gap_orbit_nine_two, by decide, gapSurvivesFiniteAngleStack_nine_two⟩

theorem so4_delta_obstruction_forces_symmetric_square_pair_at_anchor_nine
    (_hOb : SO4DeltaOrbitObstruction 9) :
    ∃ g, symmetricPrimeReflectionAtGap 9 g :=
  ⟨2, symmetricPrimeReflectionAtGap_nine_two⟩

structure SO4SquareLadderSymmetricDischargeWitness (m : ℕ) where
  hm : 0 < m
  obstruction : SO4DeltaOrbitObstruction (m * m)
  symmetric_gap : ∃ g, symmetricPrimeReflectionAtGap (m * m) g

theorem so4_square_ladder_symmetric_discharge_witness_three
    (hOb : SO4DeltaOrbitObstruction 9) :
    SO4SquareLadderSymmetricDischargeWitness 3 :=
  { hm := by decide
    obstruction := hOb
    symmetric_gap := so4_delta_obstruction_forces_symmetric_square_pair_at_anchor_nine hOb }

theorem so4_square_ladder_symmetric_discharge_witness_two
    (hOb : SO4DeltaOrbitObstruction 4) :
    SO4SquareLadderSymmetricDischargeWitness 2 :=
  { hm := by decide
    obstruction := hOb
    symmetric_gap := ⟨1, symmetricPrimeReflectionAtGap_four_one⟩ }

theorem so4_delta_orbit_obstruction_anchors_established :
    SO4DeltaOrbitObstruction 4 ∧ SO4DeltaOrbitObstruction 9 ∧
      (∃ g, symmetricPrimeReflectionAtGap 4 g) ∧
      (∃ g, symmetricPrimeReflectionAtGap 9 g) :=
  ⟨so4_delta_orbit_obstruction_at_four, so4_delta_orbit_obstruction_at_nine,
    ⟨1, symmetricPrimeReflectionAtGap_four_one⟩,
    ⟨2, symmetricPrimeReflectionAtGap_nine_two⟩⟩

/-! ## Δ-orbit obstruction → square ladder (open targets + conditional discharge) -/

/--
**Open discharge target (strong).**  At every square midpoint, SO(4) Δ-orbit obstruction
forces a unit-`m−n` Ng-square pair `MidpointGapNgSquare (m²) (n²)` with `n < m`.
Not proved — this is the multiplicative-to-additive ladder step.
-/
def SO4DeltaOrbitObstructionForcesUnitMnNgSquarePair : Prop :=
  ∀ m, 0 < m → SO4DeltaOrbitObstruction (m * m) →
    ∃ n, n < m ∧ MidpointGapNgSquare (m * m) (n * n) ∧ m - n = 1

/--
**Open discharge target (gap-one slice).**  Δ-orbit obstruction forces a symmetric
Ng-square pair at **gap `g = 1`** on the square ladder — the twin activation channel.
-/
def SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair : Prop :=
  ∀ m, 0 < m → SO4DeltaOrbitObstruction (m * m) →
    symmetricPrimeReflectionAtGap (m * m) 1 ∧ MidpointGapNgSquare (m * m) 1

/--
**Replacement open target (wider symmetric gaps).**  Δ-orbit obstruction at each square
midpoint forces **some** symmetric prime reflection `∃ g`.  The gap-one / twin slice
(`g = 1`) is refuted globally — see
`so4_delta_obstruction_forces_gap_one_symmetric_square_pair_false`.
-/
def SO4DeltaOrbitObstructionForcesSymmetricSquarePair : Prop :=
  ∀ m, 0 < m → SO4DeltaOrbitObstruction (m * m) →
    ∃ g, symmetricPrimeReflectionAtGap (m * m) g

/--
**Square-ladder symmetric pressure:** infinitely often some `m²` hosts a symmetric
prime gap (any `g`, not necessarily gap-one).
-/
def SquareLadderSymmetricPressure : Prop :=
  ∀ M₀, ∃ m, m ≥ M₀ ∧ ∃ g, symmetricPrimeReflectionAtGap (m * m) g

theorem so4_delta_obstruction_forces_symmetric_square_pair_at_certified_m
    {m : ℕ} (hm : m = 2 ∨ m = 3) (_hOb : SO4DeltaOrbitObstruction (m * m)) :
    ∃ g, symmetricPrimeReflectionAtGap (m * m) g := by
  rcases hm with rfl | rfl
  · exact ⟨1, symmetricPrimeReflectionAtGap_four_one⟩
  · exact ⟨2, symmetricPrimeReflectionAtGap_nine_two⟩

theorem so4_delta_obstruction_symmetric_square_pair_conditional_discharge
    (hRoute : SO4DeltaOrbitObstructionForcesSymmetricSquarePair)
    (m : ℕ) (hm : 0 < m) (hOb : SO4DeltaOrbitObstruction (m * m)) :
    ∃ g, symmetricPrimeReflectionAtGap (m * m) g ∧
      SO4SquareLadderSymmetricDischargeWitness m := by
  rcases hRoute m hm hOb with ⟨g, hg⟩
  exact ⟨g, hg, ⟨hm, hOb, ⟨g, hg⟩⟩⟩

theorem so4_square_ladder_symmetric_witnesses_certified :
    SO4SquareLadderSymmetricDischargeWitness 2 ∧
      SO4SquareLadderSymmetricDischargeWitness 3 :=
  ⟨so4_square_ladder_symmetric_discharge_witness_two so4_delta_orbit_obstruction_at_four,
    so4_square_ladder_symmetric_discharge_witness_three so4_delta_orbit_obstruction_at_nine⟩

/--
The global Δ-orbit ⇒ gap-one symmetric forcing target is **false**: obstruction at
`N = 9` cannot produce a twin on the square ladder (`m = 3 > 2`).
-/
theorem so4_delta_obstruction_forces_gap_one_symmetric_square_pair_false :
    ¬ SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair := by
  intro hRoute
  have hsym := (hRoute 3 (by decide) so4_delta_orbit_obstruction_at_nine).1
  exact no_twin_on_square_midpoint_for_m_gt_two (by decide) hsym

theorem so4_delta_obstruction_gap_one_symmetric_forcing_contradiction_at_nine
    (hRoute : SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair) :
    False :=
  so4_delta_obstruction_forces_gap_one_symmetric_square_pair_false hRoute

/--
Witness bundle: obstruction at `m²` together with the gap-one symmetric Ng-square
input (the conditional bridge once the open target above is closed).
-/
structure SO4SquareLadderGapOneDischargeWitness (m : ℕ) where
  hm : 0 < m
  obstruction : SO4DeltaOrbitObstruction (m * m)
  symmetric_gap_one : symmetricPrimeReflectionAtGap (m * m) 1
  ng_square_gap_one : MidpointGapNgSquare (m * m) 1

theorem so4_square_ladder_gap_one_discharge_witness_two_of_obstruction
    (hOb : SO4DeltaOrbitObstruction 4) :
    SO4SquareLadderGapOneDischargeWitness 2 :=
  { hm := by decide
    obstruction := hOb
    symmetric_gap_one := symmetricPrimeReflectionAtGap_four_one
    ng_square_gap_one := square_midpoint_twin_at_four.2.1 }

theorem so4_square_ladder_discharge_witness_forces_activation {m : ℕ}
    (h : SO4SquareLadderGapOneDischargeWitness m) :
    0 < goldbachGapOneActivationMass (m * m) ∧
      GoldbachTwinGapOneSweepPackage (m * m - 1)
        (symmetric_gap_one_iff_twin.mp h.symmetric_gap_one).2 := by
  refine ⟨?_, ?_⟩
  · exact goldbach_gap_one_activation_mass_pos_of_symmetric_gap_one h.symmetric_gap_one
  · exact square_diff_prime_forces_twin_sweep_package h.symmetric_gap_one

theorem so4_delta_obstruction_at_four_forces_activation
    (hOb : SO4DeltaOrbitObstruction 4) :
    0 < goldbachGapOneActivationMass 4 :=
  (so4_square_ladder_discharge_witness_forces_activation
    (so4_square_ladder_gap_one_discharge_witness_two_of_obstruction hOb)).1

theorem so4_delta_orbit_anchor_four_activation :
    0 < goldbachGapOneActivationMass 4 :=
  so4_delta_obstruction_at_four_forces_activation so4_delta_orbit_obstruction_at_four

/--
**Full anchor discharge.**  Obstruction at `N = 4` + gap-one symmetric input ⇒
positive activation mass and twin sweep package at the smallest square midpoint.
-/
theorem so4_delta_orbit_anchor_four_discharge :
    0 < goldbachGapOneActivationMass 4 ∧
      GoldbachTwinGapOneSweepPackage 3 ⟨nat_prime_three, nat_prime_five⟩ :=
  so4_square_ladder_discharge_witness_forces_activation
    (so4_square_ladder_gap_one_discharge_witness_two_of_obstruction so4_delta_orbit_obstruction_at_four)

theorem so4_delta_obstruction_conditional_gap_one_activation {m : ℕ} (hm : 0 < m)
    (_hOb : SO4DeltaOrbitObstruction (m * m))
    (hSym : symmetricPrimeReflectionAtGap (m * m) 1)
    (hNg : MidpointGapNgSquare (m * m) 1) :
    0 < goldbachGapOneActivationMass (m * m) ∧
      GoldbachTwinGapOneSweepPackage (m * m - 1)
        (symmetric_gap_one_iff_twin.mp hSym).2 :=
  so4_square_ladder_discharge_witness_forces_activation ⟨hm, _hOb, hSym, hNg⟩

/--
**Named open target (unit `m − n`).**  Closing this shows Δ-orbit obstruction yields
`∃ n, MidpointGapNgSquare (m²) (n²)` with `m − n = 1` on the square ladder.
-/
theorem so4_delta_orbit_obstruction_forces_unit_mn_ng_square_pair
    (hRoute : SO4DeltaOrbitObstructionForcesUnitMnNgSquarePair)
    (m : ℕ) (hm : 0 < m) (hOb : SO4DeltaOrbitObstruction (m * m)) :
    ∃ n, n < m ∧ MidpointGapNgSquare (m * m) (n * n) ∧ m - n = 1 :=
  hRoute m hm hOb

/--
**Named open target (gap-one symmetric).**  Closing this turns the conditional bridge
into a discharge route from Δ-orbit obstruction to twin sub-budget activation.
-/
theorem so4_delta_orbit_obstruction_forces_g_one_symmetric_square_pair
    (hRoute : SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair)
    (m : ℕ) (hm : 0 < m) (hOb : SO4DeltaOrbitObstruction (m * m)) :
    symmetricPrimeReflectionAtGap (m * m) 1 ∧ MidpointGapNgSquare (m * m) 1 :=
  hRoute m hm hOb

theorem so4_delta_obstruction_square_ladder_discharge_chain
    (hRoute : SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair)
    (m : ℕ) (hm : 0 < m) (hOb : SO4DeltaOrbitObstruction (m * m)) :
    0 < goldbachGapOneActivationMass (m * m) ∧
      IsNgSquareSymmetricPair (m * m) 1 := by
  rcases hRoute m hm hOb with ⟨hSym, hNg⟩
  exact ⟨goldbach_gap_one_activation_mass_pos_of_symmetric_gap_one hSym,
    ng_square_symmetric_pair_of_midpoint_gap hNg hSym⟩

theorem so4_delta_obstruction_unit_mn_and_gap_one_route_forces_activation
    (hUnit : SO4DeltaOrbitObstructionForcesUnitMnNgSquarePair)
    (hGapOne : SO4DeltaOrbitObstructionForcesGapOneSymmetricSquarePair)
    (m : ℕ) (hm : 0 < m) (hOb : SO4DeltaOrbitObstruction (m * m)) :
    0 < goldbachGapOneActivationMass (m * m) :=
  (so4_delta_obstruction_square_ladder_discharge_chain hGapOne m hm hOb).1

theorem so4_delta_obstruction_unit_mn_gap_one_forces_certified_activation
    (_hUnit : SO4DeltaOrbitObstructionForcesUnitMnNgSquarePair)
    (m : ℕ) (_hm : 0 < m) (_hOb : SO4DeltaOrbitObstruction (m * m))
    (hn1 : ∃ n, n < m ∧ MidpointGapNgSquare (m * m) (n * n) ∧ m - n = 1 ∧ n * n = 1) :
    m = 2 ∧ 0 < goldbachGapOneActivationMass 4 := by
  rcases hn1 with ⟨n, hnm, hNg, hunit, hn1⟩
  have hnpos : 0 < n := by nlinarith
  rcases square_ladder_unit_mn_ng_square_gap_one_is_certified hnpos hnm hunit hNg hn1 with
    ⟨hm, _, _⟩
  subst hm
  exact ⟨rfl, square_midpoint_twin_at_four.2.2.1⟩

end

end Hqiv.Story
