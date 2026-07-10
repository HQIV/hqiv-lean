import Hqiv.Story.S3PolarProjectionCollapse
import Hqiv.Story.S3ExplicitFormulaDualitySlot
import Hqiv.Geometry.ScaleOrbitMulMod

/-!
# Holonomy never skips a number: the no-skip / no-double ladder split

This module formalizes the intuition *"both RH and Goldbach come down to
holonomy doesn't skip a number"* against the SO(8) half-slope bridge, and
extracts the sharpest version that is provable today.

## The two ladders

* **Additive (Goldbach) ladder.**  The bridge's midpoint field
  `SO4ZetaHolonomyForcesMidpointPairs 2` is literally
  `∀ N ≥ 2, 0 < goldbachMidpointCount N` — the holonomy pair count never
  touches zero as the midpoint climbs.  "Never skips a rung" **is** the
  Goldbach channel (`midpoint_never_skips_iff_goldbach`).

* **Vertical (ζ) ladder.**  An off-line zero at height `t` forces a *second*
  zero at the same height (its polar partner `1 − conj ρ`), so RH is exactly
  "no height carries two zeros" (`RH_iff_unique_zero_per_height`).  The ζ
  channel is the mirror statement: the vertical ladder never **doubles** a
  rung (`zero_never_doubles_iff_RH`).

## What is unconditional (proved here / re-exported)

1. **Transport never skips.**  The coprime mul-mod holonomy transport hits
   every position `0 < k < n` (`transport_never_skips_position`).  Skipping
   positions was never the open problem.

2. **The additive rung is never empty (Bertrand).**  Every rung `N ≥ 2` has
   a prime strictly inside `(N, 2N)` — the right arm of the midpoint mirror
   always carries a prime candidate (`bertrand_right_arm_never_empty`).

3. **The vertical rung is never half-occupied (FE + Schwarz).**  Every zero
   height also carries the polar partner zero
   (`zero_height_carries_polar_partner`).

## The honest split (the interesting result)

`rung_populated_iff_reflected_prime_hit` localizes each Goldbach rung:

`0 < goldbachMidpointCount N ↔ ∃ q, q prime ∧ N ≤ q ∧ (2N − q) prime`.

So, given the unconditional population of both ladders, the two open
millennium payloads are *precisely*:

* **GB** = "at every rung some unconditional right-arm prime hit *reflects*
  to a prime" (`midpoint_never_skips_iff_bertrand_hit_reflects`);
* **RH** = "the unconditional same-height polar pair never *splits*"
  (`never_doubles_forces_polar_collapse` + `polar_collapse_iff_RH`).

The capstone `so8_bridge_iff_no_double_and_no_skip` proves the bridge is
equivalent to the conjunction (no-double ∧ no-skip): the intuition is a
faithful reformulation with zero slack — not a discharge, but the exact
geometric form of what remains.
-/

namespace Hqiv.Story

open Complex Hqiv.Geometry

noncomputable section

/-! ## The two no-skip predicates -/

/--
**Additive no-skip.**  The Goldbach midpoint holonomy count is positive at
every rung `N ≥ 2` — the ladder never skips a number.  Definitionally the
bridge's midpoint field at threshold `2`.
-/
def MidpointHolonomyNeverSkips : Prop :=
  SO4ZetaHolonomyForcesMidpointPairs 2

/--
**Vertical no-double.**  No height carries two distinct nontrivial zeros —
the winding along the critical strip takes each rung exactly once instead of
doubling one height (and, by zero counting, skipping none).
-/
def ZeroHeightHolonomyNeverDoubles : Prop :=
  ∀ ρ₁ ρ₂ : ℂ, IsNontrivialZetaZero ρ₁ → IsNontrivialZetaZero ρ₂ →
    ρ₁.im = ρ₂.im → ρ₁ = ρ₂

/-- The additive no-skip is exactly Goldbach parity (zero slack). -/
theorem midpoint_never_skips_iff_goldbach :
    MidpointHolonomyNeverSkips ↔ GoldbachParity :=
  so4_zeta_holonomy_bridge_two_iff_goldbach_parity

/-- The vertical no-double is exactly RH (zero slack), given the Schwarz
conjugation identity carried as an explicit hypothesis. -/
theorem zero_never_doubles_iff_RH
    (hconj : ∀ t : ℂ, riemannZeta (schwarzReflect t) = schwarzReflect (riemannZeta t)) :
    ZeroHeightHolonomyNeverDoubles ↔ RiemannHypothesis :=
  (RH_iff_unique_zero_per_height hconj).symm

/-! ## Unconditional layer 1: the transport itself never skips -/

/--
**Transport never skips (unconditional).**  The coprime mul-mod holonomy
transport hits every position `0 < k < n`.  The open content of the bridge
was never positional skipping — it is whether a hit position is prime-paired.
-/
theorem transport_never_skips_position {n m : ℕ} (hn : 0 < n)
    (hcop : Nat.Coprime m n) :
    ∀ k : ℕ, 0 < k → k < n → ∃ x : ℕ, x < n ∧ scaleOrbitMulMod n m x = k :=
  fun k hk₀ hk => scaleOrbitMulMod_hits_position (k := k) hn hcop hk₀ hk

/-! ## Unconditional layer 2: the additive rung is never empty (Bertrand) -/

/--
**Bertrand right-arm population (unconditional).**  Every midpoint rung
`N ≥ 2` carries a prime strictly inside `(N, 2N)`: the right arm of the
mirror is never empty.  (The endpoint `2N` is excluded because `2N ≥ 4` is
even, hence composite.)
-/
theorem bertrand_right_arm_never_empty {N : ℕ} (hN : 2 ≤ N) :
    ∃ q : ℕ, Nat.Prime q ∧ N < q ∧ q < 2 * N := by
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  rcases Nat.lt_or_ge q (2 * N) with h | h
  · exact ⟨q, hq, hlt, h⟩
  · exfalso
    have hq2N : q = 2 * N := le_antisymm hle h
    rw [hq2N] at hq
    have h2 : (2 : ℕ) ∣ 2 * N := Dvd.intro N rfl
    rcases hq.eq_one_or_self_of_dvd 2 h2 with h1 | hself
    · norm_num at h1
    · omega

/-! ## Rung localization: populated ⟺ some right-arm hit reflects prime -/

/--
**Rung localization.**  A rung is populated exactly when some prime `q ≥ N`
has a prime mirror image `2N − q`.  (No upper bound on `q` is needed: a
prime mirror forces `q ≤ 2N − 2` automatically.)
-/
theorem rung_populated_iff_reflected_prime_hit (N : ℕ) :
    0 < goldbachMidpointCount N ↔
      ∃ q : ℕ, Nat.Prime q ∧ N ≤ q ∧ Nat.Prime (2 * N - q) := by
  constructor
  · intro h
    obtain ⟨p, q, hPair⟩ := exists_midpoint_pair_of_count_pos h
    obtain ⟨hp, hq, hpN, hNq, hsum⟩ := hPair
    refine ⟨q, hq, hNq, ?_⟩
    have hpq : 2 * N - q = p := by omega
    rw [hpq]
    exact hp
  · rintro ⟨q, hq, hNq, hp⟩
    have hp2 := hp.two_le
    have hPair : GoldbachMidpointPair N (2 * N - q) q :=
      ⟨hp, hq, by omega, hNq, by omega⟩
    exact midpoint_count_pos_of_midpoint_pair hPair

/--
**Goldbach = every Bertrand-type hit ladder reflects.**  The additive
no-skip is exactly: at every rung `N ≥ 2`, some prime right-arm hit `q ≥ N`
(whose existence in `(N, 2N)` is unconditional by
`bertrand_right_arm_never_empty`, plus the diagonal `q = N` when `N` is
prime) reflects to a prime left arm `2N − q`.
-/
theorem midpoint_never_skips_iff_bertrand_hit_reflects :
    MidpointHolonomyNeverSkips ↔
      ∀ N : ℕ, 2 ≤ N →
        ∃ q : ℕ, Nat.Prime q ∧ N ≤ q ∧ Nat.Prime (2 * N - q) := by
  unfold MidpointHolonomyNeverSkips SO4ZetaHolonomyForcesMidpointPairs
  constructor
  · intro h N hN
    exact (rung_populated_iff_reflected_prime_hit N).mp (h N hN)
  · intro h N hN
    exact (rung_populated_iff_reflected_prime_hit N).mpr (h N hN)

/--
The open no-skip content localizes to composite rungs: prime midpoints are
populated by the diagonal `p = q = N` unconditionally.
-/
theorem midpoint_never_skips_iff_composite_rungs :
    MidpointHolonomyNeverSkips ↔
      ∀ N : ℕ, 2 ≤ N → ¬ Nat.Prime N → 0 < goldbachMidpointCount N := by
  unfold MidpointHolonomyNeverSkips SO4ZetaHolonomyForcesMidpointPairs
  constructor
  · intro h N hN _
    exact h N hN
  · intro h N hN
    by_cases hprime : Nat.Prime N
    · exact goldbachMidpointCount_pos_of_prime hprime
    · exact h N hN hprime

/-! ## Unconditional layer 3: the vertical rung is never half-occupied -/

/--
**Polar-partner population (FE + Schwarz).**  Every zero height also carries
the polar partner zero `1 − conj ρ` at the *same* height.  Off the line the
partner is distinct — the rung is doubled; on the line it merges.  The
vertical ladder is never half-occupied: RH decides merge versus split, not
presence.
-/
theorem zero_height_carries_polar_partner
    (hconj : ∀ t : ℂ, riemannZeta (schwarzReflect t) = schwarzReflect (riemannZeta t))
    {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    IsNontrivialZetaZero (polarPartner ρ) ∧ (polarPartner ρ).im = ρ.im := by
  have hczero : riemannZeta (schwarzReflect ρ) = 0 := by
    rw [hconj ρ, hzz.1, schwarzReflect_zero]
  have hcnt : ¬ IsTrivialNegativeEvenZeroSlot (schwarzReflect ρ) := by
    rintro ⟨n, hn⟩
    apply hzz.2.1
    refine ⟨n, ?_⟩
    have := congrArg (starRingEnd ℂ) hn
    simpa [schwarzReflect, Complex.conj_conj, map_mul, map_add, map_neg,
      map_ofNat, map_one] using this
  have hcone : schwarzReflect ρ ≠ 1 := by
    intro h1'
    apply hzz.2.2
    have := congrArg (starRingEnd ℂ) h1'
    simpa [schwarzReflect, Complex.conj_conj] using this
  have hcz : IsNontrivialZetaZero (schwarzReflect ρ) := ⟨hczero, hcnt, hcone⟩
  exact ⟨nontrivial_zero_fe_closed hcz, one_sub_schwarz_same_height ρ⟩

/--
No-double forces the polar collapse: if no height carries two zeros, the
(unconditionally present) partner must coincide with the zero itself —
single-point polar projection, i.e. RH.
-/
theorem never_doubles_forces_polar_collapse
    (hconj : ∀ t : ℂ, riemannZeta (schwarzReflect t) = schwarzReflect (riemannZeta t))
    (hU : ZeroHeightHolonomyNeverDoubles) :
    PolarProjectionCollapsesOnZeros := by
  intro ρ hzz
  have hp := zero_height_carries_polar_partner hconj hzz
  exact hU _ ρ hp.1 hzz hp.2

/-! ## Capstone: the bridge is exactly (no-double ∧ no-skip) -/

/--
**Capstone.**  The SO(8) projected half-slope bridge at threshold `2` is
equivalent to the conjunction of the two ladder laws:

* the vertical zero ladder never doubles a height (⟺ RH), and
* the additive midpoint ladder never skips a rung (⟺ Goldbach parity).

"Holonomy doesn't skip a number" is thus a faithful, zero-slack geometric
form of the joint bridge — with the unconditional halves
(`bertrand_right_arm_never_empty`, `zero_height_carries_polar_partner`,
`transport_never_skips_position`) already proved, and the open content
localized to reflect-prime hits and polar merges.
-/
theorem so8_bridge_iff_no_double_and_no_skip
    (hconj : ∀ t : ℂ, riemannZeta (schwarzReflect t) = schwarzReflect (riemannZeta t)) :
    SO8ProjectedHalfSlopeBridge 2 ↔
      (ZeroHeightHolonomyNeverDoubles ∧ MidpointHolonomyNeverSkips) := by
  rw [so8_projected_half_slope_two_iff_rh_and_goldbach_parity]
  constructor
  · rintro ⟨hRH, hG⟩
    exact ⟨(zero_never_doubles_iff_RH hconj).mpr hRH,
      midpoint_never_skips_iff_goldbach.mpr hG⟩
  · rintro ⟨hU, hS⟩
    exact ⟨(zero_never_doubles_iff_RH hconj).mp hU,
      midpoint_never_skips_iff_goldbach.mp hS⟩

/-- The ladder-law conjunction is exactly the millennium conjunction. -/
theorem no_double_and_no_skip_iff_millennium
    (hconj : ∀ t : ℂ, riemannZeta (schwarzReflect t) = schwarzReflect (riemannZeta t)) :
    (ZeroHeightHolonomyNeverDoubles ∧ MidpointHolonomyNeverSkips) ↔
      (RiemannHypothesis ∧ GoldbachParity) := by
  rw [← so8_bridge_iff_no_double_and_no_skip hconj,
    so8_projected_half_slope_two_iff_rh_and_goldbach_parity]

/--
**Honest population summary (all unconditional given Schwarz).**  Both
ladders are provably populated at every rung: the additive rung by a
Bertrand prime in `(N, 2N)`, the vertical rung by the same-height polar
partner.  What remains open is never *presence* — only reflection
(prime mirror) on the additive side and merging (polar collapse) on the
vertical side.
-/
theorem holonomy_ladders_unconditionally_populated
    (hconj : ∀ t : ℂ, riemannZeta (schwarzReflect t) = schwarzReflect (riemannZeta t)) :
    (∀ N : ℕ, 2 ≤ N → ∃ q : ℕ, Nat.Prime q ∧ N < q ∧ q < 2 * N) ∧
      (∀ ρ : ℂ, IsNontrivialZetaZero ρ →
        IsNontrivialZetaZero (polarPartner ρ) ∧ (polarPartner ρ).im = ρ.im) :=
  ⟨fun _ hN => bertrand_right_arm_never_empty hN,
    fun _ hzz => zero_height_carries_polar_partner hconj hzz⟩

end

end Hqiv.Story
