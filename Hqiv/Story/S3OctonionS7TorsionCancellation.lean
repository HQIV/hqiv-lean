import Hqiv.Story.S3OctonionicAssociatorChannel

/-!
# S⁷ torsion cancellation: the SO(8) twist on the associator channel

The associator channel gave a positive scalar; this module keeps the full
**torsion vector** in the octonion carrier ℝ⁸ and asks where it *cancels*
between functional-equation partners.  The unit sphere of the carrier is
S⁷ and the rotation group is SO(8), whose complete invariant on ℝ⁸ is the
norm — so "same SO(8) orbit" is exactly "same norm sphere," and the S⁷
geometry of the torsion is fully captured by ray + radius.

## Proved here

* **The torsion projects to a single point of S⁷**
  (`octTorsionVector_eq`, `octTorsion_single_point_on_s7`): for every
  spectral parameter the torsion vector is a *positive* multiple of the
  fixed direction `−e₃ − e₄`.  The whole spectral flow is radial in the
  carrier; the S⁷ shadow never moves.  All the information sits in the
  scalar weight `(abc)^{−σ}`.
* **FE weight gap and antisymmetry**
  (`octTorsionDefect_eq`, `octTorsionDefect_antisymm`): the defect
  between FE partners is `gap • (−e₃ − e₄)` with
  `gap = (abc)^{−σ} − (abc)^{−(1−σ)}`, and it is odd under `s ↦ 1−s`.
* **Cancellation law** (`octTorsionDefect_zero_iff`): the torsion of `s`
  and the torsion of `1−s` cancel **iff** `Re s = 1/2`.  On the critical
  line — and only there — the FE pair carries identical torsion vectors.
* **Chirality flip** (`octTorsionWeightGap_pos_iff`,
  `octTorsionWeightGap_neg_iff`): the defect points along `−e₃ − e₄` for
  `σ < 1/2` and along `+e₃ + e₄` for `σ > 1/2`.  The critical line is the
  unique chirality-neutral locus — the CP-odd signature of the channel.
* **SO(8) orbit law** (`octTorsion_so8_orbit_iff`): the FE partners'
  torsion vectors lie on a common norm sphere (= common SO(8) orbit, the
  norm being the complete invariant) iff `Re s = 1/2`; and since both
  vectors sit on the *same ray*, orbit coincidence already forces vector
  equality (`octTorsion_orbit_eq_iff_collapse`).
* **RH as S⁷ torsion cancellation**
  (`RH_iff_zero_torsion_cancellation`): RH ⟺ at every nontrivial zero
  the FE torsion defect vanishes for every triple.

## Honest scope

The additional twist sharpens the geometry but does not change the
logical status: because the S⁷ direction is constant, cancellation is
governed by the radial weight alone, and the radial weight is σ-driven —
so "torsion cancels at every zero" is exactly RH, with zero slack.  The
genuinely new unconditional content is the rigidity (single S⁷ point, odd
defect, chirality flip) and the orbit form of the locator.  Note the
frozen-table caveat recorded in `AGENTS/OCTONION_TABLE_AUDIT_TODO.md`:
the witness direction `−e₃ − e₄` is specific to the current tables.
-/

namespace Hqiv.Story

open Complex Hqiv.Algebra Hqiv.Geometry

noncomputable section

/-- **The torsion vector**: the associator of the prime-weighted triple,
kept as a vector in the octonion carrier ℝ⁸. -/
noncomputable def octTorsionVector (a b c : ℕ) (s : ℂ) : OctonionVec :=
  octonionAssociator
    (‖so4SpectralLine a s‖ • e1)
    (‖so4SpectralLine b s‖ • e2)
    (‖so4SpectralLine c s‖ • e4)

/-- **The FE weight gap**: the difference of radial torsion weights
between functional-equation partners. -/
noncomputable def octTorsionWeightGap (a b c : ℕ) (s : ℂ) : ℝ :=
  ((a * b * c : ℕ) : ℝ) ^ (-s.re) - ((a * b * c : ℕ) : ℝ) ^ (-(1 - s.re))

/-- **The FE torsion defect**: the failure of the torsion of `s` and the
torsion of `1 − s` to cancel in the carrier. -/
noncomputable def octTorsionDefect (a b c : ℕ) (s : ℂ) : OctonionVec :=
  octTorsionVector a b c s - octTorsionVector a b c (1 - s)

/-- Joint spectral weight collapses to a single rpow of the product. -/
private theorem weight_product {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (r : ℝ) :
    ((a : ℝ)) ^ r * ((b : ℝ)) ^ r * ((c : ℝ)) ^ r =
      ((a * b * c : ℕ) : ℝ) ^ r := by
  have _ := ha; have _ := hb; have _ := hc
  push_cast
  rw [← Real.mul_rpow (by positivity) (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity)]

/-- **Closed form of the torsion vector**: a positive radial weight times
the fixed carrier direction `−e₃ − e₄`. -/
theorem octTorsionVector_eq {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (s : ℂ) :
    octTorsionVector a b c s =
      (((a * b * c : ℕ) : ℝ) ^ (-s.re)) • (-e3 - e4 : OctonionVec) := by
  unfold octTorsionVector
  rw [octonionAssociator_smul, octonionAssociator_e1_e2_e4,
    so4SpectralLine_norm ha, so4SpectralLine_norm hb,
    so4SpectralLine_norm hc, weight_product ha hb hc]

/-- The torsion's squared carrier norm is the associator channel. -/
theorem octTorsionVector_normSq (a b c : ℕ) (s : ℂ) :
    (∑ i : Fin 8, (octTorsionVector a b c s i) ^ 2) =
      octAssociatorChannel a b c s := rfl

/-- **The S⁷ shadow never moves**: at every spectral parameter the
torsion is a positive multiple of one fixed direction.  The whole flow is
radial; S⁷ sees a single point. -/
theorem octTorsion_single_point_on_s7 {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (s : ℂ) :
    ∃ w : ℝ, 0 < w ∧
      octTorsionVector a b c s = w • (-e3 - e4 : OctonionVec) := by
  refine ⟨((a * b * c : ℕ) : ℝ) ^ (-s.re), ?_, octTorsionVector_eq ha hb hc s⟩
  have habc : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos ha hb) hc
  exact Real.rpow_pos_of_pos habc _

/-- **Closed form of the FE defect**: weight gap times the fixed
direction. -/
theorem octTorsionDefect_eq {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (s : ℂ) :
    octTorsionDefect a b c s =
      octTorsionWeightGap a b c s • (-e3 - e4 : OctonionVec) := by
  unfold octTorsionDefect octTorsionWeightGap
  have hre : (1 - s).re = 1 - s.re := by
    simp [Complex.sub_re, Complex.one_re]
  rw [octTorsionVector_eq ha hb hc, octTorsionVector_eq ha hb hc, hre,
    sub_smul]

/-- **The defect is FE-odd**: reflecting `s ↦ 1−s` flips the defect
(unconditionally — no positivity needed). -/
theorem octTorsionDefect_antisymm (a b c : ℕ) (s : ℂ) :
    octTorsionDefect a b c (1 - s) = -(octTorsionDefect a b c s) := by
  unfold octTorsionDefect
  rw [show (1 : ℂ) - (1 - s) = s by ring]
  exact (neg_sub _ _).symm

/-- The weight gap vanishes exactly on the critical line. -/
theorem octTorsionWeightGap_zero_iff {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) {s : ℂ} :
    octTorsionWeightGap a b c s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  have ha0 : 0 < a := by omega
  have habcN : 2 ≤ a * b * c := by
    have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have h2 : a * b ≤ a * b * c := Nat.le_mul_of_pos_right (a * b) hc
    omega
  have hX : (1 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast habcN)
  unfold octTorsionWeightGap
  rw [sub_eq_zero]
  constructor
  · intro h
    have := rpow_left_inj_of_one_lt hX h
    linarith
  · intro h
    rw [h]
    norm_num

/-- **Chirality, left side**: for `σ < 1/2` the defect weight is
positive — the defect points along `−e₃ − e₄`. -/
theorem octTorsionWeightGap_pos_iff {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) {s : ℂ} :
    0 < octTorsionWeightGap a b c s ↔ s.re < (1 / 2 : ℝ) := by
  have habcN : 2 ≤ a * b * c := by
    have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have h2 : a * b ≤ a * b * c := Nat.le_mul_of_pos_right (a * b) hc
    omega
  have hX : (1 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast habcN)
  unfold octTorsionWeightGap
  rw [sub_pos, Real.rpow_lt_rpow_left_iff hX]
  constructor <;> intro h <;> linarith

/-- **Chirality, right side**: for `σ > 1/2` the defect weight is
negative — the defect points along `+e₃ + e₄`.  Together with the
positive side, the critical line is the unique chirality-neutral locus of
the torsion defect. -/
theorem octTorsionWeightGap_neg_iff {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) {s : ℂ} :
    octTorsionWeightGap a b c s < 0 ↔ (1 / 2 : ℝ) < s.re := by
  have habcN : 2 ≤ a * b * c := by
    have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have h2 : a * b ≤ a * b * c := Nat.le_mul_of_pos_right (a * b) hc
    omega
  have hX : (1 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast habcN)
  unfold octTorsionWeightGap
  rw [sub_neg, Real.rpow_lt_rpow_left_iff hX]
  constructor <;> intro h <;> linarith

/-- **Torsion cancellation law**: the FE partners' torsion vectors cancel
in the carrier exactly on the critical line. -/
theorem octTorsionDefect_zero_iff {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) {s : ℂ} :
    octTorsionDefect a b c s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  have ha0 : 0 < a := by omega
  rw [octTorsionDefect_eq ha0 hb hc]
  constructor
  · intro h
    have h3 : octTorsionWeightGap a b c s *
        ((-e3 - e4 : OctonionVec) 3) = 0 := congrFun h 3
    have hu : ((-e3 - e4 : OctonionVec)) 3 = -1 := by
      show -(if (3 : Fin 8) = 3 then (1 : ℝ) else 0) -
        (if (3 : Fin 8) = 4 then (1 : ℝ) else 0) = -1
      rw [if_pos rfl, if_neg (by decide : ¬(3 : Fin 8) = 4)]
      norm_num
    rw [hu] at h3
    have hg : octTorsionWeightGap a b c s = 0 := by linarith
    exact (octTorsionWeightGap_zero_iff ha hb hc).mp hg
  · intro h
    rw [(octTorsionWeightGap_zero_iff ha hb hc).mpr h, zero_smul]

/-- **SO(8) orbit law**: the norm being the complete SO(8) invariant on
the carrier, the FE partners' torsion vectors lie on a common orbit
(equal squared norms, i.e. equal channels) exactly on the critical
line. -/
theorem octTorsion_so8_orbit_iff {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) {s : ℂ} :
    octAssociatorChannel a b c s = octAssociatorChannel a b c (1 - s) ↔
      s.re = (1 / 2 : ℝ) := by
  have ha0 : 0 < a := by omega
  have habcN : 2 ≤ a * b * c := by
    have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have h2 : a * b ≤ a * b * c := Nat.le_mul_of_pos_right (a * b) hc
    omega
  have hX : (1 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast habcN)
  have hre : (1 - s).re = 1 - s.re := by
    simp [Complex.sub_re, Complex.one_re]
  rw [octAssociatorChannel_eq ha0 hb hc, octAssociatorChannel_eq ha0 hb hc,
    hre]
  constructor
  · intro h
    have h' := mul_left_cancel₀ (two_ne_zero (α := ℝ)) h
    have := rpow_left_inj_of_one_lt hX h'
    linarith
  · intro h
    rw [h]
    norm_num

/-- **Orbit coincidence is already vector collapse**: because both
torsion vectors sit on the same ray of the carrier, lying on a common
SO(8) orbit forces them to be *equal* — and either statement is the
critical line. -/
theorem octTorsion_orbit_eq_iff_collapse {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) {s : ℂ} :
    (octAssociatorChannel a b c s = octAssociatorChannel a b c (1 - s)) ↔
      octTorsionVector a b c s = octTorsionVector a b c (1 - s) := by
  rw [octTorsion_so8_orbit_iff ha hb hc]
  constructor
  · intro h
    have hd := (octTorsionDefect_zero_iff ha hb hc).mpr h
    unfold octTorsionDefect at hd
    exact sub_eq_zero.mp hd
  · intro h
    have hd : octTorsionDefect a b c s = 0 := by
      unfold octTorsionDefect
      rw [h, sub_self]
    exact (octTorsionDefect_zero_iff ha hb hc).mp hd

/-- **RH as S⁷ torsion cancellation**: RH ⟺ at every nontrivial zero
the FE torsion defect vanishes for every triple — the zeros are exactly
the points where the SO(8) twist closes the torsion loop. -/
theorem RH_iff_zero_torsion_cancellation :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, IsNontrivialZetaZero ρ → ∀ a b c : ℕ, 2 ≤ a → 0 < b → 0 < c →
        octTorsionDefect a b c ρ = 0 := by
  constructor
  · intro hRH ρ hz a b c ha hb hc
    exact (octTorsionDefect_zero_iff ha hb hc).mpr
      (hRH ρ hz.1 hz.2.1 hz.2.2)
  · intro hW ρ hz hnt h1
    exact (octTorsionDefect_zero_iff (le_refl 2) one_pos one_pos).mp
      (hW ρ ⟨hz, hnt, h1⟩ 2 1 1 (le_refl 2) one_pos one_pos)

end

end Hqiv.Story
