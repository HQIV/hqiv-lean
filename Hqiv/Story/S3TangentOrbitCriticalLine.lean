import Hqiv.Story.S3ZetaAxisRotationProjection
import Hqiv.Story.S3ZeroQuadrupletOrbit
import Hqiv.Story.S3SigmaReadoutScope

/-!
# Tangent law of the zero orbit: the critical line is the unimodular locus

The strip closed form carries a **factorization angle** `π s / 2`: the j/k
rotation slots are `sin(πs/2)` and `cos(πs/2)`, and their ratio
`zetaAxisRotationRatio s = tan(πs/2)` is the projection readout
(`S3ZetaAxisRotationProjection`).  This module proves the *orbit law* for that
readout under the FE + Schwarz quadruplet of `S3ZeroQuadrupletOrbit`:

* **FE inverts the tangent.**  `s ↦ 1 − s` swaps the sin and cos slots
  (`proj_sin_one_sub`, `proj_cos_one_sub`), so
  `tan(π(1−s)/2) = (tan(πs/2))⁻¹` (`projTangent_one_sub`) and the orbit
  reciprocity `tan(π(1−s)/2) · tan(πs/2) = 1` holds on the whole strip
  (`projTangent_orbit_reciprocity`).
* **Schwarz conjugates the tangent.**  `s ↦ conj s` gives
  `tan(π conj s/2) = conj(tan(πs/2))` (`projTangent_schwarz`).
* **Quadruplet tangent orbit.**  The four points of `zetaZeroQuadruplet`
  read out as `{T, T⁻¹, conj T, (conj T)⁻¹}` (`projTangent_quadruplet`).

* **The critical line is exactly the unimodular-tangent locus.**  On the
  strip, `‖tan(πs/2)‖² = 1 ↔ Re s = 1/2`
  (`normSq_projTangent_eq_one_iff`): the readout modulus is a *complete
  invariant* for the critical line.  Moreover `‖T‖` **sorts the strip**:
  `‖T‖² < 1 ↔ Re s < 1/2` and `‖T‖² > 1 ↔ Re s > 1/2`
  (`normSq_projTangent_lt_one_iff`, `one_lt_normSq_projTangent_iff`).
  The engine is the exact identity
  `‖sin(πs/2)‖² − ‖cos(πs/2)‖² = −cos(π·Re s)`
  (`normSq_proj_sin_sub_cos`): the imaginary part rides in `cosh`/`sinh`
  factors that cancel in the difference, so the modulus comparison sees only
  `Re s` — the same σ-blindness proved for the equator readout in
  `S3SigmaReadoutScope`, now at the tangent level.

* **Orbit collapse ⟺ critical line.**  Inversion equals conjugation —
  `T⁻¹ = conj T`, collapsing the quadruplet tangent orbit from four values to
  two — precisely on the critical line (`projTangent_inv_eq_conj_iff`).

* **Tie to the ζ factorization.**  The equator factor of
  `ζ = h·(2σ−1)/√2` vanishes exactly where the tangent is unimodular:
  `so4CriticalFactor s = 0 ↔ ‖tan(πs/2)‖² = 1` on the strip
  (`so4CriticalFactor_zero_iff_unimodular_tangent`), and the tangent *is* the
  slot ratio (`projTangent_eq_zetaAxisRotationRatio`).

Everything here is unconditional (no RH input): it is the geometry of the
projection, not a zero-localization claim.  What it adds to the orbit story:
the quadruplet does not merely permute points — it acts on the factorization
angle through the tangent by the group `{1, inv, conj, inv∘conj}`, and the
critical line is the fixed locus where the inversion and conjugation actions
agree.
-/

namespace Hqiv.Story

open Complex

noncomputable section

/-- The projection tangent readout `tan(π s/2)` — the j/k slot ratio of the
strip factorization, now studied as an orbit observable. -/
noncomputable def projTangent (s : ℂ) : ℂ :=
  tan (Real.pi * s / 2)

theorem projTangent_eq_tan (s : ℂ) : projTangent s = tan (Real.pi * s / 2) :=
  rfl

/-- On the strip the tangent *is* the j/k rotation ratio of
`S3ZetaAxisRotationProjection`. -/
theorem projTangent_eq_zetaAxisRotationRatio (s : ℂ) :
    projTangent s = zetaAxisRotationRatio s := by
  unfold projTangent zetaAxisRotationRatio zetaSinSlot zetaCosSlot
  rw [Complex.tan_eq_sin_div_cos]

/-! ## Strip nonvanishing of the slots -/

/-- The cosine slot never vanishes on the open strip: `cos(πs/2) = 0` forces
`s` to be an odd integer. -/
theorem proj_cos_ne_zero_of_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    cos (Real.pi * s / 2) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : s = ((2 * k + 1 : ℤ) : ℂ) := by
    have hk' : (Real.pi : ℂ) * s = (Real.pi : ℂ) * ((2 * k + 1 : ℤ) : ℂ) := by
      push_cast
      linear_combination 2 * hk
    exact mul_left_cancel₀ hπ hk'
  have hre : s.re = ((2 * k + 1 : ℤ) : ℝ) := by rw [hs, Complex.intCast_re]
  rw [hre] at h0 h1
  have h0' : (0 : ℤ) < 2 * k + 1 := by exact_mod_cast h0
  have h1' : (2 * k + 1 : ℤ) < 1 := by exact_mod_cast h1
  omega

/-- The sine slot never vanishes on the open strip: `sin(πs/2) = 0` forces
`s` to be an even integer. -/
theorem proj_sin_ne_zero_of_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    sin (Real.pi * s / 2) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : s = ((2 * k : ℤ) : ℂ) := by
    have hk' : (Real.pi : ℂ) * s = (Real.pi : ℂ) * ((2 * k : ℤ) : ℂ) := by
      push_cast
      linear_combination 2 * hk
    exact mul_left_cancel₀ hπ hk'
  have hre : s.re = ((2 * k : ℤ) : ℝ) := by rw [hs, Complex.intCast_re]
  rw [hre] at h0 h1
  have h0' : (0 : ℤ) < 2 * k := by exact_mod_cast h0
  have h1' : (2 * k : ℤ) < 1 := by exact_mod_cast h1
  omega

theorem projTangent_ne_zero_of_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    projTangent s ≠ 0 := by
  unfold projTangent
  rw [Complex.tan_eq_sin_div_cos]
  exact div_ne_zero (proj_sin_ne_zero_of_strip h0 h1) (proj_cos_ne_zero_of_strip h0 h1)

/-! ## The orbit law: FE inverts, Schwarz conjugates -/

/-- FE reflection swaps the sine slot into the cosine slot. -/
theorem proj_sin_one_sub (s : ℂ) :
    sin (Real.pi * (1 - s) / 2) = cos (Real.pi * s / 2) := by
  rw [show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 - Real.pi * s / 2 by ring]
  exact Complex.sin_pi_div_two_sub _

/-- FE reflection swaps the cosine slot into the sine slot. -/
theorem proj_cos_one_sub (s : ℂ) :
    cos (Real.pi * (1 - s) / 2) = sin (Real.pi * s / 2) := by
  rw [show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 - Real.pi * s / 2 by ring]
  exact Complex.cos_pi_div_two_sub _

/-- **FE inverts the projection tangent**: `tan(π(1−s)/2) = (tan(πs/2))⁻¹`,
unconditionally (the slot swap is exact; `inv_div` is junk-value-safe). -/
theorem projTangent_one_sub (s : ℂ) :
    projTangent (1 - s) = (projTangent s)⁻¹ := by
  unfold projTangent
  rw [Complex.tan_eq_sin_div_cos, Complex.tan_eq_sin_div_cos,
    proj_sin_one_sub, proj_cos_one_sub, inv_div]

/-- **Orbit reciprocity**: the FE pair multiplies to tangent `1` on the whole
strip — the tangent readout of the orbit `{s, 1−s}` is an inversion pair. -/
theorem projTangent_orbit_reciprocity {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    projTangent (1 - s) * projTangent s = 1 := by
  rw [projTangent_one_sub s]
  exact inv_mul_cancel₀ (projTangent_ne_zero_of_strip h0 h1)

/-- **Schwarz conjugates the projection tangent**:
`tan(π·conj s/2) = conj(tan(πs/2))`. -/
theorem projTangent_schwarz (s : ℂ) :
    projTangent (schwarzReflect s) = starRingEnd ℂ (projTangent s) := by
  unfold projTangent schwarzReflect
  rw [show (Real.pi : ℂ) * starRingEnd ℂ s / 2
      = starRingEnd ℂ (Real.pi * s / 2) by
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]]
  exact Complex.tan_conj _

/-- **Quadruplet tangent orbit**: the FE + Schwarz orbit
`{s, 1−s, conj s, 1−conj s}` reads out through the tangent as
`{T, T⁻¹, conj T, (conj T)⁻¹}` — inversion and conjugation, composed. -/
theorem projTangent_quadruplet (s : ℂ) :
    projTangent (1 - s) = (projTangent s)⁻¹ ∧
    projTangent (schwarzReflect s) = starRingEnd ℂ (projTangent s) ∧
    projTangent (1 - schwarzReflect s) = (starRingEnd ℂ (projTangent s))⁻¹ := by
  refine ⟨projTangent_one_sub s, projTangent_schwarz s, ?_⟩
  rw [projTangent_one_sub (schwarzReflect s), projTangent_schwarz s]

/-! ## The modulus identity: the difference sees only `Re s` -/

/-- Exact modulus identity for sin/cos at `a + bI`: the hyperbolic factors
cancel in the difference, leaving a function of the real part alone. -/
private theorem normSq_sin_sub_normSq_cos (a b : ℝ) :
    Complex.normSq (Complex.sin ((a : ℂ) + (b : ℂ) * Complex.I)) -
      Complex.normSq (Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I))
      = Real.sin a ^ 2 - Real.cos a ^ 2 := by
  have hs : Complex.sin ((a : ℂ) + (b : ℂ) * Complex.I)
      = ((Real.sin a * Real.cosh b : ℝ) : ℂ) +
        ((Real.cos a * Real.sinh b : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add_mul_I]
    push_cast
    ring
  have hc : Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)
      = ((Real.cos a * Real.cosh b : ℝ) : ℂ) +
        ((-(Real.sin a * Real.sinh b) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_add_mul_I]
    push_cast
    ring
  rw [hs, hc, Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]
  linear_combination (Real.sin a ^ 2 - Real.cos a ^ 2) * Real.cosh_sq b

/-- **The modulus comparison of the slots sees only `Re s`** — and is exactly
`−cos(π·Re s)`:
`‖sin(πs/2)‖² − ‖cos(πs/2)‖² = −cos(π·Re s)`.
The `Im s` content rides in common `cosh`/`sinh` factors that cancel: this is
the σ-blindness of `S3SigmaReadoutScope`, reappearing at the tangent level. -/
theorem normSq_proj_sin_sub_cos (s : ℂ) :
    Complex.normSq (sin (Real.pi * s / 2)) -
      Complex.normSq (cos (Real.pi * s / 2))
      = -Real.cos (Real.pi * s.re) := by
  have hdecomp : (Real.pi : ℂ) * s / 2
      = ((Real.pi * s.re / 2 : ℝ) : ℂ) + ((Real.pi * s.im / 2 : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im s]
    push_cast
    ring
  rw [hdecomp, normSq_sin_sub_normSq_cos]
  have h2 := Real.cos_two_mul' (Real.pi * s.re / 2)
  rw [show 2 * (Real.pi * s.re / 2) = Real.pi * s.re by ring] at h2
  linarith [h2]

/-! ## Sign of `cos(πσ)` sorts the strip -/

private theorem cos_pi_sigma_pos {σ : ℝ} (h0 : 0 < σ) (h : σ < 1 / 2) :
    0 < Real.cos (Real.pi * σ) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

private theorem cos_pi_sigma_neg {σ : ℝ} (h : 1 / 2 < σ) (h1 : σ < 1) :
    Real.cos (Real.pi * σ) < 0 := by
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

private theorem cos_pi_sigma_zero {σ : ℝ} (h : σ = 1 / 2) :
    Real.cos (Real.pi * σ) = 0 := by
  rw [h, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring]
  exact Real.cos_pi_div_two

/-! ## The critical line as the unimodular locus -/

private theorem normSq_projTangent_eq_div {s : ℂ} :
    Complex.normSq (projTangent s)
      = Complex.normSq (sin (Real.pi * s / 2)) /
        Complex.normSq (cos (Real.pi * s / 2)) := by
  unfold projTangent
  rw [Complex.tan_eq_sin_div_cos, Complex.normSq_div]

private theorem normSq_proj_cos_pos {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    0 < Complex.normSq (cos (Real.pi * s / 2)) :=
  Complex.normSq_pos.mpr (proj_cos_ne_zero_of_strip h0 h1)

/-- **The critical line is exactly the unimodular-tangent locus**: on the open
strip, `‖tan(πs/2)‖² = 1 ↔ Re s = 1/2`.  The factorization-angle readout
modulus is a complete invariant for the critical line. -/
theorem normSq_projTangent_eq_one_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    Complex.normSq (projTangent s) = 1 ↔ s.re = 1 / 2 := by
  have hpos := normSq_proj_cos_pos h0 h1
  rw [normSq_projTangent_eq_div, div_eq_one_iff_eq hpos.ne']
  have hdiff := normSq_proj_sin_sub_cos s
  constructor
  · intro h
    have hzero : Real.cos (Real.pi * s.re) = 0 := by linarith [h ▸ hdiff]
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hzero
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have hσ : s.re = (2 * (k : ℝ) + 1) / 2 := by
      have := mul_left_cancel₀ hπ.ne'
        (show Real.pi * s.re = Real.pi * ((2 * (k : ℝ) + 1) / 2) by
          rw [hk]; ring)
      linarith [this]
    rw [hσ] at h0 h1
    have h0' : (0 : ℤ) < 2 * k + 1 := by exact_mod_cast (by linarith : (0:ℝ) < 2 * (k:ℝ) + 1)
    have h1' : (2 * k + 1 : ℤ) < 2 := by exact_mod_cast (by linarith : 2 * (k:ℝ) + 1 < 2)
    have hk0 : k = 0 := by omega
    rw [hσ, hk0]
    norm_num
  · intro h
    have hzero := cos_pi_sigma_zero h
    linarith [hdiff, hzero ▸ hdiff]

/-- Left of the line the tangent is strictly inside the unit circle:
`‖tan(πs/2)‖² < 1 ↔ Re s < 1/2`. -/
theorem normSq_projTangent_lt_one_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    Complex.normSq (projTangent s) < 1 ↔ s.re < 1 / 2 := by
  have hpos := normSq_proj_cos_pos h0 h1
  rw [normSq_projTangent_eq_div, div_lt_one hpos]
  have hdiff := normSq_proj_sin_sub_cos s
  constructor
  · intro h
    by_contra hge
    push_neg at hge
    rcases eq_or_lt_of_le hge with heq | hlt
    · have := cos_pi_sigma_zero heq.symm
      linarith
    · have := cos_pi_sigma_neg hlt h1
      linarith
  · intro h
    have := cos_pi_sigma_pos h0 h
    linarith

/-- Right of the line the tangent is strictly outside the unit circle:
`1 < ‖tan(πs/2)‖² ↔ 1/2 < Re s`.  Together with the previous two lemmas,
the tangent modulus **sorts the strip** around the critical line. -/
theorem one_lt_normSq_projTangent_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    1 < Complex.normSq (projTangent s) ↔ 1 / 2 < s.re := by
  have hpos := normSq_proj_cos_pos h0 h1
  rw [normSq_projTangent_eq_div, one_lt_div hpos]
  have hdiff := normSq_proj_sin_sub_cos s
  constructor
  · intro h
    by_contra hge
    push_neg at hge
    rcases eq_or_lt_of_le hge with heq | hlt
    · have := cos_pi_sigma_zero heq
      linarith
    · have := cos_pi_sigma_pos h0 hlt
      linarith
  · intro h
    have := cos_pi_sigma_neg h h1
    linarith

/-! ## Orbit collapse ⟺ critical line -/

/-- **Inversion = conjugation exactly on the critical line.**  The FE action
(`T ↦ T⁻¹`) and the Schwarz action (`T ↦ conj T`) on the projection tangent
agree precisely when `Re s = 1/2`: the quadruplet tangent orbit
`{T, T⁻¹, conj T, (conj T)⁻¹}` collapses to `{T, conj T}` on the line, and
only there.  This is the tangent-level mechanism behind the critical line:
it is the fixed locus where the two orbit symmetries become one. -/
theorem projTangent_inv_eq_conj_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (projTangent s)⁻¹ = starRingEnd ℂ (projTangent s) ↔ s.re = 1 / 2 := by
  have hT := projTangent_ne_zero_of_strip h0 h1
  rw [← normSq_projTangent_eq_one_iff h0 h1]
  constructor
  · intro h
    have hmul : projTangent s * (projTangent s)⁻¹
        = projTangent s * starRingEnd ℂ (projTangent s) := by rw [h]
    rw [mul_inv_cancel₀ hT, Complex.mul_conj] at hmul
    exact_mod_cast hmul.symm
  · intro h
    have hmul : projTangent s * starRingEnd ℂ (projTangent s) = 1 := by
      rw [Complex.mul_conj, h]
      norm_num
    calc (projTangent s)⁻¹
        = (projTangent s)⁻¹ * (projTangent s * starRingEnd ℂ (projTangent s)) := by
          rw [hmul, mul_one]
      _ = starRingEnd ℂ (projTangent s) := by
          rw [← mul_assoc, inv_mul_cancel₀ hT, one_mul]

/-! ## Tie to the ζ factorization -/

/-- **The equator factor vanishes exactly where the tangent is unimodular**:
on the strip, `so4CriticalFactor s = 0 ↔ ‖tan(πs/2)‖² = 1`.  The
pointwise-vanishing locus of the factorization `ζ = h·(2σ−1)/√2` — the RH
locus — is the unimodular locus of the factorization-angle tangent. -/
theorem so4CriticalFactor_zero_iff_unimodular_tangent {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    so4CriticalFactor s = 0 ↔ Complex.normSq (projTangent s) = 1 := by
  rw [normSq_projTangent_eq_one_iff h0 h1]
  unfold so4CriticalFactor
  rw [Complex.ofReal_eq_zero]
  exact exact_twiddle_zero_iff_on_line s

end

end Hqiv.Story
