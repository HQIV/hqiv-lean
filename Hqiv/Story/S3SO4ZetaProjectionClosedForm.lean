import Hqiv.Story.S3SO4InteriorWitness
import Hqiv.Story.S3ClosureDeltaLiftBridge
import Hqiv.Algebra.OctonionSphereConstruction
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# `ζ(s)` as SO(4) projections to the complex plane

The functional-equation pair `(σ, 1−σ)` is rotated at **45°** (`θ = π/4`).  At that
angle Mathlib proves

`cos(π/4) = sin(π/4) = √2/2`,

so the diagonal and equator channels split the `cos+sin = √2` budget equally.  The
**diagonal** projection is the fixed even carrier (`1/√2`); the **equator**
projection is the odd sin/cos carrier (`(2σ−1)/√2`).

On the **8-dimensional SO(4) shell** (`OctonionSphereConstruction`), the unit
7-sphere area proxy is `π⁴/3`; the **45° equator half** is therefore

`π⁴/6 = (π⁴/3) / 2`.

This is the geometric π⁴/6 slot.  The classical even zeta value

`ζ(2) = π²/6`

is the **π²-sector** analogue (Bernoulli `B₂ = 1/6`, not `π⁴`).

## Regional closed forms (all proved against Mathlib)

| Region | SO(4) channel | Closed form |
|--------|---------------|-------------|
| `Re > 1` | even / Dirichlet | `∑ 1/(n+1)^s` |
| `0 < Re < 1` | odd / sin–cos–Γ | FE assembly (`oddStripChannel`) |
| even `2k ≥ 2` | π-sector | `ζ(2k) = (−1)^{k+1} 2^{2k−1} π^{2k} B_{2k}/(2k)!` |
| `−k` negative | Bernoulli | `ζ(−k) = −B'_{k+1}/(k+1)` |
| positive odd `≥ 3` | odd continuation | no elementary closed form (Apéry slot) |
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## 45° SO(4) rotation projectors to `ℂ` -/

/-- Exact 45° cosine slot (`√2/2`). -/
noncomputable def so4Cos45 : ℝ :=
  Real.sqrt 2 / 2

/-- Exact 45° sine slot (`√2/2`). -/
noncomputable def so4Sin45 : ℝ :=
  Real.sqrt 2 / 2

theorem so4Cos45_eq_cos_pi_div_four : so4Cos45 = Real.cos (Real.pi / 4) :=
  Real.cos_pi_div_four.symm

theorem so4Sin45_eq_sin_pi_div_four : so4Sin45 = Real.sin (Real.pi / 4) :=
  Real.sin_pi_div_four.symm

theorem so4Cos45_eq_sin45 : so4Cos45 = so4Sin45 := by
  rw [so4Cos45_eq_cos_pi_div_four, so4Sin45_eq_sin_pi_div_four, Real.cos_pi_div_four,
    Real.sin_pi_div_four]

/-- At 45° the sin and cos slots are equal; their sum is `√2` (not `π`). -/
theorem so4Cos45_add_sin45 : so4Cos45 + so4Sin45 = Real.sqrt 2 := by
  rw [so4Cos45_eq_cos_pi_div_four, so4Sin45_eq_sin_pi_div_four]
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith [h2]

/-- Diagonal SO(4) projection of `(σ, 1−σ)` to `ℂ` (even / fixed channel). -/
noncomputable def so4DiagProject (s : ℂ) : ℂ :=
  (rot45Diag (functionalPair s.re) : ℂ)

/-- Equator SO(4) projection to `ℂ` (odd / sin–cos carrier). -/
noncomputable def so4EquatorProject (s : ℂ) : ℂ :=
  (rot45Free (functionalPair s.re) : ℂ)

theorem so4DiagProject_eq_inv_sqrt_two (s : ℂ) :
    so4DiagProject s = (1 / Real.sqrt 2 : ℂ) := by
  simp [so4DiagProject, rot45Diag_functionalPair]

theorem so4EquatorProject_eq_critical_factor (s : ℂ) :
    so4EquatorProject s = so4CriticalFactor s := by
  simp [so4EquatorProject, so4CriticalFactor, exactTwiddleReadout]

/-- sin/cos ratio line from general twiddle angle (45° pins `1/2`). -/
noncomputable def so4SinCosRatio (θ : ℝ) : ℝ :=
  projectionLine θ

theorem so4SinCosRatio_pi_div_four : so4SinCosRatio (Real.pi / 4) = (1 / 2 : ℝ) :=
  projectionLine_pi_div_four

/-! ## Origin / real-one anchors and doubled critical-line readout -/

/-- The real two-plane used for the SO(4) projection-to-`ℂ` readout. -/
abbrev SO4ReadoutPoint := ℝ × ℝ

/-- Origin anchor of the projected SO(4) readout plane. -/
def so4ReadoutOrigin : SO4ReadoutPoint :=
  (0, 0)

/-- Real-unit anchor of the projected SO(4) readout plane. -/
def so4ReadoutRealOne : SO4ReadoutPoint :=
  (1, 0)

/--
The doubled complex-plane readout.

For a critical-line point `s = 1/2 + i t`, this sends the real coordinate to
`1` and the height to `2t`.  Thus the first nontrivial zero at height `t₁`
would project to the endpoint `(1, 2t₁)`, numerically `(1, ~28.27)`.
-/
def so4DoubledComplexReadout (s : ℂ) : SO4ReadoutPoint :=
  (2 * s.re, 2 * s.im)

/--
The SO(4) tangent/readout transformation.

This is the construction-level version of `so4DoubledComplexReadout`: first
take the functional-equation pair `(σ, 1 - σ)`, rotate it by 45°, then normalize
the fixed diagonal slot by `√2`; the vertical coordinate is the doubled strip
height.
-/
noncomputable def so4TangentReadoutFromRotation (s : ℂ) : SO4ReadoutPoint :=
  (Real.sqrt 2 * rot45Diag (functionalPair s.re), 2 * s.im)

/--
The tangent/readout transformation lands on the real-one vertical line for every
functional-equation pair: the normalized diagonal slot is exactly `1`.
-/
theorem so4TangentReadoutFromRotation_fst_eq_one (s : ℂ) :
    (so4TangentReadoutFromRotation s).1 = 1 := by
  simp [so4TangentReadoutFromRotation, rot45Diag_functionalPair]

/--
On the critical line, the doubled complex readout and the SO(4) rotated tangent
readout are the same point.
-/
theorem so4DoubledComplexReadout_eq_tangentReadout_on_critical
    {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) :
    so4DoubledComplexReadout s = so4TangentReadoutFromRotation s := by
  ext <;> simp [so4DoubledComplexReadout, so4TangentReadoutFromRotation,
    rot45Diag_functionalPair, hs]

/--
Exact tangent endpoint form from the SO(4) rotation-normalization map.
-/
theorem so4TangentReadoutFromRotation_eq_real_one_height
    {s : ℂ} {t : ℝ} (him : s.im = t) :
    so4TangentReadoutFromRotation s = (1, 2 * t) := by
  ext
  · exact so4TangentReadoutFromRotation_fst_eq_one s
  · simp [so4TangentReadoutFromRotation, him]

/--
The SO(4) tangent/readout map factors through the critical equator precisely
when the free rotated coordinate vanishes.
-/
theorem so4_tangent_readout_through_critical_equator_iff (s : ℂ) :
    rot45Free (functionalPair s.re) = 0 ↔ s.re = (1 / 2 : ℝ) :=
  rot45Free_re_pair_eq_zero_iff s

/-- The doubled readout always has real coordinate `2 * Re(s)`. -/
theorem so4DoubledComplexReadout_fst (s : ℂ) :
    (so4DoubledComplexReadout s).1 = 2 * s.re :=
  rfl

/-- The doubled readout always has height coordinate `2 * Im(s)`. -/
theorem so4DoubledComplexReadout_snd (s : ℂ) :
    (so4DoubledComplexReadout s).2 = 2 * s.im :=
  rfl

/--
On the critical line, the doubled readout lands on the real-one vertical
through `x = 1`.
-/
theorem so4DoubledComplexReadout_real_eq_one_of_critical
    {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) :
    (so4DoubledComplexReadout s).1 = 1 := by
  simp [so4DoubledComplexReadout, hs]

/--
Exact endpoint form for a critical-line point of height `t`: `(1, 2t)`.
-/
theorem so4DoubledComplexReadout_eq_real_one_height
    {s : ℂ} {t : ℝ}
    (hre : s.re = (1 / 2 : ℝ)) (him : s.im = t) :
    so4DoubledComplexReadout s = (1, 2 * t) := by
  ext <;> simp [so4DoubledComplexReadout, hre, him]

/--
Slope of the line from the origin to a projected readout point.

This is intentionally just the affine complex-plane slope; it is separate from
the `1/2` midpoint slope in the Goldbach tangent channel.
-/
noncomputable def so4OriginLineSlope (P : SO4ReadoutPoint) : ℝ :=
  P.2 / P.1

/--
For a critical-line endpoint `(1, 2t)`, the origin-line slope is exactly `2t`.
-/
theorem so4_origin_line_slope_doubled_critical_eq_two_height
    {s : ℂ} {t : ℝ}
    (hre : s.re = (1 / 2 : ℝ)) (him : s.im = t) :
    so4OriginLineSlope (so4DoubledComplexReadout s) = 2 * t := by
  rw [so4DoubledComplexReadout_eq_real_one_height hre him]
  simp [so4OriginLineSlope]

/--
Named first-zero readout payload: if a first-zero height `t₁` is supplied by an
analytic certificate, the SO(4) doubled endpoint is `(1, 2t₁)` and the line from
the origin has slope `2t₁`.
-/
structure SO4FirstZeroOriginLineReadout where
  height : ℝ
  zero_point : ℂ
  on_critical_line : zero_point.re = (1 / 2 : ℝ)
  height_eq : zero_point.im = height
  zeta_zero : riemannZeta zero_point = 0
  doubled_endpoint :
    so4DoubledComplexReadout zero_point = (1, 2 * height)
  origin_line_slope :
    so4OriginLineSlope (so4DoubledComplexReadout zero_point) = 2 * height

/-- Package a critical-line zero into the origin-line doubled-readout certificate. -/
def so4_first_zero_origin_line_readout_of_critical_zero
    {s : ℂ} {t : ℝ}
    (hre : s.re = (1 / 2 : ℝ)) (him : s.im = t)
    (hz : riemannZeta s = 0) :
    SO4FirstZeroOriginLineReadout :=
  { height := t
    zero_point := s
    on_critical_line := hre
    height_eq := him
    zeta_zero := hz
    doubled_endpoint := so4DoubledComplexReadout_eq_real_one_height hre him
    origin_line_slope := so4_origin_line_slope_doubled_critical_eq_two_height hre him }

/-! ## π⁴/6 from the SO(4) 8-shell equator halving -/

/-- Unit 7-sphere area proxy on the SO(4) 8-shell (`π⁴/3`). -/
noncomputable def so4UnitSphereArea : ℝ :=
  Hqiv.Algebra.continuousSphereArea7 1

theorem so4UnitSphereArea_eq_pi_four_thirds :
    so4UnitSphereArea = Real.pi ^ 4 / 3 := by
  unfold so4UnitSphereArea Hqiv.Algebra.continuousSphereArea7
  ring

/-- 45° equator half of the unit sphere area: `π⁴/6`. -/
noncomputable def so4EquatorHalfArea : ℝ :=
  so4UnitSphereArea / 2

theorem so4EquatorHalfArea_eq_pi_four_sixths :
    so4EquatorHalfArea = Real.pi ^ 4 / 6 := by
  rw [so4EquatorHalfArea, so4UnitSphereArea_eq_pi_four_thirds]
  ring

theorem pi_four_sixths_from_cos_sin_half_split :
    Real.pi ^ 4 / 6 = (Real.pi ^ 4 / 3) / 2 := by
  ring

/-! ## Even π-sector closed forms (positive even integers) -/

/--
Even-sector SO(4) π-projection closed form for `ζ(2k)`, `k ≥ 1`.
Uses the Mathlib Bernoulli/π identity (`riemannZeta_two_mul_nat`).
-/
noncomputable def zetaEvenSO4ClosedForm (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) *
    bernoulli (2 * k) / Nat.factorial (2 * k)

theorem zeta_even_so4_closed_form {k : ℕ} (hk : k ≠ 0) :
    riemannZeta (2 * k) = zetaEvenSO4ClosedForm k := by
  unfold zetaEvenSO4ClosedForm
  exact riemannZeta_two_mul_nat hk

/-- `ζ(2) = π²/6`: π-sector even value (Bernoulli `B₂ = 1/6`). -/
theorem riemannZeta_two_so4_pi_sector :
    riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 := by
  simpa using riemannZeta_two

theorem riemannZeta_two_eq_even_so4_closed_form :
    riemannZeta 2 = zetaEvenSO4ClosedForm 1 := by
  simpa [two_mul, Nat.cast_one] using zeta_even_so4_closed_form (k := 1) (by decide)

theorem bernoulli_two_is_sixth : bernoulli 2 = 6⁻¹ := bernoulli_two

theorem zeta_two_bernoulli_sixth :
    riemannZeta 2 = (Real.pi : ℂ) ^ 2 * (bernoulli 2 : ℂ) := by
  rw [riemannZeta_two_so4_pi_sector, bernoulli_two_is_sixth]
  ring

/-- `ζ(4) = π⁴/90` (even π-sector; denominator 90, not 6). -/
theorem riemannZeta_four_so4_pi_sector :
    riemannZeta 4 = (Real.pi : ℂ) ^ 4 / 90 := by
  simpa using riemannZeta_four

theorem riemannZeta_four_eq_even_so4_closed_form :
    riemannZeta (2 * 2) = zetaEvenSO4ClosedForm 2 :=
  zeta_even_so4_closed_form (k := 2) (by decide)

/-! ## Odd-sector closed forms -/

/--
Odd strip / fractional values (`0 < Re s < 1`): sin/cos–Γ–π FE projection
(`oddStripChannel` = `ζ` on the strip).
-/
noncomputable def zetaFractionalSO4ClosedForm (s : ℂ) : ℂ :=
  oddStripChannel s

theorem zeta_fractional_so4_eq_zeta
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zetaFractionalSO4ClosedForm s = riemannZeta s :=
  oddStripChannel_eq_zeta h0 h1

/-- Negative-integer slots: Bernoulli closed form (odd negatives are nonzero, not zeros). -/
theorem zeta_neg_so4_bernoulli (k : ℕ) :
    riemannZeta (-k) = -bernoulli' (k + 1) / (k + 1) :=
  riemannZeta_bernoulli_neg_closed_form k

/--
Positive odd integers `ζ(2n+1)` (e.g. `ζ(3)`) have **no** elementary closed form in
Mathlib; the plastic / Apéry continuation slot lives in `PlasticSpiralInterceptCoverage`.
-/
def OddPositiveZetaSO4ClosedFormSlot (_n : ℕ) : Prop :=
  True

/-! ## Right half-plane even channel -/

/-- `Re > 1` even/Dirichlet channel (shell sum). -/
noncomputable def zetaEvenDirichletSO4 (s : ℂ) : ℂ :=
  ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s

theorem zeta_even_dirichlet_so4_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    zetaEvenDirichletSO4 s = riemannZeta s :=
  (riemannZeta_dirichlet_closed_form s hs).symm

/-! ## Master projected readout (region theorems above) -/

/--
**Packaging.** `zetaSO4Projected s` is `ζ(s)` with the regional closed-form
characterizations proved in this module as `zeta_*_so4_*` theorems.
-/
noncomputable def zetaSO4Projected (s : ℂ) : ℂ :=
  riemannZeta s

theorem zetaSO4Projected_eq_zeta (s : ℂ) : zetaSO4Projected s = riemannZeta s := rfl

/--
Off the critical line on the open strip, `ζ` is the odd sin/cos channel; normalized
by the equator projection it matches `interiorStripH`.
-/
theorem zetaSO4Projected_eq_sin_cos_channel_off_line
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hσ : s.re ≠ (1 / 2 : ℝ)) :
    zetaSO4Projected s = so4EquatorProject s * interiorStripH s := by
  have hζ : oddStripChannel s = riemannZeta s := oddStripChannel_eq_zeta h0 h1
  have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
  suffices so4EquatorProject s * interiorStripH s = riemannZeta s from this.symm
  calc so4EquatorProject s * interiorStripH s
      = so4CriticalFactor s * (riemannZeta s / so4CriticalFactor s) := by
        unfold interiorStripH evenStripChannel
        rw [so4EquatorProject_eq_critical_factor, hζ]
        simp [zero_add]
    _ = riemannZeta s := mul_div_cancel₀ _ hcf

end

end Hqiv.Story
