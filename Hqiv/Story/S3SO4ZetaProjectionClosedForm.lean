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
