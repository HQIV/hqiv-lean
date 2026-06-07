import Hqiv.Story.S3SixPolesResidual
import Hqiv.Story.S3SO4ZetaProjectionClosedForm
import Hqiv.Story.S3ZetaClosedForm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# ζ projection: j/k rotations cancel at even π-slots; odd/fractional carry ratios

The functional-equation odd channel carries

`cos(π·s/2)`  and  `sin(π·s/2)`

as the complex-plane projection of the SO(4) twiddle.  Read these as the **j/k
rotation slots** on the quaternion shell:

* **i-axis** — diagonal / even carrier (`1/√2`, fixed under FE reflection);
* **j-axis** — sine slot;
* **k-axis** — cosine slot.

## Even ζ-sector (exact multiples of `π` in the `π·s/2` angle)

At **even** integers `s = 2k` the angle is `k·π`:

`sin(π·s/2) = sin(kπ) = 0`  — j/k rotations **cancel** (sin channel vanishes);
`cos(π·s/2) = cos(kπ) = (−1)^k` — cosine lands on a **full turn** residue.

This is the π-sector of `ζ(2k)` (Bernoulli / `π^{2k}` closed forms): the even
values are pure π-powers because the sin/j–k content has rotated away.

## Odd and fractional sectors (rotation ratios survive)

At **odd** integers `s = 2k+1` the angle is `(k + 1/2)·π`:

`cos(π·s/2) = 0`  — cosine slot cancels;
`sin(π·s/2) = (−1)^k` — sine carries the full residue (Apéry / plastic slot).

On the **open strip** (`0 < Re s < 1`, non-integer) both slots are generally
nonzero: the **rotation ratio**

`tan(π·s/2) = sin(π·s/2) / cos(π·s/2)`

is the fractional projection (`so4SinCosRatio` at general twiddle angles).

The six S³ poles `±i, ±j, ±k` realize the axis projections; antipodal pairs
cancel as orbits (`headTail_orbit_pair_cancels`) while single-axis poles survive
with `±1/√2` residuals.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real

/-! ## Quaternion axis projectors (j / k slots) -/

/-- j-axis projection to the 45° critical readout. -/
noncomputable def jAxisProj (p : QuaternionCoords) : ℝ :=
  p 2 / Real.sqrt 2

/-- k-axis projection to the 45° critical readout. -/
noncomputable def kAxisProj (p : QuaternionCoords) : ℝ :=
  p 3 / Real.sqrt 2

/-- i-axis projection to the 45° critical readout. -/
noncomputable def iAxisProj (p : QuaternionCoords) : ℝ :=
  p 1 / Real.sqrt 2

theorem jAxisProj_poleJplus : jAxisProj poleJplus = 1 / Real.sqrt 2 := by
  simp [jAxisProj, poleJplus]

theorem kAxisProj_poleKplus : kAxisProj poleKplus = 1 / Real.sqrt 2 := by
  simp [kAxisProj, poleKplus]

theorem jAxisProj_poleJminus : jAxisProj poleJminus = -(1 / Real.sqrt 2) := by
  simp [jAxisProj, poleJminus]
  ring

theorem kAxisProj_poleKminus : kAxisProj poleKminus = -(1 / Real.sqrt 2) := by
  simp [kAxisProj, poleKminus]
  ring

/-- Antipodal j-poles cancel as an orbit pair. -/
theorem jAxis_orbit_cancels :
    jAxisProj poleJplus + jAxisProj poleJminus = 0 := by
  rw [jAxisProj_poleJplus, jAxisProj_poleJminus]
  ring

/-- Antipodal k-poles cancel as an orbit pair. -/
theorem kAxis_orbit_cancels :
    kAxisProj poleKplus + kAxisProj poleKminus = 0 := by
  rw [kAxisProj_poleKplus, kAxisProj_poleKminus]
  ring

/-! ## sin/cos rotation slots (= j/k complex projection) -/

/-- Sine slot: j-rotation content in the FE projection. -/
noncomputable def zetaSinSlot (s : ℂ) : ℂ :=
  sin (Real.pi * s / 2)

/-- Cosine slot: k-rotation content in the FE projection. -/
noncomputable def zetaCosSlot (s : ℂ) : ℂ :=
  cos (Real.pi * s / 2)

theorem zetaCosSlot_eq_zetaSinCosFactor (s : ℂ) :
    zetaCosSlot s = zetaSinCosFactor s := rfl

/-! ### Even integers: j/k cancel at exact `π` multiples -/

theorem zetaSinSlot_even_nat (k : ℕ) :
    zetaSinSlot (2 * k) = 0 := by
  unfold zetaSinSlot
  have hangle : (Real.pi : ℂ) * (2 * k : ℂ) / 2 = ↑(Real.pi * (k : ℝ)) := by
    push_cast; ring
  rw [hangle, ← ofReal_sin, mul_comm, Real.sin_nat_mul_pi, ofReal_zero]

theorem zetaCosSlot_even_nat (k : ℕ) :
    zetaCosSlot (2 * k) = (-1 : ℂ) ^ k := by
  unfold zetaCosSlot
  have hangle : (Real.pi : ℂ) * (2 * k : ℂ) / 2 = ↑(Real.pi * (k : ℝ)) := by
    push_cast; ring
  rw [hangle, ← ofReal_cos, mul_comm, Real.cos_nat_mul_pi]
  simp

/--
**Even ζ-sector packaging.** At even integers the sin/j–k channel vanishes; only
the cos/k residue `(-1)^k` survives — full π-turn cancellation on the sine slot.
-/
theorem even_zeta_rotation_slots_cancel_sin (k : ℕ) :
    zetaSinSlot (2 * k) = 0 ∧ zetaCosSlot (2 * k) = (-1 : ℂ) ^ k :=
  ⟨zetaSinSlot_even_nat k, zetaCosSlot_even_nat k⟩

/-! ### Odd integers: cosine cancels; sine carries the ratio -/

theorem zetaCosSlot_odd_nat (k : ℕ) :
    zetaCosSlot (2 * k + 1) = 0 := by
  unfold zetaCosSlot
  have hangle :
      (Real.pi : ℂ) * (2 * k + 1 : ℂ) / 2 =
        ↑(Real.pi * (k : ℝ) + Real.pi / 2) := by
    push_cast; ring_nf
  rw [hangle, ← ofReal_cos, Real.cos_add_pi_div_two]
  have hsin : Real.sin (Real.pi * (k : ℝ)) = 0 := by
    rw [mul_comm, Real.sin_nat_mul_pi]
  simp [hsin, ofReal_zero]

theorem zetaSinSlot_odd_nat (k : ℕ) :
    zetaSinSlot (2 * k + 1) = (-1 : ℂ) ^ k := by
  unfold zetaSinSlot
  have hangle :
      (Real.pi : ℂ) * (2 * k + 1 : ℂ) / 2 =
        ↑(Real.pi * (k : ℝ) + Real.pi / 2) := by
    push_cast; ring_nf
  rw [hangle, ← ofReal_sin, Real.sin_add_pi_div_two, mul_comm, Real.cos_nat_mul_pi]
  norm_cast

/--
**Odd ζ-sector packaging.** At odd integers the cos/k slot vanishes; the sin/j slot
carries `(-1)^k` — no elementary π-power closed form (Apéry slot).
-/
theorem odd_zeta_rotation_ratio_pure_sin (k : ℕ) :
    zetaCosSlot (2 * k + 1) = 0 ∧ zetaSinSlot (2 * k + 1) = (-1 : ℂ) ^ k :=
  ⟨zetaCosSlot_odd_nat k, zetaSinSlot_odd_nat k⟩

/-! ### Fractional strip: both slots live; rotation ratio -/

/-- Fractional rotation ratio: `tan(π·s/2)` when the cosine slot is nonzero. -/
noncomputable def zetaAxisRotationRatio (s : ℂ) : ℂ :=
  zetaSinSlot s / zetaCosSlot s

theorem zetaAxisRotationRatio_eq_tan (s : ℂ) (_hcos : zetaCosSlot s ≠ 0) :
    zetaAxisRotationRatio s = tan (Real.pi * s / 2) := by
  unfold zetaAxisRotationRatio zetaSinSlot zetaCosSlot
  rw [Complex.tan_eq_sin_div_cos]

/--
On the open strip at `σ = 1/2`, both slots equal `√2/2` — balanced j/k ratio `1`.
-/
theorem zetaAxisRotationRatio_at_half :
    zetaAxisRotationRatio (1 / 2 : ℂ) = 1 := by
  have hcos : zetaCosSlot (1 / 2 : ℂ) ≠ 0 := by
    rw [zetaCosSlot_eq_zetaSinCosFactor, zetaSinCosFactor_at_half]
    have hpos : (0 : ℝ) < Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
      positivity
    exact_mod_cast hpos.ne'
  rw [zetaAxisRotationRatio_eq_tan (1 / 2) hcos]
  have harg : (Real.pi : ℂ) * (1 / 2 : ℂ) / 2 = ↑(Real.pi / 4) := by
    push_cast; ring_nf
  rw [harg, ← ofReal_tan, Real.tan_pi_div_four, ofReal_one]

/--
**Fractional packaging.** Non-integer strip points keep a genuine sin/cos rotation
ratio; this is exactly the odd/FE channel (`oddStripChannel`).
-/
theorem fractional_zeta_carries_rotation_ratio
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    zetaFractionalSO4ClosedForm s = riemannZeta s :=
  zeta_fractional_so4_eq_zeta h0 h1

/-! ### Even ζ values link to π-sector (sin slot already cancelled) -/

theorem even_zeta_two_sin_slot_vanishes :
    zetaSinSlot 2 = 0 := by
  simpa [two_mul, Nat.cast_one] using zetaSinSlot_even_nat 1

theorem even_zeta_two_cos_slot_is_minus_one :
    zetaCosSlot 2 = -1 := by
  simpa [two_mul, Nat.cast_one] using zetaCosSlot_even_nat 1

theorem even_zeta_four_sin_slot_vanishes :
    zetaSinSlot (2 * 2) = 0 :=
  zetaSinSlot_even_nat 2

theorem even_zeta_four_cos_slot_is_one :
    zetaCosSlot (2 * 2) = 1 := by
  simpa using zetaCosSlot_even_nat 2

end

end Hqiv.Story
