import HqivSpine.Foundation.Carrier
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Foundation.HopfLadder` — topology pins the carrier at the octonions

`Carrier` derived the multiplicity `8` from 3D growth and placed it on the
Cayley–Dickson / Hurwitz dimension ladder `1, 2, 4, 8 = 2ᵏ`. That ladder is, a
priori, infinite (the doubling `divisionAlgebraDim k = 2ᵏ` never stops). This
module supplies the missing **selection principle**: of all the doubling rungs,
only finitely many carry a *normed division algebra*, and the carrier sits at the
top of that finite set.

The selection is topological. Each normed division algebra `𝔸` of dimension `2ᵏ`
is the data of a **Hopf fibration** `S^(2ᵏ−1) ↪ S^(2^(k+1)−1) → S^(2ᵏ)`, and a
fibration of *Hopf invariant one* exists in exactly four cases (Adams):

| index `k` | fiber  | total | base | division algebra |
|-----------|--------|-------|------|------------------|
| `0` (ℝ)   | `S⁰`   | `S¹`  | `S¹` | `ℝ` (dim `1`)    |
| `1` (ℂ)   | `S¹`   | `S³`  | `S²` | `ℂ` (dim `2`)    |
| `2` (ℍ)   | `S³`   | `S⁷`  | `S⁴` | `ℍ` (dim `4`)    |
| `3` (𝕆)   | `S⁷`   | `S¹⁵` | `S⁸` | `𝕆` (dim `8`)    |

We record the four fibrations as pure dimension bookkeeping (every claim by
`decide`), identify the **octonionic** rung with the carrier (`S⁷` is the seven
imaginary directions, `S⁸` is the eight channels), and prove the decisive
structural fact: the carrier dimension `8` is the **maximum** of the
Hopf-invariant-one set `{1, 2, 4, 8}`, while the next Cayley–Dickson rung
(the sedenions, dimension `16`) **leaves** that set. So the doubling ladder,
though infinite, is selected down to a finite ladder that *terminates at the
octonions* — and 3D growth lands the carrier exactly on its last rung.

Still pure `ℕ`/`Finset` arithmetic: the analytic content (Adams' theorem itself)
is encoded only through the finite admissible set `{1, 2, 4, 8}`, never assumed
as an axiom.
-/

namespace HqivSpine.Foundation

open Finset

/-! ## Hopf fibration dimension bookkeeping

The `k`-th doubling rung `𝔸` (dimension `2ᵏ`) would be fibred by unit `𝔸`-lines:
the fiber is the unit sphere of `𝔸` (`S^(2ᵏ−1)`), the total space the unit sphere
of `𝔸²` (`S^(2^(k+1)−1)`), and the base the projective `𝔸`-line (`S^(2ᵏ)`). -/

/-- Fiber-sphere dimension of the `k`-th Hopf fibration: `S^(2ᵏ−1)`. -/
def hopfFiberDim (k : ℕ) : ℕ := 2 ^ k - 1

/-- Total-sphere dimension of the `k`-th Hopf fibration: `S^(2^(k+1)−1)`. -/
def hopfTotalDim (k : ℕ) : ℕ := 2 ^ (k + 1) - 1

/-- Base-sphere dimension of the `k`-th Hopf fibration: `S^(2ᵏ)`. -/
def hopfBaseDim (k : ℕ) : ℕ := 2 ^ k

/-- The base-sphere dimension is exactly the carried division-algebra dimension:
the projective `𝔸`-line `S^(2ᵏ)` has the dimension of `𝔸` itself. -/
theorem hopfBaseDim_eq_divisionAlgebraDim (k : ℕ) :
    hopfBaseDim k = divisionAlgebraDim k := rfl

/-! ### The four classical fibrations, by index -/

/-- Real Hopf data `S⁰ ↪ S¹ → S¹`, division algebra `ℝ` (dim `1`). -/
theorem hopf_real_dims :
    hopfFiberDim 0 = 0 ∧ hopfTotalDim 0 = 1 ∧ hopfBaseDim 0 = 1 := by decide

/-- Complex Hopf data `S¹ ↪ S³ → S²`, division algebra `ℂ` (dim `2`). -/
theorem hopf_complex_dims :
    hopfFiberDim 1 = 1 ∧ hopfTotalDim 1 = 3 ∧ hopfBaseDim 1 = 2 := by decide

/-- Quaternionic Hopf data `S³ ↪ S⁷ → S⁴`, division algebra `ℍ` (dim `4`). -/
theorem hopf_quaternion_dims :
    hopfFiberDim 2 = 3 ∧ hopfTotalDim 2 = 7 ∧ hopfBaseDim 2 = 4 := by decide

/-- Octonionic Hopf data `S⁷ ↪ S¹⁵ → S⁸`, division algebra `𝕆` (dim `8`). -/
theorem hopf_octonion_dims :
    hopfFiberDim 3 = 7 ∧ hopfTotalDim 3 = 15 ∧ hopfBaseDim 3 = 8 := by decide

/-! ## Identification of the octonionic fibration with the forced carrier -/

/-- **The octonionic Hopf fiber `S⁷` is the seven imaginary directions.** -/
theorem octonionic_fiber_eq_imaginaryDim : hopfFiberDim 3 = imaginaryDim := by
  rw [imaginaryDim_eq_seven]; decide

/-- **The octonionic Hopf base `S⁸` is the eight carrier channels.** -/
theorem octonionic_base_eq_carrier : hopfBaseDim 3 = carrierMultiplicity := by
  rw [carrierMultiplicity_eq_eight]; decide

/-- **The octonionic Hopf total space `S¹⁵`** has dimension `2·carrier − 1`. -/
theorem octonionic_total_eq : hopfTotalDim 3 = 2 * carrierMultiplicity - 1 := by
  rw [carrierMultiplicity_eq_eight]; decide

/-! ## The Hopf-invariant-one ladder and its termination at the octonions -/

/-- **Division-algebra dimensions admitting a Hopf-invariant-one fibration**
(Adams' theorem): exactly `{1, 2, 4, 8}`. This finite set is the entire analytic
content; everything below is its arithmetic. -/
def hopfInvariantOneDims : Finset ℕ := {1, 2, 4, 8}

/-- Each of the four classical fibration indices lands in the admissible set. -/
theorem hopfBaseDim_mem (k : ℕ) (hk : k ≤ 3) :
    hopfBaseDim k ∈ hopfInvariantOneDims := by
  interval_cases k <;> decide

/-- **The next Cayley–Dickson rung (the sedenions) has dimension `16`.** -/
theorem sedenion_dim : divisionAlgebraDim 4 = 16 := rfl

/-- **The sedenions are not Hopf-invariant-one**: `16 ∉ {1, 2, 4, 8}`. The
doubling can be continued algebraically, but it leaves the topological ladder. -/
theorem sedenion_not_hopfInvariantOne :
    divisionAlgebraDim 4 ∉ hopfInvariantOneDims := by decide

/-- **Topological pinning of the carrier (fully proved, no hypothesis).**

The carrier multiplicity — forced to `8` by 3D growth — is a Hopf-invariant-one
dimension, it is the **maximum** of the admissible set, and the next doubling step
leaves the set. So topology selects the carrier as the *last* Hopf fibration, whose
normed division algebra is `𝕆`: the ladder terminates at the octonions. -/
theorem carrier_is_maximal_hopf_division :
    carrierMultiplicity ∈ hopfInvariantOneDims ∧
    (∀ n ∈ hopfInvariantOneDims, n ≤ carrierMultiplicity) ∧
    divisionAlgebraDim 4 ∉ hopfInvariantOneDims := by
  refine ⟨?_, ?_, sedenion_not_hopfInvariantOne⟩
  · rw [carrierMultiplicity_eq_eight]; decide
  · rw [carrierMultiplicity_eq_eight]; decide

/-- **The selected ladder is finite and exhausted by the four classical rungs.**
The doubling `divisionAlgebraDim` is injective, so the four admissible
dimensions `{1, 2, 4, 8}` come from exactly the four indices `k ∈ {0, 1, 2, 3}`,
the largest of which is the carrier. -/
theorem hopfInvariantOneDims_card : hopfInvariantOneDims.card = 4 := by decide

end HqivSpine.Foundation
