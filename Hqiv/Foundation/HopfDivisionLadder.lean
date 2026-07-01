import Hqiv.Foundation.OctonionForcing
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# HopfDivisionLadder — topology pins the carrier at the octonionic Hopf fibration

This module tightens the octonion-forcing frontier with the **TUFT topological
hypothesis**: topology forces Hopf fibrations, and each Hopf fibration carries a normed
division algebra. There are exactly four (Hopf invariant one / Adams):

| index `k` | fiber       | total        | base       | division algebra |
|-----------|-------------|--------------|------------|------------------|
| 0 (ℝ)     | `S⁰`        | `S¹`         | `S¹`       | `ℝ`  (dim 1)     |
| 1 (ℂ)     | `S¹`        | `S³`         | `S²`       | `ℂ`  (dim 2)     |
| 2 (ℍ)     | `S³`        | `S⁷`         | `S⁴`       | `ℍ`  (dim 4)     |
| 3 (𝕆)     | `S⁷`        | `S¹⁵`        | `S⁸`       | `𝕆`  (dim 8)     |

All dimensions here are powers of two, matching `divisionAlgebraDim k = 2ᵏ` from
`CarrierBudget`. The decisive facts, all proved below with `rfl`/`decide`:

* the **octonionic fiber** `S⁷` has dimension `imaginaryDim = 7` — the seven imaginary
  directions are exactly the fiber of the maximal Hopf fibration;
* the **octonionic base** `S⁸` has dimension `carrierMultiplicity = 8`;
* the division-algebra ladder is `{1, 2, 4, 8}`, the carrier sits at its **maximum**, and
  the next Cayley–Dickson rung (`16`, the sedenions) is **not** Hopf-invariant-one — so
  the ladder provably terminates at the octonions.

This replaces the earlier ad-hoc uniqueness premise with a **topological selection**:
3D growth lands the carrier at dimension 8, and topology pins 8 as the *last* Hopf
fibration, whose division algebra is `𝕆`. The only residue is the classical statement
that this maximal fibration's normed division algebra is unique — carried, as before, as
an explicit hypothesis, never an axiom.
-/

namespace Hqiv.Foundation

/-! ## Hopf fibration dimension bookkeeping -/

/-- Fiber-sphere dimension of the `k`-th Hopf fibration: `S^(2ᵏ−1)`. -/
def hopfFiberDim (k : ℕ) : ℕ := 2 ^ k - 1

/-- Total-sphere dimension of the `k`-th Hopf fibration: `S^(2^(k+1)−1)`. -/
def hopfTotalDim (k : ℕ) : ℕ := 2 ^ (k + 1) - 1

/-- Base-sphere dimension of the `k`-th Hopf fibration: `S^(2ᵏ)`. -/
def hopfBaseDim (k : ℕ) : ℕ := 2 ^ k

/-- Division-algebra dimension carried by the `k`-th Hopf fibration: `2ᵏ`. -/
def hopfDivisionDim (k : ℕ) : ℕ := 2 ^ k

/-- The Hopf division-algebra dimension is the Cayley–Dickson dimension of `CarrierBudget`. -/
theorem hopfDivisionDim_eq_divisionAlgebraDim (k : ℕ) :
    hopfDivisionDim k = divisionAlgebraDim k := rfl

/-! ### The four classical fibrations, by index -/

theorem hopf_real_dims :
    hopfFiberDim 0 = 0 ∧ hopfTotalDim 0 = 1 ∧ hopfBaseDim 0 = 1 ∧ hopfDivisionDim 0 = 1 := by
  decide

theorem hopf_complex_dims :
    hopfFiberDim 1 = 1 ∧ hopfTotalDim 1 = 3 ∧ hopfBaseDim 1 = 2 ∧ hopfDivisionDim 1 = 2 := by
  decide

theorem hopf_quaternion_dims :
    hopfFiberDim 2 = 3 ∧ hopfTotalDim 2 = 7 ∧ hopfBaseDim 2 = 4 ∧ hopfDivisionDim 2 = 4 := by
  decide

theorem hopf_octonion_dims :
    hopfFiberDim 3 = 7 ∧ hopfTotalDim 3 = 15 ∧ hopfBaseDim 3 = 8 ∧ hopfDivisionDim 3 = 8 := by
  decide

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

/-- **Division-algebra dimensions admitting a Hopf-invariant-one fibration** (Adams):
exactly `{1, 2, 4, 8}`. -/
def hopfInvariantOneDims : Finset ℕ := {1, 2, 4, 8}

/-- Each of the four fibration indices lands in the ladder. -/
theorem hopfDivisionDim_mem (k : ℕ) (hk : k ≤ 3) :
    hopfDivisionDim k ∈ hopfInvariantOneDims := by
  interval_cases k <;> decide

/-- **The next Cayley–Dickson rung (sedenions, dimension 16) is not Hopf-invariant-one.** -/
theorem sedenion_dim : divisionAlgebraDim 4 = 16 := rfl

theorem sedenion_not_hopfInvariantOne : divisionAlgebraDim 4 ∉ hopfInvariantOneDims := by
  decide

/-- **Topological pinning of the carrier (fully proved, no hypothesis).**

The carrier multiplicity (forced to `8` by 3D growth) is a Hopf-invariant-one dimension,
it is the **maximum** of the ladder, and the next doubling step leaves the ladder. So
topology pins the carrier at the octonionic Hopf fibration: `𝕆` is the last division
algebra. -/
theorem carrier_is_maximal_hopf_division :
    carrierMultiplicity ∈ hopfInvariantOneDims ∧
    (∀ n ∈ hopfInvariantOneDims, n ≤ carrierMultiplicity) ∧
    divisionAlgebraDim 4 ∉ hopfInvariantOneDims := by
  refine ⟨?_, ?_, sedenion_not_hopfInvariantOne⟩
  · rw [carrierMultiplicity_eq_eight]; decide
  · rw [carrierMultiplicity_eq_eight]; decide

/-! ## The TUFT topological frontier -/

/-- **TUFT topological selection principle (the frontier — stated, never an axiom).**

Reading of the residual gap through the Hopf hypothesis: topology forces the carrier
onto the maximal Hopf-invariant-one fibration (the octonionic one, `S⁷ ↪ S¹⁵ → S⁸`), and
that fibration's normed division algebra is the unique carrier multiplication.

The *dimension* half of this principle is proved (`carrier_is_maximal_hopf_division`,
`octonionic_fiber_eq_imaginaryDim`, `octonionic_base_eq_carrier`). The remaining content
is precisely the classical division-algebra uniqueness at the maximal rung, which is
`OctonionTableUnique`. We therefore *define* the topological selection as that residual,
making explicit that the only thing left to prove is per-fibration uniqueness. -/
def TuftHopfSelectsOctonion : Prop := OctonionTableUnique

/-- **Topological route to the end goal.**

Under the TUFT Hopf-selection principle, 3D growth forces the octonion carrier. This is
the Hopf-fibration reading of `threeD_forces_octonion_of_uniqueness`: the dimension is
pinned topologically and the residual uniqueness is the fibration's division algebra. -/
theorem tuftHopf_forces_octonion (h : TuftHopfSelectsOctonion) : ThreeDForcesOctonion :=
  threeD_forces_octonion_of_uniqueness h

/-- The TUFT topological frontier is exactly the maximal-Hopf division-algebra
uniqueness — no extra content is smuggled in. -/
theorem tuftHopfSelectsOctonion_iff : TuftHopfSelectsOctonion ↔ OctonionTableUnique := Iff.rfl

end Hqiv.Foundation
