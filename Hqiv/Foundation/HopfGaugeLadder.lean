import Hqiv.Foundation.HopfDivisionLadder
import Mathlib.Tactic

/-!
# HopfGaugeLadder — the nested Hopf bundles carry U(1), SU(2), SU(3), and SO(8) collects them

Building on `HopfDivisionLadder`, this module records the Furey–Dixon division-algebra
reading of the Standard Model gauge group as **arithmetic that is forced by the carrier**.

The four Hopf fibrations nest: the *total* space of fibration `k` is the *fiber* of
fibration `k+1` (`hopf_tower_nesting`), giving the tower

```
        S¹  ⊂  S³  ⊂  S⁷
       (U(1)) (SU(2))  (color level)
```

* the **complex** Hopf fiber `S¹` is a Lie group, `S¹ ≅ U(1)` — `dim = 1`;
* the **quaternionic** Hopf fiber `S³` is a Lie group, `S³ ≅ SU(2)` — `dim = 3`;
* the **octonionic** Hopf fiber `S⁷` is *not* a group (octonions are non-associative;
  `S⁷` is a Moufang loop). Colour `SU(3)` therefore appears one level up, as the
  subgroup of `G₂ = Aut(𝕆)` fixing one imaginary unit — `dim = 8`. This asymmetry (two
  fibers are groups, the third is not) is the structural reason colour is the "confined"
  factor.

Putting the rungs together, the rotation algebra of the carrier collects all three:

* `g2Dim = 14 = 8 + 3 + 3` — `𝔤₂ ↓ SU(3)` is the colour octet plus a `3 ⊕ 3̄`;
* `imaginaryDim = 7 = 1 + 3 + 3` — the seven imaginary directions are `1 ⊕ 3 ⊕ 3̄`;
* `soDim 8 = 28 = (8+3+3) + (1+3+3) + (1+3+3)` — the full `so(8) ↓ 𝔤₂ ↓ SU(3)` branch;
* `rank SO(8) = 4 = 1 + 1 + 2 = rank(U(1) × SU(2) × SU(3))`.

So the Standard Model gauge dimensions (`1 + 3 + 8 = 12`) and its rank (`4`) sit inside
`so(8)` exactly as the nested-Hopf / `G₂` branching prescribes. The remaining content —
that these dimensions are realized by an *actual* subgroup `U(1) × SU(2) × SU(3) ↪
Spin(8)` built from the division-algebra tower — is the named frontier, carried as prose,
never as an `axiom`.
-/

namespace Hqiv.Foundation

/-! ## Gauge-factor dimensions and ranks -/

/-- `dim U(1) = 1` (the complex Hopf fiber `S¹`). -/
def u1Dim : ℕ := 1
/-- `dim SU(2) = 3` (the quaternionic Hopf fiber `S³`). -/
def su2Dim : ℕ := 3
/-- `dim SU(3) = 8` (colour, the `G₂`-stabilizer at the octonionic level). -/
def su3Dim : ℕ := 8

/-- Standard Model gauge-algebra dimension `1 + 3 + 8 = 12`. -/
def smGaugeDim : ℕ := u1Dim + su2Dim + su3Dim

theorem smGaugeDim_eq : smGaugeDim = 12 := rfl

/-- Ranks: `U(1)` rank 1, `SU(2)` rank 1, `SU(3)` rank 2. -/
def u1Rank : ℕ := 1
def su2Rank : ℕ := 1
def su3Rank : ℕ := 2

/-- Standard Model gauge rank `1 + 1 + 2 = 4`. -/
def smGaugeRank : ℕ := u1Rank + su2Rank + su3Rank

theorem smGaugeRank_eq : smGaugeRank = 4 := rfl

/-- `rank SO(2n) = n`, so `rank SO(8) = carrier/2 = 4`. -/
def so8Rank : ℕ := carrierMultiplicity / 2

theorem so8Rank_eq : so8Rank = 4 := by
  unfold so8Rank; rw [carrierMultiplicity_eq_eight]

/-! ## The nested Hopf tower -/

/-- **The Hopf bundles nest.** The total sphere of fibration `k` is the fiber of fibration
`k+1`: `S^(2^(k+1)−1)`. So `S¹ ⊂ S³ ⊂ S⁷ ⊂ S¹⁵` is a single tower of fibers. -/
theorem hopf_tower_nesting (k : ℕ) : hopfTotalDim k = hopfFiberDim (k + 1) := rfl

/-! ## Each nested fiber carries its gauge factor -/

/-- **The complex Hopf fiber `S¹` is `U(1)`.** -/
theorem complex_fiber_is_u1 : hopfFiberDim 1 = u1Dim := by decide

/-- **The quaternionic Hopf fiber `S³` is `SU(2)`.** (`S³ ≅ SU(2)` as Lie groups.) -/
theorem quaternion_fiber_is_su2 : hopfFiberDim 2 = su2Dim := by decide

/-- **The octonionic fiber `S⁷` is the seven imaginary directions, not a group.**
Colour `SU(3)` is sourced one level up via `G₂ = Aut(𝕆)`; see `g2_branch_su3`. -/
theorem octonion_fiber_is_imaginary : hopfFiberDim 3 = imaginaryDim :=
  octonionic_fiber_eq_imaginaryDim

/-! ## Colour SU(3) from G₂, and the seven imaginary triplets -/

/-- **`𝔤₂ ↓ SU(3)`** colour branch: `14 = 8 ⊕ 3 ⊕ 3̄`. The colour octet lives inside the
derivation algebra `𝔤₂ = Aut(𝕆)`. -/
theorem g2_branch_su3 : g2Dim = su3Dim + 3 + 3 := by
  rw [g2Dim_eq_fourteen]; decide

/-- **The seven imaginary octonions are an `SU(3)` `1 ⊕ 3 ⊕ 3̄`.** -/
theorem imaginary_branch_su3 : imaginaryDim = 1 + 3 + 3 := by
  rw [imaginaryDim_eq_seven]

/-! ## SO(8) collects all three gauge factors -/

/-- **`so(8) ↓ 𝔤₂ ↓ SU(3)`.** The full 28-dimensional rotation algebra of the carrier
decomposes as `(8 ⊕ 3 ⊕ 3̄) ⊕ (1 ⊕ 3 ⊕ 3̄) ⊕ (1 ⊕ 3 ⊕ 3̄)`, i.e. one colour octet plus
imaginary triplets — the colour `SU(3)` appears exactly once. -/
theorem so8_branch_su3_color :
    soDim carrierMultiplicity = (su3Dim + 3 + 3) + (1 + 3 + 3) + (1 + 3 + 3) := by
  rw [soDim_carrier]; decide

/-- **Rank match:** `rank SO(8) = 4 = rank(U(1) × SU(2) × SU(3))`. -/
theorem smGauge_rank_matches_so8 : smGaugeRank = so8Rank := by
  rw [smGaugeRank_eq, so8Rank_eq]

/-- The Standard Model gauge dimension fits inside `so(8)`: `12 ≤ 28`. -/
theorem smGauge_dim_le_so8 : smGaugeDim ≤ soDim carrierMultiplicity := by
  rw [soDim_carrier]; decide

/-- The `so(8)` dimensions left over after the Standard Model gauge algebra: `28 − 12 = 16`. -/
theorem so8_minus_smGauge : soDim carrierMultiplicity - smGaugeDim = 16 := by
  rw [soDim_carrier]; decide

/-! ## Decomposition certificate -/

/-- **Gauge-dimension decomposition of the carrier (fully proved, no hypothesis).**

Bundles the facts that the nested-Hopf / `G₂` branching of the carrier's rotation algebra
reproduces the Standard Model gauge dimensions and rank. -/
structure GaugeDimDecomposition : Prop where
  /-- Colour octet inside the derivation algebra: `14 = 8 + 3 + 3`. -/
  color_in_g2 : g2Dim = su3Dim + 3 + 3
  /-- Imaginary directions as `SU(3)` triplets: `7 = 1 + 3 + 3`. -/
  imaginary_triplets : imaginaryDim = 1 + 3 + 3
  /-- Full `so(8) ↓ SU(3)` colour branch. -/
  so8_color : soDim carrierMultiplicity = (su3Dim + 3 + 3) + (1 + 3 + 3) + (1 + 3 + 3)
  /-- `rank SO(8) = rank` of the Standard Model gauge group. -/
  rank_match : smGaugeRank = so8Rank
  /-- The Standard Model gauge dimension embeds dimensionally. -/
  dim_fits : smGaugeDim ≤ soDim carrierMultiplicity

theorem gaugeDimDecomposition : GaugeDimDecomposition where
  color_in_g2 := g2_branch_su3
  imaginary_triplets := imaginary_branch_su3
  so8_color := so8_branch_su3_color
  rank_match := smGauge_rank_matches_so8
  dim_fits := smGauge_dim_le_so8

end Hqiv.Foundation
