import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic

import Hqiv.Algebra.OctonionSphereConstruction

/-!
# Representation count `r₈(m)` on the integer octonion lattice (`Fin 8 → ℤ`)

For `z : Fin 8 → ℤ`, define **`sumSqInt8 z = ∑ᵢ |zᵢ|²`** (as `ℕ`). The **shell** at squared radius `m` is
`{ z | sumSqInt8 z = m }`; its finite cardinality is **`r8 m`**.

Pure discrete geometry of `\mathbb{Z}⁸` — the same shell index `m` as in `OctonionSphereConstruction` /
Lagrange four-squares, but here we **count** lattice points rather than prove existence.

**Construction:** coordinates with `∑ zᵢ² = m` satisfy `|zᵢ| ≤ ⌊√m⌋`, so we enumerate `Fintype.piFinset`
and filter by `sumSqInt8 z = m`.

**Positivity:** `r8 m > 0` for every `m` (`r8_pos`) — the same four-square padding as
`OctonionSphereConstruction.embedNatFour` hits every shell.
-/

noncomputable section

open Finset Fintype
open scoped BigOperators

namespace Hqiv.Algebra

/-- Sum of squared absolute values `∑ᵢ |zᵢ|²`. -/
def sumSqInt8 (z : Fin 8 → ℤ) : ℕ :=
  ∑ i : Fin 8, (z i).natAbs ^ 2

/-- Four-square padding in `ℤ⁸` has `sumSqInt8` equal to the four-square sum. -/
theorem sumSqInt8_embedNatFour (a b c d : ℕ) :
    sumSqInt8 (fun i => (embedNatFour a b c d i : ℤ)) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  dsimp [sumSqInt8]
  have h0 : embedNatFour a b c d (0 : Fin 8) = a := rfl
  have h1 : embedNatFour a b c d 1 = b := rfl
  have h2 : embedNatFour a b c d 2 = c := rfl
  have h3 : embedNatFour a b c d 3 = d := rfl
  have h4 : embedNatFour a b c d 4 = 0 := rfl
  have h5 : embedNatFour a b c d 5 = 0 := rfl
  have h6 : embedNatFour a b c d 6 = 0 := rfl
  have h7 : embedNatFour a b c d 7 = 0 := rfl
  rw [Fin.sum_univ_eight, h0, h1, h2, h3, h4, h5, h6, h7]
  ring

lemma natAbs_le_sqrt_of_sumSqInt8_eq {m : ℕ} (z : Fin 8 → ℤ) (h : sumSqInt8 z = m) (i : Fin 8) :
    (z i).natAbs ≤ Nat.sqrt m := by
  have hi : (z i).natAbs ^ 2 ≤ m := by
    have hsum : ∑ j : Fin 8, (z j).natAbs ^ 2 = m := h
    have hle := Finset.single_le_sum (f := fun j : Fin 8 => (z j).natAbs ^ 2)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa [hsum] using hle
  rw [Nat.pow_two] at hi
  exact Nat.le_sqrt.2 hi

lemma mem_Icc_neg_natCast_iff_natAbs {B : ℕ} (z : ℤ) :
    z ∈ Finset.Icc (-(B : ℤ)) (B : ℤ) ↔ z.natAbs ≤ B := by
  rw [Finset.mem_Icc, ← abs_le, Int.abs_eq_natAbs]
  rw [← Nat.cast_le (α := ℤ)]

/-- Finite box: each coordinate in `[-√m, √m]`. -/
def latticeBox8 (m : ℕ) : Finset (Fin 8 → ℤ) :=
  piFinset (fun _ : Fin 8 => Finset.Icc (-(Nat.sqrt m : ℤ)) (Nat.sqrt m : ℤ))

/-- Crude axis box `[-m,m]⁸` (superset of the exact `√m`-box in `latticeBox8`). Used only for **cardinality**
upper bounds on `r₈(m)`. -/
def latticeBox8Wide (m : ℕ) : Finset (Fin 8 → ℤ) :=
  piFinset fun _ : Fin 8 => Finset.Icc (-(m : ℤ)) (m : ℤ)

lemma mem_latticeBox8Wide_iff {m : ℕ} (z : Fin 8 → ℤ) :
    z ∈ latticeBox8Wide m ↔ ∀ i : Fin 8, z i ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) :=
  mem_piFinset

/-- Shell `∑ zᵢ² = m` in `\mathbb{Z}⁸`. -/
def latticeShell8Finset (m : ℕ) : Finset (Fin 8 → ℤ) :=
  (latticeBox8 m).filter fun z => sumSqInt8 z = m

/-- `r₈(m)`: number of integer lattice points with `∑ᵢ zᵢ² = m`. -/
def r8 (m : ℕ) : ℕ :=
  (latticeShell8Finset m).card

lemma mem_latticeBox8_iff {m : ℕ} (z : Fin 8 → ℤ) :
    z ∈ latticeBox8 m ↔ ∀ i : Fin 8, z i ∈ Finset.Icc (-(Nat.sqrt m : ℤ)) (Nat.sqrt m : ℤ) :=
  mem_piFinset

lemma mem_latticeShell8Finset_iff {m : ℕ} (z : Fin 8 → ℤ) :
    z ∈ latticeShell8Finset m ↔ sumSqInt8 z = m := by
  constructor
  · intro h
    simpa [latticeShell8Finset, Finset.mem_filter] using (Finset.mem_filter.1 h).2
  · intro hsum
    apply Finset.mem_filter.2
    refine ⟨?_, hsum⟩
    rw [mem_latticeBox8_iff]
    intro i
    rw [mem_Icc_neg_natCast_iff_natAbs]
    exact natAbs_le_sqrt_of_sumSqInt8_eq z hsum i

theorem r8_eq_card_shell (m : ℕ) : r8 m = (latticeShell8Finset m).card :=
  rfl

lemma card_Icc_int_neg_B_B (B : ℕ) :
    (Finset.Icc (-(B : ℤ)) (B : ℤ)).card = 2 * B + 1 := by
  rw [Int.card_Icc]
  rw [show (B : ℤ) + 1 - (-(B : ℤ)) = ((2 * B + 1 : ℕ) : ℤ) by push_cast; ring]
  simpa using Int.toNat_natCast (2 * B + 1)

theorem card_latticeBox8Wide (m : ℕ) : (latticeBox8Wide m).card = (2 * m + 1) ^ 8 := by
  dsimp [latticeBox8Wide]
  rw [Fintype.card_piFinset]
  simp_rw [card_Icc_int_neg_B_B m]
  exact Fin.prod_const (8 : ℕ) (2 * m + 1)

lemma latticeShell8Finset_subset_latticeBox8Wide (m : ℕ) :
    latticeShell8Finset m ⊆ latticeBox8Wide m := by
  intro z hz
  rw [mem_latticeShell8Finset_iff] at hz
  rw [mem_latticeBox8Wide_iff]
  intro i
  rw [mem_Icc_neg_natCast_iff_natAbs]
  exact Nat.le_trans (natAbs_le_sqrt_of_sumSqInt8_eq z hz i) (Nat.sqrt_le_self m)

/-- **Crude** bound: shell points lie in `[-m,m]⁸`, so `r₈(m) ≤ (2m+1)⁸` (far from sharp). -/
theorem r8_le_two_mul_add_one_pow_eight (m : ℕ) : r8 m ≤ (2 * m + 1) ^ 8 := by
  rw [r8, ← card_latticeBox8Wide]
  exact Finset.card_le_card (latticeShell8Finset_subset_latticeBox8Wide m)

/-- The shell at `m = 0` is only the origin. -/
theorem r8_zero : r8 0 = 1 := by
  native_decide

/-- At `m = 1`, the `16` signed standard basis vectors. -/
theorem r8_one : r8 1 = 16 := by
  native_decide

/-- Every shell has at least one lattice point (Lagrange four-square padding). -/
theorem r8_pos (m : ℕ) : 0 < r8 m := by
  cases m with
  | zero =>
    rw [r8_zero]
    decide
  | succ m =>
    obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (Nat.succ m)
    let z : Fin 8 → ℤ := fun i => (embedNatFour a b c d i : ℤ)
    have hz : sumSqInt8 z = Nat.succ m := by rw [sumSqInt8_embedNatFour, h]
    have hmem : z ∈ latticeShell8Finset (Nat.succ m) :=
      (mem_latticeShell8Finset_iff (m := Nat.succ m) z).mpr hz
    rw [r8]
    exact Finset.card_pos.2 ⟨z, hmem⟩

end Hqiv.Algebra

end
