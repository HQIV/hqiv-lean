import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic.FinCases

/-!
# Integer lattice points in `ℤ³` grouped by max-|coordinate| shells

Index lattice points `p : Fin 3 → ℤ` by **`maxNatAbsCoord p := sup_i |p i|`** (a Chebyshev / L∞-type
shell label on the cubic lattice). This is the **discrete** analogue of nested Euclidean shells in
`SpatialSliceManifold`: disjoint layers indexed by `ℕ`, but using **max absolute coordinate** rather
than Euclidean radius.

**Proved:** shells `latticeMaxAbsShell k` for distinct `k` are **pairwise disjoint**; layer `0` is
exactly the origin.

**Not here:** asymptotic comparison with `euclideanShellVolumeReal` or identification with a particular
Euclidean ball — optional future bridges.
-/

namespace Hqiv.Geometry

open Finset

/-- `sup` of `|p i|` over the three axes (nonnegative integer). -/
def maxNatAbsCoord (p : Fin 3 → ℤ) : ℕ :=
  (univ : Finset (Fin 3)).sup fun i => (p i).natAbs

/-- Lattice points whose max-|coordinate| shell index is exactly `k`. -/
def latticeMaxAbsShell (k : ℕ) : Set (Fin 3 → ℤ) :=
  { p | maxNatAbsCoord p = k }

@[simp]
theorem mem_latticeMaxAbsShell (k : ℕ) (p : Fin 3 → ℤ) :
    p ∈ latticeMaxAbsShell k ↔ maxNatAbsCoord p = k :=
  Iff.rfl

/-- If all three coordinates agree, the max-`natAbs` shell label is `|j|`. -/
theorem maxNatAbsCoord_eq_natAbs_of_all_eq (p : Fin 3 → ℤ) (j : ℤ)
    (h0 : p 0 = j) (h1 : p 1 = j) (h2 : p 2 = j) : maxNatAbsCoord p = j.natAbs := by
  unfold maxNatAbsCoord
  have hf : ∀ i : Fin 3, (p i).natAbs = j.natAbs := by
    intro i
    fin_cases i <;> simp [h0, h1, h2]
  rw [show (fun i : Fin 3 => (p i).natAbs) = fun _ => j.natAbs from funext hf]
  exact Finset.sup_const Finset.univ_nonempty j.natAbs

/-- If `p 0 = p 1`, the max-`natAbs` label is `max |p 0| |p 2|`. -/
theorem maxNatAbsCoord_eq_max_of_eq01 (p : Fin 3 → ℤ) (h01 : p 0 = p 1) :
    maxNatAbsCoord p = max (p 0).natAbs (p 2).natAbs := by
  unfold maxNatAbsCoord
  have hf1 : (p 1).natAbs = (p 0).natAbs := by rw [h01]
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro i _
    fin_cases i <;> simp [hf1]
  · refine max_le ?_ ?_
    · exact Finset.le_sup (f := fun i => (p i).natAbs) (mem_univ (0 : Fin 3))
    · exact Finset.le_sup (f := fun i => (p i).natAbs) (mem_univ (2 : Fin 3))

/-- If `p 0 = p 2`, the max-`natAbs` label is `max |p 0| |p 1|`. -/
theorem maxNatAbsCoord_eq_max_of_eq02 (p : Fin 3 → ℤ) (h02 : p 0 = p 2) :
    maxNatAbsCoord p = max (p 0).natAbs (p 1).natAbs := by
  unfold maxNatAbsCoord
  have hf2 : (p 2).natAbs = (p 0).natAbs := by rw [h02]
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro i _
    fin_cases i <;> simp [hf2]
  · refine max_le ?_ ?_
    · exact Finset.le_sup (f := fun i => (p i).natAbs) (mem_univ (0 : Fin 3))
    · exact Finset.le_sup (f := fun i => (p i).natAbs) (mem_univ (1 : Fin 3))

/-- If `p 1 = p 2`, the max-`natAbs` label is `max |p 0| |p 1|`. -/
theorem maxNatAbsCoord_eq_max_of_eq12 (p : Fin 3 → ℤ) (h12 : p 1 = p 2) :
    maxNatAbsCoord p = max (p 0).natAbs (p 1).natAbs := by
  unfold maxNatAbsCoord
  have hf2 : (p 2).natAbs = (p 1).natAbs := by rw [h12]
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro i _
    fin_cases i <;> simp [h12, hf2]
  · refine max_le ?_ ?_
    · exact Finset.le_sup (f := fun i => (p i).natAbs) (mem_univ (0 : Fin 3))
    · exact Finset.le_sup (f := fun i => (p i).natAbs) (mem_univ (1 : Fin 3))

theorem maxNatAbsCoord_eq_zero_iff (p : Fin 3 → ℤ) : maxNatAbsCoord p = 0 ↔ p = 0 := by
  constructor
  · intro h
    funext i
    have hi : i ∈ (univ : Finset (Fin 3)) := mem_univ i
    have hle : (p i).natAbs ≤ maxNatAbsCoord p :=
      Finset.le_sup (f := fun j => (p j).natAbs) hi
    rw [h] at hle
    have hn : (p i).natAbs = 0 := Nat.eq_zero_of_le_zero hle
    exact Int.natAbs_eq_zero.mp hn
  · rintro rfl
    unfold maxNatAbsCoord
    have hf : (fun i : Fin 3 => ((0 : Fin 3 → ℤ) i).natAbs) = fun _ => (0 : ℕ) := by
      funext i
      simp
    rw [hf, Finset.sup_const Finset.univ_nonempty]

/-- Only the origin lies in shell `0`. -/
theorem latticeMaxAbsShell_zero : latticeMaxAbsShell 0 = {0} := by
  ext p
  simp [latticeMaxAbsShell, maxNatAbsCoord_eq_zero_iff]

theorem latticeMaxAbsShell_disjoint_of_ne {k j : ℕ} (h : k ≠ j) :
    Disjoint (latticeMaxAbsShell k) (latticeMaxAbsShell j) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext p
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, mem_latticeMaxAbsShell]
  intro hk hj
  exact h (hk.symm.trans hj)

theorem latticeMaxAbsShell_pairwise_disjoint :
    ∀ ⦃k j : ℕ⦄, k ≠ j → Disjoint (latticeMaxAbsShell k) (latticeMaxAbsShell j) :=
  fun _ _ => latticeMaxAbsShell_disjoint_of_ne

end Hqiv.Geometry
