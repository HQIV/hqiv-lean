import HqivSpine.Chemistry.ShellStructure
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.Aufbau` — the Madelung filling order, derived

`Chemistry.Binding.slaterEffectiveCharge` took the principal-block occupancy `block : Fin Z → ℕ`
*abstractly*, so it was independent of which orbital each electron actually occupies. This module
supplies that occupancy **from the spine's own combinatorics**, closing the gap and (unlike the
legacy period-≤2 Compton-shell guess in `Hqiv.QuantumChemistry.AtomElectronicBinding`) getting the
period-3+ valence right (e.g. sodium's outermost electron sits at `n = 3`).

The only ordering input is the **Madelung / `(n+ℓ)` rule**: subshells fill by increasing `n+ℓ`,
ties broken by increasing `n`. That key is exactly the network step-distance
`ShellStructure.shellGeneration n ℓ = n + ℓ` from the `1s` origin, refined by the principal radius.
Each subshell `(n, ℓ)` then holds `ShellStructure.subshellCapacity ℓ = 4ℓ + 2` electrons — already
derived there from monogamy pairing × angular degeneracy.

What is proved:

* `madelung_sorted` — the canonical subshell list `1s … 7p` is **exactly** the `(n+ℓ, n)`-lexicographic
  order (strictly increasing Madelung key), so the list is the Madelung order, not a posited table.
* `principalList_length` — the filling accounts for all `118` electrons up to oganesson.
* `noble_gas_closures` — the cumulative capacities at the period boundaries are
  `2, 10, 18, 36, 54, 86, 118` (He, Ne, Ar, Kr, Xe, Rn, Og), each a prefix sum of the derived
  subshell capacities.
* `principalBlock` — the concrete occupancy `Fin Z → ℕ` (electron index ↦ its principal `n`),
  with the period-3+ witnesses `sodium_valence_n_three`, `carbon_2p`, etc.

Mathlib + foundation only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Aufbau

open HqivSpine.Chemistry.ShellStructure

/-- A subshell labelled by its principal `n` and orbital `ℓ`. -/
abbrev Subshell := ℕ × ℕ

/-- The Madelung sort key of a subshell, as a single scalar. Order by the network generation
`n + ℓ` first (`ShellStructure.shellGeneration`), then by the principal radius `n`. Since every
populated subshell has `n ≤ 7 < 8`, the encoding `8(n+ℓ) + n` is faithful to the lexicographic
`(n+ℓ, n)` order. -/
def madelungKey (s : Subshell) : ℕ := 8 * shellGeneration s.1 s.2 + s.1

/-- The canonical Madelung-ordered subshell list, `1s … 7p`. This covers every element through
oganesson (`Z = 118`). Validated as *the* Madelung order by `madelung_sorted`. -/
def madelungSubshells : List Subshell :=
  [(1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (3, 2), (4, 1), (5, 0), (4, 2),
   (5, 1), (6, 0), (4, 3), (5, 2), (6, 1), (7, 0), (5, 3), (6, 2), (7, 1)]

/-- **The list is exactly the Madelung order.** The keys `8(n+ℓ)+n` are strictly increasing along
the list, i.e. the subshells are sorted by the `(n+ℓ, n)` lexicographic rule — so the order is
derived, not posited. -/
theorem madelung_sorted :
    List.Pairwise (· < ·) (madelungSubshells.map madelungKey) := by decide

/-- The electron occupancy of one subshell: its principal number `n`, repeated `4ℓ+2` times. -/
def subshellOccupancy (s : Subshell) : List ℕ :=
  List.replicate (subshellCapacity s.2) s.1

/-- The full principal-number filling list: electron index ↦ principal `n`, in Madelung order. -/
def principalList : List ℕ :=
  (madelungSubshells.map subshellOccupancy).flatten

/-- The Madelung filling accounts for exactly `118` electrons (oganesson). -/
theorem principalList_length : principalList.length = 118 := by decide

/-- Cumulative electron count through the first `k` subshells (a prefix sum of the derived
subshell capacities). -/
def configThrough (k : ℕ) : ℕ :=
  ((madelungSubshells.take k).map (fun s => subshellCapacity s.2)).sum

/-- The closed-shell (noble-gas) atomic numbers, as comparison labels. -/
def nobleGasClosures : List ℕ := [2, 10, 18, 36, 54, 86, 118]

/-- **Noble-gas closures are prefix sums of the derived capacities.** Cutting the Madelung list
after `1s`, `2p`, `3p`, `4p`, `5p`, `6p`, `7p` gives the cumulative counts
`2, 10, 18, 36, 54, 86, 118` — He, Ne, Ar, Kr, Xe, Rn, Og — using only `subshellCapacity = 4ℓ+2`. -/
theorem noble_gas_closures :
    [1, 3, 5, 8, 11, 15, 19].map configThrough = nobleGasClosures := by decide

/-- The total filling equals the full prefix sum `configThrough 19`. -/
theorem principalList_length_eq_configThrough :
    principalList.length = configThrough 19 := by decide

/-! ## Concrete occupancy and period-3+ witnesses -/

/-- The derived occupancy for a `Z`-electron atom: electron `i` carries the principal number `n` of
its Madelung-assigned subshell. (Indices past the table fall back to `0`, never reached for
`Z ≤ 118`.) This is the concrete witness for `Chemistry.Binding.slaterEffectiveCharge`'s abstract
`block`. -/
def principalBlock (Z : ℕ) : Fin Z → ℕ := fun i => principalList.getD i.val 0

/-- Hydrogen's single electron is `1s` (`n = 1`). -/
theorem hydrogen_1s : principalBlock 1 ⟨0, by omega⟩ = 1 := by decide

/-- Both of helium's electrons are `1s` (`n = 1`). -/
theorem helium_1s : principalBlock 2 ⟨0, by omega⟩ = 1 ∧ principalBlock 2 ⟨1, by omega⟩ = 1 := by
  refine ⟨by decide, by decide⟩

/-- Carbon's 6th electron is a `2p` electron (`n = 2`). -/
theorem carbon_2p : principalBlock 6 ⟨5, by omega⟩ = 2 := by decide

/-- **Period-3 valence, the legacy gap.** Sodium's outermost (11th) electron sits at `n = 3`
(the `3s` electron) — the assignment the period-≤2 Compton-shell guess could not produce. -/
theorem sodium_valence_n_three : principalBlock 11 ⟨10, by omega⟩ = 3 := by decide

/-- Potassium's outermost (19th) electron is the `4s` electron at `n = 4`: it fills *before* `3d`,
exactly the Madelung inversion `(4+0) < (3+2)`. -/
theorem potassium_valence_n_four : principalBlock 19 ⟨18, by omega⟩ = 4 := by decide

/-! ## Valence electron count and period

The valence electrons of a main-group atom are the electrons in its **highest occupied principal
shell** `n`. With the derived filling in hand this is now a Lean function, and it recovers the
period number (`topPrincipal`) and the group's valence count (`valenceCount`) directly. -/

/-- The principal-number list of a neutral `Z`-electron atom (first `Z` entries of the filling). -/
def principalConfig (Z : ℕ) : List ℕ := principalList.take Z

/-- The highest occupied principal shell — the **period** of the element. -/
def topPrincipal (Z : ℕ) : ℕ := (principalConfig Z).foldr max 0

/-- The number of electrons in the highest occupied shell — the **valence electron count**
(exact for the s/p main groups; for d-block atoms it counts the outer `ns` electrons). -/
def valenceCount (Z : ℕ) : ℕ := (principalConfig Z).count (topPrincipal Z)

/-- Carbon sits in period 2 with four valence electrons (group 14). -/
theorem carbon_valence : topPrincipal 6 = 2 ∧ valenceCount 6 = 4 := by
  refine ⟨by decide, by decide⟩

/-- Oxygen: period 2, six valence electrons (group 16). -/
theorem oxygen_valence : topPrincipal 8 = 2 ∧ valenceCount 8 = 6 := by
  refine ⟨by decide, by decide⟩

/-- Sodium: **period 3**, one valence electron (group 1) — the period-3 readout the legacy
period-≤2 model could not produce. -/
theorem sodium_valence : topPrincipal 11 = 3 ∧ valenceCount 11 = 1 := by
  refine ⟨by decide, by decide⟩

/-- Chlorine: period 3, seven valence electrons (group 17). -/
theorem chlorine_valence : topPrincipal 17 = 3 ∧ valenceCount 17 = 7 := by
  refine ⟨by decide, by decide⟩

/-- Potassium: **period 4**, one valence electron — the `4s`-over-`3d` Madelung inversion seen in
the valence count, not just the single-electron assignment. -/
theorem potassium_valence : topPrincipal 19 = 4 ∧ valenceCount 19 = 1 := by
  refine ⟨by decide, by decide⟩

/-- **The valence octet.** Neon, argon and krypton each close their outer shell with exactly `8`
valence electrons — and that `8` is the same `ShellStructure.octetCapacity` (the so(8) carrier
multiplicity), now read off the *filled configuration* rather than the s+p capacity sum. -/
theorem noble_valence_octet :
    valenceCount 10 = octetCapacity ∧ valenceCount 18 = octetCapacity ∧
      valenceCount 36 = octetCapacity := by
  refine ⟨by decide, by decide, by decide⟩

/-- The first Madelung electron sits in shell `1`. -/
theorem principalList_head : principalList.getD 0 0 = 1 := by decide

theorem le_foldr_max_of_mem {l : List ℕ} {n : ℕ} (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    simp only [List.foldr, List.mem_cons] at h ⊢
    rcases h with rfl | hl
    · exact le_max_left _ _
    · exact le_trans (ih hl) (Nat.le_max_right _ _)

private theorem le_foldr_max_of_forall_le {l : List ℕ} {M : ℕ}
    (h : ∀ x ∈ l, x ≤ M) : l.foldr max 0 ≤ M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr]
    rw [max_le_iff]
    exact ⟨h a (by simp), ih fun x hx => h x (by simp [hx])⟩

private theorem madelungSubshell_fst_le_seven : ∀ s ∈ madelungSubshells, s.1 ≤ 7 := by decide

private theorem subshellOccupancy_mem_eq {s : Subshell} {n : ℕ}
    (h : n ∈ subshellOccupancy s) : n = s.1 := by
  unfold subshellOccupancy at h
  rw [List.mem_replicate] at h
  exact h.2

theorem principalList_mem_le_seven {n : ℕ} (h : n ∈ principalList) : n ≤ 7 := by
  unfold principalList at h
  simp only [List.mem_flatten, List.mem_map] at h
  obtain ⟨occ, hocc, hn⟩ := h
  obtain ⟨s, hs, rfl⟩ := hocc
  rw [subshellOccupancy_mem_eq hn]
  exact madelungSubshell_fst_le_seven s hs

theorem mem_principalConfig {n Z : ℕ} (h : n ∈ principalConfig Z) : n ∈ principalList := by
  unfold principalConfig at h
  exact List.mem_of_mem_take h

/-- Every atom's period shell is at most shell `7` (`7p` closes the table). -/
theorem topPrincipal_le_seven (Z : ℕ) : topPrincipal Z ≤ 7 := by
  unfold topPrincipal principalConfig
  apply le_foldr_max_of_forall_le
  intro x hx
  exact principalList_mem_le_seven (mem_principalConfig hx)
/-- The first Madelung electron always occupies shell `n = 1`. -/
theorem principalBlock_first (Z : ℕ) (h : 0 < Z) : principalBlock Z ⟨0, by omega⟩ = 1 := by
  unfold principalBlock
  exact principalList_head

theorem principalList_get_zero : principalList[0] = 1 := by
  unfold principalList
  decide

/-- The `1s` shell is always present in a physical atom's configuration. -/
theorem one_mem_principalConfig (Z : ℕ) (h : 0 < Z) : 1 ∈ principalConfig Z := by
  unfold principalConfig
  apply List.mem_of_getElem? (i := 0) (a := 1)
  rw [List.getElem?_take, if_pos h, List.getElem?_eq_getElem (by decide : 0 < principalList.length)]
  simp [principalList_get_zero]

/-- **`topPrincipal Z ≥ 1` for physical `Z > 0`.** The filling begins at `1s`, so the period is
never below shell `1`. -/
theorem topPrincipal_ge_one (Z : ℕ) (h : 0 < Z) : 1 ≤ topPrincipal Z := by
  unfold topPrincipal
  exact le_foldr_max_of_mem (one_mem_principalConfig Z h)

/-- Witness: hydrogen sits in period `1`. -/
theorem topPrincipal_pos_one : topPrincipal 1 = 1 := by decide

/-! ## Shell-resolved occupancy (for Slater screening without large `Fin` sums) -/

/-- Electrons occupying principal shell `n` in a neutral `Z`-atom (`principalConfig` count). -/
def shellElectronCount (Z n : ℕ) : ℕ := (principalConfig Z).count n

/-- The last Madelung electron occupies the period shell (s/p main-group scope; fails once
`3d/4f` back-filling leaves the final index in an inner shell). -/
def lastElectronInTopShell : ℕ → Prop
  | 0 => False
  | Z + 1 => principalBlock (Z + 1) ⟨Z, by omega⟩ = topPrincipal (Z + 1)

theorem lastElectronInTopShell_carbon :
    lastElectronInTopShell 6 := by show principalBlock 6 ⟨5, by omega⟩ = topPrincipal 6; decide

theorem lastElectronInTopShell_nitrogen :
    lastElectronInTopShell 7 := by show principalBlock 7 ⟨6, by omega⟩ = topPrincipal 7; decide

theorem lastElectronInTopShell_oxygen :
    lastElectronInTopShell 8 := by show principalBlock 8 ⟨7, by omega⟩ = topPrincipal 8; decide

theorem lastElectronInTopShell_sodium :
    lastElectronInTopShell 11 := by show principalBlock 11 ⟨10, by omega⟩ = topPrincipal 11; decide

theorem lastElectronInTopShell_chlorine :
    lastElectronInTopShell 17 := by show principalBlock 17 ⟨16, by omega⟩ = topPrincipal 17; decide

theorem lastElectronInTopShell_argon :
    lastElectronInTopShell 18 := by show principalBlock 18 ⟨17, by omega⟩ = topPrincipal 18; decide

theorem sodium_shell_counts :
    shellElectronCount 11 1 = 2 ∧ shellElectronCount 11 2 = 8 ∧ shellElectronCount 11 3 = 1 := by
  decide

theorem chlorine_shell_counts :
    shellElectronCount 17 1 = 2 ∧ shellElectronCount 17 2 = 8 ∧ shellElectronCount 17 3 = 7 := by
  decide

theorem nitrogen_shell_counts :
    shellElectronCount 7 1 = 2 ∧ shellElectronCount 7 2 = 5 := by decide

theorem carbon_shell_counts :
    shellElectronCount 6 1 = 2 ∧ shellElectronCount 6 2 = 4 := by decide

theorem oxygen_shell_counts :
    shellElectronCount 8 1 = 2 ∧ shellElectronCount 8 2 = 6 := by decide

/-! ## Fin sums grouped by shell occupancy -/

open scoped BigOperators

private theorem count_take_succ' (l : List ℕ) (Z n : ℕ) (hZ : Z < l.length) :
    (l.take (Z + 1)).count n = (l.take Z).count n + if l.getD Z 0 = n then 1 else 0 := by
  rw [List.take_add_one, List.count_append]
  have hto : (l[Z]?.toList).count n = if l.getD Z 0 = n then 1 else 0 := by
    have hidx : l[Z]'hZ = l.getD Z 0 := List.getElem_eq_getD (fallback := (0 : ℕ))
    rw [List.getElem?_eq_getElem hZ, Option.toList_some, List.count_singleton]
    simp [beq_iff_eq, hidx]
  rw [hto]

private theorem principalBlock_take_succ (Z i : ℕ) (hi : i < Z) (_hZ : Z < principalList.length) :
    principalBlock (Z + 1) ⟨i, Nat.lt_succ_of_lt hi⟩ = principalBlock Z ⟨i, hi⟩ := rfl

private def castSuccPrincipalBlock (Z : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  if h : k < Z then f (principalBlock (Z + 1) (Fin.castSucc ⟨k, h⟩)) else 0

private def finPrincipalBlock (Z : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  if h : k < Z then f (principalBlock Z ⟨k, h⟩) else 0

private theorem sum_castSucc_principalBlock (Z : ℕ) (f : ℕ → ℝ) (hlen : Z < principalList.length) :
    (∑ j : Fin Z, f (principalBlock (Z + 1) (Fin.castSucc j))) =
      ∑ j : Fin Z, f (principalBlock Z j) := by
  have hleft :
      (∑ j : Fin Z, f (principalBlock (Z + 1) (Fin.castSucc j))) =
        ∑ k ∈ Finset.range Z, castSuccPrincipalBlock Z f k := by
    have hpt : ∀ j : Fin Z, f (principalBlock (Z + 1) (Fin.castSucc j)) =
        castSuccPrincipalBlock Z f j.val := fun j => by simp [castSuccPrincipalBlock, j.isLt]
    rw [← Fin.sum_univ_eq_sum_range (f := castSuccPrincipalBlock Z f) Z]
    exact Fintype.sum_congr
      (f := fun j => f (principalBlock (Z + 1) (Fin.castSucc j)))
      (g := fun j => castSuccPrincipalBlock Z f j.val) hpt
  have hright :
      ∑ j : Fin Z, f (principalBlock Z j) = ∑ k ∈ Finset.range Z, finPrincipalBlock Z f k := by
    have hpt : ∀ j : Fin Z, f (principalBlock Z j) = finPrincipalBlock Z f j.val := fun j => by
      simp [finPrincipalBlock, j.isLt]
    rw [← Fin.sum_univ_eq_sum_range (f := finPrincipalBlock Z f) Z]
    exact Fintype.sum_congr (f := fun j => f (principalBlock Z j))
      (g := fun j => finPrincipalBlock Z f j.val) hpt
  rw [hleft, hright]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp [castSuccPrincipalBlock, finPrincipalBlock, Finset.mem_range.mp hk,
    principalBlock_take_succ Z k _ hlen]

private theorem principalList_get_lt_eight {i : ℕ} (hi : i < 118) :
    principalList.getD i 0 < 8 := by
  revert i
  decide

/-- **Fin sum factorization:** electron index sum = shell occupancy sum (through `Z = 118`). -/
theorem fin_sum_principalBlock (Z : ℕ) (hZ : Z ≤ 118) (f : ℕ → ℝ) :
    ∑ j : Fin Z, f (principalBlock Z j) =
    ∑ s ∈ Finset.range 8, (shellElectronCount Z s : ℝ) * f s := by
  induction Z with
  | zero => simp [shellElectronCount, principalBlock, principalConfig]
  | succ Z ih =>
    have hlen : Z < principalList.length := by rw [principalList_length]; omega
    have hle : Z ≤ 118 := Nat.le_of_succ_le hZ
    have hsum :
        ∑ j : Fin (Z + 1), f (principalBlock (Z + 1) j) =
          ∑ j : Fin Z, f (principalBlock Z j) +
            f (principalBlock (Z + 1) ⟨Z, Nat.lt_succ_self Z⟩) := by
      calc
        ∑ j : Fin (Z + 1), f (principalBlock (Z + 1) j) =
            (∑ j : Fin Z, f (principalBlock (Z + 1) (Fin.castSucc j))) +
              f (principalBlock (Z + 1) (Fin.last Z)) :=
          Fin.sum_univ_castSucc _
        _ = ∑ j : Fin Z, f (principalBlock Z j) +
              f (principalBlock (Z + 1) ⟨Z, Nat.lt_succ_self Z⟩) := by
          simpa [Fin.last] using sum_castSucc_principalBlock Z f hlen
    have hsplit :
        ∑ s ∈ Finset.range 8, (shellElectronCount (Z + 1) s : ℝ) * f s =
          (∑ s ∈ Finset.range 8, (shellElectronCount Z s : ℝ) * f s) +
            f (principalBlock (Z + 1) ⟨Z, Nat.lt_succ_self Z⟩) := by
      have hi118 : Z < 118 := by omega
      have hmem : principalList.getD Z 0 ∈ Finset.range 8 :=
        Finset.mem_range.mpr (principalList_get_lt_eight hi118)
      calc
        ∑ s ∈ Finset.range 8, (shellElectronCount (Z + 1) s : ℝ) * f s
            = ∑ s ∈ Finset.range 8, ((shellElectronCount Z s : ℝ) * f s + if s = principalList.getD Z 0 then f s else 0) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              unfold shellElectronCount principalConfig
              rw [count_take_succ' principalList Z s hlen]
              push_cast
              by_cases heq : s = principalList.getD Z 0
              · subst heq
                simp
                ring
              · have hne : principalList.getD Z 0 ≠ s := Ne.symm heq
                simp only [if_neg heq, if_neg hne]
                ring
        _ = (∑ s ∈ Finset.range 8, (shellElectronCount Z s : ℝ) * f s) +
              ∑ s ∈ Finset.range 8, (if s = principalList.getD Z 0 then f s else 0) :=
            Finset.sum_add_distrib
        _ = (∑ s ∈ Finset.range 8, (shellElectronCount Z s : ℝ) * f s) +
              f (principalList.getD Z 0) := by
              rw [Finset.sum_ite_eq' (s := Finset.range 8) (a := principalList.getD Z 0) (b := f),
                if_pos hmem]
        _ = (∑ s ∈ Finset.range 8, (shellElectronCount Z s : ℝ) * f s) +
              f (principalBlock (Z + 1) ⟨Z, Nat.lt_succ_self Z⟩) := rfl
    rw [hsum, ih hle, hsplit]

/-! ## Explicit Madelung blocks used by Slater screening proofs (comparison with textbook `Z_eff`). -/
theorem principalBlock_seven (i : Fin 7) :
    principalBlock 7 i = [1, 1, 2, 2, 2, 2, 2][i.val]! := by
  fin_cases i <;> decide

theorem principalBlock_eight (i : Fin 8) :
    principalBlock 8 i = [1, 1, 2, 2, 2, 2, 2, 2][i.val]! := by
  fin_cases i <;> decide

theorem principalBlock_eleven (i : Fin 11) :
    principalBlock 11 i = [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3][i.val]! := by
  fin_cases i <;> decide

theorem principalBlock_seventeen (i : Fin 17) :
    principalBlock 17 i = [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3][i.val]! := by
  fin_cases i <;> decide

/-! ## IUPAC main-group number from valence count

For the s/p main groups: groups `1–2` when `valence ≤ 2`, and groups `13–18` when `valence ≥ 3`
via `valence + 10`. D-block bookkeeping is out of scope here. -/

/-- IUPAC group number for an s/p main-group element from its derived valence count. -/
def iupacMainGroupNumber (Z : ℕ) : ℕ :=
  if valenceCount Z ≤ 2 then valenceCount Z else valenceCount Z + 10

theorem sodium_iupac_group_one : iupacMainGroupNumber 11 = 1 := by decide

theorem chlorine_iupac_group_seventeen : iupacMainGroupNumber 17 = 17 := by decide

theorem carbon_iupac_group_fourteen : iupacMainGroupNumber 6 = 14 := by decide

theorem neon_iupac_group_eighteen : iupacMainGroupNumber 10 = 18 := by decide

end HqivSpine.Chemistry.Aufbau
