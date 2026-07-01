import HqivSpine.Chemistry.ShellStructure
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
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

end HqivSpine.Chemistry.Aufbau
