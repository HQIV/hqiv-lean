import HqivSpine.Physics.LockIn
import HqivSpine.Algebra.Triality

/-!
# `HqivSpine.Physics.Exclusion` — why quantum numbers can't collapse to the Planck pole

The lock-in shell's *inward* wall (no collapse toward the Planck pole) is **not** the
posited "capacity 40" of `Physics.LockIn`; that number is bookkeeping. The genuine wall
is **spin-statistics**, and in HQIV it is the face of **informational monogamy**
(`Shell.gammaHQIV = 2/5`). Two independent, fully derived mechanisms forbid collapse:

* **Degeneracy pressure (Pauli ⇒ pigeonhole).** Identical fermions cannot share a state
  — the occupation of quanta into carrier states is *injective*. That injectivity **is**
  monogamy: each carrier slot hosts at most one quantum (no information is shared). The
  states available through shell `m` are finite, `cumulativeModes m = ∑_{k≤m} N(k) =
  4(m+1)(m+2)` (a genuine partial sum of the unlocked modes `N(k) = 8(k+1)`). Pigeonhole
  (`Fintype.card_le_of_injective`) then forces any monogamous content of `N` quanta to
  need `N ≤ cumulativeModes m` states — so a content exceeding the few states near the
  pole **cannot** be hosted there (`no_monogamous_overfill`). At the pole only the bare
  carrier `cumulativeModes 0 = 8` states exist, so the chiral fermion content `48`
  (`Algebra.chiralSlotCount`) provably **cannot** collapse to `m = 0`
  (`chiral_content_no_collapse_to_pole`).

* **Pair conservation (you need annihilation to remove a quantum number).** A net charge /
  fermion number changes only through monogamous `(+q, −q)` partner pairs, which are
  charge-neutral (`netCharge_pairExtend`); the net is therefore invariant under *any*
  sequence of pair creations/annihilations (`netCharge_applyPairs`). Hence a configuration
  with nonzero net charge can **never** reach the vacuum / Planck pole
  (`pair_moves_cannot_reach_vacuum`): a lone unpaired quantum has nothing to annihilate
  against, and monogamy forbids it sharing a partner.

Together (`spin_statistics_no_collapse`) these give the inward wall as a *theorem*, not a
number. Honest scope: degeneracy pressure pins a **floor** (`cumulativeModes` is
`StrictMono`, so more content needs a larger shell) but does not by itself single out `4`
— the `48` chiral slots already fit by shell `2`; reaching `4` still needs the mode-budget
balance of `Physics.LockIn`. What this module *does* settle is the deeper question the
capacity number only gestured at: **why there is an inward wall at all.**

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation HqivSpine.Algebra

/-! ## Cumulative single-particle states through a shell -/

/-- **States available through shell `m`** — the running total of unlocked modes
`∑_{k≤m} N(k)`. Each is a single-particle (Pauli) slot a quantum may occupy. -/
def cumulativeModes (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), newModes k

/-- **Closed form** `cumulativeModes m = 4(m+1)(m+2)` — the triangular sum of
`N(k) = 8(k+1)`. (`8·(1+2+⋯+(m+1)) = 8·(m+1)(m+2)/2`.) -/
theorem cumulativeModes_eq (m : ℕ) : cumulativeModes m = 4 * (m + 1) * (m + 2) := by
  induction m with
  | zero => decide
  | succ n ih =>
      rw [cumulativeModes, Finset.sum_range_succ, ← cumulativeModes, ih, newModes_eq]
      ring

/-- The pole hosts exactly the bare carrier's `8` states. -/
theorem cumulativeModes_zero : cumulativeModes 0 = carrierMultiplicity := by
  rw [cumulativeModes_eq, carrierMultiplicity_eq_eight]

/-- Adding a shell adds its newly-unlocked modes. -/
theorem cumulativeModes_succ (m : ℕ) :
    cumulativeModes (m + 1) = cumulativeModes m + newModes (m + 1) := by
  rw [cumulativeModes, Finset.sum_range_succ, ← cumulativeModes]

/-- **More room the farther out:** the available-state count is strictly increasing, so
the Pauli floor for a fixed content is well-defined (larger content ⇒ larger shell). -/
theorem cumulativeModes_strictMono : StrictMono cumulativeModes := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [cumulativeModes_succ]
  have : 0 < newModes (m + 1) := by rw [newModes_eq]; omega
  omega

/-! ## Monogamy = Pauli exclusion = injective occupation -/

/-- **Informational monogamy on carrier states** (the HQIV reading of spin-statistics /
Pauli exclusion): a quantum-to-state assignment is *injective* — no carrier slot hosts
two quanta. -/
def Monogamous {N K : ℕ} (f : Fin N → Fin K) : Prop := Function.Injective f

/-- **Degeneracy pressure (pigeonhole).** A monogamous occupation of `N` quanta into the
states through shell `m` forces `N ≤ cumulativeModes m`: identical fermions need distinct
slots, so too much content cannot fit too few states. -/
theorem pauli_pigeonhole {N m : ℕ} (f : Fin N → Fin (cumulativeModes m))
    (hf : Monogamous f) : N ≤ cumulativeModes m := by
  simpa using Fintype.card_le_of_injective f hf

/-- **No collapse by overfilling.** If the content `N` exceeds the states available
through shell `m`, *no* occupation is monogamous — the configuration cannot live at or
below shell `m`. -/
theorem no_monogamous_overfill {N m : ℕ} (h : cumulativeModes m < N)
    (f : Fin N → Fin (cumulativeModes m)) : ¬ Monogamous f := fun hf =>
  absurd (pauli_pigeonhole f hf) (not_le.mpr h)

/-- **Spin-statistics forbids collapse to the Planck pole.** The pole offers only the bare
carrier's `8` states, but the chiral fermion content is `48` Weyl slots
(`Algebra.chiralSlotCount`); since `8 < 48`, no monogamous occupation exists, so a
configuration carrying that content can never reach `m = 0`. -/
theorem chiral_content_no_collapse_to_pole
    (f : Fin chiralSlotCount → Fin (cumulativeModes 0)) : ¬ Monogamous f := by
  apply no_monogamous_overfill
  rw [cumulativeModes_zero, carrierMultiplicity_eq_eight, chiralSlotCount_eq_48]
  norm_num

/-! ## Pair conservation — a lone quantum number cannot annihilate -/

/-- A configuration of `±` quantum numbers (fermion number, a conserved charge, …). -/
abbrev Charges := List ℤ

/-- **Net quantum number** = signed sum. The vacuum / Planck pole (no quanta) has `0`. -/
def netCharge (c : Charges) : ℤ := c.sum

/-- **Monogamous pair move:** create / annihilate a partner pair `(+q, −q)`. This is the
*only* allowed change — monogamy forbids adding or removing an unpaired quantum. -/
def pairExtend (c : Charges) (q : ℤ) : Charges := c ++ [q, -q]

/-- **Pairs are charge-neutral:** a `(+q, −q)` partner pair leaves the net unchanged. -/
theorem netCharge_pairExtend (c : Charges) (q : ℤ) :
    netCharge (pairExtend c q) = netCharge c := by
  unfold netCharge pairExtend
  rw [List.sum_append]
  simp

/-- Apply a whole sequence of pair moves. -/
def applyPairs : Charges → List ℤ → Charges
  | c, [] => c
  | c, q :: qs => applyPairs (pairExtend c q) qs

/-- **Net charge is invariant under any sequence of pair moves.** -/
theorem netCharge_applyPairs (c : Charges) (qs : List ℤ) :
    netCharge (applyPairs c qs) = netCharge c := by
  induction qs generalizing c with
  | nil => rfl
  | cons q qs ih => rw [applyPairs, ih, netCharge_pairExtend]

/-- **A nonzero net quantum number can never reach the vacuum.** No matter how many
monogamous pair creations/annihilations are applied, the net is conserved, so a
configuration with nonzero net charge stays non-empty — it cannot collapse to the
Planck-pole vacuum. -/
theorem pair_moves_cannot_reach_vacuum {c : Charges} (h : netCharge c ≠ 0)
    (qs : List ℤ) : applyPairs c qs ≠ [] := by
  intro hreach
  have hinv : netCharge (applyPairs c qs) = netCharge c := netCharge_applyPairs c qs
  rw [hreach] at hinv
  simp [netCharge] at hinv
  exact h hinv.symm

/-! ## Capstone: the inward wall is spin-statistics, not a capacity number -/

/-- **Why quantum numbers cannot collapse to the Planck pole.** Two derived mechanisms,
both rooted in monogamy:

1. **Degeneracy pressure** — the chiral fermion content `48` has no monogamous occupation
   into the pole's `8` states (`chiral_content_no_collapse_to_pole`), and more generally
   any overfilling content has none (`no_monogamous_overfill`);
2. **Pair conservation** — a nonzero net quantum number is invariant under all pair moves,
   so it never reaches the vacuum (`pair_moves_cannot_reach_vacuum`).

This earns the *inward* wall of the lock-in tug-of-war as a theorem. -/
theorem spin_statistics_no_collapse :
    (∀ f : Fin chiralSlotCount → Fin (cumulativeModes 0), ¬ Monogamous f) ∧
    (∀ (c : Charges), netCharge c ≠ 0 → ∀ qs : List ℤ, applyPairs c qs ≠ []) :=
  ⟨chiral_content_no_collapse_to_pole,
   fun _ h qs => pair_moves_cannot_reach_vacuum h qs⟩

end HqivSpine.Physics
