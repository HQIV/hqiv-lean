import Hqiv.Physics.FanoResonance

/-!
# Cycles, Fano indexing, and Hodge **probe** (Millennium roadmaps)

**Purpose:** minimal **algebraic** scaffolding to align `AGENTS/HODGE_HQIV_NARRATIVE.md` and the Fano mod‑7
story with abstract **cycle** carriers — without Chow groups, Hodge classes, or the Hodge conjecture.

**What is here**

* `FanoIndexedCycles` — seven distinguished objects of type `C`, one per `FanoVertex`.
* `canonicalFanoCycles` — the identity indexing on `C = FanoVertex`.
* Surjectivity / bijectivity lemmas for the canonical case.
* `shellResidueFano` — same residue constructor as the physics zeta partition (for cross-module alignment).
* `shellResidueFano_of_f_val_add_seven_mul` — each strand `f.val + 7·k` in the Fano zeta split carries tag `f`.

**What is not here:** complex projective varieties, `H^{p,q}`, rational equivalence, periods as integrals
of algebraic forms, or L-functions.
-/

namespace Hqiv.Algebra

open Hqiv.Physics

/-- Seven distinguished cycles (or cycle tokens) tagged by Fano vertices. -/
structure FanoIndexedCycles (C : Type*) where
  cycleOf : FanoVertex → C

/-- Canonical tagging: vertices label themselves. -/
def canonicalFanoCycles : FanoIndexedCycles FanoVertex where
  cycleOf := id

theorem canonicalFanoCycles_surjective :
    Function.Surjective (canonicalFanoCycles.cycleOf) :=
  Function.surjective_id

theorem canonicalFanoCycles_bijective :
    Function.Bijective (canonicalFanoCycles.cycleOf) :=
  Function.bijective_id

/-- Fano vertex of shell residue `m % 7` (matches `Hqiv.Physics.fano_vertex_of_shell` naming intent). -/
def shellResidueFano (m : ℕ) : FanoVertex :=
  ⟨m % 7, Nat.mod_lt m (by decide : 0 < 7)⟩

theorem shellResidueFano_val (m : ℕ) : (shellResidueFano m).val = m % 7 :=
  rfl

theorem surjective_shellResidueFano : Function.Surjective shellResidueFano := by
  intro f
  refine ⟨f.val, ?_⟩
  ext
  dsimp [shellResidueFano]
  exact Nat.mod_eq_of_lt f.is_lt

/-- Along the arithmetic progression `f.val + 7·k` used in `zeta_HQIV_eq_sum_Fano_residue_classes`,
    the algebra cycle tag is **exactly** `f` — the seven-way zeta split aligns with `FanoIndexedCycles`. -/
theorem shellResidueFano_of_f_val_add_seven_mul (f : FanoVertex) (k : ℕ) :
    shellResidueFano (f.val + 7 * k) = f := by
  apply Fin.ext
  dsimp [shellResidueFano]
  rw [Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt f.is_lt

end Hqiv.Algebra
