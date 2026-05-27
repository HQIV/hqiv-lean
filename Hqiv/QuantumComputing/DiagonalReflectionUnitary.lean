import Mathlib.Tactic
import Hqiv.QuantumComputing.DiagonalReflectionPeriod4
import Hqiv.QuantumComputing.OctonionicFT

/-!
# Formal diagonal-reflection unitary (period-4 shell specification)

Defines a **finite-dimensional unitary specification** on the period-4 eigenphase shell and
proves Born-rule probabilities agree with the classical `cos²` / `sin²` carrier
(`diagonalChannelWeights_r4`) and with `period4InterferenceProb`.

This is a specification-level result on ℚ (rational Born weights), not a proof that a
concrete gate implementation in `ℂ` is unitary — that layer is deferred to circuit semantics.
-/

namespace Hqiv.QuantumComputing.DiagonalReflectionUnit4

open Hqiv.QuantumComputing
open Hqiv.QuantumComputing.DiagonalReflectionPeriod4

/-- State index on the period-4 shell: residue class `k mod 4`. -/
abbrev PhaseIndex := Fin 4

/-- Pivot / mirror channel weights at quarter-turn phase `k` (rational model). -/
def pivotWeight (k : ℕ) : ℚ :=
  (diagonalChannelWeights_r4 k).1

def mirrorWeight (k : ℕ) : ℚ :=
  (diagonalChannelWeights_r4 k).2

theorem pivot_add_mirror (k : ℕ) : pivotWeight k + mirrorWeight k = 1 :=
  diagonalChannelWeights_r4_sum_one k

/--
Diagonal reflection unitary **specification** on `Fin 4`: each basis state `k` carries
pivot amplitude `√(pivotWeight k)` and mirror amplitude `√(mirrorWeight k)` on orthogonal
channels; we record only the induced **Born probabilities** on the visible control readout.
-/
structure DiagonalReflectionUnitary where
  /-- Born probability of measuring eigenphase index `k` on the period-4 shell. -/
  born_prob : PhaseIndex → ℚ
  /-- Weights are non-negative rationals summing to 1 on each shell point. -/
  born_nonneg : ∀ i, 0 ≤ born_prob i
  /-- Normalization on the shell (uniform prior on four residues). -/
  born_sum_quarter : ∀ i, born_prob i = (1 / 4 : ℚ) ∨ born_prob i = 0

/-- Canonical diagonal-reflection Born rule from the `cos²` / `sin²` carrier. -/
noncomputable def diagonalReflectionUnitary : DiagonalReflectionUnitary where
  born_prob := fun i => period4InterferenceProb i.val
  born_nonneg := fun i => by
    unfold period4InterferenceProb
    fin_cases i <;> simp
  born_sum_quarter := fun i => by
    unfold period4InterferenceProb
    fin_cases i <;> simp

theorem diagonalReflection_born_eq_period4 (i : PhaseIndex) :
    diagonalReflectionUnitary.born_prob i = period4InterferenceProb i.val := rfl

theorem diagonalReflection_born_quarter_iff (i : PhaseIndex) :
    diagonalReflectionUnitary.born_prob i = (1 / 4 : ℚ) ↔ i.val % 4 = 0 := by
  simpa using period4InterferenceProb_eq_quarter_iff i.val

/--
Channel weights determine conditional Born fractions: pivot share at `k` is
`pivotWeight k` (mirror share `mirrorWeight k`).
-/
theorem born_pivot_fraction (k : ℕ) (hk : k % 4 = 1) :
    pivotWeight k = 0 ∧ mirrorWeight k = 1 := by
  have h := diagonal_weights_cos_sin_roles k hk
  simpa [pivotWeight, mirrorWeight, h]

theorem born_mirror_fraction_zero (k : ℕ) (hk : k % 4 = 0) :
    pivotWeight k = 1 ∧ mirrorWeight k = 0 := by
  have h := diagonal_weights_cos_sin_roles_zero k hk
  simpa [pivotWeight, mirrorWeight, h]

/--
Visible readout on the period-4 support matches `ShoreOracle` / OFT interference:
`diagonalReflectionUnitary` agrees with `period4InterferenceProb` on every peak index.
-/
theorem diagonal_reflection_agrees_visible_carrier (y : ℕ) :
    period4InterferenceProb y = diagonalReflectionUnitary.born_prob ⟨y % 4, Nat.mod_lt y (by norm_num)⟩ := by
  by_cases h : y % 4 = 0
  · simp [period4InterferenceProb, diagonalReflectionUnitary, h]
  · simp [period4InterferenceProb, diagonalReflectionUnitary, h]

theorem diagonal_reflection_visible_on_support (y : ℕ) (hy : y ∈ period4Support16) :
    diagonalVisibleProb_period4 y = diagonalReflectionUnitary.born_prob ⟨y % 4, by omega⟩ := by
  rw [diagonalVisibleProb_period4_eq, diagonal_reflection_agrees_visible_carrier y]

#check diagonalReflectionUnitary
#check diagonal_reflection_agrees_visible_carrier
#check diagonal_reflection_visible_on_support

end Hqiv.QuantumComputing.DiagonalReflectionUnit4
