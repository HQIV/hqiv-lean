import Mathlib.Tactic
import Hqiv.QuantumComputing.OctonionicFT
import Hqiv.QuantumComputing.SemiprimeOrthogonalDiagonalQuantum

/-!
# Diagonal reflection weights and `period4InterferenceProb` (N = 15 shell)

Links the classical/quantum **specification** of orthogonal-diagonal eigenphase weights
(`cos²` on pivot channel, `sin²` on mirror channel) to the closed-form Born pattern
`period4InterferenceProb` already used in `ShoreOracle` for `N = 15`.

This is **not** a full Hilbert-space derivation of a unitary diagonal reflection gate.
It proves the rational peak bookkeeping on the period-4 shell matches the OFT scaffold.
-/

namespace Hqiv.QuantumComputing.DiagonalReflectionPeriod4

open Hqiv.QuantumComputing
open Hqiv.QuantumComputing.SemiprimeOrthogonalDiagonalQuantum

/-- Quarter-turn lattice model for `θ = 2πk/4`: `(cos²θ, sin²θ)` as rationals. -/
def diagonalChannelWeights_r4 (k : ℕ) : ℚ × ℚ :=
  match k % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 0)
  | _ => (0, 1)

theorem diagonalChannelWeights_r4_sum_one (k : ℕ) :
    (diagonalChannelWeights_r4 k).1 + (diagonalChannelWeights_r4 k).2 = 1 := by
  rcases h : k % 4 with _ | _ | _ | _ <;> simp [diagonalChannelWeights_r4, h] <;> norm_num

/-- Pivot channel is cos²-type; mirror channel is sin²-type at `k ≡ 1 (mod 4)`. -/
theorem diagonal_weights_cos_sin_roles (k : ℕ) (hk : k % 4 = 1) :
    diagonalChannelWeights_r4 k = (0, 1) := by
  simp [diagonalChannelWeights_r4, hk]

theorem diagonal_weights_cos_sin_roles_zero (k : ℕ) (hk : k % 4 = 0) :
    diagonalChannelWeights_r4 k = (1, 0) := by
  simp [diagonalChannelWeights_r4, hk]

/--
Visible measurement probability on index `y` after uniform mixing on the period-4 shell:
matches `period4InterferenceProb`.
-/
def diagonalVisibleProb_period4 (y : ℕ) : ℚ :=
  period4InterferenceProb y

theorem diagonalVisibleProb_period4_eq (y : ℕ) :
    diagonalVisibleProb_period4 y = period4InterferenceProb y := rfl

theorem diagonalVisibleProb_quarter_iff (y : ℕ) :
    diagonalVisibleProb_period4 y = (1 / 4 : ℚ) ↔ y % 4 = 0 :=
  period4InterferenceProb_eq_quarter_iff y

/--
On the `N = 15` dominant eigenphase (`k = 1`, `r = 4`), the diagonal carrier places unit
weight on the sin² (mirror) channel — consistent with a peak at quarter phase.
-/
theorem n15_dominant_eigenphase_weights :
    diagonalChannelWeights_r4 eigenphaseMeasurement_n15.k = (0, 1) := by
  simp [eigenphaseMeasurement_n15, diagonalChannelWeights_r4]

theorem n15_visible_probs_match_shoreOracle :
    ∀ y ∈ period4Support16, diagonalVisibleProb_period4 y = (1 / 4 : ℚ) := by
  intro y hy
  have hy' : y = 0 ∨ y = 4 ∨ y = 8 ∨ y = 12 := by simpa [period4Support16] using hy
  rcases hy' with rfl | rfl | rfl | rfl
  all_goals simp [diagonalVisibleProb_period4, period4InterferenceProb]

#check diagonalChannelWeights_r4_sum_one
#check n15_dominant_eigenphase_weights
#check n15_visible_probs_match_shoreOracle

end Hqiv.QuantumComputing.DiagonalReflectionPeriod4
