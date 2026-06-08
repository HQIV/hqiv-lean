import Mathlib.Analysis.Complex.Exponential
import Mathlib.NumberTheory.ArithmeticFunction.Misc

import Hqiv.Algebra.IntegerLatticeShellCount8
import Hqiv.Algebra.OctonionAxisAngles

/-!
# Quaternion block, `Ω`–additivity, and the arity phasor on the unwrapped circle

This module is the **next formal layer** after `IntegerLatticeShellCount8` / `sumSqInt8_embedNatFour`:

* The **quaternionic subalgebra** is modeled by the first four `Fin 8` coordinates (`quaternionEmbed`).
  Shell mass there matches `∑_{i<4} |zᵢ|²`, so Lagrange four-squares traffic lives entirely in this block
  when the tail is zero.

* **Total prime-factor count** `Ω` is **additive on multiplication** (`Ω (m·n) = Ω m + Ω n` for `m,n ≠ 0`).
  Together with `intrinsicShellAxisAngle m = π / (2·Ω m)`, this is the clean arithmetic input that
  later harmonic-analysis packaging (discrete Fourier on a window, moiré score) cites as
  “representation-level” bookkeeping on the quaternion block.

* On the **continuous** circle model, the complex **phasor** at the narrative axis angle
  `axisAngle k = π/(2k)` has **unit modulus** — the isolated “Fourier atom” at that frequency in the
  complex exponential basis.

**Not claimed here:** that a specific DFT on a finite time-window attains a **unique peak** at bin
`k` without fixing the window, weights, and projection — that step remains pipeline glue (see
`AGENTS/archive/OCTONION_SPHERE_PATCH.md`).
-/

noncomputable section

open scoped ArithmeticFunction.Omega
open ArithmeticFunction

namespace Hqiv.Algebra

/-- Quaternionic block embedded in `ℤ⁸` (indices `0…3`; last four slots zero). -/
def quaternionEmbed (z : Fin 4 → ℤ) : Fin 8 → ℤ
  | ⟨0, _⟩ => z 0
  | ⟨1, _⟩ => z 1
  | ⟨2, _⟩ => z 2
  | ⟨3, _⟩ => z 3
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => 0
  | ⟨7, _⟩ => 0

theorem sumSqInt8_quaternionEmbed (z : Fin 4 → ℤ) :
    sumSqInt8 (quaternionEmbed z) = ∑ i : Fin 4, (z i).natAbs ^ 2 := by
  dsimp [sumSqInt8, quaternionEmbed]
  rw [Fin.sum_univ_eight, Fin.sum_univ_four]
  ring

/-- Coprime-free **additivity** of `Ω` on nonzero factors (prime-factor multiset union). -/
theorem Omega_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : Ω (m * n) = Ω m + Ω n :=
  cardFactors_mul hm hn

/-- Intrinsic `π/(2·Ω·)` angle for a **product shell**: denominator adds like `Ω`. -/
theorem intrinsicShellAxisAngle_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 1 < m * n) :
    intrinsicShellAxisAngle (m * n) hmn = Real.pi / (2 * (Ω m + Ω n)) := by
  rw [intrinsicShellAxisAngle_eq, Omega_mul hm hn]
  simp [Nat.cast_add]

/-- For real `t`, `exp(i·t)` lies on the unit circle (`‖·‖ = 1`). -/
theorem complex_exp_mul_I_real_unit (t : ℝ) : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  have hre : (Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.ofReal_re]
  rw [Complex.norm_exp, hre, Real.exp_zero]

/-- Complex unit phasor at the narrative arity axis `π/(2k)` (`k ≥ 1`). -/
theorem complex_exp_axisAngle_unit (k : ℕ) (hk : 0 < k) :
    ‖Complex.exp (Complex.I * (axisAngle k hk : ℂ))‖ = 1 :=
  complex_exp_mul_I_real_unit (axisAngle k hk)

/-- Same unit-modulus statement for `intrinsicShellAxisAngle` on any shell `m > 1`. -/
theorem complex_exp_intrinsicShellAxisAngle_unit (m : ℕ) (hm : 1 < m) :
    ‖Complex.exp (Complex.I * (intrinsicShellAxisAngle m hm : ℂ))‖ = 1 :=
  complex_exp_mul_I_real_unit (intrinsicShellAxisAngle m hm)

end Hqiv.Algebra

end
