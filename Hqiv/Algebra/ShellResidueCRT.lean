import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# CRT shell typing: `mod 4` × `mod 7` ↔ `mod 28`

`4` and `7` are coprime, so congruence **`mod 28`** is equivalent to **`(mod 4, mod 7)`**. This is the
arithmetic backbone for combining the Fano **`mod 7`** partition with the **`mod 4`** axis from the
ζ / shell-succ story (`ShellIndexRiemannZetaBridge`).

Pure `ℕ` / `ZMod 28` — no analytic continuation.
-/

namespace Hqiv.Algebra

theorem coprime_four_seven : Nat.Coprime 4 7 := by
  decide

theorem modEq_twenty_eight_iff {a b : ℕ} :
    a ≡ b [MOD 28] ↔ a ≡ b [MOD 4] ∧ a ≡ b [MOD 7] := by
  rw [show (28 : ℕ) = 4 * 7 by norm_num]
  exact (Nat.modEq_and_modEq_iff_modEq_mul coprime_four_seven).symm

theorem modEq_twenty_eight_of_mod_four_and_mod_seven {a b : ℕ} (h4 : a ≡ b [MOD 4])
    (h7 : a ≡ b [MOD 7]) : a ≡ b [MOD 28] :=
  modEq_twenty_eight_iff.mpr ⟨h4, h7⟩

/-- Class of `m` in `ℤ/28ℤ` (joint residue). -/
abbrev shellClass28 (m : ℕ) : ZMod 28 :=
  m

theorem shellClass28_eq_iff_modEq (a b : ℕ) : shellClass28 a = shellClass28 b ↔ a ≡ b [MOD 28] := by
  simp [shellClass28, ZMod.natCast_eq_natCast_iff', Nat.ModEq]

end Hqiv.Algebra
