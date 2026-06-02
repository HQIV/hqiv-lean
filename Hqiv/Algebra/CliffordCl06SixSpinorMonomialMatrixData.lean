import Hqiv.Algebra.CliffordCl06SixSpinorGammaMatInt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Spinor monomial Gram matrix (`W`) over `ℤ`

For each bitmask `m : Fin 64`, `spinorGammaMonomialMatZ m` is the ordered `γ` product in the
integral Kronecker model (`CliffordCl06SixSpinorGammaMatInt`).  The **normalized Frobenius**
pairing is the `64 × 64` integer matrix
`Wᵢⱼ := (1/8) * ∑_{a,b : Fin 8} (Mᵢ)ₐᵦ * (Mⱼ)ₐᵦ`.

The factor `8` divides every Frobenius sum entry; we record this as an explicit axiom (see
`scripts/verify_spinor_frob_sum_div8.py` for a fast recomputation over all `64 × 64` pairs).

## Mod-`101` determinant certificate

The heavy finite check lives in `scripts/spinor_monomial_gram_det_mod101.py` (exit `0` on success).
Lean records it as `spinorMonomialGramColumnsZMod101_det`; from this we prove
`spinorMonomialGramColumns.det ≠ 0` without `native_decide` on the full integer determinant.
-/

namespace Hqiv.Algebra

open scoped BigOperators

/-- Frobenius inner-product sum `∑_{a,b} (Mᵢ)ₐᵦ (Mⱼ)ₐᵦ` over `ℤ` (without the `1/8` normalization). -/
def spinorMonomialGramFrobSum (i j : Fin 64) : ℤ :=
  ∑ a : Fin 8, ∑ b : Fin 8, spinorGammaMonomialMatZ i a b * spinorGammaMonomialMatZ j a b

/--
Divisibility of each Frobenius sum by `8`.

**Executable check:** `python3 scripts/verify_spinor_frob_sum_div8.py` (exit `0` on success).

Kernel `native_decide` on all `64 × 64` pairs is omitted here because it is prohibitively slow in
CI-sized builds.
-/
axiom eight_dvd_spinorMonomialGramFrobSum (i j : Fin 64) : 8 ∣ spinorMonomialGramFrobSum i j

/-- Normalized Frobenius Gram matrix `W` with entries in `ℤ`. -/
def spinorMonomialGramColumns : Matrix (Fin 64) (Fin 64) ℤ :=
  fun i j => spinorMonomialGramFrobSum i j / 8

theorem spinorMonomialGramFrobSum_eq_mul_spinorMonomialGramColumns (i j : Fin 64) :
    spinorMonomialGramFrobSum i j = 8 * spinorMonomialGramColumns i j := by
  simp [spinorMonomialGramColumns, Int.mul_ediv_cancel' (eight_dvd_spinorMonomialGramFrobSum i j)]

/-! ### Mod-`101` determinant certificate -/

/-- Reduction mod `101` of `spinorMonomialGramColumns` (determinant certificate). -/
def spinorMonomialGramColumnsZMod101 : Matrix (Fin 64) (Fin 64) (ZMod 101) :=
  (Int.castRingHom (ZMod 101)).mapMatrix spinorMonomialGramColumns

/--
**Trusted computation** (same role as `so8CoordMatrix_transpose_mul_self` in `So8CoordMatrix`).

`det` of the mod-`101` Gram matrix is `1` (hence nonzero).

Proof reference: `scripts/spinor_monomial_gram_det_mod101.py` — recomputes `det` in `F₁₀₁`, and
checks equality with `1` (exit code `0` on success).
-/
axiom spinorMonomialGramColumnsZMod101_det :
    spinorMonomialGramColumnsZMod101.det = 1

theorem spinorMonomialGramColumns_det_ne_zero : spinorMonomialGramColumns.det ≠ 0 := by
  intro h
  have hmap := (Int.castRingHom (ZMod 101)).map_det spinorMonomialGramColumns
  rw [h, map_zero] at hmap
  change 0 = spinorMonomialGramColumnsZMod101.det at hmap
  rw [spinorMonomialGramColumnsZMod101_det] at hmap
  exact (by decide : (0 : ZMod 101) ≠ 1) hmap

end Hqiv.Algebra
