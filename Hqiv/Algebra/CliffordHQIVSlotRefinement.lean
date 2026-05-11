import Hqiv.Algebra.CliffordMinimalIdeal
import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.GeneratorsFromAxioms
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Clifford minimal ideals vs HQIV hypercharge / rapidity **slots**

`Hqiv.Algebra.CliffordMinimalIdeal` proves the **algebraic pattern** behind Furey’s
use of minimal left ideals in the **division-ring / simple-module** case: for the
concrete `Cl(1) ≅ ℂ` Clifford model, `⊤` is the **unique** nonzero left ideal.

This file packages the **HQIV-side refinement certificate** that matches the
*slot-level* story in `Hqiv.Physics.RapidityIdealPurposeBridge`:

* **Clifford slot (proved here, `Cl(1)` model):** `⊤` is a minimal nonzero left
  ideal in `CliffordOneDim`.
* **Matrix hypercharge slot (proved here):** the ℝ-line spanned by
  `Hqiv.phaseLiftDelta` / `hyperchargeGenerator` has **real** dimension `1`.

Together these are the correct “two halves” of the narrative:

* the **ideal-theoretic** language fixes a **one-generator** submodule pattern
  (here, the whole field as a simple left module);
* the **SM embedding** fixes the **Lie-algebra direction** of hypercharge as the
  concrete matrix `Δ` on the octonion carrier (`SMEmbedding`, `PhaseLiftDelta`).

What is **still not** formalized (and remains the Furey bridge obligation) is a
**single** Clifford algebra whose minimal ideals are **8-real-dimensional** and
equivariant with the octonion spinor representation tying `ι(·)` to the **same**
8×8 matrices as `phaseLiftDelta` — i.e. a `Cl(6)` (or complexified `Cl(6)`)
spinor isomorphism layer.

**Progress:** `Hqiv.Algebra.CliffordSixImaginaryScaffold` builds **\(\mathrm{Cl}(0,6)\)**
on `e₁,…,e₆` with `ι(δⱼ)² = -1` in the abstract algebra, and `Hqiv.Algebra.OctonionLeftMulSquare`
proves **`L(e_k)² = -I₈`** matrix-wise for all imaginary units.  **`Hqiv.Algebra.CliffordCl06SixDimension`**
proves the abstract algebra has **`finrank = 64`** (exterior-algebra path); **`Hqiv.Algebra.OctonionLeftMulCliffordObstruction`**
records that naive **left-mult** matrices on the six directions **cannot** satisfy the mixed
Clifford relations needed for a `CliffordAlgebra.lift` into `Mat(8,ℝ)` for that `Q`.
Ideal-to-spinor transport is **representation-conditional** (`Hqiv.Algebra.CliffordCl06SixSpinorBridge`);
a concrete `ρ` is `Hqiv.Algebra.cl06StandardSpinorRho` (`Hqiv.Algebra.CliffordCl06SixStandardSpinorRho`).
-/

namespace Hqiv.Algebra

open Module Submodule

theorem phaseLiftDelta_ne_zero : Hqiv.phaseLiftDelta ≠ 0 := by
  intro h
  have h17 := congr_arg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M 1 7) h
  simp [Hqiv.phaseLiftDelta_17] at h17

/-- The ℝ-line in `Matrix (Fin 8) (Fin 8) ℝ` through HQIV’s phase-lift / hypercharge
generator has dimension `1`. -/
theorem hqiv_hypercharge_line_finrank_one :
    Module.finrank ℝ (ℝ ∙ Hqiv.phaseLiftDelta) = 1 :=
  finrank_span_singleton phaseLiftDelta_ne_zero

/--
Joint **slot refinement** certificate: a concrete minimal left ideal in the
`Cl(1)` Clifford model **and** the HQIV hypercharge matrix line in `Mat(8,ℝ)`.

This is the precise Lean sense in which “minimal ideals refine the same slots”
available today: **simplicity/minimality on the Clifford side** packaged next to
the **1-dimensional matrix slot** for `Δ` that `RapidityIdealPurposeBridge` already
aligns with the rapidity / zeta phase scaffold.
-/
structure CliffordHyperchargeSlotRefinement where
  cliffTopMinimal : IsMinimalLeftIdeal (⊤ : LeftIdeal CliffordOneDim)
  matrixHyperchargeLineFinrankOne :
    Module.finrank ℝ (ℝ ∙ Hqiv.phaseLiftDelta) = 1

/-- Canonical certificate combining `Cl(1)` minimality with the HQIV Δ-line. -/
def canonicalCliffordHyperchargeSlotRefinement : CliffordHyperchargeSlotRefinement where
  cliffTopMinimal := cliffordOneDim_top_isMinimalLeftIdeal
  matrixHyperchargeLineFinrankOne := hqiv_hypercharge_line_finrank_one

theorem canonicalCliffordHyperchargeSlotRefinement_matrix_finrank :
    canonicalCliffordHyperchargeSlotRefinement.matrixHyperchargeLineFinrankOne =
      hqiv_hypercharge_line_finrank_one :=
  rfl

end Hqiv.Algebra
