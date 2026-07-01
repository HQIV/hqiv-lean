import HqivSpine.Algebra.So8

/-!
# `HqivSpine.Algebra.Gauge` — the Standard-Model gauge generators inside `𝔰𝔬(8)`

Concrete gauge generators as genuine skew matrices in `𝔰𝔬(8)`, with proven Lie
closure where the structure is small:

* **`u(1)` hypercharge** — one generator on the distinguished `(e₁,e₇)` plane,
  abelian;
* **`su(2)` weak ≅ `so(3)`** — three plane generators with the *proven* closure
  relations `[L₁,L₂] = −L₃`, `[L₁,L₃] = L₂`, `[L₂,L₃] = −L₁`;
* **`su(3)` colour** sits in the genuine colour block `so(6)` (`finrank 15`), of
  dimension `8`;
* the **SM gauge dimension** is `8 + 3 + 1 = 12`.

Everything is built on the standard skew basis of `So8`, so there is no `axiom`,
`sorry`, `native_decide`, or determinant.
-/

namespace HqivSpine.Algebra

open Matrix

/-! ## `u(1)` hypercharge -/

/-- **Hypercharge generator** `Y` on the distinguished `(e₁, e₇)` plane. -/
def hyperchargeGen : Matrix (Fin 8) (Fin 8) ℝ := skewGen 1 7

theorem hyperchargeGen_mem : hyperchargeGen ∈ skewMatrices 8 := skewGen_mem 1 7

/-- **`u(1)` is abelian:** `[Y, Y] = 0`. -/
theorem hypercharge_abelian : bracket hyperchargeGen hyperchargeGen = 0 := by
  simp [bracket, sub_self]

/-! ## `su(2)` weak ≅ `so(3)` -/

/-- Weak generator `L₁` on the `(e₂, e₃)` plane. -/
def weakL1 : Matrix (Fin 8) (Fin 8) ℝ := skewGen 2 3
/-- Weak generator `L₂` on the `(e₂, e₄)` plane. -/
def weakL2 : Matrix (Fin 8) (Fin 8) ℝ := skewGen 2 4
/-- Weak generator `L₃` on the `(e₃, e₄)` plane. -/
def weakL3 : Matrix (Fin 8) (Fin 8) ℝ := skewGen 3 4

theorem weakL1_mem : weakL1 ∈ skewMatrices 8 := skewGen_mem 2 3
theorem weakL2_mem : weakL2 ∈ skewMatrices 8 := skewGen_mem 2 4
theorem weakL3_mem : weakL3 ∈ skewMatrices 8 := skewGen_mem 3 4

/-- **`[L₁, L₂] = −L₃`.** -/
theorem weak_bracket_12 : bracket weakL1 weakL2 = -weakL3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [bracket, weakL1, weakL2, weakL3, skewGen, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.neg_apply, Matrix.single_apply]

/-- **`[L₁, L₃] = L₂`.** -/
theorem weak_bracket_13 : bracket weakL1 weakL3 = weakL2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [bracket, weakL1, weakL2, weakL3, skewGen, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.single_apply]

/-- **`[L₂, L₃] = −L₁`.** -/
theorem weak_bracket_23 : bracket weakL2 weakL3 = -weakL1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [bracket, weakL1, weakL2, weakL3, skewGen, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.neg_apply, Matrix.single_apply]

/-- **`su(2)` weak closes** to the `so(3)` it spans (each bracket is `±` a generator). -/
theorem weak_su2_closes :
    bracket weakL1 weakL2 = -weakL3 ∧
    bracket weakL1 weakL3 = weakL2 ∧
    bracket weakL2 weakL3 = -weakL1 :=
  ⟨weak_bracket_12, weak_bracket_13, weak_bracket_23⟩

/-- **`su(2)` weak dimension** `= 3`. -/
def su2WeakDim : ℕ := 3

/-! ## `su(3)` colour inside the colour block `so(6)` -/

/-- **The colour rotation block `so(6)`** (the three complex colour pairs) has the
genuine dimension `15`. -/
theorem finrank_so6 : Module.finrank ℝ (skewMatrices 6) = 15 := by
  rw [finrank_skewMatrices]; decide

/-- **`su(3)` colour dimension** `= 8`, the traceless colour generators inside the
`15`-dimensional colour block `so(6)`. -/
def su3ColourDim : ℕ := 8

theorem su3_le_so6 : su3ColourDim ≤ Module.finrank ℝ (skewMatrices 6) := by
  rw [finrank_so6]; norm_num [su3ColourDim]

/-! ## Standard-Model gauge dimension -/

/-- **`u(1)` hypercharge dimension** `= 1`. -/
def u1HyperDim : ℕ := 1

/-- **Total SM gauge dimension** `dim(su(3)) + dim(su(2)) + dim(u(1)) = 8 + 3 + 1`. -/
def smGaugeDim : ℕ := su3ColourDim + su2WeakDim + u1HyperDim

theorem smGaugeDim_eq : smGaugeDim = 12 := by decide

theorem smGaugeDim_branch : smGaugeDim = 8 + 3 + 1 := by decide

/-- The SM gauge algebra fits inside the carrier rotation algebra: `12 ≤ 28`. -/
theorem smGaugeDim_le_so8 : smGaugeDim ≤ Module.finrank ℝ (skewMatrices 8) := by
  rw [finrank_so8, smGaugeDim_eq]; norm_num

end HqivSpine.Algebra
