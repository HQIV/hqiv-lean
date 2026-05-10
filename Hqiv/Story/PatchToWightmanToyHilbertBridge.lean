import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.RCLike.Basic
import Hqiv.Story.MillenniumBridgePatchVacuum
import Hqiv.Story.MillenniumBridgePoincareWightman
import Hqiv.Story.PatchHilbertBridge

/-!
# Patch Hilbert ↔ 1D Wightman toy carrier

`PatchHilbert = LatticeHilbert 4` is eight-dimensional over `ℝ`, while the certified Dojo spine
`poincareToyQuantumYangMills` uses `WightmanToyHilbert = EuclideanSpace ℝ (Fin 1)`. There is no
unitary identification between these spaces; this file fixes a **bounded ℝ-linear comparison map**
in the sense of `HilbertPatchBridge`.

**Definition:** send `ψ` to `(2 * (ψ 0).re) • wightmanToyVacuum`. The scalar `2` matches the
equimodular patch vacuum `patchVacuum` from `MillenniumBridgePatchVacuum`, which has every chart
coordinate `(2 : ℂ)⁻¹` (`patchVacuum_apply`), so the bridge carries `patchVacuum` to
`wightmanToyVacuum`.

Downstream alignment of **operators** still uses `HilbertPatchBridge.patchOpAsLinearOperator`: a
ℂ-linear patch endomorphism becomes a rank-one (or small-rank) operator on the toy line, not the
full patch jet on `PatchHilbert`.
-/

namespace Hqiv.Story

open scoped InnerProductSpace
open ContinuousLinearMap EuclideanSpace

noncomputable section

/-- First chart coordinate, real part, as a bounded `ℝ`-linear functional on `PatchHilbert`. -/
noncomputable def patchCoord0Re : PatchHilbert →L[ℝ] ℝ where
  toFun ψ := (ψ 0).re
  cont :=
    Complex.continuous_re.comp
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 4 => ℂ) (0 : Fin 4))
  map_add' ψ φ := by simp [PiLp.add_apply, Complex.add_re]
  map_smul' r ψ := by
    simp only [RingHom.id_apply, PiLp.smul_apply, Complex.smul_re, smul_eq_mul]

/-- Post-multiply by `2` on `ℝ`. -/
noncomputable def realPostMul2 : ℝ →L[ℝ] ℝ where
  toFun x := 2 * x
  cont := continuous_const.mul continuous_id
  map_add' x y := by simp [mul_add]
  map_smul' m x := by
    simp only [RingHom.id_apply, smul_eq_mul, mul_assoc, mul_comm]

/-- `ψ ↦ 2 * (ψ 0).re`, so `patchVacuum` maps to `1 : ℝ` along the toy axis. -/
noncomputable def patchToWightmanToyScaledRePart : PatchHilbert →L[ℝ] ℝ :=
  realPostMul2.comp patchCoord0Re

@[simp]
theorem patchCoord0Re_apply (ψ : PatchHilbert) : patchCoord0Re ψ = (ψ 0).re :=
  rfl

@[simp]
theorem patchToWightmanToyScaledRePart_apply (ψ : PatchHilbert) :
    patchToWightmanToyScaledRePart ψ = 2 * (ψ 0).re := by
  simp [patchToWightmanToyScaledRePart, realPostMul2]

/-- Bounded `ℝ`-linear map `PatchHilbert → WightmanToyHilbert` (rank one, along `wightmanToyVacuum`). -/
noncomputable def patchToWightmanToyHilbertIncl : PatchHilbert →L[ℝ] WightmanToyHilbert :=
  (LinearIsometry.toSpanSingleton (𝕜 := ℝ) (E := WightmanToyHilbert) wightmanToyVacuum_norm).toContinuousLinearMap.comp
    patchToWightmanToyScaledRePart

@[simp]
theorem patchToWightmanToyHilbertIncl_apply (ψ : PatchHilbert) (i : Fin 1) :
    patchToWightmanToyHilbertIncl ψ i = (2 * (ψ 0).re) * wightmanToyVacuum i := by
  simp [patchToWightmanToyHilbertIncl, LinearIsometry.toSpanSingleton_apply]

@[simp]
theorem patchToWightmanToyHilbertIncl_apply_zero (ψ : PatchHilbert) :
    patchToWightmanToyHilbertIncl ψ 0 = 2 * (ψ 0).re := by
  simp [wightmanToyVacuum, EuclideanSpace.single_apply, mul_one]

/-- Concrete `HilbertPatchBridge` into the Poincaré toy carrier used by `poincareToyQuantumYangMills`. -/
noncomputable def patchToWightmanToyHilbertBridge : HilbertPatchBridge WightmanToyHilbert where
  incl := patchToWightmanToyHilbertIncl

theorem patchVacuum_first_coord_re : (patchVacuum (0 : Fin 4)).re = (1 / 2 : ℝ) := by
  rw [patchVacuum_apply]
  norm_num

@[simp]
theorem patchToWightmanToyHilbertIncl_patchVacuum :
    patchToWightmanToyHilbertIncl patchVacuum = wightmanToyVacuum := by
  ext i
  fin_cases i
  simp [patchToWightmanToyHilbertIncl_apply, patchVacuum_apply, wightmanToyVacuum,
    EuclideanSpace.single_apply]

@[simp]
theorem patchToWightmanToyHilbertBridge_incl :
    patchToWightmanToyHilbertBridge.incl = patchToWightmanToyHilbertIncl :=
  rfl

end

end Hqiv.Story
