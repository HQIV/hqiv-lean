import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FinCases
import Hqiv.Story.GaugeGroupFromHQIVSketch
import Hqiv.Story.PatchHilbertBridge

/-!
# Millennium bridge — concrete `G`, patch Hilbert slot, and vacuum vector

This is the first **constructed** layer toward a full `QuantumYangMillsTheory G`: we fix the gauge
carrier `G = Perm (Fin 3)` (already a `CompactSimpleGaugeGroup` in
`GaugeGroupFromHQIVSketch`), take the HQIV patch Hilbert space `LatticeHilbert 4`, equip it with the
identity `HilbertPatchBridge`, and choose an explicit **normalized** vector to serve as the patch
vacuum: the equimodular superposition `(1/2) ∑_{i=0}^3 e_i` in `ℂ⁴` (so every chart coordinate is
nonzero). This matches the eight real first-order modes of `𝓢(ℝ⁴, ℂ)` smearing on the patch.

Downstream: when `qft.hilbertSpace` is instantiated as `LatticeHilbert 4`, the Dojo Wightman vacuum
`wightman.vacuum` should be identified with (or transported to) `patchVacuum` via the same Hilbert
identification used in `HilbertPatchBridge.incl`.
-/

namespace Hqiv.Story

open scoped InnerProductSpace
open Finset
open Hqiv.QM
open EuclideanSpace

/-- Concrete compact gauge group \(S_3 \cong \mathrm{Perm}(\mathrm{Fin}\,3)\) (same as
`HQIVStoryGaugeSketch` / `MillenniumBridgeGauge`). -/
abbrev MillenniumG : Type :=
  HQIVStoryGaugeSketch

/-- Patch Hilbert carrier for the `Fin 4` chart / Cauchy patch (`ℂ⁴` with standard `L²` inner product). -/
abbrev PatchHilbert : Type :=
  LatticeHilbert 4

/-- Identity Hilbert patch bridge on the patch carrier itself (`incl = id`). -/
noncomputable def patchHilbertPatchBridge : HilbertPatchBridge PatchHilbert :=
  HilbertPatchBridge.latticeIdentityBridge

/-- Normalized equimodular vacuum on `ℂ⁴`: `(1/2) ∑_i e_i` has `ℓ²` norm `1`. -/
noncomputable def patchVacuum : PatchHilbert :=
  (2 : ℂ)⁻¹ • Finset.sum Finset.univ fun i : Fin 4 => EuclideanSpace.single i (1 : ℂ)

@[simp]
theorem patchVacuum_apply (i : Fin 4) : patchVacuum i = (2 : ℂ)⁻¹ := by
  classical
  simp_rw [patchVacuum, PiLp.smul_apply, smul_eq_mul]
  rw [← Finset.sum_apply]
  fin_cases i <;> (
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, EuclideanSpace.single_apply,
      mul_one, add_zero])

theorem patchVacuum_norm : ‖patchVacuum‖ = 1 := by
  classical
  let u : PatchHilbert := Finset.sum Finset.univ fun i : Fin 4 => EuclideanSpace.single i (1 : ℂ)
  have hu_coord (j : Fin 4) : u j = 1 := by
    rw [show u = Finset.sum Finset.univ fun i : Fin 4 => EuclideanSpace.single i (1 : ℂ) from rfl]
    rw [← Finset.sum_apply]
    fin_cases j <;> simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
      EuclideanSpace.single_apply, mul_one, add_zero]
  have hu2 : ‖u‖ ^ 2 = 4 := by
    rw [EuclideanSpace.norm_sq_eq (𝕜 := ℂ) (n := Fin 4) u]
    simp_rw [hu_coord, norm_one, one_pow, sum_const, card_univ, Fintype.card_fin]
    simp
  have hu : ‖u‖ = 2 := by
    have h0 : 0 ≤ ‖u‖ := norm_nonneg _
    rw [← sq_eq_sq₀ h0 (by norm_num : (0 : ℝ) ≤ (2 : ℝ)), hu2]
    norm_num
  rw [patchVacuum, norm_smul, hu, norm_inv]
  have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2c, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)]

theorem patchVacuum_ne_zero : patchVacuum ≠ 0 := by
  intro h
  have := congr_arg (fun v : PatchHilbert => v 0) h
  simp only [patchVacuum_apply, PiLp.zero_apply] at this
  norm_num at this

theorem patchVacuum_inner_self : inner ℂ patchVacuum patchVacuum = 1 := by
  rw [inner_self_eq_norm_sq_to_K]
  simp only [patchVacuum_norm, sq]
  norm_cast

end Hqiv.Story
