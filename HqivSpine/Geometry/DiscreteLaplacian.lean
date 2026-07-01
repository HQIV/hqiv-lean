import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# `HqivSpine.Geometry.DiscreteLaplacian` — axis-aligned discrete Laplacian on the observer chart

The discrete-analysis layer matching the spine's discrete-first philosophy. The spatial observer
chart `ObserverChart = Fin 3 → ℝ` carries the standard **7-point** central second-difference
stencil with step `h`:

`Δ_h f (x) = (1/h²) ∑ᵢ (f(x + h eᵢ) + f(x − h eᵢ) − 2 f(x))`.

Results (pure stencil algebra + trigonometry):

* additivity (`HQVM_rawSecondDiff_sum_add`) and central-difference symmetry `h ↦ −h`
  (`HQVM_discreteLaplacian_symm_h`);
* **domain rescaling** `x ↦ c•x` conjugates the stencil and the Laplacian picks up `c²`
  (`HQVM_discreteLaplacian_comp_smul`) — the discrete shadow of `Δ(f∘(c·)) = c²(Δf)∘(c·)`;
* the **Fourier symbol** on a separable cosine mode: `Δ_h` acts with eigen-coefficient
  `2(cos kh − 1)`, equivalently `−(4/h²) sin²(kh/2)` (`HQVM_discreteLaplacian_cosModeOnAxis`,
  `…_sin_sq`) — the standard discrete Helmholtz symbol, with continuum limit `−k²` as `h → 0`.

This is a finite-difference stencil on the continuum chart, **not** a graph Laplacian on a shell
graph nor the Laplace–Beltrami operator. Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new
`axiom`, no `native_decide`.
-/

namespace HqivSpine.Geometry

open Finset Real

/-- Spatial observer chart: `ℝ³` coordinates indexed by `Fin 3`. -/
abbrev ObserverChart := Fin 3 → ℝ

section AxisStencil

/-- Shift the observer chart by `h` along axis `i` (`ℝ³` standard basis via `Fin 3`). -/
def HQVM_axisShift (x : ObserverChart) (i : Fin 3) (h : ℝ) : ObserverChart :=
  x + Pi.single i h

theorem HQVM_axisShift_apply_same (x : ObserverChart) (i : Fin 3) (h : ℝ) :
    HQVM_axisShift x i h i = x i + h := by
  simp [HQVM_axisShift, Pi.add_apply, Pi.single_eq_same]

theorem HQVM_axisShift_apply_of_ne {x : ObserverChart} {i i₀ : Fin 3} (h : ℝ) (hne : i ≠ i₀) :
    HQVM_axisShift x i h i₀ = x i₀ := by
  simp [HQVM_axisShift, Pi.add_apply, Pi.single_eq_of_ne hne.symm]

/-- Raw central second difference of `f` at `x` along axis `i` (not divided by `h²`). -/
def HQVM_rawSecondDiffAlong (h : ℝ) (f : ObserverChart → ℝ) (x : ObserverChart) (i : Fin 3) : ℝ :=
  f (HQVM_axisShift x i h) + f (HQVM_axisShift x i (-h)) - 2 * f x

/-- Sum of axis-aligned central second differences (7-point Laplacian stencil without `1/h²`). -/
noncomputable def HQVM_rawSecondDiff_sum (h : ℝ) (f : ObserverChart → ℝ) (x : ObserverChart) : ℝ :=
  ∑ i : Fin 3, HQVM_rawSecondDiffAlong h f x i

/-- Discrete Laplacian `(1/h²) ∑ᵢ (f(x+h eᵢ)+f(x−h eᵢ)−2f(x))` on the observer chart. -/
noncomputable def HQVM_discreteLaplacian (h : ℝ) (f : ObserverChart → ℝ) (x : ObserverChart) : ℝ :=
  HQVM_rawSecondDiff_sum h f x / h ^ 2

end AxisStencil

section ElementaryAlgebra

theorem HQVM_rawSecondDiffAlong_add (h : ℝ) (f g : ObserverChart → ℝ) (x : ObserverChart)
    (i : Fin 3) :
    HQVM_rawSecondDiffAlong h (fun y => f y + g y) x i =
      HQVM_rawSecondDiffAlong h f x i + HQVM_rawSecondDiffAlong h g x i := by
  dsimp [HQVM_rawSecondDiffAlong]; ring

theorem HQVM_rawSecondDiff_sum_add (h : ℝ) (f g : ObserverChart → ℝ) (x : ObserverChart) :
    HQVM_rawSecondDiff_sum h (fun y => f y + g y) x =
      HQVM_rawSecondDiff_sum h f x + HQVM_rawSecondDiff_sum h g x := by
  simp [HQVM_rawSecondDiff_sum, Finset.sum_add_distrib, HQVM_rawSecondDiffAlong_add]

/-- Invariance under `h ↦ −h` (central-difference symmetry). -/
theorem HQVM_rawSecondDiffAlong_symm_h (h : ℝ) (f : ObserverChart → ℝ) (x : ObserverChart)
    (i : Fin 3) :
    HQVM_rawSecondDiffAlong (-h) f x i = HQVM_rawSecondDiffAlong h f x i := by
  dsimp [HQVM_rawSecondDiffAlong, HQVM_axisShift]; ring_nf

theorem HQVM_rawSecondDiff_sum_symm_h (h : ℝ) (f : ObserverChart → ℝ) (x : ObserverChart) :
    HQVM_rawSecondDiff_sum (-h) f x = HQVM_rawSecondDiff_sum h f x := by
  simp [HQVM_rawSecondDiff_sum, HQVM_rawSecondDiffAlong_symm_h]

theorem HQVM_discreteLaplacian_symm_h (h : ℝ) (f : ObserverChart → ℝ) (x : ObserverChart) :
    HQVM_discreteLaplacian (-h) f x = HQVM_discreteLaplacian h f x := by
  simp [HQVM_discreteLaplacian, HQVM_rawSecondDiff_sum_symm_h, sq]

private theorem smul_add_axisShift (c h : ℝ) (x : ObserverChart) (i : Fin 3) :
    c • (x + Pi.single i h) = c • x + Pi.single i (c * h) := by
  ext j
  simp only [Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul]
  split_ifs with hij <;> ring

/-- Domain rescaling `x ↦ c•x` conjugates the raw stencil: step `h` on the pulled-back field
matches step `c*h` on `f` at `c•x`. -/
theorem HQVM_rawSecondDiff_sum_comp_smul (c h : ℝ) (f : ObserverChart → ℝ) (x : ObserverChart) :
    HQVM_rawSecondDiff_sum h (fun y => f (c • y)) x =
      HQVM_rawSecondDiff_sum (c * h) f (c • x) := by
  dsimp [HQVM_rawSecondDiff_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  change
    f (c • (x + Pi.single i h)) + f (c • (x + Pi.single i (-h))) - 2 * f (c • x) =
      f (c • x + Pi.single i (c * h)) + f (c • x + Pi.single i (-(c * h))) - 2 * f (c • x)
  rw [smul_add_axisShift, smul_add_axisShift c (-h)]
  have hslice :
      c • x + Pi.single i (c * -h) = c • x + Pi.single i (-(c * h)) := by
    congr 1
    exact congrArg (Pi.single i) (by ring : c * -h = -(c * h))
  rw [hslice]

/-- Under `h ≠ 0` and `c*h ≠ 0`, the scaled discrete Laplacian picks up a factor `c²` (the
continuum scaling `Δ(f∘(c•)) = c²((Δf)∘(c•))` for the axis-aligned Laplacian). -/
theorem HQVM_discreteLaplacian_comp_smul (c h : ℝ) (f : ObserverChart → ℝ) (x : ObserverChart)
    (hh : h ≠ 0) (hch : c * h ≠ 0) :
    HQVM_discreteLaplacian h (fun y => f (c • y)) x =
      c ^ 2 * HQVM_discreteLaplacian (c * h) f (c • x) := by
  unfold HQVM_discreteLaplacian
  rw [HQVM_rawSecondDiff_sum_comp_smul]
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hch).1
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hch2 : (c * h) ^ 2 ≠ 0 := pow_ne_zero 2 hch
  rw [show (c * h) ^ 2 = c ^ 2 * h ^ 2 by ring]
  field_simp [hh2, hc2, hch2]

end ElementaryAlgebra

section CosModeToy

/-- Axis-aligned cosine mode `cos (k · x_{i₀})` (separable mode on the chart). -/
noncomputable def HQVM_cosModeOnAxis (i₀ : Fin 3) (k : ℝ) (x : ObserverChart) : ℝ :=
  cos (k * x i₀)

private theorem cos_shift_identity (k x₀ h : ℝ) :
    cos (k * (x₀ + h)) + cos (k * (x₀ - h)) - 2 * cos (k * x₀) =
      2 * cos (k * x₀) * (cos (k * h) - 1) := by
  have ha : k * (x₀ + h) = k * x₀ + k * h := by ring
  have hb : k * (x₀ - h) = k * x₀ - k * h := by ring
  rw [ha, hb, cos_add, cos_sub]; ring

private theorem HQVM_rawSecondDiffAlong_cosModeOnAxis_of_ne {i₀ i : Fin 3} (hne : i ≠ i₀)
    (k h : ℝ) (x : ObserverChart) :
    HQVM_rawSecondDiffAlong h (HQVM_cosModeOnAxis i₀ k) x i = 0 := by
  dsimp [HQVM_rawSecondDiffAlong]
  have hf1 : (HQVM_cosModeOnAxis i₀ k) (HQVM_axisShift x i h) = cos (k * x i₀) := by
    dsimp [HQVM_cosModeOnAxis, HQVM_axisShift]
    congr 1
    rw [Pi.single_eq_of_ne hne.symm]; ring
  have hf2 : (HQVM_cosModeOnAxis i₀ k) (HQVM_axisShift x i (-h)) = cos (k * x i₀) := by
    dsimp [HQVM_cosModeOnAxis, HQVM_axisShift]
    congr 1
    rw [Pi.single_eq_of_ne hne.symm]; ring
  simp_rw [hf1, hf2, HQVM_cosModeOnAxis]; ring

private theorem HQVM_rawSecondDiffAlong_cosModeOnAxis_same (i₀ : Fin 3) (k h : ℝ)
    (x : ObserverChart) :
    HQVM_rawSecondDiffAlong h (HQVM_cosModeOnAxis i₀ k) x i₀ =
      2 * cos (k * x i₀) * (cos (k * h) - 1) := by
  dsimp [HQVM_rawSecondDiffAlong]
  have hf1 : (HQVM_cosModeOnAxis i₀ k) (HQVM_axisShift x i₀ h) = cos (k * (x i₀ + h)) := by
    dsimp [HQVM_cosModeOnAxis, HQVM_axisShift]
    congr 1
    rw [Pi.single_eq_same]
  have hf2 : (HQVM_cosModeOnAxis i₀ k) (HQVM_axisShift x i₀ (-h)) = cos (k * (x i₀ - h)) := by
    dsimp [HQVM_cosModeOnAxis, HQVM_axisShift]
    congr 1
    rw [Pi.single_eq_same]; ring
  rw [hf1, hf2]
  simp only [HQVM_cosModeOnAxis]
  exact cos_shift_identity k (x i₀) h

/-- For a cosine mode along `i₀`, only the `i₀` axis contributes; the stencil acts with the
trigonometric eigen-coefficient `2(cos(kh)−1)` (continuum limit `−k² h²` as `h → 0`). -/
theorem HQVM_rawSecondDiff_sum_cosModeOnAxis (i₀ : Fin 3) (k h : ℝ) (x : ObserverChart) :
    HQVM_rawSecondDiff_sum h (HQVM_cosModeOnAxis i₀ k) x =
      2 * cos (k * x i₀) * (cos (k * h) - 1) := by
  dsimp [HQVM_rawSecondDiff_sum]
  rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)]
  · exact HQVM_rawSecondDiffAlong_cosModeOnAxis_same i₀ k h x
  · intro b _ hb
    exact HQVM_rawSecondDiffAlong_cosModeOnAxis_of_ne hb k h x

theorem HQVM_discreteLaplacian_cosModeOnAxis (i₀ : Fin 3) (k h : ℝ) (x : ObserverChart)
    (_hh : h ≠ 0) :
    HQVM_discreteLaplacian h (HQVM_cosModeOnAxis i₀ k) x =
      2 * cos (k * x i₀) * (cos (k * h) - 1) / h ^ 2 := by
  simp [HQVM_discreteLaplacian, HQVM_rawSecondDiff_sum_cosModeOnAxis]

/-- Equivalent form `−(4/h²) sin²(kh/2)` (the standard discrete Helmholtz symbol). -/
theorem HQVM_discreteLaplacian_cosModeOnAxis_sin_sq (i₀ : Fin 3) (k h : ℝ) (x : ObserverChart)
    (hh : h ≠ 0) :
    HQVM_discreteLaplacian h (HQVM_cosModeOnAxis i₀ k) x =
      -(4 * cos (k * x i₀) * sin (k * h / 2) ^ 2 / h ^ 2) := by
  rw [HQVM_discreteLaplacian_cosModeOnAxis _ _ _ _ hh]
  have hcos : cos (k * h) - 1 = -2 * sin (k * h / 2) ^ 2 := by
    have hk : k * h = 2 * (k * h / 2) := by field_simp
    rw [hk, cos_two_mul]
    have hsq := sin_sq_add_cos_sq (k * h / 2)
    have hcos2 : cos (k * h / 2) ^ 2 = 1 - sin (k * h / 2) ^ 2 := by linarith [hsq]
    rw [hcos2]; ring_nf
  rw [hcos]; ring

end CosModeToy

end HqivSpine.Geometry
