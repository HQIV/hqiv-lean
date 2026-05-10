import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

import Hqiv.Archive.Algebra.MoireCuspBracket
import Hqiv.Geometry.SpatialSliceRapidityScaffold

/-!
# Rapidity / arc parameter ↔ discrete patch index (bridge scaffold)

This module **names** the bridges discussed for moiré search, Fourier patch concentration, and
continuum geometry — without claiming a full equivalence with DFT character orthogonality.

## Three bridges (design targets)

1. **Sampling / monotone parameter** — Patch indices `j : Fin n` sit on an increasing list of real
   parameters `s j` along a 1D curve (arc-length or rapidity-related). Then edge increments
   `s (j+1) − s j` are nonnegative and play the role of discrete “Δ arc”.

2. **Rapidity polar angle** — `polarAngleFromRapidity φ t m` from `SpatialSliceRapidityScaffold` is one
   concrete choice of scalar along shells. Relating **patch index** `j` to **shell index** `m` uses an
   explicit `idx : Fin n → ℕ` (or richer chart data). Monotonicity of `s j = polarAngleFromRapidity φ t (idx j)`
   holds when `idx` is monotone (`IdxMonotone`) and `0 ≤ φ * t` (since `δθ'(m)` is monotone in the cast
   shell coordinate `m : ℝ`); see `MonotonePatchParameter_of_polarAngle_mul_nonneg`.

3. **DFT / character orthogonality** — The Fourier patch in `OctonionSphereFourierPatch` uses a
   length-`n` harmonic kernel `exp(2π i k j/n)`. Cancellation from
   `sum_exp_two_pi_int_mul_fin_eq_zero_sub` applies to **that** character sum; aligning the **arity**
   phasor `exp(i·π/(2k')·j)` with the same frequency is **extra calibration** (documented there).

**Proved here:** monotonicity of `s` ⇒ nonnegative parameter increments along interior edges; pullback
of a real score through `s`; compatibility of `IdxMonotone` with `MonotonePatchParameter` when
`polarAngleFromRapidity` is monotone in `m` for `0 ≤ φ * t`, or via `MonotonePatchParameter_of_monotone_polarAngle`
with a supplied `Monotone` proof otherwise; **Lipschitz pullback bounds** relating `|Δ(f∘s)|` to `|Δs|` and
`moireCumulativeAbsVariation` to `K * (s(j) - s(0))`, including the **`sin` pullback** (`Real.lipschitzWith_sin`).

**Not here:** smooth limits (mesh → 0), `deriv` along embedded curves in `S²`, or orthogonality of the
full weighted patch sum — those need separate hypotheses or future files.
-/

noncomputable section

open scoped BigOperators NNReal
open Finset

namespace Hqiv.Geometry

variable {n : ℕ}

/-- Real parameters `s j` for patch indices, monotone in `Fin n` (arc / rapidity proxy along the patch). -/
structure MonotonePatchParameter (n : ℕ) where
  /-- Parameter value at patch vertex `j`. -/
  s : Fin n → ℝ
  /-- Monotone along the canonical order on `Fin n`. -/
  mono : Monotone s

/-- Edge increment of a patch parameter between consecutive indices (`j` indexes an *edge* in `Fin (n-1)`). -/
noncomputable def patchParamEdgeDelta {n : ℕ} (hn : 1 < n) (s : Fin n → ℝ) (j : Fin (n - 1)) : ℝ :=
  s ⟨j.val + 1, by
      have hj := j.is_lt
      omega⟩ -
    s ⟨j.val, by
      have hj := j.is_lt
      omega⟩

theorem patchParamEdgeDelta_nonneg {n : ℕ} (hn : 1 < n) (P : MonotonePatchParameter n) (j : Fin (n - 1)) :
    0 ≤ patchParamEdgeDelta hn P.s j := by
  have hj_lt : j.val < n - 1 := j.is_lt
  have hj1 : j.val + 1 < n := by omega
  have hj0 : j.val < n := by omega
  let i0 : Fin n := ⟨j.val, hj0⟩
  let i1 : Fin n := ⟨j.val + 1, hj1⟩
  have hi : i0 ≤ i1 := by
    rw [Fin.le_iff_val_le_val]
    exact Nat.le_succ _
  have := P.mono hi
  dsimp [patchParamEdgeDelta]
  linarith

/-- Pull back a continuum score `f : ℝ → ℝ` along patch parameters (discrete score on `Fin n`). -/
noncomputable def scoreFromPullback (s : Fin n → ℝ) (f : ℝ → ℝ) : Hqiv.Algebra.MoirePatchScore n :=
  fun j => f (s j)

/-- Shell indices along the patch; monotonicity of `idx` along `Fin n` is still an explicit hypothesis. -/
structure IdxMonotone (n : ℕ) (idx : Fin n → ℕ) : Prop where
  mono : ∀ i j : Fin n, i.val ≤ j.val → idx i ≤ idx j

/-- Patch parameters given by `polarAngleFromRapidity` at shell indices `idx j`. -/
noncomputable def patchParamFromPolarAngles (φ t : ℝ) (idx : Fin n → ℕ) : Fin n → ℝ := fun j =>
  polarAngleFromRapidity φ t (idx j)

/--
If `polarAngleFromRapidity φ t` is monotone in the shell index and `idx` is monotone on `Fin n`, then
`s j := polarAngleFromRapidity φ t (idx j)` is monotone on the patch — hence `MonotonePatchParameter`.
-/
def MonotonePatchParameter_of_monotone_polarAngle {φ t : ℝ} {idx : Fin n → ℕ}
    (hθ : Monotone fun m : ℕ => polarAngleFromRapidity φ t m) (hidx : IdxMonotone n idx) :
    MonotonePatchParameter n :=
  ⟨patchParamFromPolarAngles φ t idx, fun i j hij => hθ (hidx.mono i j (Fin.le_iff_val_le_val.mp hij))⟩

/--
Convenient instance: `polarAngleFromRapidity` is monotone in `m` when `0 ≤ φ * t`
(`SpatialSliceRapidityScaffold.polarAngleFromRapidity_monotone_of_mul_nonneg`), so only `IdxMonotone`
is needed for a `MonotonePatchParameter` from polar angles.
-/
noncomputable def MonotonePatchParameter_of_polarAngle_mul_nonneg {φ t : ℝ} {idx : Fin n → ℕ}
    (hφt : 0 ≤ φ * t) (hidx : IdxMonotone n idx) : MonotonePatchParameter n :=
  MonotonePatchParameter_of_monotone_polarAngle (polarAngleFromRapidity_monotone_of_mul_nonneg φ t hφt) hidx

/-!
### Lipschitz pullback: discrete edges controlled by `|Δs|`, cumulative variation by `K * (s(j) − s(0))`
-/

/-- One edge of a Lipschitz pullback: `|Δ(f∘s)| ≤ K * Δs` when `s` is monotone along the edge. -/
theorem abs_sub_scoreFromPullback_edge_le {n : ℕ} (P : MonotonePatchParameter n) (f : ℝ → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) {i : ℕ} (hi : i + 1 < n) :
    |f (P.s ⟨i + 1, hi⟩) - f (P.s ⟨i, Nat.lt_of_succ_lt hi⟩)| ≤
      (K : ℝ) * (P.s ⟨i + 1, hi⟩ - P.s ⟨i, Nat.lt_of_succ_lt hi⟩) := by
  have hmono : P.s ⟨i, Nat.lt_of_succ_lt hi⟩ ≤ P.s ⟨i + 1, hi⟩ := by
    refine P.mono ?_
    rw [Fin.le_iff_val_le_val]
    exact Nat.le_succ i
  have habs := hf.dist_le_mul (P.s ⟨i + 1, hi⟩) (P.s ⟨i, Nat.lt_of_succ_lt hi⟩)
  rw [Real.dist_eq, Real.dist_eq] at habs
  have hΔ : |P.s ⟨i + 1, hi⟩ - P.s ⟨i, Nat.lt_of_succ_lt hi⟩| =
      P.s ⟨i + 1, hi⟩ - P.s ⟨i, Nat.lt_of_succ_lt hi⟩ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
  rw [hΔ] at habs
  simpa using habs

/--
Telescoping: `∑_{i < j.val} (s(i+1) − s(i)) = s(j) − s(0)` for `s : Fin n → ℝ`.

Uses `Finset.sum_range_sub` after embedding `k ↦ s⟨k, _⟩` as a map `ℕ → ℝ` (irrelevant outside `k < n`).
-/
theorem sum_range_succ_diff_eq_sub {n : ℕ} (hn : 0 < n) (s : Fin n → ℝ) (j : Fin n) :
    (∑ i ∈ Finset.range j.val,
        (if hi : i < j.val then
          s ⟨i + 1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hi) j.is_lt⟩ -
            s ⟨i, Nat.lt_trans hi j.is_lt⟩
        else 0)) = s j - s ⟨0, hn⟩ := by
  classical
  let f : ℕ → ℝ := fun k => if hk : k < n then s ⟨k, hk⟩ else 0
  have hf_eq :
      ∀ i ∈ Finset.range j.val,
        (if hi : i < j.val then
            s ⟨i + 1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hi) j.is_lt⟩ -
              s ⟨i, Nat.lt_trans hi j.is_lt⟩
          else 0) =
          f (i + 1) - f i := by
    intro i hi
    have hi' : i < j.val := Finset.mem_range.mp hi
    simp only [hi', dite_true]
    have hi1 : i + 1 < n := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hi') j.is_lt
    have hi0 : i < n := Nat.lt_trans hi' j.is_lt
    dsimp [f]
    simp only [dif_pos hi1, dif_pos hi0]
  calc
    (∑ i ∈ Finset.range j.val,
        (if hi : i < j.val then
            s ⟨i + 1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hi) j.is_lt⟩ -
              s ⟨i, Nat.lt_trans hi j.is_lt⟩
          else 0))
        = ∑ i ∈ Finset.range j.val, (f (i + 1) - f i) := Finset.sum_congr rfl hf_eq
    _ = f j.val - f 0 := Finset.sum_range_sub f j.val
    _ = s j - s ⟨0, hn⟩ := by
      have hfj : f j.val = s j := by
        simp [f, dif_pos j.is_lt, Fin.eta]
      have hf0 : f 0 = s ⟨0, hn⟩ := by
        simp [f, dif_pos hn]
      rw [hfj, hf0]

theorem moireCumulativeAbsVariation_le_K_mul_sub_endpoints {n : ℕ} (hn : 0 < n) (P : MonotonePatchParameter n)
    (f : ℝ → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) (j : Fin n) :
    Hqiv.Algebra.moireCumulativeAbsVariation (scoreFromPullback P.s f) j ≤ (K : ℝ) * (P.s j - P.s ⟨0, hn⟩) := by
  classical
  dsimp [Hqiv.Algebra.moireCumulativeAbsVariation]
  -- Explicit RHS summand so `Finset.sum_le_sum` does not depend on an unknown `g` (avoids a metavariable cycle).
  let g : ℕ → ℝ := fun i =>
    if hi : i < j.val then
      (K : ℝ) * (P.s ⟨i + 1, Hqiv.Algebra.succ_lt_n_of_lt hi⟩ - P.s ⟨i, Hqiv.Algebra.lt_n_of_lt hi⟩)
    else 0
  have hpt :
      ∀ i ∈ Finset.range j.val,
        (if hi : i < j.val then
            |f (P.s ⟨i + 1, Hqiv.Algebra.succ_lt_n_of_lt hi⟩) - f (P.s ⟨i, Hqiv.Algebra.lt_n_of_lt hi⟩)|
          else 0) ≤ g i := by
    intro i hi_mem
    have hi' : i < j.val := Finset.mem_range.mp hi_mem
    simp only [hi', dite_true]
    dsimp [g]
    simp only [hi', dite_true]
    have hi1 : i + 1 < n := Hqiv.Algebra.succ_lt_n_of_lt hi'
    have eσ : (⟨i + 1, Hqiv.Algebra.succ_lt_n_of_lt hi'⟩ : Fin n) = ⟨i + 1, hi1⟩ := Fin.ext rfl
    have eι : (⟨i, Hqiv.Algebra.lt_n_of_lt hi'⟩ : Fin n) = ⟨i, Nat.lt_of_succ_lt hi1⟩ := Fin.ext rfl
    simp_rw [eσ, eι]
    exact abs_sub_scoreFromPullback_edge_le P f hf hi1
  have hinner :
      (∑ i ∈ Finset.range j.val,
          if hi : i < j.val then
            P.s ⟨i + 1, Hqiv.Algebra.succ_lt_n_of_lt hi⟩ - P.s ⟨i, Hqiv.Algebra.lt_n_of_lt hi⟩
          else 0) =
        P.s j - P.s ⟨0, hn⟩ := by
    refine Eq.trans ?_ (sum_range_succ_diff_eq_sub hn P.s j)
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < j.val := Finset.mem_range.mp hi
    simp only [hi', dite_true]
  have hKsum : (∑ i ∈ Finset.range j.val, g i) = (K : ℝ) * (P.s j - P.s ⟨0, hn⟩) := by
    have hsumEq :
        ∑ i ∈ Finset.range j.val, g i =
          ∑ i ∈ Finset.range j.val,
            (K : ℝ) *
              (if hi : i < j.val then
                P.s ⟨i + 1, Hqiv.Algebra.succ_lt_n_of_lt hi⟩ - P.s ⟨i, Hqiv.Algebra.lt_n_of_lt hi⟩
              else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi' : i < j.val := Finset.mem_range.mp hi
      dsimp [g]
      simp only [hi', dite_true]
    rw [hsumEq, ← Finset.mul_sum, hinner]
  exact le_trans (Finset.sum_le_sum hpt) (by rw [hKsum])

/-- Same bound with **`K = 1`** and `f = Real.sin` (Mathlib: `Real.lipschitzWith_sin`). Matches the
numeric pullback in `scripts/hqiv_geometric_3sat_demo.py` (`lean_pullback_sin_scores`). -/
theorem moireCumulativeAbsVariation_le_sub_endpoints_sin {n : ℕ} (hn : 0 < n) (P : MonotonePatchParameter n)
    (j : Fin n) :
    Hqiv.Algebra.moireCumulativeAbsVariation (scoreFromPullback P.s Real.sin) j ≤ P.s j - P.s ⟨0, hn⟩ := by
  simpa [one_mul] using
    moireCumulativeAbsVariation_le_K_mul_sub_endpoints (f := Real.sin) hn P Real.lipschitzWith_sin j

/-!
### Moiré cumulative variation (re-export narrative)

`Hqiv.Algebra.moireCumulativeAbsVariation` is **intrinsically** monotone in the patch endpoint for any
`MoirePatchScore`. With `MonotonePatchParameter` and Lipschitz `f`, see
`moireCumulativeAbsVariation_le_K_mul_sub_endpoints`.
-/

theorem moireCumulativeAbsVariation_mono_remark (S : Hqiv.Algebra.MoirePatchScore n) {j k : Fin n}
    (hjk : j.val ≤ k.val) :
    Hqiv.Algebra.moireCumulativeAbsVariation S j ≤ Hqiv.Algebra.moireCumulativeAbsVariation S k :=
  Hqiv.Algebra.moireCumulativeAbsVariation_mono S hjk

/-!
### Abstract manifold carrier (scalar field)

`ManifoldLagrangianScaffold.LagrangianDensity M` is definitionally `M → ℝ`; a continuum score on `M`
pulls back along any map `Fin n → M` by composition — recorded here only as narrative alignment with
`AuxiliaryScalarField M` in `SpatialSliceRapidityScaffold`.
-/

end Hqiv.Geometry

end
