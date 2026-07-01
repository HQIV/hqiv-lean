import HqivSpine.Physics.CPHolonomyPhase
import HqivSpine.Physics.CabibboInterference
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Matrix.Basic

/-!
# `HqivSpine.Physics.CKMMixingMatrix` — the full `3×3` unitary CKM matrix

All the pieces are now on the spine to assemble the complete mixing matrix:

* the **real plane rotations** `R₁₂, R₂₃` whose angles are the mass-ratio (Gatto–Sartori–Tonin)
  angles of `MixingAngles` / `CabibboInterference`, and
* the **complex `(1,3)` rotation** `R₁₃(δ)` carrying the fibre-holonomy phase `e^{±iδ}` of
  `CPHolonomyPhase`.

Assembling them in the standard order gives the CKM matrix `V = R₂₃ · R₁₃(δ) · R₁₂`. The key results:

* **Each factor is unitary** (`rot12_unitary`, `rot23_unitary`, `rot13_unitary`) — proved entrywise
  from `cos²+sin² = 1` and the phase identity `e^{iδ}e^{−iδ} = 1`.
* **The product is unitary** (`ckm_unitary`): `Vᴴ V = 1` (`ckm_unitary_apply`), so it is a genuine
  member of `U(3)` — the unitarity certificate the open programme asked for.
* **The Jarlskog invariant is the closed form** `J = c₁₂c₁₃²c₂₃s₁₂s₁₃s₂₃·sin δ` (`ckm_jarlskog`),
  computed from the four CKM entries via `CPHolonomyPhase.jarlskog`.
* **Built from the spine** (`ckmSpine`, `ckmSpine_unitary`): plugging the `CabibboInterference`
  mass-ratio angles into the three planes gives a unitary matrix whose CP violation
  (`ckmSpine_cp_violation`) is non-zero **iff** the holonomy phase is genuine — no PDG matrix fit.

**Honest scope.** The three mixing angles and the CP phase are *inputs* taken from the already-derived
spine pieces (mass ratios + holonomy); this module proves they assemble into a bona-fide unitary
matrix with the standard Jarlskog measure. It does not re-derive the angle *values* here (that is
`MixingAngles`) nor fix `δ`'s value (still open: graph-theoretic Fano overlap weights).

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.CKMMixingMatrix

open Complex ComplexConjugate
open HqivSpine.Physics.CPHolonomyPhase
open scoped Matrix

/-! ## The three plane rotations -/

/-- Real `(1,2)` rotation embedded in `3×3`. -/
noncomputable def rot12 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(c:ℂ), (s:ℂ), 0; (-(s:ℂ)), (c:ℂ), 0; 0, 0, 1]

/-- Real `(2,3)` rotation embedded in `3×3`. -/
noncomputable def rot23 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, (c:ℂ), (s:ℂ); 0, (-(s:ℂ)), (c:ℂ)]

/-- Complex `(1,3)` rotation carrying the CP/holonomy phase `e^{±iδ}`. -/
noncomputable def rot13 (c s δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(c:ℂ), 0, (s:ℂ) * link (-δ); 0, 1, 0; (-(s:ℂ)) * link δ, 0, (c:ℂ)]

/-- Phase-square cancellation, used in the `(1,3)` unitarity. -/
private theorem link_neg_mul (δ : ℝ) : link (-δ) * link δ = 1 := by
  rw [link_mul, neg_add_cancel, link_zero]

theorem rot12_unitary (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    rot12 c s ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := by
  have hC : (c : ℂ) * c + (s : ℂ) * s = 1 := by
    rw [show (1 : ℂ) = ((c ^ 2 + s ^ 2 : ℝ) : ℂ) by rw [h]; simp]; push_cast; ring
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rot12, Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf <;>
      linear_combination hC

theorem rot23_unitary (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    rot23 c s ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := by
  have hC : (c : ℂ) * c + (s : ℂ) * s = 1 := by
    rw [show (1 : ℂ) = ((c ^ 2 + s ^ 2 : ℝ) : ℂ) by rw [h]; simp]; push_cast; ring
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rot23, Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf <;>
      linear_combination hC

theorem rot13_unitary (c s δ : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    rot13 c s δ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := by
  have hC : (c : ℂ) * c + (s : ℂ) * s = 1 := by
    rw [show (1 : ℂ) = ((c ^ 2 + s ^ 2 : ℝ) : ℂ) by rw [h]; simp]; push_cast; ring
  have hL : link (-δ) * link δ = 1 := link_neg_mul δ
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rot13, Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf <;>
      first
        | linear_combination hC
        | linear_combination hC + ((s : ℂ) * (s : ℂ)) * hL

/-! ## The CKM matrix `V = R₂₃ · R₁₃(δ) · R₁₂` -/

/-- **The CKM mixing matrix** in standard parametrization. -/
noncomputable def ckm (c12 s12 c13 s13 c23 s23 δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  rot23 c23 s23 * rot13 c13 s13 δ * rot12 c12 s12

/-- **The CKM matrix is unitary** — a product of unitary plane rotations. -/
theorem ckm_unitary {c12 s12 c13 s13 c23 s23 δ : ℝ} (h12 : c12 ^ 2 + s12 ^ 2 = 1)
    (h13 : c13 ^ 2 + s13 ^ 2 = 1) (h23 : c23 ^ 2 + s23 ^ 2 = 1) :
    ckm c12 s12 c13 s13 c23 s23 δ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) :=
  mul_mem (mul_mem (rot23_unitary c23 s23 h23) (rot13_unitary c13 s13 δ h13))
    (rot12_unitary c12 s12 h12)

/-- **Unitarity certificate:** `Vᴴ V = 1`. -/
theorem ckm_unitary_apply {c12 s12 c13 s13 c23 s23 δ : ℝ} (h12 : c12 ^ 2 + s12 ^ 2 = 1)
    (h13 : c13 ^ 2 + s13 ^ 2 = 1) (h23 : c23 ^ 2 + s23 ^ 2 = 1) :
    star (ckm c12 s12 c13 s13 c23 s23 δ) * ckm c12 s12 c13 s13 c23 s23 δ = 1 :=
  (ckm_unitary h12 h13 h23).1

/-! ## The CKM entries and the Jarlskog invariant -/

theorem ckm_us (c12 s12 c13 s13 c23 s23 δ : ℝ) :
    ckm c12 s12 c13 s13 c23 s23 δ 0 1 = (s12 : ℂ) * c13 := by
  simp [ckm, rot12, rot13, rot23, Matrix.mul_apply, Fin.sum_univ_three]; ring

theorem ckm_cb (c12 s12 c13 s13 c23 s23 δ : ℝ) :
    ckm c12 s12 c13 s13 c23 s23 δ 1 2 = (s23 : ℂ) * c13 := by
  simp [ckm, rot12, rot13, rot23, Matrix.mul_apply, Fin.sum_univ_three]

theorem ckm_ub (c12 s12 c13 s13 c23 s23 δ : ℝ) :
    ckm c12 s12 c13 s13 c23 s23 δ 0 2 = (s13 : ℂ) * link (-δ) := by
  simp [ckm, rot12, rot13, rot23, Matrix.mul_apply, Fin.sum_univ_three]

theorem ckm_cs (c12 s12 c13 s13 c23 s23 δ : ℝ) :
    ckm c12 s12 c13 s13 c23 s23 δ 1 1
      = (c12 : ℂ) * c23 - (s12 : ℂ) * s13 * s23 * link δ := by
  simp [ckm, rot12, rot13, rot23, Matrix.mul_apply, Fin.sum_univ_three]; ring

/-- **The Jarlskog invariant of the CKM matrix** in closed form:
`J = c₁₂ c₁₃² c₂₃ s₁₂ s₁₃ s₂₃ · sin δ`. CP violation is carried entirely by the holonomy phase. -/
theorem ckm_jarlskog (c12 s12 c13 s13 c23 s23 δ : ℝ) :
    jarlskog (ckm c12 s12 c13 s13 c23 s23 δ 0 1) (ckm c12 s12 c13 s13 c23 s23 δ 1 2)
      (ckm c12 s12 c13 s13 c23 s23 δ 0 2) (ckm c12 s12 c13 s13 c23 s23 δ 1 1)
      = c12 * c13 ^ 2 * c23 * s12 * s13 * s23 * Real.sin δ := by
  rw [ckm_us, ckm_cb, ckm_ub, ckm_cs]
  unfold jarlskog
  have hL : link δ * link (-δ) = 1 := by rw [link_mul, add_neg_cancel, link_zero]
  have key : (s12 : ℂ) * c13 * ((s23 : ℂ) * c13) * conj ((s13 : ℂ) * link (-δ))
        * conj ((c12 : ℂ) * c23 - (s12 : ℂ) * s13 * s23 * link δ)
      = ((c12 * c13 ^ 2 * c23 * s12 * s13 * s23 : ℝ) : ℂ) * link δ
        - ((c13 ^ 2 * s12 ^ 2 * s13 ^ 2 * s23 ^ 2 : ℝ) : ℂ) * (link δ * link (-δ)) := by
    simp only [map_mul, map_sub, Complex.conj_ofReal, conj_link, neg_neg]
    push_cast; ring
  rw [key, hL, mul_one, Complex.sub_im, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, link_im, link_re, zero_mul, add_zero]
  ring

/-! ## Assembled from the spine: mass-ratio angles + holonomy phase -/

open HqivSpine.Physics.CabibboInterference

/-- **The CKM matrix built from spine data:** each plane's angle is the Gatto–Sartori–Tonin
mass-ratio angle (`CabibboInterference.cosθ/sinθ`), the phase is the fibre holonomy `δ`. -/
noncomputable def ckmSpine (m1 m1' m2 m2' m3 m3' δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ckm (cosθ m1 m1') (sinθ m1 m1') (cosθ m2 m2') (sinθ m2 m2') (cosθ m3 m3') (sinθ m3 m3') δ

private theorem sector_pyth (m m' : ℝ) (hm : 0 < m) (hm' : 0 < m') :
    cosθ m m' ^ 2 + sinθ m m' ^ 2 = 1 := by
  have := sin_sq_add_cos_sq m m' hm hm'; linarith

/-- **The spine-assembled CKM matrix is unitary.** -/
theorem ckmSpine_unitary {m1 m1' m2 m2' m3 m3' δ : ℝ} (h1 : 0 < m1) (h1' : 0 < m1')
    (h2 : 0 < m2) (h2' : 0 < m2') (h3 : 0 < m3) (h3' : 0 < m3') :
    ckmSpine m1 m1' m2 m2' m3 m3' δ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) :=
  ckm_unitary (sector_pyth m1 m1' h1 h1') (sector_pyth m2 m2' h2 h2') (sector_pyth m3 m3' h3 h3')

private theorem sinθ_pos (m m' : ℝ) (hm : 0 < m) (hm' : 0 < m') : 0 < sinθ m m' :=
  Real.sqrt_pos.mpr (by positivity)

private theorem cosθ_pos (m m' : ℝ) (hm : 0 < m) (hm' : 0 < m') : 0 < cosθ m m' :=
  Real.sqrt_pos.mpr (by positivity)

/-- **CP violation from the spine:** the spine-assembled CKM matrix has a non-zero Jarlskog
invariant **iff** the holonomy phase is genuine (`sin δ ≠ 0`). The mixing angles are all non-trivial
for positive masses, so CP violation is exactly the non-triviality of the fibre holonomy. -/
theorem ckmSpine_cp_violation {m1 m1' m2 m2' m3 m3' δ : ℝ} (h1 : 0 < m1) (h1' : 0 < m1')
    (h2 : 0 < m2) (h2' : 0 < m2') (h3 : 0 < m3) (h3' : 0 < m3') (hδ : Real.sin δ ≠ 0) :
    jarlskog (ckmSpine m1 m1' m2 m2' m3 m3' δ 0 1) (ckmSpine m1 m1' m2 m2' m3 m3' δ 1 2)
      (ckmSpine m1 m1' m2 m2' m3 m3' δ 0 2) (ckmSpine m1 m1' m2 m2' m3 m3' δ 1 1) ≠ 0 := by
  rw [ckmSpine, ckm_jarlskog]
  have c1 := cosθ_pos m1 m1' h1 h1'
  have s1 := sinθ_pos m1 m1' h1 h1'
  have c2 := cosθ_pos m2 m2' h2 h2'
  have s2 := sinθ_pos m2 m2' h2 h2'
  have c3 := cosθ_pos m3 m3' h3 h3'
  have s3 := sinθ_pos m3 m3' h3 h3'
  have hprod : cosθ m1 m1' * cosθ m2 m2' ^ 2 * cosθ m3 m3' * sinθ m1 m1' * sinθ m2 m2'
      * sinθ m3 m3' ≠ 0 := by positivity
  exact mul_ne_zero hprod hδ

/-! ## Closure -/

/-- **Full CKM discharge bundle.** -/
structure CKMMixingDischarged : Prop where
  factors_unitary :
    ∀ (c s δ : ℝ), c ^ 2 + s ^ 2 = 1 →
      rot12 c s ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) ∧
      rot23 c s ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) ∧
      rot13 c s δ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ)
  ckm_unitary :
    ∀ (c12 s12 c13 s13 c23 s23 δ : ℝ), c12 ^ 2 + s12 ^ 2 = 1 → c13 ^ 2 + s13 ^ 2 = 1 →
      c23 ^ 2 + s23 ^ 2 = 1 →
      star (ckm c12 s12 c13 s13 c23 s23 δ) * ckm c12 s12 c13 s13 c23 s23 δ = 1
  jarlskog_closed_form :
    ∀ (c12 s12 c13 s13 c23 s23 δ : ℝ),
      jarlskog (ckm c12 s12 c13 s13 c23 s23 δ 0 1) (ckm c12 s12 c13 s13 c23 s23 δ 1 2)
        (ckm c12 s12 c13 s13 c23 s23 δ 0 2) (ckm c12 s12 c13 s13 c23 s23 δ 1 1)
        = c12 * c13 ^ 2 * c23 * s12 * s13 * s23 * Real.sin δ

/-- **The full unitary CKM matrix is discharged:** the three plane rotations (mass-ratio angles +
holonomy phase) are each unitary, their product is a unitary `U(3)` element, and its Jarlskog
invariant has the standard closed form `c₁₂c₁₃²c₂₃s₁₂s₁₃s₂₃·sin δ`. -/
theorem ckmMixingDischarged_holds : CKMMixingDischarged where
  factors_unitary c s δ h := ⟨rot12_unitary c s h, rot23_unitary c s h, rot13_unitary c s δ h⟩
  ckm_unitary _ _ _ _ _ _ _ h12 h13 h23 := ckm_unitary_apply h12 h13 h23
  jarlskog_closed_form := ckm_jarlskog

end HqivSpine.Physics.CKMMixingMatrix
