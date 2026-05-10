import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Problems.YangMills.Quantum

/-!
# Real Schwartz functions as complex-valued Schwartz functions

`MillenniumYangMillsDefs.SchwartzSpace` is `𝓢(ℝ⁴, ℝ)`. The HQIV patch jet layer uses
`PatchSchwartzSpace = 𝓢(ℝ⁴, ℂ)`. This file provides the canonical ℝ-linear embedding
`f ↦ (x ↦ (f x : ℂ))`, used to feed real Clay test functions into the patch OVD.
-/

namespace Hqiv.Story

open MillenniumYangMillsDefs
open scoped SchwartzMap

noncomputable section

open SchwartzMap

/-- Coerce a real Schwartz map to a complex-valued Schwartz map (pointwise `Complex.ofReal`). -/
noncomputable def schwartzRealToComplex (f : SchwartzSpace) : PatchSchwartzSpace :=
  let fR : SchwartzMap Spacetime ℝ := (f : SchwartzMap Spacetime ℝ)
  { toFun := fun x => Complex.ofRealCLM (fR x)
    smooth' := by
      simpa [SchwartzMap] using
        (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.comp (fR.smooth ⊤)
    decay' := by
      intro k n
      rcases f.decay' k n with ⟨C, hC⟩
      refine ⟨C, fun x => ?_⟩
      have hf := contDiff_iff_contDiffAt.1 (fR.smooth ⊤) x
      have hcomp :
          ‖iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ fR) x‖ ≤ ‖iteratedFDeriv ℝ n fR x‖ :=
        (ContinuousLinearMap.norm_iteratedFDeriv_comp_left (L := Complex.ofRealCLM) (f := fR)
            (x := x) hf (n := n) (by norm_cast; exact le_top)).trans
          (by
            have h1 : ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ = 1 := by simp [Complex.ofRealCLM]
            simp [h1])
      calc
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun t : Spacetime => Complex.ofRealCLM (fR t)) x‖
            = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ fR) x‖ := rfl
        _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n fR x‖ := by gcongr
        _ ≤ C := hC x }

@[simp]
theorem schwartzRealToComplex_apply (f : SchwartzSpace) (x : Spacetime) :
    (schwartzRealToComplex f).toFun x = (f.toFun x : ℂ) :=
  rfl

/-- Spacelike separation support for real tests implies the same pointwise separation for the
complex lifts used in `patchDerivOVD`. -/
theorem schwartzRealToComplex_spacelikeSeparation (f g : SchwartzSpace)
    (h : ∀ (x y : Spacetime), MinkowskiMetric (x - y) (x - y) < 0 → f.toFun x = 0 ∨ g.toFun y = 0) :
    ∀ (x y : Spacetime), MinkowskiMetric (x - y) (x - y) < 0 →
      (schwartzRealToComplex f).toFun x = 0 ∨ (schwartzRealToComplex g).toFun y = 0 := by
  intro x y hxy
  rcases h x y hxy with hf | hg
  · left; simp [schwartzRealToComplex_apply, hf]
  · right; simp [schwartzRealToComplex_apply, hg]

end

end Hqiv.Story
