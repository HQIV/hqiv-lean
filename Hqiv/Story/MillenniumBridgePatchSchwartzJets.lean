/-
Copyright (c) 2026 HQIV contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.Support
import Problems.YangMills.Quantum

/-!
# Schwartz jet surjectivity at the origin (patch smearing)

Construction: a smooth compactly supported bump `φ` equal to `1` near `0`, multiplied by the
complex linear form `x ↦ ∑ᵢ wᵢ · (xᵢ : ℂ)`. On `𝓝 0` this agrees with the linear map, so each
directional derivative along the standard basis matches `wᵢ`.
-/

namespace Hqiv.Story

open Filter Function Metric Finset
open scoped ContDiff Topology

noncomputable section

open MillenniumYangMillsDefs EuclideanSpace SchwartzMap

/-- Affine complex linear form on `Spacetime = ℝ⁴` used to prescribe first jets at the origin. -/
noncomputable def patchJetLinearCLM (w : Fin 4 → ℂ) : Spacetime →L[ℝ] ℂ :=
  Finset.univ.sum fun i : Fin 4 =>
    (w i) • (Complex.ofRealCLM.comp (PiLp.proj _ _ i : Spacetime →L[ℝ] ℝ))

theorem patchJetLinearCLM_single (w : Fin 4 → ℂ) (i : Fin 4) :
    patchJetLinearCLM w (EuclideanSpace.single i (1 : ℝ)) = w i := by
  classical
  simp [patchJetLinearCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, PiLp.proj_apply,
    EuclideanSpace.single_apply, apply_ite, Finset.mem_univ]

theorem contDiff_patchJetLinearCLM_apply (w : Fin 4 → ℂ) {n : ℕ∞} :
    ContDiff ℝ n (patchJetLinearCLM w) :=
  (patchJetLinearCLM w).contDiff

/-- Pointwise product of a real bump and the jet linear map, `ℂ`-valued. -/
noncomputable def patchJetBumpFun (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℂ) :
    Spacetime → ℂ :=
  fun x => (φ x : ℂ) * patchJetLinearCLM w x

theorem eventuallyEq_patchJetBumpFun_patchJetLinearCLM (φ : ContDiffBump (0 : Spacetime)) (w) :
    patchJetBumpFun φ w =ᶠ[𝓝 (0 : Spacetime)] patchJetLinearCLM w := by
  filter_upwards [ContDiffBump.eventuallyEq_one φ] with x hx
  simp [patchJetBumpFun, hx, Complex.ofReal_one, one_mul]

theorem contDiff_patchJetBumpFun (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℂ) {n : ℕ∞} :
    ContDiff ℝ n (patchJetBumpFun φ w) := by
  change ContDiff ℝ n fun x => (φ x : ℂ) * patchJetLinearCLM w x
  have hφ : ContDiff ℝ n fun x : Spacetime => (φ x : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (φ.contDiff : ContDiff ℝ n (φ : Spacetime → ℝ))
  exact hφ.mul (contDiff_patchJetLinearCLM_apply w)

theorem hasCompactSupport_patchJetBumpFun (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℂ) :
    HasCompactSupport (patchJetBumpFun φ w) := by
  classical
  have hφ : HasCompactSupport (φ : Spacetime → ℝ) := ContDiffBump.hasCompactSupport φ
  have hsupp :
      Function.support (fun x : Spacetime => (φ x : ℂ)) = Function.support φ := by
    ext x
    simp [Function.mem_support, Complex.ofReal_eq_zero]
  have hsupp_t : tsupport (fun x : Spacetime => (φ x : ℂ)) = tsupport φ := by
    simp [tsupport, hsupp]
  have hφℂ : HasCompactSupport fun x : Spacetime => (φ x : ℂ) := by
    simpa [HasCompactSupport, hsupp_t] using hφ
  have hmul :
      patchJetBumpFun φ w = (fun x : Spacetime => (φ x : ℂ)) * fun t => patchJetLinearCLM w t := by
    rfl
  rw [hmul]
  exact HasCompactSupport.mul_right hφℂ

noncomputable def patchJetBumpSchwartz (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℂ) :
    SchwartzMap Spacetime ℂ :=
  (hasCompactSupport_patchJetBumpFun φ w).toSchwartzMap (contDiff_patchJetBumpFun (n := ⊤) φ w)

theorem lineDeriv_patchJetLinearCLM_single (w : Fin 4 → ℂ) (i : Fin 4) :
    lineDeriv ℝ (patchJetLinearCLM w) (0 : Spacetime) (EuclideanSpace.single i (1 : ℝ)) = w i := by
  classical
  let L := patchJetLinearCLM w
  have hdiff : DifferentiableAt ℝ (fun x : Spacetime => L x) 0 := L.differentiableAt
  rw [hdiff.lineDeriv_eq_fderiv, ContinuousLinearMap.fderiv]
  exact patchJetLinearCLM_single w i

theorem lineDeriv_patchJetBumpSchwartz_single
    (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℂ) (i : Fin 4) :
    lineDeriv ℝ (patchJetBumpSchwartz φ w) (0 : Spacetime)
        (EuclideanSpace.single i (1 : ℝ)) = w i := by
  classical
  let v := EuclideanSpace.single i (1 : ℝ)
  have hev := eventuallyEq_patchJetBumpFun_patchJetLinearCLM φ w
  have hld :=
    Filter.EventuallyEq.lineDeriv_eq (𝕜 := ℝ) (F := ℂ) (f₁ := patchJetBumpFun φ w)
      (f := fun x : Spacetime => patchJetLinearCLM w x) (x := (0 : Spacetime)) (v := v) hev
  have hco :
      lineDeriv ℝ (patchJetBumpSchwartz φ w) (0 : Spacetime) v =
        lineDeriv ℝ (patchJetBumpFun φ w) (0 : Spacetime) v := rfl
  rw [hco, hld, lineDeriv_patchJetLinearCLM_single]

/-- Independent complex directional derivatives at `0` along the standard Euclidean basis. -/
theorem schwartzMap_complex_directionalJets_at_zero_single (w : Fin 4 → ℂ) :
    ∃ f : SchwartzMap Spacetime ℂ, ∀ i : Fin 4,
      lineDeriv ℝ f (0 : Spacetime) (EuclideanSpace.single i (1 : ℝ)) = w i := by
  classical
  let φ : ContDiffBump (0 : Spacetime) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  refine ⟨patchJetBumpSchwartz φ w, fun i => ?_⟩
  simpa using lineDeriv_patchJetBumpSchwartz_single φ w i

end

end Hqiv.Story
