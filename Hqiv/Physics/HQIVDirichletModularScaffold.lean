import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Hqiv.Geometry.SpatialSliceRapidityScaffold

/-!
# HQIV Dirichlet / modular scaffold (Milestones F–G)

This file provides:

* a canonical coefficient scaffold `hqivCoeff` derived from the class/domain `1/k` spiral phase;
* a Dirichlet-series definition `hqivDirichletSeries`;
* explicit coefficient growth bounds `|a_n| ≤ C * (n+1)^ε` under stated hypotheses;
* **proved** absolute convergence on `Re s > 1` (same p-series mechanism as `OctonionicZeta`);
* a theorem-shaped completed-L scaffold for functional-equation packaging.

Functional equations / reflection to the critical strip are still packaged as explicit hypotheses
(`ThreeSpiralGammaSymmetry`), not as finished analytic theorems.
-/

namespace Hqiv.Physics

open scoped BigOperators Topology
open Complex
open Hqiv.Geometry

noncomputable section

/-- Canonical probe coefficient from the class/domain `1/k` spiral phase. -/
noncomputable def hqivCoeff (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k n : ℕ) : ℝ :=
  Real.cos (rapidityPhaseFromOmegaOneOverKOnDomain φ t ω domains c k n)

/-- Coefficient growth base bound: cosine slot is uniformly bounded by `1`. -/
theorem abs_hqivCoeff_le_one (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k n : ℕ) :
    |hqivCoeff φ t ω domains c k n| ≤ 1 := by
  simpa [hqivCoeff] using Real.abs_cos_le_one (rapidityPhaseFromOmegaOneOverKOnDomain φ t ω domains c k n)

/-- Explicit `n^ε` growth envelope for coefficients (for any `ε ≥ 0`, `C ≥ 1`). -/
theorem abs_hqivCoeff_le_C_mul_pow (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k n : ℕ) (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 ≤ ε) :
    |hqivCoeff φ t ω domains c k n| ≤ C * ((n + 1 : ℝ) ^ ε) := by
  have h1 : |hqivCoeff φ t ω domains c k n| ≤ 1 :=
    abs_hqivCoeff_le_one φ t ω domains c k n
  have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hpow : (1 : ℝ) ≤ (n + 1 : ℝ) ^ ε := by
    simpa using Real.one_le_rpow hbase hε
  have hCnonneg : 0 ≤ C := le_trans (by norm_num) hC
  have hmul : (1 : ℝ) ≤ C * ((n + 1 : ℝ) ^ ε) := by
    nlinarith [hC, hpow, hCnonneg]
  exact le_trans h1 hmul

/-- Dirichlet-series term from canonical coefficients. -/
noncomputable def hqivDirichletTerm (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  (hqivCoeff φ t ω domains c k n : ℂ) * ((n + 1 : ℂ) ^ (-s))

/-- Canonical Dirichlet-series scaffold for HQIV coefficients. -/
noncomputable def hqivDirichletSeries (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, hqivDirichletTerm φ t ω domains c k s n

theorem hqivDirichletTerm_eq (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (s : ℂ) (n : ℕ) :
    hqivDirichletTerm φ t ω domains c k s n =
      (hqivCoeff φ t ω domains c k n : ℂ) * ((n + 1 : ℂ) ^ (-s)) := by
  rfl

theorem norm_hqivCoeff_complex_le_one (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k n : ℕ) :
    ‖(hqivCoeff φ t ω domains c k n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_hqivCoeff_le_one φ t ω domains c k n

theorem norm_hqivDirichletTerm_le (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (s : ℂ) (n : ℕ) :
    ‖hqivDirichletTerm φ t ω domains c k s n‖ ≤ (1 : ℝ) / ((n + 1 : ℝ) ^ s.re) := by
  have hnpos : (0 : ℝ) < (n + 1 : ℝ) := Nat.cast_add_one_pos n
  have hcast : (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) := by norm_cast
  have hcpow : ‖(n + 1 : ℂ) ^ (-s)‖ = (n + 1 : ℝ) ^ (-s.re) := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.neg_re]
  have hcoef := norm_hqivCoeff_complex_le_one φ t ω domains c k n
  have hmul :
      ‖(hqivCoeff φ t ω domains c k n : ℂ)‖ * ‖(n + 1 : ℂ) ^ (-s)‖ ≤
        1 * (n + 1 : ℝ) ^ (-s.re) := by
    rw [hcpow]
    exact mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (n + 1 : ℝ) ^ (-s.re))
  calc
    ‖hqivDirichletTerm φ t ω domains c k s n‖
        = ‖(hqivCoeff φ t ω domains c k n : ℂ)‖ * ‖(n + 1 : ℂ) ^ (-s)‖ := by
          rw [hqivDirichletTerm, Complex.norm_mul]
    _ ≤ 1 * (n + 1 : ℝ) ^ (-s.re) := hmul
    _ = (n + 1 : ℝ) ^ (-s.re) := by ring
    _ = (1 : ℝ) / ((n + 1 : ℝ) ^ s.re) := by
          have hn' : (0 : ℝ) ≤ (n + 1 : ℝ) := hnpos.le
          rw [Real.rpow_neg hn', inv_eq_one_div]

theorem hqivDirichletTerm_summable_of_re_gt_one (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (s : ℂ) (hs : 1 < s.re) :
    Summable (hqivDirichletTerm φ t ω domains c k s) := by
  have h1 : 1 < s.re := hs
  have hps :
      Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℝ) ^ s.re) := by
    have h0 := (Real.summable_one_div_nat_add_rpow (a := (1 : ℝ)) (s := s.re)).mpr h1
    refine Summable.congr h0 ?_
    intro n
    have habs : |(n : ℝ) + 1| = (n : ℝ) + 1 :=
      abs_of_nonneg (Nat.cast_add_one_pos n).le
    simp [div_eq_mul_inv, habs]
  exact Summable.of_norm_bounded hps fun n => norm_hqivDirichletTerm_le φ t ω domains c k s n

@[simp]
theorem hqivDirichletSeries_eq_tsum (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (s : ℂ) :
    hqivDirichletSeries φ t ω domains c k s = ∑' n : ℕ, hqivDirichletTerm φ t ω domains c k s n :=
  rfl

/-- Completed-L scaffold from an external gamma factor candidate. -/
noncomputable def completedHQIVL (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (gammaFactor : ℂ → ℂ) (s : ℂ) : ℂ :=
  gammaFactor s * hqivDirichletSeries φ t ω domains c k s

/-- Packaged symmetry hypothesis (e.g. from 3-spiral class symmetry analysis). -/
structure ThreeSpiralGammaSymmetry (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) where
  gammaFactor : ℂ → ℂ
  epsilon : ℂ
  functionalEquation :
    ∀ s : ℂ,
      completedHQIVL φ t ω domains c k gammaFactor s =
        epsilon * completedHQIVL φ t ω domains c k gammaFactor (1 - s)

/-- Functional equation theorem once symmetry data is supplied. -/
theorem completedHQIVL_functionalEquation_of_threeSpiralSymmetry
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains) (c k : ℕ)
    (S : ThreeSpiralGammaSymmetry φ t ω domains c k) :
    ∀ s : ℂ,
      completedHQIVL φ t ω domains c k S.gammaFactor s =
        S.epsilon * completedHQIVL φ t ω domains c k S.gammaFactor (1 - s) :=
  S.functionalEquation

end

