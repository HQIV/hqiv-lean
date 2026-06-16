import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Hqiv.Story.S3HeatFlowArrowNoBackprojection

/-!
# de Bruijn–Newman lattice inheritance: the classical target, formalized

`S3HeatFlowArrowNoBackprojection` proved the lattice side: backward flow is
impossible on the discrete carrier and the ladder analogue locks
`lambdaHQIV = 0`.  This module formalizes the **classical side** so the
inheritance claim ("the lattice no-backprojection bound transfers to the
continuum `ξ` heat flow") is a precise Lean statement, not prose.

## Contents

* **The classical objects, concretely.**  `dbnPhiTerm` / `dbnPhi` is the de
  Bruijn–Newman density
  `Φ(u) = ∑ₙ (2π²n⁴e^{9u} − 3πn²e^{5u}) e^{−πn²e^{4u}}`,
  and `dbnHeatFamily t z = ∫_{u>0} e^{tu²} Φ(u) cos(zu) du` is the deformed
  family with `H₀` the (normalized) `ξ`.  Both are now Lean terms.
  **Proved:** every `Φ`-term is nonnegative for `u ≥ 0`
  (`dbnPhiTerm_nonneg`) and the term series is summable
  (`dbnPhi_summable`), so `dbnPhi` is an honest convergent sum on `u ≥ 0`.

* **Weight-level dictionary (proved).**  The dBN Gaussian factor *is* the
  repo's discrete heat weight under `(τ, u) ↦ (−t, u²)`:
  `dbnGaussianFactor t u = discreteHeatKernelWeight (−t) (u²)`.
  The forward/backward dichotomy transfers: `t ≤ 0` is a contraction on every
  mode, `t > 0` is unbounded — the exact continuum mirror of
  `backprojection_weight_unbounded`.

* **The inheritance bridge.**  `DBNLatticeInheritance` carries the classical
  constant `Λ` with its two classical facts as explicit fields (Rodgers–Tao
  `Λ ≥ 0`; Newman/dBN `RH ↔ Λ ≤ 0` — neither is in Mathlib yet) plus the
  single new claim `lattice_dominates : Λ ≤ lambdaHQIV`.  Since the ladder
  witness proves `lambdaHQIV = 0`, the bridge forces `Λ = 0` and hence RH.

* **Honesty theorem.**  `lattice_dominates_iff_RiemannHypothesis`: given the
  two classical imports, the inheritance bound is *equivalent to RH*.  This is
  the precise formal content of "I can't imagine a world where that isn't
  true" — the conviction names exactly the RH-hard step, with the
  thermodynamic side already discharged.
-/

namespace Hqiv.Story

open Hqiv.Physics

noncomputable section

/-! ## The de Bruijn–Newman density `Φ` -/

/-- `n`-th term of the de Bruijn–Newman density (indexing `m = n + 1 ≥ 1`):
`(2π²m⁴e^{9u} − 3πm²e^{5u}) · e^{−πm²e^{4u}}`. -/
def dbnPhiTerm (u : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
      - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u)) *
    Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)))

/-- The de Bruijn–Newman density `Φ(u)` as a series over shells. -/
def dbnPhi (u : ℝ) : ℝ :=
  ∑' n : ℕ, dbnPhiTerm u n

/-- Off-horizon shell scale is at least `1`. -/
private theorem one_le_shell (n : ℕ) : (1 : ℝ) ≤ (n : ℝ) + 1 := by
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private theorem one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : (1 : ℝ) ≤ Real.exp x := by
  have h := Real.add_one_le_exp x
  linarith

/-- The leading factor dominates: `3 ≤ 2π m² e^{4u}` for `u ≥ 0`, `m ≥ 1`. -/
private theorem three_le_leading {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (3 : ℝ) ≤ 2 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) := by
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hm : (1 : ℝ) ≤ (n : ℝ) + 1 := one_le_shell n
  have hm2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have he : (1 : ℝ) ≤ Real.exp (4 * u) := one_le_exp_of_nonneg (by linarith)
  have hπpos : (0 : ℝ) < Real.pi := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hm2 (by linarith : (0:ℝ) ≤ 2 * Real.pi),
    mul_le_mul_of_nonneg_left he
      (by nlinarith : (0:ℝ) ≤ 2 * Real.pi * ((n : ℝ) + 1) ^ 2)]

/-- **Positivity of the density terms** for `u ≥ 0`: the quartic shell term
dominates the quadratic one as soon as `2π m² e^{4u} ≥ 3`, which holds on every
shell since `π > 3`. -/
theorem dbnPhiTerm_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ dbnPhiTerm u n := by
  have hexp9 : Real.exp (9 * u) = Real.exp (4 * u) * Real.exp (5 * u) := by
    rw [← Real.exp_add]; ring_nf
  have hP : (0 : ℝ) < Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u) := by
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have hm : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    positivity
  have hfac := three_le_leading hu n
  have hAB :
      0 ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
          - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u) := by
    rw [hexp9]
    nlinarith [mul_nonneg
      (by linarith : (0:ℝ) ≤ 2 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) - 3)
      hP.le]
  exact mul_nonneg hAB (Real.exp_pos _).le

/-- **Summability of the density series** for `u ≥ 0`: dominated by a
polynomial-times-geometric tail with ratio `e^{−πe^{4u}} < 1`. -/
theorem dbnPhi_summable {u : ℝ} (hu : 0 ≤ u) :
    Summable (dbnPhiTerm u) := by
  set c : ℝ := Real.pi * Real.exp (4 * u) with hc_def
  have hcpos : 0 < c := by
    have := Real.pi_pos
    positivity
  set r : ℝ := Real.exp (-c) with hr_def
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr_def, show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h1 : Summable (fun k : ℕ => (k : ℝ) ^ 4 * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 4
      (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  have h2 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 4 * r ^ (n + 1)) :=
    h1.comp_injective Nat.succ_injective
  set K : ℝ := 2 * Real.pi ^ 2 * Real.exp (9 * u) with hK_def
  have hK : 0 ≤ K := by
    have := Real.pi_pos
    positivity
  refine Summable.of_nonneg_of_le (fun n => dbnPhiTerm_nonneg hu n) (fun n => ?_)
    (h2.mul_left K)
  -- Bound term `n`: drop the negative part, then `e^{−πm²e^{4u}} ≤ r^{m}`.
  have hm1 : (1 : ℝ) ≤ (n : ℝ) + 1 := one_le_shell n
  have hEbound :
      Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))) ≤ r ^ (n + 1) := by
    have hpow : r ^ (n + 1) = Real.exp (((n + 1 : ℕ) : ℝ) * (-c)) := by
      rw [hr_def, ← Real.exp_nat_mul]
    rw [hpow]
    apply Real.exp_le_exp.mpr
    have hm2 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    push_cast
    rw [hc_def]
    nlinarith [hcpos, mul_le_mul_of_nonneg_right hm2 hcpos.le]
  have hBpos : 0 ≤ 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u) := by
    have := Real.pi_pos
    positivity
  have hApos : 0 ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u) := by
    have := Real.pi_pos
    positivity
  calc dbnPhiTerm u n
      ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u) *
          Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))) := by
        unfold dbnPhiTerm
        have hE : (0 : ℝ) < Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))) :=
          Real.exp_pos _
        nlinarith [mul_nonneg hBpos hE.le]
    _ ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u) * r ^ (n + 1) := by
        apply mul_le_mul_of_nonneg_left hEbound hApos
    _ = K * (((n + 1 : ℕ) : ℝ) ^ 4 * r ^ (n + 1)) := by
        rw [hK_def]
        push_cast
        ring

/-! ## The deformed family `H_t` and the weight-level dictionary -/

/-- The de Bruijn–Newman Gaussian deformation factor `e^{tu²}`. -/
def dbnGaussianFactor (t u : ℝ) : ℝ :=
  Real.exp (t * u ^ 2)

/-- The deformed de Bruijn–Newman family
`H_t(z) = ∫_{u>0} e^{tu²} Φ(u) cos(zu) du`; `H₀` is the (normalized) `ξ`. -/
def dbnHeatFamily (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ),
    ((dbnGaussianFactor t u * dbnPhi u : ℝ) : ℂ) * Complex.cos (z * u)

/--
**Weight-level dictionary (proved).**  The classical Gaussian deformation
factor *is* the repo's discrete heat weight under `(τ, u) ↦ (−t, u²)`:
the lattice and continuum flows use the same one-parameter kernel family.
-/
theorem dbnGaussianFactor_eq_discreteHeatKernelWeight (t u : ℝ) :
    dbnGaussianFactor t u = discreteHeatKernelWeight (-t) (u ^ 2) := by
  simp [dbnGaussianFactor, discreteHeatKernelWeight]

/-- Backward continuum flow (`t ≤ 0`) is a contraction on every mode. -/
theorem dbn_backward_factor_le_one {t : ℝ} (ht : t ≤ 0) (u : ℝ) :
    dbnGaussianFactor t u ≤ 1 := by
  unfold dbnGaussianFactor
  have : t * u ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht (sq_nonneg u)
  exact Real.exp_le_one_iff.mpr this

/--
Forward continuum flow (`t > 0`) is **unbounded in the mode coordinate** —
the continuum mirror of `backprojection_weight_unbounded` on the lattice:
the same kernel family that cannot host a backward semigroup on the discrete
carrier amplifies without bound under forward continuum deformation.
-/
theorem dbn_forward_factor_unbounded {t : ℝ} (ht : 0 < t) (C : ℝ) :
    ∃ u : ℝ, C < dbnGaussianFactor t u := by
  refine ⟨Real.sqrt ((|C| + 1) / t), ?_⟩
  unfold dbnGaussianFactor
  have habs : (0 : ℝ) ≤ |C| := abs_nonneg C
  have hquot : 0 ≤ (|C| + 1) / t := by positivity
  have hsq : Real.sqrt ((|C| + 1) / t) ^ 2 = (|C| + 1) / t := Real.sq_sqrt hquot
  rw [hsq, mul_div_cancel₀ _ (ne_of_gt ht)]
  have hC : C ≤ |C| := le_abs_self C
  calc C ≤ |C| := hC
    _ < |C| + 1 + 1 := by linarith
    _ ≤ Real.exp (|C| + 1) := Real.add_one_le_exp _

/-- At `t = 0` the deformation factor is the identity weight. -/
theorem dbnGaussianFactor_zero (u : ℝ) : dbnGaussianFactor 0 u = 1 := by
  simp [dbnGaussianFactor]

/-! ## The inheritance bridge -/

/--
**de Bruijn–Newman lattice inheritance.**  Carries the classical constant
`Lambda` with its two classical facts as explicit fields — they are honest
imports, not yet in Mathlib:

* `rodgers_tao` — the Rodgers–Tao theorem `Λ ≥ 0`;
* `newman_iff` — the Newman / de Bruijn equivalence `RH ↔ Λ ≤ 0`;

plus the single new claim this repo's geometry is after:

* `lattice_dominates` — the discrete no-backprojection lock transfers:
  `Λ ≤ lambdaHQIV` for the concrete ladder witness `W` (whose `lambdaHQIV = 0`
  is already proved).
-/
structure DBNLatticeInheritance (W : TempLadderFiniteWindowConcrete) where
  Lambda : ℝ
  rodgers_tao : 0 ≤ Lambda
  newman_iff : RiemannHypothesis ↔ Lambda ≤ 0
  lattice_dominates : Lambda ≤ (W.toLambdaHQIVZero).lambdaHQIV

/-- The inheritance bridge pins the classical constant to zero. -/
theorem Lambda_eq_zero_of_inheritance
    {W : TempLadderFiniteWindowConcrete} (B : DBNLatticeInheritance W) :
    B.Lambda = 0 := by
  have hlock : (W.toLambdaHQIVZero).lambdaHQIV = 0 :=
    lambdaHQIV_eq_zero_of_finiteWindowConcrete W
  have hle : B.Lambda ≤ 0 := hlock ▸ B.lattice_dominates
  exact le_antisymm hle B.rodgers_tao

/-- The inheritance bridge yields Mathlib's `RiemannHypothesis`. -/
theorem RiemannHypothesis_of_dbnLatticeInheritance
    {W : TempLadderFiniteWindowConcrete} (B : DBNLatticeInheritance W) :
    RiemannHypothesis :=
  B.newman_iff.mpr (Lambda_eq_zero_of_inheritance B).le

/--
**Honesty theorem: the inheritance bound is exactly RH.**  Given the two
classical imports (Rodgers–Tao and Newman/dBN), the lattice-domination field
is *equivalent* to the Riemann Hypothesis.  The thermodynamic side
(`lambdaHQIV = 0`) is free; the entire content of "the lattice
no-backprojection lock transfers to the continuum" is the RH frontier itself,
faithfully named.
-/
theorem lattice_dominates_iff_RiemannHypothesis
    (Lambda : ℝ) (_hRT : 0 ≤ Lambda) (hN : RiemannHypothesis ↔ Lambda ≤ 0)
    (W : TempLadderFiniteWindowConcrete) :
    Lambda ≤ (W.toLambdaHQIVZero).lambdaHQIV ↔ RiemannHypothesis := by
  rw [lambdaHQIV_eq_zero_of_finiteWindowConcrete W]
  exact hN.symm

/-- The inheritance bridge instantiates the heat-flow vaporization bridge:
classical `Λ = 0` delivers the localization payload. -/
def vaporizationBridge_of_dbnLatticeInheritance
    {W : TempLadderFiniteWindowConcrete} (B : DBNLatticeInheritance W) :
    HeatFlowVaporizationBridge where
  ladder := W.toLambdaHQIVZero
  conserved := W.toFiniteWindowWitness_conserved
  regularized := W.toFiniteWindowWitness_regularized
  vaporization :=
    vaporization_iff_RiemannHypothesis.mpr
      (RiemannHypothesis_of_dbnLatticeInheritance B)

/--
**Equivalence with the vaporization payload.**  Given a concrete ladder
witness and the two classical imports, the inheritance bridge is inhabited
*iff* RH — the same frontier as the heat-flow vaporization bridge, now with
the classical constant `Λ` explicit.
-/
theorem dbnLatticeInheritance_iff_RiemannHypothesis
    (Lambda : ℝ) (hRT : 0 ≤ Lambda) (hN : RiemannHypothesis ↔ Lambda ≤ 0)
    (W : TempLadderFiniteWindowConcrete) :
    Nonempty (DBNLatticeInheritance W) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨B⟩
    exact RiemannHypothesis_of_dbnLatticeInheritance B
  · intro hRH
    exact ⟨{
      Lambda := Lambda
      rodgers_tao := hRT
      newman_iff := hN
      lattice_dominates := by
        rw [lambdaHQIV_eq_zero_of_finiteWindowConcrete W]
        exact hN.mp hRH }⟩

end

end Hqiv.Story
