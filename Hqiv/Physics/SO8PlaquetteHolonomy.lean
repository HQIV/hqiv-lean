import Hqiv.Physics.DiscretePlaquetteHolonomy
import Hqiv.Generators
import Hqiv.Topology.HopfShellComplex
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators

/-!
# SO(8) matrix plaquette holonomy (Hopf-shell + generator chart)

First **non-abelian SO(8)** upgrade beyond abelian `linearEnd` in `ActionHolonomyGlue`:

* matrix transport on the octonion carrier `Fin 8 → ℝ`;
* generator seed plaquette `G_i · G_j` on two edges;
* Hopf-shell **T11 torsion matrix** on a single Wilson edge (links `HopfShellComplex`).

Full four-edge Wilson transport and a pinned `(G₀, G₄)` non-abelian witness are discharged
here. Measure choice on rotated charts remains in
`NonAbelianHolonomyMeasureScaffold.FullNonAbelianHolonomyMeasurePending`.
-/

namespace Hqiv.Physics

set_option maxHeartbeats 80000000

open Hqiv
open Hqiv.Topology
open Hqiv.Geometry
open Matrix
open scoped BigOperators

/-- Real octonion carrier chart for SO(8) matrix transport. -/
abbrev OctonionCarrier := Fin 8 → ℝ

/-- Matrix transport on the octonion carrier. -/
def so8MatrixVecEnd (M : Matrix (Fin 8) (Fin 8) ℝ) : Function.End OctonionCarrier :=
  fun v => M.mulVec v

@[simp]
theorem so8MatrixVecEnd_mul (A B : Matrix (Fin 8) (Fin 8) ℝ) :
    so8MatrixVecEnd A * so8MatrixVecEnd B = so8MatrixVecEnd (A * B) := by
  funext v
  simp [so8MatrixVecEnd, Function.End.mul_def, mulVec_mulVec]

noncomputable section

def so8GeneratorEdge (k : Fin 28) : Function.End OctonionCarrier :=
  so8MatrixVecEnd (so8Generator k)

/-- Two SO(8) generator edges, identity on the remaining cyclic slots. -/
def so8GeneratorPlaquetteEdge (i j : Fin 28) : PlaquetteEdge OctonionCarrier :=
  fun k =>
    match k with
    | 0 => so8GeneratorEdge i
    | 1 => so8GeneratorEdge j
    | _ => 1

/-- **Full four-edge** SO(8) Wilson plaquette: one generator transport per cyclic edge. -/
def so8FullGeneratorPlaquetteEdge (i j k l : Fin 28) : PlaquetteEdge OctonionCarrier :=
  fun e =>
    so8GeneratorEdge <|
      match e with
      | 0 => i
      | 1 => j
      | 2 => k
      | 3 => l

/-- Pinned G₂-chart generator pair `(G₀, G₄)` for the concrete holonomy witness. -/
def so8PlaquetteGenI : Fin 28 := ⟨0, by decide⟩
def so8PlaquetteGenJ : Fin 28 := ⟨4, by decide⟩

@[simp] lemma so8Generator_zero : so8Generator ⟨0, by decide⟩ = generator_0 := by
  simp [so8Generator]

@[simp] lemma so8Generator_four : so8Generator ⟨4, by decide⟩ = generator_4 := by
  simp [so8Generator]

lemma so8Generator_plaquetteGenI : so8Generator so8PlaquetteGenI = generator_0 := by
  simpa [so8PlaquetteGenI] using so8Generator_zero

lemma so8Generator_plaquetteGenJ : so8Generator so8PlaquetteGenJ = generator_4 := by
  simpa [so8PlaquetteGenJ] using so8Generator_four

/-- T11 torsion transport on the first plaquette edge only. -/
def hopfShellTorsionPlaquetteEdge (s : HopfShell) (h : s.integrable) : PlaquetteEdge OctonionCarrier :=
  fun k =>
    if k = 0 then so8MatrixVecEnd (HopfShell.torsionMatrix s h) else 1

/-- **Full four-edge** Hopf-shell torsion Wilson plaquette: `T⁴` holonomy. -/
def hopfShellFullTorsionPlaquetteEdge (s : HopfShell) (h : s.integrable) : PlaquetteEdge OctonionCarrier :=
  fun _ => so8MatrixVecEnd (HopfShell.torsionMatrix s h)

def octonionBasis (i : Fin 8) : OctonionCarrier :=
  fun j => if j = i then 1 else 0

theorem so8GeneratorPlaquette_holonomy_apply (i j : Fin 28) (v : OctonionCarrier) :
    (discreteSquareHolonomy (so8GeneratorPlaquetteEdge i j)) v =
      (so8Generator i * so8Generator j).mulVec v := by
  unfold discreteSquareHolonomy so8GeneratorPlaquetteEdge so8GeneratorEdge so8MatrixVecEnd
  simp [Function.End.mul_def, mulVec_mulVec]

theorem so8FullGeneratorPlaquette_holonomy_apply (i j k l : Fin 28) (v : OctonionCarrier) :
    (discreteSquareHolonomy (so8FullGeneratorPlaquetteEdge i j k l)) v =
      (so8Generator i * so8Generator j * so8Generator k * so8Generator l).mulVec v := by
  unfold discreteSquareHolonomy so8FullGeneratorPlaquetteEdge so8GeneratorEdge so8MatrixVecEnd
  simp [Function.End.mul_def, mulVec_mulVec, Fin.sum_univ_four, mul_assoc]

theorem hopfShellTorsionPlaquette_holonomy_apply (s : HopfShell) (h : s.integrable) (v : OctonionCarrier) :
    (discreteSquareHolonomy (hopfShellTorsionPlaquetteEdge s h)) v =
      (HopfShell.torsionMatrix s h).mulVec v := by
  unfold discreteSquareHolonomy hopfShellTorsionPlaquetteEdge so8MatrixVecEnd
  simp [Function.End.mul_def, mulVec_mulVec, Fin.sum_univ_four]

theorem hopfShellFullTorsionPlaquette_holonomy_apply (s : HopfShell) (h : s.integrable) (v : OctonionCarrier) :
    (discreteSquareHolonomy (hopfShellFullTorsionPlaquetteEdge s h)) v =
      ((HopfShell.torsionMatrix s h) ^ 4).mulVec v := by
  unfold discreteSquareHolonomy hopfShellFullTorsionPlaquetteEdge so8MatrixVecEnd
  simp [Function.End.mul_def, mulVec_mulVec, Fin.sum_univ_four, pow_succ, Matrix.mul_assoc]

theorem phaseLiftDelta_mulVec_e1 (c : ℝ) :
    (c • Hqiv.phaseLiftDelta).mulVec (octonionBasis 1) = c • octonionBasis 7 := by
  ext j
  fin_cases j <;>
    simp [octonionBasis, Matrix.mulVec, Matrix.smul_mulVec, dotProduct,
      Hqiv.phaseLiftDelta, Hqiv.phaseLiftDelta_71, Matrix.of_apply]

theorem phaseLiftDelta_mulVec_e7 (c : ℝ) :
    (c • Hqiv.phaseLiftDelta).mulVec (octonionBasis 7) = (-c) • octonionBasis 1 := by
  ext j
  fin_cases j <;>
    simp [octonionBasis, Matrix.mulVec, Matrix.smul_mulVec, dotProduct,
      Hqiv.phaseLiftDelta, Hqiv.phaseLiftDelta_17, Matrix.of_apply]

theorem phaseLiftDelta_sq_mulVec_e1 :
    (Hqiv.phaseLiftDelta * Hqiv.phaseLiftDelta).mulVec (octonionBasis 1) = (-1 : ℝ) • octonionBasis 1 := by
  rw [← Matrix.mulVec_mulVec (octonionBasis 1) Hqiv.phaseLiftDelta Hqiv.phaseLiftDelta]
  have inner : Hqiv.phaseLiftDelta.mulVec (octonionBasis 1) = octonionBasis 7 := by
    simpa [one_smul] using phaseLiftDelta_mulVec_e1 1
  have outer : Hqiv.phaseLiftDelta.mulVec (octonionBasis 7) = (-1 : ℝ) • octonionBasis 1 := by
    simpa [one_smul] using phaseLiftDelta_mulVec_e7 1
  rw [inner, outer]

theorem phaseLiftDelta_pow_four_mulVec_e1 :
    (Hqiv.phaseLiftDelta ^ 4).mulVec (octonionBasis 1) = octonionBasis 1 := by
  have hsq : (Hqiv.phaseLiftDelta ^ 2).mulVec (octonionBasis 1) = (-1 : ℝ) • octonionBasis 1 := by
    simpa [pow_two] using phaseLiftDelta_sq_mulVec_e1
  rw [show Hqiv.phaseLiftDelta ^ 4 = Hqiv.phaseLiftDelta ^ 2 * Hqiv.phaseLiftDelta ^ 2 by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]]
  rw [← Matrix.mulVec_mulVec (octonionBasis 1) (Hqiv.phaseLiftDelta ^ 2) (Hqiv.phaseLiftDelta ^ 2),
    hsq, Matrix.mulVec_smul, hsq]
  simp only [Matrix.mulVec_smul, neg_smul, smul_smul, neg_neg, one_smul]

theorem torsionMatrix_pow_four_mulVec_e1 (s : HopfShell) (h : s.integrable) :
    ((HopfShell.torsionMatrix s h) ^ 4).mulVec (octonionBasis 1) =
      HopfShell.torsionMatrixCoefficient s ^ 4 • octonionBasis 1 := by
  unfold HopfShell.torsionMatrix Hqiv.Algebra.phaseLiftDeltaMatrix
  set c := HopfShell.torsionMatrixCoefficient s
  set T := c • Hqiv.phaseLiftDelta
  have h1 : T.mulVec (octonionBasis 1) = c • octonionBasis 7 := by
    dsimp [T]
    exact phaseLiftDelta_mulVec_e1 c
  have h2 : T.mulVec (octonionBasis 7) = (-c) • octonionBasis 1 := by
    dsimp [T]
    exact phaseLiftDelta_mulVec_e7 c
  have hsq : (T ^ 2).mulVec (octonionBasis 1) = (-c ^ 2) • octonionBasis 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec (octonionBasis 1) T T, h1, Matrix.mulVec_smul, h2,
      smul_smul, neg_smul]
    simp [neg_smul, pow_two]
  have hfour : (T ^ 2 * T ^ 2).mulVec (octonionBasis 1) = c ^ 4 • octonionBasis 1 := by
    rw [← Matrix.mulVec_mulVec (octonionBasis 1) (T ^ 2) (T ^ 2), hsq, Matrix.mulVec_smul, hsq]
    ext j
    fin_cases j <;> simp [octonionBasis]
    ring
  rw [show T ^ 4 = T ^ 2 * T ^ 2 from by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]]
  exact hfour

theorem hopfShellTorsionPlaquette_moves_e1_to_e7 (s : HopfShell) (h : s.integrable) :
    (HopfShell.torsionMatrix s h).mulVec (octonionBasis 1) =
      HopfShell.torsionMatrixCoefficient s • octonionBasis 7 := by
  unfold HopfShell.torsionMatrix
  simpa using phaseLiftDelta_mulVec_e1 (HopfShell.torsionMatrixCoefficient s)

theorem hopfShell_light_torsion_plaquette_nontrivial :
    (discreteSquareHolonomy
        (hopfShellTorsionPlaquetteEdge (mkIntegrable 1 (Or.inl rfl)) (by trivial)))
        (octonionBasis 1) ≠ octonionBasis 1 := by
  rw [hopfShellTorsionPlaquette_holonomy_apply, hopfShellTorsionPlaquette_moves_e1_to_e7]
  apply ne_of_apply_ne (fun v => v 1)
  simp [octonionBasis]

theorem mkIntegrable_one_torsionMatrixCoefficient :
    (mkIntegrable 1 (Or.inl rfl)).torsionMatrixCoefficient = (2 : ℝ) / 5 := by
  dsimp [HopfShell.torsionMatrixCoefficient, HopfShell.curvatureImprintAlpha, mkIntegrable]
  rw [Hqiv.Algebra.phaseLiftCoeff, phi_of_shell_closed_form 1,
    phiTemperatureCoeff_eq_two, alpha_eq_3_5]
  norm_num

theorem hopfShell_light_full_torsion_plaquette_nontrivial :
    (discreteSquareHolonomy
        (hopfShellFullTorsionPlaquetteEdge (mkIntegrable 1 (Or.inl rfl)) (by trivial)))
        (octonionBasis 1) ≠ octonionBasis 1 := by
  rw [hopfShellFullTorsionPlaquette_holonomy_apply, torsionMatrix_pow_four_mulVec_e1,
    mkIntegrable_one_torsionMatrixCoefficient]
  apply ne_of_apply_ne (fun v => v 1)
  norm_num [octonionBasis]

theorem so8Generator04_mulVec_e1_row0_ne :
    (generator_0 * generator_4).mulVec (octonionBasis 1) 0 ≠ 0 := by
  have h01 : (generator_0 * generator_4) 0 1 ≠ 0 := by
    simp only [Matrix.mul_apply, generator_0, generator_4, Matrix.of_apply,
      Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    norm_num (maxSteps := 5000000)
  simpa [Matrix.mulVec, dotProduct, octonionBasis] using h01

theorem so8Generator04_mulVec_e1_row0_ne_comm :
    (generator_0 * generator_4).mulVec (octonionBasis 1) 0 ≠
      (generator_4 * generator_0).mulVec (octonionBasis 1) 0 := by
  have h01 : (generator_0 * generator_4) 0 1 ≠ (generator_4 * generator_0) 0 1 := by
    simp only [Matrix.mul_apply, generator_0, generator_4, Matrix.of_apply,
      Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    norm_num (maxSteps := 5000000)
  simpa [Matrix.mulVec, dotProduct, octonionBasis] using h01

theorem so8GeneratorPlaquette04_nontrivial :
    (discreteSquareHolonomy (so8GeneratorPlaquetteEdge so8PlaquetteGenI so8PlaquetteGenJ))
        (octonionBasis 1) ≠ octonionBasis 1 := by
  rw [so8GeneratorPlaquette_holonomy_apply, so8Generator_plaquetteGenI, so8Generator_plaquetteGenJ]
  apply ne_of_apply_ne (fun v => v 0)
  intro heq
  exact so8Generator04_mulVec_e1_row0_ne (by simpa [octonionBasis] using heq)

theorem so8Generator_zero_mul_four_ne_one :
    so8Generator so8PlaquetteGenI * so8Generator so8PlaquetteGenJ ≠ (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [so8Generator_plaquetteGenI, so8Generator_plaquetteGenJ]
  intro h
  have h00 := congrArg (fun M => M 0 0) h
  simp only [Matrix.one_apply, Matrix.mul_apply, generator_0, generator_4, Matrix.of_apply,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h00
  norm_num (maxSteps := 5000000) at h00

theorem so8Generator_zero_mul_four_ne_comm :
    so8Generator so8PlaquetteGenI * so8Generator so8PlaquetteGenJ ≠
      so8Generator so8PlaquetteGenJ * so8Generator so8PlaquetteGenI := by
  rw [so8Generator_plaquetteGenI, so8Generator_plaquetteGenJ]
  intro h
  have h01 := congrArg (fun M => M 0 1) h
  simp only [Matrix.mul_apply, generator_0, generator_4, Matrix.of_apply,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h01
  norm_num (maxSteps := 5000000) at h01

/-- Discharged SO(8) plaquette layer (generator chart + Hopf-shell torsion Wilson line). -/
structure SO8PlaquetteHolonomyDischarged : Prop where
  generator_holonomy :
    ∀ (i j : Fin 28) (v : OctonionCarrier),
      (discreteSquareHolonomy (so8GeneratorPlaquetteEdge i j)) v =
        (so8Generator i * so8Generator j).mulVec v
  full_four_edge_holonomy :
    ∀ (i j k l : Fin 28) (v : OctonionCarrier),
      (discreteSquareHolonomy (so8FullGeneratorPlaquetteEdge i j k l)) v =
        (so8Generator i * so8Generator j * so8Generator k * so8Generator l).mulVec v
  torsion_holonomy :
    ∀ (s : HopfShell) (h : s.integrable) (v : OctonionCarrier),
      (discreteSquareHolonomy (hopfShellTorsionPlaquetteEdge s h)) v =
        (HopfShell.torsionMatrix s h).mulVec v
  full_torsion_holonomy :
    ∀ (s : HopfShell) (h : s.integrable) (v : OctonionCarrier),
      (discreteSquareHolonomy (hopfShellFullTorsionPlaquetteEdge s h)) v =
        ((HopfShell.torsionMatrix s h) ^ 4).mulVec v
  light_shell_nontrivial :
    (discreteSquareHolonomy
        (hopfShellTorsionPlaquetteEdge (mkIntegrable 1 (Or.inl rfl)) (by trivial)))
        (octonionBasis 1) ≠ octonionBasis 1
  light_shell_full_torsion_nontrivial :
    (discreteSquareHolonomy
        (hopfShellFullTorsionPlaquetteEdge (mkIntegrable 1 (Or.inl rfl)) (by trivial)))
        (octonionBasis 1) ≠ octonionBasis 1
  generator_pair04_product_nontrivial :
    so8Generator so8PlaquetteGenI * so8Generator so8PlaquetteGenJ ≠ (1 : Matrix (Fin 8) (Fin 8) ℝ)
  generator_pair04_noncommuting :
    so8Generator so8PlaquetteGenI * so8Generator so8PlaquetteGenJ ≠
      so8Generator so8PlaquetteGenJ * so8Generator so8PlaquetteGenI
  generator_plaquette04_nontrivial :
    (discreteSquareHolonomy (so8GeneratorPlaquetteEdge so8PlaquetteGenI so8PlaquetteGenJ))
        (octonionBasis 1) ≠ octonionBasis 1

theorem so8PlaquetteHolonomyDischarged_holds : SO8PlaquetteHolonomyDischarged where
  generator_holonomy := so8GeneratorPlaquette_holonomy_apply
  full_four_edge_holonomy := so8FullGeneratorPlaquette_holonomy_apply
  torsion_holonomy := hopfShellTorsionPlaquette_holonomy_apply
  full_torsion_holonomy := hopfShellFullTorsionPlaquette_holonomy_apply
  light_shell_nontrivial := hopfShell_light_torsion_plaquette_nontrivial
  light_shell_full_torsion_nontrivial := hopfShell_light_full_torsion_plaquette_nontrivial
  generator_pair04_product_nontrivial := so8Generator_zero_mul_four_ne_one
  generator_pair04_noncommuting := so8Generator_zero_mul_four_ne_comm
  generator_plaquette04_nontrivial := so8GeneratorPlaquette04_nontrivial

end

end Hqiv.Physics
