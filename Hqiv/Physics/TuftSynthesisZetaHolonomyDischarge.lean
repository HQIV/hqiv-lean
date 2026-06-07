import Hqiv.Physics.ActionHolonomyGlue
import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.DivisionAlgebraZetaScaffold
import Hqiv.Physics.FanoSectorSpectralMassEmergence
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.ReadoutGaugeSeed
import Hqiv.Physics.WeakHiggsFromOMaxwellScaffold
import Hqiv.Algebra.WeakInComplexStructure
import Hqiv.SO8Closure
import Hqiv.Topology.DiscretePhaseEvolution
import Hqiv.Topology.HopfShellComplex

/-!
# TUFT synthesis: zeta subleading + holonomy upgrade discharge

The TUFT+SM synthesis paper lists **subleading zeta terms** and **non-abelian holonomy**
as open relative to Nielsen's external smooth contact-manifold programme.  In HQIV the
honest geometry is already **continuous Lie data on the octonion light-cone carrier**:

* **SO(8)** — 28 antisymmetric generators, bracket closure, linear independence
  (`SO8Closure.so8_closure_theorem` / `GeneratorsLieClosure`).
* **G₂ + Δ chart** — `phaseLiftDelta` antisymmetric in \(\mathfrak{so}(8)\), preferred
  \((e_1,e_7)\) U(1) plane (`DiscretePhaseEvolution`).
* **Hopf-shell torsion** — skew 8×8 matrices on the octonion carrier, supplying Δ-action
  into `SO8AdmissibleHolonomy` (`HopfShellComplex.t11_torsion_supplies_delta_in_so8_admissible_holonomy`).

This module **discharges** the synthesis obligations by wiring those witnesses together with:

* **Zeta:** T8 leading × T11 torsion subleading (`FanoSectorSpectralMassEmergence`), lattice
  amplitude match at `δ = 0` (`GlobalDetuning` / `DivisionAlgebraZetaScaffold`).
* **Holonomy:** Fano row splits + T10 phase matrix; O–Maxwell cyclic plaquette flatness in the
  abelian ℝ chart; SU(2)/SU(3) weak/colour commutator certificates; **SO(8) light-cone holonomy**
  on integrable Hopf shells.

**Still not claimed:** Nielsen-style external smooth principal bundles, contact-manifold
self-adjointness, and path-integral measure choice — not because HQIV lacks a Lie algebra,
but because those theorems are not reproved on a separate \(C^\infty\) carrier.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Topology
open Hqiv.Algebra
open Complex

noncomputable section

/-! ## Higher-order zeta at the patch layer -/

/-- Lattice zeta leading amplitude `(effCorrected 0 m)^{-s}` matches the T8 sector-determinant body. -/
theorem patchLatticeZetaLeading_eq_tuftSectorDetLeading
    (s : HopfShell) (h : s.integrable) (m : ℕ) (sC : ℂ) :
    zetaR1_latticeTerm 0 sC m =
      ((tuftSectorZetaDet s h).leadingTerm m : ℂ) ^ (-sC) := by
  rw [zetaR1_latticeTerm_eq]
  rw [effCorrected_zero_eq_detunedShellSurface]
  rw [tuftSectorZetaDet_leading_eq_detunedShellSurface]

theorem torsionMatrixCoefficient_mkIntegrable_one :
    (mkIntegrable 1 (Or.inl rfl)).torsionMatrixCoefficient = (2 : ℝ) / 5 := by
  simpa [hopfShellForGeneration_zero] using hopfShellForGeneration_torsionCoeff_light

theorem torsionMatrixCoefficient_mkIntegrable_two :
    (mkIntegrable 2 (Or.inr (Or.inl rfl))).torsionMatrixCoefficient = (3 : ℝ) / 5 := by
  simpa [hopfShellForGeneration_one] using hopfShellForGeneration_torsionCoeff_middle

theorem torsionMatrixCoefficient_hopfShellWinding_one :
    (hopfShellOfGenerationWinding 1 (Or.inl rfl)).torsionMatrixCoefficient = (2 : ℝ) / 5 := by
  unfold hopfShellOfGenerationWinding
  exact torsionMatrixCoefficient_mkIntegrable_one

theorem torsionMatrixCoefficient_hopfShellWinding_two :
    (hopfShellOfGenerationWinding 2 (Or.inr (Or.inl rfl))).torsionMatrixCoefficient =
      (3 : ℝ) / 5 := by
  unfold hopfShellOfGenerationWinding
  exact torsionMatrixCoefficient_mkIntegrable_two

theorem tuftSectorZetaSubleadingCoeff_two_eq_raySinger :
    tuftSectorZetaSubleadingCoeff 2 = tuftRaySingerSubleadingCoeff := by
  unfold tuftSectorZetaSubleadingCoeff
  simp

theorem hopfShellT8TorsionSubleading_winding_two_ne_one :
    hopfShellT8TorsionSubleading (hopfShellOfGenerationWinding 2 (Or.inr (Or.inl rfl))) ≠ 1 := by
  unfold hopfShellT8TorsionSubleading hopfShellOfGenerationWinding mkIntegrable
  simp [HopfShell.torsionMatrixCoefficient, HopfShell.curvatureImprintAlpha,
    alpha_eq_3_5, Algebra.phaseLiftCoeff, phi_of_shell_closed_form, phiTemperatureCoeff_eq_two,
    t12_heavy_torsion_coeff_eq_four_fifths, tuftSectorZetaSubleadingCoeff_two_eq_raySinger,
    tuftRaySingerSubleadingCoeff]
  intro h
  linarith

theorem hopfShellT8TorsionSubleading_winding_one_ne_one :
    hopfShellT8TorsionSubleading (hopfShellOfGenerationWinding 1 (Or.inl rfl)) ≠ 1 := by
  unfold hopfShellT8TorsionSubleading hopfShellOfGenerationWinding mkIntegrable
  simp [HopfShell.torsionMatrixCoefficient, HopfShell.curvatureImprintAlpha,
    alpha_eq_3_5, Algebra.phaseLiftCoeff, phi_of_shell_closed_form, phiTemperatureCoeff_eq_two,
    t12_heavy_torsion_coeff_eq_four_fifths, tuftSectorZetaSubleadingCoeff,
    tuftFiberSectorMultiplicity, gamma_eq_2_5]
  norm_num

theorem tuftLeptonT8GenerationFactor_mu_ne_one :
    tuftLeptonT8GenerationFactor 2 (Or.inr (Or.inl rfl)) ≠ 1 :=
  hopfShellT8TorsionSubleading_winding_two_ne_one

theorem tuftLeptonT8GenerationFactor_electron_ne_one :
    tuftLeptonT8GenerationFactor 1 (Or.inl rfl) ≠ 1 :=
  hopfShellT8TorsionSubleading_winding_one_ne_one

theorem tuftLeptonGeometricScalarT8_mu_ne_leadingOnly :
    tuftLeptonGeometricScalarT8 2 (Or.inr (Or.inl rfl)) ≠ tuftLeptonGeometricScalar 2 := by
  intro h
  have hne := tuftLeptonT8GenerationFactor_mu_ne_one
  unfold tuftLeptonGeometricScalarT8 at h
  rw [tuftLeptonT8GenerationFactor_heavy_eq_one] at h
  field_simp [ne_of_gt (tuftLeptonGeometricScalar_pos 2)] at h
  exact hne h

theorem tuftLeptonGeometricScalarT8_electron_ne_leadingOnly :
    tuftLeptonGeometricScalarT8 1 (Or.inl rfl) ≠ tuftLeptonGeometricScalar 1 := by
  intro h
  have hne := tuftLeptonT8GenerationFactor_electron_ne_one
  unfold tuftLeptonGeometricScalarT8 at h
  rw [tuftLeptonT8GenerationFactor_heavy_eq_one] at h
  field_simp [ne_of_gt (tuftLeptonGeometricScalar_pos 1)] at h
  exact hne h

/-- Patch discharge of TUFT synthesis **subleading zeta** (T8 + T11 on Hopf shells). -/
structure PatchSubleadingZetaDischarged : Prop where
  full_witness : TuftSectorZetaDetFullWitness
  lattice_leading_matches_det :
    ∀ (s : HopfShell) (h : s.integrable) (m : ℕ) (sC : ℂ),
      zetaR1_latticeTerm 0 sC m =
        ((tuftSectorZetaDet s h).leadingTerm m : ℂ) ^ (-sC)
  mu_subleading_required :
    tuftLeptonGeometricScalarT8 2 (Or.inr (Or.inl rfl)) ≠ tuftLeptonGeometricScalar 2
  electron_subleading_required :
    tuftLeptonGeometricScalarT8 1 (Or.inl rfl) ≠ tuftLeptonGeometricScalar 1
  lattice_deltaE_summable :
    ∀ (φ t : ℝ) (sC : ℂ),
      (∀ m : ℕ, RindlerDenDeltaPos 0 m) → 1 < sC.re →
        Summable (zetaR1_latticeTerm_deltaE 0 φ t sC)

theorem patchSubleadingZetaDischarged_holds : PatchSubleadingZetaDischarged where
  full_witness := defaultTuftSectorZetaDetFullWitness
  lattice_leading_matches_det := patchLatticeZetaLeading_eq_tuftSectorDetLeading
  mu_subleading_required := tuftLeptonGeometricScalarT8_mu_ne_leadingOnly
  electron_subleading_required := tuftLeptonGeometricScalarT8_electron_ne_leadingOnly
  lattice_deltaE_summable := fun φ t sC hden hs =>
    zetaR1_latticeTerm_deltaE_summable_of_re_gt_one 0 φ t sC (by norm_num) hden hs

/-! ## Holonomy upgrade: Fano rows + light-cone SO(8) -/

/-- SO(8) Lie algebra on the octonion light-cone carrier (28 generators, bracket closure). -/
structure LightconeSO8HolonomyDischarged : Prop where
  so8_closure :
    (∀ k : Fin 28, so8Generator k + (so8Generator k)ᵀ = 0) ∧
      (∀ i j : Fin 28, ∃ f : Fin 28 → ℝ,
        lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k) ∧
      LinearIndependent ℝ (fun k : Fin 28 => so8Generator k)
  delta_antisymmetric_in_so8 : phaseLiftDelta + phaseLiftDeltaᵀ = 0
  delta_u1_plane :
    phaseLiftDelta 1 7 = -1 ∧ phaseLiftDelta 7 1 = 1
  triality_three_eight_dim_slots : Fintype.card Algebra.So8RepIndex = 3
  shell_torsion_skew :
    ∀ (s : HopfShell) (h : s.integrable),
      HopfShell.torsionMatrix s h + (HopfShell.torsionMatrix s h)ᵀ = 0
  hopf_shell_so8_admissible :
    ∀ (s : HopfShell) (h : s.integrable),
      ∃ hol : SO8AdmissibleHolonomy (s.toDiscrete3Complex_integrable h),
        hol.fields_g2_delta_recoverable ∧
          hol.delta_resolves_pinched_links ∧
          hol.triality_three_slots

theorem lightconeSO8HolonomyDischarged_holds : LightconeSO8HolonomyDischarged where
  so8_closure := so8_closure_theorem
  delta_antisymmetric_in_so8 := delta_antisymmetric
  delta_u1_plane := preferred_delta_u1_plane
  triality_three_eight_dim_slots := so8_triality_three_slots_default
  shell_torsion_skew := fun s h => HopfShell.torsionMatrix_skew s h
  hopf_shell_so8_admissible := fun s h =>
    HopfShell.t11_torsion_supplies_delta_in_so8_admissible_holonomy s h

theorem weakPauliPlus_mul_ne_comm_weakPauliMinus :
    weakPauliPlus * weakPauliMinus ≠ weakPauliMinus * weakPauliPlus := by
  intro h
  have hz : weakPauliZ3 ≠ 0 := by
    intro hz0
    have h00 := congrArg (fun M => M 0 0) hz0
    simp [weakPauliZ3, Matrix.of_apply] at h00
  have hc := weakPauli_ladder_comm
  unfold lieBracketMat₂ at hc
  rw [show weakPauliPlus * weakPauliMinus - weakPauliMinus * weakPauliPlus = 0 from by rw [h, sub_self]] at hc
  exact hz hc.symm

/-- Holonomy discharge: Fano/T10 readout + weak/colour charts + light-cone SO(8). -/
structure PatchHolonomyUpgradeDischarged : Prop where
  lightcone_so8 : LightconeSO8HolonomyDischarged
  admissible_generation_cycle : generationVerticesFormAdmissibleCycle
  abelian_cyclic_plaquette_flat :
    ∀ (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8),
      discreteSquareHolonomy (fun i => linearEnd (F_from_A A a i (i + 1))) = 1
  readout_seed_cycle_flat :
    ∀ (ω θ : ℝ) (a : Fin 8),
      discreteSquareHolonomy
          (fun i => linearEnd (F_from_A (seedPotentialMinimalCycle ω θ) a i (i + 1))) = 1
  nonabelian_su2_chart : weakHiggsNonAbelianLieCertified
  su2_matrix_transport_nonabelian : weakPauliPlus * weakPauliMinus ≠ weakPauliMinus * weakPauliPlus
  t10_heavy_to_middle : assembleT10MixingPhaseMatrix.heavyToMiddle = 2
  t10_middle_to_light : assembleT10MixingPhaseMatrix.middleToLight = 3

theorem patchHolonomyUpgradeDischarged_holds : PatchHolonomyUpgradeDischarged where
  lightcone_so8 := lightconeSO8HolonomyDischarged_holds
  admissible_generation_cycle := the_three_generation_fano_vertices_form_admissible_cycle
  abelian_cyclic_plaquette_flat := discreteSquareHolonomy_F_cyclic_eq_one
  readout_seed_cycle_flat := fun ω θ a =>
    seedPotentialMinimalCycle_discrete_holonomy_one ω θ a
  nonabelian_su2_chart := weakHiggsNonAbelianLieCertified_holds
  su2_matrix_transport_nonabelian := weakPauliPlus_mul_ne_comm_weakPauliMinus
  t10_heavy_to_middle := assembleT10MixingPhaseMatrix_heavyToMiddle_eq
  t10_middle_to_light := assembleT10MixingPhaseMatrix_middleToLight_eq

/-- Combined TUFT synthesis discharge (subleading zeta + holonomy on light-cone SO(8)). -/
structure TuftSynthesisZetaHolonomyDischarged : Prop where
  subleading_zeta : PatchSubleadingZetaDischarged
  holonomy_upgrade : PatchHolonomyUpgradeDischarged

theorem tuftSynthesisZetaHolonomyDischarged_holds : TuftSynthesisZetaHolonomyDischarged where
  subleading_zeta := patchSubleadingZetaDischarged_holds
  holonomy_upgrade := patchHolonomyUpgradeDischarged_holds

end

end Hqiv.Physics
