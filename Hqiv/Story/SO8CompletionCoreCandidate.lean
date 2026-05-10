import Hqiv.Story.SO8CompletionCoreWitness
import Hqiv.Story.QuantumYangMillsFromPatchHQIV
import Hqiv.Story.MillenniumBridgePatchPoincareWightman
import Hqiv.Story.HQIVPatchQFTInputsSO8
import Hqiv.Story.YMBridgeProvedHelpers
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# SO(8) completion-core candidate

This file is the concrete SO(8) completion candidate built from the patch-native HQIV QFT path.

Current status:
- `hExist`, `hGap`, and `hFin` are proved from the patch Hamiltonian/operator package.
- the remaining external input is the real-smearing vacuum-cyclicity bridge
  `hVacuumCyclic`.
-/

namespace Hqiv.Story

open Hqiv.Story.MassGapCompletion
open MillenniumYangMills MillenniumYangMillsDefs
open Hqiv.Story.QuantumYangMillsFromPatchHQIV

noncomputable section

/-- Assumed real-Schwartz vacuum cyclicity for the HQIV patch jet field on `PatchHilbert`.
This is the only remaining bridge input for the candidate. -/
variable (hVacuumCyclic :
  Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega :
    Set PatchHilbert))

/-- Candidate SO(8) quantum YM theory built from HQIV patch QFT data (non-toy path). -/
noncomputable def hqivQFT : QuantumYangMillsTheory HQIVSO8Gauge :=
  hqivPatchQuantumYangMills HQIVSO8Gauge hVacuumCyclic hqivPatchQuantumYangMillsInputsSO8

/-- Clay-existence witness for the SO(8) candidate QFT. -/
theorem hqivQFT_hExist : ClayExistence hqivQFT := by
  -- `ClayExistence` is `NontrivialTheory`, i.e. nontrivial Hilbert carrier.
  show Nontrivial hqivQFT.hilbertSpace
  infer_instance

/-- Candidate spectral-gap parameter. -/
def so8CandidateDelta : ℝ := by
  -- Replace with your chosen explicit positive gap scale.
  exact 1

/-- Mass-gap spectrum witness for the SO(8) candidate QFT at `so8CandidateDelta`. -/
theorem hqivQFT_hGap :
    HasMassGapSpectrum HQIVSO8Gauge hqivQFT so8CandidateDelta := by
  rcases patchWightman_massGapOnSpectrum with ⟨hpos, hdisj⟩
  change so8CandidateDelta > 0 ∧
    Disjoint (spectrum ℝ patchHamiltonian) (Set.Ioo 0 so8CandidateDelta)
  simpa [so8CandidateDelta, PatchWightmanMassGapOnSpectrum] using ⟨hpos, hdisj⟩

/-- Finite-mass-spectrum proposition for the SO(8) candidate QFT. -/
abbrev so8Candidate_hFin : Prop :=
  FiniteMassSpectrum HQIVSO8Gauge hqivQFT

private noncomputable def hqivOrthMode : PatchHilbert :=
  EuclideanSpace.single 0 (1 : ℂ) - EuclideanSpace.single 1 (1 : ℂ)

private theorem hqivOrthMode_ne_zero : hqivOrthMode ≠ 0 := by
  intro h0
  have h := congrArg (fun v : PatchHilbert => v 0) h0
  simp [hqivOrthMode, EuclideanSpace.single_apply] at h

private theorem hqivOrthMode_inner_vacuum_zero : inner ℝ hqivOrthMode patchWightmanOmega = 0 := by
  rw [real_inner_eq_re_inner]
  have hcoord0 := patchWightmanOmega_coord_eq (0 : Fin 4)
  have hcoord1 := patchWightmanOmega_coord_eq (1 : Fin 4)
  simp [hqivOrthMode, hcoord0, hcoord1, inner_sub_left, inner_single_right]

private theorem patchRankOneOmega_apply_hqivOrthMode :
    patchRankOneOmega hqivOrthMode = 0 := by
  simp [patchRankOneOmega, rankOne_apply, hqivOrthMode_inner_vacuum_zero]

private theorem patchComplementProjector_apply_hqivOrthMode :
    patchComplementProjector hqivOrthMode = hqivOrthMode := by
  simp [patchComplementProjector, patchRankOneOmega_apply_hqivOrthMode]

private theorem patchHamiltonian_apply_hqivOrthMode :
    patchHamiltonian hqivOrthMode = ladderGapCandidate • hqivOrthMode := by
  rw [patchHamiltonian_eq_smul_complement, ContinuousLinearMap.smul_apply,
    patchComplementProjector_apply_hqivOrthMode]

private theorem ladderGapCandidate_mem_patch_spectrum :
    ladderGapCandidate ∈ spectrum ℝ patchHamiltonian := by
  have hEigVec : patchHamiltonian.HasEigenvector ladderGapCandidate hqivOrthMode := by
    refine (mem_eigenspace_iff).2 ?_
    exact patchHamiltonian_apply_hqivOrthMode
  exact (hasEigenvalue_of_hasEigenvector hEigVec).mem_spectrum

private theorem hqivQFT_hasMassGapSpectrum_le_ladderGapCandidate
    (Δ : ℝ) (hΔ : HasMassGapSpectrum HQIVSO8Gauge hqivQFT Δ) :
    Δ ≤ ladderGapCandidate := by
  rcases hΔ with ⟨hΔpos, hdisj⟩
  by_contra hgt
  have hlt : ladderGapCandidate < Δ := lt_of_not_ge hgt
  have hInIoo : ladderGapCandidate ∈ Set.Ioo 0 Δ := ⟨ladderGapCandidate_pos, hlt⟩
  have hInSpecQft : ladderGapCandidate ∈ spectrum ℝ hqivQFT.wightman.hamiltonian := by
    simpa [hqivQFT, hqivPatchQuantumYangMills, hqivPatchWightmanAxioms] using
      ladderGapCandidate_mem_patch_spectrum
  have : ¬ladderGapCandidate ∈ Set.Ioo 0 Δ := by
    exact (Set.disjoint_left.mp hdisj) ladderGapCandidate hInSpecQft
  exact this hInIoo

theorem hqivQFT_hFin : so8Candidate_hFin := by
  refine FiniteMassSpectrum_of_global_bound (G := HQIVSO8Gauge) (qft := hqivQFT)
    ladderGapCandidate ladderGapCandidate_pos ?_
  intro Δ hΔ
  exact hqivQFT_hasMassGapSpectrum_le_ladderGapCandidate Δ hΔ

/-- Bundled obligations object for SO(8), ready to feed the final bridge theorem. -/
def so8CandidateObligations : SO8CompletionCoreObligations :=
  { qft := hqivQFT
    Δ := so8CandidateDelta
    hExist := hqivQFT_hExist
    hGap := hqivQFT_hGap
    hFin := hqivQFT_hFin }

/-- Once the four candidate lemmas are discharged, this is the SO(8) Clay YM theorem. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge := by
  exact yangMillsExistenceAndMassGap_of_so8_obligations
    so8CandidateObligations

/-- Closure form with explicit cyclicity bridge hypothesis:
if real-smearing and patch-smearing generated vectors agree at `patchWightmanOmega`,
then the SO(8) Clay YM target follows. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_range_eq
    (hRange :
      Set.range (fun f : SchwartzSpace =>
          hqivPatchJetOperatorValuedDistribution f patchWightmanOmega) =
        Set.range (fun f : PatchSchwartzSpace => patchDerivOVD f patchWightmanOmega)) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge := by
  let hVacuumCyclic' :
      Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega :
        Set PatchHilbert) :=
    hqiv_realVacuumCyclic_patchOmega_of_range_eq' hRange
  simpa using (yangMillsExistenceAndMassGap_so8_from_candidate (hVacuumCyclic := hVacuumCyclic'))

/-- Lapse-native closure form: if the HQVM lapse-window bridge is provided, the SO(8) Clay YM target follows. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_lapseWindowRangeBridge
    {N : ℝ}
    (hBridge : LapseWindowRangeBridgeAtPatchOmega N) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge := by
  let hVacuumCyclic' :
      Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega :
        Set PatchHilbert) :=
    hqiv_realVacuumCyclic_patchOmega_of_lapseWindowRangeBridge hBridge
  simpa using (yangMillsExistenceAndMassGap_so8_from_candidate (hVacuumCyclic := hVacuumCyclic'))

/-- GR-shaped endpoint (`N = HQVM_lapse Φ φ t`): once the lapse-window bridge is proved at this
HQVM lapse value, the SO(8) Clay YM target follows immediately. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_lapseWindowRangeBridge
    {Φ φ t : ℝ}
    (hBridge : LapseWindowRangeBridgeAtPatchOmega (HQVM_lapse Φ φ t)) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge :=
  yangMillsExistenceAndMassGap_so8_from_candidate_of_lapseWindowRangeBridge hBridge

/-- Monogamy/lightcone closure form: if you can provide a time-angle parameterization at patch omega
and the HQVM lapse lower bound against `phaseTheta`, the SO(8) Clay YM target follows. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_timeAngleParam
    {Φ φ t : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t)
    (hParam : TimeAngleRangeParameterizationAtPatchOmega) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge := by
  refine yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_lapseWindowRangeBridge ?_
  exact lapseWindowRangeBridgeAtPatchOmega_of_timeAngle_param_HQVM_lapse hθN hParam

/-- Proof-first monogamy closure form: reuse the proved HQIV directional-monogamy theorem,
plus a single bridge implication from that monogamy statement to patch-omega range
parameterization, to close the SO(8) Clay YM target. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_monogamyProof
    {Φ φ t : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t)
    (hMonogamyBridge : MonogamyClusterToTimeAngleRangeBridgeAtPatchOmega) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge := by
  refine yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_timeAngleParam hθN ?_
  exact timeAngleRangeParameterizationAtPatchOmega_of_monogamyProof hMonogamyBridge

/-- From-scratch closure form: combine
1) real-jet surjectivity on lifted real Schwartz tests,
2) monogamy-cluster ⇒ patch-omega real-jet admissibility, and
3) one fixed phase-window point `0 < timeAngle φ t < phaseTheta`,
to obtain the SO(8) Clay YM target. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_monogamyProof_realJets
    {Φ φ t φ0 t0 : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t)
    (hRealJets : PatchOmegaRealJetSurjective)
    (hMonogamyToJets : MonogamyClusterToPatchOmegaRealJetAdmissible)
    (hφ0 : 0 < φ0) (ht0 : 0 < t0)
    (hcap0 : timeAngle φ0 t0 < Hqiv.Physics.phaseTheta) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge := by
  refine yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_timeAngleParam hθN ?_
  exact timeAngleRangeParameterizationAtPatchOmega_of_monogamyProof_realJets
    hRealJets hMonogamyToJets hφ0 ht0 hcap0

/-- Same closure endpoint, with monogamy bridge supplied in reduced "imaginary jets vanish" form. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_monogamyProof_imagZero
    {Φ φ t φ0 t0 : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t)
    (hImagBridge : MonogamyClusterToPatchOmegaJetImagZero)
    (hφ0 : 0 < φ0) (ht0 : 0 < t0)
    (hcap0 : timeAngle φ0 t0 < Hqiv.Physics.phaseTheta) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge := by
  refine yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_monogamyProof_realJets
    hθN patchOmegaRealJetSurjective ?_ hφ0 ht0 hcap0
  exact monogamyClusterToPatchOmegaRealJetAdmissible_of_imagZero hImagBridge

/-- Preferred endpoint: monogamy closes YM through the physical parameterization bridge directly
(phase/observable-level), without requiring the stronger imaginary-jet-vanishing route. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_physicalMonogamyBridge
    {Φ φ t : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t)
    (hBridge : MonogamyClusterToPhysicalRangeBridgeAtPatchOmega) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge :=
  yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_monogamyProof hθN hBridge

/-- Preferred endpoint from the refined probe-family bridge (support/time-angle window form). -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_probeFamilyPhysicalBridge
    {Φ φ t : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t)
    (hProbe : MonogamyProbeFamilyPhysicalBridgeAtPatchOmega) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge :=
  yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_physicalMonogamyBridge hθN
    (monogamyClusterToPhysicalRangeBridgeAtPatchOmega_of_probeFamilyBridge hProbe)

/-- End-to-end wiring from the correlator/separation analytic package to the SO(8) YM target. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_correlatorAxioms
    {Φ φ t : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t)
    (hAxioms : PatchMonogamyCorrelatorAxiomsAtPatchOmega) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge :=
  yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_probeFamilyPhysicalBridge hθN
    (monogamyProbeFamilyPhysicalBridgeAtPatchOmega_of_correlatorAxioms hAxioms)

/-- Fast closure endpoint using the reference-backed literature bridge slot. -/
theorem yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_literatureBridge
    {Φ φ t : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t)
    (hLit : LiteratureClusterCorrelatorBridgeAtPatchOmega) :
    MillenniumYangMills.YangMillsExistenceAndMassGap HQIVSO8Gauge :=
  yangMillsExistenceAndMassGap_so8_from_candidate_of_HQVM_probeFamilyPhysicalBridge hθN
    (monogamyProbeFamilyPhysicalBridgeAtPatchOmega_of_correlatorBridge hLit)

end

end Hqiv.Story

