import Hqiv.Story.HQIVQFTLieAlgebraFeed
import Hqiv.Story.SchwartzRealToComplexLift
import Hqiv.Story.MillenniumBridgePatchPoincareWightman
import Hqiv.Story.QuantumYangMillsFromPoincareToy
import Hqiv.Physics.ComptonIRWindow
import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.LightConeMaxwellQFTBridge
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# HQIV patch layer ↔ Dojo `QuantumYangMillsTheory` promotion slot

The **native HQIV continuum smearing** for the patch jet operator-valued distribution is
`patchDerivOVD` on `PatchSchwartzSpace = 𝓢(ℝ⁴, ℂ)` (`MillenniumBridgePatchPoincareWightman`), with
a nontrivial ladder-scaled Hamiltonian on `PatchHilbert = LatticeHilbert 4`.

The Clay / Lean Dojo `QuantumYangMillsTheory` record still insists on **real** Schwartz smearing
`SchwartzSpace = 𝓢(ℝ⁴, ℝ)` and `WightmanAxioms` for that real field. Transporting the full patch
Wightman package across this real/complex smearing mismatch (in particular **W4 cyclicity**) is a
separate mathematical step; this module therefore **promotes the HQIV patch jet OVD** as explicit
data and keeps the **existing** complete Dojo interface witness from
`QuantumYangMillsFromPoincareToy` as the current inhabitation of `QuantumYangMillsTheory G`.

Use `hqivPatchJetOperatorValuedDistribution` when stating alignment between patch jets and any
Dojo `field_operators` layer; use `hqivInterfaceQuantumYangMills` for the certified `QuantumYangMillsTheory G`.

**Octonion / G₂ ∪ Δ → matrix 𝔰𝔬(8) feed (lightweight):** this file imports
`Hqiv.Story.HQIVQFTLieAlgebraFeed` so the QFT promotion line can cite skew-adjoint `so8Generator` /
`phaseLiftDelta` facts and the `28`-dimensional target **without** pulling `SO8ClosureInterface` /
`GeneratorsLieClosure`. The full bracket-span + linear-independence certificate remains in
`OctonionLieDOF` (heavy `HQIVSO8Closure` build).

**Patch Hamiltonian ladder scale:** `MillenniumBridgePatchPoincareWightman` imports
`LadderGapCandidateWell` (not `SketchesConsumedLadderWell`) so `Chapter08_ClayMillennium` can import
this module without an import cycle through `MassGapCompletionBundle`.

**Step 4 (Schwartz / patch jet ↔ Wightman spine — partial):** `SchwartzRealToComplexLift` gives
`schwartzRealToComplex_spacelikeSeparation`, so the real-smeared patch jet satisfies
`hqivPatchJet_operator_locality` and `hqivPatchJet_operator_patchCovariance` (trivial patch test action).
Still open for a full Dojo `QuantumYangMillsTheory` built on `PatchHilbert`: **W4 cyclicity** for
`fieldGeneratedSubmodule` built from `hqivPatchJetOperatorValuedDistribution`. A concrete
**Hilbert / vacuum bridge** to the toy spine is `PatchToWightmanToyHilbertBridge` (`patchToWightmanToyHilbertBridge`,
`patchToWightmanToyHilbertIncl_patchVacuum`).
-/

namespace Hqiv.Story

open MillenniumYangMillsDefs
open Filter
open scoped Topology

namespace QuantumYangMillsFromPatchHQIV

/-- HQIV patch jet field, fed by **real** Clay Schwartz tests via `schwartzRealToComplex`. -/
noncomputable def hqivPatchJetOperatorValuedDistribution :
    OperatorValuedDistribution PatchHilbert :=
  fun f => patchDerivOVD (schwartzRealToComplex f)

theorem hqivPatchJetOperatorValuedDistribution_apply (f : SchwartzSpace) :
    hqivPatchJetOperatorValuedDistribution f = patchDerivOVD (schwartzRealToComplex f) :=
  rfl

/-- **W5-style locality** for the real-smeared patch jet: inherited from `patchDeriv_locality` on
`PatchSchwartzSpace` via `schwartzRealToComplex_spacelikeSeparation`. -/
theorem hqivPatchJet_operator_locality (f g : SchwartzSpace)
    (h : ∀ (x y : Spacetime), MinkowskiMetric (x - y) (x - y) < 0 → f.toFun x = 0 ∨ g.toFun y = 0) :
    hqivPatchJetOperatorValuedDistribution f ∘L hqivPatchJetOperatorValuedDistribution g =
      hqivPatchJetOperatorValuedDistribution g ∘L hqivPatchJetOperatorValuedDistribution f := by
  simpa [hqivPatchJetOperatorValuedDistribution] using
    patchDeriv_locality (schwartzRealToComplex f) (schwartzRealToComplex g)
      (schwartzRealToComplex_spacelikeSeparation f g h)

/-- **Covariance** with the patch trivial Poincaré test action: since `patchMillenniumPoincareTrivialTestAction`
fixes every complex test, this is the same identity as `patchDeriv_covariance` specialized to
`schwartzRealToComplex f`. -/
theorem hqivPatchJet_operator_patchCovariance (g : PatchMillenniumPoincareGroup) (f : SchwartzSpace) :
    hqivPatchJetOperatorValuedDistribution f =
      conjugateOperator (patchMillenniumPoincareTrivialUnitaryRep g)
        (hqivPatchJetOperatorValuedDistribution f) := by
  rw [hqivPatchJetOperatorValuedDistribution]
  conv_lhs =>
    rw [← congrArg patchDerivOVD
      (show patchMillenniumPoincareTrivialTestAction g (schwartzRealToComplex f) = schwartzRealToComplex f from rfl)]
  exact patchDeriv_covariance g (schwartzRealToComplex f)

/-! ### Real-vs-complex smearing transfer (domain-aware) -/

/-- Domain-aware base fact: real-smearing generated vectors are contained in the
complex-smearing generated set (via `schwartzRealToComplex`). -/
theorem hqiv_realGenerated_range_subset_patchGenerated_range
    (Ω : PatchHilbert) :
    Set.range (fun f : SchwartzSpace => hqivPatchJetOperatorValuedDistribution f Ω) ⊆
      Set.range (fun f : PatchSchwartzSpace => patchDerivOVD f Ω) := by
  intro v hv
  rcases hv with ⟨f, rfl⟩
  refine ⟨schwartzRealToComplex f, ?_⟩
  simp [hqivPatchJetOperatorValuedDistribution]

/-- Consequently, the real-generated submodule is always contained in the complex-generated one. -/
theorem hqiv_fieldGeneratedSubmodule_le_patchFieldGeneratedSubmodule (Ω : PatchHilbert) :
    fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution Ω ≤
      patchFieldGeneratedSubmodule patchDerivOVD Ω := by
  refine Submodule.span_le.mpr ?_
  intro v hv
  rcases hqiv_realGenerated_range_subset_patchGenerated_range Ω hv with ⟨f, rfl⟩
  exact Submodule.subset_span ⟨f, rfl⟩

/-- Upgrade condition: if every complex-generated vector also has a real-smearing preimage,
then generated submodules coincide. -/
theorem hqiv_fieldGeneratedSubmodule_eq_patchFieldGeneratedSubmodule_of_range_eq
    (Ω : PatchHilbert)
    (hRange :
      Set.range (fun f : SchwartzSpace => hqivPatchJetOperatorValuedDistribution f Ω) =
        Set.range (fun f : PatchSchwartzSpace => patchDerivOVD f Ω)) :
    fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution Ω =
      patchFieldGeneratedSubmodule patchDerivOVD Ω := by
  simpa [fieldGeneratedSubmodule, patchFieldGeneratedSubmodule] using
    congrArg (Submodule.span ℝ) hRange

/-- Cyclicity transfer under the same upgrade condition (`range` equality). -/
theorem hqiv_realVacuumCyclic_of_patchVacuumCyclic_and_range_eq
    (Ω : PatchHilbert)
    (hPatch :
      Dense (patchFieldGeneratedSubmodule patchDerivOVD Ω : Set PatchHilbert))
    (hRange :
      Set.range (fun f : SchwartzSpace => hqivPatchJetOperatorValuedDistribution f Ω) =
        Set.range (fun f : PatchSchwartzSpace => patchDerivOVD f Ω)) :
    Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution Ω : Set PatchHilbert) := by
  rw [hqiv_fieldGeneratedSubmodule_eq_patchFieldGeneratedSubmodule_of_range_eq Ω hRange]
  exact hPatch

/-- Practical SO(8)/HQIV-use specialization at the canonical patch vacuum. -/
theorem hqiv_realVacuumCyclic_patchOmega_of_range_eq
    (hRange :
      Set.range (fun f : SchwartzSpace =>
          hqivPatchJetOperatorValuedDistribution f patchWightmanOmega) =
        Set.range (fun f : PatchSchwartzSpace => patchDerivOVD f patchWightmanOmega)) :
    Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega :
      Set PatchHilbert) :=
  hqiv_realVacuumCyclic_of_patchVacuumCyclic_and_range_eq
    patchWightmanOmega patch_vacuum_cyclic hRange

/-- Port of the standard cyclicity pattern used in toy/patch files:
`fieldGeneratedSubmodule = ⊤` implies dense generated set. -/
theorem hqiv_realVacuumCyclic_of_eq_top
    (Ω : PatchHilbert)
    (hTop : fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution Ω = ⊤) :
    Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution Ω : Set PatchHilbert) := by
  rw [hTop]
  simp

/-- If range equality holds at the patch vacuum, real-generated submodule is top. -/
theorem hqiv_fieldGeneratedSubmodule_patchOmega_eq_top_of_range_eq
    (hRange :
      Set.range (fun f : SchwartzSpace =>
          hqivPatchJetOperatorValuedDistribution f patchWightmanOmega) =
        Set.range (fun f : PatchSchwartzSpace => patchDerivOVD f patchWightmanOmega)) :
    fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega = ⊤ := by
  calc
    fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega
        = patchFieldGeneratedSubmodule patchDerivOVD patchWightmanOmega :=
      hqiv_fieldGeneratedSubmodule_eq_patchFieldGeneratedSubmodule_of_range_eq patchWightmanOmega hRange
    _ = ⊤ := patchFieldGeneratedSubmodule_patchDeriv_eq_top

/-- Consolidated bridge target: to prove real-smearing vacuum cyclicity, it suffices to prove
range equality between real-smearing and patch-smearing generated vectors at `patchWightmanOmega`. -/
theorem hqiv_realVacuumCyclic_patchOmega_of_range_eq'
    (hRange :
      Set.range (fun f : SchwartzSpace =>
          hqivPatchJetOperatorValuedDistribution f patchWightmanOmega) =
        Set.range (fun f : PatchSchwartzSpace => patchDerivOVD f patchWightmanOmega)) :
    Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega :
      Set PatchHilbert) :=
  hqiv_realVacuumCyclic_of_eq_top patchWightmanOmega
    (hqiv_fieldGeneratedSubmodule_patchOmega_eq_top_of_range_eq hRange)

/-- Theta-window bound viewed as a function of lapse.

This keeps the bridge signature aligned with the GR/HQVM side where the admissible
phase-window scale is read from lapse data. -/
def thetaWindowBoundFromLapse (N : ℝ) : ℝ := N

@[simp] theorem thetaWindowBoundFromLapse_eq (N : ℝ) :
    thetaWindowBoundFromLapse N = N := rfl

/-- Lapse-parameterized theta-window bridge schema (physics side): every complex-smearing generated
vacuum vector can be realized by some real-smearing test indexed by a parameter in
`0 < x < thetaWindowBoundFromLapse N`. -/
def LapseWindowRangeBridgeAtPatchOmega (N : ℝ) : Prop :=
  ∀ g : PatchSchwartzSpace,
    ∃ x : ℝ, 0 < x ∧ x < thetaWindowBoundFromLapse N ∧
      ∃ f : SchwartzSpace,
        hqivPatchJetOperatorValuedDistribution f patchWightmanOmega =
          patchDerivOVD g patchWightmanOmega

/-- The lapse-window bridge implies the needed range equality at `patchWightmanOmega`. -/
theorem hqiv_range_eq_patchOmega_of_lapseWindowRangeBridge
    {N : ℝ} (hBridge : LapseWindowRangeBridgeAtPatchOmega N) :
    Set.range (fun f : SchwartzSpace =>
        hqivPatchJetOperatorValuedDistribution f patchWightmanOmega) =
      Set.range (fun g : PatchSchwartzSpace => patchDerivOVD g patchWightmanOmega) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact hqiv_realGenerated_range_subset_patchGenerated_range patchWightmanOmega
  · intro v hv
    rcases hv with ⟨g, rfl⟩
    rcases hBridge g with ⟨_x, _hx0, _hxN, f, hf⟩
    exact ⟨f, hf⟩

/-- One-line closure: a lapse-window bridge yields real-smearing vacuum cyclicity at patch omega. -/
theorem hqiv_realVacuumCyclic_patchOmega_of_lapseWindowRangeBridge
    {N : ℝ} (hBridge : LapseWindowRangeBridgeAtPatchOmega N) :
    Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega :
      Set PatchHilbert) :=
  hqiv_realVacuumCyclic_patchOmega_of_range_eq'
    (hqiv_range_eq_patchOmega_of_lapseWindowRangeBridge hBridge)

/-- Convenience shape for HQVM lapse input. -/
theorem phaseTheta_le_thetaWindowBoundFrom_HQVM_lapse
    (Φ φ t : ℝ)
    (hBound : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t) :
    Hqiv.Physics.phaseTheta ≤ thetaWindowBoundFromLapse (HQVM_lapse Φ φ t) := by
  simpa [thetaWindowBoundFromLapse]

/-- Equivalent lower-bound form at HQVM lapse value (useful when importing inequalities from GR side). -/
theorem thetaWindowBoundFrom_HQVM_lapse_ge_phaseTheta_iff
    (Φ φ t : ℝ) :
    Hqiv.Physics.phaseTheta ≤ thetaWindowBoundFromLapse (HQVM_lapse Φ φ t) ↔
      Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t := by
  simp [thetaWindowBoundFromLapse]

/-- Numerical window helper: any `x` in the phase cap window is also in the lapse window whenever
`phaseTheta ≤ thetaWindowBoundFromLapse N`. -/
theorem in_lapseWindow_of_in_phaseWindow
    {N x : ℝ}
    (hx0 : 0 < x) (hxθ : x < Hqiv.Physics.phaseTheta)
    (hθN : Hqiv.Physics.phaseTheta ≤ thetaWindowBoundFromLapse N) :
    0 < x ∧ x < thetaWindowBoundFromLapse N := by
  refine ⟨hx0, lt_of_lt_of_le hxθ hθN⟩

/-- Lapse-window witness from the GR-style time-angle phase window (`x = timeAngle φ t`). -/
theorem lapseWindowWitness_of_timeAngle_phaseWindow
    {N φ t : ℝ}
    (hφ : 0 < φ) (ht : 0 < t)
    (hcap : timeAngle φ t < Hqiv.Physics.phaseTheta)
    (hθN : Hqiv.Physics.phaseTheta ≤ thetaWindowBoundFromLapse N) :
    ∃ x : ℝ, 0 < x ∧ x < thetaWindowBoundFromLapse N ∧ x = timeAngle φ t := by
  have hphase : 0 < timeAngle φ t ∧ timeAngle φ t < Hqiv.Physics.phaseTheta :=
    Hqiv.Physics.phase_window_of_timeAngle φ t hφ ht hcap
  refine ⟨timeAngle φ t, ?_, ?_, rfl⟩
  · exact hphase.1
  · exact lt_of_lt_of_le hphase.2 hθN

/-- Constructor-friendly reformulation: to prove the lapse-window bridge, it suffices to provide a
time-angle parameterization of each patch-generated vacuum vector inside the phase cap, together with
a comparison `phaseTheta ≤ thetaWindowBoundFromLapse N`. -/
def TimeAngleRangeParameterizationAtPatchOmega : Prop :=
  ∀ g : PatchSchwartzSpace, ∃ (φ t : ℝ),
    0 < φ ∧ 0 < t ∧ timeAngle φ t < Hqiv.Physics.phaseTheta ∧
    ∃ f : SchwartzSpace,
      hqivPatchJetOperatorValuedDistribution f patchWightmanOmega =
        patchDerivOVD g patchWightmanOmega

/-- Re-export of the parameterization shape used to build a lapse-window bridge. -/
theorem timeAngleRangeParameterizationAtPatchOmega_iff :
    TimeAngleRangeParameterizationAtPatchOmega ↔
      (∀ g : PatchSchwartzSpace, ∃ (φ t : ℝ),
        0 < φ ∧ 0 < t ∧ timeAngle φ t < Hqiv.Physics.phaseTheta ∧
        ∃ f : SchwartzSpace,
          hqivPatchJetOperatorValuedDistribution f patchWightmanOmega =
            patchDerivOVD g patchWightmanOmega) := by
  rfl

/-- Monogamy-proof bridge schema:
the directional monogamy time-angle-budget cluster theorem implies the patch-omega
time-angle range parameterization needed by the real/complex smearing bridge. -/
def MonogamyClusterToTimeAngleRangeBridgeAtPatchOmega : Prop :=
  Hqiv.QM.ClusterDecompositionStatement
      (Hqiv.Physics.clusterCorrelationDirectionalMonogamyTimeAngleBudget 1 1) →
    TimeAngleRangeParameterizationAtPatchOmega

/-- If the monogamy cluster theorem is connected to patch-omega range parameterization,
we get the required parameterization from the already-proved HQIV monogamy theorem. -/
theorem timeAngleRangeParameterizationAtPatchOmega_of_monogamyProof
    (hBridge : MonogamyClusterToTimeAngleRangeBridgeAtPatchOmega) :
    TimeAngleRangeParameterizationAtPatchOmega :=
  hBridge (Hqiv.Physics.cluster_decomposition_directional_monogamy_timeAngleBudget_holds 1 1 zero_lt_one)

/-- Core analytic slot for the from-scratch bridge:
every real 4-jet at the origin is realizable by a real Schwartz test after complex lift. -/
def PatchOmegaRealJetSurjective : Prop :=
  ∀ w : Fin 4 → ℝ, ∃ f : SchwartzSpace, ∀ i : Fin 4,
    patchLineDerivℂAtZero (spacetimeBasis i) (schwartzRealToComplex f) = (w i : ℂ)

/-- Real directional-jet surjectivity at the origin on `SchwartzSpace = 𝓢(ℝ⁴, ℝ)`. -/
def RealDirectionalJetsAtZeroSurjective : Prop :=
  ∀ w : Fin 4 → ℝ, ∃ f : SchwartzSpace, ∀ i : Fin 4,
    lineDeriv ℝ f.toFun (0 : Spacetime) (spacetimeBasis i) = w i

/-- Real affine linear form prescribing first jets along `spacetimeBasis`. -/
noncomputable def realJetLinearCLM (w : Fin 4 → ℝ) : Spacetime →L[ℝ] ℝ :=
  Finset.univ.sum fun i : Fin 4 => (w i) • (PiLp.proj _ _ i : Spacetime →L[ℝ] ℝ)

theorem realJetLinearCLM_single (w : Fin 4 → ℝ) (i : Fin 4) :
    realJetLinearCLM w (spacetimeBasis i) = w i := by
  classical
  simp [realJetLinearCLM, spacetimeBasis, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    PiLp.proj_apply, EuclideanSpace.single_apply, apply_ite, Finset.mem_univ]

noncomputable def realJetBumpFun (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℝ) :
    Spacetime → ℝ :=
  fun x => φ x * realJetLinearCLM w x

theorem eventuallyEq_realJetBumpFun_realJetLinearCLM
    (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℝ) :
    realJetBumpFun φ w =ᶠ[𝓝 (0 : Spacetime)] realJetLinearCLM w := by
  filter_upwards [ContDiffBump.eventuallyEq_one φ] with x hx
  simp [realJetBumpFun, hx]

theorem contDiff_realJetBumpFun (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℝ) {n : ℕ∞} :
    ContDiff ℝ n (realJetBumpFun φ w) := by
  change ContDiff ℝ n fun x => φ x * realJetLinearCLM w x
  exact (φ.contDiff : ContDiff ℝ n (φ : Spacetime → ℝ)).mul (realJetLinearCLM w).contDiff

theorem hasCompactSupport_realJetBumpFun (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℝ) :
    HasCompactSupport (realJetBumpFun φ w) := by
  have hφ : HasCompactSupport (φ : Spacetime → ℝ) := ContDiffBump.hasCompactSupport φ
  rw [show realJetBumpFun φ w = (fun x : Spacetime => φ x) * fun t => realJetLinearCLM w t by rfl]
  exact HasCompactSupport.mul_right hφ

noncomputable def realJetBumpSchwartz (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℝ) :
    SchwartzSpace :=
  (hasCompactSupport_realJetBumpFun φ w).toSchwartzMap (contDiff_realJetBumpFun (n := ⊤) φ w)

theorem lineDeriv_realJetLinearCLM_single (w : Fin 4 → ℝ) (i : Fin 4) :
    lineDeriv ℝ (realJetLinearCLM w) (0 : Spacetime) (spacetimeBasis i) = w i := by
  let L := realJetLinearCLM w
  have hdiff : DifferentiableAt ℝ (fun x : Spacetime => L x) 0 := L.differentiableAt
  rw [hdiff.lineDeriv_eq_fderiv, ContinuousLinearMap.fderiv]
  exact realJetLinearCLM_single w i

theorem lineDeriv_realJetBumpSchwartz_single
    (φ : ContDiffBump (0 : Spacetime)) (w : Fin 4 → ℝ) (i : Fin 4) :
    lineDeriv ℝ (realJetBumpSchwartz φ w).toFun (0 : Spacetime)
      (spacetimeBasis i) = w i := by
  have hev := eventuallyEq_realJetBumpFun_realJetLinearCLM φ w
  have hld :=
    Filter.EventuallyEq.lineDeriv_eq (𝕜 := ℝ) (F := ℝ) (f₁ := realJetBumpFun φ w)
      (f := fun x : Spacetime => realJetLinearCLM w x) (x := (0 : Spacetime)) (v := spacetimeBasis i) hev
  have hco :
      lineDeriv ℝ (realJetBumpSchwartz φ w).toFun (0 : Spacetime)
        (spacetimeBasis i) =
        lineDeriv ℝ (realJetBumpFun φ w) (0 : Spacetime) (spacetimeBasis i) := rfl
  rw [hco, hld, lineDeriv_realJetLinearCLM_single]

/-- Constructive witness: any real 4-jet at origin is realized by a real Schwartz test. -/
theorem realDirectionalJetsAtZeroSurjective :
    RealDirectionalJetsAtZeroSurjective := by
  unfold RealDirectionalJetsAtZeroSurjective
  intro w
  let φ : ContDiffBump (0 : Spacetime) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  refine ⟨realJetBumpSchwartz φ w, fun i => ?_⟩
  simpa using lineDeriv_realJetBumpSchwartz_single φ w i

/-- Promotion lemma: once line-derivative compatibility for `schwartzRealToComplex` is supplied,
the constructive real jet-surjectivity theorem upgrades to `PatchOmegaRealJetSurjective`. -/
theorem patchOmegaRealJetSurjective_of_lineDerivCompat
    (hCompat : ∀ (f : SchwartzSpace) (i : Fin 4),
      patchLineDerivℂAtZero (spacetimeBasis i) (schwartzRealToComplex f) =
        ((lineDeriv ℝ (F := ℝ) f.toFun (0 : Spacetime) (spacetimeBasis i)) : ℂ)) :
    PatchOmegaRealJetSurjective := by
  intro w
  rcases realDirectionalJetsAtZeroSurjective w with ⟨f, hf⟩
  refine ⟨f, fun i => ?_⟩
  rw [hCompat f i, hf i]

/-- Compatibility of patch complex directional derivative with complexified real directional derivative. -/
theorem patchLineDerivℂAtZero_schwartzRealToComplex_eq_lineDeriv
    (f : SchwartzSpace) (i : Fin 4) :
    patchLineDerivℂAtZero (spacetimeBasis i) (schwartzRealToComplex f) =
      ((lineDeriv ℝ (F := ℝ) f.toFun (0 : Spacetime) (spacetimeBasis i)) : ℂ) := by
  let g : Spacetime → ℂ := fun x => Complex.ofRealCLM (f.toFun x)
  have hg_coe : (schwartzRealToComplex f : Spacetime → ℂ) = g := by
    funext x
    change (schwartzRealToComplex f).toFun x = Complex.ofRealCLM (f.toFun x)
    simp [schwartzRealToComplex_apply]
  have hf_diff : DifferentiableAt ℝ f.toFun (0 : Spacetime) := by
    exact (f.differentiableAt (x := (0 : Spacetime)))
  have hg_diff : DifferentiableAt ℝ g (0 : Spacetime) := by
    simpa [g] using (Complex.ofRealCLM.differentiableAt.comp (0 : Spacetime) hf_diff)
  have hg_def : g = Complex.ofRealCLM ∘ f.toFun := by
    funext x
    rfl
  calc
    patchLineDerivℂAtZero (spacetimeBasis i) (schwartzRealToComplex f)
        = lineDeriv ℝ (schwartzRealToComplex f) (0 : Spacetime) (spacetimeBasis i) := by
          simp [patchLineDerivℂAtZero, patchSchwartzEvalAtZero_apply, SchwartzMap.lineDerivOp_apply]
    _ = lineDeriv ℝ g (0 : Spacetime) (spacetimeBasis i) := by
          rw [hg_coe]
    _ = (fderiv ℝ g (0 : Spacetime)) (spacetimeBasis i) := by
          rw [hg_diff.lineDeriv_eq_fderiv]
    _ = (Complex.ofRealCLM (fderiv ℝ f.toFun (0 : Spacetime) (spacetimeBasis i))) := by
          rw [hg_def, fderiv_comp (x := (0 : Spacetime)) Complex.ofRealCLM.differentiableAt hf_diff]
          simp [ContinuousLinearMap.comp_apply]
    _ = ((lineDeriv ℝ (F := ℝ) f.toFun (0 : Spacetime) (spacetimeBasis i)) : ℂ) := by
          rw [hf_diff.lineDeriv_eq_fderiv]
          rfl

/-- Discharged form of `PatchOmegaRealJetSurjective` using the proved line-derivative compatibility. -/
theorem patchOmegaRealJetSurjective :
    PatchOmegaRealJetSurjective :=
  patchOmegaRealJetSurjective_of_lineDerivCompat
    (hCompat := patchLineDerivℂAtZero_schwartzRealToComplex_eq_lineDeriv)

/-- Strong jet-level admissibility at patch omega: first complex directional derivatives are real-valued.

This is a mathematically convenient strengthening used in one proof route; it is not the only
physically meaningful bridge target. Prefer `MonogamyClusterToTimeAngleRangeBridgeAtPatchOmega`
for phase/observable-level closures. -/
def PatchOmegaJetRealAdmissible (g : PatchSchwartzSpace) : Prop :=
  ∃ w : Fin 4 → ℝ, ∀ i : Fin 4, patchLineDerivℂAtZero (spacetimeBasis i) g = (w i : ℂ)

/-- Equivalent scalar form of jet admissibility: all imaginary jet components vanish. -/
def PatchOmegaJetImagZero (g : PatchSchwartzSpace) : Prop :=
  ∀ i : Fin 4, (patchLineDerivℂAtZero (spacetimeBasis i) g).im = 0

theorem patchOmegaJetRealAdmissible_iff_imagZero (g : PatchSchwartzSpace) :
    PatchOmegaJetRealAdmissible g ↔ PatchOmegaJetImagZero g := by
  constructor
  · intro h
    rcases h with ⟨w, hw⟩
    intro i
    rw [hw i]
    simp
  · intro hIm
    refine ⟨fun i => (patchLineDerivℂAtZero (spacetimeBasis i) g).re, ?_⟩
    intro i
    apply Complex.ext
    · simp
    · simpa [PatchOmegaJetImagZero] using hIm i

/-- If a patch test has real-admissible origin jets and real jets are realizable by lifted real
Schwartz tests, then its `patchDerivOVD` value at `patchWightmanOmega` is realized by the real-smearing
HQIV jet OVD. -/
theorem patchOmega_realSmearing_realizes_of_realJetAdmissible
    (hRealJets : PatchOmegaRealJetSurjective)
    {g : PatchSchwartzSpace} (hAdm : PatchOmegaJetRealAdmissible g) :
    ∃ f : SchwartzSpace,
      hqivPatchJetOperatorValuedDistribution f patchWightmanOmega =
        patchDerivOVD g patchWightmanOmega := by
  rcases hAdm with ⟨w, hw⟩
  rcases hRealJets w with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  ext j
  rw [hqivPatchJetOperatorValuedDistribution, patchDerivOVD_apply_omega, patchDerivOVD_apply_omega,
    hf j, hw j]

/-- From-scratch parameterization constructor:
real-jet surjectivity + real-jet admissibility for all patch tests already gives the required
time-angle parameterization (for any fixed phase-window point). -/
theorem timeAngleRangeParameterizationAtPatchOmega_of_realJetSurjective
    (hRealJets : PatchOmegaRealJetSurjective)
    (hAdmissible : ∀ g : PatchSchwartzSpace, PatchOmegaJetRealAdmissible g)
    {φ t : ℝ}
    (hφ : 0 < φ) (ht : 0 < t) (hcap : timeAngle φ t < Hqiv.Physics.phaseTheta) :
    TimeAngleRangeParameterizationAtPatchOmega := by
  intro g
  rcases patchOmega_realSmearing_realizes_of_realJetAdmissible hRealJets (hAdmissible g) with ⟨f, hf⟩
  exact ⟨φ, t, hφ, ht, hcap, f, hf⟩

/-- Monogamy-to-jets bridge schema: the directional monogamy cluster theorem implies patch-omega
real-jet admissibility for all patch Schwartz tests. -/
def MonogamyClusterToPatchOmegaRealJetAdmissible : Prop :=
  Hqiv.QM.ClusterDecompositionStatement
      (Hqiv.Physics.clusterCorrelationDirectionalMonogamyTimeAngleBudget 1 1) →
    ∀ g : PatchSchwartzSpace, PatchOmegaJetRealAdmissible g

/-- Reduced *strong* monogamy bridge target: vanishing imaginary jet components.

This is intentionally stronger than a phase/observable-level bridge and should be treated as
an optional route, not the default physical interpretation. -/
def MonogamyClusterToPatchOmegaJetImagZero : Prop :=
  Hqiv.QM.ClusterDecompositionStatement
      (Hqiv.Physics.clusterCorrelationDirectionalMonogamyTimeAngleBudget 1 1) →
    ∀ g : PatchSchwartzSpace, PatchOmegaJetImagZero g

theorem monogamyClusterToPatchOmegaRealJetAdmissible_of_imagZero
    (hImag : MonogamyClusterToPatchOmegaJetImagZero) :
    MonogamyClusterToPatchOmegaRealJetAdmissible := by
  intro hMon g
  exact (patchOmegaJetRealAdmissible_iff_imagZero g).2 (hImag hMon g)

/-- Canonical bridge target for the monogamy→jets step.
This is definitionally the same shape as `MonogamyClusterToPatchOmegaRealJetAdmissible`. -/
theorem monogamyClusterToPatchOmegaRealJetAdmissible_target :
    (Hqiv.QM.ClusterDecompositionStatement
      (Hqiv.Physics.clusterCorrelationDirectionalMonogamyTimeAngleBudget 1 1) →
        ∀ g : PatchSchwartzSpace, PatchOmegaJetRealAdmissible g) ↔
      MonogamyClusterToPatchOmegaRealJetAdmissible := by
  rfl

/-- Because the directional-monogamy cluster statement at budget `(1,1)` is already proved,
the current bridge obligation is equivalent to global real-jet admissibility for all
patch Schwartz tests. This highlights that the obligation is stronger than a purely
phase/observable-level closure target. -/
theorem monogamyClusterToPatchOmegaRealJetAdmissible_iff_global :
    MonogamyClusterToPatchOmegaRealJetAdmissible ↔
      (∀ g : PatchSchwartzSpace, PatchOmegaJetRealAdmissible g) := by
  constructor
  · intro h g
    exact h (Hqiv.Physics.cluster_decomposition_directional_monogamy_timeAngleBudget_holds 1 1 zero_lt_one) g
  · intro h _hCluster g
    exact h g

/-- User-facing constructor: once the analytic monogamy-imaginary-part bridge is proved,
the real-jet admissibility target follows immediately. -/
theorem monogamy_implies_patch_jet_real
    (_hCluster : Hqiv.QM.ClusterDecompositionStatement
        (Hqiv.Physics.clusterCorrelationDirectionalMonogamyTimeAngleBudget 1 1))
    (hImag :
      ∀ g : PatchSchwartzSpace, PatchOmegaJetImagZero g) :
    ∀ g : PatchSchwartzSpace, PatchOmegaJetRealAdmissible g := by
  intro g
  exact (patchOmegaJetRealAdmissible_iff_imagZero g).2 (hImag g)

/-- Preferred physical bridge shape: monogamy gives the parameterization needed for closure directly,
without forcing pointwise jet-reality. -/
abbrev MonogamyClusterToPhysicalRangeBridgeAtPatchOmega : Prop :=
  MonogamyClusterToTimeAngleRangeBridgeAtPatchOmega

/-- Probe-family condition used by the physical bridge: pick a time-angle point
strictly inside the phase cap. This is the phase/observable-level window condition. -/
def PatchOmegaProbeFamilyCondition (φ t : ℝ) : Prop :=
  0 < φ ∧ 0 < t ∧ timeAngle φ t < Hqiv.Physics.phaseTheta

/-- Refined physical bridge schema: from the monogamy cluster statement, every patch test admits
an in-window probe-family point together with a real-smearing realization at `patchWightmanOmega`.
This avoids committing to the stronger global jet-reality target. -/
def MonogamyProbeFamilyPhysicalBridgeAtPatchOmega : Prop :=
  Hqiv.QM.ClusterDecompositionStatement
      (Hqiv.Physics.clusterCorrelationDirectionalMonogamyTimeAngleBudget 1 1) →
    ∀ g : PatchSchwartzSpace,
      ∃ φ t : ℝ, PatchOmegaProbeFamilyCondition φ t ∧
        ∃ f : SchwartzSpace,
          hqivPatchJetOperatorValuedDistribution f patchWightmanOmega =
            patchDerivOVD g patchWightmanOmega

/-- Precise remaining analytic step:
translate the proved directional monogamy cluster statement into the probe-family physical bridge
at `patchWightmanOmega` (correlator-level unpacking). -/
def MonogamyClusterToProbeFamilyCorrelatorBridgeAtPatchOmega : Prop :=
  Hqiv.QM.ClusterDecompositionStatement
      (Hqiv.Physics.clusterCorrelationDirectionalMonogamyTimeAngleBudget 1 1) →
    ∀ g : PatchSchwartzSpace,
      ∃ f : SchwartzSpace,
        hqivPatchJetOperatorValuedDistribution f patchWightmanOmega =
          patchDerivOVD g patchWightmanOmega

/-- Reference-backed bridge slot (cluster decomposition + locality on separated supports).

Use this as the lightweight closure hypothesis while the full correlator/error-bound formalization
is developed in Story. Standard references for the underlying argument pattern include
Streater–Wightman (cluster property), Weinberg Vol. I §4.3, and Haag. -/
abbrev LiteratureClusterCorrelatorBridgeAtPatchOmega : Prop :=
  MonogamyClusterToProbeFamilyCorrelatorBridgeAtPatchOmega

/-- Placeholder for support/time-angle separation of the probe family from a reference patch test.
This is the geometric side of the correlator argument; the concrete support relation can be refined
without changing downstream wiring. -/
def PatchProbeSupportSeparatedAtPatchOmega
    (_g : PatchSchwartzSpace) (_f : SchwartzSpace) (_φ _t : ℝ) : Prop :=
  True

/-- Placeholder for the correlator-level imaginary-part control used in the monogamy step.
This packages the analytic estimate that forces jet mismatch to vanish in the chosen probe window. -/
def PatchCorrelatorImagControlAtPatchOmega
    (_g : PatchSchwartzSpace) (_f : SchwartzSpace) (_φ _t : ℝ) : Prop :=
  True

/-- Refined analytic package for the remaining monogamy→probe-family step.
`hSelect` chooses an in-cap probe point for each `g`; `hCorr` is the correlator-imaginary-part
control at that point; `hRealize` is the resulting realization equality. -/
def PatchMonogamyCorrelatorAxiomsAtPatchOmega : Prop :=
  ∀ g : PatchSchwartzSpace, ∃ φ t : ℝ, PatchOmegaProbeFamilyCondition φ t ∧
    ∃ f : SchwartzSpace,
      PatchProbeSupportSeparatedAtPatchOmega g f φ t ∧
      PatchCorrelatorImagControlAtPatchOmega g f φ t ∧
      hqivPatchJetOperatorValuedDistribution f patchWightmanOmega =
        patchDerivOVD g patchWightmanOmega

/-- Wiring theorem: once correlator/separation axioms are provided, the monogamy probe-family
bridge follows immediately. This is the single integration point for the remaining analytic proof. -/
theorem monogamyProbeFamilyPhysicalBridgeAtPatchOmega_of_correlatorAxioms
    (hAxioms : PatchMonogamyCorrelatorAxiomsAtPatchOmega) :
    MonogamyProbeFamilyPhysicalBridgeAtPatchOmega := by
  intro _hCluster g
  rcases hAxioms g with ⟨φ, t, hcond, f, _hsep, _hcorr, hf⟩
  exact ⟨φ, t, hcond, f, hf⟩

/-- Constructor reducing the full probe-family bridge to the single correlator-level step. -/
theorem monogamyProbeFamilyPhysicalBridgeAtPatchOmega_of_correlatorBridge
    (hCorr : MonogamyClusterToProbeFamilyCorrelatorBridgeAtPatchOmega) :
    MonogamyProbeFamilyPhysicalBridgeAtPatchOmega := by
  intro hCluster g
  have hProbe : ∃ φ t : ℝ, PatchOmegaProbeFamilyCondition φ t := by
    refine ⟨1, 1, ?_⟩
    refine ⟨by norm_num, by norm_num, ?_⟩
    rw [Hqiv.Physics.phaseTheta_eq_pi_div_two]
    have hpi : (2 : ℝ) < Real.pi := by
      linarith [Real.pi_gt_three]
    have hhalf : (1 : ℝ) < Real.pi / 2 := by
      nlinarith
    simpa [timeAngle] using hhalf
  rcases hProbe with ⟨φ, t, hcond⟩
  rcases hCorr hCluster g with ⟨f, hf⟩
  exact ⟨φ, t, hcond, f, hf⟩

/-- The refined probe-family bridge implies the canonical physical range bridge. -/
theorem monogamyClusterToPhysicalRangeBridgeAtPatchOmega_of_probeFamilyBridge
    (hProbe : MonogamyProbeFamilyPhysicalBridgeAtPatchOmega) :
    MonogamyClusterToPhysicalRangeBridgeAtPatchOmega := by
  intro hCluster g
  rcases hProbe hCluster g with ⟨φ, t, hcond, f, hf⟩
  exact ⟨φ, t, hcond.1, hcond.2.1, hcond.2.2, f, hf⟩

/-- Concrete phase-window point used by the physical bridge constructor:
`φ = 1`, `t = 1`, so `timeAngle φ t = 1 < phaseTheta = π/2`. -/
theorem phaseWindow_point_one_one :
    ∃ φ t : ℝ, 0 < φ ∧ 0 < t ∧ timeAngle φ t < Hqiv.Physics.phaseTheta := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  rw [Hqiv.Physics.phaseTheta_eq_pi_div_two]
  have hpi : (2 : ℝ) < Real.pi := by
    linarith [Real.pi_gt_three]
  have hhalf : (1 : ℝ) < Real.pi / 2 := by
    nlinarith
  simpa [timeAngle] using hhalf

/-- Physical bridge constructor from the monogamy cluster theorem plus the jet-admissibility bridge.

This keeps the target at phase/observable level (`TimeAngleRangeParameterizationAtPatchOmega`) and
does not force the stronger pointwise imaginary-jet-vanishing route. -/
theorem monogamyClusterToPhysicalRangeBridgeAtPatchOmega_of_realJetBridge
    (hMonogamyToJets : MonogamyClusterToPatchOmegaRealJetAdmissible) :
    MonogamyClusterToPhysicalRangeBridgeAtPatchOmega := by
  intro hCluster g
  rcases phaseWindow_point_one_one with ⟨φ, t, hφ, ht, hcap⟩
  have hRealJet : PatchOmegaJetRealAdmissible g := hMonogamyToJets hCluster g
  rcases patchOmega_realSmearing_realizes_of_realJetAdmissible
      patchOmegaRealJetSurjective hRealJet with ⟨f, hf⟩
  exact ⟨φ, t, hφ, ht, hcap, f, hf⟩

/-- Composition theorem: monogamy proof + monogamy→jets bridge + real-jet surjectivity yields the
`TimeAngleRangeParameterizationAtPatchOmega` target used by the SO(8) YM closure chain. -/
theorem timeAngleRangeParameterizationAtPatchOmega_of_monogamyProof_realJets
    (hRealJets : PatchOmegaRealJetSurjective)
    (hMonogamyToJets : MonogamyClusterToPatchOmegaRealJetAdmissible)
    {φ t : ℝ}
    (hφ : 0 < φ) (ht : 0 < t) (hcap : timeAngle φ t < Hqiv.Physics.phaseTheta) :
    TimeAngleRangeParameterizationAtPatchOmega := by
  refine timeAngleRangeParameterizationAtPatchOmega_of_realJetSurjective
    hRealJets (hMonogamyToJets ?_) hφ ht hcap
  exact Hqiv.Physics.cluster_decomposition_directional_monogamy_timeAngleBudget_holds 1 1 zero_lt_one

/-- Constructor-friendly reformulation: to prove the lapse-window bridge, it suffices to provide a
time-angle parameterization of each patch-generated vacuum vector inside the phase cap, together with
a comparison `phaseTheta ≤ thetaWindowBoundFromLapse N`. -/
theorem lapseWindowRangeBridgeAtPatchOmega_of_timeAngle_param
    {N : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ thetaWindowBoundFromLapse N)
    (hParam : TimeAngleRangeParameterizationAtPatchOmega) :
    LapseWindowRangeBridgeAtPatchOmega N := by
  intro g
  rcases hParam g with ⟨φ, t, hφ, ht, hcap, f, hf⟩
  rcases lapseWindowWitness_of_timeAngle_phaseWindow (N := N) (φ := φ) (t := t) hφ ht hcap hθN
    with ⟨x, hx0, hxN, _hxEq⟩
  exact ⟨x, hx0, hxN, f, hf⟩

/-- HQVM-lapse-specialized constructor: if your parameterization theorem is stated at
`N = HQVM_lapse Φ φ t`, this packages it directly into a lapse-window bridge. -/
theorem lapseWindowRangeBridgeAtPatchOmega_of_timeAngle_param_HQVM_lapse
    {Φ φ t : ℝ}
    (hθN : Hqiv.Physics.phaseTheta ≤ HQVM_lapse Φ φ t)
    (hParam : TimeAngleRangeParameterizationAtPatchOmega) :
    LapseWindowRangeBridgeAtPatchOmega (HQVM_lapse Φ φ t) := by
  refine lapseWindowRangeBridgeAtPatchOmega_of_timeAngle_param
    (N := HQVM_lapse Φ φ t) ?_ hParam
  exact phaseTheta_le_thetaWindowBoundFrom_HQVM_lapse Φ φ t hθN

/-- Real-Schwartz Wightman package on `PatchHilbert`, driven by the HQIV patch jet OVD.

All spectral/vacuum/Poincare fields are taken from `MillenniumBridgePatchPoincareWightman`.
The only extra input is vacuum cyclicity for the **real** smearing-generated submodule.
-/
noncomputable def hqivPatchWightmanAxioms
    (hVacuumCyclic :
      Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega :
        Set PatchHilbert)) :
    WightmanAxioms PatchHilbert hqivPatchJetOperatorValuedDistribution where
  poincare_group := PatchMillenniumPoincareGroup
  poincare_structure := Multiplicative.group (α := Space)
  unitary_rep := patchMillenniumPoincareTrivialUnitaryRep
  action_on_tests := fun _g f => f
  action_on_tests_one := by intro f; rfl
  action_on_tests_mul := by intro g₁ g₂ f; rfl
  covariance := hqivPatchJet_operator_patchCovariance
  hamiltonian := patchHamiltonian
  is_hamiltonian_self_adjoint := patchHamiltonian_isSelfAdjoint
  is_hamiltonian_positive := patchHamiltonian_isPositive
  spaceTranslation := patchSpatialTranslation
  spaceTranslation_zero := patchSpatialTranslation_zero
  spaceTranslation_add := patchSpatialTranslation_add
  spectrum_nonneg := patch_spectrum_nonneg
  vacuum_energy_zero := patch_vacuum_energy_zero
  vacuum := patchWightmanOmega
  is_vacuum := patch_isVacuum
  vacuum_invariant := patch_vacuum_poincare_invariant
  vacuum_spatial_invariant := patch_vacuum_spatial_invariant
  vacuum_cyclic := hVacuumCyclic
  locality := hqivPatchJet_operator_locality

/-- Remaining non-Wightman slots needed to build a full Dojo `QuantumYangMillsTheory`
on top of the HQIV patch Wightman package. -/
structure HQIVPatchQuantumYangMillsInputs (G : Type) [CompactSimpleGaugeGroup G] where
  localOperators : LocalOperatorAssignment G PatchHilbert
  shortDistance : ShortDistanceAgreement hqivPatchJetOperatorValuedDistribution patchWightmanOmega
  stressTensor : StressEnergyTensor PatchHilbert
  operatorProductExpansion : OperatorProductExpansion G PatchHilbert
  localOperators_covariant :
    ∀ g p f,
      (localOperators.op p) ((fun _g' (f' : SchwartzSpace) => f') g f) =
        conjugateOperator (patchMillenniumPoincareTrivialUnitaryRep g) ((localOperators.op p) f)
  localOperators_locality :
    ∀ (p q : GaugeInvariantLocalPolynomial G) (f g : SchwartzMap Spacetime ℝ),
      (∀ (x y : Spacetime),
        (MinkowskiMetric (x - y) (x - y) < 0) → f x = 0 ∨ g y = 0) →
      (localOperators.op p f) ∘L (localOperators.op q g) =
        (localOperators.op q g) ∘L (localOperators.op p f)

/-- Full non-toy QFT constructor on `PatchHilbert` from HQIV patch data. -/
noncomputable def hqivPatchQuantumYangMills (G : Type) [CompactSimpleGaugeGroup G]
    (hVacuumCyclic :
      Dense (fieldGeneratedSubmodule hqivPatchJetOperatorValuedDistribution patchWightmanOmega :
        Set PatchHilbert))
    (inputs : HQIVPatchQuantumYangMillsInputs G) :
    QuantumYangMillsTheory G where
  hilbertSpace := PatchHilbert
  field_operators := hqivPatchJetOperatorValuedDistribution
  wightman := hqivPatchWightmanAxioms hVacuumCyclic
  localOperators := inputs.localOperators
  shortDistance := inputs.shortDistance
  stressTensor := inputs.stressTensor
  operatorProductExpansion := inputs.operatorProductExpansion
  localOperators_covariant := inputs.localOperators_covariant
  localOperators_locality := inputs.localOperators_locality

/-- Certified Dojo `QuantumYangMillsTheory` witness (current spine: minimal Schwartz carrier). -/
noncomputable abbrev hqivInterfaceQuantumYangMills (G : Type) [CompactSimpleGaugeGroup G] :
    QuantumYangMillsTheory G :=
  QuantumYangMillsFromPoincareToy.poincareToyQuantumYangMills G

theorem nonempty_hqivInterface_quantumYangMills (G : Type) [CompactSimpleGaugeGroup G] :
    Nonempty (QuantumYangMillsTheory G) :=
  ⟨hqivInterfaceQuantumYangMills G⟩

end QuantumYangMillsFromPatchHQIV

end Hqiv.Story
