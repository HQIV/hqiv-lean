import HqivSpine.Physics.MassLadder
import HqivSpine.Physics.Age
import HqivSpine.Physics.Baryogenesis
import HqivSpine.Physics.AlphaRunning
import HqivSpine.Physics.Forces
import HqivSpine.Physics.ColorCasimir
import HqivSpine.Physics.TrappedCasimir
import HqivSpine.Physics.CurvatureKernel
import HqivSpine.Physics.NeutrinoMixing
import HqivSpine.Physics.NowSliceFromLattice
import HqivSpine.Physics.LockInMechanism
import HqivSpine.Physics.ClosureAction
import HqivSpine.Physics.JointClosureAction
import HqivSpine.Physics.BulkHyperboloidDynamics
import HqivSpine.Physics.NowSliceCausalDiamond
import HqivSpine.Physics.NowSliceOmegaKBridge
import HqivSpine.Physics.NowSliceClosure
import HqivSpine.Physics.HQVMGeodesics
import HqivSpine.Physics.CovariantOMaxwell
import HqivSpine.Geometry.HQVMMetric
import HqivSpine.Physics.BaryogenesisShellLadder
import HqivSpine.Physics.NestedHopfBinding
import HqivSpine.Physics.SectorNestedHopfBinding
import HqivSpine.Physics.ContentClassCompositeTrace
import HqivSpine.Physics.TuftBeltramiMassFunctional
import HqivSpine.Physics.GenerationResonanceLadder
import HqivSpine.Physics.LeptonAbsoluteScale
import HqivSpine.Physics.HeavyQuarkAbsoluteScale
import HqivSpine.Physics.NeutrinoAbsoluteScale
import HqivSpine.Physics.ContinuousHorizon
import HqivSpine.Algebra.StrongColorSu3LieLaw
import HqivSpine.Algebra.StrongColorEmbed
import HqivSpine.Physics.NonAbelianMatrixElement
import HqivSpine.Physics.NonAbelianDynamics
import HqivSpine.Algebra.Triality
import HqivSpine.Algebra.Anomaly

/-!
# `HqivSpine.Physics.Frontiers` — explicit derivation boundaries

The spine is honest about what is **derived** versus what is still an **anchor or
open obligation**. The single physical anchor is the **now slice** (`NowSlice`),
which carries the curvatures `φ`, `Φ`, `Ω_k`; every mass is the dimensionless
now-scale times a ratio. The empirical proton MeV value is **not** the anchor — it
is a comparison number that, at most, fixes the MeV unit label.

Nothing here is asserted as an axiom. Frontiers are descriptive records; the
contrasting *closed* facts (lepton ratios, meson/baryon scale, curvature imprint)
are ordinary proved theorems re-exported for contrast.
-/

namespace HqivSpine.Physics

/-- A named derivation boundary: what must still be proved to remove an anchor. -/
structure DerivationFrontier where
  /-- Short identifier. -/
  name : String
  /-- The obligation that would close the frontier. -/
  obligation : String
  /-- Whether closing it would leave the now slice as the sole physical input. -/
  collapsesToNowSlice : Bool

/-- Now-slice curvature closure: derive the slice curvatures `φ`, `Φ`, `Ω_k`
themselves (and hence `massUnit` and `δ_E`) from the lattice/bulk geometry.

**Partially closed** on the discrete null lattice (`NowSliceFromLattice`): temperature
ladder, shell-ledger `Φ`, and lock-in readout `(φ, Φ, Ω_k, t) = (1, 0, 1, 4)`.
**Partially closed** for `Ω_k`: primary readout is the continuous horizon chart
(`omegaKPartial = omegaKChart`; `NowSliceOmegaKBridge`); left-sample shell sum bounds harmonic
imprint only.
**Partially closed** for homogeneous bulk `H(t) = N(t) = 1 + φ·t` (`BulkHyperboloidDynamics`).
**Partially closed** as a **causal diamond** (`NowSliceCausalDiamond`): local apex chart + global
`(α,γ)` evaluation map.
**Partially closed** for **null geodesics** on the discrete chart (`Geometry.Lorentz.lorentz_closure`)
and the homogeneous comoving worldline (`BulkHyperboloidDynamics`).
**Closed** for HQVM Christoffel jet + comoving and spatial-lapse inhomogeneous geodesics
(`HQVMGeodesics`, `HQVMMetric`).
**Closed** for non-comoving timelike/spacelike straight lines in the flat-jet HQVM chart
(`HQVMGeodesics.geodesicStraightLine_flatJet`, `referenceM_noncomoving_geodesics_closed`).
**Consolidated** in `NowSliceClosure` (`referenceM_now_slice_closure_closed`). -/
def nowSliceCurvatureFrontier : DerivationFrontier where
  name := "now_slice_curvature_closure"
  obligation :=
    "Closed: HQVM Christoffel jet, comoving and non-comoving geodesics (flat-jet straight lines), " ++
    "spatial lapse gradients, covariant plasma O-Maxwell, chart Ω_k, causal diamond, bulk clock " ++
    "(NowSliceClosure / HQVMGeodesics / CovariantOMaxwell)."
  collapsesToNowSlice := false

/-- Heavy-quark absolute scale: **closed** — quark constituent scales from nested Hopf chart
binding with the three-slot content-class trace; cross-sector `9/4` from `(l_q/l_ℓ)² = C_A/C_F`
(`SectorNestedHopfBinding`). -/
def heavyQuarkScaleFrontier : DerivationFrontier where
  name := "heavy_quark_absolute_scale"
  obligation :=
    "Closed: quark nested Hopf binding + content-class trace + cross-sector Casimir ratio " ++
    "(SectorNestedHopfBinding)."
  collapsesToNowSlice := true

/-- Lepton absolute scale: **closed** — charged leptons use the two-slot content-class trace on
nested Hopf rows; composite = Beltrami readout (`SectorNestedHopfBinding`). -/
def leptonAbsoluteScaleFrontier : DerivationFrontier where
  name := "lepton_absolute_scale"
  obligation :=
    "Closed: charged-fermion two-slot composite trace on nested Hopf rows, distinct from " ++
    "nucleon reuse (SectorNestedHopfBinding)."
  collapsesToNowSlice := true

/-- Neutrino absolute scale: **closed** — one-slot trace on nested Hopf rows gives readout
`λ_min/4`; physical mass = matched charged-lepton anchor × `γ/S(referenceM+2) = anchor/140`
(`NeutrinoAbsoluteScale` + `CarrierMonogamySuppression`). Cosmological normalization remains
comparison-only. -/
def neutrinoAbsoluteScaleFrontier : DerivationFrontier where
  name := "neutrino_absolute_scale"
  obligation :=
    "Closed: one-slot nested Hopf readout + carrier monogamy suppression γ/(7·8) " ++
    "(NeutrinoAbsoluteScale). MeV calibration and Σm_ν comparison stay quarantined."
  collapsesToNowSlice := true

/-- Detuned generation resonance: **closed** on the now slice via outer shells `15 → 33 → 58`
(`GenerationResonanceLadder`). Structural ratios `μ/e = 4484/2499`, `τ/μ = 175/76` mined from legacy
charged-lepton resonance. PDG-scale absolute masses remain comparison-only (TUFT sector spectral / MeV
discharge quarantined). -/
def detunedGenerationResonanceFrontier : DerivationFrontier where
  name := "detuned_generation_resonance"
  obligation :=
    "Closed: Hopf heavy anchor × outer-ladder descent on shells 15/33/58 (GenerationResonanceLadder). " ++
    "Ratios μ/e and τ/μ match legacy structural targets. PDG MeV labels stay quarantined."
  collapsesToNowSlice := true

/-- MeV unit convention: the now-scale is dimensionless; the MeV label is fixed by
the empirical proton comparison value, not derived. -/
def mevUnitConventionFrontier : DerivationFrontier where
  name := "mev_unit_convention"
  obligation :=
    "The now-scale is dimensionless; attaching MeV is a unit convention fixed by " ++
    "the empirical proton comparison value, not a derived number."
  collapsesToNowSlice := false

/-- Comparison discipline: NIST/PDG/CODATA tables may validate but must never feed
the prediction path. -/
def comparisonQuarantineFrontier : DerivationFrontier where
  name := "comparison_quarantine"
  obligation :=
    "Keep PDG/CODATA/NIST strictly in a comparison layer; predictions depend only " ++
    "on the now slice and derived ratios."
  collapsesToNowSlice := false

/-- Baryon-asymmetry shell ladder: discrete `η(m) = Ω_k(m)·δ_E(m)` on every balanced-horizon
shell via `BaryogenesisShellLadder` / `CausalDiamond.readoutAtShell`. Lock-in `η = δ_E(4)`
recovers `BBN.baryonToPhoton`. Comparison to `η_observed` remains quarantined. -/
def baryonAsymmetryScaleFrontier : DerivationFrontier where
  name := "baryon_asymmetry_absolute_scale"
  obligation :=
    "Closed: sub-lock-in η(m) = omegaKPartial m · deltaE m on the discrete ladder " ++
    "(BaryogenesisShellLadder); lock-in η = δ_E(referenceM). Compare to η_observed only in " ++
    "the comparison layer."
  collapsesToNowSlice := true

/-- Non-abelian dynamics: the colour Casimirs, four-channel mask, full `su(3)` chart
(`f^{abc}` + global Lie law), matrix-element pipeline, `8 × 8` complex carrier embed,
real-skew `su(3) ↪ 𝔰𝔬(6) ↪ 𝔰𝔬(8)`, and the lock-in **`4+4` complex structure** on the carrier
(`NonAbelianDynamics`: `J² = −1`, gauge block `{0,1,2,3}` → strong block `{4,5,6,7}` at
`m = referenceM = 4`). Still optional downstream: full Spin(8) triality automorphism on 𝔰𝔬(8)
or dynamical QCD. -/
def nonAbelianDynamicsFrontier : DerivationFrontier where
  name := "non_abelian_matrix_elements"
  obligation :=
    "Closed: chart, pipeline, carrier Lie law, real `su(3) ⊂ 𝔰𝔬(6)`, lock-in `4+4` complex " ++
    "structure (`NonAbelianDynamics.referenceM_non_abelian_dynamics_closed`). Optional: full " ++
    "Spin(8) triality automorphism on 𝔰𝔬(8) or dynamical non-abelian field equations."
  collapsesToNowSlice := false

/-- Screened low-energy α: derive the Thomson/hydrogen `1/137` from the naked
high-scale coupling by vacuum-polarisation screening *inside the chemistry layer* —
never as a spine target. -/
def screenedAlphaChemistryFrontier : DerivationFrontier where
  name := "screened_low_energy_alpha"
  obligation :=
    "The naked high-scale coupling 1/α_eff(EW) ≈ 1/128 is derived; the screened " ++
    "1/137 (Thomson/hydrogen) is a chemistry/spectroscopy-layer readout via vacuum " ++
    "polarisation, not a spine number, and is never chased on hydrogen."
  collapsesToNowSlice := false

/-- The current open derivation boundaries of the clean spine. -/
def openFrontiers : List DerivationFrontier :=
  [screenedAlphaChemistryFrontier,
    mevUnitConventionFrontier, comparisonQuarantineFrontier]

/-- External inputs the clean spine refuses to use in the prediction path. -/
def quarantinedExternalInputs : List String :=
  ["m_top_GeV", "m_bottom_GeV", "quark_readout_triples", "electroweakVev_MeV",
    "PDG_mass_tables", "CODATA_alpha", "witness_JSON_as_input",
    "proton_mass_as_anchor", "eta_baryon_observed",
    "screened_alpha_137_on_hydrogen", "alpha_MZ_decimal"]

/-- **Comparison only:** the empirical proton mass in MeV. This is *not* the spine
anchor (that is the now slice); it is the number a now-slice readout is compared
against and which fixes the MeV unit label. -/
def protonMass_MeV_comparison : ℝ := 938.272

/-- **Comparison only (chemistry layer):** the screened low-energy `1/α ≈ 137.036`
(Thomson / hydrogen). This is the *screened* coupling after vacuum polarisation — it
is **not** the HQIV target and lives in a separate chemistry/spectroscopy
comparison layer, not the prediction spine. -/
def oneOverAlpha_screened_lowEnergy_comparison : ℝ := 137.035999

/-- **Comparison only:** the high-scale "naked on the W" `1/α ≈ 127.95`. The spine
derives the *symbolic* naked-W readout `42·(1 + c·(3/5)·log 13)`; this decimal is the
number that readout is compared against, not an input. -/
def oneOverAlpha_nakedW_comparison : ℝ := 127.95

/-! ## Closed facts re-exported for contrast (these are proved) -/

/-- **Closed:** charged-lepton absolute readout ratios from outer-ladder resonance
(`GenerationResonanceLadder`; mined legacy `175/76`, `4484/2499`). Bare Beltrami spectral steps
`4/3`, `3/2` remain in `MassLadder` / `HadronSpectrum` for the TUFT chart ladder only. -/
theorem lepton_generation_ratios_closed :
    GenerationResonanceLadder.generationResonanceMassFactor 3 /
        GenerationResonanceLadder.generationResonanceMassFactor 2 = 175 / 76 ∧
      GenerationResonanceLadder.generationResonanceMassFactor 2 /
        GenerationResonanceLadder.generationResonanceMassFactor 1 = 4484 / 2499 :=
  ⟨GenerationResonanceLadder.generationResonanceMassFactor_tau_over_muon,
    GenerationResonanceLadder.generationResonanceMassFactor_mu_over_electron⟩

/-- **Closed:** the meson/baryon intrinsic mass scale is the derived `4/9`. -/
theorem meson_baryon_scale_closed :
    hadronIntrinsicScale .meson = (4 : ℝ) / 9 ∧ hadronIntrinsicScale .baryon = 1 :=
  ⟨hadronIntrinsicScale_meson, hadronIntrinsicScale_baryon⟩

/-- **Closed:** the curvature imprint weight strictly decays in the shell index,
so the discrete index is load-bearing (a continuum limit destroys it). -/
theorem curvature_imprint_discrete_loadbearing (m : ℕ) :
    imprintWeight (m + 1) < imprintWeight m :=
  imprintWeight_strictAnti m

/-- **Closed:** the curvature norm is the foundation number `N₆₇ = 6⁷√3`. -/
theorem curvature_norm_closed : curvatureNorm = (6 : ℝ) ^ 7 * Real.sqrt 3 :=
  curvatureNorm_eq

/-- **Closed:** the baryon asymmetry is positive for positive curvature at every shell
(it is a now-slice curvature readout, not a fitted constant). -/
theorem baryon_asymmetry_positive_closed (s : NowSlice) (hΩ : 0 < s.omegaK) (m : ℕ) :
    0 < baryonAsymmetry s m :=
  baryonAsymmetry_pos s hΩ m

/-- **Closed:** the unification coupling is the foundation number `1/α_GUT = 6·imaginaryDim = 42`. -/
theorem alpha_GUT_closed : alphaGUTinv = 6 * (Foundation.imaginaryDim : ℝ) ∧ alphaGUTinv = 42 :=
  ⟨alphaGUTinv_eq_six_mul_imaginaryDim, alphaGUTinv_eq_42⟩

/-- **Closed:** the derived (naked, high-scale) fine-structure coupling at the
electroweak shell is `42·(1 + c·(3/5)·log 13)` and sits strictly above unification —
the HQIV α is this `O(1/128)` naked-W value, not the screened `1/137`. -/
theorem naked_alpha_closed (c : ℝ) (hc : 0 < c) :
    oneOverAlphaNakedW c = 42 * (1 + c * (3 / 5) * Real.log 13) ∧
    alphaGUTinv < oneOverAlphaNakedW c :=
  ⟨oneOverAlphaNakedW_closed_form c, oneOverAlphaNakedW_gt_GUT hc⟩

/-- **Closed:** the homogeneous age ratio is `1 + φ·t/2`, a now-slice consequence. -/
theorem age_ratio_closed (s : NowSlice) (ht : s.apparentAge ≠ 0) :
    s.wallClockAge / s.apparentAgeValue = 1 + s.phi * s.apparentAge / 2 :=
  s.ageRatio_eq ht

/-- **Closed (discrete lattice):** lock-in `(φ, Φ, Ω_k, t) = (1, 0, 1, 4)` and
`massUnit = 5 = ξ_lock` from null-lattice geometry. -/
theorem now_slice_lockin_from_lattice_closed :
    NowSliceFromLattice.lockinNowSlice.phi = 1 ∧
    NowSliceFromLattice.lockinNowSlice.bigPhi = 0 ∧
    NowSliceFromLattice.lockinNowSlice.omegaK = 1 ∧
    NowSliceFromLattice.lockinNowSlice.apparentAge = 4 ∧
    NowSliceFromLattice.lockinNowSlice.massUnit = 5 :=
  ⟨NowSliceFromLattice.lockinNowSlice_fields.1,
    NowSliceFromLattice.lockinNowSlice_fields.2.1,
    NowSliceFromLattice.lockinNowSlice_fields.2.2.1,
    NowSliceFromLattice.lockinNowSlice_fields.2.2.2,
    NowSliceFromLattice.lockinNowSlice_massUnit⟩

/-- **Closed:** lock-in ages from the lattice slice — wall-clock `12`, ratio `3`. -/
theorem now_slice_lockin_ages_closed :
    NowSliceFromLattice.lockinNowSlice.wallClockAge = 12 ∧
    NowSliceFromLattice.lockinNowSlice.wallClockAge /
      NowSliceFromLattice.lockinNowSlice.apparentAgeValue = 3 :=
  ⟨NowSliceFromLattice.lockinNowSlice_wallClockAge,
    NowSliceFromLattice.lockinNowSlice_ageRatio⟩

/-- **Closed:** the three-layer lock-in mechanism at `referenceM = 4` — sector-closure
balance (`lockInDrive` / `modeDeficit`), monogamy inward wall with Pauli floor at shell `2`,
blackbody stability, and `η_mode(4) = 1/3`. -/
theorem referenceM_lockin_mechanism_closed : Nonempty ReferenceMLockInMechanism :=
  ⟨referenceMLockInMechanism⟩

/-- **Closed:** variational shell lock-in — closure budget `V(m)=(N(m)−C)²/(2C)` has unique
minimum at `m = referenceM`, gradient `∂V/∂m = −8·modeDeficit/C`, and overdamped flow matches
`lockInDrive`; Hopf chart `n+1 = 4` and `Δ ⊂ 𝔰𝔬(8)`. -/
theorem referenceM_closure_action_closed : Nonempty ReferenceMClosureAction :=
  ⟨referenceMClosureAction⟩

/-- **Closed:** dynamic inner/outer Casimir balance `trapped·ξ·γ/S = C` uniquely at
`m = referenceM`, hence `ξ_lock = xiOfShell referenceM = horizonCount referenceM = 5`
and `massUnit = ξ_lock` at lock-in (`referenceMCasimirClosureAction`). -/
theorem referenceM_casimir_closure_action_closed : Nonempty ReferenceMCasimirClosureAction :=
  ⟨referenceMCasimirClosureAction⟩

/-- **Closed:** homogeneous bulk `H(t) = N(t)` with `dτ/dt = N`; lock-in gives `H(4) = massUnit`
and `gEff(φ) = φ` at the Planck pole (`bulkHyperboloidDynamics`). -/
theorem referenceM_bulk_hyperboloid_dynamics_closed : Nonempty BulkHyperboloidDynamicsClosure :=
  ⟨bulkHyperboloidDynamics⟩

/-- **Closed:** joint sector + Casimir potential has unique minimum at `m = referenceM` and
shell/Casimir gradient drives agree (`referenceMJointClosureAction`). -/
theorem referenceM_joint_closure_action_closed : Nonempty ReferenceMJointClosureAction :=
  ⟨referenceMJointClosureAction⟩

/-- **Closed:** the now slice is a **causal diamond** apex chart; global `(α,γ)` glue is
evaluated at the event (`causalDiamondClosure`); lock-in diamond `(H,Φ,Ω_k,t,N,ξ)=(1,0,1,4,5,5). -/
theorem referenceM_causal_diamond_closed : Nonempty CausalDiamond.CausalDiamondClosure :=
  ⟨CausalDiamond.causalDiamondClosure⟩

/-- **Closed:** discrete shell-ladder baryogenesis `η(m) = Ω_k(m)·δ_E(m)` with strict climb to
lock-in and causal-diamond readout agreement (`baryogenesisShellLadderClosure`). -/
theorem referenceM_baryogenesis_shell_ladder_closed :
    Nonempty BaryogenesisShellLadder.BaryogenesisShellLadderClosure :=
  ⟨BaryogenesisShellLadder.baryogenesisShellLadderClosure⟩

/-- **Closed:** TUFT/Hopf Beltrami anchor — `λ_min(n) = d_n = n+1`, chart `m = n+1`,
heavy chart `= referenceM`, link to `S³` harmonic dimension (`tuftBeltramiAnchorClosure`). -/
theorem referenceM_tuft_beltrami_anchor_closed :
    Nonempty TuftBeltramiAnchor.TuftBeltramiAnchorClosure :=
  ⟨TuftBeltramiAnchor.tuftBeltramiAnchorClosure⟩

/-- **Closed:** TUFT chart row = Beltrami label on balanced diamond events; lock-in lapse
`N = λ_min + 1`; lepton readout = heavy-hopf TUFT readout × resonance descent
(`tuftBeltramiMassFunctionalClosure`). -/
theorem referenceM_tuft_beltrami_mass_functional_closed :
    Nonempty TuftBeltramiMassFunctional.TuftBeltramiMassFunctionalClosure :=
  ⟨TuftBeltramiMassFunctional.tuftBeltramiMassFunctionalClosure⟩

/-- **Closed:** extended detuned-shell resonance on outer ladder shells `15 → 33 → 58`;
structural charged-lepton ratios `μ/e = 4484/2499`, `τ/μ = 175/76`
(`generationResonanceLadderClosure`). -/
theorem referenceM_generation_resonance_ladder_closed :
    Nonempty GenerationResonanceLadder.GenerationResonanceLadderClosure :=
  ⟨GenerationResonanceLadder.generationResonanceLadderClosure⟩

/-- **Closed:** nested Hopf chart shells carry the 8×8 binding network with Hopf fiber weight
`n/(n+2)` in the coupling cell; contact < ladder; composite mass = Beltrami readout; heavy row =
proton lock-in binding `(3/5)·E_bind(4)` (`nestedHopfBindingClosure`). -/
theorem referenceM_nested_hopf_binding_closed :
    Nonempty NestedHopfBinding.NestedHopfBindingClosure :=
  ⟨NestedHopfBinding.nestedHopfBindingClosure⟩

/-- **Closed:** content-class composite traces (`l = 1/2/3` carrier slots) and binding
`E_bind = l · count · α_eff` (`contentClassCompositeTraceClosure`). -/
theorem referenceM_content_class_composite_trace_closed :
    Nonempty ContentClassCompositeTrace.ContentClassCompositeTraceClosure :=
  ⟨ContentClassCompositeTrace.contentClassCompositeTraceClosure⟩

/-- **Closed:** sector-specific nested Hopf binding — lepton two-slot trace, quark three-slot,
cross-sector `9/4` = `C_A/C_F` (`sectorNestedHopfBindingClosure`). -/
theorem referenceM_sector_nested_hopf_binding_closed :
    Nonempty SectorNestedHopfBinding.SectorNestedHopfBindingClosure :=
  ⟨SectorNestedHopfBinding.sectorNestedHopfBindingClosure⟩

/-- **Closed:** lepton absolute scale from sector nested Hopf binding. -/
theorem referenceM_lepton_absolute_scale_closed :
    Nonempty SectorNestedHopfBinding.SectorNestedHopfBindingClosure :=
  referenceM_sector_nested_hopf_binding_closed

/-- **Closed:** heavy-quark absolute scale from sector nested Hopf binding. -/
theorem referenceM_heavy_quark_absolute_scale_closed :
    Nonempty SectorNestedHopfBinding.SectorNestedHopfBindingClosure :=
  referenceM_sector_nested_hopf_binding_closed

/-- **Closed:** neutrino absolute scale — one-slot nested Hopf readout + horizon suppression. -/
theorem referenceM_neutrino_absolute_scale_closed :
    Nonempty NeutrinoAbsoluteScale.NeutrinoAbsoluteScaleClosure :=
  ⟨NeutrinoAbsoluteScale.neutrinoAbsoluteScaleClosure⟩

/-- **Bookkeeping (superseded):** lepton readout hypothesis at anchored `λ_min(n)`. -/
theorem referenceM_lepton_absolute_scale_bookkeeping :
    Nonempty LeptonAbsoluteScale.LeptonAbsoluteScaleClosure :=
  ⟨LeptonAbsoluteScale.leptonAbsoluteScaleClosure⟩

/-- **Bookkeeping (open frontier):** quark readout hypothesis with complexity prefactor. -/
theorem referenceM_heavy_quark_absolute_scale_bookkeeping :
    Nonempty HeavyQuarkAbsoluteScale.HeavyQuarkAbsoluteScaleClosure :=
  ⟨HeavyQuarkAbsoluteScale.heavyQuarkAbsoluteScaleClosure⟩

/-- **Closed:** `Ω_k` on the now slice is the continuous horizon chart ratio
(`omegaKPartial = omegaKChart`); harmonic shell sum bounds the discrete imprint integral;
strict increase below lock-in; lock-in normalisation `Ω_k = 1`. -/
theorem now_slice_omegaK_lattice_structure_closed :
    (∀ n, NowSliceFromLattice.harmonicSum n ≤ NowSliceFromLattice.curvatureIntegral n) ∧
    (∀ {n1 n2 : ℕ}, n1 < n2 → n2 ≤ referenceM →
      NowSliceFromLattice.omegaKPartial n1 < NowSliceFromLattice.omegaKPartial n2) ∧
    (∀ m, NowSliceFromLattice.omegaKPartial m =
      ContinuousHorizon.omegaKContinuous (ContinuousHorizon.xiOfShell m) ContinuousHorizon.xiLockin) ∧
    NowSliceFromLattice.omegaKPartial referenceM = 1 :=
  ⟨NowSliceFromLattice.harmonicSum_le_curvatureIntegral,
    fun h href => NowSliceFromLattice.omegaKPartial_strictMono h href,
    fun m => NowSliceFromLattice.omegaKPartial_eq_omegaKContinuous m,
    NowSliceFromLattice.omegaKPartial_at_referenceM⟩

theorem referenceM_now_slice_omega_k_bridge_closed :
    Nonempty NowSliceOmegaKBridge.NowSliceOmegaKBridgeClosure :=
  NowSliceOmegaKBridge.referenceM_nowSliceOmegaKBridge_closed

/-- **Closed (consolidated):** lock-in now slice, Ω_k chart bridge, bulk clock, causal diamond,
forward-null geodesics, HQVM geodesics, and covariant plasma O-Maxwell (`nowSliceClosure`). -/
theorem referenceM_now_slice_closure_closed :
    Nonempty NowSliceClosure.NowSliceClosure :=
  NowSliceClosure.referenceM_now_slice_closure_closed

/-- **Closed:** covariant plasma O-Maxwell on the HQVM chart — metric surrogate, Christoffel-form
divergence, flat-jet bridge, schematic EM-channel plasma current (`covariantOMaxwellClosure`). -/
theorem referenceM_covariant_plasma_omaxwell_closed :
    Nonempty CovariantOMaxwell.CovariantOMaxwellClosure :=
  CovariantOMaxwell.referenceM_covariant_plasma_omaxwell_closed

/-- **Closed:** non-comoving timelike/spacelike straight lines in the flat-jet HQVM chart
(`geodesicStraightLine_flatJet`, interval classification via `hqvmIntervalSq`). -/
abbrev referenceM_noncomoving_geodesics_closed :=
  HQVMGeodesics.referenceM_noncomoving_geodesics_closed

/-- **Closed:** HQVM Christoffel jet, comoving time geodesic, spatial lapse Christoffels, and
lock-in proper-time rate (`hqvmGeodesicsClosure`). -/
theorem referenceM_hqvm_geodesics_closed :
    Nonempty HQVMGeodesics.HQVMGeodesicsClosure :=
  HQVMGeodesics.referenceM_hqvm_geodesics_closed

/-- **Closed:** the strong sector occupies exactly four octonion channels, and the
three force sectors `1 + 3 + 4` partition the `8` carrier channels — no independent
gluon field is added. -/
theorem strong_sector_channels_closed :
    strongComponents.card = 4 ∧
    emComponents.card + weakComponents.card + strongComponents.card = Foundation.carrierMultiplicity :=
  ⟨strongComponents_card, sector_card_sum_eq_carrier⟩

/-- **Closed:** the colour Casimirs follow from `N_c = 3`: `C_A/C_F = 9/4` (and
`C_F = 4/3`), derived rather than fit. -/
theorem colour_casimir_ratio_closed :
    casimirAdjoint / casimirFundamental colourCount = (9 : ℝ) / 4 ∧
    casimirFundamental 3 = (4 : ℝ) / 3 :=
  ⟨casimir_ratio_nine_quarters, casimirFundamental_three⟩

/-- **Closed:** quark electric charges are quantized as loop multiplicity over the
colour rank (`2/3`, `−1/3`), and the quark:charged-lepton **wave-complexity** ratio is
exactly the colour **Casimir** ratio `C_A/C_F = 9/4` — charge quantization and the
non-abelian splitting weight share one integer, `N_c = 3`. -/
theorem quark_charge_and_complexity_closed :
    quarkElectricCharge .upLike = 2 / 3 ∧
    quarkElectricCharge .downLike = -1 / 3 ∧
    intrinsicWaveComplexity .quark / intrinsicWaveComplexity .chargedLepton
      = casimirAdjoint / casimirFundamental colourCount := by
  refine ⟨quarkElectricCharge_up, quarkElectricCharge_down, ?_⟩
  rw [intrinsicWaveComplexity_quark_over_chargedLepton, casimir_ratio_nine_quarters]

/-- **Closed:** exactly three fermion generations from the three 8-dim `Spin(8)` slots
permuted by the order-3 triality cycle, with `48` chiral Weyl slots — generation count
is a carrier-algebra theorem, not an input. -/
theorem three_generations_closed :
    Fintype.card Algebra.So8RepIndex = 3 ∧
    (∀ r : Algebra.So8RepIndex, Algebra.trialityCycle (Algebra.trialityCycle2 r) = r) ∧
    Algebra.chiralSlotCount = 48 :=
  ⟨Algebra.card_so8RepIndex_eq_three, Algebra.triality_cycle_order_3, Algebra.chiralSlotCount_eq_48⟩

/-- **Closed:** the embedded SM is anomaly-free — every finite trace vanishes per
generation and the sum over the three triality generations is zero. -/
theorem sm_anomaly_free_closed :
    (Algebra.u1YCubicTrace = 0 ∧ Algebra.gravU1YTrace = 0 ∧ Algebra.su3SqU1YTrace = 0 ∧
      Algebra.su2SqU1YTrace = 0 ∧ Algebra.su3CubicTrace = 0 ∧ Algebra.su2CubicTrace = 0) ∧
    ∑ r : Algebra.So8RepIndex, Algebra.anomalyCoeff r = 0 :=
  ⟨Algebra.sm_anomaly_free_one_generation, Algebra.anomaly_free_three_generations⟩

/-- **Closed:** neutrino maximal mixing `θ = π/4` (`sin 2θ = 1`) from the lock-in shell
`4 = 2²` and the CP phase `δ = π/5 = (γ/2)π` — both dimensionless geometry. -/
theorem neutrino_mixing_closed :
    neutrinoMixingAngle = Real.pi / 4 ∧
    Real.sin (2 * neutrinoMixingAngle) = 1 ∧
    neutrinoCPPhase = Real.pi / 5 :=
  ⟨neutrinoMixingAngle_eq_pi_div_four, neutrino_maximal_mixing, neutrinoCPPhase_eq_pi_div_five⟩

/-- **Closed:** strong binding factors as trapped zero-point budget times normalised
SO(8) selection — strong binding *is* trapped Casimir zero-point, not gluon exchange. -/
theorem trapped_casimir_factorisation_closed (m : ℕ) (k : So8Index) (c : ℝ) :
    bindingCouplingAtShell m k c = trappedCasimirEnergy m / 4 * normalizedSelection m c :=
  bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection m k c

/-- **Closed:** the spine running coupling is the bare coupling times the unified
curvature log kernel at the ladder coordinate, and contact amplification is strictly
below ladder amplification at every shell. -/
theorem curvature_log_kernel_closed (m : ℕ) (c : ℝ) (hc : 0 < c) :
    oneOverAlphaEffAtShell m c = oneOverAlphaBare * curvatureLogKernel (ladderArg m) c ∧
    curvatureLogKernel (contactArg m) c < curvatureLogKernel (ladderArg m) c :=
  ⟨oneOverAlphaEffAtShell_eq_bare_mul_ladderKernel m c, contactKernel_lt_ladderKernel m c hc⟩

/-- **Closed:** global `su(3)` chart Lie law on all eight half–Gell–Mann generators. -/
theorem su3_lie_algebra_closed (a b : Fin 8) :
    Algebra.StrongColor.lieBracketMat3
        (Algebra.StrongColor.halfGellMannFull a)
        (Algebra.StrongColor.halfGellMannFull b) =
      Complex.I • ∑ c : Fin 8,
        (Algebra.StrongColor.su3fStructure a b c : ℂ) • Algebra.StrongColor.halfGellMannFull c :=
  Algebra.StrongColor.halfGellMannFull_lieBracket_eq_I_smul_f_sum a b

/-- **Closed:** non-abelian matrix elements factor as network emission × `C_A/C_F`. -/
theorem non_abelian_matrix_element_closed (m : ℕ) (w : NetworkWeight) (k : So8Index) (c : ℝ) :
    NonAbelianMatrixElement.nonAbelianMatrixElement m w k c =
      NonAbelianMatrixElement.generatorEmissionWeight m w k c *
        NonAbelianMatrixElement.colourChartFilter ∧
    NonAbelianMatrixElement.colourChartFilter = (9 : ℝ) / 4 :=
  ⟨NonAbelianMatrixElement.nonAbelianMatrixElement_eq_emission_times_filter m w k c,
    NonAbelianMatrixElement.colourChartFilter_eq_nine_quarters⟩

/-- **Closed:** lock-in `4+4` carrier chart, triality/colour integer match, complex structure `J`,
and bundled strong-sector discharge (`nonAbelianDynamicsClosure`). -/
theorem referenceM_non_abelian_dynamics_closed :
    Nonempty NonAbelianDynamics.NonAbelianDynamicsClosure :=
  NonAbelianDynamics.referenceM_non_abelian_dynamics_closed

/-- **Closed:** the `su(3)` chart lifts to `8 × 8` on the carrier with full Lie law. -/
theorem su3_carrier_embed_closed (a b : Fin 8) :
    Algebra.StrongColor.lieBracketMat8
        (Algebra.StrongColor.colorGellMannEmbed (Algebra.StrongColor.halfGellMannFull a))
        (Algebra.StrongColor.colorGellMannEmbed (Algebra.StrongColor.halfGellMannFull b)) =
      Complex.I • ∑ c : Fin 8,
        (Algebra.StrongColor.su3fStructure a b c : ℂ) •
          Algebra.StrongColor.colorGellMannEmbed (Algebra.StrongColor.halfGellMannFull c) :=
  Algebra.StrongColor.halfGellMannEmbed_carrier_lieBracket_eq_I_smul_f_sum a b

end HqivSpine.Physics
