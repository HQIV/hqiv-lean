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
import HqivSpine.Physics.ContinuousHorizon
import HqivSpine.Algebra.StrongColorSu3LieLaw
import HqivSpine.Algebra.StrongColorEmbed
import HqivSpine.Physics.NonAbelianMatrixElement
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
ladder, shell-ledger `Φ`, discrete `Ω_k` ratio, and lock-in readout `(φ, Φ, Ω_k, t) = (1, 0, 1, 4)`.
Still open: dynamical `H(t)` from the bulk hyperboloid and continuous–discrete identification
on all horizons. -/
def nowSliceCurvatureFrontier : DerivationFrontier where
  name := "now_slice_curvature_closure"
  obligation :=
    "Complete the now-slice closure: dynamical H(t) from the bulk hyperboloid and " ++
    "continuous–discrete Ω_k on all horizons. Discrete (φ, Φ, Ω_k) from the null " ++
    "lattice are in NowSliceFromLattice."
  collapsesToNowSlice := false

/-- Heavy-quark absolute scale: derive heavy-quark constituent inputs from the
now-scale `massUnit` times dimensionless shell/Beltrami ratios, with no GeV literal. -/
def heavyQuarkScaleFrontier : DerivationFrontier where
  name := "heavy_quark_absolute_scale"
  obligation :=
    "Derive heavy-quark constituent values from the now-scale and shell/Beltrami " ++
    "ratios; top/bottom GeV literals are external (excluded from this spine)."
  collapsesToNowSlice := true

/-- Lepton absolute scale: the generation *ratios* are derived (Beltrami spectrum);
the absolute lepton scale as a now-scale multiple is open. -/
def leptonAbsoluteScaleFrontier : DerivationFrontier where
  name := "lepton_absolute_scale"
  obligation :=
    "Fix the absolute charged-lepton scale as a now-scale multiple; ratios 4/3 " ++
    "(τ:μ) and 3/2 (μ:e) are already derived from λ_min(n)=n+1."
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

/-- Baryon-asymmetry absolute scale: at lock-in the lattice gives `η = δ_E(referenceM)`
(`Ω_k = 1` from `NowSliceFromLattice`); sub-horizon shells still need the discrete
`Ω_k(m)` ratio. Comparison to `η_observed` remains quarantined. -/
def baryonAsymmetryScaleFrontier : DerivationFrontier where
  name := "baryon_asymmetry_absolute_scale"
  obligation :=
    "Lock-in η = δ_E(referenceM) is closed from the lattice (Ω_k = 1); extend the " ++
    "absolute scale to sub-lock-in shells via discrete Ω_k(m), and compare to η_observed " ++
    "only in the comparison layer."
  collapsesToNowSlice := true

/-- Non-abelian dynamics: the colour Casimirs, four-channel mask, full `su(3)` chart
(`f^{abc}` + global Lie law), matrix-element pipeline, and `8 × 8` complex carrier embed are
derived in `StrongColorSu3`, `StrongColorSu3LieLaw`, `StrongColorEmbed`, and
`NonAbelianMatrixElement`. Real-skew closure is in `SkewChartBridge`: `su(3) ↪ 𝔰𝔬(6)` with
transported `f^{abc}` law, plus general `𝔰𝔬(m) ↪ 𝔰𝔬(n)` padding (`skewPad`). Still optional:
Spin(8) triality / preferred complex structure on the octonion carrier. -/
def nonAbelianDynamicsFrontier : DerivationFrontier where
  name := "non_abelian_matrix_elements"
  obligation :=
    "Optional: identify a Spin(8) triality-compatible complex structure tying the complex " ++
    "`colorGellMannEmbed` chart to a preferred real `𝔰𝔬(8)` slice. Closed: chart, pipeline, " ++
    "carrier Lie law, and real `su(3) ⊂ 𝔰𝔬(6)` (`SkewChartBridge`)."
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
  [nowSliceCurvatureFrontier, heavyQuarkScaleFrontier, leptonAbsoluteScaleFrontier,
    baryonAsymmetryScaleFrontier, nonAbelianDynamicsFrontier,
    screenedAlphaChemistryFrontier,
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

/-- **Closed:** the charged-lepton generation steps are pinned dimensionless ratios. -/
theorem lepton_generation_ratios_closed :
    leptonSpectralRatio 3 2 = (4 : ℝ) / 3 ∧ leptonSpectralRatio 2 1 = (3 : ℝ) / 2 :=
  ⟨leptonSpectralRatio_tau_mu, leptonSpectralRatio_mu_e⟩

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

/-- **Closed:** discrete `Ω_k` is bounded below by the harmonic shell sum and strictly
increases below lock-in; the continuous-ξ chart shares lock-in normalisation and parallel
strict monotonicity on integer shells. -/
theorem now_slice_omegaK_lattice_structure_closed :
    (∀ n, NowSliceFromLattice.harmonicSum n ≤ NowSliceFromLattice.curvatureIntegral n) ∧
    (∀ {n1 n2 : ℕ}, n1 < n2 → n2 ≤ referenceM →
      NowSliceFromLattice.omegaKPartial n1 < NowSliceFromLattice.omegaKPartial n2) ∧
    ContinuousHorizon.omegaKContinuous ContinuousHorizon.xiLockin ContinuousHorizon.xiLockin = 1 :=
  ⟨NowSliceFromLattice.harmonicSum_le_curvatureIntegral,
    fun h href => NowSliceFromLattice.omegaKPartial_strictMono h href,
    NowSliceFromLattice.omegaKContinuous_agrees_at_lockin⟩

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
