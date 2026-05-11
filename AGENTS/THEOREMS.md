# Theorems and defs with usable outputs

Lean names are given in **fully qualified** form where helpful; short names assume `open Hqiv` or the module namespace as documented. Use `#check` / `grep` in-repo for the exact type.

**Status context:** this file is the **name index** for high-value lemmas; it is **not** exhaustive. For **what is still open** (ray theorems, classical Hodge, modularity, …), read [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) and [HODGE_HQIV_NARRATIVE.md](./HODGE_HQIV_NARRATIVE.md) §5. When you add a row here, prefer **cross-cutting** results (see roadmap **Proof priority**).

## Clay Millennium (Lean Dojo) ↔ HQIV bridge

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Bridge.LeanDojo.yangMills_millennium_of_witness` | Sufficient: from `qft` + `Δ` + the three `MillenniumYangMills` conjuncts ⇒ `YangMillsExistenceAndMassGap G`. (Does *not* construct `QuantumYangMillsTheory` from HQIV.) |
| (doc only) | Intended HQIV↔**spectral mass** line: `Hqiv.Physics.HarmonicLadderMass`, `Hqiv.Physics.ConservedContentMassBridge`, baryogenesis/shell readouts in `BaryogenesisCore` / `TrialityRapidityWellEquivalence` — *not* the separate SM–GR unification `Prop` bundle. |
| `Hqiv.Bridge.LeanDojo.navier_stokes_millennium_of_fefferman_{A,B,C,D}` | Each disjunct of the Fefferman (A)–(D) union is enough to prove `NavierStokesMillenniumTarget`. (HQIV does not yet prove any of A–D.) |
| | Build: `lake build HQIVClayMillennium`; see `Hqiv/Bridge/LeanDojoClayMillennium.lean` and [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md). |

## Discrete light cone (`Hqiv.Geometry.OctonionicLightCone`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.latticeSimplexCount` | Stars-and-bars count on the 3D null lattice at shell `m`. |
| `Hqiv.latticeSimplexCount_eq` | Closed form `latticeSimplexCount m = (m+2)(m+1)`. |
| `Hqiv.cumLatticeSimplexCount_closed` | Hockey-stick / closed form for cumulative count. |
| `Hqiv.available_modes` | ℝ-valued mode budget at shell `m` (4·(m+2)(m+1)); ties to octonion factor via `available_modes_octonion`. |
| `Hqiv.new_modes` | Incremental new modes; `new_modes_succ` relates successive shells. |
| `Hqiv.alpha` / `Hqiv.alpha_eq_3_5` | **Sole** HQIV curvature-imprint exponent: `α = 3/5` (proved); physical derivation in companion HQIV + Brodie 2026 (see `AGENTS/ASSUMPTIONS.md` §1b). |
| `Hqiv.latticeAlphaRatio_eq_alpha` | Discrete ratio equals `α` for every `n`. |
| `Hqiv.alpha_gamma_forced_pair` / `Hqiv.lattice_imprint_ratio_forced_three_fifths` | `AlphaGammaForcedByLattice`: joint uniqueness `α = 3/5`, `γ = 2/5`, `α + γ = 1`; per-shell imprint ratio equals `3/5`. |
| `Hqiv.curvature_norm_*` / `Hqiv.deltaE_eq` | Curvature norm and δ_E imprint from the combinatorial structure. In particular, `curvature_norm_determined_by_structure` / `curvature_norm_from_lightcone_axiom` pin the canonical norm to `(cube directions)^(octonion dim) * unitCubeHalfDiagonal = 6^7 * sqrt(3)`, while `curvature_norm_quaternionicCandidate_exact`, `curvature_norm_combinatorial_eq_1296_mul_quaternionicCandidate`, `deltaE_eq_1296_mul_deltaE_quaternionicCandidate`, and `deltaE_ne_deltaE_quaternionicCandidate_of_shell_shape_ne_zero` give the parallel quaternionic comparison: the `H`-sector `6^3 * sqrt(3)` candidate undershoots the current shell imprint by a rigid factor `1296`, so it does not reproduce the canonical HQIV δ_E ladder on any shell with nonzero shape. |
| `Hqiv.curvature_integral_ge_harmonic` / `curvature_integral_le_harmonic_mul_log` | Analytic sandwich for growth of curvature integral. |
| `Hqiv.omega_k_at_horizon` / `Hqiv.omega_k_partial_tends_to_atTop` | Horizon-indexed curvature ratio and asymptotic behaviour. |

## HQVM metric (`Hqiv.Geometry.HQVMetric`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.HQVM_lapse` | ADM lapse `N = 1 + Φ + φ t` (informational-energy / monogamy story in module doc). |
| `Hqiv.timeAngle` | `φ * t` piece tied to horizon coupling in docs. |
| `Hqiv.gamma_HQIV` / `Hqiv.gamma_eq_2_5` | **Sole** HQIV monogamy / horizon-overlap coefficient: `γ := 1 − α`, proved `γ = 2/5`; same external provenance as `α` (companion HQIV + Brodie 2026). |
| `Hqiv.G_eff` / Friedmann-related defs | Effective `G` as function of `φ`; homogeneous-limit statements in-file. |

## M6 gravity readout packaging (`Hqiv.Physics.HQIVGravityReadoutScalars`)

Roadmap **M6 — No fundamental graviton target**: not a QG metaphysics theorem, but an explicit record that the HQVM **interface** is scalar-only (see module doc).

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.HQVMGravityLapseArgumentTuple` / `Hqiv.Physics.HQVM_lapse_eq_tuple` | The lapse API is exhausted by three reals `(Φ, φ, t)`. |
| `Hqiv.Physics.linearizedHQVM_lapse_eq_components` / `Hqiv.Physics.linearizedHQVM_g_tt_depends_on_scalar_deltaN` | First-order lapse and linearized `g_tt` use only declared scalar increments (one `δN` branch for `g_tt`). |
| `Hqiv.Physics.HQIVFormalGravitonPolarizationIdx` / `HQIVFormalGravitonPolarizationIdx_elim` | Deliberately empty polarization index (`Fin 0`) at this formalization layer. |
| `Hqiv.Physics.SMGaugeCarrierMat8` | Type alias for `8 × 8` real matrices (SO(8) generator bookkeeping scale); contrasts with scalar `ℝ` lapse values in prose + docstrings. |
| `Hqiv.Physics.latticeSimplexCount_constant_in_observerTime` / `shellSurface_constant_in_observerTime` / `detunedShellSurface_constant_in_observerTime` | Null-lattice readout data at fixed `m` is **not** a function of coordinate time `t` in the API (constant dummy-`ℝ` wrappers). |
| `Hqiv.Physics.timeAngle_diff` / `HQVM_lapse_diff_fixedPotentials` / `HQVM_lapse_affine_in_coordinateTime` | With fixed `(Φ, φ)`, lapse and `timeAngle` differences are **linear in `Δt`**; lapse is affine in `t`. |
| `Hqiv.Physics.HQVM_g_tt_eq_neg_sq_lapse` | Timelike coefficient along the chart is `-N²` with `N = HQVM_lapse` only (comoving-clock / proper-time normalization surface). |

## Algebra-first O-Maxwell ladder (`Hqiv.Physics.OMaxwellAlgebraSeed`, `Hqiv.Physics.ModifiedMaxwell`, `Hqiv.Physics.PromotedOMaxwell`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.algebraicMaxwellSeedSet` | Lightweight algebraic seed set `G₂ ∪ {Δ}` used by the refactored Maxwell ladder. |
| `Hqiv.algebraicMaxwellHBlock` / `Hqiv.algebraicMaxwellParentGenerator` | The `4 × 4` Cayley-Dickson / H-sector block cut from the existing `so8Generator` package and the parent `8 × 8` generator it came from. |
| `Hqiv.algebraicMaxwellParentGenerator_mem_seedSpan` | The parent generator for the algebra-first H block lies in the existing `span ℝ (range so8Generator)` carrier. |
| `Hqiv.algebraicMaxwellProjectionSlot` / `Hqiv.algebraicMaxwellCouplingLog` | Positive algebra-first Maxwell scalar slot and its logarithmic correction term; this is now primary, with `phi_of_T` only as an optional projection/readout. |
| `Hqiv.AlgebraicMaxwellProjectionHypothesis` / `Hqiv.algebraicMaxwellCouplingLog_eq_phi_of_T` | Explicit bridge recovering the old shell/temperature presentation `log (phi_of_T (T m))` from the algebra-first slot. |
| `Hqiv.delta_theta_prime_eq_arctan_mul_pi_div_two` / `Hqiv.tipping_delta_theta_zero` | `δθ′(E′) = arctan(E′)·(π/2)` and the rest/zero-field value `δθ′(0)=0`; the theorem now lives in `OMaxwellAlgebraSeed`, not `ModifiedMaxwell`. |
| `Hqiv.algebraicMaxwellRapiditySeed_zero` | In the rest / non-relativistic sanity limit, the algebraic rapidity contribution vanishes. |
| `Hqiv.O_reduces_to_classic_Maxwell_in_H` / `Hqiv.classic_Maxwell_in_H_under_flat_limit` | The O-equation restricted to the quaternionic `H` sector collapses to classic Maxwell on a flat constant-`φ` background. |
| `Hqiv.algebraic_nonrelativistic_limit_reduces_to_classic_Maxwell_in_H` | Algebra-first sanity theorem: at zero rapidity seed, the quaternionic sector still reduces to classic Maxwell. |
| `Hqiv.PromotedOMaxwellAlgebraicSlotHypotheses` / `Hqiv.PromotedOMaxwellGradientHypotheses` / `Hqiv.PromotedOMaxwellProjectionToPhiOfT` | The promoted bridge now separates algebraic-slot identification, chart-gradient identification, and optional recovery of the legacy `phi_of_T` form. |
| `Hqiv.promotedOMaxwellResidual_eq_EL_coordsField` / `Hqiv.promotedOMaxwellResidual_eq_covariantResidual` | Main bridge theorems now target the algebraic Maxwell slot first. |
| `Hqiv.promotedOMaxwellResidual_eq_legacyShellProjected` | Second-stage theorem recovering the old shell-based `phi_of_T` correction form. |

## SO(8) H-block bridge (`Hqiv.Algebra.SO8ClosureAbstract`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Algebra.modifiedMaxwellHMatrix_eq_algebraicMaxwellHBlock` | The old `modifiedMaxwellHMatrix` is definitionally the same H-block used by the new algebra-first Maxwell seed. |
| `Hqiv.Algebra.em_magnetic_block_is_algebraicMaxwellHBlock` | Heavy-side bridge theorem: the old EM/H block statement can be read directly as the new algebra-first Maxwell block. |

## Strong color / `su(3)` triplet chart (`Hqiv.Physics.QuarkColorCarrierGaugeScaffold`, `StrongColorSu3ChartClosure`, `StrongColorCarrierClosure`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.colorHalfGellMannFull` / `Hqiv.Physics.colorGellMannLambdaFull` | Eight Hermitian Gell–Mann matrices on the active `3 × 3` chart and half-generators `T^a = λ^a / 2`. |
| `Hqiv.Physics.colorSu3fStructure` / `Hqiv.Physics.colorSu3fSorted` / `Hqiv.Physics.colorSu3fSorted_congrProofs` | Totally antisymmetric real structure constants `f^{abc}` (sorted-table convention) with proof-irrelevance for strict-inequality witnesses. |
| `Hqiv.Physics.colorTripletCovariantTermFull` | Eight-channel schematic covariant slot built from all `T^a`. |
| `Hqiv.Physics.colorTripletB` / `Hqiv.Physics.colorTripletB_conjTranspose_mul_self` | Orthonormal `8 × 3` embed `B` with `BᴴB = 1₃` and `B.mulVec ψ = colorTripletInclCoeff ψ`. |
| `Hqiv.Physics.colorGellMannEmbed` / `colorGellMannEmbed_mul` / `colorGellMannEmbed_lieBracket` | Conjugate `3 × 3` operators to `8 × 8` on `WeakComplexOctonionCarrier`, mirroring the Pauli embed API. |
| `Hqiv.Physics.lieBracketMat₃_neg_swap` | Antisymmetry of the matrix commutator bracket on `Matrix (Fin 3) (Fin 3) ℂ`. |
| `Hqiv.Physics.colorGellMannEmbed_chart_lieBracket_smul` | **Scaffold:** packages any future chart identity `lieBracketMat₃ A B = I • R` into the same `I •` normalization on the carrier (see `StrongColorCarrierClosure` module docstring). |
| (optional target) | `lake build HQIVStrongColorSu3Certificate`: generated `@[simp]` lemmas for **nonzero** `colorSu3fStructure` atoms (`Hqiv.Physics.StrongColorSu3fStructureSimp`, regen `scripts/gen_strong_color_su3_f_simp.py`). **Not** in the default `HQIVLEAN` glob. |
| (still open) | Full chart Lie law `∀ a b, lieBracketMat₃ (colorHalfGellMannFull a) (colorHalfGellMannFull b) = I • ∑ c, (colorSu3fStructure a b c : ℂ) • colorHalfGellMannFull c` for all eight generators—layer on the certificate table + `Fin.sum_univ_eight` / `Finset.sum_eq_single` (see `StrongColorSu3ChartClosure` / `StrongColorSu3LieCertificate` docs). |

## SM–GR unification (`Hqiv.Physics.SM_GR_Unification`, namespace `Hqiv`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.alpha_derived` | Same canonical `alpha = 3/5` (`SM_GR_Unification`; provenance: companion HQIV + Brodie 2026). |
| `Hqiv.gamma_derived` | Same canonical `gamma_HQIV = 2/5`. |
| `Hqiv.alpha_GUT_eq_1_42` | `α_GUT = 1/42`. |
| `Hqiv.one_over_alpha_EM_derived` / `Hqiv.one_over_alpha_EM_derived_closed_form` | `1/α_eff` at `φ(m)` expanded to `42 * (1 + c·(3/5)·log(2(m+1)+1))` (no extra lattice parameters). |
| `Hqiv.electroweakPhiShell` / `Hqiv.one_over_alpha_EM_derived_electroweak_closed` | Electroweak shell `referenceM+1` → `log` argument `13`. |
| `Hqiv.one_over_alpha_EM_at_MZ_eq` | Numeric `1/α_EM(M_Z) = 127.9` as `rfl` (paper-aligned witness; see `one_over_alpha_EM_derived_*` for symbolic derivation). |
| `Hqiv.HQIV_satisfies_YangMills_SM_GR_Unification` | Main “unification satisfied” proposition bundle. |
| `Hqiv.sm_constants_at_now_derived` | Packaging of derived-at-now constants (see theorem statement). |
| `Hqiv.higgs_mass_from_proton_mass` / `Hqiv.higgs_mass_numerical` | Higgs scale from proton anchor + numeric literal. |
| `Hqiv.m_proton_MeV_in_interval` / `Hqiv.m_neutron_MeV_in_interval` | Baryon mass intervals in MeV (paper-style). |

## Outer-horizon mass witnesses (`Hqiv.Physics.DerivedGaugeAndLeptonSector`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.outerClosureScale` / `Hqiv.outerClosureScale_eq_reference_step` | Boson / neutrino outer-closure **gauge** scale from `T_lockin`, the next outer-horizon surface, monogamy lift, and the EW gauge quantum lift (`ewGaugeSectorQuantumLift`). |
| `Hqiv.M_W_derived` / `Hqiv.M_Z_derived` / `Hqiv.m_H_derived` / `Hqiv.raw_local_boson_layers_from_outerClosureScale` | Boson witnesses: `W = g_SU2 * outerClosureScale` with lifted vev; `Z = (g_SU2 + g_U1) * outerClosureScale` (no PDG weak-mixing import); `H = 2 * vacuumExpectationValueScalar` with scalar lift `3 + 2`. |
| `Hqiv.M_Z_derived_eq_W_times_one_plus_gamma` | `M_Z_derived = (1 + gammaDerived) * M_W_derived` from the coupling sum on the same vev. |
| `Hqiv.boson_witness_M_W` / `Hqiv.boson_witness_M_Z` / `Hqiv.boson_witness_m_H` / `Hqiv.boson_witness_values` | Closed forms: `M_W_derived = 392/5` GeV, `M_Z_derived = 2744/25` GeV, `m_H_derived = 588/5` GeV. |
| `Hqiv.raw_ew_boson_W_H_below_PDG_Z_above` | Tree-level comparison to PDG centrals: `W` and Higgs below; `Z` closure **above** `M_Z` PDG (naive `g+g'` line, no mixing). |
| `Hqiv.m_nu_e_derived` / `Hqiv.m_nu_mu_derived` / `Hqiv.m_nu_tau_derived` | Neutrino witnesses built from `M_Z_derived` and outer-surface suppression. |
| `Hqiv.m_nu_e_derived_eq_suppression_times_M_Z` | Electron-neutrino witness as `outerHorizonNeutrinoSuppression * M_Z_derived`. |
| `Hqiv.neutrinoDeltaMSquared_*_derived` / `neutrinoDeltaMSquared_*_derived_eq` | Squared-mass splittings from the ν ladder, expanded in `outerHorizonNeutrinoSuppression` and `M_Z_derived`. |
| `Hqiv.neutrinoOscillationPhase` / `Hqiv.neutrinoSurvivalProb_twoFlavor` | Two-flavor vacuum phase `Δm² L/(4E)` and `P_{ee} = 1 - sin²(2θ) sin²(phase)`; `θ` is an explicit parameter (like nuclear `ℳ` in `beta_decay_rate`), not a PMNS import. |
| `Hqiv.Physics.Omega_referenceM_eq_two` / `Hqiv.Physics.neutrinoMixingAngle_fanoPlane_lockin` / `Hqiv.Physics.neutrinoMixingAngle_fanoPlane_lockin_eq` | Lock-in shell has `Ω referenceM = 2`; Fano-plane intrinsic axis angle fixes `θ = π/4` via `Hqiv.Algebra.intrinsicShellAxisAngle_of_Omega_two`. |
| `Hqiv.Physics.neutrinoCPPhase_skew_from_rapidity` / `Hqiv.Physics.neutrinoCPPhase_skew_from_rapidity_eq` | Monogamy rapidity skew `(γ_derived/2)·π` on the oscillation phase; equals `π/5` at the ladder `α = 3/5`. |
| `Hqiv.Physics.neutrinoSurvivalProb_fanoLockin_twoFlavor` / `Hqiv.Physics.neutrinoSurvivalProb_fanoLockin_twoFlavor_withRapidityCP` | `P_{ee}` with Fano-locked `θ` and optional CP phase shift in `sin(phase + skew)`. |
| `Hqiv.ageMassCorrection` / `Hqiv.ageMassCorrection_value` / `Hqiv.ageMassCorrection_gt_one` | Published wall-clock / apparent-age mass rescaling factor `51.2 / 13.8`; theorem-backed as strictly bigger than `1`, so it is a genuine comparison-layer amplification rather than a neutral rewrite. |
| `Hqiv.M_W_ageAdjusted` / `Hqiv.M_Z_ageAdjusted` / `Hqiv.m_H_ageAdjusted` | Boson witnesses after multiplying by the published age ratio. |
| `Hqiv.age_adjusted_boson_witness_values` / `Hqiv.published_age_layer_eq_mul_raw` | Age-adjusted witnesses as `raw * ageMassCorrection` and the generic multiplicative layer identity. |
| `Hqiv.age_adjusted_boson_masses_exceed_PDG_centrals` | After EW-scale quantum lifts, multiplying by the published age ratio **overshoots** PDG centrals (the age layer is not an EW refinement at this scale). |
| `Hqiv.published_age_ratio_exceeds_multiplicative_PDG_closure_for_W` | The age ratio exceeds the multiplicative factor needed to match `M_W` alone — consistent with “age compression” not being the right handle near the electroweak scale. |
| `Hqiv.bosonLocalizationEnergyLowerBound` / `Hqiv.bosonLocalizationEnergyLowerBound_value` / `Hqiv.bosonLocalizationEnergyLowerBound_pos` / `Hqiv.horizon_localization_layer_eq_add_raw` | Local horizon layer from `Δx ≤ Θ_local`: the minimal correction is `1 / Θ_local = 6` at the boson-closure shell, and the horizon-localized mass is exactly the raw witness plus that local term. |
| `Hqiv.M_W_ageAndHorizonAdjusted` / `Hqiv.M_Z_ageAndHorizonAdjusted` / `Hqiv.m_H_ageAndHorizonAdjusted` / `Hqiv.age_and_horizon_layer_eq_age_of_horizon_localized` / `Hqiv.age_and_horizon_layer_eq_age_plus_localization` | Boson witnesses after the combined age-rescaling and horizon-localization layer; packaged both as “age applied to the horizon-localized mass” and as “age-adjusted raw mass plus age-adjusted localization term.” |
| `Hqiv.M_W_raw_lt_age_lt_ageAndHorizon` / `Hqiv.M_Z_raw_lt_age_lt_ageAndHorizon` / `Hqiv.m_H_raw_lt_age_lt_ageAndHorizon` | Clean separation of comparison layers: for each boson witness, `raw local < published-age layer < age+horizon layer`. |

## Charged-lepton shell interface (`Hqiv.Physics.LeptonGenerationLockin`, `Hqiv.Physics.ChargedLeptonResonance`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.OuterHorizonLeptonShellSelection` | Minimal **exact-shell** interface for a charged-lepton rule: `muonShell`, `electronShell`, and the two strict inequalities from the heavy τ shell. Likely still a proxy layer if the physics is upgraded to shell-band / support-region occupancy. |
| `Hqiv.Physics.leptonModalFrequencySpec` / `Hqiv.Physics.leptonModalFrequencySpec_quarterPhase_eq_horizonQuarter` / `Hqiv.Physics.leptonModalFrequencySpec_detuning_affine` / `Hqiv.Physics.outerHorizonLeptonShellSelectionFromModal` / `Hqiv.Physics.currentOuterHorizonLeptonShellSelection_eq_modal_readout` | Lepton lock-in now has an explicit modal-frequency/horizon wrapper: the τ/lock-in line exports a modal-first spec whose quarter-phase matches `horizonQuarterPeriod` and whose detuning hook is affine; current μ/e picks are documented as readouts from that modal layer (without changing existing threshold proofs). |
| `Hqiv.Physics.tauModalFrequencySpec` / `Hqiv.Physics.muonModalFrequencySpec` / `Hqiv.Physics.electronModalFrequencySpec` / `Hqiv.Physics.resonance_k_tau_mu_eq_modal_readout` / `Hqiv.Physics.resonance_k_mu_e_eq_modal_readout` / `Hqiv.Physics.m_mu_from_lockin_surface_candidate_eq_tau_over_modal_readout` / `Hqiv.Physics.m_e_from_lockin_surface_candidate_eq_mu_over_modal_readout` | `ChargedLeptonResonance.lean` now consumes the modal layer explicitly: τ/μ/e each expose a modal-frequency/horizon wrapper, the two resonance ratios are identified with modal geometric-step readouts, and the lock-in candidate ladder (`τ → μ → e`) is packaged as repeated modal relaxations rather than only raw shell arithmetic. |
| `Hqiv.Physics.LeptonResonanceGlobalDetuning.tauModalFrequencySpec` / `Hqiv.Physics.LeptonResonanceGlobalDetuning.muonModalFrequencySpec` / `Hqiv.Physics.LeptonResonanceGlobalDetuning.kTauMu_eq_modal_geometricStepReadout` / `Hqiv.Physics.LeptonResonanceGlobalDetuning.kMuE_eq_modal_geometricStepReadout` | `LeptonResonanceGlobalDetuning.lean` is now the preferred lightweight lepton modal/horizon spine: it exposes τ/μ/e modal wrappers and identifies the obstruction-layer surface ratios with modal geometric-step readouts without importing the thicker resonance-anchor phenomenology. |
| `Hqiv.Physics.outerClosureModalFrequencySpec` / `Hqiv.Physics.neutrinoSuppressionModalFrequencySpec` / `Hqiv.Physics.outerClosureModalFrequencySpec_quarterPhase_eq_horizonQuarter` / `Hqiv.Physics.outerClosureModal_detunedSurfaceReadout` | `DerivedGaugeAndLeptonSector.lean` now also serves as a lightweight outer-horizon modal package: the boson closure shell and neutrino-suppression shell each expose quarter-period-compatible modal wrappers, keeping shell indices as readout/bookkeeping while the closure witnesses stay on the outer-horizon side. |
| `Hqiv.Physics.leptonResonanceThresholdPred` / `Hqiv.Physics.firstShellAtOrAboveResonanceThreshold` / `Hqiv.Physics.firstShellAtOrAboveResonanceThreshold_spec` / `Hqiv.Physics.firstShellAtOrAboveResonanceThreshold_min` | The new threshold-selector core: the first shell after a given anchor whose geometric resonance step clears a chosen charged-lepton comparison threshold, packaged with its threshold witness and minimality theorem. |
| `Hqiv.Physics.derivedLeptonMuonShell` / `Hqiv.Physics.derivedLeptonElectronShell` / `Hqiv.Physics.derivedLeptonMuonShell_meets_threshold` / `Hqiv.Physics.derivedLeptonElectronShell_meets_threshold` | First derived μ/e selector on the current exact-shell interface: μ (then e) is the first shell whose `geometricResonanceStep` reaches the detuned-surface **octave** `chargedLeptonDetunedSurfaceOctaveRatio = 2` (area-doubling / one generation step), not fitted constants like `17` or `207`. |
| `Hqiv.Physics.chargeDecoratedMuonSupportPred` / `Hqiv.Physics.chargeDecoratedElectronSupportPred` / `Hqiv.Physics.derivedLeptonMuonShell_is_chargeDecorated_support` / `Hqiv.Physics.derivedLeptonElectronShell_is_chargeDecorated_support` / `Hqiv.Physics.derivedLeptonMuonShell_is_first_chargeDecorated_support` / `Hqiv.Physics.derivedLeptonElectronShell_is_first_chargeDecorated_support` | Deeper `M4` support packaging: the active μ/e shells are not just threshold picks but the **first charge-decorated support crossings** on the outer ladder, first from τ to μ and then from μ to e. |
| `Hqiv.Physics.thresholdDerivedOuterHorizonLeptonShellSelection` / `Hqiv.Physics.currentOuterHorizonLeptonShellSelection` / `Hqiv.Physics.leptonMuonShell_eq_derived` / `Hqiv.Physics.leptonElectronShell_eq_derived` | The exported active charged-lepton shell selection is now the threshold-derived selector rather than the old provisional numeral witness. |
| `Hqiv.Physics.thresholdDerivedOuterHorizonLeptonShellSelection_realizes_chargeDecorated_support` | The exported selector itself is theorem-backed as a charge-decorated support object on the current exact-shell proxy. |
| `Hqiv.Physics.lepton_shells_ordered` / `Hqiv.Physics.shellSurface_lepton_chain_strict` | Structural consequences of any valid selection: τ < μ < e and the same strict ordering on shell surfaces. |
| `Hqiv.Physics.T_lepton_mu_lt_T_tau` / `Hqiv.Physics.T_lepton_e_lt_T_mu` | Larger-shell charged leptons sit at strictly lower ladder temperatures. |
| `Hqiv.Physics.charged_lepton_resonance_uses_current_shell_selection` | The resonance module reads the μ/e shells from the exported current selection object rather than naming local shell numerals directly. |
| `Hqiv.Physics.m_tau_from_lockin_surface_candidate` / `Hqiv.Physics.m_tau_from_lockin_surface_candidate_value` | New τ **candidate** scale from the heavy lock-in shell, charged-lepton content count, and the local detuned surface; currently evaluates to `16 / 9`. |
| `Hqiv.Physics.m_tau_from_lockin_surface_candidate_approx_resonance` | The new lock-in-surface τ candidate lies within the existing relative-tolerance window of the current τ resonance anchor. |
| `Hqiv.Physics.m_mu_from_lockin_surface_candidate` / `Hqiv.Physics.m_e_from_lockin_surface_candidate` | Detuned μ/e candidates obtained by descending from the τ lock-in candidate through the existing τ→μ and μ→e resonance ratios. |
| `Hqiv.Physics.m_e_from_lockin_surface_candidate_eq_tau_over_resonanceProduct` | The full charged-lepton candidate ladder can be read as τ divided by the existing two-step resonance product. |
| `Hqiv.Physics.m_mu_from_lockin_surface_candidate_approx_resonance` / `Hqiv.Physics.m_e_from_lockin_surface_candidate_approx_resonance` | Because all three candidates use the same detuning ratios as the current resonance ladder, the μ/e candidates inherit the same relative-tolerance fit to the old μ/e resonance witnesses. |
| `Hqiv.Physics.resonance_k_tau_mu_eq_geometricResonanceStep` / `Hqiv.Physics.resonance_k_mu_e_eq_geometricResonanceStep` | The two charged-lepton resonance ratios are already expressed as geometric resonance steps of the selected shells; a future derived shell rule can therefore feed the whole ladder without changing the formulas. |

## Generated `G₂ ∪ {Δ}` Lie object (`Hqiv.Algebra.G2DeltaGeneratedLie`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Algebra.G2Generators` | The explicit seed set `range g2Generator` inside the 8×8 matrix carrier. |
| `Hqiv.Algebra.G2UnionDelta` | The physical generating set `G₂ ∪ {Δ}` as a set of 8×8 real matrices. |
| `Hqiv.Algebra.so8LieSubalgebra` | The honest skew-adjoint Euclidean `so(8)` Lie subalgebra inside `Matrix (Fin 8) (Fin 8) ℝ`. |
| `Hqiv.Algebra.g2DeltaGeneratedLie` | `LieSubalgebra.lieSpan ℝ (G₂ ∪ {Δ})`, i.e. the Lie subalgebra generated by the physical seed set. |
| `Hqiv.Algebra.G2UnionDelta_subset_g2DeltaGeneratedLie` | The seed set is contained in its generated Lie subalgebra. |
| `Hqiv.Algebra.g2Generator_mem_g2DeltaGeneratedLie` / `phaseLiftDelta_mem_g2DeltaGeneratedLie` | Each explicit `G₂` generator and `Δ` lie in the generated Lie subalgebra. |
| `Hqiv.Algebra.g2DeltaGeneratedLie_le_iff` | Minimality/universal property: `g2DeltaGeneratedLie ≤ K ↔ G₂ ∪ {Δ} ⊆ K`. |
| `Hqiv.Algebra.g2DeltaGeneratedLie_le_so8LieSubalgebra` | The generated Lie algebra stays inside the honest skew-adjoint `so(8)` model. |
| `Hqiv.Algebra.g2DeltaWitness` / `g2DeltaWitness_linearIndependent` | Explicit 28-element witness family inside the generated Lie algebra, together with linear independence. |
| `Hqiv.Algebra.finrank_so8LieSubalgebra` / `finrank_g2DeltaGeneratedLie_eq_28` | Both the honest skew-adjoint `so(8)` model and the `LieSpan(G₂ ∪ {Δ})` carrier are shown to have dimension `28`. |
| `Hqiv.Algebra.g2DeltaGeneratedLie_eq_so8LieSubalgebra` | The generated Lie algebra from the physical seed set is identified with the honest Euclidean `so(8)` Lie subalgebra. |
| `Hqiv.Algebra.so8Generator_mem_g2DeltaGeneratedLie` / `span_so8Generators_le_g2DeltaGeneratedLie` | Every packaged `so8Generator` lies in the generated Lie algebra, bridging the physical seed set to the existing 28-generator closure package. |

## Canonical Yang-Mills package (`Hqiv.Physics.HQIVYangMillsPackage`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.hqivGaugeCarrier` | Canonical finite-dimensional gauge carrier: `span ℝ (range so8Generator)` inside `Matrix (Fin 8) (Fin 8) ℝ`. |
| `Hqiv.Physics.hqivGeneratedGaugeCarrier` | Temporary package-level name for the physical-seed-generated carrier; currently a lightweight alias to `hqivGaugeCarrier` until the heavy `G2DeltaGeneratedLie` module is promoted into the normal build graph. |
| `Hqiv.Physics.hqivGeneratedGaugeCarrier_eq_hqivGaugeCarrier` | Current bridge theorem showing the temporary generated-carrier name coincides with the existing span-based carrier. |
| `Hqiv.Physics.HQIVYangMillsPackage` | Structure bundling the `so(8)` carrier, basis, bracket expansion, `G₂/Δ` membership, `SU(2)_L` / hypercharge membership, triality count, forced `α/γ`, and rapidity-phase alignment. |
| `Hqiv.Physics.hqivYangMillsPackage` | Canonical packaged instance of `HQIVYangMillsPackage`. |
| `Hqiv.Physics.hqivYangMillsPackage_carrier_eq_generated` | The canonical package is now expressed in terms of the generated-carrier abstraction rather than naming the span carrier directly. |
| `Hqiv.Physics.hqivYangMillsPackage_nonempty` | Existence of the canonical package. |
| `Hqiv.Physics.hqivYangMillsPackage_basis_bracket` | Repackages `lieBracket_in_span` through the canonical package basis. |
| `Hqiv.Physics.hqivYangMillsPackage_rapid_phase` | Repackages the rapidity/polar-angle phase alignment through the canonical package. |

## Furey ↔ HQIV ontology bridge scaffold (`Hqiv.Physics.FureyHQIVOntologyBridge`)

The module doc opens with the **Stage 2–3** line: **`Cl(1)` + 1D hypercharge refinement
proved; full `Cl(6)`-scale equivariant ideals open.** Until a paper-aligned `Cl(6)`
layer lands, these rows are **bookkeeping / partial slot** material — **not** tagged
**`Furey claim supported`** (reserve that phrase in this file for theorems that
explicitly carry the full Furey Clifford claim).

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.HQIVFoundationFirstAnchor` / `hqivFoundationFirstAnchor` | Lightweight record and canonical instance bundling the current HQIV-first anchors: spinor carrier dimension, one-generation SM quantum-number witness, triality count, and forced `α/γ`. |
| `Hqiv.Physics.HQIVFureyGenerationIndex` / `HQIVFureyThreeGenerationCarrier` | HQIV-derived landing zone for Furey's three-generation embedding: `So8RepIndex` labels, with one `OctonionSpinorCarrier` per generation label. |
| `Hqiv.Physics.hqivFurey_generation_count_eq_three` / `hqivFurey_generationSlot_count_eq_twenty_four` / `hqivFurey_chiralSlot_count_eq_forty_eight` | Concrete finite bookkeeping: three generation labels, 24 real 8s carrier slots, and 48 chiral Weyl generation slots from HQIV foundations. |
| `Hqiv.Physics.FureyThreeGenerationEmbeddingFromHQIV` / `hqivFureyThreeGenerationEmbedding` / `hqivFureyThreeGenerationEmbedding_exists` | The theorem-backed HQIV-side certificate that supplies the three-generation embedding target for future Furey minimal-ideal equivalence proofs. |
| `Hqiv.Physics.FureyGenerationShape` / `FureyShapeThreeGenerationsFromHQIV` | Furey-shaped generation abstraction: any finite generation-label type equivalent to the HQIV triality labels inherits the HQIV three-generation result. |
| `Hqiv.Physics.fureyShape_generation_count_eq_three` / `fureyShape_chiralSlot_count_eq_forty_eight` / `canonicalFureyGenerationShape_count_eq_three` | Main proof layer for “Furey’s shape + HQIV foundation ⇒ three generations”: cardinality `3` and 48 chiral bookkeeping slots follow from `HQIVFoundationFirstAnchor.trialityRepCount`. |
| `Hqiv.Physics.FureyCandidateDerivation` | Record of future Furey-side bridge obligations: complex carrier, minimal-left-ideal one-generation bridge, number-operator charge match, three-generation split, and ontology refinements. |
| `Hqiv.Physics.FureyMayRefineHQIV` | Predicate/certificate that all Furey bridge obligations are proved before the Furey layer may refine HQIV ontology. |
| `Hqiv.Physics.hqivFoundationFirstAnchor_exists` | The HQIV foundation-first anchor exists without any Furey/Clifford assumptions. |
| `Hqiv.Physics.furey_refinement_requires_{carrier,charge,generation,shell_support}_bridge` | Projection lemmas making the conflict rule explicit: Furey can refine carrier, charge, generation, or shell/support ontology only through proved bridge obligations. |

### Partial Clifford / hypercharge slot refinement (Stage 2–3 slice; abstract `Cl(0,6)` dimension)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Algebra.IsMinimalLeftIdeal` / `Hqiv.Algebra.LeftIdeal` | Definitions: nonzero minimal left ideals as submodules of `R` over itself. |
| `Hqiv.Algebra.cliffordOneDim_top_isMinimalLeftIdeal` | `⊤` is minimal in `CliffordOneDim` (Mathlib `Cl(1) ≅ ℂ` model). |
| `Hqiv.Algebra.phaseLiftDelta_ne_zero` / `hqiv_hypercharge_line_finrank_one` | `Δ` is nonzero; the ℝ-span of `phaseLiftDelta` has `finrank` 1. |
| `Hqiv.Algebra.CliffordHyperchargeSlotRefinement` / `canonicalCliffordHyperchargeSlotRefinement` | Bundles the `Cl(1)` minimal-ideal fact with the 1D matrix line for `Δ`. |
| `Hqiv.Physics.sm_hyperchargeGenerator_eq_phaseLiftDelta` / `rapidity_carrier_zeta_phase_arg_eq_polarAngle` | SM hypercharge generator is `Δ`; zeta phase exponent matches the rapidity polar-angle scaffold (`RapidityIdealPurposeBridge`). |
| `Hqiv.octonionLeftMul_N_mul_self` (`Hqiv.Algebra.OctonionLeftMulSquare`) | For each `k = 1,…,7`, `L(e_k)² = -I₈` as `8×8` real matrices (entrywise `fin_cases` proof). |
| `Hqiv.Algebra.quadFormCl06Six` / `CliffordCl06Six` / `imaginarySixIndex` / `imaginarySixLeftMulMatrix` | **\(\mathrm{Cl}(0,6)\)** quadratic form on `Fin 6 → ℝ`, Clifford algebra type, embedding `e₁..e₆ → Fin 8`, and matched left-mult matrices `L(e_{j+1})`. |
| `Hqiv.Algebra.quadFormCl06Six_basisVec` / `cliffordCl06Six_iota_sq` / `cliffordCl06Six_iota_sq_eval` | Clifford generator squares: `ι(δⱼ)²` maps to `Q(δⱼ) = -1` in `ℝ → CliffordCl06Six`. |
| `Hqiv.Algebra.imaginarySix_leftMul_matrix_mul_self` | On the six directions, `L(e_{j+1})² = -I₈` (specializes `octonionLeftMul_N_mul_self`). |
| `Hqiv.Algebra.cliffordCl06Six_finrank` / `Hqiv.Algebra.finrank_extCl06` | **Furey claim supported — partial (abstract `Cl(0,6)` + concrete `8`-dim spinor `ρ`)**: `Module.finrank ℝ CliffordCl06Six = 64` via `CliffordAlgebra.equivExterior` and the `⋀^k ℝ⁶` grading (`Nat.sum_range_choose`). |
| `Hqiv.Algebra.cl06StandardSpinorMatLift` / `Hqiv.Algebra.cl06StandardSpinorRho` / `Hqiv.Algebra.cl06StandardSpinorMatLift_ι` | Mathlib `CliffordAlgebra.lift` of `quadFormCl06Six` into `Matrix (Fin 8) (Fin 8) ℝ`, then `algEquivMatrix'` into `CliffordCl06Six →ₐ[ℝ] End(OctonionSpinorCarrier)`; six explicit `γ` Kronecker matrices (`cl06SpinorGammaMat`), **not** octonion left-mult on `e₁…e₆`. |
| `Hqiv.Algebra.cl06StandardSpinorRhoRange_finrank_le` | The `ℝ`-linear range of `ρ` sits in `End(ℝ⁸)` hence has `finrank ≤ 64` (ambient `8×8` real dimension). (A tight `8`-dimensional **minimal-ideal** image still needs further simple-module / surjectivity packaging.) |
| `Hqiv.Algebra.cliffordCl06SixLeftIdealGenerated` / `cliffordCl06SixLeftIdealGenerated_one_eq_top` / `exists_nonzero_idempotent_cliffordCl06Six` | Abstract left-ideal packaging in `CliffordCl06Six`; `⟨1⟩_L = ⊤`; nontrivial idempotent `1`. |
| `Hqiv.Algebra.cliffordIdealToSpinorVec` | Representation-conditional bridge `I →ₗ[ℝ] OctonionSpinorCarrier` from any `ρ : CliffordCl06Six →ₐ[ℝ] End(ℝ⁸)` (instantiate with `cl06StandardSpinorRho`) and a seed vector (orthogonal to the naive left-mult matrix lift obstruction below). |
| `Hqiv.Algebra.octonionLeftMul_1_mul_2_add_mul_swap_ne_zero` / `octonionLeftMul_add_sum_square_entry_33_ne` (`Hqiv.Algebra.OctonionLeftMulCliffordObstruction`) | **Matrix obstruction (kept explicit):** naive octonion **left** `L(e₁),L(e₂)` fail mixed Clifford relations, so they cannot be the six generators of a `Cl(0,6)` `CliffordAlgebra.lift` into `Mat₈(ℝ)` for the standard `Q` on `ℝ⁶`. |

## Conserved-content mass bridge (`Hqiv.Physics.ConservedContentMassBridge`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.FermionContentClass` | Inductive ν / charged lepton / quark (narrative: 1 / 2 / 3 Fano triples). |
| `Hqiv.Physics.FermionClosureLayer` / `Hqiv.Physics.closureLayerOfContent` / `Hqiv.Physics.closureLayer_rank_matches_triple_count` | New post-Step-B packaging of the same ν / charged-lepton / quark bridge as a closure-decoration hierarchy: `spinOnly`, `chargeDecorated`, `colorComposed`, with rank exactly matching the old `1 / 2 / 3` conserved-triple counts. |
| `Hqiv.Physics.VisibleChargeState` / `Hqiv.Physics.VisibleChargeState.toInt` / `Hqiv.Physics.VisibleChargeState.toRat` / `Hqiv.Physics.visibleChargeStateAllowed` | New visible-state interface for the shell ladder: the exported shell-visible charges are only `neutral`, `positive`, and `negative`, with explicit integer/rational realizations and an admissibility predicate by closure layer. |
| `Hqiv.Physics.visibleChargeStateAllowed_spinOnly_iff` / `Hqiv.Physics.visibleChargeStateAllowed_chargeDecorated_iff` / `Hqiv.Physics.visibleChargeStateAllowed_colorComposed` | The allowed visible shell states are now theorem-backed by rung: spin-only is neutral only, charge-decorated is signed only, and color-composed can realize all three integer/neutral visible channels. |
| `Hqiv.Physics.neutrino_visible_charge_is_neutral` / `Hqiv.Physics.chargedLepton_visible_charge_is_signed` / `Hqiv.Physics.quark_visible_charge_channels_are_integer_states` | The ν / charged-lepton / quark closure classes are now explicitly bridged to visible shell-state admissibility rather than only to content counts. |
| `Hqiv.Physics.visible_shell_states_match_integer_lepton_charges` / `Hqiv.Physics.quark_fractional_embedding_charges_are_residual_not_visible` | The key visible/residual split: integer/neutral visible shell states match the lepton-side algebraic charges, while the quark fractions from `SMEmbedding` are proved not to be visible shell-state values. |
| `Hqiv.Physics.shellClass28_and_closureRank_are_parallel_bookkeeping` | Joint residue typing (`mod 28`) and closure rank are now packaged side-by-side as parallel bookkeeping layers, not one collapsed definition. |
| `Hqiv.Physics.conservedTripleCount` | Maps each class to `1`, `2`, or `3`; now explicitly aligned with the closure-layer ranking. |
| `Hqiv.Physics.intrinsicWaveComplexity` | `(conservedTripleCount c)²` with strict ordering lemmas. |
| `Hqiv.Physics.closureLayer_rank_neutrino_lt_chargedLepton` / `Hqiv.Physics.closureLayer_rank_chargedLepton_lt_quark` / `Hqiv.Physics.content_class_order_matches_triple_counts` | The hierarchy is strict in both languages: ν < charged lepton < quark, and `spinOnly < chargeDecorated < colorComposed`. |
| `Hqiv.Physics.chargedLeptonContentCount_eq_conservedTripleCount` / `Hqiv.Physics.chargedLepton_intrinsicWaveComplexity_eq_content_square` / `Hqiv.Physics.chargedLepton_chargeDecorationFactor_over_neutral` | The charged-lepton rung is now tied explicitly to the closure hierarchy: its local bookkeeping count matches the `chargeDecorated` class, its complexity is exactly that count squared, and it is a rigid factor `4` above the neutral spin-only rung. |
| `Hqiv.Physics.m_tau_from_lockin_surface_candidate_eq_chargeDecorated_closure` / `Hqiv.Physics.m_mu_from_lockin_surface_candidate_eq_chargeDecorated_relaxation` / `Hqiv.Physics.m_e_from_lockin_surface_candidate_eq_chargeDecorated_two_step_relaxation` | The τ/μ/e candidate ladder is now packaged as a **charge-decorated closure**: τ is the heavy lock-in charge-decorated witness, and μ/e are its first and second resonance relaxations. |
| `Hqiv.Physics.m_nu_e_derived_from_neutralClosureWitness` / `Hqiv.Physics.neutrino_ladder_from_neutralClosureWitness` | The current neutrino ladder is now pointed directly at the **neutral outer-closure** channel: `ν_e = suppression * neutralClosureWitness`, then `ν_μ` and `ν_τ` are its second and third suppressed descendants. |
| `Hqiv.Physics.m_nu_e_derived_lt_m_tau_from_lockin_surface_candidate` / `Hqiv.Physics.chargeDecorated_candidate_ladder_descends` | First `M4` hierarchy bridge: the neutral ν witness sits below the charge-decorated τ candidate, and the charge-decorated candidate ladder descends strictly `τ > μ > e` along the threshold-derived resonance steps. |
| `Hqiv.Physics.quark_intrinsicWaveComplexity_eq_content_square` / `Hqiv.Physics.colorComposed_factor_over_chargeDecorated` / `Hqiv.Physics.colorComposed_factor_over_neutral` | The quark rung is now tied explicitly to the closure hierarchy too: the `colorComposed` class has complexity `3² = 9`, i.e. a rigid factor `9/4` above the charged-lepton rung and `9` above the neutral rung. |
| `Hqiv.Physics.nucleonTraceChannelCount_eq_colorComposedTripleCount` / `Hqiv.Physics.nucleonTraceChannelCount_eq_colorComposed_rank` | The baryon-side composite trace uses exactly three active channels, matching the `colorComposed` closure rank. |
| `Hqiv.Physics.colorComposed_baryon_binding_uses_three_channel_network` / `Hqiv.Physics.protonMassFromMetaHarmonics_eq_colorComposed_network_mass` / `Hqiv.Physics.neutronMassFromMetaHarmonics_eq_colorComposed_network_mass` / `Hqiv.Physics.colorComposed_quark_rung_has_three_harmonics_and_network_binding` | First `M5` bridge: baryons are now packaged as the color-composed rung realized by a three-channel composite trace and network binding at `referenceM`, not just by separate shell tables and prose. |
| `Hqiv.Physics.quarkConstituentBaseLift_MeV` / `Hqiv.Physics.quarkConstituentDress_MeV` / `Hqiv.Physics.quarkResidualDetuningDress_MeV` / `Hqiv.Physics.activeUpLightQuarkMass_GeV` / `Hqiv.Physics.activeDownLightQuarkMass_GeV` | Second `M5` bridge: the baryon constituent layer is no longer solved backward from the proton decimal. It now uses one shared constituent baseline from the same network binding, one large shared light-rung dressing scale, and one smaller residual detuning scale on the active up/down visible masses. |
| `Hqiv.Physics.protonMassFromMetaHarmonics_eq_quantum_number_energy_budget` / `Hqiv.Physics.neutronMassFromMetaHarmonics_eq_quantum_number_energy_budget` / `Hqiv.Physics.protonMassFromMetaHarmonics_pos` / `Hqiv.Physics.neutronMassFromMetaHarmonics_pos` / `Hqiv.Physics.proton_neutron_split_from_dressed_light_quarks` | The proton/neutron witnesses are now explicit bottom-up quantum-number energy budgets: a shared light-rung state-space mass carries most of the constituent energy, while the neutron-proton split is controlled only by the smaller residual detuning term rather than by the full dressed light-quark mismatch. |
| `Hqiv.Physics.top_and_tau_share_reference_lockin_index` / `Hqiv.Physics.top_and_tau_lockin_is_index_level_alignment` | Heavy charged lepton and top are now packaged as sharing `referenceM` only at the lock-in-index level, without claiming a single common mass law or identical resonance bookkeeping. |
| `Hqiv.Physics.AllowedColorResonanceBand` / `Hqiv.Physics.ResidualChargeChannel` / `Hqiv.Physics.AllowedColorResonanceBand.toGenerationIndex` / `Hqiv.Physics.ResidualChargeChannel.loopMultiplicity` / `Hqiv.Physics.ResidualChargeChannel.toRat` | New public quark-rung API: heavy/mid/light color-composed resonance bands are primary, while `upLike` / `downLike` are internal residual channels whose fractions come from simple integer loop multiplicities over the color-composed denominator. |
| `Hqiv.Physics.ResidualChargeChannel.heavyMassWeight` / `Hqiv.Physics.residualChargeChannel_heavyMassWeight_eq_loopMultiplicity_natAbs` / `Hqiv.Physics.topLockinColorResonanceAnchorMass` / `Hqiv.Physics.crossChannelHeavyShellDetuning` / `Hqiv.Physics.downChannelVisibleBudgetCount` / `Hqiv.Physics.channelVisibleMassCompression` / `Hqiv.Physics.channelHeavyColorResonanceMass` | New heavy-band normalization layer: the public quark ladder is anchored at the top lock-in band, but the down-like heavy visible state is no longer a bare loop fraction. Instead the shared spin/color energy is compressed by the heavy-shell cross-detuning and the `2 × 3` visible-state bookkeeping budget. |
| `Hqiv.Physics.allowedColorResonanceMass` / `Hqiv.Physics.allowedColorResonanceShell` / `Hqiv.Physics.colorResonanceProduct` / `Hqiv.Physics.allowedColorResonanceMass_eq_shared_heavy_band_over_product` / `Hqiv.Physics.allowedColorResonanceMass_upLike_heavy_eq_top_lockin_anchor` / `Hqiv.Physics.allowedColorResonanceMass_downLike_heavy_eq_top_over_detuning_and_visible_budget` / `Hqiv.Physics.allowedColorResonanceMass_downLike_heavy_eq_upLike_over_detuning_and_visible_budget` / `Hqiv.Physics.residualChargeChannel_is_fractional_bookkeeping` | The heavy/mid/light allowed-band API is now fed by a top-at-lockin heavy anchor plus channel-specific visible compression, then relaxed by the same detuned-shell resonance products; the active down branch no longer uses the naive `top / 2` rule. |
| `Hqiv.Physics.allowedColorResonanceModalFrequencySpec` / `Hqiv.Physics.topModalFrequencySpec` / `Hqiv.Physics.bottomModalFrequencySpec` / `Hqiv.Physics.resonanceK_internal_top_charm_eq_modal_readout` / `Hqiv.Physics.resonanceK_internal_down_bottom_strange_eq_modal_readout` / `Hqiv.Physics.m_charm_GeV_eq_top_over_modal_readout` / `Hqiv.Physics.m_strange_GeV_eq_bottom_over_modal_readout` / `Hqiv.Physics.allowedColorResonanceMass_upLike_mid_eq_heavy_over_modal_readout` / `Hqiv.Physics.allowedColorResonanceMass_downLike_mid_eq_heavy_over_modal_readout` | `QuarkMetaResonance.lean` now exposes explicit modal-frequency/horizon readouts for the public quark/color ladder. The top and bottom heavy channels provide modal wrappers, internal detuned-shell steps are identified with modal geometric-step readouts, and both the derived charm/strange masses and the public mid-band masses are packaged as heavy-band relaxations through that modal layer. |
| `Hqiv.Physics.residualChargeChannel_loopMultiplicity_values` / `Hqiv.Physics.residualChargeChannel_toRat_eq_loopMultiplicity_over_color_denominator` / `Hqiv.Physics.upLike_loopMultiplicity_is_double_downLike_magnitude` / `Hqiv.Physics.upLike_residual_is_double_downLike_magnitude` | Quark residuals are now explicitly generated from simple loop arithmetic: `upLike` carries two positive loop quanta, `downLike` one negative quantum, and the familiar `2/3` / `-1/3` fractions arise only after division by the shared color-composed denominator. |
| `Hqiv.Physics.quark_loop_residual_denominator_matches_colorComposed_rank` / `Hqiv.Physics.quark_residuals_are_loop_multiplicity_over_color_rank` / `Hqiv.Physics.upLike_quark_residual_is_double_downLike_magnitude_over_color_rank` | The ontology bridge is now theorem-backed in the hierarchy file too: the residual denominator is exactly the `colorComposed` rank `3`, and the up-like branch is the double-strength member of the residual pair over that common denominator. |
| `Hqiv.Physics.allowedColorResonanceMass_upLike_heavy_eq_top_GeV` / `Hqiv.Physics.allowedColorResonanceMass_downLike_heavy_eq_top_GeV_over_detuning_and_visible_budget` | The active heavy visible states are now theorem-backed directly: the up-like heavy band is the top lock-in anchor, while the down-like heavy band is the same shared heavy state observed through heavy-shell detuning and the `2 × 3` visible-state budget. |
| `Hqiv.Physics.quark_detuning_and_omaxwell_em_slot_share_monogamy_split` / `Hqiv.Physics.upResonanceAxis_vertex_ne_em_vertex` / `Hqiv.Physics.downResonanceAxis_vertex_ne_em_vertex` / `Hqiv.Physics.resonanceK_internal_zero_eq` / `Hqiv.Physics.crossChannelHeavyShellDetuning_eq` | `QuarkOMaxwellBridge.lean`: proved packaging that quark internal steps are literal `geometricResonanceStep` ratios, canonical quark ladder axes use **non-EM** Fano vertices (`1` and `4`), and the lattice split `α+γ=1` links Rindler detuning (`c_rindler_shared = γ/2`) to the O-Maxwell EL φ-slot on channel `a=0` (`Hqiv.EL_O_general`). Does **not** derive shell integers from eigenmodes (see `AGENTS/O_MAXWELL_EIGEN_SHELL_SELECTION.md`). |
| `Hqiv.Physics.rindlerDetuningShared_eq_affine` / `Hqiv.Physics.rindlerDetuningShared_eq_one_plus_half_gamma` / `Hqiv.Physics.detunedShellSurface_eq_shell_div_one_plus_half_gamma` / `Hqiv.Physics.detuned_eq_shell_over_omaxwell_hook` / `Hqiv.Physics.FanoOmaxwell_detuning1Jet_eq_spectralFanoRindlerLimit` | `FanoDetuningFirstOrder.lean`: the detuning law is first-order **affine** in shell index with slope `γ/2`, `detunedShellSurface` rewrites to `S(m)/(1+(γ/2)m)`, and `omaxwellFanoDetuning1Jet` is sourced from the direct spectral scaffold (`spectralFanoRindler1Jet` on the canonical incidence line `FanoLine.ofTag canonicalSpectralTag`). The spectral matching theorem remains **conditional**: any candidate 1-jet agreeing with that hook on all `m` is forced to the same affine law. |
| `Hqiv.Physics.ModalFrequencyHorizonSpec` / `Hqiv.Physics.modalFrequencyHorizonFromShellNominal` / `Hqiv.Physics.modalFrequencyHorizonFromFanoLine` / `Hqiv.Physics.modalFrequencyHorizonFromCompton` / `Hqiv.Physics.modalFrequencyHorizonFromShellNominal_detuning_affine` / `Hqiv.Physics.modalFrequencyHorizonFromFanoLine_detuning_affine` | `ModalFrequencyHorizon.lean`: modal-first interface that packages nominal frequency, interaction horizon quarter-period compatibility (`ω·Δt_quarter = horizonQuarterPeriod`), and a detuning 1-jet map. Constructors expose three current sources (self-clock readout, direct Fano spectral source, Compton parameterization) while preserving affine detuning compatibility theorems. |
| `Hqiv.Physics.detunedShellSurface_eq_shell_div_trialityProjectedDenominator` / `Hqiv.Physics.trialityProjectedDenominator_eq_rindler` / `Hqiv.Physics.trialityProjected_denominator_at_shell_zero_eq_one` / `Hqiv.Physics.trialityProjectedDenominator_stub_eq_affine_shell` / `Hqiv.Physics.trialityProjectedDenominator_firstOrder` | `FanoTrialityDetuningScaffold.lean` + `FanoOmaxwellSpectrum.lean`: user-facing quotient `detunedShellSurface m = S(m) / trialityProjectedDenominatorTag line m` now routes through the direct O-Maxwell spectral source (`trialityProjectedDenominator L m := spectralFanoRindler1Jet L m`). Public tags are incidence-driven (`FanoLineTag = FanoVertex`, `FanoLine.ofTag` picks a canonical incident line). Affine-shell and shell-zero identities are proved from the spectral layer. Open research remains deriving the same normalization from explicit `Hqiv.Algebra.Triality` equivariance rather than from current scaffold normalization choices. |
| `Hqiv.Physics.deltaTurnIncrement_eq_projectedDetuned` / `Hqiv.Physics.turnIncrementBarrier_eq_universalDetunedWell` / `Hqiv.Physics.hyperchargePathBarrier_eq_base_plus_turns` / `Hqiv.Physics.hyperchargePathBarrier_strict_order` | `HyperchargePathBarrierScaffold.lean`: formal scaffold for the three-path picture (`Y ∈ {0,+1,-1}` as turn-counts `0,1,2`) over one universal detuned well. Adds a `Δ`-facing interface (`DeltaTurnIncrementModel`, active map `deltaTurnIncrement`) as the designated replacement point for future algebraic derivations. In the current scaffold, `deltaTurnIncrement` is identified with the projected detuned well, yielding proved ordering `straight < plusTurn < minusTwoTurn`. Does **not** yet derive turn increment or line-dependence from explicit `Δ` / triality / Fano structure (see `AGENTS/O_MAXWELL_EIGEN_SHELL_SELECTION.md` §2.3). |
| `Hqiv.Physics.trialityRepTurnIncrement_invariant_under_cycle` / `Hqiv.Physics.rapidityLiftedDenominator_eq_affine_shell` / `Hqiv.Physics.rapidityLiftedDenominator_eq_trialityProjectedDenominator` / `Hqiv.Physics.trialityRapidityWellResidual_eq_zero` / `Hqiv.Physics.trialityRapidityWell_nearEquivalent` / `Hqiv.Physics.rapidityCPBias_eq_eta_ratio_minus_one` / `Hqiv.Physics.cpSensitiveTrialityRapidityResidual_eq` / `Hqiv.Physics.cpSensitiveTrialityRapidityResidual_rep8V_eq_zero` / `Hqiv.Physics.cpSensitiveTrialityIncrement_threeRep_average_eq_rapidityWell` / `Hqiv.Physics.cpSensitiveTrialityRapidityResidual_bound_of_bias` | `TrialityRapidityWellEquivalence.lean`: explicit harness comparing triality-indexed and rapidity-written well constructions. Baseline scaffold remains exactly matched (`residual = 0`). A rep-sensitive candidate is added using the same baryogenesis channel but with a derived, non-fitted CP-bias slot (`rapidityCPBias m := omega_k_at_horizon m m_lockin - 1`), plus bridge theorem to the η-ratio form under lockin positivity. Triality orientation weights (`8v:0, 8s⁺:+1, 8s⁻:-1`) give opposite-sign spinor residuals and zero vector residual, with exact recovery of the rapidity well under three-rep averaging and a quantitative near-equivalence bound controlled by CP-bias magnitude. |
| `Hqiv.Physics.chargeDecorated_tau_candidate_lt_colorComposed_heavy_visible_band` / `Hqiv.Physics.visible_state_hierarchy_ν_e_tau_colorHeavy` | New visible-state hierarchy witness: the τ charge-decorated lock-in candidate lies below the top-anchored heavy color-composed band, so the ν → charged-lepton → heavy color-composed ordering is now stated through the active visible API rather than the archived witness chain. |
| `Hqiv.Physics.colorComposed_visible_resonance_above_chargeDecorated_same_shell` | First cross-sector visible-state ordering theorem on the ansatz side: at fixed shell and positive normalization, the `colorComposed` rung sits above the `chargeDecorated` rung. |
| `Hqiv.Physics.m_nu_e_derived_lt_m_tau_from_resonance` | Derived ν\_e scale `<` τ witness (`m_tau_from_resonance`). |
| `Hqiv.Physics.m_tau_from_resonance_lt_m_top_GeV` / `Hqiv.Physics.observed_mass_hierarchy_ν_e_tau_top` | Archived in `Hqiv/Archive/Physics/LegacyTopAnchorWitnesses.lean`: old `ν < τ < top` witness chain kept only as a legacy theorem path after the public visible-state API was rebuilt around top-at-lockin plus heavy-shell detuning and visible-state compression. |
| `Hqiv.Physics.massScalingAnsatz` | `k * l² * effCorrected δ m` (ties to `GlobalDetuning`; `k` is an explicit positive scale, not derived from δ_E in this file). |
| `Hqiv.Physics.massScalingAnsatz_lt_of_lt_l` / `massScalingAnsatz_lt_of_lt_m` | Strict monotonicity in `l` (fixed shell) and in shell `m` (fixed `l`), under `RindlerDenDeltaPos` / `0 ≤ δ` as stated. |
| `Hqiv.Physics.massScalingAnsatz_eq_k_l2_mul_zetaHQIVTerm_at_minus_one` | At `s = -1` with trivial rapidity phase, `(massScalingAnsatz k δ l m : ℂ) = k·l²·zetaHQIVTerm δ φ t (-1) m` (`OctonionicZeta`). |
| `Hqiv.Physics.intrinsicWaveComplexity_eq_sphericalHarmonicCumulativeCount_pred` | For each `FermionContentClass`, `l²` equals cumulative `S²` Laplace–Beltrami degeneracy `(L+1)²` at `L = l - 1` (`sphericalHarmonicCumulativeCount` in `SphericalHarmonicsBridge`). |
| `Hqiv.Physics.neutrinoShellCandidate` | `Finset.Icc 4 6` (candidate small-`m` band for the ν narrative). |
| `Hqiv.Physics.referenceNeutrinoShell_mem` | `5 ∈ neutrinoShellCandidate`. |

## Octonionic lattice zeta (`Hqiv.Physics.OctonionicZeta`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.zeta_HQIV` | Rapidity-modulated Dirichlet-style sum over shells `m` with `effCorrected (delta_auxiliary_phi_per_shell …)` and phase `cexp (I * φ * t * delta_theta_prime (m : ℝ))`. |
| `Hqiv.Physics.zeta_HQIV_eq_sum_residue_ZMod7` / `zeta_HQIV_eq_sum_Fano_residue_classes` | Partition into seven mod-7 progressions (Fano vertices = `Fin 7`); same residue structure as `Nat.sumByResidueClasses`. |
| `Hqiv.Physics.zeta_HQIV_summable_of_re_gt_one` | Absolute convergence when `1 < s.re` and Rindler denominators stay positive. |
| `Hqiv.Physics.zeta_HQIV_same_shell_axis_as_modeRatio_bridge` | `ShellToHarmonicLimit` witness linking to `ContinuumManyBodyQFTScaffold`. |
| `Hqiv.Physics.fano_prime` / `zetaHQIVFormalEulerFactor` | One-based line labels `1…7` and formal single-shell Euler template (not asserted equal to the full zeta sum). |
| `Hqiv.Physics.exists_eff_gt` | For any real `C`, some shell has `effCorrected δ m > C` (uses asymptotic `eff/(m+1) → 5`). |
| `Hqiv.Physics.exists_next_shell_eff_ratio_ge` | Given `current_m` and `threshold > 1`, some larger shell has `eff(m')/eff(current_m) ≥ threshold`. |
| `Hqiv.Physics.next_lattice_prime` / `next_lattice_prime_spec` / `next_lattice_prime_gt` / `next_lattice_prime_min` | Smallest `m' > current_m` with relative `eff` jump ≥ `threshold` (default `1.5`); minimality via `Nat.find`. **Not** rational factorization in `ℤ`. |
| `Hqiv.Physics.exists_fano_vertex_same_residue_mod_seven` | Every shell index matches some `FanoVertex` mod 7 (same partition as the zeta residue sum). |
| `Hqiv.Physics.exists_fano_fano_prime_eq_shell_residue_succ` | For every shell `m`, some Fano vertex has `fano_prime f = (m % 7) + 1` (one-based line label from shell residue). |

## Octonion-coordinate `ℝ⁸` shell (`Hqiv.Algebra.OctonionSphereConstruction`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Algebra.intLatticeToO8` / `Hqiv.Algebra.intLatticeToO8_apply` | Embed `Fin 8 → ℤ` into `EuclideanSpace ℝ (Fin 8)` via `PiLp` / `toLp 2`. |
| `Hqiv.Algebra.o8normSq` / `Hqiv.Algebra.o8normSq_eq_sum_sq` | Squared norm equals coordinate sum of squares. |
| `Hqiv.Algebra.embedNatFour` / `Hqiv.Algebra.sum_sq_embedNatFour` | Pad four naturals into `Fin 8 → ℕ` (zeros in last four slots); sum of squares matches four-squares sum. |
| `Hqiv.Algebra.exists_int_lattice_o8_norm_sq` | Every `m : ℕ` is `‖x‖²` for some integer lattice point (Lagrange + padding). |
| `Hqiv.Algebra.volume_closedBall_o8_eq` | Lebesgue mass of the closed `r`-ball in `ℝ⁸` is `π⁴/24 · r⁸` (`InnerProductSpace.volume_closedBall_of_dim_even`, `k = 4`). |
| `Hqiv.Algebra.continuousBallVolume8` / `Hqiv.Algebra.continuousSphereArea7` / `Hqiv.Algebra.deriv_continuousBallVolume8` | Closed-form `V₈`, surface proxy `A₇`, and `dV₈/dr = A₇`. |
| `Hqiv.Algebra.closedBall_o8_sqrt_subset_sqrt_succ` / `Hqiv.Algebra.volume_closedBall_o8_sqrt_le_sqrt_succ` / `Hqiv.Algebra.continuousBallVolume8_sqrt_le_sqrt_succ` / `Hqiv.Algebra.continuousSphereArea7_sqrt_lt_sqrt_succ` | Shell `m → m+1`: nested `closedBall` at radii `√m`, monotone Lebesgue mass and `V₈`/`A₇` proxies. |
| `Hqiv.Algebra.sumSqInt8` / `Hqiv.Algebra.latticeShell8Finset` / `Hqiv.Algebra.r8` / `Hqiv.Algebra.mem_latticeShell8Finset_iff` | Integer shell count `r₈(m)` on `Fin 8 → ℤ` via bounded `piFinset` + filter (`scripts/test_integer_lattice_shell_count8.py`). |
| `Hqiv.Algebra.r8_zero` / `Hqiv.Algebra.r8_one` | `r₈(0)=1`, `r₈(1)=16` (`native_decide`). |
| `Hqiv.Algebra.latticeBox8Wide` / `Hqiv.Algebra.card_latticeBox8Wide` / `Hqiv.Algebra.r8_le_two_mul_add_one_pow_eight` | Crude bounding box `[-m,m]⁸`; `(2m+1)⁸` shell-card upper bound on `r₈(m)` (not sharp). |
| `Hqiv.Algebra.modEq_twenty_eight_iff` / `Hqiv.Algebra.shellClass28_eq_iff_modEq` | CRT: `a ≡ b (mod 28)` ↔ joint `(mod 4, mod 7)`; `shellClass28` in `ZMod 28`. |
| `Hqiv.Algebra.example_143_lattice_norm` | Shell `m = 143`: padded vector `(9,7,3,2,0,0,0,0)` has squared norm `143`. |

## Theta-series coefficient bridge (`Hqiv.Algebra.ModularThetaBridgeScaffold`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Algebra.thetaZ8FormalCoeff` | Coefficient of `q^m` in `∑ r₈(m) q^m`; definitionally `r8 m`. |
| `Hqiv.Algebra.thetaZ8FormalCoeff_eq_r8` | `thetaZ8FormalCoeff m = r8 m`. |
| `Hqiv.Algebra.CoeffsAgreeWithR8` | Hypothesis: `ℕ → ℂ` agrees pointwise with `r8` (embedded in `ℂ`). |
| `Hqiv.Algebra.thetaZ8FormalCoeffComplex` / `Hqiv.Algebra.coeffsAgree_thetaZ8FormalCoeffComplex` | Canonical coerced stream; trivially satisfies `CoeffsAgreeWithR8`. |
| `Hqiv.Algebra.thetaZ8LSeriesCoeff` / `Hqiv.Algebra.thetaZ8LSeriesCoeff_succ` | Mathlib `LSeries` coefficients (`0 ↦ 0`, index `n+1 ↦ r8 n`); matches `thetaZ8FormalCoeff` (`ThetaZ8LSeriesScaffold`). |
| `Hqiv.Algebra.ThetaZ8ModularFormWitness` / `Hqiv.Algebra.thetaZ8LevelOneE4Witness` | Weight-`4` modular data (`Γ`, `ModularFormClass`, `q`-period); concrete witness = Mathlib Eisenstein `E 4` (not θ\_{ℤ⁸} coefficients). |
| `Hqiv.Algebra.ThetaZ8ModularRealization` | Extends the witness with `coeff_eq`: `qExpansion` coefficients = `(r8 m : ℂ)` — **open** (classical θ identification). |
| `Hqiv.Algebra.exists_thetaZ8_modular_realization` | `Nonempty ThetaZ8ModularFormWitness` (**proved** via `thetaZ8LevelOneE4Witness`). |
| `Hqiv.Algebra.norm_thetaZ8LSeriesCoeff_le` / `Hqiv.Algebra.abscissaOfAbsConv_thetaZ8LSeriesCoeff_le_nine` | `O(n⁸)` norm bound ⇒ abscissa of absolute convergence `≤ 9` (Dirichlet/analytic hook; not a modular-form theorem). |

## Completed L-function / functional equation bridge (`Hqiv.Algebra.ThetaCompletedLFunctionalScaffold`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Algebra.completedLFunction_modOne_apply` | For `χ : DirichletCharacter ℂ 1`, `completedLFunction χ s = completedRiemannZeta s` (Mathlib). |
| `Hqiv.Algebra.completedLFunction_modOne_one_sub` | Same `χ`: `completedLFunction χ (1 - s) = completedLFunction χ s` — **proved** FE (inherits Λ symmetry). |
| `Hqiv.Algebra.CompletedLFunctionalInvolutionHypothesis` / `Hqiv.Algebra.WeightFourCompletedLInvolutionHypothesis` | **Hypothesis** target `Λ(k-s)=Λ(s)` (weight `4` abbrev); **not** proved for `thetaZ8LSeriesCoeff`. |
| `Hqiv.Physics.hqivDirichletSeries_eq_LFunction_modOne_of_hqivCoeff_one` | `hqivCoeff ≡ 1`, `1 < re s` ⇒ `hqivDirichletSeries … s = DirichletCharacter.LFunction χ s` for any `χ : DirichletCharacter ℂ 1` (`HQIVLSeriesAnalytic`). |
| `Hqiv.Physics.hqivDirichletSeries_eq_LSeries_trivialCharacter_of_hqivCoeff_one` | Same hypotheses ⇒ equality with naive `LSeries (χ ·) s` (`LFunction_eq_LSeries`). |
| `Hqiv.Physics.ne_zero_of_one_lt_re` | `1 < re s` ⇒ `s ≠ 0` (for `riemannZeta_def_of_ne_zero` / gamma-factor identities). |
| `Hqiv.Physics.even_dirichletCharacter_modOne` | Any `χ : DirichletCharacter ℂ 1` is **even** (`χ.Even`). |
| `Hqiv.Physics.hqivDirichletSeries_eq_completedRiemannZeta_div_Gammaℝ_of_hqivCoeff_one` | `hqivCoeff ≡ 1`, `1 < re s` ⇒ `hqivDirichletSeries … = completedRiemannZeta s / Gammaℝ s` (Λ factorization). |
| `Hqiv.Physics.hqivDirichletSeries_eq_completedLFunction_div_gammaFactor_of_hqivCoeff_one` | Same ⇒ `= completedLFunction χ s / gammaFactor χ s`. |
| `Hqiv.Physics.hqivDirichletSeries_eq_completedLFunction_div_Gammaℝ_of_hqivCoeff_one` | Same ⇒ `= completedLFunction χ s / Gammaℝ s` (mod-1 even character). |
| `Hqiv.Physics.Gammaℝ_ne_zero_of_one_lt_re` | `1 < re s` ⇒ `Gammaℝ s ≠ 0` (Deligne gamma nonvanishing on that half-plane). |
| `Hqiv.Physics.completedLFunction_eq_hqivDirichletSeries_mul_gammaFactor_of_hqivCoeff_one` | `hqivCoeff ≡ 1`, `1 < re s`, `gammaFactor χ s ≠ 0` ⇒ `completedLFunction χ s = hqivDirichletSeries … s · gammaFactor χ s`. |
| `Hqiv.Physics.completedLFunction_eq_hqivDirichletSeries_mul_Gammaℝ_of_hqivCoeff_one` | Same (no extra hypothesis): `completedLFunction χ s = hqivDirichletSeries … s · Gammaℝ s`. |
| `Hqiv.Physics.hqivDirichletSeries_eq_const_smul_riemannZeta_of_hqivCoeff_const` | `hqivCoeff ≡ c₀`, `1 < re s` ⇒ `hqivDirichletSeries … = c₀ · ζ(s)` (`LSeries_smul`). |
| `Hqiv.Physics.hqivDirichletSeries_eq_const_smul_completedRiemannZeta_div_Gammaℝ_of_hqivCoeff_const` | Same ⇒ `= c₀ · (completedRiemannZeta s / Gammaℝ s)`. |
| `Hqiv.Physics.completedLFunction_eq_LFunction_mul_gammaFactor_of_gamma_ne_zero` | Mathlib: `completedLFunction χ s = LFunction χ s · gammaFactor χ s` when `gammaFactor χ s ≠ 0` (and `s ≠ 0 ∨ N ≠ 1`). |
| `Hqiv.Physics.LFunction_mul_gammaFactor_modOne_one_sub` | Modulus `1`, `s ≠ 0,1`, gamma factors nonzero at `s` and `1-s` ⇒ `L(1-s)·γ(1-s) = L(s)·γ(s)` (Λ symmetry for the **L·γ** product). |

**Narrative:** Trivial-character / `hqivCoeff ≡ 1` branch matches ζ, **`LFunction`**, and inherits the completed ζ FE (`ThetaCompletedLFunctionalScaffold`); `r₈` is **not** a Dirichlet character series — modular identification for Θ₈ remains open. See module doc and [MODULAR_THETA_CURVATURE_BRIDGE.md](./MODULAR_THETA_CURVATURE_BRIDGE.md).

**Next:** Mathlib `ModularForm` / classical θ `q`-expansion identification — still not proved for `r₈`; `LSeries` + trivial FE hooks are in place. See [MODULAR_THETA_ACTION_PLAN.md](./MODULAR_THETA_ACTION_PLAN.md) (P2–P3).

Narrative / open items (parked): [archive/OCTONION_SPHERE_PATCH.md](./archive/OCTONION_SPHERE_PATCH.md).

## Ω–axis angles (`Hqiv.Algebra.OctonionAxisAngles`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Algebra.intrinsicShellAxisAngle` / `Hqiv.Algebra.intrinsicShellAxisAngle_eq` | For `m > 1`, angle `π / (2 · Ω m)` with `Ω` = total prime factors (multiplicity). |
| `Hqiv.Algebra.intrinsicShellAxisAngle_of_prime` | Prime `p > 1` ⇒ angle `π/2`. |
| `Hqiv.Algebra.intrinsicShellAxisAngle_eq_axisAngle_of_Omega` | If `Ω m = k` then `intrinsicShellAxisAngle m hm = axisAngle k hk` (= `π/(2k)`). |
| `Hqiv.Algebra.two_mul_axisAngle_eq_pi_div_k` | `2 · axisAngle k hk = π / k` (two per-step increments span arc `π/k`). |
| `Hqiv.Algebra.exists_one_lt_intrinsicShellAxisAngle_eq_pi_div_two_k` | For each `k ≥ 1`, some `m > 1` has `Ω m = k` and `intrinsicShellAxisAngle m = π/(2k)` (packages `exists_one_lt_with_Omega_eq` + angle formula). |
| `Hqiv.Algebra.quarkPole` | Six nonzero Fano directions `1…6` in `Fin 7` (EM at `0`). |
| `Hqiv.Algebra.kthRootUnityAngle` | Standard roots-of-unity angles `2π j / k` (separate normalization from `π/(2k)`). |

**Caveat:** This is **definitional** alignment (`Ω` → angle), not a proof that an external harmonic pipeline recovers these angles without fixing that map.

## Moiré jerk ↔ Ω / `A₇` proxy (`Hqiv.Archive.Algebra.MoireJerkSphereModeBridge`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Algebra.moireSecondDiff` / `Hqiv.Algebra.moirePatchSlopeStep_eq_second_diff` | Discrete second difference along the patch equals `moirePatchSlopeStep` (jerk). |
| `Hqiv.Algebra.real_second_diff_sin` / `Hqiv.Algebra.moirePatchSlopeStep_sin` | Pure sinusoid score `sin(α + β·j)` ⇒ jerk `−4 sin(·) sin²(β/2)` on interior indices. |
| `Hqiv.Algebra.moirePatchSlopeStep_sin_axisAngle` / `Hqiv.Algebra.sin_sq_axisAngle_div_two` | Same with `β = axisAngle k`; `sin²(axisAngle k / 2) = sin²(π/(4k))`. |
| `Hqiv.Algebra.moirePatchSlopeStep_sin_intrinsic_of_Omega` | If `Ω m = k` and `S(j) = sin(α + intrinsicShellAxisAngle m · j)`, jerk carries factor `sin²(π/(4k))`. |
| `Hqiv.Algebra.moirePatchSlopeStep_sin_intrinsic_eq_zero_iff` | In that intrinsic sinusoid model, jerk vanishes iff midpoint sine or `sin(π/(4k))` is zero (no third “Ω-free” channel). |
| `Hqiv.Geometry.planeCirclePoint` / `norm_sq_planeCirclePoint` / `intrinsicKShellPlaneArc` / `exists_shell_pi_over_two_k_axis` / `axisAngle_two_step_span_pi_div_k` | **SAT rapidity plane:** embeds the `π/(2k)` / `Ω` shell axis (`OctonionAxisAngles`) in `EuclideanSpace ℝ (Fin 2)`; `dist (γ θ) 0 = |M|`; forwards existence of shells with `Ω m = k` and two-step span `π/k`; ribbons → annulus via `inAnnulus_of_shell_arc_ribbon` (`SATRapidityAnnulusCircle`). |
| `Hqiv.Algebra.continuousSphereArea7_eq_deriv_volume` | Restates `dV₈/dr = A₇` (`deriv_continuousBallVolume8` in `OctonionSphereConstruction`). |

**Scope:** Closed-form lemmas assume the **named** sinusoid on `Fin n`; bridging a pipeline score to that model (or to `fourierPatchPeakCorrelation`) remains separate — see [archive/OCTONION_SPHERE_PATCH.md](./archive/OCTONION_SPHERE_PATCH.md) and [archive/FT_PATCH_CLOSED_TARGET.md](./archive/FT_PATCH_CLOSED_TARGET.md). **BST** (`Hqiv.Archive.Algebra.MoireToyThresholdSearch`) addresses **unique least** threshold crossings on monotone `cum`, not uniqueness of a jerk argmax.

## CNF / SAT search scaffolds (`Hqiv.Archive.Logic.CNFPatchBridge`, `Hqiv.Geometry.GeneralizedGeometricOracle`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.CNFFormula.satisfiable_iff_exists_patch_index` | For `CNFFormula n`, satisfiable iff some `j : Fin (2 ^ n)` works under `assignmentFromPatchIndex`; this is the exact patch-index / exhaustive-enumeration bridge in `CNFPatchBridge`. |
| `Hqiv.Geometry.prune_boundary_family_generates_seed_gap` | Concrete near-degenerate witness theorem: at the unit prune boundary, the retained witness stays optimal in the pruned family and `seedCost ≤ optimalCost + (δ : ℝ) + tensorResidualErr + rapidityErr + axisErr`. |
| `Hqiv.Geometry.recursiveCandidateBudget` / `Hqiv.Geometry.recursive_level_count_bounded` | Generic explored-search budget for recursive candidate pipelines: level `depth` is bounded by `topk * beam^depth` when one-step branching is bounded by `beam`. |
| `Hqiv.Geometry.recursive_level_count_lt_factorial_of_budget` / `Hqiv.Geometry.departed_degeneracy_certificate_implies_subfactorial_search` | If the certified recursive budget is `< Nat.factorial tourArity`, then the explored recursive level is **strictly subfactorial**. |
| `Hqiv.Geometry.ReducedFrontierDegeneracyProfile` / `Hqiv.Geometry.reduced_frontier_profile_budget_lt_factorial` | Packages a positive degeneracy departure together with reduced frontier / `topk` / `beam` / `depth` controls and proves the induced recursive budget is `< tourArity!`. |
| `Hqiv.Geometry.recursive_level_count_le_of_beam_slack` / `Hqiv.Geometry.reduced_frontier_profile_implies_explicit_search_bound` | Sharper search-space theorem: if `beam + slack ≤ frontierArity`, then explored search is bounded by `topk * (frontierArity - slack)^depth`, not just by the frontier base itself. |
| `Hqiv.Geometry.slackFromGap` / `Hqiv.Geometry.beam_add_slackFromGap_le_frontier` / `Hqiv.Geometry.reduced_frontier_profile_implies_gap_slack_search_bound` | Canonical **gap-to-slack** bridge: extract admissible slack from integer gap data `δ` via `min (frontierArity - beam) (Int.toNat δ)`, then feed it into the explicit search bound. |
| `Hqiv.Geometry.prune_boundary_family_departure_implies_gap_slack_search_bound` | Strongest current concrete SAT-search scaffold: a pruned near-degenerate family gives (i) optimal witness in the pruned family, (ii) the real seed-gap bound, and (iii) an explicit explored-search bound using canonical slack derived from `δ`. |
| `Hqiv.Geometry.K_exactUnionCard_le_two_mul_of_planeLocalShell` / `K_exactUnionCard_le_two_mul_arcRibbonCount` / `residualCount_le_two_mul_countBound_of_plane` | Chains `SATRapidityAnnulusCircle` (≤2 points per `C_q ∩ C_{shellR}`) into `K_exactUnionCard` and residual-length bounds; combines with `ArcRibbonLatticeCardBound` (`SATRapidityPlaneBridge`). |
| `Hqiv.Geometry.PlaneWitnessMap` / `planeCenterOfResidual` | **Option A encoding:** abstract manifold `M` unchanged; `ResidualPoint M → Plane` composed with `residualPoint` to place shell centers for planar lemmas (`SATRapidityPlaneBridge`). Plane predicate renamed `planeLocalShellIntersections` (vs scaffold `localShellIntersections` on `Finset ℕ`). |
| `Hqiv.Geometry.direction_selection_with_plane_witness_implies_gap_bridge` / `sat_rapidity_gap_bridge_implies_geometric_collapse` / `direction_selection_geometric_collapse_via_gap_bridge_eq` | End-to-end packaging of SAT rapidity control: direction-selection + plane witness hypotheses are enough to construct the gap bridge and recover the geometric-collapse certificate in one theorem pipeline (`SATRapidityPlaneBridge`, `SATRapidityGapBridge`). |
| `Hqiv.Geometry.ribbon_cover_collapse` / `ribbon_cover_collapse_hasPolynomialResidualBudget` / `ribbon_cover_collapse_implies_nat_root_envelope` | Strongest current annulus/ribbon cover package: once exact-frontier cover data is supplied, residual search is formally polynomially bounded and translated into a natural root-envelope bound for follow-on arithmetic filtering (`SATRapidityPlaneBridge`). |
| `Hqiv.Geometry.factorPair_from_3spiral_correct` / `pickFromCandidates_sound` / `chart_bridge_and_picker_sound` / `factorTree_prod_eq` / `OneStepPickCertificate.sound` / `OneStepPickCertificate.pair_product` / `allCandidates_length` / `factorPair_candidate_scan_le_budget` / `factorPair_from_3spiral_is_O1` / `Bridge.firstValidDivisor_scanCost_le_length` / `Bridge.allCandidatesWithCurvature_length` / `Bridge.pickFromCandidates_scanCost_le_seven` | Rapidity-polar factor oracle chain: locked-shell hypotheses certify returned factors multiply to `m`; candidate picker remains divisor-sound under arbitrary curvature-density proposals; recursive `factorTree` is product-preserving; new certificate wrapper packages one-step picks in a single object with theorem-backed nontrivial-divisor and pair-product outputs; and the scan-cost side is now explicit: generic `firstValidDivisor` scan cost is bounded by input list length, with a specialized curvature-candidate bound `≤ 7`, yielding certified O(k) (generic list) and O(1) (current fixed-candidate scaffold) statements (`RapidityPolarFactorOracle`). |

## Shell index `m+1` ↔ classical ζ / Λ (`Hqiv.Physics.ShellIndexRiemannZetaBridge`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.riemannZeta_tsum_succ_eq` | For `Re s > 1`, `ζ(s) = ∑' n, 1/(n+1)^s` (same `(n+1)` shift as `hqivDirichletTerm`). |
| `Hqiv.Physics.completedRiemannZeta_functional_symmetry` | `completedRiemannZeta (1 - s) = completedRiemannZeta s` (Mathlib Λ(s)). |
| `Hqiv.Physics.riemannZeta_trivial_zero_at_neg_two_mul_succ` | `ζ(-2(n+1)) = 0` (trivial zero ladder). |
| `Hqiv.Physics.shell_succ_mod_four_eq_one_or_three_of_even` | Even `m` ⇒ `(m+1) % 4 ∈ {1,3}` (odd shell labels mod 4). |
| `Hqiv.Physics.hqivDirichletSeries_eq_tsum_succ_of_coeff_one` | If all `hqivCoeff = 1`, HQIV Dirichlet series equals the same `∑' n, 1/(n+1)^s` on `Re s > 1`. |

**Caveat:** No automatic link to `effCorrected` phases or tomographic mod‑4 selection; trivial zeros are classical ζ facts, not HQIV poles.

## Division-algebra zeta scaffold + millennium **probes** (`DivisionAlgebraZetaScaffold`, `SpatialSliceRapidityScaffold`, `LatticeNextPrimeGenerator`, `CycleHodgeProbeScaffold`)

**Caveat (lattice next-“prime” scaffold):** The **composed** walk `decompose_to_fano_moduli → … → next_prime_generator` is **not** a correct or complete end-to-end algorithm (greedy real product ≠ decomposition of `x`; packing/rapidity stages not wired into `next_prime_generator`). See the module doc in `Hqiv.Physics.LatticeNextPrimeGenerator` and [QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md](./QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md) §0.

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.zetaR1_latticeTerm` / `zetaR1_latticeTerm_deltaE` | No-phase shell term vs same with `cexp (I * φ * t * deltaE m)`; summability / norm lemmas mirror `zetaHQIVTerm` where stated. |
| `Hqiv.delta_theta_prime_eq_arctan_mul_pi_div_two` | `δθ′(E′) = arctan(E′)·(π/2)` (`OMaxwellAlgebraSeed`); horizon quarter-period is **π/2**, not **2/π**. |
| `Hqiv.Physics.zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity` / `zetaHQIVTerm_cexp_eq_cexp_polarAngleFromRapidity` / `zetaHQIVTerm_eq_effCorrected_mul_cexp_polarAngleFromRapidity` | `zetaHQIVTerm` phase exponent **equals** `I * polarAngleFromRapidity` / `cexp` thereof (`RapidityZetaPhaseBridge` — geometry spiral and zeta channel identified in Lean). |
| `Hqiv.Algebra.shellResidueFano_of_f_val_add_seven_mul` / `Hqiv.Physics.fano_vertex_of_shell_f_val_add_seven_mul` | Fano residue strand `f.val + 7·k` carries tag `f`; zeta seven-way sum aligns with algebra `shellResidueFano` (`CycleHodgeProbeScaffold` / `DivisionAlgebraZetaScaffold`). |
| `Hqiv.Physics.HodgeClassProbe_eq_mul_of_FanoPeriodRapidityCoincidence` / `zetaHQIVTerm_eq_eff_mul_cexp_polarAngle_of_coincident_rapidity` | Under `FanoPeriodRapidityCoincidence`, Hodge probe = `φ·t`; if `φ,t` match the bundle, `zetaHQIVTerm` phase uses `polarAngleFromRapidity` (`HodgeRapidityZetaBridge` — **scaffold coherence**, not classical Hodge). |
| `Hqiv.Geometry.PlasticZetaPhaseProbe` / `PlasticZetaPhaseProbe.nearZeroWitness` / `PlasticZetaPhaseProbe.existsStepWithPhaseLink` | Lean-facing hypothesis bundle for plastic/root-scale zeta probing: sampled snaps `(p,m,k)`, rapidity-phase link `polarAngleFromRapidity φ t m` to a zeta-phase channel at `tEff`, and a near-known-zero witness with small `|ζ(1/2 + i·tEff)|` (probe scaffold, not a classical RH theorem). |
| `Hqiv.Geometry.InterceptOrderClassification` / `intercept_order_classification` / `Hqiv.Geometry.ZeroChannelOfInterceptProfile` / `zero_channel_of_intercept_profile` | Theorem-shape bridge for the plastic arity claim: composite shells admit higher-order intercepts (`k ≥ 3`), prime/two-power shells are low-order (`k ≤ 2`), and intercept-profile compatibility yields a `PlasticZetaPhaseProbe`-style near-zero witness. |
| `Hqiv.Story.TwoArityPoleDischarge` / `Hqiv.Story.HighArityInterceptTheory` / `Hqiv.Story.ArityInterceptClassification` / `arity_intercept_proof_spine` / `prime_no_intercepts_in_proof_range` | Story-level proof spine: discharge arity-2 pole channel (`2` / two-powers) separately, then state the arithmetic proof range on `k ≥ 3` (composites have intercepts, primes do not). |
| `Hqiv.Story.spiralPlasticNumber` / `Hqiv.Story.spiralPlasticAngle` / `Hqiv.Story.spiralOrbitStep` / `Hqiv.Story.plasticSpiralPhaseAtStep` / `Hqiv.Story.exists_spiral_orbit_step_eq` / `Hqiv.Story.InterceptAlignedOnPlasticSpiral` / `Hqiv.Story.intercept_on_spiral_from_global_witness` | **Proved** discrete plastic scaffold: `spiralPlasticNumber` / `spiralPlasticAngle` **alias** `Hqiv.Geometry.plasticNumber` / `plasticAngle` (`GeneralRiemannianRapidityOracle` — unique `ρ > 0` with `ρ³ − ρ − 1 = 0`, not a free decimal); orbit map `spiralOrbitStep m = m`, phase `spiralPlasticAngle * m`, alignment predicate `InterceptAlignedOnPlasticSpiral`, witness eliminators. Unconditional “every arithmetic intercept hits some bounded spiral step” remains external number theory until discharged. |
| `Hqiv.Physics.zetaR1_latticeTerm_deltaESlot` / `zetaR1_latticeTerm_deltaE_quaternionicCandidate` / `zetaR1_latticeTerm_deltaE_quaternionicCandidate_eq_geometric` / `zetaR1_deltaE_phaseSlot_ne_quaternionicCandidate` / `zetaR1_deltaE_geometricQuaternionicSlot_ne_deltaE` | Arbitrary per-shell phase slot `δslot : ℕ → ℝ`; **summable for all** `δslot` (`Re s > 1`); agrees with `zetaR1_latticeTerm_deltaE` when `δslot` matches `deltaE` / `deltaE_geometricModel` under explicit hypotheses. The quaternionic comparison slot `6^3 * sqrt(3) * shell_shape` also threads through the same geometric/zeta bridge, but Lean proves it is still **not** the canonical HQIV `deltaE` slot on the current shell ladder. |
| `Hqiv.Physics.zetaR1_latticeTerm_monogamic3DRamanujanTerm` / `zetaR1_monogamic3DRamanujanSum_eq_tsum` | Step-wise rapidity `phi_t_step : ℕ → ℝ` in the same discrete `m : ℕ` shell sum; curvature via `δslot : ℕ → ℝ`. |
| `Hqiv.Physics.zetaR1_latticeTerm_monogamic3DRamanujanTerm_summable_of_re_gt_one` | `Summable` of the step-wise monogamic term family when `Re s > 1` and denominators stay positive. |
| `Hqiv.Physics.zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_zetaR1_latticeTerm_deltaESlot_of_const_phi_t` | If `phi_t_step m = φt` for all `m`, the monogamic term matches the existing `δslot` phase term (with convention `t = 1`). |
| `Hqiv.Physics.zetaR1_deltaESlotSum` / `zetaR1_deltaESlotSum_eq_of_slot_eq` | Constant-`φt` sum on an arbitrary curvature slot; shellwise slot equality implies full `tsum` equality. |
| `Hqiv.Physics.zetaR1_monogamic3DRamanujanSum_eq_of_slot_eq` | Shellwise equality of `δslot` implies equality of the monogamic step-wise `tsum`. |
| `Hqiv.Physics.zetaR1_monogamic3DRamanujanSum_eq_zetaR1_deltaESlotSum_of_const_phi_t` | Sum-level collapse from step-wise `phi_t_step` to constant `φt` (again with `t = 1`). |
| `Hqiv.Physics.zetaR1_monogamic3DRamanujanSum_eq_sum_residue_ZMod7` / `zetaR1_monogamic3DRamanujanSum_eq_sum_Fano_residue_classes` | Mod-7 / Fano residue decomposition for the monogamic sum (assuming summability). |
| `Hqiv.Physics.criticalLineReHalf` / `mem_criticalLineReHalf_iff` | Subset of ℂ with \(\Re z = 1/2\) (RH language; no zeros proved). |
| `Hqiv.Physics.rationalTilt` | `ℚ → ℝ` cast for rational **tilt** bookkeeping. |
| `Hqiv.Physics.norm_zetaR1_latticeTerm_eq_zpow_re_half` / `norm_zetaR1_latticeTerm_deltaE_eq_zpow_re_half` | On `s.re = 1/2`, shell-term norms are `eff^(-1/2)`. |
| `Hqiv.Physics.fano_prime_pred_eq_val` | `fano_prime f - 1 = f.val` (Euler-factor shell index in `OctonionicZeta`). |
| `Hqiv.Physics.CriticalLineRationalFanoOctonionProbe` / `CriticalLineRationalFanoOctonionProbe.re_eq_half` | Single record: critical-line `s`, rational `qtilt`, Fano vertex `f`. |
| `Hqiv.Physics.zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_of_const_rat_tilt` | Constant rational tilt on all shells ⇒ monogamic term matches `zetaR1_latticeTerm_deltaESlot` with `φ = rationalTilt q`, `t = 1`. |
| `Hqiv.Geometry.LagrangianDensity` / `pullbackLagrangianDensity` / `constantLagrangianDensity` / `lagrangianFromChart` / `lagrangianFromChart_comp` | Abstract continuum **Lagrangian density** `M → ℝ` on any carrier `M`; pullback along `N → M`; chart pullback from coordinate `Λ : (Fin d → ℝ) → ℝ`; functoriality (`ManifoldLagrangianScaffold`). |
| `Hqiv.Geometry.LatticeContinuumActionCoincidence` (`discreteProxy`, `continuumProxy`, `discrete_eq_continuum`) / `LatticeContinuumActionCoincidence.refl` | Hypothesis bundle pairing a discrete action proxy with a continuum value; trivial diagonal instance (`ManifoldLagrangianScaffold`). |
| `Hqiv.Geometry.SpatialSliceEuclidean3` / `euclideanHorizonShell` / `ShellFamilyPairwiseDisjoint_euclideanHorizonShell` | Flat `l²` model `EuclideanSpace ℝ (Fin 3)`; nested balls/annuli `ShellFamily`; pairwise disjoint under `StrictMono r`. |
| `Hqiv.Geometry.measurableSet_euclideanHorizonShell` / `volume_euclideanHorizonShell_lt_top` / `euclideanShellVolumeReal` | Borel measurability; finite Lebesgue volume per shell; real volume via `ENNReal.toReal`. |
| `Hqiv.Geometry.spatialSliceToSpacetimeCoords` / `spacetimeThinSlice` | `Fin.cons` embed into `Fin 4 → ℝ` (time index `0`); image of a spatial set at fixed time. |
| `Hqiv.Geometry.maxNatAbsCoord` / `latticeMaxAbsShell` / `latticeMaxAbsShell_disjoint_of_ne` / `latticeMaxAbsShell_zero` | Integer `Fin 3 → ℤ` **lattice-point** shells by `sup_i \|p i\|` (Chebyshev / L∞-style); pairwise disjoint; layer `0` = origin only (`LatticePointMaxAbsShells`). |
| `Hqiv.Geometry.joinThirdCoordinate` / `planarHead` / `mem_closedBall_joinThirdCoordinate_iff` / `closedBall_inter_coordPlane_eq_image_slice` | Horizontal slice of `closedBall 0 R` at fixed third coordinate `z` is the embedded planar `closedBall` of radius `√(R²−z²)` (`EuclideanBallHorizontalSlice`). |
| `Hqiv.Geometry.coordPlaneIsometry` / `joinCoordinateSlice` / `mem_closedBall_joinCoordinateSlice_iff` / `closedBall_inter_coordPlane_k_eq_image_slice` | Same slice identity for **any** coordinate hyperplane `x k = z` (coordinate permutation isometry `piLpCongrLeft`). |
| `Hqiv.Geometry.piSliceAreaBaseline` / `sliceAreaDefect` / `observedArea_eq_piBaseline_add_sliceAreaDefect` / `sliceAreaDefect_eq_zero_iff` | Formalizes the Euclidean `π` baseline area for slices and the measurable/model **difference** (`observed - baseline`) as a first-class quantity. |
| `Hqiv.Geometry.piSliceAreaBaselineAt` / `sliceAreaDefectAt` / `observedArea_eq_piBaselineAt_add_sliceAreaDefectAt` / `sliceAreaDefectAt_eq_zero_iff` | Shell-indexed (`m : ℕ`) version of the same baseline/gap bookkeeping using radius ladder `r (m+1)`. |
| `Hqiv.Geometry.spacetimeCoordsEquiv_spacetimeOfCoords` / `spacetimePointFromSpatialSlice` / `mem_spacetimeThinSlice_iff` | Continuum-chart round-trip; point in `SpacetimeEuclidean4` from slice; thin-slice membership (`SpatialSliceContinuumBridge`). |
| `Hqiv.Geometry.rVolFromGeometricModelTarget` / `deltaE_geometricModel_rVolFromGeometricModelTarget_eq` / `deltaE_geometricModel_rVolFromDeltaE_eq` / `deltaE_geometricModel_rVolFromQuaternionicCandidate_eq` / `deltaE_geometricModel_rVolFromQuaternionicCandidate_ne_deltaE` | Algebraic inverse for `R_vol` in `deltaE_geometricModel`; specialization to combinatorial `deltaE`, and parallel specialization to the quaternionic comparison imprint. The latter passes through the same inverse/geometry slot but is proved **not** to reproduce the canonical combinatorial `deltaE`. |
| `Hqiv.Geometry.deltaE_geometricModel_geometricScalarSlotFromShellVolume_eq_deltaE` / `agreesWithCombinatorialDeltaE_deltaE_geometricModel_of_shellVolume_matches_rVol` | If scaled Lebesgue volume equals `rVolFromGeometricModelTarget deltaE` shellwise, geometric model matches `deltaE`; packaged `agreesWithCombinatorialDeltaE` for the composed per-shell output. |
| `Hqiv.Geometry.deltaE_geometricModel` | Formula `(1/(m+1))(1 + α·R_vol(m))·curvature_norm_combinatorial`; `R_vol` is user data (narrative: curvature integral slot), not built from a metric. |
| `Hqiv.Geometry.agreesWithCombinatorialDeltaE_geometricModel_iff` | `agreesWithCombinatorialDeltaE (fun k => deltaE_geometricModel R k) m ↔ deltaE_geometricModel R m = deltaE m`. |
| `Hqiv.Geometry.IntegratedScalarCurvatureSlot` / `deltaE_geometricModel_fromIntegratedScalarCurvature_eq` | Integrated scalar-curvature slot (abstract `m ↦ Rint(m)`) and simp lift: `deltaE_geometricModel_fromIntegratedScalarCurvature Rint m = deltaE_geometricModel Rint m`. |
| `Hqiv.Geometry.fanoContourPeriodSum` / `fanoContourPeriodSum_eq_seven_mul` | Sum of `PhiContourFunctional.eval` over seven `FanoVertex` paths; `7 * r` when each term is `r`. |
| `Hqiv.Geometry.FanoPeriodRapidityCoincidence` / `phi_t_eq_fanoContourPeriodSum` | Hypothesis bundle `timeAngle = fanoContourPeriodSum`; concludes `φ * t` equals that sum. |
| `Hqiv.Geometry.FanoPeriodRapidityCoincidence.phi_t_eq_periodMap_pairing` | Re-labelling lemma: `φ * t` equals the period-map pairing over the Fano-indexed cycle/path family. |
| `Hqiv.Geometry.HodgeClassProbe` / `FanoPeriodRapidityCoincidence.phi_t_eq_hodgeClassProbe` | Probe-level identification: `φ * t` equals the “Hodge class” value defined as the same Fano-summed period-map pairing. |
| `Hqiv.Physics.fano_vertex_of_shell_eq_algebra_shellResidueFano` | `fano_vertex_of_shell m = Hqiv.Algebra.shellResidueFano m` (`rfl`). |
| `Hqiv.Physics.haugenPrimeLift` / `haugenPrimeLift_gt` / `haugenPrimeLift_fano_vertex_val` / `haugenPrimeLiftIter` / `haugenPrimeLiftIter_strict_step` | Base layer for “critical lifts / Haugen primes”: transparent alias of `next_lattice_prime`, strict-growth step, Fano-tag compatibility, and iterated-lift recursion. |
| `Hqiv.Physics.tempLadderConserved` / `tempLadderRegularized` / `tHQIV` / `TempLadderBoundaryData` / `TempLadderForcesLambdaHQIVZero` / `lambdaHQIV_eq_zero_of_all_hyp` | Probe-level HQIV boundary-lock scaffold for conserved temperature ladders; explicit conditional `lambdaHQIV = 0` under hypothesis fields (analogue only, not classical de Bruijn–Newman `Λ`). |
| `Hqiv.Physics.TempLadderFiniteWindowWitness` / `toBoundaryData` / `toLambdaHQIVZero` / `lambdaHQIV_eq_zero_of_finiteWindowWitness` | Concrete finite-window witness layer turning checked range hypotheses into a proved `lambdaHQIV = 0` probe instance (`lambdaHQIV` chosen as `0` in the canonical constructor). |
| `Hqiv.Physics.TempLadderFiniteWindowConcrete` / `toFiniteWindowWitness` / `toLambdaHQIVZero` / `lambdaHQIV_eq_zero_of_finiteWindowConcrete` | Stronger finite-window scaffold with explicit `Finset.range N` conservation equation + regularization anchor + phase-lock relation, then bridged to the same proved `lambdaHQIV = 0` instance. |
| `Hqiv.paper_FLRW_node_Sgrav_iff_Friedmann` / `paper_FLRW_node_Sgrav_iff_CLASS_H2_rational` / `paper_FLRW_node_Sgrav_iff_CLASS_H2_rational_Geff_power` / `paper_standard_flat_GR_H2_iff_CLASS_rhoCrit` / `paper_FLRW_node_Sgrav_vacuum_iff_phi_zero` | **Single-node HQVM gravity ↔ Friedmann ↔ CLASS-style \(H^2\)** packaging (`S_HQVM_grav=0`, rational `15/13`, optional `G_eff=φ^α` for `φ≥0`), plus textbook flat `3H^2=8πρ` ↔ `H^2=ρ_crit` bridge and vacuum `φ=0`. **Not** full Boltzmann/ΛCDM pipeline (`HQVM_FLRW_PaperAlignment`). |
| `Hqiv.Physics.hqivFluidInertiaFactor` / `hqivVacuumMomentumSource3` / `hqivEddyViscosity` / `hqivEddyViscosity_HQIV` / `hqivFluidInertiaFactor_eq_one_of_phi_zero` / `hqivVacuumMomentumSource3_eq_zero_of_grad_zero` / `hqivEddyViscosity_HQIV_eq` | Effective modified-fluid closure (**definitions** matching `pyhqiv.fluid`; small algebraic lemmas). **Not** Navier–Stokes PDEs or O-Maxwell derivation (`HQIVFluidClosureScaffold`). |
| `Hqiv.Physics.spatialFin4` / `chartSpatialPhiGradient` / `chartSpatialDotGradient` / `OMaxwellFluidChartHypothesis` / `hqivVacuumMomentumSource3_of_OMaxwellFluidChartHypothesis` | **F2 typed chart hypothesis:** at `c : Fin 4 → ℝ`, fluid `(φ, ∇φ, δ̇θ′, ∇δ̇θ′)` identified with `φF c`, `coordsGradientComponents` on spatial indices, `delta_theta_prime Eprime`, and `∇dotF` — rewrites `hqivVacuumMomentumSource3` to pure chart data. **Not** a dynamical identification; see [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md) F2. |
| `Hqiv.Physics.PlasmaFluidClosureAssumptions` / `nuTotal_eq_nuMol_add_hqivEddy` | F3 hypothesis bundle: scalar viscosity split + HQIV eddy match + `C ∈ [0,1]`; proved consequence `ν_total = ν_mol + hqivEddyViscosity …` from the hypotheses. **Not** kinetic or Maxwell derivation. |
| `Hqiv.Physics.hqivEddyViscosity_nonneg` / `hqivEddyViscosity_pos` / `hqivEddyViscosity_HQIV_nonneg` / `hqivEddyViscosity_HQIV_shell_debye` / `hqivEddyViscosity_HQIV_shell_debye_eq` / `hqivEddyViscosity_HQIV_shell_debye_nonneg` / `hqivEddyViscosity_HQIV_shell_debye_pos` | Sign lemmas + **shell + Debye** specialization: `Θ_local = T m`, `ℓ_coh = lambdaDebye` in `hqivEddyViscosity_HQIV` (`HQIVFluidClosureScaffold`). **Not** a kinetic derivation. |
| `Hqiv.Physics.PlasmaFluidClosureAssumptions.mk_shell_debye` / `nuTotal_eq_nuMol_add_shell_debye` | F3 constructor + total viscosity rewrite when `Θ = T m` and `ℓ_coh = lambdaDebye`. |
| `Hqiv.abs_schematicPlasmaScalar` | `|schematicPlasmaScalar j₀ r| = |j₀| * plasmaRadialProfile r` (profile positive; `SchematicPlasmaCurrent`). |
| `Hqiv.J_O_plasma_eq_schematic_on_em` / `Hqiv.J_O_plasma_nonem_zero` / `Hqiv.abs_J_O_plasma_em` | EM leg of schematic current equals `schematicPlasmaScalar`; other octonion indices zero; `|J|` on EM leg = `|j₀| * plasmaRadialProfile` (`SchematicPlasmaCurrent`). |
| `Hqiv.L_O_source_general_J_O_plasma_plasmaProxyCoordUniform` / `Hqiv.coherenceFromPlasmaAmp_eq_min_mul_abs_schematic` / `Hqiv.plasma_action_coherence_same_schematic_core` | Uniform chart `plasmaProxyCoordUniform r`: `L_O_source_general` sums `schematicPlasmaScalar j₀ r * A 0 ν`; fluid `coherenceFromPlasmaAmp` uses `|schematicPlasmaScalar j₀ r|` — packaged together. (`ActionPlasmaBridge`) |
| `Hqiv.L_O_source_general_J_O_plasma_uniform_eq_j₀_mul_profile_mul_sum` / `Hqiv.coherenceFromPlasmaAmp_eq_min_mul_abs_j₀_profile` / `Hqiv.plasma_action_coherence_derived` / `Hqiv.plasma_action_coherence_derived_schematic` | **Algebraic derivation** from `schematicPlasmaScalar = j₀ * plasmaRadialProfile` and `abs_schematicPlasmaScalar`: `L_O` factors as `j₀ * plasmaRadialProfile r * ∑ A 0 ν`; coherence as `min 1 (κ * |j₀| * plasmaRadialProfile r)`. **Not** kinetic or variational physics. (`ActionPlasmaBridge`) |
| `Hqiv.L_O_source_general_J_O_plasma_uniform_add` / `Hqiv.hqivEddyViscosity_HQIV_shell_debye_plasmaAmp_eq_profile` / `Hqiv.nuTotal_eq_nuMol_add_shell_debye_plasmaAmp_profile` | Uniform-proxy superposition of `L_O` in `j₀`; shell+Debye eddy + F3 total viscosity with `min 1 (κ * |j₀| * plasmaRadialProfile r)` substituted. (`ActionPlasmaBridge`) |
| `Hqiv.L_O_Maxwell_general_add_J` / `Hqiv.action_O_Maxwell_general_add_J` / `Hqiv.action_total_general_add_J` | **Nonlinearity of full action density in `J`:** doubling `J₁+J₂` subtracts one copy each of kinetic, φ-coupling, and (for `action_total_general`) `S_HQVM_grav` versus naive sum of two densities — only `L_O_source_general` is linear in `J`. (`Action`) |
| `Hqiv.plasmaRadialProfile_le_one_of_nonneg` | For `r ≥ 0`, `plasmaRadialProfile r ≤ 1` (`SchematicPlasmaCurrent`). |
| `Hqiv.Physics.coherenceFromPlasmaAmp_mono_κ` / `coherenceFromPlasmaAmp_mono_abs_j₀` / `coherenceFromPlasmaAmp_eq_one_iff` / `coherenceFromPlasmaAmp_eq_mul_iff` | `min` bookkeeping: monotone in `κ` and in `|j₀|` (via `|schematicPlasmaScalar|`); `= 1` iff `1 ≤ κ*|schematic|`; `= κ*|schematic|` iff `κ*|schematic| ≤ 1`. (`HQIVFluidClosureScaffold`) |
| `Hqiv.Physics.coherenceFromPlasmaAmp` / `coherenceFromPlasmaAmp_mem_unit` / `hqivEddyViscosity_HQIV_shell_debye_plasmaAmp` | Closure choice: `C = min 1 (κ * |schematicPlasmaScalar|)` in `[0,1]` (`κ ≥ 0`); eddy viscosity at shell+Debye with that `C`. **Not** derived from kinetics. |
| `Hqiv.Physics.PlasmaFluidClosureAssumptions.mk_shell_debye_plasmaAmp` / `nuTotal_eq_nuMol_add_shell_debye_plasmaAmp` | F3 constructor + total viscosity when `C` comes from `coherenceFromPlasmaAmp`. |
| `Hqiv.Physics.BalancePillarShellDebyePlasmaAmp` / `balance_nuTotal_eq_mol_plus_eddy_shell_debye_plasmaAmp` / `BalancePillarWithHQIVGamma.of_shell_debye_plasmaAmp` | Pillar B with plasma-amplitude coherence (`LightConeFundamentalsPillars`). |
| `Hqiv.Physics.uvRegulatorShellBudget` / `uvRegulatorShellBudget_pos` / `kineticSpatialBinCount` / `HorizonExchangeCollisionRate` / `meanFreePathProxy` / `BalancePillarWithHQIVGamma` / `balance_nuTotal_eq_mol_plus_eddy_hqiv` / `BalancePillarShellDebye` / `balance_nuTotal_eq_mol_plus_eddy_shell_debye` / `BalancePillarWithHQIVGamma.of_shell_debye` / `KuboHQIVSpectralWeight` / `pillarD_same_phi_O_Maxwell_HQVM` / `pillarD_same_alpha_lattice` / `EffectiveDiracHypothesis` / `combinatorialEntropyHook` | **Pillar scaffold** tying [LIGHTCONE_FUNDAMENTALS_DERIVATION_PLAN.md](./LIGHTCONE_FUNDAMENTALS_DERIVATION_PLAN.md) to defs/hypotheses: cumulative mode budget = `available_modes`, kinetic bins, collision-rate placeholder, mfp proxy, fluid closure at fixed `gamma_HQIV` (including shell+Debye bundle), Kubo weight record, `GRFromMaxwell` bridges, Dirac mass slot, `log` mode-count hook. **Not** Boltzmann collision physics, Kubo coefficients, or Dirac PDE. |
| `Hqiv.Physics.kuboPhiSlopeAtShell` / `kuboPhiSlopeAtShell_eq` / `phi_of_T_increment_shell` / `linearizedLapse_from_shell` / `linearizedLapse_from_shell_kuboSlope` | Shell-indexed perturbations: Θ = `T m`, `deriv phi_of_T` slope, exact `phi_of_T` increment, Θ-channel lapse linearization = `t * kuboPhiSlopeAtShell * δΘ` (`HQIVPerturbationScaffold`; see [HQIV_PERTURBATION_THEORY_ROADMAP.md](./HQIV_PERTURBATION_THEORY_ROADMAP.md)). **Not** Bardeen/FLRW gauge pipeline. |
| `Hqiv.linearizedHQVM_g_tt_from_lapse` / `HQVM_g_tt_increment_eq_linearized_remainder` / `HQVM_g_tt_increment_eq_of_lapse_increment` | First metric readout of observer skew: because `g_tt = -N^2`, the exact timelike metric-coefficient increment splits into the linearized lapse-driven term `-2 N δN` plus the quadratic remainder `-δN^2` (`HQVMPerturbations`). |
| `Hqiv.Physics.rapidityNormalizedShellPhiIncrement` / `rapidityNormalizedShellPhiIncrement_eq_exp` / `rapidityNormalizedShellPhiIncrement_tendsto_zero` / `linearizedLapse_from_shell_rapidityNormalized` / `HQVM_lapse_increment_shell_rapidityNormalized` / `HQVM_g_tt_increment_shell_rapidityNormalized` / `HQVM_g_tt_increment_shell_rapidityNormalized_phiChannel` / `HQVM_spatial_coeff_increment_zero_of_pure_phi_channel` / `HQVM_metric_shell_rapidityNormalized_phiChannel_timelikeOnly` | Rapidity as observer-side skew normalization in the perturbation ladder: the shell-induced `δφ` is weighted by the same doubled observer-time transport law from `LightConeMaxwellQFTBridge`, decays at large budget, enters the exact homogeneous lapse increment with the same bilinear remainder `δφ * δt`, lands directly in the timelike metric coefficient `g_tt` with a linearized-plus-quadratic exact split, and leaves `HQVM_spatial_coeff` unchanged at this rung unless separate `δa` / `δΦ` data are added. |
| `Hqiv.Physics.rapidityNormalizedPotentialIncrement` / `rapidityNormalizedPotentialIncrement_eq_exp` / `rapidityNormalizedPotentialIncrement_tendsto_zero` / `HQVM_spatial_coeff_increment_rapidityNormalizedPotential` / `HQVM_spatial_coeff_increment_rapidityNormalizedPotential_linear` / `HQVM_spatial_coeff_increment_rapidityNormalizedPotential_homogeneous` / `HQVM_metric_shell_rapidityNormalized_withPotentialChannel` | Minimal extra spatial rung: the same observer-budget transport law can normalize a supplied Newtonian-potential increment `δΦ`, giving a theorem-backed way to move `HQVM_spatial_coeff` while keeping `δa = 0`. This packages the current scope cleanly: shell/`φ` channel drives the timelike metric readout, while a separately supplied normalized `δΦ` is the first legitimate mover of the spatial coefficient. |
| `Hqiv.Physics.CoefficientsTowardClassicalNS` / `hqivVacuumMomentumSource3_toward_classical_of_grad_zero` | F4 coefficient step (`f=1`, `g_vac=0`); example lemma when gradients vanish. **Not** classical 3D NS global theory. |
| `Hqiv.Physics.dimWeightNormalizer` / `dimShellWeight` / `tempLadderConserved_dimShellWeight` / `tempLadderConserved_dimShellWeight_R1,R2,R3,R4,R8` / `mkTempLadderFiniteWindowConcrete_dim` | Dimension-template base work (`p = dim - 1`) giving explicit finite-range conservation for shell ladders and ready-made concrete witness constructors in `R1,2,3,4,8`. |
| `Hqiv.Physics.shellCombinatoricWays` / `shellCombinatoricWays_R1,R2,R3,R4,R8` / `shellCombinatoricWays_R3_eq_half_latticeSimplexCount` / `haugenPrimeStepCandidateCount` | Combinatorics constructor layer for dimension curves (stars-and-bars shell multiplicities) plus a lift-gap candidate count interpreted as “ways per Haugen-prime step”. |
| `Hqiv.Physics.fanoLineWeight_fano_vertex_of_shell_eq` | `fanoLineWeight (fano_vertex_of_shell m) = (m % 7) % 3 + 1` (explicit `l_f` scaffold). |
| `Hqiv.Physics.FanoModulusStep` / `decompose_to_fano_moduli` / `decompose_last_shell` | Greedy ℝ¹ “Fano moduli” product along shells (`eff^l_f`); `phi_t_step` in signature but **ignored**; fuel-bounded loop. |
| `Hqiv.Physics.rapidity_effect_on_sphere` / `SphereEffect` | Stretch `eff(m+1)/eff(m)`, `max(divisors(m+1), divisors(m+2))`, slot `phi_t_step m * δslot m`. |
| `Hqiv.Physics.next_prime_generator` | `next_lattice_prime` from `decompose_last_shell` only — **not** a proved “next prime from `x`” procedure; same detuning / threshold API as `OctonionicZeta`. |
| `Hqiv.Physics.sliceDefectProfileAtZ` / `absSliceDefectProfileAtZ` / `nextShellDefectCandidate` / `nextShellDefectValue` / `IsGlobalPeak` / `IsGlobalAbsPeak` / `IsWindowPeak` / `IsWindowAbsPeak` / `isWindowAbsPeak_iff_range` / `candidate_isWindowAbsPeak_of_hyp` / `candidate_isWindowAbsPeak_of_rangeHyp` | Candidate-only bridge: use `next_prime_generator` output as a shell index to evaluate/scan geometric slice-defect profiles, including bounded-window peak predicates and `Finset.range` test form; no theorem that this candidate is the true global peak. |
| `Hqiv.Physics.decompose_*_eq_of_const_phi_t` / `next_prime_generator_eq_of_const_phi_t` | Step-wise `phi_t_step` drops out of decomposition / generator (`dsimp`/`rw`/`simp`). |
| `Hqiv.Geometry.SpherePackingInfo` / `spherePackingAtShell` | `eff` proxy, `#Nat.divisors (m+1)`, cyclic order `7` (probe; not sphere-packing theorem). |
| (narrative, not theorems) | [QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md](./QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md) — quantum-circuit / sparse-simulation mapping for the same pipeline; no complexity proofs in Lean. |
| `Hqiv.QuantumComputing.fanoLineCyclicPerm` / `fano_line_probability_mass_invariant` | `finRotate 7` on `Fin 7`; \(\sum_i p(\sigma i)=\sum_i p(i)\) (`Equiv.sum_comp`). |
| `Hqiv.QuantumComputing.hqiv_gate_trans_preserves_ip` | `discreteIp` preserved under `HQIVGate.trans` (re-states `HQIVGate` composition). |
| `Hqiv.QuantumComputing.latticeNextPrimePipelineStageCount` / `lattice_next_prime_pipeline_stages_eq_four` | Doc constant `4` for **narrative** stages only; does not assert the classical code implements all four or that the pipeline is correct. |
| `Hqiv.Geometry.ShellFamily` / `ShellFamilyPairwiseDisjoint` | `ℕ → Set M` shell tagging; optional disjointness `Prop`. |
| `Hqiv.Geometry.LatticeContinuumRapidityCoincidence` / `LatticeContinuumRapidityCoincidence.refl` | Pairs lattice vs continuum rapidity scalars; trivial diagonal instance. |
| `Hqiv.Geometry.latticeRapidity_eq_timeAngle` | `φ * t = timeAngle φ t`. |
| `Hqiv.Geometry.PhiContourFunctional` / `SpatialRapidityProbe` | Abstract `Path a b → ℝ` slot + bundled probe (no measures). |
| `Hqiv.Geometry.GeometricScalarCurvatureSlot` / `agreesWithCombinatorialDeltaE` | Per-shell `ℝ` slot vs `Hqiv.deltaE` as explicit `Prop`. |
| `Hqiv.Algebra.FanoIndexedCycles` / `canonicalFanoCycles` | Seven `C`-valued cycles per `FanoVertex`; identity instance surjective/bijective. |
| `Hqiv.Algebra.shellResidueFano` / `surjective_shellResidueFano` | `m % 7` as `FanoVertex`; surjective map `ℕ → FanoVertex`. |

**Scope:** probe types for `AGENTS/MANIFOLD_ZETA_ROADMAP.md` — not NS, not Hodge, not Ricci integrals unless future modules discharge new hypotheses.

**Narrative companion (not theorems):** [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md) — single standing-wave / horizon thread across RH / Yang–Mills / NS / Hodge at probe level, with self-clock as one candidate state-language; explicit “what is not claimed.”

## SO(8) closure (`Hqiv.GeneratorsLieClosure`, `Hqiv.SO8Closure`, `Hqiv.Algebra.SO8ClosureAbstract`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.so8_generators_linear_independent` | 28 generators linearly independent over ℝ. |
| `Hqiv.lieBracket_in_span` | Closure of Lie bracket in span of generators (coefficient expansion). |
| `Hqiv.generators_from_octonion_closure` | Narrative bridge: generators from octonion/Lie data (see statement). |
| `Hqiv.Algebra.span_G2_union_Delta_le_span_so8Generator` / `Hqiv.Algebra.finrank_span_G2_union_Delta_le_15` / `Hqiv.Algebra.exists_so8Generator_not_mem_span_G2_union_Delta` | Linear span of `G₂ ∪ {Δ}` is **≤15**-dimensional and lies in `span(so8)`; cannot exhaust 28-dim `𝔰𝔬(8)` (`SO8ClosureAbstract`). |
| `Hqiv.QM.opCommutator_smearedOpIntervalMax_pair` | Bilinear (double) sum for `opCommutator` of two smeared interval–max Pauli operators (`PatchIntervalMaxSmeared`). |
| `Hqiv.QM.continuum_interval_max_microcausality_operator_layer_notes` | Scalar interval-max microcausality + operator smearing vanishing packaged (`ContinuumManyBodyQFTClosureLink`). |

## Spin–statistics (`Hqiv.Physics.SpinStatistics`, namespace `Hqiv.Physics`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.HQIVFermionMode` / `HQIVBosonMode` / `HQIVMode` | Concrete shell-aware mode carriers: fermionic octonion-spinor modes plus bosonic observables carrying local patch support. |
| `Hqiv.Physics.hqivModeSpacelikeSep` | Concrete locality relation: same-shell modes whose primary `Fin 4` patches are Minkowski-spacelike via `PatchQFTBridge.patchChartPoint`. |
| `Hqiv.Physics.hqivModeSpacelikeSep_same_shell_spatial` / `hqivModeSpacelikeSep_has_witness` / `hqivModeSpacelikeSep_not_universal` | Witnesses that the concrete HQIV locality relation is genuine: some pairs are spacelike, and it is not the degenerate all-pairs relation. |
| `Hqiv.Physics.hqivTrialityObservable` | Triality-style bilinear witness preserving shell/patch support data instead of collapsing to a trivial bosonic slot. |
| `Hqiv.Physics.hqivTrialityObservable_support_data` | The triality observable always lands in the bosonic carrier and records the shell/patch pair determined by its input modes. |
| `Hqiv.Physics.hqivModePairObservableOp` / `hqivModePairObservableCommutatorY` (`SpinStatisticsOperatorBridge`) | Concrete smeared interval-max operator and Pauli-commutator attached to an HQIV mode pair via the exact patch support recorded by the spin-statistics layer. |
| `Hqiv.Physics.hqivModePairObservableOp_eq_zero_of_spacelike` / `hqivModePairObservableCommutatorY_eq_zero_of_spacelike` | Spacelike HQIV mode pairs induce vanishing smeared operator / Pauli commutator on `patchEventChartFour`, tying the mode-level spin relation to the operator-facing microcausal scaffold. |
| `Hqiv.Physics.HQIV_satisfies_SpinStatistics_from_triality_and_causality` | Main constructive satisfaction statement used by QM/QFT bridge modules. |

## QM / QFT horizon packages (`Hqiv.QuantumMechanics.*`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.QM.bornProbN_unique_of_coherence` | Finite `Fin n`: normalized nonnegative `p` with `BornCoherent ψ p` is uniquely `bornProbN ψ` (`BornRuleFirstPrinciples`). |
| `Hqiv.QM.born_from_coherence_unique` | Alias for `bornProbN_unique_of_coherence` (`BornGleasonDecisionScaffold`). |
| `Hqiv.QM.GleasonAnalyticTarget` / `Hqiv.QM.DecisionTheoreticBornTarget` | Scaffold types documenting the **Gleason** (projection-lattice measure) and **decision-theoretic Born** programs; not analytic proofs—see module doc (`BornGleasonDecisionScaffold`). |
| `Hqiv.QM.opCommutator` / `Hqiv.QM.smearedField_opCommutator_eq_zero` | Operator commutator on `LatticeHilbert n`; diagonal smeared fields commute (`HorizonFreeFieldScaffold`). |
| `Hqiv.QM.fieldOpFromChart` / `Hqiv.QM.fieldOpFromChart_microcausal_op` | Chart coordinates as weights on `LatticeHilbert 4`; abelian ⇒ commutator `0` (`MinkowskiFieldOperatorScaffold`). |
| `Hqiv.QM.matComm` / `Hqiv.QM.matComm_pauli_xy_entry00_ne_zero` | Pauli matrices: **nonzero** commutator entry (`PauliCommutatorExample`). |
| `Hqiv.QM.pauliX_intervalMax` / `Hqiv.QM.opCommutator_pauliX_intervalMax_pauliY` / `Hqiv.QM.opCommutator_toEuclideanLin_matComm` | Interval–max `max 0 η` as coefficient on `σ_x`; genuine `matComm` / `opCommutator` on `ℂ²` (`IntervalMaxOperatorCommutator`; not literal `[A,B]=I`, see `CCRFiniteDimObstruction`). |
| `Hqiv.QM.opCommutator_sum_finset_first` / `Hqiv.QM.opCommutator_sum_univ_first` | `opCommutator` is linear in the **first** argument; commutes with finite `Finset`/`Fintype` sums (`HorizonFreeFieldScaffold`). |
| `Hqiv.QM.opCommutator_pauliX_intervalMax_pauliY_eq_zero_of_comm_kernel_eq_zero` / `Hqiv.QM.chartLightlikeBoundaryExample` / `Hqiv.QM.opCommutator_pauli_intervalMax_lightlike_boundary_example` | `κ = max 0 η = 0` (lightlike boundary) ⇒ Pauli commutator lift `0` (`IntervalMaxOperatorCommutator`). |
| `Hqiv.QM.WeightSupportInRegionPair` / `Hqiv.QM.smearedOpIntervalMax` / `Hqiv.QM.smearedOpIntervalMax_patchEventChartFour_eq_zero_of_disjoint_spatial_regions` / `Hqiv.QM.opCommutator_smearedOpIntervalMax_pauliY_eq_zero_of_spacelike_support` | Bilinear smearing of interval–max Pauli ops on the patch; vanishing on η-spacelike support; disjoint spatial regions ⇒ `0` (`PatchIntervalMaxSmeared`). |
| `Hqiv.QM.Matrix.trace_commutator_eq_zero` / `Hqiv.QM.not_exists_matrix_CCR_one` | Trace kills **exact** `[A,B]=I` on fixed `Mat_{n×n}(ℂ)`; HQIV still uses **finite patches** + **limits**, not global `L²` as a formal requirement (`CCRFiniteDimObstruction`). |
| `Hqiv.QM.diagonalSmearedNet` / `Hqiv.QM.diagonalSmearedNet_isotony` / `Hqiv.QM.diagonalSmearedNet_commute_all_regions` | Constant diagonal local net; commuting observables across regions (`LocalAlgebraNetScaffold`). |
| `Hqiv.QM.WeightSupportInRegion` / `Hqiv.QM.patchAlgebraAt` / `Hqiv.QM.patchAlgebraAt_isotony` | Smeared weights supported in `R : Finset (Fin 4)`; genuine isotony (`PatchQFTBridge`). |
| `Hqiv.QM.patchChartPoint` / `Hqiv.QM.minkowski_spacelike_patchChartPoint_spatial` / `Hqiv.QM.regions_disjoint_spatial_spacelike` | Minkowski corner embedding; spatial pairs spacelike; disjoint spatial regions ⇒ spacelike pairs (`PatchQFTBridge`). |
| `Hqiv.QM.patchEventChartFour` / `Hqiv.QM.spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions` | `EventChart` on ℕ (`n<4` ↔ corners); disjoint spatial regions ⇒ `spacelikeRelationMinkowski` on labels (`PatchQFTBridge`). |
| `Hqiv.QM.microcausality_zero_comm_patchEventChartFour` | `MicrocausalityStatement commutatorKernelZero (spacelikeRelationMinkowski patchEventChartFour)`. |
| `Hqiv.QM.patchAlgebra_opComm_zero_and_events_spacelike_in_patchChart` | `patchAlgebraAt` commutator `0` ∧ labels spacelike in `patchEventChartFour` when regions satisfy the spatial disjoint hypotheses. |
| `Hqiv.QM.HorizonContinuumAxioms` (in `HorizonLimitedRenormLocality.lean`) | **Record of Props** — explicit slots for continuum closure (not a single Lean `axiom`). Concrete operator content feeding the narrative: `PatchIntervalMaxSmeared` (smeared interval–max Pauli) + `IntervalMaxOperatorCommutator`. |
| `Hqiv.QM.horizon_continuum_closure_core_HQIV` | Closure theorem when core axioms + proved spin-stat + finite CPTP slot align (see file). Related: `Hqiv.QM.horizon_qm_qft_full_package_core_HQIV`, `Hqiv.QM.horizon_continuum_closure_of_axioms`. |
| `Hqiv.QM.horizonContinuumAxiomsMinimal_ratioWitness_all_slots` | Conjunction of the five proved fields for `horizonContinuumAxiomsMinimal_ratioWitness`. |
| `Hqiv.QM.minkowskiIntervalSq` / `Hqiv.QM.spacelikeRelationMinkowski` / `Hqiv.QM.minkowski_spacelike_of_same_time` | Flat $(+,{-},{-},{-})$ interval and chart-pulled-back spacelike relation; same-time spatial separation ⇒ spacelike. |
| `Hqiv.QM.microcausality_in_domain_minkowski_scaffold_holds` | ∀ charts, `MicrocausalityStatement commutatorKernelZero (spacelikeRelationMinkowski chart)` (zero kernel; Minkowski predicate). |
| `Hqiv.QM.commutatorKernelIntervalMax_exists_ne_zero` / `Hqiv.QM.microcausality_intervalMax_scaffold_and_surrogate_nonzero` | Some chart has **nonzero** interval-max surrogate; combined with interval-max microcausality on all charts (`ContinuumManyBodyQFTScaffold`). |
| `Hqiv.QM.commutatorKernelIntervalMax` / `Hqiv.QM.microcausality_in_domain_minkowski_interval_scaffold_holds` | `max 0 η` commutator surrogate; microcausal w.r.t. η-spacelike; see `commutatorKernelIntervalMax_nontrivial`. |
| `Hqiv.QM.clusterCorrelationDirectionalMonogamyRedshift` / `cluster_decomposition_directional_monogamy_redshift_holds` / `clusterCorrelationDirectionalMonogamyRedshift_nonzero_at_zero` | Forward-channel cluster kernel: monogamy budget `coherenceProxy` plus extra shell redshift `1/phi_of_shell`; nearest-neighbor channel tends to `0` but is not identically zero (`ContinuumManyBodyQFTScaffold`). |
| `Hqiv.QM.photonGeodesicTransportN` / `photonGeodesicTransportN_eq_exp_neg_div` / `photonGeodesicTransportN_tendsto_zero` | Photon transport term from the finite measurement ledger: `redshiftedEnergyN 1 (birefringenceRedshiftN ((n:ℝ)+1) κ)` is exactly exponential attenuation and tends to `0` for positive `κ` (`ContinuumManyBodyQFTScaffold`). |
| `Hqiv.QM.photonGeodesicTransportFromScale` / `photonGeodesicTransportFromScale_tendsto_zero` | General transport family: any HQIV scale `s n → ∞` can drive the photon/birefringence ledger and yields vanishing transport (`ContinuumManyBodyQFTScaffold`). |
| `Hqiv.QM.photonModeBudgetScaleN` / `photonModeBudgetScaleN_tendsto_atTop` / `photonModeBudgetTransportN` | Cumulative photon mode budget scale from `available_modes`; theorem-backed as an `atTop` transport scale (`ContinuumManyBodyQFTScaffold`). |
| `Hqiv.QM.clusterCorrelationDirectionalMonogamyPhotonGeodesic` / `cluster_decomposition_directional_monogamy_photonGeodesic_holds` / `clusterCorrelationDirectionalMonogamyPhotonGeodesic_nonzero_at_zero` | Stronger forward-channel cluster kernel: monogamy budget transported by the photon geodesic/birefringence ledger rather than only by inverse-`phi` shell damping (`ContinuumManyBodyQFTScaffold`). |
| `Hqiv.QM.clusterCorrelationDirectionalMonogamyPhotonBudget` / `cluster_decomposition_directional_monogamy_photonBudget_holds` / `clusterCorrelationDirectionalMonogamyPhotonBudget_nonzero_at_zero` | Forward-channel cluster kernel using the cumulative photon mode budget as transport scale, giving faster exponential attenuation than shell-step geodesic transport (`ContinuumManyBodyQFTScaffold`). |
| `Hqiv.QM.commutatorKernelIntervalMax_patchEventChartFour_0_4_eq_one` / `…_ne_zero` | On `patchEventChartFour`, labels `0` and `4` give **η = 1** ⇒ surrogate **nonzero** (timelike domain); `microcausality_patchEventChartFour_intervalMax_and_nonzero` (`PatchQFTBridge`). |
| `Hqiv.QM.continuum_many_body_closure_minkowskiMicroWitness` | Same closure as `continuum_many_body_closure_ratioWitness_trivialRest` but microcausality slot uses the Minkowski scaffold. |
| `Hqiv.QM.horizonContinuumAxiomsMinimal_minkowskiIntervalMonogamyClusterWitness` / `continuum_many_body_closure_minkowskiIntervalMonogamyClusterWitness` | Minimal continuum closure witness with interval-max microcausality **and** the directional monogamy/redshift cluster kernel, replacing the zero cluster surrogate (`HorizonLimitedRenormLocality`). |
| `Hqiv.QM.horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonGeodesicClusterWitness` / `continuum_many_body_closure_minkowskiIntervalPhotonGeodesicClusterWitness` | Minimal continuum closure witness with interval-max microcausality and photon-geodesic monogamy transport (`κ = 1` concrete witness) (`HorizonLimitedRenormLocality`). |
| `Hqiv.QM.horizonContinuumAxiomsMinimal_minkowskiIntervalPhotonBudgetClusterWitness` / `continuum_many_body_closure_minkowskiIntervalPhotonBudgetClusterWitness` | Minimal continuum closure witness with interval-max microcausality and cumulative photon-budget monogamy transport (`κ = 1` concrete witness) (`HorizonLimitedRenormLocality`). |
| `Hqiv.QM.continuum_many_body_closure_minkowskiIntervalWitness` | Same closure with interval-max surrogate (nonzero on some timelike pairs). |
| `Hqiv.QM.microcausality_zero_comm_allSpacelike_holds` / `Hqiv.QM.scattering_consistency_unit_channel_holds` | Degenerate “all spacelike” schema + unit scattering channel in `[0,1]` (`ContinuumManyBodyQFTScaffold`). |

## Light cone ↔ Maxwell ↔ QM bridge (`Hqiv.Physics.LightConeMaxwellQFTBridge`)
| `Hqiv.Physics.timeAngleBudgetScaleN` / `timeAngleBudgetScaleN_eq_accessibleModeBudgetUpToShell` / `timeAngleBudgetScaleN_tendsto_atTop` | Doubled observer-time budget scale: `accessibleModeBudgetUpToTimeAngle (4(n+1)) = accessibleModeBudgetUpToShell (2n+1)`, giving a theorem-backed cumulative time-angle transport scale. |
| `Hqiv.Physics.timeAngleBudgetTransportN` / `clusterCorrelationDirectionalMonogamyTimeAngleBudget` / `cluster_decomposition_directional_monogamy_timeAngleBudget_holds` | Forward cluster kernel using the doubled observer-time budget as the photon transport scale; same monogamy budget, stronger cumulative time-angle attenuation. |
| `Hqiv.Physics.timeAngleBudgetScale_feeds_HQVM_GR` / `timeAngleBudgetTransport_and_HQVM_GR` | Same doubled observer-time budget is also a valid homogeneous HQVM gravity input: lapse law, `H_of_phi`, `G_eff`, `S_HQVM_grav = 0 ↔ HQVM_Friedmann_eq`, and the explicit `(13/5)` Friedmann form all hold at that scale. |
| `Hqiv.Physics.LightConeFunctionalBridge.timeAngleBudgetWitnessBridge` / `lightConeMaxwellQFT_continuumClosure_timeAngleBudgetWitness` / `lightConeMaxwellQFT_fullPackage_timeAngleBudgetWitness` | Physics-side bridge witness and full package using interval-max microcausality plus the doubled time-angle budget transport law. |

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.accessibleModeBudgetUpToShell` | ℝ mode budget on shells `0…M` (= `Hqiv.available_modes M`); finite-patch alias for grepability. |
| `Hqiv.Physics.accessibleModeBudgetUpToShell_eq_sum_new_modes` | Patch budget = cumulative `∑_{i≤M} new_modes i` (`SphericalHarmonicsBridge.sum_new_modes_eq_available_modes`). |
| `Hqiv.Physics.accessiblePatch_modeBudget_div_harmonic_tends_four` | `accessibleModeBudgetUpToShell M / sphericalHarmonicCumulativeCount M → 4` as `M → ∞`. |
| `Hqiv.Physics.PhotonHorizonModeLimitValue` / `Hqiv.Physics.PhotonHorizonModeLimit` | **Definite** asymptotic value `4` (= octonion factor); alias for `ShellToHarmonicLimit` (`photonHorizonModeLimit_holds`). |
| `Hqiv.Physics.photonHorizonModeLimit_tendsto` | `Tendsto` of the mode ratio to `𝓝 PhotonHorizonModeLimitValue` (same as harmonic bridge). |
| `Hqiv.Physics.accessiblePatch_shellToHarmonicLimit` | Same `Prop` as `shell_to_harmonic_limit_holds` — named for finite-patch narrative. |
| `Hqiv.Physics.realShellPlusOneFromTimeAngle` / `realShellPlusOneFromTimeAngle_timeAngle_phi_shell_unit` | Continuous coordinate `θ/2`; at `θ = timeAngle (phi_of_shell m) 1` equals `m+1` (`AuxiliaryField`, `HQVMetric`). |
| `Hqiv.Physics.shellIndexFromTimeAngle` / `shellIndexFromTimeAngle_timeAngle_phi_shell` | `⌊max(0,(m+1)t-1)⌋₊` from `θ = timeAngle (phi_of_shell m) t`. |
| `Hqiv.Physics.accessibleModeBudgetUpToTimeAngle` / `accessibleModeBudgetUpToPhiTime` | Mode budget from time-angle–derived shell index; `accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit` at `t=1`. |
| `Hqiv.Physics.lightCone_discreteModes_shellToHarmonicLimit` | Same as `shell_to_harmonic_limit_holds` — discrete `available_modes` ladder vs harmonic count. |
| `Hqiv.Physics.lightCone_emergent_coordsField_constPhi_eq_general` | Constant φ on chart ⇒ emergent O–Maxwell coords RHS = `emergentMaxwellInhomogeneous_O_general` (`ContinuumOmaxwellClosure`). |
| `Hqiv.Physics.lightCone_ratioWitnessBridge_shellProof_eq_discreteLimit` | Identifies `ratioWitnessBridge.shellProof` with `lightCone_discreteModes_shellToHarmonicLimit`. |

## Quantum chemistry (`Hqiv.QuantumChemistry.*`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.QuantumChemistry.latticeFullModeEnergy_closed_form` | First-principles closed form for site energy: `latticeFullModeEnergy m = 4*(m+2)*(m+1)^2` (from `available_modes` + `phi_of_shell`). |
| `Hqiv.QuantumChemistry.siteModeBudgetTraceFromPhiTime_unit_eq_siteModeBudgetTrace` | Unit-time `phi·t` specialization matches shell-index budget sum over sites. |
| `Hqiv.QuantumChemistry.h2SiteEnergyTrace_same_shell_closed_form` | Equal-shell H₂ site trace: `8*(m+2)*(m+1)^2`. |
| `Hqiv.QuantumChemistry.referenceM_eq_four` | Proton anchor shell identity `referenceM = 4`. |
| `Hqiv.QuantumChemistry.h2SiteEnergyTrace_referenceM_numeric` | H₂ equal-shell trace at proton anchor (`m=4`) evaluates to `1200` in this site-energy normalization. |
| `Hqiv.QuantumChemistry.h2Output_referenceM_numeric` | H₂ site-energy output at proton anchor (`referenceM`) evaluates to `1200`. |
| `Hqiv.QuantumChemistry.h2ModeBudgetOutput_eq_sum_accessibleShellBudgets` | H₂ QFT/QM budget output equals sum of two shell-wise `accessibleModeBudgetUpToShell` terms. |
| `Hqiv.QuantumChemistry.h2ModeBudgetOutput_fromPhiTime_unit` | H₂ QFT/QM budget output matches the unit-time `phi·t` lifted budget (`siteModeBudgetTraceFromPhiTime ... 1`). |
| `Hqiv.QuantumChemistry.h2oOutput_eq_sum_siteEnergies` | H₂O site-energy output decomposes into the sum of three per-site first-principles energies. |
| `Hqiv.QuantumChemistry.moleculeModeBudgetOutput_fromPhiTime_unit` | General `n`-site mode-budget output agrees with unit-time `phi·t` lifted budget. |
| `Hqiv.QuantumChemistry.symm_plus_antisymm_eq_original` | Any two-electron spatial wavefunction decomposes exactly into symmetric + antisymmetric exchange parts. |
| `Hqiv.QuantumChemistry.heliumSpatialAnsatz_exchange_invariant` | Shell-based two-electron helium spatial ansatz is exchange-symmetric. |
| `Hqiv.QuantumChemistry.spinSinglet_antisymmetric` / `heliumPauliCompatible_holds` | Spin-singlet scaffold is exchange-antisymmetric; combined with symmetric spatial factor yields Pauli-compatible helium scaffold. |
| `Hqiv.QuantumChemistry.excitationSiteEnergyDelta_eq_sum` | For any atom and any excitation profile, site-energy excitation delta is an exact finite sum of per-electron shell-step differences. |
| `Hqiv.QuantumChemistry.excitationModeBudgetDelta_eq_sum` | For any atom and any excitation profile, QFT/QM mode-budget excitation delta is an exact finite sum of per-electron shell-step differences. |
| `Hqiv.QuantumChemistry.atomModeBudgetOutputFromPhiTime_unit_eq` | For any atom spec, unit-time lifted `phi·t` budget output equals direct shell-index budget output. |
| `Hqiv.QuantumChemistry.atomProductWavefunction` / `atomProductWavefunctionExcited` | Generic many-electron product-wavefunction scaffold from shell-resolved `hydrogenGroundStateOfShell` (ground and excited shell maps). |
| `Hqiv.QuantumChemistry.atomProductWavefunctionExcited_pointwise` | Pointwise excited-state product formula: shell increments `δ` feed directly into orbital shell labels. |
| `Hqiv.QuantumChemistry.slaterDetTwo_exchange_sign` | Generic two-orbital Slater determinant scaffold is exchange-antisymmetric. |
| `Hqiv.QuantumChemistry.atomActivePairSlater_exchange_sign` | For any atom and any active pair indices, Slater-pair scaffold is exchange-antisymmetric. |
| `Hqiv.QuantumChemistry.atomActivePairSlaterExcited_exchange_sign` | Excited-state active-pair Slater scaffold remains exchange-antisymmetric under shell-profile excitation. |
| `Hqiv.QuantumChemistry.ReactionGate` | Generic stoichiometric gate: `n` element types, `k` species slots, composition matrix `Fin k → Fin n → ℕ`, consume/produce vectors, and geometry/temperature/heat metadata. |
| `Hqiv.QuantumChemistry.stoichiometricElementResidual` | Per-element balance check: `∑_i (p_i - c_i) * a_{i,e}` in `ℤ` (zero ⟺ mass-balanced for that element). |
| `Hqiv.QuantumChemistry.ReactionGate.apply_preserves_totalElementAtoms` | If the gate is element-balanced and reactant counts suffice, one application preserves all per-element atom totals. |
| `Hqiv.QuantumChemistry.waterSynthesisGate` | `ReactionGate 2 3` instance for water (`2H + O → H₂O`) with standard composition matrix and geometry/temperature/heat metadata. |
| `Hqiv.QuantumChemistry.waterSynthesisGate_balanced` | Water gate is element-balanced on the two-element (H, O) dictionary. |
| `Hqiv.QuantumChemistry.applyWaterGate` | Species-indexed state update matching `waterSynthesisGate.apply` on the `Fin 3` register (`registerOfSpeciesState` bridge). |
| `Hqiv.QuantumChemistry.waterSynthesisGate_apply_preserves_H` / `..._preserves_O` | `applyWaterGate` preserves total H and O atom counts when the register can fire. |

*For a full list of `theorem`/`lemma` lines, agents can run `rg '^theorem |^lemma ' Hqiv/` — this file is intentionally curated, not exhaustive.*
