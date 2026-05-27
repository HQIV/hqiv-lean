# Assumptions, defs, and hidden handwaving

This is an **honest inventory** of what the formal development rests on besides “proofs in Lean.” It is aimed at agents who must not confuse marketing language in comments with Mathlib’s logical foundations.

**Patch ontology (agent contract):** [PATCH_ONTOLOGY.md](./PATCH_ONTOLOGY.md) — accessible patch as observable universe, continuum as readout not foundation, patch-closed “completeness,” simulation aliasing. Read before conflating `main.tex` “complete GUT” language with proved continuum QFT.

## 1. Conceptual “axioms” of HQIV (paper-level)

These are **not** necessarily `axiom` declarations in Lean. They are the **narrative foundations** repeated in module docs:

- **Discrete null lattice / counting:** New modes per shell follow stars-and-bars combinatorics on the 3D null lattice, multiplied by the octonion factor (encoded as defs and theorems in `OctonionicLightCone`).
- **Informational-energy / monogamy (metric sector):** ADM lapse `N = 1 + Φ + φ t` and the HQVM line element story (`HQVMetric` and related files). `φ` is tied to the auxiliary-field ladder (`AuxiliaryField`), not introduced as a free continuous parameter in the comments’ intent.
- **Algebra-first Maxwell ladder:** the current O-Maxwell stack is documented and formalized as an **algebra-first** seed (`OMaxwellAlgebraSeed`) built from `G₂ ∪ {Δ}`, the extracted H-block / EM block of the existing `so(8)` package, and the rapidity/tipping slot. The shell-temperature ladder `phi_of_T` is now a **secondary projection/readout layer**, not the primary definition of the Maxwell correction.
- **Quaternionic reduction is a sanity limit, not the canonical curvature carrier:** `ModifiedMaxwell` proves the octonionic `O` equation reduces to classic Maxwell in the quaternionic `H` block on the flat constant-`φ` limit, but the canonical curvature imprint is still fixed in `OctonionicLightCone` by the octonionic lift as `6^7 * sqrt(3)`, not by a quaternionic `6^3 * sqrt(3)` substitute. The new comparison lemmas make this precise: the quaternionic candidate produces a shell imprint smaller by the rigid factor `1296` on the same shell shape, so agents should not quietly swap “classical Maxwell in H” for the full HQIV curvature normalization.
- **Standing-wave structure is more central than self-clock:** given the limited structure available on a horizon / holographic medium, agents may treat **standing-wave encoding of quantum-number-like data** as a serious HQIV design direction. But modules such as `SurfaceWaveSelfClock` and `ComptonHorizonPhase` still package only **one possible configuration/state language** on top of that standing-wave picture. So the standing-wave layer is more earned than the specific self-clock story, while the self-clock itself remains provisional.
- **Exact shell occupancy may be too rigid for standing-wave modes:** for charged leptons especially, agents should allow that a mode may occupy a **shell band / support region** or a potential difference rather than one exact shell index. Exact shell labels may still be useful as peaks, anchors, or representative indices, but they should not automatically be treated as the whole physical support of the mode.
- **No physically fundamental sub-Planck continuum:** when files use calculus, derivatives, charts, or metric coefficients, agents should read these as **IR / observer-readout structures built over the discrete null-lattice shell ladder**, not as a commitment that HQIV’s primary ontology is a smooth manifold below the lattice cutoff. The lattice is UV-complete bookkeeping; the continuum is an effective language for large-scale or observer-side normalization.
- **Experimental precision and HQIV witness precision are different budgets:** when a mass candidate lands close to a PDG central value but not within the laboratory error bars, agents should not describe that as “inside experimental uncertainty.” The better HQIV reading is that the **measurement** uncertainty remains small while the current **theory/readout** uncertainty is larger, because lapse/readout normalization, shell/support selection, and other observer-side layers are not yet fully collapsed to a unique final observable prediction.
- **Single active scale witness (2026 discipline):** at most **one** dimensionful witness may pin a given Python export or coupling solve. Default: **`proton_lockin`** — `derivedProtonMass` at `referenceM` sets the mass/unit chart; CODATA `1/α`, CMB horizons, and PDG centrals are **predictions or comparison layers**, not simultaneous anchors. Legacy **`codata_alpha`** mode keeps the continuous Gauss→EW brace as the sole EM scale row. See `Hqiv.Physics.ScaleWitness`, `data/hqiv_witnesses.json`, `scripts/hqiv_scale_witness.py`.

Agents should treat **Mathlib** as the substrate for analysis, linear algebra, and `ℝ`.

## 1b. Canonical `α` and `γ` (sole HQIV identifiers; companion + Brodie provenance)

In this repository, **there is only one** curvature-imprint exponent and **only one** monogamy / horizon-overlap coefficient in the HQIV sense:

| Lean name | Role | Proved value |
|-----------|------|----------------|
| `Hqiv.alpha` (`OctonionicLightCone`) | Curvature imprint / $G_{\mathrm{eff}}$ ladder exponent | `3/5` (`alpha_eq_3_5`) |
| `Hqiv.gamma_HQIV` (`HQVMetric`) | Monogamy split; **defined** as `1 - alpha` | `2/5` (`gamma_eq_2_5`) |

No alternate “HQIV α” or “HQIV γ” definitions appear elsewhere: downstream physics (`SM_GR_Unification`, `AuxiliaryField`, CMB hooks, **etc.**) refers to these symbols only.

**Uniqueness is forced in Lean:** `latticeAlphaRatio_eq_alpha` identifies the shell-wise imprint ratio with `alpha` for every `n`; `alpha_eq_3_5` evaluates `alpha = 3/5`; `gamma_HQIV := 1 - alpha` and `gamma_eq_2_5` give `2/5` with `alpha_add_gamma = 1`. These are bundled as `alpha_gamma_forced_pair` in `Hqiv/Geometry/AlphaGammaForcedByLattice.lean`. The **thermodynamic / geometric narrative** explaining why this discrete structure is the HQIV vacuum lives in the **companion HQIV manuscript** and **Brodie (2026)** (`ettinger2026hqiv`, `brodie2026`); Lean **discharges** the rational identities and the complement split, not a menu of tunable parameters.

## 2. Lean `axiom` keyword

A search for user-declared `axiom` statements in `Hqiv/` shows **no free-standing HQIV physics axioms** of the kind “we assume this unprovable proposition.” Discussion of “axiom” in the codebase is overwhelmingly **documentation** (e.g. “single axiom”, “informational-energy axiom”) attached to **definitions** or **named Prop bundles**.

**Explicit `Prop` bundles** (e.g. `HorizonContinuumAxioms`, `HorizonContinuumAxiomsCore` in `HorizonLimitedRenormLocality.lean`) are **assumption records**: they make the continuum-QFT bridge requirements **visible**. Some slots are discharged by other modules (e.g. spin–statistics via `SpinStatistics`). **Scattering-consistency** is not only schematic: `ContinuumManyBodyQFTScaffold` gives proved `[0,1]` channels (including zero / unit channels and an **associator–vorticity** channel from `OctonionBasics`), and `Hqiv.QM.continuum_scattering_associatorVorticity_holds` packages one of these in `HorizonLimitedRenormLocality`. **Microcausality** has **Minkowski** upgrades: `spacelikeRelationMinkowski` with either the zero kernel (`microcausality_in_domain_minkowski_scaffold`) or the **interval-max** surrogate `commutatorKernelIntervalMax` = `max 0 η` (`microcausality_in_domain_minkowski_interval_scaffold` — vanishes on spacelike pairs, positive on some timelike pairs; `commutatorKernelIntervalMax_nontrivial`). Operator-level **scaffolds** exist (`opCommutator`, `fieldOpFromChart`, Pauli **toy**), and the spin side now reaches this layer through `SpinStatisticsOperatorBridge`: HQIV mode pairs are sent to concrete smeared interval-max operators / Pauli commutators that vanish on spacelike patch support. The cluster slot is no longer only the identically-zero witness. There is now a **small family** of theorem-backed forward kernels: `clusterCorrelationDirectionalMonogamyRedshift` (monogamy plus inverse-`phi` shell damping), `clusterCorrelationDirectionalMonogamyPhotonGeodesic` (monogamy transported through the finite photon measurement ledger `redshiftedEnergyN 1 (birefringenceRedshiftN ((n:ℝ)+1) κ) = exp (-(n+1)/κ)`), `clusterCorrelationDirectionalMonogamyPhotonBudget` (same transport law but driven by the cumulative photon mode budget `available_modes n`), and the physics-side `clusterCorrelationDirectionalMonogamyTimeAngleBudget` (same transport law but driven by the doubled observer-time budget `accessibleModeBudgetUpToTimeAngle (4(n+1)) = accessibleModeBudgetUpToShell (2n+1)`). The concrete closure witnesses `continuum_many_body_closure_minkowskiIntervalMonogamyClusterWitness`, `continuum_many_body_closure_minkowskiIntervalPhotonGeodesicClusterWitness`, `continuum_many_body_closure_minkowskiIntervalPhotonBudgetClusterWitness`, and `lightConeMaxwellQFT_continuumClosure_timeAngleBudgetWitness` package these nontrivial cluster laws. **Exact CCR `[A,B]=I` as literal fixed-size matrices** is impossible (`not_exists_matrix_CCR_one`—trace obstruction); a **minimal local net** (`diagonalSmearedNet`) is formalized with trivial isotony.  HQIV does **not** aim to import full textbook infinite-dimensional QFT as a prerequisite: physics is phrased in **finite** accessible regions inside the light cone, with **limits** as cutoff / horizon resources grow (e.g. shell→harmonic).  Stronger patchwise nets, effective brackets, and continuum limits remain to be formalized; global `L²` representations are optional background, not a stated goal of this repo.  A named **finite-patch** hook is `Hqiv.Physics.accessibleModeBudgetUpToShell` (= cumulative mode budget on shells `0…M`, tied to `sum_new_modes`) and the limit lemmas `accessiblePatch_shellToHarmonicLimit` / `accessiblePatch_modeBudget_div_harmonic_tends_four` in `LightConeMaxwellQFTBridge`.  **Time ↔ shell** on the same ladder uses `timeAngle` with `phi_of_shell` (`shellIndexFromTimeAngle`, `accessibleModeBudgetUpToPhiTime`, unit-time match `accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit`), and the new `timeAngleBudgetScaleN` makes a `phi`-free doubled observer-time version explicit.  **Event chart:** `Hqiv.QM.patchEventChartFour` ties `EventLabel = ℕ` to the same corners as `patchChartPoint` for `n < 4`; `spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions` links disjoint spatial **Fin 4** regions to η-spacelike **ℕ** pairs (with `microcausality_zero_comm_patchEventChartFour` for the zero commutator surrogate).  **Definite horizon / photon refinement limit:** `Hqiv.Physics.PhotonHorizonModeLimit` / `PhotonHorizonModeLimitValue` (`4`) and `photonHorizonModeLimit_tendsto` — EM null-ladder vs cumulative `S²` harmonics; curvature–horizon growth is separate (`omega_k_partial_tends_to_atTop` in `OctonionicLightCone`).  **Interval-max commutator surrogate** `max 0 η` is **not** globally zero: `commutatorKernelIntervalMax_exists_ne_zero`, `microcausality_intervalMax_scaffold_and_surrogate_nonzero`; on the patch chart, `commutatorKernelIntervalMax_patchEventChartFour_0_4_ne_zero` (labels `0` vs parked `4`).

## 3. Mathlib (and dependencies)

- **Every proof** ultimately rests on **Mathlib’s** axioms for classical mathematics (reals, sets, linear algebra, etc.). This is standard; no attempt is made here to re-derive foundations.
- **Trust boundary:** If Mathlib is trusted, the HQIV proofs are “relative to Mathlib + the items below.”

## 4. Script-generated and numeric data in Lean

- **`GeneratorsLieClosureData0` … `GeneratorsLieClosureData27` and related files:** Large **precomputed** coefficient data (from Python scripts in `scripts/`, per `README.md`) to keep the SO(8) Lie closure proof tractable in Lean. This is **not** magic: it is **imported data** baked into lemmas. Agents should treat it as “verified external input” unless they re-run the scripts and regenerate.
- **Strong-color SU(3) certificate stack (optional `HQIVStrongColorSu3Certificate`):** `StrongColorSu3fStructureSimp` and `StrongColorSu3LieChartLaw` are **generated Lean** from `scripts/gen_strong_color_su3_f_simp.py` and `scripts/gen_strong_color_su3_lie_chart_law.py`. The Lie-chart file proves the global `su(3)` bracket identity on the abstract `3×3` chart by **64 explicit matrix cases** (not a single abstract Lie-algebra tactic). Trust boundary is “regen scripts + `lake build` agree”; default `HQIVLEAN` does not import this cone.
- **`so8Generator` matrices:** Originate from the same pipeline as `matrices.py` / project scripts (see repo docs).
- **Spinor monomial Gram certificate:** `CliffordCl06SixSpinorMonomialMatrixData.lean` declares the Frobenius divisibility by `8` and the mod-`101` determinant certificate as axioms (`eight_dvd_spinorMonomialGramFrobSum`, `spinorMonomialGramColumnsZMod101_det`). The intended verification scripts are `scripts/verify_spinor_frob_sum_div8.py` and `scripts/spinor_monomial_gram_det_mod101.py`. Treat downstream LI / mat-lift theorems as relative to this trusted finite computation unless the heavy cert is rebuilt.

## 5. `sorry` (known gaps)

| Location | What is left |
|----------|----------------|
| `Hqiv/Algebra/SO8ClosureAbstract.lean` | **Linear-span obstruction (still the key warning):** `Submodule.span ℝ (G₂ ∪ {Δ})` has `finrank ≤ 15` (`finrank_span_G2_union_Delta_le_15`), so it **cannot** equal the 28-dimensional `span(so8Generator)` — see `exists_so8Generator_not_mem_span_G2_union_Delta`. Containment `span_G2_union_Delta_le_span_so8Generator` is proved. **Do not** confuse this with Lie closure (see below). |
| `Hqiv/Algebra/G2DeltaGeneratedLie.lean` | **Lie closure (positive result):** `g2DeltaGeneratedLie_eq_so8LieSubalgebra` proves the Lie subalgebra **generated** by `G₂ ∪ {Δ}` (`LieSubalgebra.lieSpan ℝ …`) equals the standard Euclidean `so8LieSubalgebra` (dimension `28`), with `so8Generator_mem_g2DeltaGeneratedLie` bridging to the packaged `so8Generator` basis. This is the formal sense in which “G₂ + Δ closes to 𝔰𝔬(8)” — brackets, not bare linear span of fifteen matrices. |
| Root `tmp_*.lean` (if present) | Scratch files — **gitignored** (`.gitignore`); local only, not part of the library story. A root `tmp_im_test.lean` (or similar) may contain `sorry`; exclude from release claims. |

**Do not** claim “zero sorry in the entire repo” without running `rg 'sorry' --glob '*.lean'` — the README’s “100% proved” claim targets the **intended release stack**; verify against the actual `lake` target you build. In `Hqiv/`, occurrences of the word `sorry` inside **comments** (e.g. explaining why `#eval` on `ℝ` is avoided) are not proof gaps.

## 6. Numeric literals and `rfl` proofs

Many “physical outputs” (e.g. `1/α_EM(M_Z) = 127.9`, Higgs mass ratio) are **fixed by definition** in Lean and then proved by `rfl` or `norm_num`. That means:

- They are **exactly as trustworthy as the numeric encoding** and the **paper alignment** they are meant to match.
- They are **not** independent predictions produced by a separate numeric solver inside Lean unless a separate proof says so.

## 6b. Millennium Prize formalizations (lean-dojo)

- Claims that **resolve** or **materially advance** a Clay Millennium problem in Lean must be **compatible with** the statements in [**lean-dojo/LeanMillenniumPrizeProblems**](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) (Lean 4 formalization of the seven problems). See [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md).
- This repository’s HQIV bridges (`lambdaHQIV`, lattice zeta, fluid hypotheses, …) are **probe-level** unless a theorem explicitly rewrites them to Mathlib or Lean Dojo definitions.

## 7. Conventions (not secret, but easy to misread)

- **`referenceM`, `qcdShell`, `latticeStepCount` (substrate pin):** In Lean these are plain `Nat`
  definitions (`qcdShell := 1`, `latticeStepCount := 3`, hence `referenceM = 4`). They sit **below**
  the proved `α`/`γ` identities and the `T_lockin` / curvature-imprint **formulas** in the dependency
  stack: a large derived sector unfolds **once** a shell index is fixed, but **this file does not
  derive those three naturals from a smaller axiom block inside Mathlib.** Treat them as the explicit
  place the discrete shell program is pinned—aligned with the paper’s QCD + lock-in narrative—not as
  constants forced by stars-and-bars alone. Changing them changes **which shell** is “reference,” not
  the logical validity of downstream proofs **conditional** on the new indices.
- **Natural units / Planck reference:** In HQIV’s Lean mass bridges, **Planck energy (or `T_Pl`) is either the unit `1` or trivial.** Setting it to `0` collapses the dimensionful sector; any other positive overall mass scale is just a change of units relative to that `1`, not an independent “Planck witness.” Charged-lepton code still names `m_tau_Pl` for τ in **`E_Pl = 1`** normalization (see `ChargedLeptonResonance`). Likewise `G₀`, `H₀` are often `1` as stated in module docs.

## 7c. Boundary-lock analogy (`lambdaHQIV`, not classical `Λ`)

- The repository now carries an **HQIV analogue** scaffold in `DivisionAlgebraZetaScaffold`:
  `TempLadderBoundaryData` / `TempLadderForcesLambdaHQIVZero` with explicit consequence lemmas.
- This is intentionally **not** the classical de Bruijn–Newman constant: any statement of
  `lambdaHQIV = 0` is conditional on explicit HQIV hypothesis fields (`conservedRedistribution`,
  `regularizedBoundary`) and must not be reported as a theorem about classical RH/`Λ`.

## 7d. Plasma–fluid closure (`PlasmaFluidClosureAssumptions`, not kinetic theory)

- `Hqiv.Physics.PlasmaFluidClosureAssumptions` bundles explicit **Props**: scalar viscosities add
  (`ν_total = ν_mol + ν_eddy`), the eddy piece matches `hqivEddyViscosity`, and `C ∈ [0,1]`.
- Satisfying the bundle is **bookkeeping**, not a derivation from Vlasov–Maxwell, Braginskii
  transport, or O-Maxwell currents. The Python mirror `PlasmaFluidClosureHypothesis.holds()` is the
  same check for numerics.
- `CoefficientsTowardClassicalNS` is a separate **coefficient-level** slot toward classical NS form;
  it does **not** assert global well-posedness for 3D Navier–Stokes.
- `HQIVFirstPrinciplesNSBridge` is a **conditional first-principles bridge**: O-Maxwell action/EL
  chart data, F2 chart identification, F3 scalar viscosity closure, and an explicit
  continuum/coarse-graining momentum-balance hypothesis imply the HQIV DNS-shaped momentum equation.
  It still does **not** derive molecular viscosity, a closed kinetic stress tensor, existence,
  uniqueness, or regularity.
- The reduced bridge variants discharge more bookkeeping: `HQIVFirstPrinciplesMomentumData.canonical_chartHypothesis`
  makes F2 chart identification definitional; `HQIVCanonicalShellDebyeClosure.to_continuumBalanceClosure`
  constructs the F3 shell/Debye closure from canonical eddy/total-viscosity equalities; and
  `HQIVPlasmaAmplitudeCoherence.coherence_mem_unit` derives `C ∈ [0,1]` from
  `coherenceFromPlasmaAmp` when `κ ≥ 0`. The remaining fluid assumption is therefore the continuum
  stress/balance decomposition (`OMaxwellToFluidBalanceHypothesis`), not the HQIV closure bookkeeping.

## 7e. SAT / ATSP search certificates (`GeneralizedGeometricOracle`, not solver correctness)

- `DepartedDegeneracySearchCertificate` and `ReducedFrontierDegeneracyProfile` are explicit
  **certificate / profile records** for explored-search bounds: they package branching-budget,
  frontier, depth, and gap hypotheses so Lean can prove subfactorial or slack-reduced search bounds.
- These records certify properties of the **explored search space** (`recursiveCandidateBudget`,
  `topk * beam^depth`, `topk * (frontierArity - slack)^depth`), not correctness of a polynomial-time
  SAT or ATSP decision procedure.
- `slackFromGap` is a proved way to turn integer gap data into an admissible search slack; it is
  **not** a theorem that every positive gap is efficiently detectable from raw SAT geometry without
  the stated hypotheses.

## 7b. Lepton shells (canonical: lock-in + `ChargedLeptonResonance`)

- **`LeptonGenerationLockin`**: **structural** alignment with quarks — **τ at `referenceM`**
  (lock-in), **μ and e on strictly larger ℕ shells**, so **the electron sits on the highest shell
  index** among charged leptons in that module. **Thresholding** uses
  `chargedLeptonDetunedSurfaceOctaveRatio = 2`: a **single modeling choice** (detuned capacity doubling
  per generation), consistent with the Rindler/detuned-surface machinery but **not** proved from the
  combinatorial lattice count alone.
- **`ChargedLeptonResonance`**: geometric `resonance_k_*`, `m_tau_Pl` (τ mass in **`E_Pl = 1`**
  units—not a separate “Planck witness”), `resonanceProduct`, etc., on those same three shells
  (imported by `SM_GR_Unification`). **Dimensionful GeV** charged-lepton masses still anchor on
  `m_tau_from_resonance` (PDG central τ mass); lighter generations follow by **dividing** by the proved
  `resonance_k_*`. The lock-in candidate `m_tau_from_lockin_surface_candidate` (`= 16/9` in its
  normalization) is a **parallel witness**; the `≈` lemma vs `m_tau_from_resonance` is an alignment
  check, not a uniqueness theorem for the PDG numeral.
- **Archived only:** the old **τ = highest ℕ shell** Planck-volume book-keeping (`m_e < m_mu < m_tau`
  with τ at `274211`) is kept as `archive/abandoned/GenerationResonanceTauHighestShell.lean` and is
  **not** in the default lake targets.
- **Continuous shells:** nothing in the formalism *requires* shell labels to be integers; the
  repo’s **proved** surfaces use **ℕ** for `shellSurface` and detuning. A future layer could use
  `ℝ` labels with the same `(m+1)(m+2)` pattern evaluated on non-integer points — not done here.
- **Cumulative rapidity (dynamic Rindler δ):** `Hqiv.Physics.delta_auxiliary_phi_per_shell` and
  `rindlerDenWithDeltaRapidity` in `GlobalDetuning` add `β_cum * (φ·t)` on the same lattice time
  track as `timeAngle` — in-repo defs/theorems, not a `sorry`.

## 7f. Quark ladder and nucleon witness (`QuarkMetaResonance`)

- **Same machinery, explicit tables:** quark **ratios** use `geometricResonanceStep` /
  `detunedShellSurface` like charged leptons. The **ℕ** shell triples (`m_quark_up_*`, `m_quark_down_*`)
  and GeV anchors (`m_top_GeV`, `m_bottom_GeV`) are **named witnesses** in Lean—auditable and stable,
  but not proved unique from a shorter input list in this repo.
- **Nucleon / composite trace:** the multi-channel 8×8 witness is **explicit and documented**; treat it
  as an HQIV-shaped binding ansatz backed by theorems **given** those inputs, not as the only
  mathematically possible trace.
- **Spinor mass probe policy:** `scripts/spinor_mass_operator_reality_probe.py` defaults to HQIV-internal
  spectral/shell diagnostics. Any PDG-style quark/lepton mass table in that script is an opt-in
  external yardstick (`--comparison-mode external`), not a promoted mass-selection rule and not a
  substitute for constituent/network binding theorems.
- **Proton lock-in vs quark GeV anchors:** under **`proton_lockin`**, exported nucleon masses (`derivedProtonMass`, `derivedNeutronMass`, `derivedDeltaM`) are the **primary** mass witnesses in Python (`scripts/informational_energy_mass.py`, `scripts/hqiv_scale_witness.py`). The quark **ladder** still uses **`m_top_GeV`** and shell tables for color-composed ratios; that anchor is **sector-local** to the quark module and must not be treated as a second active scale witness in the same solve as proton lock-in. `protonAnchorMass_MeV = 938.272` in `QuarkMetaResonance` is a **legacy reference row** for lapse readout lemmas (`LapseMassReadout`), not an independent physics input when `derivedProtonMass` is already exported.

## 7g. Single-scale witness (`ScaleWitness`)

- **Lean enum:** `Hqiv.Physics.ScaleWitness` — `proton_lockin` (default), `codata_alpha`, `cmb_now`.
- **JSON bundle:** `data/hqiv_witnesses.json` (fields include `scale_witness_default`, `referenceM`, `derivedProtonMass_MeV`, boson masses, `CODATA_inv_alpha` as **comparison only** under default mode).
- **Python:** `scripts/hqiv_scale_witness.py` loads the bundle; `scripts/hqiv_coupling_linear_system.py --scale-witness` selects the active witness; `scripts/informational_energy_mass.py` defaults to `proton_lockin`.
- **Rule for agents:** never wire CODATA α **and** proton mass **and** a third cosmology anchor into the **same** solve/export without documenting which one is active and which are predictions.
- **Export caveat:** full Lean re-evaluation of noncomputable `derivedProtonMass` via `scripts/export_witnesses.lean` may fail to compile; metadata refresh uses `scripts/export_witnesses_metadata.lean`. Mass numerals in JSON are the current derived snapshot until a computable export path lands.

## 7h. Informational-energy mass row and Fano coupling

- **Informational energy (natural units):** `E_tot = m_rest + 1/Θ_local(ξ)` with `Θ_local(ξ) = T_Pl/ξ` (`InformationalEnergyMass.lean`). Not a new Mathlib `axiom`; packaged as defs + gauge lemmas.
- **Readout gauges:** bosons → `additiveLocalization` (full `E_tot`); hadrons → `multiplicativeLapse` / `hadronMassFromXi` (rest ÷ `HQVM_lapse`, localization in lapse increment). `gauge_transformation_localization_to_lapse` calibrates when gauges agree.
- **Default mass row (Lean + Python):** `c₀ + loc(ξ_G) = 2π·Ω_k(ξ_G)` (`informationalEnergyMassRow` in `ContinuousXiCoupling.lean`). Legacy row `holonomyRowRhs(0)·Ω_k` is `informationalEnergyMassRowLegacy` — regression only.
- **Three Ω_k charts (do not conflate):** brace/coupling @ ξ_G≈3.47 with ξ_lock=5 (~0.72); shallow ξ≈1.07 (~0.03); Ω_k^true / CMB horizons — comparison layers, not interchangeable with the brace mass row.
- **Coupling solve under `proton_lockin`:** normalize `c₀=1`; report braced `1/α` as prediction vs CODATA; mass row at ξ_lock = `referenceM+1`.

## 7i. Excited hadrons (calculator + MetaHorizonExcitedStates)

- **Lean module:** `Hqiv.Physics.MetaHorizonExcitedStates` — radial/orbital modes on the lock-in drum via `totalModeMass(n,ℓ)` and composite-trace binding at `referenceM+n+ℓ`.
- **Calculator rule:** ground mass from witness/coupling/informational-energy stack **without** excitation tag; then add ΔM from `scripts/hqiv_excited_states.py`:
  - `decuplet` → radial `n=1` (spin-3/2 excitation on same valence content),
  - `vector` → orbital `ℓ=1` on meson ground anchor.
- **Light Δ(1232) multiplet:** for `u,d`-only decuplet configs, spin ground is **proton lock-in** (isospin split ≪ radial excitation in PDG chart), not uuu constituent scaling.
- **Not legacy scaffold:** the old `constituent − E_bind·scale` meson/baryon heuristic is retired from the benchmark path; do not reintroduce ad hoc `0.38` meson binding factors as if they were part of informational energy.
- **Open theorem/export gaps:**
  1. Lean `totalModeMass` is noncomputable — export `derivedDeltaM_radial_1_MeV` (or full mode table) when a computable snapshot exists.
  2. Raw composite-trace binding **increases** with shell index → sign wrong for baryon excitation; fix in Lean or prove an inverted readout layer before dropping the surface-step operational ΔM.
  3. PDG comparison table `data/hadron_published_masses.json` must use **Δ(1232) ≈ 1232 MeV**, not 2452 MeV rows, for decuplet benchmark stats to be meaningful.
  4. Strange decuplet (Σ*, Ξ*, Ω*): ground should track **octet partner** at same valence, not proton + constituent scaling alone.

## 8. Imports = logical dependency (not “handwaving,” but easy to miss)

If module A imports module B, **all** definitions and axioms of B (and Mathlib transitive closure) are in force. The root `HQIVLEAN.lean` lists the **intended** high-level import graph; individual features may compile under smaller `lake` targets — see `lakefile.toml`.

## 9. When to update this file

Update **ASSUMPTIONS.md** when you:

- Add or remove a `sorry`
- Add new script-generated data files
- Introduce new explicit `Prop` assumption bundles for bridges
- Change numeric reference literals that are proved by `rfl`

Also refresh **[MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md)** status snapshot (and [THEOREMS.md](./THEOREMS.md) rows) when cross-thread lemmas land, so agents do not rely on stale “open vs done” lists. After a broad corpus audit, update **§11** (layer table + provable/build-better lists) in this file.

## 9b. Where to read “proved vs still open” (Millennium-adjacent thread)

| Question | Where |
|----------|--------|
| What geometry / zeta / script milestones are **done** vs **sought**? | [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) **Status snapshot** + **Proof priority** |
| Curated **Lean names** with short descriptions? | [THEOREMS.md](./THEOREMS.md) |
| Hodge **analogy** vs **proved HQIV-internal** wires vs **classical** gaps? | [HODGE_HQIV_NARRATIVE.md](./HODGE_HQIV_NARRATIVE.md) §§1–5 (§5 + **still open**) |
| Single narrative across RH / YM / NS / Hodge **probe** language? | [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md) |
| `sorry`s, data files, bridge `Prop`s? | This file §§4–5, 6b, 7c–7d |

## 10. What can be improved (vs what stays)

Rough priority for **actually reducing** handwaving or confusion:

| Item | Can we “take care of it”? | Notes |
|------|---------------------------|--------|
| **§5 — linear span vs Lie span** | **Obstruction + closure both clear.** | Linear span of `G₂ ∪ {Δ}` stays **≤15**-dimensional (`SO8ClosureAbstract`). **Lie** subalgebra generated by the same seed set is **`𝔰𝔬(8)`** (`g2DeltaGeneratedLie_eq_so8LieSubalgebra` in `G2DeltaGeneratedLie`). Optional: align `SO8ClosureAbstract` naming/comments with `G2DeltaGeneratedLie` so “closure” is not read as linear span. |
| **§5 — `tmp_*.lean` scratch files** | **Mostly done.** | Root `tmp_*.lean` is **gitignored**; delete local copies if you want `rg sorry` to skip them entirely. |
| **§4 — Lie-closure data files** | **Partially.** | Keep as data; add optional CI: re-run `scripts/print_*.py --write` and fail on `git diff`, or record a checksum in this doc. Reduces “silent drift,” not the need for precomputed coefficients. |
| **§2 — `HorizonContinuumAxioms*` records** | **Clarity + partial discharge.** | Shell→harmonic and several **finite-layer** witnesses (microcausality kernel, cluster triviality, **scattering channels** including associator/vorticity) are **proved** under the minimal ratio witness (`horizonContinuumAxiomsMinimal_ratioWitness_all_slots`, `continuum_scattering_associatorVorticity_holds`). Microcausality also has **Minkowski** variants (`continuum_many_body_closure_minkowskiMicroWitness`, `continuum_many_body_closure_minkowskiIntervalWitness`, `spacelikeRelationMinkowski`) — η-spacelike pairs; either a zero commutator surrogate or `max 0 η` (nontrivial on timelike pairs). Operator fields / patchwise nets beyond the diagonal scaffold remain future work.  The intended physics stays **inside** finite accessible light-cone regions with **asymptotic limits** (shell ladder, mode budgets), not a mandatory global infinite-dimensional carrier. What remains “schematic” is mainly **full** textbook continuum renormalisation / arbitrary external QFT input — not something this repo targets as one closed theorem. Rename (`Hypothesis` vs `Axiom`) or split docs if agents still conflate “bridge record” with “unproved physics.” |
| **§6 — numeric `rfl` witnesses** | **Partially.** | Refactor into named `def`s (e.g. `paperWitness_one_over_alpha_EM`) with one docstring, or derive from a smaller set of definitions — improves auditability; does not turn witnesses into independent Lean computations unless you build that derivation. |
| **§1 — paper-level “two axioms”** | **No (in-repo).** | Physics design; formalised as definitions + theorems. |
| **§3 — Mathlib** | **No.** | Standard trust unless you port to a smaller foundation (out of scope). |
| **§7–8 — conventions / imports** | **Documentation only.** | Already honest; expand module docs if something is still ambiguous. |
| **§7 / 7b / 7f — shell pins + SM anchors** | **Documentation + clear `def` docstrings.** | Pins: `qcdShell`, `latticeStepCount`, `referenceM`. Anchors: `m_tau_from_resonance`, `m_top_GeV`, shell triples, composite trace. Same detuned-surface **machinery** across sectors; **uniqueness** of witnesses is open. **New:** §7g single-scale witness; §7h informational mass row — do not double-anchor CODATA α + proton in one solve. |

**Highest ROI:** (1) **Done in-repo:** Lie-subalgebra closure from `G₂ ∪ {Δ}` — `G2DeltaGeneratedLie` (see §5). (2) Optional: delete local root `tmp_*.lean` if you want cleaner `rg` sweeps (they are gitignored). (3) Optional CI on regeneration of `GeneratorsLieClosureData*`. (4) Dedupe “closure” story between `SO8ClosureAbstract` and `G2DeltaGeneratedLie` module docs.

## 11. Corpus audit — from the light cone upward (2026-04)

Read this as **dependency order**: each layer uses the previous ones as **definitions + theorems**; anything marked “pin” or “witness” is not derived from Mathlib alone.

| Layer | Main Lean locus | What is **proved / mechanical** | What remains **assumption, pin, or bridge** |
|-------|-----------------|-----------------------------------|--------------------------------------------|
| **L0 — Discrete null lattice** | `OctonionicLightCone` | Stars-and-bars counts, cumulative sums, `available_modes` / `new_modes`, `α`/`γ` forced pair (`AlphaGammaForcedByLattice`), curvature-norm and `δ_E` combinatorics, quaternionic comparison factor `1296`, harmonic/analytic sandwiches for curvature integral, horizon ratio `omega_k_*` | **Narrative** “why this is the HQIV vacuum” (papers); **non-integer support** for modes (docstring already warns); **reference row** `referenceM` is a pin (§7) |
| **L1 — HQVM metric** | `HQVMetric` | `N = 1 + Φ + φ t`, `γ = 1 − α`, `G_eff` packaging | Lapse form is a **definitional** HQVM story, not derived from Einstein equations in Lean |
| **L2 — O-Maxwell / gauge** | `OMaxwellAlgebraSeed`, `ModifiedMaxwell`, `PromotedOMaxwell`, `SO8ClosureAbstract` / `G2DeltaGeneratedLie` | H-block = algebraic seed; flat `H` → classical Maxwell; **Lie** closure `g2DeltaGeneratedLie_eq_so8LieSubalgebra`; linear span obstruction | **`PromotedOMaxwell*Hypotheses`**, chart-gradient bridges, optional `phi_of_T` recovery |
| **L3 — SM–GR packaging** | `SM_GR_Unification`, `HQIVYangMillsPackage` | `α_GUT`, `1/α_EM` symbolic forms, `HQIV_satisfies_YangMills_SM_GR_Unification` bundle structure | Numeric `rfl` anchors (§6); **unification** is a **structured witness**, not uniqueness |
| **L4 — Mass / sector ladders** | `DerivedGaugeAndLeptonSector`, `ChargedLeptonResonance`, `QuarkMetaResonance`, `ConservedContentMassBridge`, `DerivedNucleonMass`, `InformationalEnergyMass`, `ContinuousXiCoupling`, `ScaleWitness` | Inequalities and ordering lemmas **given** shell selection; closure-layer bookkeeping; nucleon gap from dressed constituents; informational-energy gauges; mass row `c₀+loc=2π·Ω_k` | **Threshold** `chargedLeptonDetunedSurfaceOctaveRatio = 2`; **PDG / named** τ and **quark** top anchors; **quark shell** tables; **baryon** composite trace ansatz; **single active scale witness** must be chosen per pipeline (§7g) |
| **L5 — Zeta / modular / analytic** | `OctonionicZeta`, `ModularThetaBridgeScaffold`, `ThetaCompletedLFunctionalScaffold` | Convergence, residue partitions, trivial-character Dirichlet hooks, `r₈` bounds | **`ThetaZ8ModularRealization.coeff_eq`** (classical θ = `r₈`); **weight-4 completed L** involution for HQIV coefficients |
| **L6 — Continuum / QFT bridges** | `LightConeMaxwellQFTBridge`, `HorizonLimitedRenormLocality`, `ContinuumManyBodyQFTScaffold` | Mode budgets, shell↔harmonic limits, microcausality scaffolds, cluster kernels | **`HorizonContinuumAxioms*`** records; full renormalised QFT **not** a goal |

### 11a. Likely provable or strengthenable (next formal targets)

- **Lie / algebra:** lemmas that shorten the path from `G2DeltaGeneratedLie` to **every** downstream use of `hqivGaugeCarrier` / `hqivYangMillsPackage` (single citation chain in docs).
- **Light cone:** more **pure combinatorics** tying `shellSurface`, `detunedShellSurface`, and `geometricResonanceStep` identities without new physics input.
- **Lepton sector:** theorems that **any** `OuterHorizonLeptonShellSelection` satisfying stated inequalities forces **order** lemmas you already export — uniqueness of the *selector* from minimal axioms is hard, but **conditional** uniqueness fragments may be tractable.
- **Zeta:** any **partial** result on `ThetaZ8LSeriesCoeff` or Dirichlet abscissa (already have bounds); full modular identification is **hard** (classical θ theory).
- **Purge / hygiene:** ensure no `sorry` in the default `lake` library; keep scratch `tmp_*.lean` out of grep-based claims.

### 11b. Build better (engineering quality)

- **One closure narrative:** point all “G₂ + Δ = 𝔰𝔬(8)” claims to `G2DeltaGeneratedLie`; point all “15 matrices don’t span” claims to `SO8ClosureAbstract` — avoid mixed wording in module headers.
- **Witness dictionary:** central table of **numeric `rfl`** names (`one_over_alpha_EM_at_MZ_eq`, Higgs, **etc.**) with one-line “paper alignment” in a single module or `THEOREMS.md` only (avoid duplicating magic numbers). Include **`ScaleWitness`**, **`informationalEnergyMassRow`**, and **`data/hqiv_witnesses.json`** keys in the same dictionary.
- **CI:** optional `scripts/print_*.py --write` diff check for `GeneratorsLieClosureData*` (§4, §10).
- **API:** where §7b says **band vs exact shell**, add a **typed** “band occupancy” layer when you refactor leptons so the formalism matches the docstring in `OctonionicLightCone` (readout grid vs support).
