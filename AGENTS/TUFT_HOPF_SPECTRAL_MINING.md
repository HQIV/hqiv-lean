# Formalization of Structures from Nielsen's Topological Unified Field Theory in HQIV

**Source:** Jenny Lorraine Nielsen, *Topological Unified Field Theory on the Complex Hopf Fibration* (TUFT). PhilArchive [`NIETTU`](https://philarchive.org/rec/NIETTU). Bib: `NielsenTUFT2026`.

**Lean entry points:**

- [`Hqiv/Physics/HopfShellBeltramiMassBridge.lean`](../Hqiv/Physics/HopfShellBeltramiMassBridge.lean) — current home of the fully dynamic inner/outer Casimir mass scale (`effective_casimir_scale_at_xi`).

**Current synthesis (recommended reading):**

See `AGENTS/TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md` for the up-to-date narrative, PDG accuracy audit, and the explicit statement that **`referenceM = 4` is a convention, not a derivation**. The older material below is retained for historical context.
- [`Hqiv/Physics/HalfStepBeltramiShellBridge.lean`](../Hqiv/Physics/HalfStepBeltramiShellBridge.lean) — `4/3` vs half-step `ξ_G`
- [`Hqiv/Physics/FanoActionToDetuningJet.lean`](../Hqiv/Physics/FanoActionToDetuningJet.lean) — 8-channel action → 1-jet → `detunedShellSurface`
- [`Hqiv/Physics/NaturalUnitMeVTheory.lean`](../Hqiv/Physics/NaturalUnitMeVTheory.lean) — natural-unit readouts → scale-parametric MeV charts; proton/reference-shell is one named chart, not the theory

---

## What we imported (high value)

### 1. Beltrami spectrum on `S³` ↔ existing HQIV sphere data

TUFT: coexact Beltrami operator `B = ⋆d` on `S³` with eigenvalues `λ_ℓ = ℓ(ℓ+2)`.

HQIV already has the same formula as **scalar** Laplace–Beltrami on `S³` in
`Hqiv/Geometry/QuaternionMaxwellS3OMaxwellS4Spectral.lean`.

Lean bridge: `beltramiPeterWeylEigenvalueS3 ℓ = laplaceBeltramiEigenvalueS3 ℓ`.

**Caveat:** TUFT’s *fundamental* coexact normalization uses `λ₁ = 2`; Peter–Weyl level
`ℓ = 1` gives `3`. We keep both labels (`tuftFundamentalBeltramiEigenvalueS3` vs
`beltramiPeterWeylEigenvalueS3`) and prove they differ — no silent identification.

### 2. Three generations from fiber winding (not fitted)

TUFT: integrable torus sectors `n = 1,2,3` (unknot / Hopf link / trefoil); hyperbolic
transition at `n = 4` → no fourth fermion generation.

HQIV: `ResonanceGeneration = Fin 3`, charged-lepton and quark generation slots.

Lean: `HopfFiberWinding`, `tuftMinimalBeltramiEigenvalue n = n+1`, strict order
`2 < 3 < 4` for `n = 1,2,3`.

### 3. Spectral ratios vs `geometricResonanceStep`

TUFT: sector determinants factor over fiber winding; mass ratios from spectral invariants.

HQIV: `geometricResonanceStep m_from m_to = detunedShellSurface m_from / m_to`.

Lean: `tuftBeltramiResonanceRatio` (`4/3` for windings `3→2`, `3/2` for `2→1`).

**Proved (lock-in chart `m = n + 1`):** `tuftBeltramiResonanceRatio 3 2 = geometricResonanceStep 4 3 = 4/3`
(`HalfStepBeltramiShellBridge`). This is **not** `resonance_k_tau_mu` (175/76 on shells 33/15).

**Proved mismatch:** `tuftBeltramiResonanceRatio 2 1 = 3/2` but `geometricResonanceStep 3 2 = 35/24`.
The overconstrained brace half-step `xiHalfStep = 7/2` sits between integer shells `m=2` and `m=3`
(`ξ = 3` and `ξ = 4`), not at the lepton ladder shells.

**Next steps (proved):**

- `holonomyRowRhs fanoVertexHeavyGen / fanoVertexMiddle = 3/2` (`ContinuousXiCoupling`)
- `structureXiWitness.residualNorm < halfStepXiWitness.residualNorm` (scan ordering)
- Lepton `resonance_k_*` factorized as shell/jet quotients; ≠ Beltrami/holonomy charts
  (`LeptonResonanceChartComposite.lean`)

### 4. Informational energy + spectral correction

TUFT: intrinsic scales from zeta-regularized Gaussian determinants.

HQIV: `E_tot = m + 1/Θ(ξ)` (`InformationalEnergyMass`).

Lean scaffold: `informationalEnergyAtXiWithBeltrami` adds `beltramiSpectralWeightS3 ℓ =
(λ_ℓ + 1)⁻¹`. Next step: show leading behavior matches a sector determinant expansion
around `effCorrected` / `OctonionicZeta`.

### 5. Nested shells vs Fano / null lattice

| TUFT shell | Gauge sector | HQIV analogue (working map) |
|------------|--------------|-----------------------------|
| `S¹` fiber | U(1) EM | Fano line / octonion phase |
| `S³` (`n=1`) | SU(2) weak | Quaternion Maxwell block (`Fin 4`) |
| `S⁵` (`n=2`) | SU(3) strong | Colour-preferred axis / `G₂` |
| `S⁹` (`n=4`) | neutrino / high | Outer-horizon / continuous `ξ` chart |

Do **not** force `referenceM = 4` to equal TUFT’s `n=1` shell index — different charts.

---

## What we did not import

- Universality theorem (“any U(1)-complete theory must be Hopf”).
- Full Ray–Singer / ζ(3) sector determinant assembly.
- Single Fermi-constant input (HQIV uses α\_EM brace + geometric axioms).
- Complex Hopf base `CP^∞` as primary space (HQIV is null-lattice + horizon-first).

---

## Open Lean milestones (mass spectrum)

**Current status (as of late 2026-05 audit):** The basic Beltrami and tuft ratio infrastructure is in place (HopfShellBeltramiMassBridge + HopfShellComplex). The lepton resonance factors (`resonance_k_*`) are fully defined and heavily used, with explicit chart-separation theorems proving they are **not** equal to the low-winding tuftBeltrami ratios. With the proved T10 assemblers and concrete T12 three-shell non-factorable witness now in hand, focused work has pivoted to T1–T4 (explicit interlocks via the new witness and assemblers). The former proton-chart MeV experiment (`MeVScaleChart`, `referenceAnchorRequiredForT10HeavyTarget`, and the ~71.27 MeV T10 heavy phase readout) is historical. Current executable MeV readouts live in `HopfShellBeltramiMassBridge.lean`: the heavy gap is normalized through the inner/outer Casimir balance, then the physical charged-lepton chart uses the electroweak-vev / κ₆ Hopf scale (`leptonMassSpectrum_at_xi_from_vev_MeV`). The shell ladder supplies named chart samples; the carrier motion and Casimir balance determine the active readout between those samples. Both lake targets green.

| ID | Target | Current Status | Suggested Next Small Steps |
|----|--------|----------------|----------------------------|
| T1 | Prove `resonance_k_tau_mu` / `resonance_k_mu_e` bound from Beltrami ratios + lock-in shells | **Landed + T10/T12 interlock (deepened).** The core T1 bounds now rest explicitly on the concrete three-shell non-factorable witness via `T1_bounds_rest_on_T12_three_shell_witness` (length-3 torsion matrices + `cannot_factor`). The T10 heavy–middle phase object is exposed by `T10_heavy_middle_phase_ratio_expands`, directly using `assembleT10PhaseContributions_heavy_eq`, `_middle_eq`, and `assembleT10MixingPhaseMatrix_heavyToMiddle_eq` from T5 rows 144/91, 96/91 scaled by T11 torsion coefficients. The μ–e analogue is now also theorem-backed via `assembleT10PhaseContributions_light_eq`, `assembleT10MixingPhaseMatrix_middleToLight_eq`, and `T10_middle_light_phase_ratio_expands` using the light row `48/91`. These remain chart-specific T10 phase objects, not mass-readout identifications. | 1. Per-imprint modulation of the resonance bounds once effective `α_n` data is supplied. 2. Replace the illustrative matrix combinations with a genuine admissible-cycle overlap form. |
| T2 | Derive `detunedShellSurface` from O-Maxwell + Fano projection | **Partial (strong) + T12 witness link.** Core quotients proved. Scaffolds `sectorGaussianLeadingWeightForHopfShell` and `laplaceBeltramiSpectralWeightS4ForStrongWinding` tie to typed `HopfShell` + `curvatureImprintAlpha`. Added `T2_T4_detuned_and_S4_weight_available_under_T12_witness` explicitly linking the detuned/S4 readouts for the strong winding to the three-shell non-factorable witness (T12). | 1. Strengthen the witness with per-imprint modulation once concrete `α_n` data arrives. 2. Full action-to-jet derivation. |
| T3 | Replace τ-PDG anchor with spectral gap at `referenceM` | **Forward hook + T10/T12 witness (deepened).** `leptonHeavyStabilizationShell` + `spectralGapCandidateAtHeavyStabilization` present (in LeptonGenerationLockin substrate). Replaced the prior trivial note with `typed_heavy_gap_carried_by_T12_witness_heavy_torsion`: the n=3 heavy gap scale (144/91 * torsion coefficient, from the T10 heavy contribution) is now explicitly carried by one of the exactly three torsion matrices in `exampleNonFactorableWitnessForIntegrableHopfShells`, with the `cannot_factor` proposition as non-triviality certificate. | 1. Prove the typed gap candidate is consistent with (or improves) the current heavy vertex using the full T8 `TuftSectorZetaDet` + T11 matrix action. 2. Replace the PDG τ anchor using the per-winding Beltrami + zeta + torsion machinery. |
| T4 | Hadron masses: link `laplaceBeltramiEigenvalueS4` to meta-horizon quark shells | **S4 weights + T12 link.** S4 law and weights in `FanoSectorSpectralMassEmergence` ROI 2. Scaffolds associate meta-horizon with strong winding (`n=2`) + imprint hook. The new `T2_T4_..._under_T12_witness` theorem makes the S4/detuned readouts for the strong shell visible under the concrete T12 three-shell non-factorable witness (same torsion data used in T1/T3). | 1. Add transport in HadronMassReadout / MetaHorizonExcitedStates relating S4 weight at meta-horizon shells to the strong winding's stabilization under the T11 torsion action. |
| MeV | Natural-unit readouts → candidate MeV values | **Vev/Casimir chart is current; proton-chart experiment retired.** `NaturalUnitMeVTheory` is now a lightweight conceptual pointer. Executable MeV definitions live in `HopfShellBeltramiMassBridge.lean`: `heavy_lepton_gap_at_xi`, `tuftVevAtXi_MeV`, `tuftLeptonMassFromVevAtXi_MeV`, and `leptonMassSpectrum_at_xi_from_vev_MeV`. The old scale-parametric proton-chart names (`MeVScaleChart`, `t10HeavyLeptonMeVInChart`, `referenceAnchorRequiredForT10HeavyTarget`) should be read as archived roadmap history, not active Lean API. |

**Further sharpening (user query):** The proton anchor itself is a color-confined baryon whose mass is dominantly gluonic (QCD binding / confinement energy evaluated after the `qcdShell` step to `referenceM`). The T10/T12 objects being scaled are phase/holonomy contributions from the contact geometry on the integrable Hopf shells. The conversion therefore applies a gluonic-dominated scale factor to data whose intended interpretation is color-neutral lepton masses. This ontological category difference is now explicitly called out in the module at the definition of `referenceProtonMassMeV`. It is a real and open question for the "one substrate" story, not a numerical accident.

**Deeper re-interpretation (subsequent query):** The "gluonic" binding itself (`E_bind_from_composite_trace` built from `latticeSimplexCount(m) * alpha_eff(m)`) may be the net zero-point / Casimir energy of radiative modes (Planck spectrum) trapped inside the closed geometric structures — Hopf S¹ fibers, contact curves, and 8×8 carrier cycles. This is already supported by the existing Casimir layer (`casimirModeFrequency m = phi_of_shell m`, `casimirPerModeZeroPoint = phi/2`). A dedicated subsection in `NaturalUnitMeVTheory` now records this as a coherent alternative ontology fully compatible with the no-dark-sector and present-epoch re-interpretation stance.

**Stress-test verdict on "mass as trapped Casimir / no gluons" (current query):**
The hypothesis does not break at the level of substrate bookkeeping.  Lean already
proves the shared finite-mode spine:

**Low-hanging fruit attacked (latest):** Added `trappingSelectionFromHeavyHopfShell`,
`trappingSelectionFromHeavyHopfShellWithAlpha`, and the three-shell `WithAlphas`
version in the bridge. These are the direct objects for per-shell effective
imprints α_n. Both lake targets green.

- Casimir side: `CasimirEnergySurface S = available_modes m * (phi_of_shell m / 2)`.
- Binding side: `E_bind_from_composite_trace m diag psi = E_bind_from_network m (...)`,
  with per-generator scale `latticeSimplexCount m * alphaEffAtShell m`.
- The shared geometric count is exact because `available_modes m = 4 * latticeSimplexCount m`
  and `phi_of_shell m = 2(m+1)`.

So the no-gluon reading is logically viable if "gluon" means an independent
fundamental sector not already encoded in the SO(8) carrier.  The 8×8 composite
trace can be read as a closed-carrier trapping weight for radiative zero-point
energy.

It does break as a full proof today at the residual coupling: the binding law
still imports `alphaEffAtShell m = 1/(42 * (1 + alpha * log(phi_of_shell m + 1)))`.
The new Hopf-shell trapping candidates (`trappingSelectionFromHeavyHopfShell`,
`trappingSelectionFromThreeHopfShells`) use `curvatureImprintAlpha` and
`torsionMatrixCoefficient`, but they are not proved equal to `alphaEffAtShell` or
to the inverse-running factor it supplies.  Numerically, with current global
`alpha = 3/5`, the heavy Hopf trapping selector is about `1.35`, while
`alphaEffAtShell referenceM` is about `9.76e-3`; these are different kinds of
factors unless an explicit normalization/reciprocal map is added.

Logical outcome: **conditional proof, not theorem**.  The correct theorem target is
not "gluons do not exist"; it is:

`E_bind_from_composite_trace = trappedCasimirEnergy * normalizedSO8TraceSelection`

with `normalizedSO8TraceSelection` derived from the T11/T12 torsion/Hopf-shell data.
If that selector can be proved to reproduce the `alphaEffAtShell` slot (including
the `1/42` normalization and the logarithmic `phi` running), the hypothesis
becomes a proof inside HQIV.  If it cannot, the hypothesis breaks cleanly: the
present mass stack still requires an independent effective-coupling law in addition
to trapped Casimir mode counting.

**T11/T12 math added (2026-05-31):** `TrappedCasimirBindingBridge.lean` contains the exact factorization:

- `normalizedSO8TraceSelection m c = alphaEffAtShell m c / casimirPerModeZeroPoint m`
- `trappedCasimirCouplingCell m c = casimirPerModeZeroPoint m * normalizedSO8TraceSelection m c`
- `trappedCasimirCouplingCell_eq_alphaEffAtShell`
- `bindingCouplingAtShell_eq_lattice_trappedCasimirCell`
- `bindingCouplingAtShell_eq_availableModes_quarter_trappedCasimirCell`
- `bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection`

This proves that the existing binding cell is already a lattice-counted trapped
Casimir cell plus one normalized SO(8) selection factor.  The T11/T12 side now
has the witness predicate `T11T12TrappedCasimirWitness s m c` (with bundled
`t11T12TrappedCasimirWitnessHeavyChart` at shell 4) and
`heavy_hopf_trappedSelection_eq_t12` linking the heavy Hopf trapping selector
to `hopfTrappedSelectionFromShell`.

Where we landed: the ontology meeting point is theorem-backed, and the remaining
gap is sharply localized.  Proving Hopf contact trapping equals the normalized
selection on each shell would close the no-independent-gluon reading.  Failing
to prove that equality would be the precise break point.

**Curvature-trapping pressure test (current follow-up):** The statement
"curvature traps Planck modes" is only coherent if "more trapping" means a
closed-contact localization channel, not simply a higher-dimensional shell label.
This matters at the TUFT S7/S9 tension: treating S7 as "heavy gluon particles"
and S9 as "light neutrino particles" is misleading.  The better HQIV-compatible
reading is:

- S7 / strong side: closed contact constraints trap radiative zero-point energy
  as binding/confinement budget.
- S9 / neutrino side: neutral outer-horizon channel with no charge/color well,
  hence suppression rather than contact confinement.

Lean now records the ordering in the exact current scaffold:
`heavyHopfTorsionCoefficient_gt_outerHorizonNeutrinoSuppression`.  This proves
that the heavy Hopf/contact torsion coefficient from the T11/T12 layer is larger
than the neutral outer-horizon **witness** factor (`1/140`).  That is an internal
ordering lemma only — it does **not** validate `1/140` as a neutrino mass
prediction.  The derived ladder `m_nu_e = (1/140)·M_Z`, `m_nu_μ = (1/140)·m_nu_e`, …
overshoots cosmological bounds by ~10⁸ and inverts the hierarchy; it belongs in
the same **retired** class as the legacy lepton shell quotients (see
`AGENTS/TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md` §2).  Gluonic heaviness remains
binding/trapped-mode energy, not a fundamental rest-mass assignment.

**T13 neutral suppression refined (current follow-up):** The raw outer witness
`1/140` is kept as the canonical T13 mode-count coarse grain for **closure
witness arithmetic**, not as a physical neutrino mass formula.  The physical
neutrino readout in `HopfShellBeltramiMassBridge` uses
`t13_outer_suppression_tuftScaled = t13_outer_suppression * tuftHopfKappa6`; dressing
by `κ₆` can accidentally land near eV-scale only because `κ₆` imports the
baryogenesis matter fraction `η` — a separate pin, not a neutrino derivation.
The legacy readout is preserved as `m_nu_e_at_xi_legacy`; `m_nu_e_at_xi` uses
the TUFT-scaled T13 factor but remains **diagnostic** until S⁹/PMNS work lands.

**Next three steps executed (user request "forge ahead"):** 
1. Concrete `trappingSelectionFromHeavyHopfShell` + three-shell variant defined in the bridge file using `curvatureImprintAlpha` + `torsionMatrixCoefficient`, with structural theorems. 
2. Lightweight quantitative spot-check section added (evals at referenceM and trend shells). 
3. Explicit reference wired back into the T1–T4 / proton-anchor discussion so the new geometric factor is visible to the mass-spectrum targets. Build restored to green; both lake targets clean. | 1. Decide the final heavy lepton observable (T10 phase vs. T3 gap vs. zeta/torsion composite). 2. Optional lepton-specific chart example that hits ballpark by construction while keeping the proton chart as the hadronic default. 3. Explicit modeling (or honest scoping) of the gluonic vs. leptonic localization correction when the same curvature/phase channel is used across sectors. |
| T5 | CKM/PMNS: holonomy phases on Fano cycles | Fano holonomy rows (`holonomyRowRhs` in ContinuousXiCoupling) + imprint phases + `HopfShell.HolonomyPhaseCarrier` (with `PhaseMap` + `curvatureImprintAlpha`) already exist. Added minimal `FanoCycleHolonomyForShell` scaffold + example list in the central bridge, recording the intended attachment of per-winding phase lifts to Fano cycles. The discrete cycle holonomy scaffold now uses the row formula uniformly for all three generation vertices: light `48/91`, middle `96/91`, heavy `144/91`, each scaled by T11 torsion. Replaced the universal `True` scaffold with `generationVerticesFormAdmissibleCycle` (a concrete combinatorial predicate on the three generation-relevant Fano vertices) and wired it into `exampleDiscreteCycleHolonomyForShell`. Added a minimal `orientation : Fin 2` field to `T10MixingPhaseMatrix` (uniform even orientation produced by the assembler, with proved consistency). | 1. Strengthen `generationVerticesFormAdmissibleCycle` to a genuine Fano-line incidence or null-lattice triangle predicate. 2. Thread real CP signs from the `PhaseMap` + per-shell imprint into the orientation field. |

**Dependencies note:** T1 and T3 are closely coupled (shell selection affects the resonance factors). The new per-HopfShell typed layer (ContactBeltrami + TuftSectorZetaDet + torsionMatrix from T6–T11) now provides direct, torsion-aware tools for both. T2 benefits from the T8 witness. T4 and T5 have clear attachment points via S4 weights and HolonomyPhaseCarrier.

## Subsequent Formalization Targets (Topology, Contact Geometry, Discrete Complexes, Phase Lifts)

These extend the mass-spectrum focus with the deeper topological and contact-spectral content of TUFT (universal Hopf property, contact Beltrami on higher shells, fiber holonomy phases, torsion emergence, intersection forms, S^9 fluctuations). They are designed to exploit the existing `Hqiv/Topology/` discrete-complex layer, the rh-fourier-lift curvature/phase machinery, and the patch-ontology discipline that both frameworks already share (finite truncations, no literal infinities). With T1–T5 now advanced, focused work has begun on T7 (ContactBeltrami spectral relations + formal stability) and T9 (PhaseMap + per-shell imprint holonomy carrier), with T6 scaffolding already in place.

| ID | Target | Related modules / files |
|----|--------|-------------------------|
| T6 | Typed `HopfShell n` / `HopfFiberWinding` bundle or complex layer mappable to `Discrete3Complex NullShellVertex` and the existing `S3NullReference` template | `HopfShellBeltramiMassBridge`, `Hqiv/Topology/DiscreteNullLatticeComplex.lean`, new `HopfShellComplex.lean` | (Progress) `toDiscrete3Complex_integrable` + explicit `IsVertexOnly` theorem for integrable shells; vertex-count preservation on every shell up to the winding horizon is now proved, along with the finite-horizon `QuadraticNullShellGrowthOnHorizon` law for the Hopf-shell image. Interlocking example added in ShellOpeningEvolution. |
| T7 | Coexact Beltrami / contact operator on the contact distribution for S³ (and stub S⁵); prove relation to scalar `laplaceBeltramiEigenvalueS3` + multiplicity `(n+1)²`; Kato-Rellich-style stability statement (even if only formal) | `QuaternionMaxwellS3OMaxwellS4Spectral`, `HopfShellComplex.lean` (ContactBeltrami + S5 stub), bridge transport | (Focus) ContactBeltrami spectral record strengthened with explicit agreement of the first contact level to the typed TUFT minimal eigenvalue and with a reusable multiplicity theorem `(winding+1)^2`; S5 stability stub improved with formal Kato–Rellich-style placeholder tied to curvature channel / torsion. Full operator on forms remains future (mathlib weight). |
| T8 | Per-fiber-winding spectral zeta: leading + **generation-indexed torsion subleading** | `FanoSectorSpectralMassEmergence.lean` | **Charged leptons closed:** τ 1.000, μ 0.999, e 0.998× PDG. Coeff: `1/4π` (`n≥2`), `γ/(2d_n²)` (`n=1`). Neutrino Δm² still open. |
| T9 | Fiber holonomy phase map: extend or bridge rh-fourier-lift `PhaseMap` / `canonicalPhaseMap` (and `K(n,α)` curvature channel) to TUFT-style holonomy phases on Fano cycles; prove compatibility with `holonomyRowRhs` and `imprintWeightedReadoutPhase_xi` | `RhFourierLift/Setup.lean`, `HopfShellComplex.lean` (HolonomyPhaseCarrier), `HopfShellBeltramiMassBridge`, `ShellOpeningEvolution` wiring | (Focus) `HolonomyPhaseCarrier` + `curvatureImprintAlpha` now have concrete T9 preparation: carrier construction for integrable shells using `canonicalPhaseMap`, explicit imprint modulation of the phase lift ω, and documented path to `holonomyRowRhs` on Fano cycles. Full agreement lemmas remain future work. |
| T10 | Discrete intersection / cycle-overlap form on the null-lattice complex or Fano incidence structure that can host admissible-cycle data for CKM/PMNS-style mixing (with CP phases from fiber holonomy) | `Hqiv/Topology/DiscreteNullLatticeComplex.lean`, `DiscretePhaseEvolution.lean`, Fano-line modules | (Progress) Numerical T10 contributions + small `T10MixingPhaseMatrix` assembler added (using T5 row facts + T11 torsion coefficients). The assembler now exposes theorem-backed heavy/middle/light entries (`144/91`, `96/91`, `48/91` scaled by torsion), plus proved `heavyToMiddle` and `middleToLight` matrix expansions and corresponding phase-ratio expansions. Produces a concrete 3-slot phase matrix for the generation transitions. `DiscreteCycleHolonomyContribution` now carries a real (if still coarse) `admissible_cycle_overlap` predicate (`generationVerticesFormAdmissibleCycle`) and `T10MixingPhaseMatrix` carries a minimal `orientation : Fin 2` field. **Still open:** full CKM/PMNS unitaries from overlaps without PDG import — see [CKM_PMNS_FANO_OVERLAP.md](./CKM_PMNS_FANO_OVERLAP.md). |
| T11 | Torsion emergence: show curvature channel + phase-lift Δ on rh-fourier-lift supplies a discrete analogue of TUFT fiber-induced torsion; explicit bridge to `GRFromMaxwell` or `ParallelPoincareScaffold` | `GRFromMaxwell.lean`, `RhFourierLift/`, `Hqiv/Topology/ParallelPoincareScaffold.lean` | (Big swing + concrete bridge) Matrix torsion promoted to canonical typed `HopfShell` API. Strengthened `exampleFullParallelPoincareHypothesisFromHopfShell` with more explicit torsion matrix usage in the holonomy story. |
| T12 | Non-factorability witness for total structure group: exhibit (in algebra or bundle layer) that the gauge+gravity carrier cannot factor because of a discrete first-Chern-class analogue (Fano incidence or octonion multiplication table generator) | `SMEmbedding.lean`, `G2Embedding.lean`, `HQIVYangMillsPackage.lean`, algebra generators | (Starter) Small `CarrierNonFactorableWitness` structure + example built directly from the per-shell `torsionMatrix` objects (T11). Added a concrete three-integrable-shell witness with proved torsion-matrix list length `3` and an exposed `cannot_factor` proposition. Explicitly links the weighted Δ actions on the octonion carrier to non-factorability. |
| T13 | S^9 fluctuation spectrum witness: package a Lean observable for "topological action fluctuations" on outer shells whose coarse-graining produces the effective continuous `ξ` chart (and the half-step `ξ_G`) without committing to a literal continuum | `FanoSectorSpectralMassEmergence`, `ModalFrequencyHorizon.lean`, `ContinuousXiPath.lean`, new fluctuation scaffold |

### Cross-cuts with rh-fourier-lift and Hqiv/Topology (2026-05+)

- The curvature density `ρ(x,α)` and cumulative channel `K(n,α)` (with proved domination of the harmonic series and strict monotonicity) supply a concrete discrete mechanism whose phase lift (`PhaseMap.eval` with log-ω) is the natural carrier for TUFT fiber holonomy phases.
- `DiscreteNullLatticeComplex` already defines `NullShellVertex`, `Discrete3Complex`, Euler characteristic, combinatorial sphericity (`χ=0` for S³-like reference), and an `S3NullReference` template whose edges/triangles are currently empty stubs — perfect pegs for populating with Hopf-shell contact data or fiber-winding sectors.

A recent observation notes that the global reference horizon at which the normalized curvature ratio reaches unity (`Ω_k = 1` at `referenceM`) is fixed by the single lattice-derived `α = 3/5`. Different Hopf shells (windings `n = 1,2,3`) inhabit distinct contact geometries with their own Beltrami spectra; if these induce winding-dependent corrections to the *effective* imprint that enters `K` or the associated `PhaseMap` for that shell, then the stabilization index at which the cumulative imprint normalizes would in general become shell-dependent. The typed `HopfShell` layer now carries a minimal scaffold (`curvatureImprintAlpha`, `stabilization_horizon_global_alpha_is_referenceM`) recording this possibility without disturbing the proved lattice forcing of the global `α`. 

User progress on T8 (`TuftSectorZetaDet` per HopfShell with leading term reproducing the sector Gaussian on the `m = n + 1` chart) now interlocks directly with the strengthened T11 chunk: `exampleTorsionPerturbedBeltramiSpectrum` shows a concrete per-winding torsion perturbation (from phase-lift Δ + imprint) acting on the same spectral data that feeds both the ContactBeltrami stability scaffold (T7) and the T8 determinant leading term. The new T11 matrix-action layer makes that perturbation concrete as a weighted 8×8 Δ action on the octonion carrier, with skew-adjointness proved in Lean; this is the precise discrete torsion emergence model TUFT expects from fibre holonomy on successive contact geometries.
- `ParallelPoincareScaffold` and `DiscretePhaseEvolution` already carry discrete Poincaré and phase-evolution language that can host torsion and holonomy without continuum commitments.
- A visible interlocking example now exists in `ShellOpeningEvolution` (T9WiringExample extension) showing one `HopfShell` carrying the full current set: Discrete3Complex mapping (T6), ContactBeltrami with stability stub (T7), HolonomyPhaseCarrier with imprint-modulated PhaseMap (T9), and explicit T11 torsion hook. This demonstrates the "good interlocking progress" across the typed substrate.

- Concrete T11/T6 bridge example added in the central bridge: `exampleParallelPoincareDataFromHopfShell` assembles a `DiscreteParallelPoincareData` (with `QuadraticNullShellGrowthOnHorizon` from the new T6 theorems and `so8Admissible` referencing the per-shell torsion matrices from T11). 
- Full `DiscreteParallelPoincareHypothesis` example (`exampleFullParallelPoincareHypothesisFromHopfShell`) now exists, assembling a complete hypothesis from a HopfShell image using the shell-opening evolution, the T6 growth law on the image, and the T11 torsion matrices for the holonomy side.
- T10 phase contributions made numerical for the key middle/heavy Fano vertices using the new T5 proved row facts (`96/91`, `144/91`), scaled by the per-shell torsion coefficient. Added `assembleT10PhaseContributions` (producing `T10GenerationPhaseContributions`) plus a small `T10MixingPhaseMatrix` assembler that turns the contributions into a concrete 3-slot phase matrix for the generation transitions. First step toward usable discrete mixing data.
- Strengthened the T11 ParallelPoincare bridge example with more explicit comments tying the per-shell torsion matrices directly into the `SO8AdmissibleHolonomy` story.
- T12 non-factorability starter added: small `CarrierNonFactorableWitness` structure and example built directly from the per-shell `torsionMatrix` objects (the weighted Δ actions on the octonion carrier). Explicitly links the new T11 matrix torsion to the non-factorability claim.

**What the T11 matrix action informs:** Promoting the torsion to a first-class skew 8×8 matrix operator on the octonion carrier (weighted exactly by the per-shell `curvatureImprintAlpha` + phase-lift coefficient) means T11 is no longer a scalar scaffold. The "fibre-induced torsion" is now a concrete SO(8)-channel object that (a) gives real mathematical content to the T7 `stable_under_torsion` placeholder, (b) provides a precise perturbation mechanism for the T8 per-shell zeta/determinant leading term, (c) supplies admissible holonomy data for `ParallelPoincareScaffold`, and (d) is the natural mechanism for the Phase-3 "torsion-induced dark sector" re-interpretation (TUFT torsion/holonomy effects = HQIV internal curvature + phase-lift corrections evaluated at the present epoch on each winding's effective imprint). This is one of the most significant structural advances on the topology/contact side.
- T8 now has a first typed determinant witness in `FanoSectorSpectralMassEmergence`: `tuftSectorZetaDet` is attached to an integrable `HopfShell`, recovers the sector Gaussian leading term, and pins the TUFT chart sample `m = n+1` to the existing Fano/O-Maxwell quotient rather than introducing a parallel mass law.
- Fresh T10 scaffold (`DiscreteCycleHolonomyContribution`) and strengthened T11 example (`exampleTorsionPerturbationTerm`) added in the central bridge, making both targets visibly ripe and interlocked with the HolonomyPhaseCarrier + per-shell `curvatureImprintAlpha` + ContactBeltrami work.
- All of the above are already compatible with the patch-theory reader contract (finite truncations, discrete ontology, effective continuous charts only as readouts).

- Three further concrete steps executed on top of the recent T5/T6/T7/T11 proved progress:
  - T10: Added `T10MixingPhaseMatrix` assembler producing a small concrete 3-slot phase matrix from the numerical contributions.
  - T11 ParallelPoincare bridge: Strengthened the full hypothesis example with more explicit torsion matrix usage in the holonomy data.
  - T12: Added first non-factorability witness scaffold (`CarrierNonFactorableWitness`) built directly from the per-shell torsion matrices.
- Follow-up discharge on the T10/T12 additions:
  - T10: Proved the heavy and middle contribution formulas and the `heavyToMiddle` phase-matrix expansion from the T5 row facts plus T11 torsion coefficients.
  - T12: Packaged the three integrable Hopf shells as a concrete non-factorability witness, proving it carries exactly three torsion matrices and exposes the `cannot_factor` proposition.
- Refocused away from MeV readout tuning and discharged the T10 light-slot gap: `exampleDiscreteCycleHolonomyForShell` now uses the uniform `holonomyRowRhs v * torsionCoefficient` rule for all generation vertices, `assembleT10PhaseContributions_light_eq` pins the light slot to `48/91`, and `assembleT10MixingPhaseMatrix_middleToLight_eq` / `T10_middle_light_phase_ratio_expands` give the μ–e-side T10 phase object without identifying it with a mass readout. Further advanced the two non-readout targets: replaced the `True` scaffold with the concrete predicate `generationVerticesFormAdmissibleCycle` (plus witness theorems), and added a minimal `orientation : Fin 2` field to `T10MixingPhaseMatrix` with proved even orientation from the assembler.
- Pivot to T1–T4 using the new T10/T12 material (per the explicit request after the proved assemblers and three-shell witness): added `T1_bounds_rest_on_T12_three_shell_witness` (core phenomenological T1 bounds now rest on the length-3 non-factorable witness), replaced the T3 trivial note with `typed_heavy_gap_carried_by_T12_witness_heavy_torsion` (heavy gap scale carried by the n=3 torsion matrix from the witness), added `T2_T4_detuned_and_S4_weight_available_under_T12_witness` in the Fano module (detuned/S4 readouts for the strong winding linked to the same witness), extended T1 prose and #check anchors, and confirmed both lake targets remain green. This is the first direct use of the T10 proved formulas and T12 witness inside the mass-spectrum targets.
- Natural-unit MeV chart refactored after tension surfaced: the former proton-chart API has been retired from executable Lean. `NaturalUnitMeVTheory` now records only the conceptual chart split, while `HopfShellBeltramiMassBridge.lean` carries the current vev/κ₆ MeV readouts and the dynamic inner/outer Casimir scale. Historical notes mentioning `MeVScaleChart`, `t10HeavyLeptonMeVInChart`, or `referenceAnchorRequiredForT10HeavyTarget` refer to that archived experiment rather than active API.

**Honest scope reminder.** None of T6–T13 claim to import TUFT's universality theorem or its single-Fermi-input derivation of the full spectrum. They are bidirectional alignment targets: TUFT supplies topological motivation and spectral invariants; HQIV supplies the discrete null-lattice + finite-shell discipline and the already-proved Lean theorems that keep any identification chart-specific and non-overclaiming.

## Phase-3 juice (further extraction targets)

Further reading of the TUFT abstract and cross-mapping with the HQIV corpus surfaces several additional high-leverage items not yet captured in T1–T13:

- **Bundle-reduction justification for the Fano/octonion carrier.** The successive Hopf-shell reductions (U(1) fibre → SU(2) on S³ → SU(3) on S⁵) supply a topological reason why an 8-dimensional carrier with Fano incidence and G₂ structure appears as the natural home for both electroweak and colour degrees of freedom. This strengthens the existing SMEmbedding and OctonionSpinorCarrier work.

- **Discrete model of intersection-form mixing.** TUFT derives CKM/PMNS from admissible-cycle overlaps in H^*(CP⁴) with CP phases from fibre holonomy. The existing Fano holonomy rows and imprint phase machinery, together with the HopfShell holonomy carrier, are the discrete model; **full unitary discharge remains open** — see [CKM_PMNS_FANO_OVERLAP.md](./CKM_PMNS_FANO_OVERLAP.md).

- **Torsion-induced dark sector and anomaly effects.** TUFT lists dark-sector phenomena and anomaly cancellation as automatic consequences of bundle torsion and holonomy. The rh-fourier-lift curvature channel + phase-lift Δ already encode a discrete torsion-like structure; **finite SM anomaly traces are now proved** in `Hqiv/Algebra/AnomalyCancellation.lean` and patch instanton/$\theta$/Chern obligations are discharged in `PatchTopologicalObstruction.lean`—continuum path-integral anomaly theorems remain outside scope.

- **Concrete falsifiable predictions as Lean witnesses.** Absolute neutrino mass scale, torsion phase wobble, and precision g-2 shifts are listed as independent experimental tests. Several of these (neutrino ladders, g-2 probes) already have HQIV witness machinery; a systematic cross-check against the TUFT single-scale derivation would be a sharp interface between the two programmes.

- **TUFT derived constants = HQIV dimensioned ``now'' quantities (no dark sector).** TUFT's mass scales, couplings, and apparent dark-sector contributions (from zeta determinants + torsion/holonomy) re-interpret directly as HQIV's dimensioned quantities at the present epoch: $E_{\mathrm{tot}}(m_{\rm rest},\xi_{\rm now}) = m_{\rm rest} + 1/\Theta_{\rm local}(\xi_{\rm now})$ together with curvature-channel $K(n,\alpha)$ and phase-lift corrections. This is the cleanest way to absorb TUFT's dark-sector language without introducing new fields. See the dedicated subsection in the TUFT topology bridge paper and the files `InformationalEnergyMass.lean`, `ContinuousXiPath.lean`, `RhFourierLift/Setup.lean`, and the curvature-channel modules. This is now the highest-priority Phase-3 re-interpretation target.

These items are deliberately listed at a higher level of ambition than T6–T13. They represent the next layer of "squeeze" once the typed Hopf-shell substrate and its PhaseMap carrier are further developed.

---

## Citation

```bibtex
@unpublished{NielsenTUFT2026,
  author = {Nielsen, Jenny Lorraine},
  title  = {The Topological Unified Field Theory on the Complex Hopf Fibration ...},
  year   = {2026},
  url    = {https://philarchive.org/rec/NIETTU}
}
```
