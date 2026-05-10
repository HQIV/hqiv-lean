# Roadmap: 3-manifold geometry ↔ lattice zeta (status-tracked)

This document is a **proof path** for agents: how one *could* connect the **discrete** HQIV shell zeta (`Hqiv.Physics.OctonionicZeta`, `Hqiv.Physics.DivisionAlgebraZetaScaffold`) to **global** statements on a spatial slice (simply connected `Σ³`), Ricci-weighted curvature data, and—much later—analytic number theory (L-functions / modular forms). **What is already in Lean** starts at the anchors in §0 — including the **constructive Euclidean** shell family and finite Lebesgue volume in `SpatialSliceManifold` (not yet Ricci integrals or identification with `deltaE`).

**Unified probe narrative (scope + four-problem storytelling, still lattice-scoped):** [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md) — single unifying object (`φ t`, curvature slots, `eff`), ℝ¹ zeta / monogamic sum, Yang–Mills and RH **as prose**, explicit “what is not claimed” table.

**Millennium formal standard:** [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md) — compatibility with [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems).

**Modular forms / L-functions / BSD ladder:** [MODULAR_FORMS_LADDER.md](./MODULAR_FORMS_LADDER.md) (long-horizon analytic thread; complements §4 below).

**Related (narrative only, no NS PDE in Lean):** [NAVIER_STOKES_HQIV_NARRATIVE.md](./NAVIER_STOKES_HQIV_NARRATIVE.md) — classical 3D NS / Millennium framing vs HQIV standing-wave / horizon regularization, with self-clock as one possible state-language.

**Related (fluid ladder, O-Maxwell attachment):** [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md) — effective modified fluid (`f`, `g_vac`, `ν_eddy`), plasma-as-viscous-fluid closure milestones F0–F5, honesty table.

**Related (Hodge conjecture analogy, not proved):** [HODGE_HQIV_NARRATIVE.md](./HODGE_HQIV_NARRATIVE.md) — cycles / periods / Fano vs algebraic Hodge classes. **Lean wiring at the same tier as rapidity–zeta:** [HODGE_HQIV_NARRATIVE.md](./HODGE_HQIV_NARRATIVE.md) §5 + `HodgeRapidityZetaBridge.lean` (`shellResidueFano_of_f_val_add_seven_mul`, `zetaHQIVTerm_eq_eff_mul_cexp_polarAngle_of_coincident_rapidity`).

**Related (quantum-circuit metaphor, not proved):** [QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md](./QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md) — sparse-register story for `LatticeNextPrimeGenerator`; classical Lean only.

### Proof priority (when choosing the next Lean lemmas)

Prefer lemmas that **serve more than one narrative thread** on the same discrete shell ladder (`m : ℕ`, `φ·t`, `eff`, Fano mod 7):

| Higher leverage | Examples of cross-cutting wins |
|-----------------|--------------------------------|
| Identities that **name the same real/complex data** in zeta, polar/spiral scaffold, and optional period/Hodge probe | `RapidityZetaPhaseBridge`, `HodgeRapidityZetaBridge`, `shellResidueFano_of_f_val_add_seven_mul` |
| Summability / analyticity **propagated** across term variants that share `eff` and phase slots | `HQIVLSeriesAnalytic` patterns, monogamic rewrites already in `DivisionAlgebraZetaScaffold` |
| Explicit `Prop` bridges **comparing** combinatorial `δ_E` / geometric slots / fluid surrogates | `agreesWithCombinatorialDeltaE`, `PlasmaFluidClosureAssumptions` (document hypotheses once, reuse) |

Defer one-off lemmas that only polish a **single** module unless they unblock the rows above.

## Status snapshot (now)

### Proved/implemented now (library + scripts)

- Euclidean shell geometry anchors are in place (`SpatialSliceManifold`, `LatticePointMaxAbsShells`).
- Ball-slice geometry is proved for both:
  - fixed third axis: `closedBall_inter_coordPlane_eq_image_slice`,
  - any axis `k : Fin 3`: `closedBall_inter_coordPlane_k_eq_image_slice` via `coordPlaneIsometry`.
- `π` baseline + defect scaffolding is implemented:
  - `piSliceAreaBaseline`, `sliceAreaDefect`,
  - shell-indexed `piSliceAreaBaselineAt`, `sliceAreaDefectAt`,
  - decomposition lemmas (`observed = baseline + defect`, zero-defect iff baseline match).
- Candidate-peak bridge from next-shell generator is implemented (explicitly non-overclaiming):
  - `sliceDefectProfileAtZ`, `nextShellDefectCandidate`, `nextShellDefectValue`,
  - global/window peak predicates and range-window wrappers:
    `IsWindowAbsPeak`, `isWindowAbsPeak_iff_range`, `candidate_isWindowAbsPeak_of_rangeHyp`.
- Search scripts exist and run:
  - `scripts/search_slice_defect_peak.py` (window peak witness format),
  - `scripts/fano_slice_fft_probe.py` (Fano-angle slice isolation + FFT).
- Milestone F scaffold now implemented:
  - class/local `k`-periodic rapidity slots and `1/k`-spiral domain law in
    `Hqiv/Geometry/SpatialSliceRapidityScaffold.lean`:
    `periodicRapidityCandidateSlots`, `RapidityKSphereDomain`,
    `rapidityPhaseFromOmegaOneOverKOnDomain`,
    `periodicOneOverKSpiralSlotsOnDomain`,
    `periodicOneOverKSpiralSlotsOnDomain_intersection_exists`.
- Milestone G probe pipeline now implemented (execution layer, still non-modularity-claim):
  - `scripts/factor_from_curvature.py` with Ω-imprint driven phase (`--omega-imprint`),
    arity root-scale search (`--arity`, `n^(1/k)` bound), axis-centered rotations,
    and recursive prime-gradient mode.
- Hodge-trajectory probe strengthened (still analogy/probe only):
  - period/slot structures now explicitly class-local and domain-local in
    `SpatialSliceRapidityScaffold.lean` (`HodgeClassProbe`,
    `FanoPeriodRapidityCoincidence`, k-sphere domain slot families).
- **Cross-thread wires (proved; not Millennium theorems):**
  - **Zeta phase = polar angle:** `RapidityZetaPhaseBridge.lean` (`zetaHQIVTerm_eq_effCorrected_mul_cexp_polarAngleFromRapidity`, …); **π/2 scale** for tipping: `delta_theta_prime_eq_arctan_mul_pi_div_two` (`OMaxwellAlgebraSeed`).
  - **Fano strands = algebra cycle tags:** `shellResidueFano_of_f_val_add_seven_mul` (`CycleHodgeProbeScaffold`), `fano_vertex_of_shell_f_val_add_seven_mul` (`DivisionAlgebraZetaScaffold`).
  - **Hodge probe + zeta (same `φ,t` hypothesis):** `HodgeRapidityZetaBridge.lean` (`zetaHQIVTerm_eq_eff_mul_cexp_polarAngle_of_coincident_rapidity`, …).
  - **HQIV Dirichlet ↔ Mathlib `LSeries`:** `HQIVLSeriesAnalytic` (equality on `Re s > 1`, holomorphy, derivative; constant-coefficient smul of ζ when `hqivCoeff` constant).

### Actively sought next (not proved yet)

- Real-data defect profiles (neutrino/quark standing-wave outputs), replacing proxy/smoke inputs.
- Robust periodicity evidence on Fano slices (threshold/window-stable retained directions, dominant periods).
- Lean-side bridge from FFT reports to theorem assumptions (currently hypotheses are fed manually).
- Any geometric statement that ties candidate shell to a **true global** defect peak (currently window-only).
- **Ray theorem:** shell `m` → unit tangent / preferred discrete ray on a **formal** Riemannian `S³` (or `Σ³` chart) agreeing with `polarAngleFromRapidity` / `delta_theta_prime` — still only `LatticeContinuumRapidityCoincidence`-style **intent**.
- **Classical Hodge / Chow / motives:** no projective variety layer; `HodgeClassProbe` remains a **real** contour-sum scaffold ([HODGE_HQIV_NARRATIVE.md](./HODGE_HQIV_NARRATIVE.md) §5 “still open”).
- **Modularity / BSD / critical line:** strategy docs only ([MODULAR_FORMS_LADDER.md](./MODULAR_FORMS_LADDER.md), [BSD_RN_RAMANUJAN_BRIDGE.md](./BSD_RN_RAMANUJAN_BRIDGE.md)); no elliptic-curve or Petersson-bound identification proved for HQIV sums.

### New intuition to formalize (HQIV analogue boundary lock)

- Working intuition: conserved shell-temperature redistribution (ladder tied to `φ·t` and `δ_E` slot)
  places the HQIV deformation exactly at an analogue boundary with no backward “vaporization room”.
- Formal discipline: encode this as an **HQIV analogue** parameter (`lambdaHQIV`), **not** as the classical
  de Bruijn–Newman constant.
- Current formal base (now in Lean): `tempLadderConserved`, `tempLadderRegularized`, `tHQIV`,
  `TempLadderBoundaryData`, `TempLadderForcesLambdaHQIVZero`, finite-window bridge
  `TempLadderFiniteWindowWitness`, and consequence lemmas that derive
  `lambdaHQIV = 0` from explicit hypothesis fields.
- Dimension-template extension now in Lean: normalized shell weights `dimShellWeight` with proved
  finite-range conservation (`tempLadderConserved_dimShellWeight`) and named specializations for
  `R1, R2, R3, R4, R8`.
- Combinatorics constructors now in Lean for the same dimensions:
  `shellCombinatoricWays_{R1,R2,R3,R4,R8}` (stars-and-bars), with `R3` linked to
  `latticeSimplexCount` via `2 * ways_R3 = latticeSimplexCount`.
- Not claimed: no theorem about classical RH or classical `Λ`; Tao–Rodgers remains motivational analogy only.

### S³ / spatial slice — proved rapidity vs “correct ray” (where we are headed)

The narrative is: on the **spatial slice** (often modeled as simply connected **`Σ³`**, and concretely as **`S³`** when you want compactness / spherical harmonics), the **same** rapidity object that already appears in the **lattice zeta phase** should **point directly at** the **right discrete ray** (axis / marginal “prime” steps vs composite angular directions at large `m`), so you are not reduced to searching every ray up to \(\sqrt{m}\)-scale heuristics.

**Already proved in Lean (ℝ / shell-index layer, not yet a manifold `S³` → `Fin n` ray theorem):**

- **`φ·t` = `timeAngle`:** `Hqiv.Geometry.latticeRapidity_eq_timeAngle` (`SpatialSliceRapidityScaffold`) — lattice rapidity is the same real as the HQVM horizon term.
- **Zeta phase channel:** `zetaHQIVTerm` uses `φ * t * delta_theta_prime (m : ℝ)` (`OctonionicZeta`); summability + norm bounds for `Re s > 1` are proved under the usual detuning hypotheses.
- **Lean-wired polar identity:** `RapidityZetaPhaseBridge.lean` proves the phase factor is **`cexp (I * polarAngleFromRapidity φ t m)`** (same data as the geometry spiral scaffold), and `OMaxwellAlgebraSeed.delta_theta_prime_eq_arctan_mul_pi_div_two` fixes the scale as **`arctan · (π/2)`** — not **`2/π`**.
- **`timeAngle` calculus:** `HQVMetric` (monotonicity in `t`, first period, `timeAngle ∈ [0, twoPi]` on the first period, etc.) — real-analytic **control** of the rapidity parameter, still **not** a statement that `φ·t` **equals** a chosen geodesic ray angle on `S³`.

**Discrete ray / shell bookkeeping (proved combinatorics / geometry):** `LatticeFirstQuadrantEdgeCount`, `Lattice3DAxisPrimeStep` (marginal `dim × 2` counts; axis steps in `ℤ³`), `LatticePointMaxAbsShells`, `EuclideanBallHorizontalSlice` (slice = disk).

**Open (the step you are aiming for):** a **theorem-shaped bundle** (or `Prop` bridge with a proof roadmap) that, on a chosen **Riemannian** `S³` (or charted region of `Σ³`), the **rapidity** / `delta_theta_prime` combination **factors through** or **agrees with** a **canonical** map from shell `m` to a **unit tangent direction** (ray) on the slice — so “rapidity points to the correct ray” becomes **provable** rather than design prose alone. **Design intent** is documented under `LatticeContinuumRapidityCoincidence` in `SpatialSliceRapidityScaffold.lean`.

## 0. Anchors already in the library (use these names)

| Idea | Lean reality |
|------|----------------|
| **Euclidean spatial slice + Lebesgue shells** | `Hqiv.Geometry.SpatialSliceEuclidean3`, `euclideanHorizonShell`, `ShellFamilyPairwiseDisjoint_euclideanHorizonShell`, `measurableSet_euclideanHorizonShell`, `volume_euclideanHorizonShell_lt_top`, `euclideanShellVolumeReal`, `spatialSliceToSpacetimeCoords`, `spacetimeThinSlice` (`SpatialSliceManifold.lean`) |
| **Discrete lattice-point shells (L∞ / max-abs on `ℤ³`)** | `maxNatAbsCoord`, `latticeMaxAbsShell`, `latticeMaxAbsShell_disjoint_of_ne`, `latticeMaxAbsShell_zero`, `maxNatAbsCoord_eq_zero_iff` (`LatticePointMaxAbsShells.lean`) — same nested-shell idea as Euclidean annuli, different norm |
| **Euclidean ball ∩ coordinate plane = planar disk** | `joinThirdCoordinate`, `planarHead`, `mem_closedBall_joinThirdCoordinate_iff`, `closedBall_inter_coordPlane_eq_image_slice` plus axis-generalized `coordPlaneIsometry`, `joinCoordinateSlice`, `mem_closedBall_joinCoordinateSlice_iff`, `closedBall_inter_coordPlane_k_eq_image_slice` (`EuclideanBallHorizontalSlice.lean`) |
| **`π` baseline vs lattice/model defect (slice area)** | `piSliceAreaBaseline`, `sliceAreaDefect`, `observedArea_eq_piBaseline_add_sliceAreaDefect`, `sliceAreaDefect_eq_zero_iff`, and shell-indexed `piSliceAreaBaselineAt`, `sliceAreaDefectAt` (+ nonneg/sqrt-radius lemmas). |
| **Slice ↔ `Fin 4` chart ↔ `deltaE_geometricModel` inverse** | `spacetimeCoordsEquiv_spacetimeOfCoords`, `mem_spacetimeThinSlice_iff`, `rVolFromGeometricModelTarget`, `deltaE_geometricModel_rVolFromGeometricModelTarget_eq`, `deltaE_geometricModel_rVolFromDeltaE_eq`, `deltaE_geometricModel_geometricScalarSlotFromShellVolume_eq_deltaE`, `agreesWithCombinatorialDeltaE_deltaE_geometricModel_of_shellVolume_matches_rVol` (`SpatialSliceContinuumBridge.lean`) |
| Discrete shell sum / rapidity phase | `Hqiv.Physics.zeta_HQIV`, `Hqiv.Physics.zetaHQIVTerm` |
| Zeta phase **=** geometry polar angle (proved) | `zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity`, `zetaHQIVTerm_cexp_eq_cexp_polarAngleFromRapidity`, `zetaHQIVTerm_eq_effCorrected_mul_cexp_polarAngleFromRapidity` (`RapidityZetaPhaseBridge.lean`) |
| Tipping angle **=** `arctan · (π/2)` (proved, typo discipline) | `Hqiv.delta_theta_prime_eq_arctan_mul_pi_div_two` (`OMaxwellAlgebraSeed.lean`; uses `horizonQuarterPeriod_eq_pi_div_two`) |
| No-phase / δ_E phase variants on the same ladder | `Hqiv.Physics.zetaR1_latticeTerm`, `Hqiv.Physics.zetaR1_latticeTerm_deltaE` (`Hqiv.deltaE` from `OctonionicLightCone`) |
| Global detuning in the **denominator** of `effCorrected` | `Hqiv.Physics.delta_auxiliary_phi_per_shell`, `Hqiv.Physics.GlobalDetuningHypothesis` |
| Maxwell tipping angle (different channel from combinatorial `deltaE`) | `Hqiv.Physics.delta_theta_prime` (`OMaxwellAlgebraSeed`) |
| Fano mod‑7 partition / next shell jump | `zeta_HQIV_eq_sum_Fano_residue_classes`, `next_lattice_prime`, `exists_fano_vertex_same_residue_mod_seven` |
| Honest scope limits | Module doc in `DivisionAlgebraZetaScaffold.lean` |
| Spatial slice + shell sets + contour placeholder | `Hqiv.Geometry.ShellFamily`, `PhiContourFunctional`, `SpatialRapidityProbe`, `LatticeContinuumRapidityCoincidence` (`SpatialSliceRapidityScaffold.lean`) |
| Combinatorial vs geometric `δ_E` bridge | `Hqiv.Geometry.agreesWithCombinatorialDeltaE`, `GeometricScalarCurvatureSlot`, `deltaE_geometricModel`, `agreesWithCombinatorialDeltaE_geometricModel_iff` |
| Integrated scalar-curvature input variant | `Hqiv.Geometry.IntegratedScalarCurvatureSlot`, `deltaE_geometricModel_fromIntegratedScalarCurvature` (simp lift to `deltaE_geometricModel`) |
| Zeta phase with arbitrary slot | `Hqiv.Physics.zetaR1_latticeTerm_deltaESlot` + summability; matches `deltaE` / geometric model when hypotheses hold |
| Step-wise (monogamic) rapidity version | `Hqiv.Physics.zetaR1_latticeTerm_monogamic3DRamanujanTerm` and `zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_zetaR1_latticeTerm_deltaESlot_of_const_phi_t` |
| Fano period scaffold | `fanoContourPeriodSum`, `FanoPeriodRapidityCoincidence` (equality is **assumed** in the structure, not proved from `π₁ = 0`) |
| Period map lemma (rapidity as pairing) | `FanoPeriodRapidityCoincidence.phi_t_eq_periodMap_pairing` (re-labelling of `phi_t_eq_fanoContourPeriodSum`) |
| “Hodge class” probe alias | `Hqiv.Geometry.HodgeClassProbe` / `FanoPeriodRapidityCoincidence.phi_t_eq_hodgeClassProbe` |
| Hodge probe **+** zeta phase (same `φ,t` hypothesis) | `HodgeClassProbe_eq_mul_of_FanoPeriodRapidityCoincidence`, `zetaHQIVTerm_eq_eff_mul_cexp_polarAngle_of_coincident_rapidity` (`HodgeRapidityZetaBridge.lean`; **not** the Hodge conjecture) |
| Fano zeta strand ↔ algebra cycle tag | `shellResidueFano_of_f_val_add_seven_mul`, `fano_vertex_of_shell_f_val_add_seven_mul` |
| Lattice `φ·t` ↔ HQVM `timeAngle` | `Hqiv.Geometry.latticeRapidity_eq_timeAngle` |
| Fano-indexed cycle skeleton / shell residue | `Hqiv.Algebra.FanoIndexedCycles`, `shellResidueFano`, `canonicalFanoCycles` (`CycleHodgeProbeScaffold.lean`) |
| Physics ↔ algebra same `m % 7` tag | `Hqiv.Physics.fano_vertex_of_shell_eq_algebra_shellResidueFano` |
| ℂ critical line + ℚ tilt + 𝕆 Fano template (probe bundle) | `criticalLineReHalf`, `rationalTilt`, `norm_zetaR1_latticeTerm_eq_zpow_re_half`, `fano_prime_pred_eq_val`, `CriticalLineRationalFanoOctonionProbe` (`DivisionAlgebraZetaScaffold`) — see [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md) §7 |
| Lattice next-“prime” generator (ℝ¹ only) | `decompose_to_fano_moduli`, `decompose_last_shell`, `spherePackingAtShell`, `rapidity_effect_on_sphere`, `next_prime_generator` (`LatticeNextPrimeGenerator`) — **scaffold only**: composed pipeline is **not** a working end-to-end algorithm; **not** classical primes; reuses `next_lattice_prime` + `effCorrected` + Fano weights |
| Candidate shell ↔ defect profile bridge | `sliceDefectProfileAtZ`, `absSliceDefectProfileAtZ`, `nextShellDefectCandidate`, `nextShellDefectValue`, `IsGlobalPeak`, `IsGlobalAbsPeak`, `IsWindowPeak`, `IsWindowAbsPeak`, `isWindowAbsPeak_iff_range`, `candidate_isWindowAbsPeak_of_rangeHyp` (window certification only; no global-optimality theorem). |

## 1. Geometric layer: from `m : ℕ` to a Riemannian 3-manifold

**Goal:** Define a class of **spatial slices** (e.g. oriented Riemannian 3-manifold `Σ`) and a map `shellIndex : Σ → ℕ` or a family of compact regions `U_m ⋐ Σ` so that **combinatorial** shell counting remains `ℕ`-indexed while **geometry** enters through scalars.

**Suggested Mathlib stack:** `Mathlib.Geometry.Manifold.*`, volume forms, integration on manifolds (`MeasureTheory.Integral.*` on charts). HQIV would add a **structure** bundling:

- a Riemannian metric `g` on `Σ` (or on an open subset used for the construction);
- optional **compact** exhaustions or shells `U_m` with `Vol(U_m)` controlled;
- hypotheses **as explicit `Prop`s** (e.g. simply connected, bounded geometry), not hidden in comments.

**Milestone A (minimal):** Prove lemmas of the form “if `deltaE_geom m` is defined as `∫_{U_m} R √g d³x` with fixed normalization, then under stated bounds, `deltaE_geom m` is finite / comparable to combinatorial `Hqiv.deltaE m` **only if** you add a **bridge assumption** equating discrete and continuum normalizations.”

**Milestone B:** Replace or **parameterize** the scalar slot in `effCorrected` / zeta so that `δ` or a phase prefactor depends on `deltaE_geom m` *by definition* in a **new** module (do not silently redefine `Hqiv.deltaE`).

## 2. Rapidity `φ·t` as a path functional

**Goal:** Turn `φ * t : ℝ` into `∫_γ φ(x) ds` along **null** or **prescribed** curves in a Lorentzian extension, or along spatial curves in `Σ` for a fixed gauge.

**Suggested path:**

- Use existing **continuum chart** bridges (`ContinuumSpacetimeChart`, `HQVM` docs) only as **scaffolding**; add a **new** definition `phi_t_along (γ : Path Σ) (φ : ...) : ℝ` once `φ` is a field, not a single real.
- **Milestone C:** Prove **independence** or **gauge** lemmas only under explicit hypotheses (Gordon-type or affine parameter choices)—otherwise state them as `Prop` bundles in `ASSUMPTIONS.md`.

**Connection to current code:** Until Milestone C exists, `phi_t_cum` / `timeAngle` remain the **formal** objects; any “global integral” story is **documentation + future defs**.

## 3. `next_lattice_prime` vs geometry

**Current Lean meaning:** `next_lattice_prime` is **`Nat.find`** on a **ratio threshold** in `effCorrected`; uniqueness is **minimality of the witness**, not a theorem from scalar curvature positivity.

**Roadmap:**

- **Milestone D:** Show `effCorrected` **strictly increasing** in `m` at fixed admissible `δ` is already in `GlobalDetuning` (`effCorrected_strictMono_nat`); relate **threshold crossings** to **geometric** data only after Milestones A–B define `eff` from `g`.
- **Milestone E (optional):** If `eff_geom m` is monotone in `m` by construction, re-prove an analogue of `exists_next_shell_eff_ratio_ge` for `eff_geom` and connect to `next_lattice_prime` via a **comparison lemma** (requires a clear definition of two indexings).

## 4. Number theory: modular forms / L-functions (long horizon)

**Dedicated ladder (M0–M5, BSD thread):** [MODULAR_FORMS_LADDER.md](./MODULAR_FORMS_LADDER.md). **BSD bridge (ℝⁿ + Ramanujan-type curvature):** [BSD_RN_RAMANUJAN_BRIDGE.md](./BSD_RN_RAMANUJAN_BRIDGE.md). **Formal standard:** [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md).

**Goal (paper-level):** An L-function whose coefficients encode Fano-line / shell data, with a functional equation.

**Formal reality:** Mathlib has modular forms and L-series in places, but **none** of it is wired to `zeta_HQIV`. Treat this as a **separate project**:

- **Milestone F (scaffold complete):** A precise periodic/slot coefficient scaffold is now present in
  `SpatialSliceRapidityScaffold.lean` (class-local k-sphere domains + `1/k`-spiral slots).
  Remaining F-work is to freeze one canonical coefficient extractor `a_m` into a dedicated
  number-theory module.
- **Milestone G (execution probe complete; theorem-level open):** Script-level Ω/periodicity probe and
  arity-aware search are implemented in `scripts/factor_from_curvature.py`.
  **Still open:** theorem-level analytic continuation / functional equation in Lean.

**Do not** claim that `DivisionAlgebraZetaScaffold` “is a modular form theorem” yet:
current status is **F/G probe scaffolding + execution pipeline**, not a proved modularity theorem.

## 5. Suggested module split (when work starts)

| Module (suggested name) | Purpose |
|-------------------------|---------|
| `SpatialSliceHypothesis` (proposed; not yet in tree) | Bundles `Σ`, `g`, optional `U_m`, measurability, finiteness of curvature integrals |
| `ZetaGeomBridge` (proposed; not yet in tree) | Compares combinatorial `deltaE` / `effCorrected` to geometric integrals **under explicit bridge props** |
| `HQIVDirichletScaffold` (proposed optional split; current anchor is `Hqiv.Physics.HQIVDirichletModularScaffold`) | Defines coefficient sequence from shell data; states (does not prove) modularity |

## 5b. Post-audit cross-thread roadmap (SAT/ATSP/oracle bridge)

The April 2026 corpus audit surfaced a now-formalized bridge that this roadmap should actively use: SAT rapidity geometric certificates already feed arithmetic/root-envelope controls, and the rapidity-polar oracle already has theorem-level soundness links.

### Already available in Lean (reuse now)

- **Geometry certificate -> arithmetic envelope path** (`SATRapidityPlaneBridge`):
  - `ribbon_cover_collapse`
  - `ribbon_cover_collapse_hasPolynomialResidualBudget`
  - `ribbon_cover_collapse_implies_nat_root_envelope`
- **Direction-selection packaging path** (`SATRapidityPlaneBridge`, `SATRapidityGapBridge`):
  - `direction_selection_with_plane_witness_implies_gap_bridge`
  - `sat_rapidity_gap_bridge_implies_geometric_collapse`
- **Factor-oracle soundness chain** (`RapidityPolarFactorOracle`):
  - `factorPair_from_3spiral_correct`
  - `pickFromCandidates_sound`
  - `chart_bridge_and_picker_sound`
  - `factorTree_prod_eq`

### Updated immediate milestones (disjoint-area leverage)

1. **M-SAT-Envelope:** expose a small bridge record in docs/prose that treats ribbon-cover certificates as admissible search-envelope hypotheses for the ATSP envelope modules (`ATSPWorstCaseCertified`), without claiming an unconditional reduction.
2. **M-Oracle-Cert:** add a script-side certification payload (fields matching the hypotheses of `pickFromCandidates_sound`) so empirical runs can emit Lean-checkable witness data.
3. **M-Shared-Budget:** document one reusable transport-budget slot (`shellIndexFromTimeAngle`, `accessibleModeBudgetUpToPhiTime`) as a cross-module schedule input, so geometry/SAT/QFT ladders stop reintroducing parallel budget notions.
4. **M-Bridge-Ledger:** maintain a single hypothesis ledger row in `ASSUMPTIONS.md` for every cross-thread bridge theorem used outside its native file (prevents drift between roadmap prose and theorem contracts).

### Progress update (python + Lean, current branch)

- `scripts/geometric_factorization_solver.py` now emits `one_step_pick_certificate`:
  - in-order picked divisor `d` (when found),
  - `is_nontrivial`, `divides`, `pair_product_ok`,
  - candidate index + `(step, seed_idx)` source metadata.
- `RapidityPolarFactorOracle.lean` now includes `Bridge.OneStepPickCertificate` with:
  - `OneStepPickCertificate.sound`
  - `OneStepPickCertificate.pair_product`
- `RapidityPolarFactorOracle.lean` now also carries a certified constant scan bound for the direct candidate pass:
  - `allCandidates_length = 7`,
  - filtered scan bound `factorPair_candidate_scan_le_budget`,
  - packaged O(1)-style statement `factorPair_from_3spiral_is_O1`.
- The one-step bridge scan now has a generic + specialized complexity certificate:
  - generic `Bridge.firstValidDivisor_scanCost_le_length` (scan cost bounded by candidate-list length),
  - specialized `Bridge.pickFromCandidates_scanCost_le_seven` on the current curvature-candidate family.
- `scripts/generalized_geometric_oracle.py` now normalizes and forwards this bridge object in SAT pipelines:
  - top-level `factor_pick_bridge`,
  - SAT-mode default packaging under `sat_bridge_certificates.one_step_pick`.
- Factorization search formulation now better matches SAT/ATSP execution shape:
  - candidate generation via rapidity register seeds,
  - local bit-flip neighborhoods,
  - per-step prune ledger,
  - register width tied to `sqrt(n)` search window (`bit_length` of the bound),
  - recursive cofactor peeling enabled in script mode (`--prime-factorization`) with trace + product verification.
- Benchmark checkpoint (increase bit length until 10s):
  - legacy trial-division-driven loop hit break near `~60` bits;
  - refactored register/flip/prune loop did not hit 10s up to `512` bits in sampled probable-prime runs (`max_steps=120`).
- Net effect: `M-Oracle-Cert` moved from pure roadmap intent to an executable handoff path between script payloads and Lean theorem targets.

## 6. Maintainer checklist

When any milestone above lands as **proved** lemmas:

1. Add entries to `THEOREMS.md` under new headings (bias toward **cross-cutting** lemmas; see **Proof priority** at top).
2. Add **bridge assumptions** to `ASSUMPTIONS.md` if you introduce `Prop` records or numeric identifications.
3. Update this file’s **Status snapshot** (proved vs actively sought) so “what’s good / what’s left” stays honest.
4. Shorten or mark roadmap subsections **done** with a link to the module; sync [HODGE_HQIV_NARRATIVE.md](./HODGE_HQIV_NARRATIVE.md) if the Hodge-analogy thread moves.

## 7. Immediate execution plan (current branch)

1. Produce real shell samples (neutrino/quark standing-wave channels) in the script input format:
   `[{m, theta, value}, ...]`.
2. Run `scripts/fano_slice_fft_probe.py` across threshold sweeps and windows; record stable retained slices and dominant periods.
3. Build defect profiles from those channels and run `scripts/search_slice_defect_peak.py` to emit `Finset.range N` witness JSON.
4. Promote stable empirical statements to Lean hypotheses and instantiate `candidate_isWindowAbsPeak_of_rangeHyp` on concrete windows.
5. Extend `TempLadderBoundaryData` from abstract `Prop` slots to checkable finite-window conditions (partial
   conservation sums, phase-lock inequalities), then prove specialized `lambdaHQIV_eq_zero` instances.
