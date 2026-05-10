# Agent-friendly map (HQIV_LEAN)

This folder is for **AI agents and new contributors** who need orientation without reading the whole Mathlib-sized dependency graph. It stays next to the project `README.md` and is updated when the formal story changes in a material way.

**What’s solid vs still open (living docs):** [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) **§ Status snapshot** (geometry, zeta, scripts, bridges) + **§ Proof priority**; curated names in [THEOREMS.md](./THEOREMS.md); Hodge-thread **§5 + “still open”** in [HODGE_HQIV_NARRATIVE.md](./HODGE_HQIV_NARRATIVE.md); honest gaps in [ASSUMPTIONS.md](./ASSUMPTIONS.md) §9b.

**Millennium / Clay claims:** substantive formal progress toward a Millennium Prize Problem must be **compatible with** [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems); read [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md). HQIV probe scaffolds are **not** automatic solutions.

**Canonical HQIV constants:** $\alpha=3/5$ (`Hqiv.alpha`) and $\gamma=2/5$ (`Hqiv.gamma_HQIV`) are the **only** curvature-imprint and monogamy parameters in this formalism; physical derivation is in the companion HQIV manuscript and Brodie (2026). See [ASSUMPTIONS.md](./ASSUMPTIONS.md) §1b.

| Doc | Contents |
|-----|----------|
| [STORY.md](./STORY.md) | **Router:** Story spine vs textbook defaults; where HQIV intentionally differs; links to audit sources (kept short — not a duplicate of `ASSUMPTIONS` / `THEOREMS`) |
| [THEOREMS.md](./THEOREMS.md) | Curated **theorems and defs with usable outputs** (Lean names, modules, what you get) |
| [ASSUMPTIONS.md](./ASSUMPTIONS.md) | **Honest accounting**: conceptual axioms, Mathlib trust, script data, `sorry`s, bridge assumptions |
| [FUREY_ALIGNMENT_GAP_ANALYSIS.md](./FUREY_ALIGNMENT_GAP_ANALYSIS.md) | **Peg-hole audit**: theorem-backed HQIV anchors vs Furey-style fermion/classification targets; accepted anchor, narrative-only links, and open blockers |
| [FUREY_PROOF_ROADMAP.md](./FUREY_PROOF_ROADMAP.md) | **Furey audit roadmap**: proof-sized paper claims vs repo status (proved / bookkeeping / placeholder / absent); staged Lean targets (complex carrier → Clifford → ideals → three generations); explicit non-goals |
| [LEAN_CORPUS_AUDIT_2026-04-20.md](./LEAN_CORPUS_AUDIT_2026-04-20.md) | Recursive Lean↔markdown audit ledger: stale references fixed, namespace-drift notes, and cross-thread insight opportunities |
| [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) | **Proof path** (not done): 3-manifold / Ricci integrals / path-valued `φ·t` / L-functions vs current `DivisionAlgebraZetaScaffold` anchors |
| [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md) | **Single narrative** threading RH / Yang–Mills / NS / Hodge at **probe** level—**no** claims beyond `THEOREMS.md` |
| [NAVIER_STOKES_HQIV_NARRATIVE.md](./NAVIER_STOKES_HQIV_NARRATIVE.md) | **Paper-level** HQIV vs classical 3D NS / Millennium framing (standing-wave / horizon structure, one possible self-clock state language, `φ·t`, `δ_E`, Fano)—not a Lean PDE result; points to roadmap |
| [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md) | **Ladder** (F0–F5): effective modified fluid (`f`, `g_vac`, `ν_eddy`), plasma ↔ algebra-first O-Maxwell attachment, classical NS limit—same honesty pattern as RH/manifold roadmaps |
| [O_MAXWELL_EIGEN_SHELL_SELECTION.md](./O_MAXWELL_EIGEN_SHELL_SELECTION.md) | **Design:** one lifted O-Maxwell + \(\varphi\); Fano projections for sectors; **target** eigen-shell / standing-wave selection to replace quark shell **tables** (links to `MASS_DERIVATION_ROADMAP.md`) |
| [MAIN_PAPER_FLRW_LEAN_ALIGNMENT.md](./MAIN_PAPER_FLRW_LEAN_ALIGNMENT.md) | **Main paper ↔ Lean:** FLRW/HQVM node claims mapped to proved iff chains (`HQVM_FLRW_PaperAlignment`); suggested **paper-only** rigor edits (`main.tex` not in this repo) |
| [LIGHTCONE_FUNDAMENTALS_DERIVATION_PLAN.md](./LIGHTCONE_FUNDAMENTALS_DERIVATION_PLAN.md) | **Roadmap**: lightcone axioms → kinetic (Boltzmann) → balance laws / modified fluids → linear response → Einstein/emergent → scattering/unitarity → Dirac → information bounds; milestones and honesty (L0–L3) |
| [HQIV_PERTURBATION_THEORY_ROADMAP.md](./HQIV_PERTURBATION_THEORY_ROADMAP.md) | **Perturbation theory**: what is proved vs classical GR; lapse/`phi_of_T`/resolution; links to `HQVMPerturbations`, `HQIVPerturbationScaffold`, Pillar C; milestones P0–P5 |
| [REFACTOR_END_TO_END_PLAN.md](./REFACTOR_END_TO_END_PLAN.md) | **Refactor / cleanup plan:** optional linear `Hqiv.Story` spine (light cone → … → Dojo/Clay wiring); `lake build HQIVStory` — `HQIVLEAN.lean` remains the full superset for now |
| [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md) | **Standard:** proofs toward Millennium problems must satisfy / align with **lean-dojo/LeanMillenniumPrizeProblems**; what “compatible” means for HQIV |
| [MODULAR_FORMS_LADDER.md](./MODULAR_FORMS_LADDER.md) | **Ladder** (M0–M5): modular forms / L-series / BSD thread—long-horizon analytic layer beyond lattice zeta probes |
| [BSD_RN_RAMANUJAN_BRIDGE.md](./BSD_RN_RAMANUJAN_BRIDGE.md) | **BSD strategy:** ℝⁿ + **arbitrary Ramanujan-type curvature** as bridge from HQIV shells to BSD-shaped L-data—**not** a proof |
| [HODGE_HQIV_NARRATIVE.md](./HODGE_HQIV_NARRATIVE.md) | **Paper-level** analogy to the Hodge conjecture (cycles, periods, Fano vs algebraic cycles)—**not** a proof; **§5** lists proved HQIV-internal scaffold wires (`HodgeRapidityZetaBridge`, Fano strand lemmas) |
| [QUANTUM_CHEMISTRY_OUTPUTS.md](./QUANTUM_CHEMISTRY_OUTPUTS.md) | Target output architecture for the Lean+numerical quantum-chemistry stack (foundational → intermediate → user-facing + interoperability + uncertainty policy) |
| [QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md](./QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md) | **Probe-level** quantum-circuit metaphor for `LatticeNextPrimeGenerator` (Fano register, diagonal rapidity, sparse simulation)—**not** Lean complexity or Grover theorems |
| [archive/](./archive/) | Parked SAT/moiré / complexity-adjacent **prose** (see `archive/README.md`); Lean counterparts under `Hqiv/Archive/` — **wired:** `Hqiv/Geometry/SATRapidityAnnulusCircle.lean` imports `OctonionAxisAngles` and exposes the osculating-circle / `π/(2k)` arc in `Plane` (see [THEOREMS.md](./THEOREMS.md) row). |

## Quick table of contents (code areas)

- **Root imports:** `HQIVLEAN.lean` — single entry listing the modules pulled into the full library build; use `HQIVStory.lean` + `Hqiv/Story/Chapter*` for the **linear narrative** spine only.
- **Light cone & combinatorics:** `Hqiv/Geometry/OctonionicLightCone.lean`, `SphericalHarmonicsBridge.lean`
- **Millennium roadmaps (probe scaffolds):** `Hqiv/Geometry/SpatialSliceRapidityScaffold.lean` (shells, rapidity bridge, `deltaE` comparison `Prop`), `Hqiv/Algebra/CycleHodgeProbeScaffold.lean` (Fano-indexed cycle skeleton); see `AGENTS/MANIFOLD_ZETA_ROADMAP.md` §0; modular forms / L-functions / BSD thread: [MODULAR_FORMS_LADDER.md](./MODULAR_FORMS_LADDER.md); formal standards: [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md)
- **Metric / lapse / cosmology bridge:** `Hqiv/Geometry/HQVMetric.lean`, `HQVMPerturbations.lean`, `HQVMCLASSBridge.lean`, `HQVM_FLRW_PaperAlignment.lean`, `UniverseAge.lean`, `Now.lean`
- **Perturbation theory (observer-centric + shell backgrounds):** [HQIV_PERTURBATION_THEORY_ROADMAP.md](./HQIV_PERTURBATION_THEORY_ROADMAP.md), `Hqiv/Physics/HQIVPerturbationScaffold.lean`
- **Modified fluid (effective closure, not NS PDE):** `Hqiv/Physics/HQIVFluidClosureScaffold.lean` (F0–F4: defs, `PlasmaFluidClosureAssumptions`, `CoefficientsTowardClassicalNS`), `hqvmpy/src/pyhqiv/fluid.py`; ladder [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md)
- **Lightcone → fundamentals (pillars A–G scaffold):** `Hqiv/Physics/LightConeFundamentalsPillars.lean`; plan [LIGHTCONE_FUNDAMENTALS_DERIVATION_PLAN.md](./LIGHTCONE_FUNDAMENTALS_DERIVATION_PLAN.md)
- **Auxiliary field / φ ladder:** `Hqiv/Geometry/AuxiliaryField.lean` (+ smeared/rapidity bridge modules as needed)
- **SO(8) / octonions:** `Hqiv/Generators*.lean`, `Hqiv/OctonionLeftMultiplication.lean`, `SO8Closure.lean`, `Hqiv/Algebra/*`
- **Strong color (`su(3)` triplet chart):** `Hqiv/Physics/QuarkColorCarrierGaugeScaffold.lean`, `StrongColorSu3ChartClosure.lean` (Gell–Mann / `f^{abc}` defs), `StrongColorCarrierClosure.lean` (`colorGellMannEmbed`, chart–carrier Lie bridge); optional heavy `@[simp]` `f^{abc}` atoms: `lake build HQIVStrongColorSu3Certificate` (`StrongColorSu3fStructureSimp.lean`, regenerated by `scripts/gen_strong_color_su3_f_simp.py`)
- **Physics unification & forces:** `Hqiv/Physics/SM_GR_Unification.lean`, `GRFromMaxwell.lean`, `Forces.lean`, `Hqiv/Physics/Action.lean`, `OMaxwellAlgebraSeed.lean`, `ModifiedMaxwell.lean`, `PromotedOMaxwell.lean`, `Baryogenesis.lean`
- **Fano detuning spectral spine:** `Hqiv/Physics/FanoLine.lean`, `FanoOmaxwellSpectrum.lean`, `ModalFrequencyHorizon.lean`, `FanoDetuningFirstOrder.lean`, `FanoTrialityDetuningScaffold.lean`, `HyperchargePathBarrierScaffold.lean`, `TrialityRapidityWellEquivalence.lean`
- **QM / QFT bridges:** `Hqiv/QuantumMechanics/*` (e.g. `HorizonLimitedQM_QFT_Closure.lean`, `HorizonLimitedRenormLocality.lean`); finite **accessible** light-cone patches and **limits** as cutoff grows (not global infinite-dimensional QFT as a prerequisite) — see `Hqiv/Physics/LightConeMaxwellQFTBridge.lean` (`accessibleModeBudgetUpToShell`, `shellIndexFromTimeAngle` / `accessibleModeBudgetUpToPhiTime`, …).
- **Quantum chemistry (canonical):** `Hqiv/QuantumChemistry/*` (finite-site chemistry contracts and outputs; `FiniteSiteQuantumChemistry.lean`, `H2.lean`, `MoleculeOutputs.lean`, `HeliumScaffold.lean`, `AtomicExcitations.lean`, `SlaterScaffold.lean`, `MolecularReactionGate.lean`).
- **Quantum computing / protein hooks:** `Hqiv/QuantumComputing/*`, `Hqiv/ProteinResearch/*`
- **Lattice next-prime generator (classical Lean):** `Hqiv/Physics/LatticeNextPrimeGenerator.lean` — **scaffold only** (composed pipeline is **not** a working end-to-end algorithm; see module doc and [QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md](./QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md) §0); optional circuit narrative: same probe doc; proved QC fragments (`fano_line_probability_mass_invariant`, `HQIVGate` composition): `Hqiv/QuantumComputing/LatticeNextPrimeQCAlgorithm.lean`

## Build targets (what actually compiles)

See `lakefile.toml` (comments at top of the file list every named `lean_lib`). Roughly:

| Target | Role |
|--------|------|
| `HQIVLeptonResonance` | Default `defaultTargets` entry: Fano / lepton detuning cone only (no Triality / SO(8) abstract pack) |
| `HQIVWitnesses` | Minimal witness stack for `scripts/export_witnesses.lean` (fast smoke) |
| `HQIVPhysics` | Geometry + physics + conservations **without** heavy `GeneratorsLieClosureData*` |
| `HQIVLEAN` | Full formal library in the main glob (includes `StrongColorSu3ChartClosure`; **excludes** matrix SO(8) certificate slices and the optional SU(3) simp certificate) |
| `HQIVPaperClaims` | Manuscript appendix cone: growth / causal package + `Hqiv/SO8ClosureSymbolic.lean` (no heavy matrix closure) |
| `HQIVSO8Closure` | Full certified \(\mathfrak{so}(8)\) matrix Lie-closure data + abstract closure |
| `HQIVStrongColorSu3Certificate` | Optional `su(3)` `f^{abc}` `@[simp]` table + `StrongColorSu3LieCertificate` (CI builds this explicitly; not in default `HQIVLEAN` glob) |
| `HQIVStory` | Linear narrative spine (`HQIVStory.lean` + `Hqiv/Story/Chapter*`) |

Use the smallest target that contains the modules you are editing.

## Maintainer note

When you add a **user-facing** formal claim that agents should rely on, add a one-line entry under the right heading in `THEOREMS.md`. When you add **new trust assumptions** (script data, `sorry`, or explicit `Prop` bundles), document them in `ASSUMPTIONS.md`.

**Interactive:** `sim/patch_qft_bridge.html` — browser UI for mode budget, time-angle shell index, Minkowski `patchChartPoint` intervals, and disjoint spatial regions (aligns with `PatchQFTBridge` / `LightConeMaxwellQFTBridge`).
