# Literature: two local structures in liquid water (Li et al. 2026)

**Bib key:** `li2026waterTwoState` in `papers/references.bib`  
**Source:** [Li et al., *Nature Physics* (2026)](https://doi.org/10.1038/s41567-026-03301-8)  
**Status:** bookmark only — **not** an HQIV input, witness, or comparison target.

## What the paper reports

Unsupervised deep learning on TIP4P/Ice molecular dynamics identifies **two distinct, interconverting local structures (A ⇌ B)** in liquid water — molecular-level support for the **two-state water model** tied to the liquid–liquid phase transition (LLPT). Reaction coordinates include local density (ρ_local) and structure indices (PCI, PCII). Near the HDL/LDL boundary, conversion follows a **full-loop pathway with three saddle points**; farther from that boundary, a **semi-loop with one saddle point**. Regime: **deeply supercooled** water (MD), not ambient liquid.

## What does **not** change today

- Gas-phase / diatomic chemistry (spectroscopy, binding charts, Morse wells, VB resonance).
- Atom construction from `Z` alone (Aufbau, Slater, electronegativity).
- Subatomic binding network (`e_bind_from_network`, proton anchor).
- Current ambient liquid water treatment: **one homogeneous bulk** with melt-comparison ρ = 1.

## Conceptual overlap (already in stack)

HQIV already encodes an **ice tetrahedral network vs melt-released liquid** dichotomy:

| HQIV today | Paper analogue |
|------------|----------------|
| Ice Ih, 4 H-bond reference (`ICE_TETRAHEDRAL_CONTACT_REFERENCE`) | Tetrahedral / LDL-like local order |
| `meltComparisonCurvatureDensityFraction` → ρ = 1 liquid | HDL-like opened lattice |
| Cryo (100 K) vs cytosol (310 K) bulk ρ switch | Phase change, not A/B fraction in liquid |

The paper adds a **finer layer inside liquid water** that the stack currently collapses to scalar ρ.

## What could matter later

**Landed (2026-07):** generalized phase diagram engine — Lean ``PhaseDiagramMixture``,
Python ``hqiv_lab/phase_diagram.py``, ``scripts/hqiv_phase_diagram.py``.
Sciortino / Li rows live in ``WATER_LLPT_OBSERVATIONS`` (comparison quarantine only).

**Refinement program:** [WATER_LDL_HDL_REFINEMENT_PROGRAM.md](./WATER_LDL_HDL_REFINEMENT_PROGRAM.md) —
H–O–H angle tiers (109.47° tet vs 104.478° ref vs θ_dyn), thermal clines, nucleation δB,
latent barrier second order, outside-curvature feedback loop.

**Arena (pyhqiv + disregardfiat.tech/#arena):** metrics
``water_phase_diagram_structural_pass_rate``, ``water_metastable_liquid_at_llcp``,
``water_h2o_melt_T_residual_K``, ``water_llcp_observation_distance``,
``thermo_allotrope_phase_residual``; programme problem ``water-anomalies-llpt``;
showcase via ``scripts/export_phase_diagram_showcase.py``.

### 1. Protein solvent participation (highest leverage)

**Modules:** `Hqiv.ProteinResearch.ProteinSolventPhaseGeometry`, `hqiv_lab/protein_solvent_phase.py`

Replace single `aqueousBulkCurvatureAtT` with a **two-population solvent**:

- f_A: tetrahedral-open / lower local ρ (LDL-like)
- f_B: denser, broken symmetry (HDL-like)
- T-dependent fraction; hydrophobic exposure may bias f_A at interfaces

Hooks: `solventCoordinationExcess`, directional register weights, `contact_curvature_weights`.

### 2. Supercooled / anomaly branch in (T, P) phase engine

**Modules:** `scripts/hqiv_thermodynamic_phase_from_tp.py`, `Hqiv.QuantumChemistry.PhaseGeometryDensity`

Extend below 273 K into **metastable liquid** (not only ice Ih solid). Qualitative targets if built:

- Widom-line / compressibility-anomaly correlations
- Loop vs semi-loop reaction topology as sanity check on any two-state partition

No TIP4P or ML reaction coordinates in the HQIV derivation path.

### 3. Material response split for liquid water

**Modules:** `Hqiv.QuantumChemistry.PhaseMaterialResponse`, `scripts/hqiv_phase_material_response.py`

Two-state thermodynamic partition (Anisimov-style, cited in the paper) could weight n, ε_r, η, L_fusion as f_A·prop_A + f_B·prop_B instead of one liquid branch.

## Related stack docs

- [archive/PHASE_GEOMETRY_CURVATURE_DENSITY.md](./archive/PHASE_GEOMETRY_CURVATURE_DENSITY.md) — ρ_curv pipeline
- [CURVATURE_CONTACT_NETWORK.md](./CURVATURE_CONTACT_NETWORK.md) — (T, P) → derived phase
- [HQIVSPINE.md](./HQIVSPINE.md) § chemistry tiers — solvent phase participation (landed); free-energy / mixture gaps (open)

## Anti-patterns

- Do **not** import TIP4P/Ice trajectories, TensorFlow autoencoder weights, or PCI/PCII as fitted inputs.
- Do **not** cite this paper as validation of current ρ_curv or fold-audit numbers.
- Comparison quarantine unchanged: NIST/CRC stay in comparison rows only.
