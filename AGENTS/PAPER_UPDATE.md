# Paper update (local working note — not versioned)

This file tracks how to align the **HQIV preprint** in the sibling tree (`HQIV/paper/main.tex`) with the **current Lean derivation** in this repository (`HQIV_LEAN`). For the canonical **proved / trust** index, prefer [`THEOREMS.md`](./THEOREMS.md) and [`ASSUMPTIONS.md`](./ASSUMPTIONS.md); this note is a working **source map** for editors.

**Target manuscript (external to this repo):** `../HQIV/paper/main.tex` (relative to this repo root), i.e. the canonical paper sources beside `HQIV_LEAN` under your `HQIV` checkout. Adjust the path if your layout differs.

---

## Source map (read before editing `main.tex`)

### HQV metric — better treatment

- [`Hqiv/Geometry/HQVMetric.lean`](../Hqiv/Geometry/HQVMetric.lean) — core metric / HQVM dictionary.
- [`Hqiv/Geometry/ContinuumSpacetimeChart.lean`](../Hqiv/Geometry/ContinuumSpacetimeChart.lean) — continuum chart bridge.
- [`Hqiv/Geometry/HQVMPerturbations.lean`](../Hqiv/Geometry/HQVMPerturbations.lean) — perturbations on the HQVM side.

### Bottom-up mass spectrum

- [`Hqiv/Physics/HarmonicLadderMass.lean`](../Hqiv/Physics/HarmonicLadderMass.lean)
- [`Hqiv/Physics/BoundStates.lean`](../Hqiv/Physics/BoundStates.lean)
- [`Hqiv/Physics/DerivedNucleonMass.lean`](../Hqiv/Physics/DerivedNucleonMass.lean)
- [`Hqiv/Physics/QuarkMetaResonance.lean`](../Hqiv/Physics/QuarkMetaResonance.lean)

Narrative in `main.tex` should follow the **order and naming** used in these modules (shell/ladder → resonances → nucleon anchor, etc.), not an older prose-only ordering.

### Strong color (`su(3)` triplet chart)

- Chart + carrier embed API: [`Hqiv/Physics/StrongColorSu3ChartClosure.lean`](../Hqiv/Physics/StrongColorSu3ChartClosure.lean), [`Hqiv/Physics/StrongColorCarrierClosure.lean`](../Hqiv/Physics/StrongColorCarrierClosure.lean), scaffold [`Hqiv/Physics/QuarkColorCarrierGaugeScaffold.lean`](../Hqiv/Physics/QuarkColorCarrierGaugeScaffold.lean).
- Optional `f^{abc}` simp certificate (not in default `HQIVLEAN`): `lake build HQIVStrongColorSu3Certificate`; regenerate `scripts/gen_strong_color_su3_f_simp.py`. When mirroring into external `main.tex`, distinguish **proved chart scaffolding** from the still-open **full eight-generator Lie law** (see `AGENTS/THEOREMS.md` strong-color table).

### QM / QFT — Lean vs prose bridge

- Long-form prose + OSHoracle pipeline: [`papers/paper/octonion_lightcone_to_oshoracle.tex`](../papers/paper/octonion_lightcone_to_oshoracle.tex)
- Lean (representative):
  - [`Hqiv/QuantumMechanics/HorizonLimitedRenormLocality.lean`](../Hqiv/QuantumMechanics/HorizonLimitedRenormLocality.lean)
  - [`Hqiv/QuantumMechanics/ContinuumManyBodyQFTScaffold.lean`](../Hqiv/QuantumMechanics/ContinuumManyBodyQFTScaffold.lean)
  - Broader: `Hqiv/QuantumMechanics/*.lean` — distinguish **proved** vs **scaffold** when mirroring into `main.tex`.

### Quantum gates — sim / prune (workhorse note)

- Local ATSP / oracle status (also gitignored): [`AGENTS/ATSP_ALGORITHM_STATUS.md`](ATSP_ALGORITHM_STATUS.md) — use this to decide what to **lift into `main.tex`**: gate simulation, pruning rounds, benchmark harnesses, and how they relate to the discrete/light-cone story. Cross-reference section headings you plan to add or rewrite in the preprint.

---

## Section checklist for `HQIV/paper/main.tex`

Use this as a scratch checklist while editing the external `main.tex`.

- [ ] **HQV metric** — definitions, continuum bridge, perturbations (aligned with `HQVMetric` / chart / perturbation modules).
- [ ] **Mass spectrum** — bottom-up shell/ladder → hadrons/leptons consistent with `HarmonicLadderMass`, `BoundStates`, `DerivedNucleonMass`, `QuarkMetaResonance`.
- [ ] **QM / horizon-limited closure / QFT bridge** — match proved statements in Lean and the narrative in `papers/paper/octonion_lightcone_to_oshoracle.tex`.
- [ ] **Strong color (`su(3)` chart)** — cite only what is in `THEOREMS.md` / `StrongColorSu3ChartClosure`; label the full eight-generator Lie law as open unless a completed `colorSu3LieAlgebra`-style theorem lands in Lean.
- [ ] **Quantum circuits** — simulation + pruning; tie terminology to `ATSP_ALGORITHM_STATUS.md` where the paper discusses oracle-style search and prune pipelines.

---

## Open questions / deltas

- [ ] Where does Zenodo / older preprint text **diverge** from current `Hqiv/Geometry/HQVMetric.lean` (symbols, hypotheses, ordering)?
- [ ] Which mass-route lemmas are **fully proved** vs **schematic** in Lean, and how should `main.tex` label them?
- [ ] Which `octonion_lightcone_to_oshoracle.tex` sections are already “paper-grade” vs still research narrative for `main.tex`?
- [ ] Which ATSP / gate / prune bullets from `ATSP_ALGORITHM_STATUS.md` belong in the main preprint vs supplementary material?
