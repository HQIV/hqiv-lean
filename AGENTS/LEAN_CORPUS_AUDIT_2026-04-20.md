# Lean Corpus -> Markdown Audit (2026-04-20)

This pass audits the `AGENTS` markdown corpus against the current Lean tree (`Hqiv/**/*.lean`) with two goals:

1. ensure references are accurate (no stale pseudo-modules presented as existing), and
2. surface cross-thread insights that are already in Lean but under-documented in the prose roadmap layer.

## Scope and method

- Recursively scanned `AGENTS/**/*.md` for Lean symbol references (`Hqiv.*`) and `.lean` module mentions.
- Classified symbol hits as:
  - **exact**: fully-qualified symbol appears in Lean text;
  - **namespace-drift**: fully-qualified token not found, but terminal identifier exists (usually open-namespace/docs shorthand);
  - **hard-missing**: neither full token nor terminal identifier exists.
- Cross-checked high-value geometry/SAT/rapidity files now active in branch context:
  - `Hqiv/Geometry/RapidityPolarFactorOracle.lean`
  - `Hqiv/Geometry/SATRapidityPlaneBridge.lean`
  - `Hqiv/Geometry/SATRapidityGapBridge.lean`
  - `Hqiv/Geometry/SATRapidityDirectionSelection.lean`

## Accuracy results

### Hard-missing references found

- `AGENTS/MANIFOLD_ZETA_ROADMAP.md`
  - `Hqiv.Geometry.SpatialSliceHypothesis`
  - `Hqiv.Physics.ZetaGeomBridge`
  - `Hqiv.NumberTheory.HQIVDirichletScaffold`
- `AGENTS/archive/OCTONION_SPHERE_PATCH.md`
  - `Hqiv.Algebra.OctonionPatchQuantum` (legacy removed namespace)

### Fixes applied in this audit

- `AGENTS/MANIFOLD_ZETA_ROADMAP.md`
  - Converted those rows to explicit **proposed/not-yet-in-tree** module names.
  - Added the current in-tree anchor: `Hqiv.Physics.HQIVDirichletModularScaffold`.
- `AGENTS/archive/OCTONION_SPHERE_PATCH.md`
  - Reworded retired heading to avoid presenting removed namespace as active.
- `AGENTS/README.md`
  - Disambiguated module paths with explicit file locations:
    - `Hqiv/OctonionLeftMultiplication.lean`
    - `Hqiv/Physics/Action.lean`
- `AGENTS/THEOREMS.md`
  - Added missing theorem rows for SAT rapidity collapse/ribbon-cover packaging and `RapidityPolarFactorOracle` soundness chain.

## Namespace-drift observations (non-blocking, but worth hygiene passes)

- Most drift occurs in `AGENTS/THEOREMS.md`, where entries often use `Hqiv.*` prefixes while Lean statements are cited by shorter/open names in the defining modules.
- This is mostly stylistic and currently does **not** indicate theorem removal.
- Suggested cleanup strategy: when touching a section, prefer one of:
  - full name exactly as exported in module text, or
  - short name plus explicit module pointer in the same table row.

## Newly recorded cross-thread insights (Lean-backed)

These are areas where formal content already supports stronger cross-references than currently emphasized.

1. **SAT collapse -> arithmetic envelope bridge is now explicit**
   - `SATRapidityPlaneBridge` already packages a full route from direction/plane certificates to:
     - geometric collapse (`ribbon_cover_collapse`), then
     - polynomial residual budget (`ribbon_cover_collapse_hasPolynomialResidualBudget`), then
     - root-envelope bound (`ribbon_cover_collapse_implies_nat_root_envelope`).
   - This should be cited in SAT + manifold roadmap prose as a formal bridge from geometry certificates to arithmetic search pruning.

2. **Rapidity-polar factor oracle has a theorem-level soundness chain (not just script narrative)**
   - `RapidityPolarFactorOracle` proves factor-product correctness and divisor-sound candidate picking under explicit hypotheses:
     - `factorPair_from_3spiral_correct`
     - `pickFromCandidates_sound`
     - `chart_bridge_and_picker_sound`
     - `factorTree_prod_eq`
   - This supports a stronger documentation claim that the oracle layer is theorem-driven with explicit assumptions, not just heuristic selection language.

3. **QFT patch locality and light-cone budget bridge can be tied more directly to geometry docs**
   - `THEOREMS.md` already captures `PatchQFTBridge` and `LightConeMaxwellQFTBridge` links (`shellIndexFromTimeAngle`, `accessibleModeBudgetUpToPhiTime`), but manifold and SAT roadmaps could cite this as a reusable transport budget interface for cross-domain arguments.

4. **Dirichlet/modular scaffold naming should stay anchored on current module reality**
   - Current executable formal anchor is `Hqiv.Physics.HQIVDirichletModularScaffold` (plus `HQIVLSeriesAnalytic`), with speculative split modules labeled as proposals.
   - This avoids accidental overclaim of a non-existent `Hqiv.NumberTheory` namespace.

## Recommended next audit slice

- Expand this process to root-level docs (`README.md`, `README_AlgebraExtension.md`) with the same exact/proposed/removed labeling convention.
- Add a tiny “symbol citation style” note to `AGENTS/README.md` maintainer section so future rows stay machine-checkable.

## Follow-up progress (same day)

- `AGENTS/MANIFOLD_ZETA_ROADMAP.md` now includes a dedicated post-audit cross-thread roadmap section wiring:
  - SAT rapidity collapse certificates,
  - arithmetic/root-envelope bridge targets,
  - rapidity-polar oracle soundness milestones.
- `AGENTS/ATSP_ALGORITHM_STATUS.md` now includes a post-audit roadmap section with concrete next implementation checkpoints (bridge contract, certificate payloads, envelope handshake, budget unification).
- Python/Lean bridge progress landed:
  - `scripts/geometric_factorization_solver.py` emits `one_step_pick_certificate`,
  - `Hqiv/Geometry/RapidityPolarFactorOracle.lean` adds `Bridge.OneStepPickCertificate` plus soundness/pair-product theorems.
  - `scripts/generalized_geometric_oracle.py` now forwards a normalized SAT-facing bridge object (`factor_pick_bridge`, `sat_bridge_certificates.one_step_pick`) with Lean target + theorem metadata.
  - Complexity certification added in Lean for direct rapidity factor scan:
    `allCandidates_length`, `factorPair_candidate_scan_le_budget`, `factorPair_from_3spiral_is_O1` (constant budget `≤ 7`).

## Addendum (2026-05-09)

- `lakefile.toml` now includes **`HQIVMeaningfulPhysics`** (import-closure globs from `scripts/physics_lib_globs.py`) and **`HQIVStory`** (single-root `HQIVStory` glob) so CI targets match the documented commands.
- **`AGENTS/README.md`**, **`README.md`**, **`AGENTS/THEOREMS.md`**, and companion **`papers/`** sources were aligned with the split between default **`HQIVLEAN`**, optional **`HQIVStrongColorSu3Certificate`**, and heavy **`HQIVSO8Closure`**.
