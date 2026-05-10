# Publication Audit (Zenodo Prep)

Date: 2026-04-30

## Scope

- Manuscript: `papers/hqiv_rapidity_manifold_so8_closure.tex`
- Appendix: `papers/so8_closure_full_appendix.tex`
- Lean proof modules tied to verification map / closure package
- Exact symbolic certificate artifacts:
  - `artifacts/so8_symbolic_certificate.json`
  - `artifacts/so4_symbolic_certificate.json`

## Current checks

- **Inventory + checksums**
  - `python3 release/zenodo/build_zenodo_bundle.py`
  - Result: required missing files = `0`
  - Output:
    - `release/zenodo/publication_inventory.json`
    - `release/zenodo/SHA256SUMS.txt`
    - `release/zenodo/MISSING_REQUIRED.txt`

- **Lean target audit** (2026-04-30, ~66 min total for `HQIVSO8Closure` attempt)
  - `lake build HQIVWitnesses` -> **pass**
  - `lake build HQIVRhFourierLift` -> **pass**
  - `lake build HQIVPlastic` -> **pass**
  - `lake build HQIVSO8Closure` -> **fail** (`Hqiv/GeneratorsLieClosure.lean`: missing `So8CoordMatrix.so8CoordMatrix_transpose_mul_self`, `mulVec_apply`; tactic/rewrite failures; `unknown constant 'Hqiv.lieBracket_in_span'`)
  - Standalone rerun (same repo state): `lake build HQIVSO8Closure` ~68 min, exit **1**; full compiler log: `/tmp/hqiv_HQIVSO8Closure.log`

- **Publication-critical objects found**
  - `papers/hqiv_rapidity_manifold_so8_closure.tex`
  - `papers/hqiv_rapidity_manifold_so8_closure.pdf`
  - `papers/so8_closure_full_appendix.tex`
  - `papers/so8_closure_full_appendix.pdf` (canonical build output; avoid stale root copy if present)
  - `artifacts/so8_symbolic_certificate.json`
  - `artifacts/so4_symbolic_certificate.json`

## Zenodo metadata status

- Root metadata draft added: `.zenodo.json`
- Working draft copy: `release/zenodo/.zenodo.json`
- Required manual edits before release:
  - creator names/affiliations/ORCIDs
  - final description
  - related manuscript DOI/URL
  - final release version tag

## Remaining button-down items

1. **Repair `HQIVSO8Closure`**: align `GeneratorsLieClosure.lean` with current `So8CoordMatrix` / matrix API and restore `lieBracket_in_span` in scope.
2. Freeze manuscript + appendix PDF generation command(s) in a reproducibility note.
3. Fill final `.zenodo.json` metadata fields.
4. Create final upload bundle from `publication_inventory.json` paths.
