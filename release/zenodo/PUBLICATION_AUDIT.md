# Publication Audit (Zenodo Prep)

Date: 2026-04-30 (Lean target notes refreshed 2026-05-12)

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

- **Lean target audit**
  - Historical (2026-04-30, ~66 min `HQIVSO8Closure` attempt on an earlier snapshot): **fail** with missing `so8CoordMatrix_transpose_mul_self` / `mulVec_apply`, `unknown constant 'Hqiv.lieBracket_in_span'`, and tactic failures in `Hqiv/GeneratorsLieClosure.lean` (log referenced as `/tmp/hqiv_HQIVSO8Closure.log` in that run).
  - Current tree (2026-05-12 spot-check): `Hqiv.so8CoordMatrix_transpose_mul_self` is present as a **documented axiom** in `Hqiv/So8CoordMatrix.lean`; `Hqiv.lieBracket_in_span` is defined in `Hqiv/GeneratorsLieClosure.lean`; `lake build Hqiv.So8CoordMatrix` **passes**. Full `lake build HQIVSO8Closure` remains a **long** job (784 `LieBracketCell` modules + closure data); re-verify locally before publication and record exit code in this file.
  - 2026-05-12 agent session: long-running `lake build HQIVSO8Closure` / `Hqiv.GeneratorsLieClosure` / `Hqiv.LieBracketCell.R0C0` jobs were **aborted** before completion (no final exit code captured); they do **not** supersede a full local or CI run.
  - **RAM:** parallel elaboration of the 784 `Hqiv/LieBracketCell` modules (entrywise `norm_num` on real literals) can exceed **~100GB** resident set. Mitigation: `scripts/build_hqiv_so8_closure_lowmem.sh` (`LEAN_NUM_THREADS=1`, `lake build HQIVSO8Closure -j 1`). The Zenodo paper-refs bundle **omits** those `.lean` files; use a full clone for `HQIVSO8Closure`.
  - `lake build HQIVWitnesses` -> **pass** (historical)
  - `lake build HQIVRhFourierLift` -> **pass** (historical)
  - `lake build HQIVPlastic` -> **pass** (historical)

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

1. **Keep `HQIVSO8Closure` reproducible**: run `lake build HQIVSO8Closure` on a clean CI runner after Mathlib bumps; if orthonormality is still axiomatized, keep manuscript language aligned (see `papers/closure.tex` reproducibility paragraph). Optionally replace `so8CoordMatrix_transpose_mul_self` with a fully expanded proof when toolchain limits allow.
2. Freeze manuscript + appendix PDF generation command(s) in a reproducibility note.
3. Fill final `.zenodo.json` metadata fields.
4. Create final upload bundle from `publication_inventory.json` paths.
