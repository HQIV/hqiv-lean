# Zenodo Publication Bundle (Draft)

This folder prepares reproducible publication objects for Zenodo, focused on:

- manuscript + appendix (`papers/*.tex` plus generated PDFs),
- Lean proof modules tied to the manuscript's verification claims,
- symbolic certificate generators and exact JSON artifacts.

## Build inventory + checksums

From repository root:

```bash
python3 release/zenodo/build_zenodo_bundle.py
```

Generated files:

- `release/zenodo/publication_inventory.json` (machine-readable manifest),
- `release/zenodo/SHA256SUMS.txt` (checksums for upload verification),
- `release/zenodo/MISSING_REQUIRED.txt` (required publication files not found).

## Zenodo metadata files

- `release/zenodo/.zenodo.json` is the editable Zenodo metadata draft.
- Copy this file to repository root as `.zenodo.json` for GitHub-release -> Zenodo auto-import workflows.

## Publication iteration checklist

1. Run Lean publication target audits (`lake build HQIVPaperClaims` for the rapidity/SO(8) manuscript cone; optionally `HQIVWitnesses`, `HQIVRhFourierLift`, `HQIVPlastic`, `HQIVSO8Closure`).
2. Rebuild manuscript/appendix PDFs.
3. Regenerate symbolic certificates if code changed.
4. Re-run `build_zenodo_bundle.py`.
5. Confirm `MISSING_REQUIRED.txt` is `none`.
6. Upload files + checksums to Zenodo draft.
