# GWTC-5.0 PE cache (ringdown mass inference)

Official catalog: https://gwosc.org/GWTC-5.0/

## Zenodo PE releases

| Release | URL | Contents |
|---------|-----|----------|
| PE Part 1 | https://zenodo.org/records/20348005 | `PESummaryTable.hdf5` + per-event HDF5 (O4a/O4b mix) |
| PE Part 2 | https://zenodo.org/records/20348006 | Per-event `combined_PEDataRelease.hdf5` (O4b) |
| Candidates | https://zenodo.org/records/20276130 | Candidate metadata |
| Notebook | https://doi.org/10.5281/zenodo.20276105 | `GWTC5p0_PE_data_release.ipynb` |

## HQIV workflow

1. **Inputs:** ringdown `f₂₂₀` (Hz) and `τ₂₂₀` (s) — from ringdown fit or Kerr map from PE mass/spin.
2. **Outputs:** inferred `M_f` (GR Kerr vs HQIV-unmapped Kerr).

```bash
# Auto-download PE summary (~200 KB) and run inference table
python3 scripts/hqiv_gw_ringdown.py --pe-summary --json

# Single measured ringdown
python3 scripts/hqiv_gw_ringdown.py --f 251 --tau-ms 4

# Full PE file (after downloading from Zenodo)
python3 scripts/hqiv_gw_ringdown.py --pe-hdf5 data/gwtc5_pe/GW250119_190238-combined_PEDataRelease.hdf5
```

Requires `h5py` (local venv: `.venv-gw/bin/pip install h5py`).

## Local files

- `PESummaryTable.hdf5` — cached by `hqiv_gwtc_pe_loader.download_pe_summary_table()`
- `manifest.json` — official URLs + usage (generated on run)

Per-event `combined_PEDataRelease.hdf5` files are large (100 MB–1 GB). Download manually from Zenodo or:

```bash
pip install zenodo_get
zenodo-get 20348005   # Part 1 (includes summary table)
zenodo-get 20348006   # Part 2
```
