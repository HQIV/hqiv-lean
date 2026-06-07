# HQIV Lab — chem & materials package

**Package:** `hqiv_lab/` (install: `pip install -e .` from repo root)  
**Lean:** `Hqiv.QuantumChemistry.PhaseAllotropeDerivation`  
**CLI:** `hqiv-lab H2O`

## Design

Inputs are **molecular specs** (fragments + bonds), not allotrope names:

```
MoleculeSpec
  → infer_monomer_geometry()   # VSEPR, motif, n_inter
  → templates_for_motif()      # Ih, Ic, fcc, …
  → unit_cell_for_allotrope()  # a,b,c,Z from contact distance
  → derive_allotropes()        # rank @ (T,P)
  → material_response()        # n, k_th, … (scripts mirror)
```

Witness overrides (experimental cell constants) live in `hqiv_phase_geometry_density`
only as optional calibration — default path is **derived**.

## API

```python
from hqiv_lab import MaterialsLab

lab = MaterialsLab()
spec = lab.spec_from_name("H2O")
print(lab.preferred_allotrope(spec).label)  # Ih
print(lab.readout(spec))
```

## Tests

```bash
PYTHONPATH=. python3 hqiv_lab/tests/test_allotrope_derivation.py
```

## Roadmap

- [ ] Custom `MoleculeSpec` from SMILES/InChI adapter (fragment graph builder)
- [ ] Periodic contact network → allotrope from `hqiv_curvature_contact_network`
- [ ] Glass / amorphous branch from disorder score
- [ ] Export `data/hqiv_lab_witnesses.json` for papers
