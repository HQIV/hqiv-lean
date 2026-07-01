# HQIV Lab — chem & materials package

**Package:** `hqiv_lab/` (install: `pip install -e .` from repo root)  
**Lean:** `Hqiv.QuantumChemistry.PhaseAllotropeDerivation`  
**CLI:** `hqiv-lab H2O`

## Non-Negotiable Input Policy

HQIV Lab prediction paths must not use external chemistry or materials data as
inputs. Disallowed as inputs: W4-17/GMTKN55/NIST/CRC values, PDG/CODATA masses
or couplings, tabulated bond lengths, tabulated bond angles, crystallographic
cell constants, density tables, fitted potentials, hydration shells, mobility
tables, or empirical phase constants.

Allowed prediction inputs are only HQIV-derived primitives and exact unit
conversions needed to express outputs in conventional units. In practice this
means formulas/names resolve to atomic numbers, electron counts, HQIV nuclear
mass readouts, TUFT/nested-wavefunction bond lengths, TUFT centre angles, the
fixed lattice rationals α = 3/5 and γ = 2/5, and the proton-lockin witness at
`referenceM = 4`.

External data may appear only in quarantined comparison fields with names like
`reference_*`, `benchmark_*`, or `comparison_*`. It must never be passed into
`MoleculeSpec`, bond builders, packing, density, phase, binding, conductivity,
or material-response formulas.

## Design

Prediction specs are **HQIV-derived molecular specs** (atomic-chart fragments
and derived bonds), not benchmark geometry:

```
formula/name
  → atomic-chart MoleculeSpec  # fragments + HQIV-derived bonds
  → infer_monomer_geometry()   # VSEPR, motif, n_inter
  → templates_for_motif()      # Ih, Ic, fcc, …
  → unit_cell_for_allotrope()  # a,b,c,Z from contact distance
  → derive_allotropes()        # rank @ (T,P)
  → material_response()        # n, k_th, … (scripts mirror)
```

Witness/literature values are comparison-only. Do not add experimental cell
constant overrides to prediction paths.

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
