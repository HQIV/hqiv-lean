# HQIV Lab — chemistry and materials from HQIV readouts

Derives **allotropes**, **unit cells**, and **material response** from molecular
formulas/names by resolving atomic-chart fragments and HQIV-derived bond
geometry. Benchmark chemistry data is comparison-only; no fitted
intermolecular potentials, tabulated bond lengths, or tabulated bond angles are
prediction inputs.

Requires the HQIV Lean repo layout: `scripts/` for physics mirrors.

## Install (editable)

```bash
cd /path/to/HQIV_LEAN
pip install -e .
```

## Usage

```python
from hqiv_lab import MaterialsLab

lab = MaterialsLab()
spec = lab.spec_from_name("H2O")

for cand in lab.derive_allotropes(spec):
    print(cand.label, cand.density_g_cm3, cand.score)

best = lab.preferred_allotrope(spec)
print(best.unit_cell.a_angstrom, best.unit_cell.c_angstrom)

witness = lab.readout(spec)
```

CLI:

```bash
hqiv-lab H2O
hqiv-lab CH4 --json
hqiv-lab NH3 --allotropes-only
```

## Pipeline

```
formula/name
  → MoleculeSpec (atomic-chart fragments + HQIV-derived bonds)
  → MonomerGeometry (VSEPR, motif, n_contacts)
  → Bravais topology (ice Ih, fcc, chain Z=4, …)
  → r_nn (intermolecular contact, distinct from covalent bond)
  → PhaseUnitCell (a,b,c,Z) from r_nn + topology (α, γ only)
  → Apolar solids: low-T nn scale ``(T/T_ref)^(γ/16)`` on r_nn
  → Motif melt ladder on κ₆(ρ_κ(n)): tetrahedral = 1, apolar/pyramidal/chain from α, γ
  → rank @ (T,P) via thermodynamic spine
  → material_response (n, k_th, C_p, …)
```

## Lean

`Hqiv.QuantumChemistry.PhaseAllotropeDerivation` — structural mirror.
