# Literature: gas-phase H₂O H–O–H bond angle (comparison quarantine)

**Status:** observational targets only — **not** HQIV derivation inputs.

**PDG note:** the Particle Data Group tabulates hadron and particle properties, not molecular
geometry. Gas-phase water angles come from **rotational / rovibrational spectroscopy** and
NIST aggregation (CCCBDB), not PDG.

## Primary comparison target (Arena median)

| Quantity | Value | Source |
|----------|-------|--------|
| θ_HOH (ground-state effective) | **104.478°** | [NIST CCCBDB H₂O](https://cccbdb.nist.gov/expgeom2.asp?casno=7732185&charge=0) |
| Practical comparison band | **104.478 ± 0.01°** | Aggregated experimental span |
| Literature span | **104.45° – 104.51°** | Microwave / rovibrational determinations |

**Bib keys:** `nistCCCBDBwaterH2O`, `hoy1979waterRotBend` in `papers/references.bib`.

## Key experimental studies

### Hoy & Bunker 1979 — equilibrium structure (most precise)

- **Reference:** Hoy, A. R. & Bunker, P. R., *J. Mol. Spectrosc.* **74**, 1–8 (1979).
- **DOI:** [10.1016/0022-2852(79)90019-5](https://doi.org/10.1016/0022-2852(79)90019-5)
- **Result:** θ_e = **104.4776° ± 0.0019°**, r_e = 0.958 Å from a least-squares fit to 375
  rovibrational energy levels (non-rigid bender Hamiltonian).
- **Role:** defines the equilibrium angle on the Born–Oppenheimer surface; NIST CCCBDB cites
  this as the primary geometry reference.

### NIST CCCBDB — aggregated gas-phase geometry

- **URL:** [cccbdb.nist.gov/expgeom2.asp?casno=7732185](https://cccbdb.nist.gov/expgeom2.asp?casno=7732185&charge=0)
- **Reports:** θ_e = 104.4776° (equilibrium); effective ground-state angle **104.478°** from
  experimental Cartesian coordinates.
- **Role:** Arena **median comparison target** (`HOH_ANGLE_GAS_REFERENCE_DEG = 104.478`).

### Cook et al. 1974 — average vibrational structure

- **Reference:** Cook, R. L. *et al.*, *J. Mol. Struct.* **20**, 349–354 (1974).
- **DOI:** [10.1016/0022-2860(74)90261-6](https://doi.org/10.1016/0022-2860(74)90261-6)
- **Result:** 〈θ_HOH〉 ≈ **104.50°** for the average ground vibrational structure (microwave +
  infrared combined analysis).
- **Role:** upper end of the comparison band (104.45–104.51°).

### Benedict et al. 1956 — early microwave rotation spectrum

- **Reference:** Benedict, W. S., Gailer, N. & Plyler, E. K., *J. Chem. Phys.* **24**, 1139–1145 (1956).
- **DOI:** [10.1063/1.1742588](https://doi.org/10.1063/1.1742588)
- **Result:** effective θ_HOH ≈ **104.5°** in later structural analyses of the rotation spectrum.
- **Role:** historical lower-anchor near **104.45°** in the literature span.

## HQIV derived angle (not an input)

| Tier | Symbol | HQIV value | Lean / Python |
|------|--------|------------|---------------|
| Tetrahedral (LDL network) | θ_tet | 109.47° | `centreAngleRadFromDomains 4` |
| Dynamic gas (HDL slot) | θ_dyn | ~104.471° | `dynamicCentreAngleRad 8 2` |
| Mixture | θ_mix(f) | f·θ_tet + (1−f)·θ_dyn | `hohAngleMixtureSlot` / `hoh_angle_mixture_deg` |

θ_dyn uses VSEPR balance minus lone-pair bent dress with **torque-tree screening**
denominator `(n_domains + n_bonds)` — no tabulated angle enters the definition.

**Current residual:** |θ_dyn − 104.478°| ≈ **0.007°** (inside the ±0.01° comparison band).

## Code hooks

- Python comparison rows: `WATER_HOH_ANGLE_OBSERVATIONS` in `hqiv_lab/phase_diagram.py`
- Audit witness: `hoh_angle_witness_row` → `data/phase_diagram_audit.json`
- Arena metrics (pyhqiv): `water_h2o_bond_angle_residual_deg`, `water_hoh_angle_taxonomy_open_gap_deg`

## Anti-patterns

- Do **not** set `waterBondAngleDeg := 104.478` by `rfl` or inject the NIST value into
  `dynamicCentreAngleRad`.
- Do **not** cite these studies as validation that HQIV *inputs* are correct — they grade
  **readouts** only (comparison quarantine unchanged).

## Related docs

- [WATER_LDL_HDL_REFINEMENT_PROGRAM.md](./WATER_LDL_HDL_REFINEMENT_PROGRAM.md) — θ tiers in LDL/HDL mixture
- [LITERATURE_WATER_TWO_STATE.md](./LITERATURE_WATER_TWO_STATE.md) — liquid two-state / LLPT literature
