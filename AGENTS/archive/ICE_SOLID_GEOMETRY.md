# Ice and solid allotropes from HQIV geometry (roadmap)

**Status:** Not implemented — architectural target aligned with existing bond/contact spine.  
**User expectation (correct):** A solid (ice Ih, Ic, etc.) should be a **derived 3D contact network** from
geometry + bonds + periodic repetition, not a hand-entered phase enum.

## What we already have (use for solids)

| Piece | Module | Role for ice |
|-------|--------|----------------|
| Intramolecular H₂O | `H2O.lean`, `CentreGeometryFromTuft`, `hqiv_dynamic_binding_chart` | O–H length, **dynamic** H–O–H angle (`dynamicCentreAngleRad 8 2`), surplus dress |
| Inter-contact curvature | `hqiv_curvature_contact_network`, `S2BindingGeometry` | `G_eff(θ)`, valley alignment, steric vs covalent |
| Periodic bookkeeping | `ContactKind.PERIODIC_IMAGE`, `lattice_repeats` | Solid env → image contact **counts** (not positions yet) |
| Equilibrium narrative | `TorqueTreeEquilibrium`, `bondValleyEM` | Minimize dihedral / valley on a **tree** |
| QAOA geometry search | `hqiv_qcomp_qaoa.py` | Discretize **one** molecule’s DOFs (not unit cell) |
| Post-α sphere touching | `post_alpha_sphere_touching` | **Nuclear** tetrahedral contact graph — analogy only for ice |

**Validated today:** isolated H₂O binding (~0.4% error vs witness after `z_centre` fix).  
**Not validated:** any ice unit cell, hydrogen-bond network, or allotrope energy ordering.

## What ice requires beyond gas-phase H₂O

1. **Tetrahedral coordination at O** — each water O accepts two H-bonds (~180° apart in lone-pair picture) while donating two H; ice Ih/Ic use **Bernal–Fowler** rules.
2. **Intermolecular contacts** — `O···H` contacts with `G_eff` at **donor–acceptor angle**, not peripheral-H **steric** repulsion (current H₂O network table undercounts H-bonds).
3. **3D lattice positions** — `FragmentConfig` + `BondGeometry` need **Cartesian** or fractional coords per molecule in the unit cell, not only bond lengths on one monomer.
4. **Periodic boundary** — replace scalar `PERIODIC_IMAGE` point count with **lattice vectors** `(a,b,c)` and image translations so contacts across cells are explicit.
5. **Allotrope comparison** — same binding functional on different space groups (Ih vs Ic vs II) → relative stability from **network binding + coordination**, not from `(T,P)` labels alone.

## Proposed build order (no fitted potentials)

1. **`IceUnitCell` witness** — minimal orthorhombic/hexagonal templates: sites, O/H indices, covalent bonds, **target** O···H distances (~1.75–1.8 Å), H–O–H and O–H···O angles.
2. **`build_ice_network(allotrope, env)`** — `build_network_from_molecule` extended to N molecules in cell + `INTERMOLECULAR_HBOND` contact kind (attractive `G_eff`, not steric).
3. **`ice_binding_energy(cell)`** — reuse `e_bind_from_network` / dynamic chart pipeline on **full cell** surplus × networked vev × geometry_align.
4. **Relaxation** — extend `hqiv_qcomp_qaoa` or torque-tree scan over **cell DOFs** (six lattice strains + internal H positions) with carrier encoding deferred.
5. **Allotrope panel** — compare Ih vs Ic total binding per molecule at 0 K limit; optional ξ(T) for stability window.

## Relation to phase / triple point

- **Solid structure** (this doc) = **0 K geometry + periodic contacts**.
- **`hqiv_thermodynamic_phase_from_tp.py`** — bulk water melt scaffold:
  `material_scales_bulk_h2o()` + `solid_liquid_transition_temperature_K()` (~269 K @ 1 atm
  from κ(ξ)·α²·(4/8)·(4/3)/(1+α)³; ~1.5% below 273.15 K NIST). Does **not** yet build ice coordinates.
- **Triple point** needs bulk coexistence curves **after** a credible ice binding curve exists.

## Out of scope for v0

- DFT/empirical force fields, fitted H-bond potentials.
- Full phonon spectrum; only static network binding + optional QAOA cell relaxation.
- Carrier peaking (`CARRIER_PEAKING_GEOMETRY_ENCODING.md`) — optional later for cell-parameter search.

## Commands (when implemented)

```bash
# placeholder
python3 scripts/hqiv_ice_unit_cell.py --allotrope Ih --relax
python3 scripts/hqiv_ice_unit_cell.py --compare Ih,Ic,II
```
