# Curvature contact network (geometry + thermodynamics)

**Lean:** `Hqiv/QuantumChemistry/CurvatureContactNetwork`, `Hqiv/Physics/ThermodynamicLawsFromLadder`  
**Python:** `scripts/hqiv_curvature_contact_network.py`, `scripts/hqiv_thermodynamic_phase_from_tp.py`  
**Consumers:** `hqiv_dynamic_binding_chart.py`, protein folding (`ProteinFoldingHook`), bulk materials

## Purpose

Single parameter-free rule engine for how **bound cluster mass** and **contact curvature**
update the TUFT **vev geometric mean** before surplus × η_p × EV_per_λ.

Extends to **materials science** and **protein folding** by taking only **(T, P)** as
environmental inputs; **phase is an output**, never `solid` / `liquid` as user knobs.

## Inputs vs outputs

| Input | Output |
|-------|--------|
| `temperature_K`, `pressure_Pa` | `derived_phase`: gas, molecular_cluster, liquid, solid, supercritical |
| Fragment geometry + bonds | Contact graph (cluster, covalent, steric, hyperclosure, periodic) |
| Atomization / cohesive binding scale | `T_melt_K`, `T_boil_K`, `P_solidify_Pa`, `P_vapor_Pa` |
| Network-built contacts | `coordination_fraction`, `contact_persistence`, `periodic_weight` |

## S² / p-shell geometry

**Module:** `scripts/hqiv_s2_binding_geometry.py` — Lean `Hqiv.QuantumChemistry.S2BindingGeometry`

| Quantity | Rule |
|----------|------|
| p-shell modes | S² degeneracy `2ℓ+1 = 3` for ℓ = 1 |
| Compton η | `η = θ/θ₀` on (m_s, m_p, m_light) triplet per bond |
| Binding angle | Experimental `bond_angle_rad` when supplied; ideal from `dynamicCentreAngleRad(Z, n_bonds)` |
| Valley alignment | `κ(1 − cos(θ_bond − θ_ideal))` minimum at native centre angle (dihedral budget) |
| Geometry alignment | `geomean(w)` on binding & vev; `w` from valley_align × η × S² |
| Dynamic binding feedback | `1 + κ(ξ)·(B_lock−B_qcd)/B_lock` with `κ(ξ)=γ·4/8·B_curv(ξ)` |
| Bond contact | `G_eff(θ_compton) × valley_align × 1/(1+d/a₀)` |

Optional `BondGeometry.bond_angle_rad` overrides inferred angles. Each node carries
`shell_geometry` (η_s, η_p, angles); each covalent contact carries `bond_geometry` in JSON witnesses.

## Contact kinds

| Kind | Sign | Rule |
|------|------|------|
| `cluster_deficit` | attractive (mass down) | Node: `tuftVevFactorNetworkedAtCluster` |
| `covalent_bond` | attractive | Edge: `G_eff(θ)`, weight `1/(1+d/a₀)` |
| `steric_repulsion` | repulsive (mass back) | Peripheral H–H (CH₄: 4 points, 2 per H) |
| `hyperclosure` | graph | ≥2 bonds: `1/√n_bonds` |
| `periodic_image` | lattice | When **derived** phase is `solid` |

## Phase derivation (T, P)

Cohesive scale (phase only, not atomization): `e_cohesive = κ(ξ) · α² / (n_inter · (1+α)²)` with `κ(ξ) = γ·(4/8)·B_curv(ξ)` and `ξ` = Compton-triplet mean (`DynamicBindingChart`).

### Phase transitions / triple point (limits, Jun 2026)

**Not in scope yet:** locating coexistence curves or the water triple point (273.16 K, 611.7 Pa). Current `(T,P)` classifier is a **ladder + κ(ξ) cohesive** scaffold, not a Clausius–Clapeyron or Gibbs-phase solver.

| Quantity | HQIV H₂O (network table) | NIST (water) |
|----------|--------------------------|--------------|
| `T_melt_K` (dilute `H2O`) | ~202 | ~273 |
| `T_melt_K` (`H2O_bulk`, 1 atm) | **~273** (phase lift + κ₆ second-order × **ρ**) | ~273 |

**Medium density ρ:** `intermolecular_contacts / 4` (ice reference) or network steric points.

Scales **κ₆** as `1 + (f₂(ξ)−1)·ρ` and **bond ``G_eff(θ)``** as `1 + (G_eff−1)·ρ` on covalent
contacts (network rebuild after steric count). Surplus-level `outside_geff` inherits ρ via
Σ `geff_theta` on scaled bonds. Dilute GMTKN55 → small ρ; bulk ice → ρ=1.
| `T_boil_K` | ~322 / ~430 bulk | ~373 |
| `P_solidify` | ~0.4 bar (STP-anchored) | triple ~611 Pa |

**Bulk solid→liquid @ 1 atm:** `material_scales_bulk_h2o()` + `solid_liquid_transition_temperature_K()` — ice below ~269 K, liquid above (κ·α²·(4/8)·(4/3)/(1+α)³ melt channel). GMTKN55 `H2O` row stays dilute (`molecular_cluster` at STP).

At triple-point `(T,P)`, readout is still `molecular_cluster` for dilute `H2O`, not coexistence. **Qualitative OK:** cold ice → `solid` (test at 150 K). **Use binding chart for gas-phase chemistry; use `H2O_bulk` for bulk melt scaffold.**

Carrier-peaking geometry readout is documented separately: `AGENTS/CARRIER_PEAKING_GEOMETRY_ENCODING.md` (deferred).

**Solid ice / allotropes:** geometry-first target (unit cell + H-bond contacts + periodic positions), not `(T,P)` alone — see `AGENTS/ICE_SOLID_GEOMETRY.md`.

**Next (homogeneous + nucleation):** `AGENTS/HOMOGENEOUS_CURVATURE_SECOND_ORDER.md` — compute `B_hom(ξ,ρ)`, add local `δB` at defects, feed `B_eff` back into binding/melt (replaces ρ-only proxy).

### Second-order terms mined from action / mass geometry (GMTKN55 chart)

| Term | Source | Formula | Chart |
|------|--------|---------|-------|
| **p-shell η₂** | LiH `lihDynamicValenceSiteEnergyTrace` + shared-p channel | `η₂ = η + (4/8)·η²` when Compton p-slot active (`m₁>1`, `m₀≠m₁`) | **on** |
| **Lapse C₂** | `tuftHopfKappa6AtXi = η·γ·C₂(ξ)` | `feedback₂ = (1+κ(ξ)·C_rel)·C₂(ξ)/C₂(ξ_lock)` | optional (over-corrects H₂/H₂O) |
| **Outside G_eff** | `outside_contact_dimless`, action bond surplus | `1 + (4/8)·Σ G_eff(θ)/surplus` | optional (~6.6% mean alone) |
| **Surplus 2nd** | `action_total_general_add_J` shared kinetic | already 1st order in `bondHorizonSurplusDimless` | — |
| **Vev cluster 2nd** | `tuftVevFactorNetworkedAtCluster` Taylor in cluster mass | `(vev/bare)^α` | not used (CH₄ overshoot) |

Lean: `dynamicComptonEtaSecondOrder`, `dynamicBindingCurvatureFeedbackSecondOrderAtXi` in `DynamicBindingChart.lean`.

### Network aggregation (geometric mean vs product)

The chart follows Lean `lihDynamicBindingCoreDimless`:

`E ∝ η_p · surplus · geomean(tuftVev)_slots · (1+κ·C) · geomean(valley_align)_bonds`

| Factor | Aggregation |
|--------|-------------|
| TUFT vev | **Geomean** over Compton slots `(m_s, m_p, m_h)`, then × steric / phase (node geomean) |
| Valley geometry | **Geomean** over covalent bonds |
| η_p | **Single** `θ_mean/θ₀` on the triplet — not geomean(per-slot η) or fragment nuclear geomean |
| Surplus | Scalar joint−separated (action non-additivity) |
| Cross-factor | **Arithmetic product** — not `geomean(η_i × vev_i)` per leg |

Strict `geomean(η_i×vev_i)` per leg underbinds hydrides ~35–50%; mean-angle η is deliberate. Witness: `network_balance` in `data/dynamic_binding_chart.json`.

### Network binding feedback (buttoned down)

**Python:** `NetworkBindingFeedback` in `hqiv_curvature_contact_network.network_binding_feedback`

Single call after `build_network_from_molecule`:

```
E_bind = η₂ · surplus · (networked_vev · geometry_align · κ_feedback(ξ)) · EV_per_λ
         └shell─┘   └────────── dimless_prefactor ──────────────┘
```

| Factor | Source | Sign / rule |
|--------|--------|-------------|
| `bare_vev_geometric_mean` | Compton slots `(m_s,m_p,m_h)` × cluster mass per slot | Heavy slots dressed down (valley deficit) |
| `steric_multiplier` | Peripheral H–H contact points | **≥ 1** — repulsive curvature mass back (CH₄ largest) |
| `phase_multiplier` | Derived `(T,P)` phase + coordination | Liquid/solid only; gas → 1 |
| `networked_vev_geometric_mean` | `bare × steric × phase` | Feeds chart geomean |
| `geometry_alignment_factor` | Geomean valley weight on covalent bonds | `θ_ideal = dynamicCentreAngleRad(Z_centre, n_bonds)` |
| `curvature_feedback_at_xi` | `1 + w·κ(ξ)·C_rel` | `w=1` heavy; H₂ uses lapse dress `w < 1` |

Witness: `network_binding_feedback` block in `contact_report()` JSON and `data/dynamic_binding_chart.json`.

**Centre wiring:** `_bond_contacts` passes `z_centre=Z_heavy` when the heavy atom has ≥2 bonds (fixes H₂O ideal ≠ 180°).

### Electronic valence shells (`scripts/hqiv_electronic_valence_shells.py`)

Contact nodes use **electronic** Compton indices (not nuclear drum `m_nuc`):

| Species | Chemist shell | Compton `m` |
|---------|---------------|-------------|
| H | `1s` | `1` |
| Period-2 centre (O, C, N, Li, …) | `2s` / `2p` | `4` / `3` |

Lean heavy-hydride triplet `(4,3,1)` drives η, vev slots, and O–H bond geometry. Nuclear rows in the chart still report `m_nuclear` / drum valence for cluster binding witnesses.

### Shell-aware pipeline (`scripts/hqiv_shell_aware_binding.py`)

| Compton class | Surplus angles | η_p | Atomization dress |
|---------------|----------------|-----|-------------------|
| `(1,1,1)` H₂ dissociation | **UUD** | S²-weighted detuning | — |
| `(4,3,1)` heavy hydride dissociation | bond-averaged Compton | S²-weighted detuning | — |
| `(4,3,1)` atomization (H₂O, …) | **electronic detuning** `(4,3,1)` | S²-weighted detuning | VSEPR lone-pair + bent-centre hyperclosure (H₂O only) |

`shell_readout` records `electronic_shell_slots` (`2s`, `2p`, `1s`), Lean splits (`H₂O` → `10+8+2`), and `surplus_dress_factor`. H₂ curvature contrast uses `1 − (4/8)(1 − C₂(ξ)/C₂(ξ_lock))`; heavy centres use **1.0**.

- `T_melt` from cohesive / `(1+α)`
- `T_boil` from cohesive
- `P_vap(T) ∝ (T/T_boil)^γ`
- **Gas / molecular_cluster** at STP for small molecules (GMTKN55)
- **Solid** when `T < T_melt` and `P ≥ P_solidify`
- **Liquid** between melt and boil at `P ≥ P_vap`
- **Biopolymer** (`protein*`): coordination from ξ(T) ladder at cytosolic T

## Building a network

```python
import hqiv_curvature_contact_network as ccn
import hqiv_thermodynamic_phase_from_tp as tptp

env = tptp.ThermodynamicEnvironment.stp()  # or .protein_cytosol()
net = ccn.build_network_from_molecule("CH4", fragments, bonds, environment=env)
vev = ccn.networked_vev_geometric_mean(net)
print(net.thermo.phase)  # derived, e.g. gas at 298 K
```

Protein scaffold:

```python
net = ccn.build_protein_network("protein_48mer", n_residues=48)
```

## Witness JSON

```bash
python3 scripts/hqiv_curvature_contact_network.py
python3 scripts/hqiv_thermodynamic_phase_from_tp.py
```

## D / T vs CH₄ (sign rule)

- **D, T:** cluster deficit lowers vev (valley memory).
- **CH₄ outer H:** steric contacts add curvature mass back (opposite sign).

Same spine (`G_eff`, γ); opposite sign on the mass ladder.

## Roadmap

1. Structure-based protein contacts → same graph + cytosol (T, P).
2. Crystal CIF → `lattice_unit_cell` when derived phase is solid.
3. Phase-diagram witness grids over (T, P) for species and folding boxes.
