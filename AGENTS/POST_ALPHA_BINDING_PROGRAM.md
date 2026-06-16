# Post-α binding energy program (`A > 4`)

**Status:** active research track — required before tuning BBN Li production or post-BBN destruction.

## Problem

For `A ≤ 4`, the isotope ladder + 8×8 composite trace (`BoundStates`, `BBNNetworkFromWeights`) gives
usable reaction Q and masses at the proton anchor (`m = 4`, 938.272 MeV).

For `A > 4`, the current BBN spine uses `bbnValleyBindingFactor` — a **normalized contact-count proxy**
— multiplied by `A × E_bind_from_composite_trace`. That preserves **ordering** (e.g. ⁷Be deeper than ⁷Li)
but not **absolute** binding vs CODATA/PDG total binding (~40 MeV vs ~19 MeV cluster ledger).

We must close the geometric derivation before changing the Li integrator.

## Three layers (build order)

| Layer | Lean | Python |
|-------|------|--------|
| 1. Contact ledger | `HQIVNuclei`: `bbnProtonFacetTouches`, `bbnFarNeutronTouches`, `postAlphaOutsideValleyCountEffective` | `hqiv_post_alpha_sphere_touching.py` |
| 2. Geometric currency | `sphereTouchContactEnergyUnit m = R_m²` (from `valleyPotential` scale) | same + `hqiv_post_alpha_binding_program.py` |
| 3. MeV bridge | `geometryToMeVCoupling m = trace / unit` → `postAlphaClusterBindingFromGeometry` | witness JSON |

**Staged facet rule (A ≥ 5):** first proton on a new α face gets **1** contact, not 3; occupation ramps toward 3 as more protons share faces (`bbnProtonFacetTouches` in `HQIVNuclei.lean`). This removes the discontinuous ⁴He → ⁵Li jump.

## Network + relaxation (mechanism)

When additional nucleons attach beyond ⁴He:

1. **Well deepening** — each post-α touch lowers the energy of the α-core sites it couples to  
   (`postAlphaCoreWellDeepening`, scale `(4/8)/6` per incremental contact).
2. **Network** — those deepened wells interact on the tetrahedral contact graph  
   (`postAlphaNetworkBindingEnergy`, `γ × (deepening − 1) ×` α-core geometric energy).
3. **Relaxation** — the *added* nucleons are often **lighter** (staged partial facet contacts, far-neutron `4/8` weight); the collective well **relaxes** and the compound **loses a little `BE/A`** vs naive `geometry/A`  
   (`postAlphaWellRelaxationEnergy` ∝ `(A−4) × light_fraction × (4/8) × γ × trace`).

Total: `postAlphaClusterBindingWithNetwork = geometry × deepening + network − relaxation`.

## Open reconciliation (do not skip)

1. **Double-counting:** α tetrahedral closure vs incremental facet contacts on the same core.
2. **Absolute MeV:** deepen + network − relax still ~O(0.2)× PDG total B — calibrate without PDG fits.
3. **Reaction Q:** map network binding to formation/capture barriers in the BBN integrator.

## Curvature + G_eff spine (Lagrangian-first)

Binding is a function of curvature; **`G_eff(η) = η^α`** (α = 3/5) couples valley contacts:

- **Inside:** `A × trace × Δ(metaHorizonTrappedInsideRatio)`
- **Outside:** `contact_units × G_eff(θ/θ₀) × trace`
- **A > 4:** `contact_units` = post-α ledger (deepen + γ-network − relax), still × `G_eff × trace`

Lean: `Hqiv.Physics.NuclearCurvatureBinding`. Python: `hqiv_curvature_binding_core.py`,
`hqiv_curvature_binding_program.py`.

**Shared-well network (June 2026):** closes most of the gap without PDG fits:

- **A ≤ 4:** `G_eff×trace×A×(1+vc/6)×D_intr + γ-network (vc>2) + barbell (A≥3) + tetra (A≥4)`
- **A > 4:** ⁴He core outside + `γ×(D_postα−1)×core` + extra-nucleon ladder + `G_eff×postAlpha`
- **Mass deficit FP:** `1 + γ·(4/8)·(B/A)/m_p` deepens wells as nucleons lose mass into the well

Panel mean |Δ| vs PDG total B ≈ **8%** (down from 66% bare `vc×G_eff×trace`).

Anchors: ²H −2%, ⁴He −4%, ⁵Li +5%, ⁶Li −3%, ⁷Be −4%, ¹⁶O +9%. Open: ⁷Li/⁸Be/¹²C
still under; collective inside-network saturation for doubly-magic / ⁸Be scaffold.

## Commands

```bash
lake build Hqiv.Physics.NuclearCurvatureBinding Hqiv.Physics.PostAlphaBindingGeometry Hqiv.Physics.HQIVNuclei
python3 scripts/hqiv_curvature_binding_program.py       # G_eff curvature spine (preferred)
python3 scripts/hqiv_curvature_binding_program.py --json data/curvature_binding_program.json
python3 scripts/hqiv_binding_energy_program.py          # unified panel (A≤4 ladder + A>4 network)
python3 scripts/hqiv_binding_energy_program.py --json data/binding_energy_program.json
python3 scripts/hqiv_post_alpha_binding_program.py      # legacy CLI (same post-α stack)
python3 scripts/hqiv_post_alpha_binding_program.py --json data/post_alpha_binding_program.json
python3 scripts/hqiv_isotope_binding_vs_pdg.py   # deepening/network diagnostic (comparison only)
```

## BBN integrator policy

- **Default (Jun 2026):** `binding_q_hybrid_at_xi` anchors to **`lockin_binding_q_network`**
  (`nuclearClusterBindingNetworkCurvature` + spin–magnetic residual). Legacy valley Q via
  `use_network_spine=False`.
- **Legacy path:** `bbn.cluster_binding_mev` / `bbnValleyBindingFactor` retained for comparison.
- **Residual closure:** `nuclearSpinMagneticResidualParticipation` — `γ²·vc/(cap·R_m)` magnetic
  contrast + `spinStabilityParticipation × |A−2Z|/A` (few % on A ≤ 4).
- Do **not** tune `HE3`/`Be7` rates to Spite Li until ⁵Li/⁵Be α+p overshoot is relaxed.

## Incremental post-α (implemented)

`postAlphaCoreIncrementalBinding` = facet/far geometry × deepen + γ-network − relax  
− `postAlphaCoreDestabilization` (isospin tension `|A−2Z|/(A−4)` on α-outside per nucleon).

Python: `post_alpha_core_incremental_binding_mev`, wired in `compound_binding_above_alpha_mev`.

## Next Lean targets
- General `bbnProtonFacetTouches` beyond explicit `A = 7` rows (feasibility + spin gate).
- Theorem: `postAlphaClusterBindingFromGeometry` agrees with `bbnClusterBinding` at `A = 7` up to explicit calibration factor, or prove they must differ and why.

## Next Python targets

- Align `hqiv_post_alpha_sphere_touching.py` staged touches with Lean (single source).
- Hook `nuclear_cluster_binding_at_xi` inside/outside split into the witness table for `A > 4`.
