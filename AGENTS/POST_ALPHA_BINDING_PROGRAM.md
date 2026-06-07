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

## Commands

```bash
lake build Hqiv.Physics.PostAlphaBindingGeometry Hqiv.Physics.HQIVNuclei Hqiv.Physics.BBNNetworkFromWeights
python3 scripts/hqiv_post_alpha_binding_program.py
python3 scripts/hqiv_post_alpha_binding_program.py --json data/post_alpha_binding_program.json
python3 scripts/hqiv_isotope_binding_vs_pdg.py   # deepening/network diagnostic (comparison only)
```

## BBN integrator policy

- **Still uses** `bbn.cluster_binding_mev` / `bbnValleyBindingFactor` (legacy normalization).
- **`bbnClusterBindingFromCausticGeometry`** now returns `postAlphaClusterBindingFromGeometry` for `A > 4` (witness path; not wired into cooling integrator until reconciliation closes).
- Do **not** tune `HE3`/`Be7` rates to Spite Li until post-α MeV scale matches PDG **order of magnitude** on ⁵–⁷Li panel.

## Next Lean targets

- `postAlphaCoreIncrementalBinding`: α caustic base + differential facet/far sums only.
- General `bbnProtonFacetTouches` beyond explicit `A = 7` rows (feasibility + spin gate).
- Theorem: `postAlphaClusterBindingFromGeometry` agrees with `bbnClusterBinding` at `A = 7` up to explicit calibration factor, or prove they must differ and why.

## Next Python targets

- Align `hqiv_post_alpha_sphere_touching.py` staged touches with Lean (single source).
- Hook `nuclear_cluster_binding_at_xi` inside/outside split into the witness table for `A > 4`.
