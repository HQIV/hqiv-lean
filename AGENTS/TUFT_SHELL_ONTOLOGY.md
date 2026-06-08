# TUFT shell chart vs HQIV lock-in shell

**Read before** editing hadron readouts, TUFT papers, or `MetaHorizonExcitedStates` prose.

Lean: `Hqiv/Physics/TuftShellChart.lean`  
Python: `scripts/hqiv_tuft_shell_chart.py`  
Paper snippet: `papers/include/shell_ontology_messaging.tex`

---

## Two languages (do not merge in text)

| Name | What it is | Use for |
|------|------------|---------|
| **`referenceM`** | HQIV substrate lock-in (`qcdShell + latticeStepCount` → 4) | Cosmology, CMB, η, single-scale witness, **legacy** meta-horizon catalog |
| **`tuftHeavyChartShell`** | TUFT Beltrami row `m = heavy Hopf winding + 1` (→ 4) | Baryon ground chart, vev-pinned hadrons, trapped-inside closure |
| **`tuftStrongChartShell`** | Strong sector chart row (→ 3) | Vector meson ground (`× 3/4` of baryon) |
| **`tuftWeakChartShell`** | Weak sector chart row (→ 2) | Weak-sector bookkeeping (not baryon tower) |
| **`tuftHadronModeShell n ℓ`** | `tuftHeavyChartShell + n + ℓ` | **Canonical** baryon excitation channel tag |

**Rule:** TUFT hadron papers and primary readouts say **heavy TUFT chart** / `tuftHadronModeShell`.
HQIV papers say **`referenceM`** where the substrate pin is load-bearing.
When both equal `4` today, say **numeric coincidence**, not “the same shell by definition.”

---

## What uses which (implementation)

| Readout | Shell ontology |
|---------|----------------|
| `tuftHadronGroundAtXi_MeV` | TUFT vev chain (scale); anchor row = heavy chart |
| `tuftHadronExcitedMassAtXi_MeV` | TUFT heavy chart Beltrami increments |
| `tuftHadronExcitedMassUnified*AtXi_MeV` | TUFT `tuftHadronModeShell` + heavy-chart trapped ratio |
| `metaHorizonExcitedMassReadout` / `totalModeShell` | **HQIV legacy** names (`referenceM + …`) |
| `metaHorizonTrappedPlanckMassReadout` | HQIV shell ladder (bridged to TUFT at lock-in) |

Bridge (proved): `totalModeShell n ℓ = tuftHadronModeShell n ℓ` when pins align.

---

## Anti-patterns (rewrite on sight)

- “Excited baryons sit on shell `referenceM + n`” in a **TUFT** hadron section → use **heavy TUFT chart**.
- “TUFT shell = HQIV shell” → **false as ontology**; only true as today's numeric bridge.
- Using `REFERENCE_M + n + ℓ` in new TUFT Python without importing `hqiv_tuft_shell_chart`.
- Assigning PDG states to `tuftWeakChartShell` or `tuftStrongChartShell` for baryons.

---

## Internal quanta `(n, ℓ)`

On the heavy chart, `n` and `ℓ` are **internal Beltrami quanta** (radial / orbital steps),
not TUFT Hopf windings 1/2/3. Mixed modes use separate radial and orbital shell steps:

- `tuftHadronRadialShell n = m_heavy + n`
- `tuftHadronOrbitalShell ℓ = m_heavy + ℓ`
- Channel tag for inside closure: `tuftHadronModeShell n ℓ = m_heavy + n + ℓ`

Split readout inverts radial and orbital increments separately on the trapped curve.

---

## Verify

```bash
lake env lean Hqiv/Physics/TuftShellChart.lean
lake env lean Hqiv/Physics/HopfShellBeltramiMassBridge.lean
python3 -c "import hqiv_tuft_shell_chart as t; assert t.reference_m_eq_tuft_heavy_chart_numeric()"
```
