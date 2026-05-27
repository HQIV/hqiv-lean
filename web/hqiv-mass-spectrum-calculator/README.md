# HQIV mass spectrum derivation calculator

Interactive trace from combinatorial backbone → Fano coupling linear system → electroweak / neutrino / quark / hadron readouts.

## Run locally

From the repo root:

```bash
python3 -m http.server 8765
```

Open [http://localhost:8765/web/hqiv-mass-spectrum-calculator/](http://localhost:8765/web/hqiv-mass-spectrum-calculator/)

(`file://` works for the engine; loading `data/hqiv_witnesses.json` needs the HTTP server.)

## UI

1. **Input anchor** — CODATA proton, CODATA 1/α, Lean witness, or geometry-only.
2. **Sector** (radio) — **Lepton** · **Hadron** · **Boson** · **Neutrino**.
3. Sector-specific target:
   - **Hadron:** 12 varieties (octet, decuplet, mesons, tetraquarks, pentaquarks, …) → second dropdown lists **valid valence configs** (e.g. p → uud, P_c → uudsc, J/ψ → c c̄).
   - **Lepton:** e, μ, τ.
   - **Boson:** W, Z, H, predicted 1/α.
   - **Neutrino:** νₑ, νμ, ντ.

## Examples

| Input | Sector | Target | Chain |
|-------|--------|--------|--------|
| CODATA proton | Hadron → doubly charmed → **ccd** | Fano + informational readout + witness-scaled constituents |
| CODATA proton | Neutrino → νₑ | Fano → `M_Z` closure → `m_νe = (γ/S(6))·M_Z` |
| CODATA 1/α | Boson → 1/α braced | Continuous σ(ξ) brace pins α |
| CODATA proton | Hadron → pentaquark charm → P_c(4312)⁺ | 5-valence scaffold |

## Lean / Python mirrors

- `hqiv-mass-engine.js` — browser math
- `scripts/hqiv_coupling_linear_system.py` — full solver CLI
- `scripts/cubic_phase_relax_probe.py` — quark coordinates & resonance steps
- `scripts/check_fano_mass_coherence.py` — boson closure checks
- `scripts/hqiv_mass_calculator_core.py` — shared coupling + informational hadron mass
- `scripts/benchmark_mass_calculator_vs_pdg.py` — batch PDG comparison (full stack)
- `scripts/informational_energy_mass.py` — informational readout gauges
- `data/hqiv_witnesses.json` — optional JSON overlay (`lake build HQIVWitnesses`)

## Published comparison (PDG)

- **102** hadron masses in `data/hadron_published_masses.json` (PDG 2024 RPP centrals; comparison only).
- Regenerate: `python3 scripts/export_hadron_published_masses.py` (also writes `hadron-published-data.js` for offline use).
- In **Hadron** sector, under the HQIV result:
  - **Published reference** box for the selected configuration (when `config_id` is linked).
  - Expandable **table** of all entries with filter; selected row shows HQIV Δ%.

## Honesty labels

- **Derived:** α, γ, boson witnesses, neutrino suppression ladder (no PDG in closure definitions).
- **Witness:** `m_top_GeV`, `m_bottom_GeV` on the quark ladder (see `AGENTS/MASS_DERIVATION_ROADMAP.md`).
- **Benchmark:** `python3 scripts/benchmark_mass_calculator_vs_pdg.py` writes `data/mass_calculator_benchmark_summary.json`.
- Hadron masses use **witness / coupling / informational-energy** readout (`hadronMassFromXi`), not the legacy constituent−`E_bind` scaffold.
