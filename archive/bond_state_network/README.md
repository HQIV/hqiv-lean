# Archived: bond-state network quantitative layer

**Status:** superseded for binding-energy benchmarks (2026-07).

This directory documents the older inside/outside curvature **projection** that produced
~1 eV H₂ readouts instead of the canonical ~4.5 eV.

## Use instead

- Python: `scripts/hqiv_dynamic_binding_chart.py`
- Lean: `Hqiv.QuantumChemistry.DynamicBindingChart`
- Agent doc: `AGENTS/BINDING_ENERGY_STACK.md`

## What remains valid here

- `Hqiv.QuantumChemistry.BondStateNetwork` — structural trace identity
  (`closedNetworkWeight = separated + edge + hyper`), no fitted coefficients.
- `scripts/hqiv_bond_state_network.py` — diagnostic decomposition only.

## What not to use

- `data/bond_state_network_chart.json` — do not cite for H₂/LiH binding accuracy.
