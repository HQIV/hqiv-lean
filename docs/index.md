---
layout: default
title: HQIV Lean
---

# HQIV Lean

Formalisation of the HQIV (Horizon-Quantised Informational Vacuum) framework in Lean 4.

## Welcome to the documentation

From the **light-cone combinatorics** (single axiom: new modes at shell \(m = 8 \times \mathrm{stars{\text -}and{\text -}bars}(m)\)), the framework yields:

| Result | API doc |
|--------|--------|
| **Modified Einstein equation** (HQVM-GR, Friedmann from O-Maxwell) | [GRFromMaxwell](/hqiv-lean/docs/Hqiv/Physics/GRFromMaxwell.html) |
| **Modified Lagrangian** (emergent O-Maxwell, reduction to classic Maxwell) | [ModifiedMaxwell](/hqiv-lean/docs/Hqiv/Physics/ModifiedMaxwell.html) |
| **Action** (O-Maxwell + HQVM-GR; stationarity ⇒ equations of motion) | [Action](/hqiv-lean/docs/Hqiv/Physics/Action.html) |
| **Interactive derivation atlas** (term-by-term GUT bridge from Action → plasma source → continuum closure → covariant packaging, with conserved-content and forces cards) | `web/hqiv-story-atlas` |
| **Baryogenesis** (horizon-quantized dynamics) | [Baryogenesis](/hqiv-lean/docs/Hqiv/Physics/Baryogenesis.html) |
| **Mass of proton and neutron** (T_CMB ladder, error bars) | [SM_GR_Unification](/hqiv-lean/docs/Hqiv/Physics/SM_GR_Unification.html) |
| **QFT bridge and quantum chemistry hooks** (finite patch budgets, site-energy traces) | [LightConeMaxwellQFTBridge](/hqiv-lean/docs/Hqiv/Physics/LightConeMaxwellQFTBridge.html), [FiniteSiteQuantumChemistry](/hqiv-lean/docs/Hqiv/QuantumChemistry/FiniteSiteQuantumChemistry.html) |
| **H₂ first-principles scaffold** (two-site shell chemistry; `referenceM=4` anchor theorem) | [H2](/hqiv-lean/docs/Hqiv/QuantumChemistry/H2.html) |
| **Geometric TSP oracle prototype** (n-arity arc tour search with exact small-`n` checker) | `scripts/geometric_tsp_oracle.py` |
| **Directed torus ATSP oracle prototype** (intrinsic + oblique edge-tilted geometry modes with narrow-arc minimizers, recursive intercepts, and rapidity-inequality reverse-flip-prune rounds) | `scripts/directed_torus_atsp_oracle.py` |
| **Rapidity-first ATSP oracle prototype** (research-first shell ladder with periodic slot families, OSHoracle-style flip pruning, optional local completion, and shell-periodicity telemetry) | `scripts/rapidity_first_atsp_oracle.py` |
| **Rapidity-first ATSP benchmark harness** (compares rapidity-first vs directed-torus runs, uses known exact/best-known/lower-bound references when available, and caches exact 11/12-city optima by matrix hash for reuse) | `scripts/benchmark_rapidity_first_atsp.py` |
| **Named TSPLIB ATSP runner** (parses explicit full-matrix TSPLIB ATSP instances, reads published best-known values, and reports ratio vs best-known together with the Lean-style `1 + n^(1/n)` envelope) | `scripts/run_tsplib_atsp_named.py` |
| **Edge-space ATSP oracle prototype** (treats directed edges as dimensions, projects edge-priority states to tours, and applies LB/UB hard+soft prune boundaries) | `scripts/edge_space_atsp_oracle.py` |
| **Dual-oracle ATSP benchmark harness** (runs directed-torus and edge-space solvers on identical matrices and reports hybrid best-of-two stats) | `scripts/benchmark_atsp_dual_oracles.py` |
| **ATSP step-down benchmark harness** (measures no-prune geometric runtime against exact `n→floor` brute-force chains with rapidity-guided city elimination) | `scripts/benchmark_atsp_stepdown.py` |
| **Rapidity prune safety checker** (exact counterexample search for witness-safety of rapidity-dominated-edge pruning scales) | `scripts/check_rapidity_prune_safety.py` |

See the [API documentation](/hqiv-lean/docs/) for the full generated Lean 4 docs.
