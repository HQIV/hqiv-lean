# Roadmap: modular forms, L-functions, and BSD (status-tracked ladder)

This document is the **coherent thread** for analytic number theory in HQIV_LEAN after the generalized scaffolding (Dirichlet series, rapidity slots, heat-flow packaging): **modular forms**, **L-series**, and the **Birch–Swinnerton-Dyer (BSD)** layer—without conflating any of it with a finished proof.

**BSD bridge strategy (active direction):** [BSD_RN_RAMANUJAN_BRIDGE.md](./BSD_RN_RAMANUJAN_BRIDGE.md) — **ℝⁿ** ambient space, **arbitrary Ramanujan-type curvature** (slots + growth hypotheses), and the path from HQIV’s **monogamic “Ramanujan”** sums toward **BSD-compatible** L-data. **Not** a proof of BSD.

**Compatibility:** substantive claims toward a Clay problem must align with [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems); see [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md).

**Nearby narratives:** Riemann/zeta geometry in [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) §4; RH probe in [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md); Dirichlet/analytic scaffolds in `Hqiv.Physics.HQIVDirichletModularScaffold`, `HQIVLSeriesAnalytic`. **Theta / modular / curvature story (honest gap map):** [MODULAR_THETA_CURVATURE_BRIDGE.md](./MODULAR_THETA_CURVATURE_BRIDGE.md).

---

## 0. Effective narrative (what we are *not* claiming yet)

1. **Modular forms** (classical or adelic) live in Mathlib in various degrees of generality; **HQIV** currently supplies **discrete** coefficients (`hqivCoeff`, octonionic zeta terms) and **hypothesis** packaging for functional equations—not a proved equivalence with a given `ModularForm`.
2. **L-functions** attached to those coefficients are scaffolded (`hqivDirichletSeries`, `LSeries` alignment for \(\Re(s)>1\) in `HQIVLSeriesAnalytic`); **continuation / FE** remain hypothesis-level where stated.
3. **BSD** concerns rational points and the order of vanishing of the **L-function of an elliptic curve**; HQIV has **no** elliptic-curve arithmetic layer wired to shell zeta. The **proposed** narrowing of that gap—**ℝⁿ + arbitrary Ramanujan-type curvature data feeding coefficient control**, thence toward modular **L** and BSD—is spelled out only in [BSD_RN_RAMANUJAN_BRIDGE.md](./BSD_RN_RAMANUJAN_BRIDGE.md) (milestones **B0–B4**).

---

## Status snapshot (now)

### In place

- **Theta coefficient bridge (M1):** `Hqiv.Algebra.ModularThetaBridgeScaffold` — `thetaZ8FormalCoeff` (= `r8`), `CoeffsAgreeWithR8`, `thetaZ8FormalCoeffComplex`; plan in [MODULAR_THETA_ACTION_PLAN.md](./MODULAR_THETA_ACTION_PLAN.md).
- **F/G rapidity scaffolds:** `SpatialSliceRapidityScaffold` (spiral domains, `hqivCoeff` inputs).
- **Dirichlet / L-series layer:** `HQIVDirichletModularScaffold`, `HQIVLSeriesAnalytic` (convergence, analytic strips where proved).
- **Heat / Tao–Rodgers packaging:** `HQIVHeatFlowDeformation`, `TaoRodgersNewmanScaffold`, `HQIVRHClosureScaffold` (hypothesis-shaped; not classical \(\Lambda\)).
- **Execution probes:** `scripts/factor_from_curvature.py`, zeta-related witnesses (non-theorem data).

### Not in place

- Proved **modularity** of HQIV coefficients.
- Proved **functional equation** / **critical-line** consequences for a completed HQIV L-object matching classical definitions.
- **Elliptic curves**, **Heegner points**, or **BSD** arithmetic in Lean in this repo.
- Automatic **import** of [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) (dependency choice is separate); **alignment** is still required by policy when claiming progress.

---

## Ladder (milestones)

| Milestone | Goal | Done when |
|-----------|------|-------------|
| **M0 — Vocabulary** | Same words in docs: modular form, cusp form, L-series, conductor, BSD rank/L. | This file + module docstrings cite Mathlib names where used. |
| **M1 — Coefficient channel** | One **canonical** `ℕ → ℝ` or `ℕ → ℂ` stream from HQIV (e.g. frozen `hqivCoeff` pipeline) documented as *candidate* modular coefficients. | Dedicated subsection in `HQIVDirichletModularScaffold` or split module + `THEOREMS.md` row. |
| **M2 — L-series lock** | `LSeries` / `holo` / abscissa lemmas extended as far as Mathlib allows for that stream. | Proved strips documented; **no** FE unless proved. |
| **M3 — Functional equation (hypothesis)** | Explicit `Prop` bundle mirroring classical completed L symmetry (cf. `ThreeSpiralGammaSymmetry`-style hooks already in scaffold). | Named hypothesis record + `ASSUMPTIONS.md` entry. |
| **M4 — Modular lift (hypothesis or Mathlib)** | Statement that coefficients match a specified modular form **or** bounded failure (not modular) — **not** claimed without proof. | Lemma or `Prop` + counter-probe doc. |
| **M5 — BSD thread (optional, hardest)** | Only after M2+: separate roadmap note tying **elliptic-curve L** to HQIV—must cite Lean Dojo BSD formal statement if claiming equivalence. | **Strategy doc:** [BSD_RN_RAMANUJAN_BRIDGE.md](./BSD_RN_RAMANUJAN_BRIDGE.md) (B0–B4); elliptic interface still **open**. |

**BSD bridge sub-ladder (see dedicated doc):**

| Milestone | Goal |
|-----------|------|
| **B0–B4** | ℝⁿ bookkeeping, **arbitrary** curvature hypotheses, Ramanujan-**type** coefficient dictionary vs classical Petersson, L-lock toward BSD shape. |

---

## Honesty table (agents)

| Question | Answer |
|----------|--------|
| Is HQIV’s Dirichlet series a known modular form? | **Not proved** here. |
| Does this repo prove BSD or RH? | **No** — see [THEOREMS.md](./THEOREMS.md) and Lean Dojo alignment doc. |
| Where does modular geometry meet shells? | **Narrative + probes** in `MANIFOLD_ZETA_ROADMAP` §4 and this ladder; formal glue is **open**. |
| Is there a documented path toward BSD? | **Strategy only:** [BSD_RN_RAMANUJAN_BRIDGE.md](./BSD_RN_RAMANUJAN_BRIDGE.md) — ℝⁿ + Ramanujan-type curvature bridge; **not** a proof. |

---

## Maintainer actions

When a milestone lands: update this snapshot, `THEOREMS.md`, `ASSUMPTIONS.md` (new `Prop`s), and add a cross-link from `MILLENNIUM_UNIFIED_NARRATIVE.md` if the four-probe story changes materially.
