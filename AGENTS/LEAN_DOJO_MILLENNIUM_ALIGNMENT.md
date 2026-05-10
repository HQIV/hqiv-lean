# Lean Dojo Millennium formalizations (compatibility requirement)

This note fixes a **documentation standard** for agents and maintainers working on anything that touches the **Clay Millennium Prize Problems** in Lean.

## Canonical target

The community formalization [**lean-dojo/LeanMillenniumPrizeProblems**](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) (“Formalization of the Millennium Problems in Lean 4”) is the **reference surface** for how those problems are stated in dependent type theory.

**In this repository (Lean 4.28.0, Mathlib v4.28.0):** a vendored **Yang–Mills + Navier–Stokes** slice of those statements (definitions only) lives under [`Vendored/LeanDojoMillennium`](../Vendored/LeanDojoMillennium/README.md). Build with `lake build LeanDojoMillennium`; entry module `LeanDojoMillenniumIndex` imports `Problems.YangMills.Millennium` and `Problems.NavierStokes.Millennium` for connection work.

## What “satisfy” means here (not automatic import)

- **Substantive claims** (e.g. “we prove RH”, “we prove BSD”, “we close NS globally”) must be **reducible to** or **directly comparable with** the problem statements as formalized in that repository—or a **clearly identified Mathlib extension** of the same mathematical content. Agents must **not** treat HQIV-specific scaffolds (`lambdaHQIV`, lattice zeta, `effCorrected`, fluid `Prop` bundles, …) as interchangeable with those statements without an explicit bridge theorem.
- **Probe-level work** in this repo (hypothesis records, cosine coefficients, execution scripts) is **explicitly not** a resolution of a Millennium problem; it remains subject to this rule only when someone **promotes** a claim to “theorem-shaped” progress toward a prize problem.
- **Practical workflow:** before adding a `theorem` whose *English name or docstring* suggests a Millennium resolution, check the corresponding module in [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) for naming, hypotheses, and equivalences; prefer **reusing** or **importing** those definitions when the dependency graph allows, or document why a parallel formulation is needed and how it maps.

## HQIV-specific honesty

All existing HQIV bridges remain **conditional** (`Prop` bundles, narrative roadmaps). Satisfying the Lean Dojo standard means: **no overclaim** relative to those formal targets—not that every file imports the external repo today.

## Related agent docs

| Doc | Role |
|-----|------|
| [THEOREMS.md](./THEOREMS.md) | What is actually proved **here** |
| [ASSUMPTIONS.md](./ASSUMPTIONS.md) | Bridge assumptions, `sorry`s, script trust |
| [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md) | Four-probe narrative (RH / YM / NS / Hodge); complexity-class prose is **not** part of the active roadmap (see `archive/`) |
| [MODULAR_FORMS_LADDER.md](./MODULAR_FORMS_LADDER.md) | Modular forms / L-functions / BSD thread (long horizon) |
| [BSD_RN_RAMANUJAN_BRIDGE.md](./BSD_RN_RAMANUJAN_BRIDGE.md) | BSD strategy via ℝⁿ + Ramanujan-type curvature bridge (not a proof) |
| [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) | Manifold ↔ lattice zeta milestones |
