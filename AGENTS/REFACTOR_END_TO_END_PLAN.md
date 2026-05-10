# Refactor: one coherent end-to-end story (light cone → NS/YM)

## Goal

- **Clean:** reduce duplicate narrative, clarify what is “spine” vs “satellite” (SAT, CNF, proteins, etc.).
- **One thread:** a **single** optional import chain that walks the physics in logical order, without replacing `HQIVLEAN.lean` overnight (it stays the build-all superset for CI).

## Delivered in this pass

- `Hqiv/Story/Chapter01_*` … `Chapter08_*` — **linear** imports; each chapter adds one layer.
- `HQIVStory.lean` — one import of the last chapter (pulls the full spine).
- `lake build HQIVStory` — dedicated target in `lakefile.toml`.

## Story order (chapters)

| # | Module | Role |
|---|--------|------|
| 1 | `Chapter01_Foundation` | Null-lattice + `OctonionicLightCone`, auxiliary field `φ` / temperature ladder |
| 2 | `Chapter02_Metric` | `HQVMetric` (lapse, γ, Friedmann interface) |
| 3 | `Chapter03_ConservedShell` | `Conservations` (structure from counting over O) |
| 4 | `Chapter04_MassLadder` | `HarmonicLadderMass` (shell → α_eff → binding scales) |
| 5 | `Chapter05_Baryogenesis` | `BaryogenesisCore` (QCD/lock-in shells, Ω_k calibration, no paper η) |
| 6 | `Chapter06_Fluid` | `HQIVFluidClosureScaffold` (effective fluid; **not** classical NS proof) |
| 7 | `Chapter07_PatchQFT` | `PatchQFTBridge` (local net, Minkowski corners, scaffold microcausality) |
| 8 | `Chapter08_ClayMillennium` | `Hqiv.Bridge.LeanDojoClayMillennium` (Dojo YM/NS *statements* + witness rules) |

## Phased cleanup (not all done in one PR)

1. **Spine only (done first):** Story modules + `HQIVStory` target. No file moves, no renames of existing theorems.
2. **Triage `HQIVLEAN.lean`:** mark sections in comments (geometry / physics / QM / algebra / archive) or split into `HQIVLEAN/Parts/*.lean` re-exporting — *later*.
3. **Deprecate duplicate paths:** where two modules prove the same lemma, keep one; use `@[deprecated]` or doc pointers — *later*.
4. **NS / YM truth:** the Story ends at **formal problem statements** + your witness theorems; proving Fefferman or `QuantumYangMillsTheory` is still **out of band** to the Story imports (see `LeanDojoClayMillennium` module doc).
5. **Default CI:** keep default targets as today; add optional `HQIVStory` in CI if desired (follow-up).

## Conventions

- `Hqiv/Story/ChapterNN_*.lean` may be **import-only** + module doc: no new `def` unless needed to avoid import cycles.
- “Satellite” work (SAT rapidity, competition solvers, archive) **stays** out of `Story` unless a future chapter is explicitly added.

## Related

- [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md)
- [NAVIER_STOKES_HQIV_NARRATIVE.md](./NAVIER_STOKES_HQIV_NARRATIVE.md)
- [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md)
