# Lean Dojo Millennium (vendored YM + NS)

Vendored from the local 4.28 build at `~/Repos/leandojo/LeanMillenniumPrizeProblems`
(same content as [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems),
with `lean-toolchain` `v4.28.0` and Mathlib `v4.28.0`).

- **License:** `LICENSE.LeanDojoUpstream` (Apache-2.0, upstream project).
- **Umbrella import:** `import LeanDojoMillenniumIndex` (see `LeanDojoMillenniumIndex.lean`).

## Clay statements to connect

| Area | Main module | Core definition |
|------|-------------|-----------------|
| Yang–Mills | `Problems.YangMills.Millennium` | `MillenniumYangMills.YangMillsExistenceAndMassGap` |
| Navier–Stokes | `Problems.NavierStokes.Millennium` | re-exports bounded-domain / Millennium statements in that file chain |

Supporting NS infrastructure lives under `Problems/NavierStokes/` (Definitions, Torus, `AdjointSpace` from SciLean, etc.); YM needs `Problems/YangMills/Quantum.lean` (Wightman / QFT data layer).

## Build

```bash
lake build LeanDojoMillennium
```

Policy note: alignment with these statements is documented in `AGENTS/LEAN_DOJO_MILLENNIUM_ALIGNMENT.md`.
