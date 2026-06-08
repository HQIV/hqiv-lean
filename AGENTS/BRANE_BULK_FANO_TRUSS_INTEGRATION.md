# Brane–bulk Fano-truss integration (HQIV-LEAN ↔ One-Octonion narrative)

This note is an **agent peg** for the optional Lake target `HQIVBraneBulkStrongSector` and the lightweight module `Hqiv.Physics.BraneBulkFanoTruss`. It mirrors the honesty style of `THEOREMS.md` and `FUREY_ALIGNMENT_GAP_ANALYSIS.md`: **proved** vs **partial** vs **open**, with external brane–bulk claims quarantined until promoted in Lean.

**Build:** `lake build HQIVBraneBulkStrongSector`  
**Zenodo bridge (hypothesis layer):** [One-Octonion Brane-Bulk Framework, record 19709652](https://zenodo.org/records/19709652)

## Build hygiene (read this)

- **One heavy build at a time.** `HQIVYangMillsPackage` already pulls `SO8ClosureAbstract` and the Lie-closure graph; Lake will spawn many `lean` children. That is normal. **Starting a second** `lake build HQIVBraneBulkStrongSector` (or `HQIVSO8Closure`) while the first is running **doubles** RAM and CPU and looks like “30 Lean tasks.”
- **Do not background long `lake build`** in the agent unless you are sure nothing else is compiling.
- **Optional cap:** set `LEAN_NUM_THREADS` lower in the environment before `lake build` if each `lean` child is too heavy (trades wall time for RAM).
- **Generated `G₂ ∪ {Δ}` Lie file** is *not* re-imported in `HQIVBraneBulkStrongSector.lean` on purpose (avoids an extra duplicate compile of the heaviest algebra). Build it when you need it: `lake build Hqiv.Algebra.G2DeltaGeneratedLie` or `lake build HQIVSO8Closure`.

## Status matrix

| Claim / deliverable | Lean peg | Status | Notes |
|---------------------|----------|--------|--------|
| Null-lattice mode area \(A(m)=4(m+1)(m+2)\) | `Hqiv.available_modes`, `Hqiv.available_modes_eq`, `Hqiv.Physics.braneTrussModeArea_eq` | **proved** | `BraneBulkFanoTruss` re-exports as `braneTrussModeArea`. |
| Mode area vs resonance `shellSurface` | `Hqiv.Physics.braneTrussModeArea_eq_four_mul_shellSurface` | **proved** | `shellSurface m = (m+1)(m+2)` in `FanoResonance`. |
| Fano incidence / seven lines | `Hqiv.Physics.FanoLine`, `fanoStandardLine` | **proved** | Combinatorial PG(2,2) table; not continuum truss mechanics. |
| Forced \(\alpha=3/5\), \(\gamma=2/5\) | `Hqiv.latticeAlphaRatio_eq_alpha`, `Hqiv.alpha_gamma_forced_pair` | **proved** | See `OctonionicLightCone` / `AlphaGammaForcedByLattice`. |
| `G₂ ∪ {Δ}` generates \(\mathfrak{so}(8)\) | `Hqiv.Algebra.g2DeltaGeneratedLie`, `Hqiv.Algebra.g2DeltaGeneratedLie_eq_so8LieSubalgebra` | **proved** | Build `Hqiv.Algebra.G2DeltaGeneratedLie` or `HQIVSO8Closure` — **not** imported by `HQIVBraneBulkStrongSector` (hygiene: avoid duplicate heavy compile). |
| Phase-lift scalar “cost” slot at shell `m` | `Hqiv.Physics.automorphismEnergyCostAtShell`, `automorphismEnergyCostAtShell_pos` | **proved** | Alias to `phaseLiftCoeff`; **not** Planck/YM gap identification (see `G2AutomorphismEnergyCost` doc). |
| Cyclic Wilson defects ↔ `L_O_kinetic` sandwich | `Hqiv.Physics.discrete_kinetic_two_sided_cyclic_wilson` | **proved** | `DiscreteYMConfinement` repackages `ActionHolonomyGlue` (abelian ℝ). |
| Horizon driver for future Wilson counting | `Hqiv.Physics.holonomyAreaDriver` | **def** (= `shellSurface`) | Hook only; no Wilson loop theorem yet. |
| Packaged YM-facing carrier | `Hqiv.Physics.HQIVYangMillsPackage`, `hqivYangMillsPackage` | **proved (finite-dim package)** | Module doc disclaims analytic Clay YM existence. |
| O–Maxwell kinetic ↔ cyclic Wilson squares | `Hqiv.Physics.L_O_kinetic_two_sided_cyclic_wilson_sq` | **proved (abelian ℝ)** | `ActionHolonomyGlue`. |
| Full `su(3)` chart Lie law for all `(a,b)` | `StrongColorSu3LieChartLaw` (`colorHalfGellMannFull_lieBracket_eq_I_smul_f_sum`), under `HQIVStrongColorSu3Certificate` | **proved (optional cert)** | Auto-generated 64-case matrix certificate + combiner; not in default `HQIVLEAN`. |
| Non-abelian plaquette transport / confinement bound | — | **open** | Planned: extend `DiscretePlaquetteHolonomy` + color embed. |
| Auxetic Fano truss, \(\nu=-1\) | — | **hypothesis** | External framework; not a Lean theorem. |
| YM mass gap = G₂ automorphism energy at \(\ell_P\) | — | **hypothesis** | Requires new cost functional bridge from `phaseLiftDelta` / action. |
| Strong CP, graviton spectrum, universal transit fractions | — | **hypothesis** | Quarantine until named modules + proofs. |

## Immediate commands

```bash
lake build Hqiv.Physics.ActionHolonomyGlue
lake build HQIVStrongColorSu3Certificate
lake build HQIVBraneBulkStrongSector
```

## Next formalization targets (short list)

1. ~~Global `su(3)` chart Lie law on the `3×3` chart~~ — **landed** in `StrongColorSu3LieChartLaw` (optional `HQIVStrongColorSu3Certificate`; regen `scripts/gen_strong_color_su3_lie_chart_law.py`). **Still open downstream:** lift identities through `colorGellMannEmbed` to carrier-scale statements beyond the packaged `colorGellMannEmbed_chart_lieBracket_smul` scaffold; non-abelian plaquette / Wilson hooks in this note’s matrix.
2. ~~`G2AutomorphismEnergyCost.lean`~~ — **landed** as `Hqiv/Physics/G2AutomorphismEnergyCost.lean` (alias + positivity; extend only with an explicit Planck/YM bridge if you add a named hypothesis).
3. ~~`DiscreteYMConfinement.lean`~~ — **landed** as `Hqiv/Physics/DiscreteYMConfinement.lean` (Wilson/kinetic sandwich + `holonomyAreaDriver` hook).
4. Non-abelian plaquette transport on the color embed; finite Wilson loops whose cost scales with `holonomyAreaDriver` / detuned surfaces (no fitted potential).
