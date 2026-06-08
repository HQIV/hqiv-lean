# Modular / theta bridge — **action plan** (execute in order)

**Sketch → plan:** [MODULAR_THETA_CURVATURE_BRIDGE.md](./MODULAR_THETA_CURVATURE_BRIDGE.md)  
**Ladder alignment:** [MODULAR_FORMS_LADDER.md](./MODULAR_FORMS_LADDER.md) (M0–M5)  
**Policy:** no Clay-scale claims without proofs — hypothesis bundles and Mathlib wiring only.

---

## Phase P0 — Vocabulary & pointers (documentation)

| # | Task | Status |
|---|------|--------|
| P0.1 | Single bridge doc with honest Mathlib vs HQIV map | ✅ [MODULAR_THETA_CURVATURE_BRIDGE.md](./MODULAR_THETA_CURVATURE_BRIDGE.md) |
| P0.2 | Action plan (this file) + ladder cross-link | ✅ |
| P0.3 | `THEOREMS.md` index row for coefficient bridge | ✅ (with scaffold merge) |

---

## Phase P1 — Lean coefficient stream (M1 start)

| # | Task | Status |
|---|------|--------|
| P1.1 | Expose `θ` formal coefficient `thetaZ8FormalCoeff = r8` | ✅ `Hqiv.Algebra.ModularThetaBridgeScaffold` |
| P1.2 | Hypothesis `CoeffsAgreeWithR8` + trivial `thetaZ8FormalCoeffComplex` | ✅ same module |
| P1.3 | Import in `HQIVLEAN.lean` | ✅ |
| P1.4 | `lake build HQIVLEAN` | ✅ (verify after merge) |

**Next (not done in this pass):** Mathlib search for `ModularForm` / Jacobi θ matching weight-4 and `r₈`; add `import` only when dependency cost is acceptable.

---

## Phase P2 — Mathlib modular form hook (M2–M4)

| # | Task | Status |
|---|------|--------|
| P2.1 | Locate Mathlib defs: theta lattice, Eisenstein, `ModularForm` level 1 | ✅ see pointers in [MODULAR_THETA_CURVATURE_BRIDGE.md](./MODULAR_THETA_CURVATURE_BRIDGE.md); entry points `Mathlib.NumberTheory.ModularForms.Basic`, `…/QExpansion` |
| P2.2 | Analytic hook: `thetaZ8LSeriesCoeff` + abscissa bound | ✅ `Hqiv.Algebra.ThetaZ8LSeriesScaffold` (`abscissaOfAbsConv_thetaZ8LSeriesCoeff_le_nine`) |
| P2.3 | `q`-expansion **target** wired to Mathlib (`ModularFormClass.qExpansion` ↔ `r8`) | 🔶 `ThetaZ8ModularRealization` (structure); **proved** `Nonempty ThetaZ8ModularFormWitness` via `E 4` — **not** `r8` match |
| P2.4 | Completed L / FE: **trivial** Dirichlet branch = Λ symmetry | ✅ `ThetaCompletedLFunctionalScaffold` (`completedLFunction_modOne_one_sub`); weight-4 `Λ(4-s)=Λ(s)` as **hypothesis only** |

---

## Phase P3 — Fourier patch ↔ L-data (narrative glue)

| # | Task | Status |
|---|------|--------|
| P3.1 | Doc link: `fourierPatchPeakCorrelation` / `moirePatchScoreSlope` do **not** imply Hecke | ✅ bridge doc |
| P3.2 | L-series from `r8` coeffs (Mathlib `LSeries` stream) | ✅ `ThetaZ8LSeriesScaffold` (separate from HQIV Dirichlet `HQIVLSeriesAnalytic`) |

---

## Phase P4 — Curvature / heat (separate track)

| # | Task | Status |
|---|------|--------|
| P4.1 | Cross-link `HQIVHeatFlowDeformation` ↔ [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) | ⬜ short paragraph |
| P4.2 | Hypothesis record: Laplacian spectrum ↔ “modal history” | ⬜ only if needed |

---

## Execution checklist (maintainer)

- [ ] After P1 merge: update `MODULAR_FORMS_LADDER.md` snapshot “In place” if desired.
- [ ] Run `lake build HQIVLEAN` on PR.
- [ ] Optional: `scripts/` probe comparing `r8 m` to OEIS / table for small `m` (already partially in `test_integer_lattice_shell_count8.py`).

---

## Related Lean modules

| Module | Role |
|--------|------|
| `Hqiv.Algebra.ModularThetaBridgeScaffold` | `thetaZ8FormalCoeff`, `CoeffsAgreeWithR8` |
| `Hqiv.Algebra.ThetaZ8LSeriesScaffold` | `thetaZ8LSeriesCoeff`, `abscissaOfAbsConv_thetaZ8LSeriesCoeff_le_nine` |
| `Hqiv.Algebra.ThetaCompletedLFunctionalScaffold` | `completedLFunction_modOne_one_sub`, `WeightFourCompletedLInvolutionHypothesis` |
| `Hqiv.Algebra.ThetaZ8ModularFormScaffold` | `ThetaZ8ModularFormWitness`, `thetaZ8LevelOneE4Witness`, `ThetaZ8ModularRealization`, `exists_thetaZ8_modular_realization` |
| `Hqiv.Algebra.IntegerLatticeShellCount8` | `r8`, `r8_le_two_mul_add_one_pow_eight` |
| `Hqiv.Algebra.OctonionSphereFourierPatch` | Fourier concentration; `moirePatchScoreSlope` |
| `Hqiv.Physics.HQIVDirichletModularScaffold` | `hqivCoeff` / Dirichlet (separate channel) |
