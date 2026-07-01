# CKM / PMNS from Fano cycle overlaps — discharge programme

**Status:** **Open (scaffold).** This is the right *kind* of next discharge: replace phenomenological mixing tables with **discrete overlap data** on the null-lattice / Fano incidence graph, with CP phases from **fiber holonomy rows**—not a PDG matrix fit.

**Read with:** [PATCH_ONTOLOGY.md](./PATCH_ONTOLOGY.md) § gauge consistency, [TUFT_HOPF_SPECTRAL_MINING.md](./TUFT_HOPF_SPECTRAL_MINING.md) T5/T10, [ASSUMPTIONS.md](./ASSUMPTIONS.md) §2b.

---

## TUFT target (continuum language)

Nielsen's TUFT programme derives CKM/PMNS from **admissible-cycle overlaps** in \(H^*(CP^4)\), with CP phases from **fibre holonomy**. HQIV does **not** re-prove that smooth theorem. The discrete analogue is:

| Continuum object | HQIV discrete counterpart |
|------------------|---------------------------|
| Admissible cycles on \(CP^4\) | Admissible triples on Fano / null-lattice vertices (`generationVerticesFormAdmissibleCycle`) |
| Intersection numbers | Overlap weights on the incidence graph (`admissible_cycle_overlap` predicate) |
| Holonomy phase | Per-row holonomy RHS \((48,96,144)/91\) scaled by shell torsion (`holonomyRowRhs`, `DiscreteCycleHolonomyContribution`) |
| CKM/PMNS unitary | **Not yet:** full \(3\times3\) unitary from overlaps; only phase-ratio scaffold |

---

## What is already proved (scaffold)

| Lean object | Module | Meaning |
|-------------|--------|---------|
| `holonomyRowRhs` / generation holonomy rows | `ContinuousXiCoupling`, `HopfShellBeltramiMassBridge` | Light / middle / heavy row ratios on the TUFT chart |
| `FanoCycleHolonomyForShell` | central TUFT bridge | Per-winding phase lifts attached to Fano cycles |
| `generationVerticesFormAdmissibleCycle` | `HopfShellBeltramiMassBridge` | Concrete combinatorial predicate (replaces universal `True`) |
| `DiscreteCycleHolonomyContribution` | same | Carries `admissible_cycle_overlap` + holonomy contribution |
| `T10MixingPhaseMatrix` / `assembleT10MixingPhaseMatrix` | `HopfShellBeltramiMassBridge` | 3-slot phase matrix; `heavyToMiddle = 2`, `middleToLight = 3` (proved) |
| `assembleT10MixingPhaseMatrix_*_eq_holonomy_torsion` | same | Phase ratios tied to holonomy × torsion |
| `t10PMNSAngle12` / `t10PMNSUnitaryReal` | same | **Diagnostic** PMNS-angle scaffold from phase ratios—not PDG validation |
| `t10NeutrinoOverlapMatrix` / `assembleT10PMNSMixingReadout` | same | Overlap-matrix assembler; export uses TUFT T10 masses |

**Honest boundary:** neutrino absolute scale and \(\Delta m^2_{21}\) diagnostics in [TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md](./TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md) use this scaffold; **CKM quark mixing is not closed**. Do not claim “TUFT mixing derived” until overlap→unitary is proved without PDG imports.

---

## Discharge checklist (agent-facing)

Work toward **patch-closed** mixing, not continuum \(H^*(CP^4)\) re-proof:

1. **Overlap weights** — ✅ **Landed (spine):** `HqivSpine.Physics.FanoMixingWeights` defines `overlap v w` as the count of shared Fano lines, **forced** by the `Foundation.Fano` incidence theorems to `1` off-diagonal (`overlap_distinct`) and `3` diagonal (`overlap_self`). The leading mixing fraction is the graph ratio \(\sin^2\theta = \mathrm{overlap}(v,w)/\mathrm{overlap}(v,v) = 1/3\) (`fano_sinSq_eq_overlap`) — counts, not fitted sines — feeding a unitary CP-violating `ckmFano`. **Remaining:** this is the *democratic baseline* \(1/3\); the measured hierarchy is the mass-ratio refinement layered on top.
2. **Phase assembly** — Extend `T10MixingPhaseMatrix` to full off-diagonal phases from `HolonomyPhaseCarrier` + imprint phases (`curvatureImprintAlpha`, `PhaseMap`).
3. **Unitary certificate** — ✅ **Landed (spine):** `HqivSpine.Physics.CKMMixingMatrix` proves the full \(3\times3\) matrix \(V = R_{23}R_{13}(\delta)R_{12}\) is unitary (`ckm_unitary_apply : VᴴV = 1`) as a product of unitary plane rotations, with the Jarlskog invariant in closed form \(J = c_{12}c_{13}^2c_{23}s_{12}s_{13}s_{23}\sin\delta\) (`ckm_jarlskog`). Assembled from the spine mass-ratio angles (`ckmSpine_unitary`); CP violation (`ckmSpine_cp_violation`) is non-zero iff the holonomy phase is genuine. **Remaining:** fix the angle/phase *values* from overlap weights (step 1) rather than mass-ratio inputs + free \(\delta\).
4. **CP phase** — ✅ **Landed (spine):** `HqivSpine.Physics.CPHolonomyPhase` derives the CP-odd phase from a complex U(1) holonomy. The Jarlskog invariant \(J = \mathrm{Im}(V_{us}V_{cb}V_{ub}^*V_{cs}^*)\) is proved **rephasing-invariant** (`jarlskog_rephasing` — the phase cannot be rotated away), vanishes for a real CKM (`jarlskog_real`), and equals \((\prod|V|)\sin\delta\) for one fibre-holonomy phase (`jarlskog_phase`); CP violation \(\iff\) non-trivial loop holonomy. Abelian Wilson loop = flux phase, flat iff flux \(\in 2\pi\mathbb{Z}\) (`u1Holonomy_eq_one_iff`).
5. **Paper row** — Keep Table claim status **Open (scaffold)** until steps 1–3 close for at least one sector without PDG matrix injection.

---

## Anti-patterns

- Importing PDG \(|V_{ub}|\), \(\sin^2\theta_{12}\), **etc.** as Lean defs and calling it “derived mixing.”
- Claiming TUFT's smooth intersection-form theorem because holonomy rows match \((48,96,144)/91\).
- Conflating **electroweak** \(\sin^2\theta_W = 168/725\) (geometric lock-in) with **flavour** CKM/PMNS.

---

## Related docs

- [THEOREMS.md](./THEOREMS.md) — `assembleT10MixingPhaseMatrix_*`, strong-color chart (separate thread)
- [TUFT_HOPF_SPECTRAL_MINING.md](./TUFT_HOPF_SPECTRAL_MINING.md) — T5, T10 alignment table
- `papers/tuft_sm_lagrangian/hqiv_tuft_sm_lagrangian_synthesis.tex` — claim table row **CKM/PMNS from Fano cycle overlaps — Open (scaffold)**
