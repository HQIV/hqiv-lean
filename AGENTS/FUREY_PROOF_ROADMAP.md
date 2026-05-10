# Furey proof roadmap (Lean-facing audit)

This document is the **documentation-only** companion to
[`FUREY_ALIGNMENT_GAP_ANALYSIS.md`](./FUREY_ALIGNMENT_GAP_ANALYSIS.md). It restates
Furey-style claims in **proof-sized pieces**, assigns each piece an honest status
relative to the current HQIV Lean corpus, and lays out a **staged theorem ladder**
for future formal work—without implying that any stage is already complete unless
stated.

**External references (paper program, not Lean obligations):** Furey thesis and
related work (e.g. arXiv:1611.09182); *Phys. Lett. B* 785 (2018) 84–89 /
arXiv:1910.08395 (complex octonions \(\mathbb{C}\otimes\mathbb{O}\), minimal left
ideals, \(SU(3)_c\times U(1)_{em}\), three generations in a 64\(\mathbb{C}\)-dim
split); Furey & Hughes (e.g. arXiv:2409.17948) on \(\mathbb{C}\otimes\mathbb{H}
\otimes\mathbb{O}\), trialities, and symmetry-breaking cascades.

---

## Status legend

Use these labels consistently in audits and PR descriptions.

| Label | Meaning |
|--------|---------|
| **proved** | Theorem or definition in Lean with the intended mathematical content (not merely naming). |
| **bookkeeping** | Correct finite counting, module structure, or witness packaging; does not yet carry the full representation-theory or Clifford content of the paper claim. |
| **placeholder** | Explicit stub (`True`, `Prop := True`, definitional `0`, etc.) or prose target; must not be cited as the paper result. |
| **narrative only** | Compatibility language in docs or comments; no corresponding formal object. |
| **absent** | No Lean module or no Mathlib-backed layer wired into HQIV for this claim. |

---

## Stage 0 — Current HQIV-native anchor (accepted cite)

**Goal:** One honest bundle agents can point to before any Furey-specific Clifford
layer exists.

| Component | Lean location | Status | Notes |
|-----------|---------------|--------|-------|
| Real 8s carrier | `Hqiv.Algebra.OctonionSpinorCarrier` (`OctonionSpinorCarrier`, `octonionSpinorCarrier_dim`) | **proved** | `Fin 8 → ℝ`; dependency-light by design. |
| SM-facing matrices + charges | `Hqiv.Algebra.SMEmbedding` | **proved** + **placeholder** | `su2_generators_in_so8`, `su2_bracket_12`, `hyperchargeGenerator`, `hypercharge_assignments_correct`, charge witnesses (`up_component_charge_two_thirds`, …) are real. `G2_contains_SM_subgroup : True` and `hyperchargeBlockCorrect : Prop := True` are **placeholders**. |
| Triality labels | `Hqiv.Algebra.Triality` (`trialityCycle`, `triality_cycle_order_3`, `card_so8_eight_dim_irreps`, `exactly_three_fermion_generations_from_HQIV_axioms`) | **bookkeeping** | Order-3 cycle on `So8RepIndex := Fin 3`. `triality_preserves_bracket` is `rfl` on matrices—**not** Spin(8) outer automorphism on \(\mathfrak{so}(8)\). |
| Packaged gauge object | `Hqiv.Physics.HQIVYangMillsPackage` (`HQIVYangMillsPackage`, `hqivYangMillsPackage`, …) | **proved** (as packaged record) | Bundles carrier, basis/bracket expansion fields, membership of \(G_2\)/\(\Delta\)/`SU(2)_L`/hypercharge, triality count, \(\alpha/\gamma\), rapidity phase bridge, unification `Prop`. See `AGENTS/THEOREMS.md` § “Canonical Yang-Mills package”. |
| Octonion multiplication / \(\mathbb{R}^8\) model | `Hqiv.Algebra.OctonionBasics`, `Hqiv.OctonionLeftMultiplication` | **proved** | Fano-plane matrices; not bundled `Octonion ℝ` in Mathlib (see module doc). |
| Generated Lie algebra from \(G_2\cup\{\Delta\}\) equals the honest Euclidean \(\mathfrak{so}(8)\) model | `Hqiv.Algebra.G2DeltaGeneratedLie` | **proved** | Main identification: `Hqiv.Algebra.g2DeltaGeneratedLie_eq_so8LieSubalgebra` (see `AGENTS/THEOREMS.md`). |
| Matrix SO(8) closure certificate | `Hqiv.Algebra.SO8ClosureAbstract`, `Hqiv.GeneratorsLieClosure*`, `HQIVSO8Closure` target in `lakefile.toml` | **proved** / **heavy build** | Use smallest `lake` target that contains the import chain you need (`AGENTS/README.md`). |
| Strong-color \(\mathfrak{su}(3)\) chart | `Hqiv.Physics.StrongColorSu3ChartClosure`, scaffolds in `QuarkColorCarrierGaugeScaffold`, `StrongColorCarrierClosure` | **proved** / **scaffold** | Structure constants and embed lemmas per `THEOREMS.md`; full chart Lie law for all pairs may still be open (see `THEOREMS.md` “still open” row). |
| “Anomaly-free three generations” | `Hqiv.Algebra.AnomalyCancellation` (`anomalyCoeff`, `sm_anomaly_free_three_generations`, …) | **placeholder** | Coefficients and index are definitionally `0`; documents intent but **not** cubic/trace anomaly calculation. |

**One-sentence honest summary:** HQIV has a strong **matrix + Lie algebra + SM
bookkeeping** anchor; it does **not** yet formalize Furey’s **Clifford / minimal
left ideal** state space or the paper’s **representation-theoretic branching**
as irrep actions—only compatible counting and witness layers where noted.

### Stage 0.5 — Lean bridge scaffold

[`Hqiv/Physics/FureyHQIVOntologyBridge.lean`](../Hqiv/Physics/FureyHQIVOntologyBridge.lean)
is the current foundation-first interface for using Furey-style results as
candidate derivations of HQIV ontology. It does not import a Clifford algebra or
minimal-left-ideal formalization. Instead, it packages:

- `HQIVFoundationFirstAnchor`: the accepted HQIV facts that remain primary
  (`octonionSpinorCarrier_dim`, `sm_quantum_numbers_one_generation`,
  `three_generations_from_triality_reps`, `alpha_gamma_forced_pair`);
- `FureyCandidateDerivation`: future Furey-side proof obligations for the
  complexified carrier, minimal ideals, number-operator charges, three-generation
  split, and shell/support bridge;
- `FureyMayRefineHQIV`: the predicate that all obligations are proved before the
  Furey layer may refine HQIV ontology;
- `HQIVFureyGenerationIndex`, `HQIVFureyThreeGenerationCarrier`, and
  `FureyThreeGenerationEmbeddingFromHQIV`: the theorem-backed HQIV landing zone
  for Furey's three-generation embedding, using `So8RepIndex` as the generation
  index, one `OctonionSpinorCarrier` per label, 24 real 8s carrier slots, and
  48 chiral Weyl bookkeeping slots;
- projection lemmas such as `furey_refinement_requires_carrier_bridge` and
  `furey_refinement_requires_shell_support_bridge`, plus the three-generation
  count/slot theorems.

This is the formal conflict rule: Furey can refine otherwise chosen HQIV ontology
only through explicit bridge theorems. Until then, HQIV's light-cone, monogamy,
and algebra package remain the foundation.

---

## Furey claims → repo map (proof-sized)

### A. \(\mathbb{C}\otimes\mathbb{O}\) or \(\mathrm{Cl}(6)\) carrier and minimal left ideals

| Furey-sized sub-claim | HQIV peg | Status |
|------------------------|----------|--------|
| Normed division octonions with fixed basis | `OctonionBasics` + `OctonionLeftMultiplication` | **proved** (real \(\mathbb{R}^8\) model) |
| Complexified octonion / spinor carrier as \(\mathbb{C}\)-module of stated dimension | Partial: `Mathlib.Data.Complex.Basic` imported in `SMEmbedding`; no dedicated `TensorProduct ℂ OctonionVec` package | **absent** as named theory |
| `CliffordAlgebra` over chosen \(Q\), action on modules, minimal left ideals | — | **absent** |
| Identification: minimal ideal ↔ one generation of Weyl fields | — | **absent** |

### B. \(SU(3)_c \times U(1)_{em}\) and charge quantization from a number operator

| Furey-sized sub-claim | HQIV peg | Status |
|------------------------|----------|--------|
| Explicit color sector on a chart | `StrongColorSu3ChartClosure`, `colorGellMannEmbed`, … | **proved** / partial (see `THEOREMS.md`) |
| \(U(1)_Y\) / EM charge table on 8 slots | `SMEmbedding.hyperchargeEigenvalue`, `chargeFromY`, witness theorems | **proved** (assignment + witnesses) |
| \(G_2 \supset SU(3)_c \times \cdots\) as subalgebra inclusion theorem | `G2_contains_SM_subgroup` | **placeholder** |
| Hypercharge as derived spectral/block property | `hyperchargeBlockCorrect` | **placeholder** |
| “Number operator” in a Fock/Clifford sense ⇒ charge quantization | — | **absent** |

### C. 64\(\mathbb{C}\)-dimensional space; three generations under color + EM

| Furey-sized sub-claim | HQIV peg | Status |
|------------------------|----------|--------|
| Three labels for eight-dimensional irreps | `Triality.So8RepIndex`, `card_so8_eight_dim_irreps` | **bookkeeping** |
| Three copies of 8-dim carrier tensored with \(\mathbb{C}\) to dimension 48 / 64 | — | **absent** (no unified `Module ℂ` of that rank proved as Furey space) |
| Decomposition into **48** physical fermion degrees of freedom with **correct** gauge quantum numbers per summand | — | **absent** |
| `branching_rules_8s` in `SMEmbedding` | `branching_rules_8s` | **bookkeeping** | Conjoins `Fintype.card (Fin 8) = 8`, a numeric `16` identity, and `card So8RepIndex = 3`; **not** irrep restriction to \(SU(3)\times SU(2)\times U(1)\). |

### D. Furey–Hughes: \(\mathbb{C}\otimes\mathbb{H}\otimes\mathbb{O}\), triality triple, Higgs doublet, GUT cascade

| Furey-sized sub-claim | HQIV peg | Status |
|------------------------|----------|--------|
| Quaternionic/octonionic tensor product algebra | — | **absent** |
| Combined trialities ⇒ scalar doublet + generations | — | **absent** |
| \(\mathrm{Spin}(10)\to\) Pati–Salam \(\to\) LR \(\to\) SM + \(B-L\) as proved chain | — | **absent** (HQIV has separate `SM_GR_Unification`-style packaging, not this cascade) |

### E. Narrative-only / easy to misread

| Location | Risk | Mitigation |
|----------|------|------------|
| `Hqiv.Physics.NuclearAndAtomicSpectra` | Mentions “Furey-style minimal left ideals” in comments | Treat as **narrative only** until a formal ideal layer exists. |
| `Triality.triality_preserves_bracket` | Name suggests Lie automorphism | Document as identity on fixed matrix bracket; outer automorphism is a **future** stage. |
| `exactly_three_fermion_generations_from_HQIV_axioms` | Name suggests physical forcing | Theorem is **Fin 3** cardinality + cycle; does not replace ladder or Clifford uniqueness. |

---

## Staged theorem ladder (suggested order for future Lean)

Stages are **dependencies** for a Furey-aligned formalization. None of stages 1–5
are required for the HQIV-native anchor in Stage 0 to remain valid.

### Stage 1 — Complexified carrier and dimension

- Define a \(\mathbb{C}\)-module structure on `Fin 8 → ℂ` (or `TensorProduct ℂ (Fin 8 → ℝ)` with a chosen linear equiv).
- Prove `finrank ℂ (Fin 8 → ℂ) = 8` (or the chosen model’s rank).
- Optional: record `StarModule` / conjugation compatible with SM bookkeeping.

### Stage 2 — Clifford algebra layer

- Import `Mathlib.LinearAlgebra.CliffordAlgebra` (or project-specific wrapper).
- Fix a nondegenerate quadratic form \(Q\) on a finite free module (e.g. six imaginary directions) and build `CliffordAlgebra Q`.
- Prove dimension formula / `Fin` basis for the Clifford module you need (paper-dependent signature).

### Stage 3 — Minimal left ideals and one generation

- Define minimal left ideals in `CliffordAlgebra Q` (e.g. as `Submodule` generated by a primitive idempotent).
- Prove ideal dimension and construct linear maps to/from `OctonionSpinorCarrier` or `Fin 8 → ℂ`.
- Replace or sharpen `G2_contains_SM_subgroup` / `hyperchargeBlockCorrect` with actual subalgebra statements linking \(G_2\), color, and hypercharge blocks.

### Stage 4 — Three generations / 64 dims

- Build the tensor product or direct sum of three eight-dimensional complex carriers keyed by `So8RepIndex`.
- Prove total `finrank` matches the paper’s 64 (if that is the chosen model).
- Upgrade `AnomalyCancellation` from definitional zeros to trace/cubic formulas **or** explicitly scope the file as “toy packaging” with a different name.

### Stage 5 — Furey–Hughes extension (optional)

- Formalize \(\mathbb{H}\otimes\mathbb{O}\) tensor products with explicit multiplication (large).
- Connect to existing `WeakInComplexStructure` / quaternionic Maxwell narrative only where a precise isomorphism is proved.

---

## Non-goals (explicit)

- Do **not** cite Stage 0 triality counting as a proof that **light-cone axioms**
  mathematically force Furey’s construction (`SMEmbedding` module doc already
  separates ladder vs triality).
- Do **not** treat `AnomalyCancellation` as physical anomaly cancellation until
  coefficients are derived from traces, not `0` by definition.
- Do **not** claim **minimal-left-ideal equivalence** of HQIV’s carrier without
  Stage 3 isomorphisms.
- HQIV project rules still apply: no PDG mass **fitting** as a substitute for
  proofs; Clifford work should remain **algebra-first** and clearly scoped in
  `AGENTS/ASSUMPTIONS.md` when new trust assumptions appear.

---

## Build and import hygiene

- Default `lake` target is intentionally light; algebra/SO(8) stacks may require
  `HQIVLEAN`, `HQIVSO8Closure`, or `HQIVStrongColorSu3Certificate` as documented
  in [`AGENTS/README.md`](./README.md) and `lakefile.toml`.
- New Clifford modules should prefer a **new** `lean_lib` glob or a thin root file
  so default CI stays fast unless the team promotes the dependency.

---

## Related documents

- [`FUREY_ALIGNMENT_GAP_ANALYSIS.md`](./FUREY_ALIGNMENT_GAP_ANALYSIS.md) — peg-hole matrix and “best anchor” statement.
- [`MASS_DERIVATION_ROADMAP.md`](./MASS_DERIVATION_ROADMAP.md) — Furey-forward vs HQIV ladder framing.
- [`THEOREMS.md`](./THEOREMS.md) — curated Lean names for cross-checking citations.
- [`ASSUMPTIONS.md`](./ASSUMPTIONS.md) — axioms, `sorry`s, and trust boundaries.
