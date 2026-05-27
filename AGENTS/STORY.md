# Story spine vs textbook defaults (agent router)

There is **no** legacy `story.md` in this folder. Use this file as a **one-page orientation**: where the formal HQIV line **agrees** with classical math/physics, where it **differs on purpose**, and where prose must **not** drift ahead of Lean.

## Canonical splits (read these first)

| Need | Doc |
|------|-----|
| **Patch = observable universe; continuum not required; “complete” vocabulary** | [PATCH_ONTOLOGY.md](./PATCH_ONTOLOGY.md) — **read before papers/sim/cosmology edits** |
| What is actually proved (names + modules) | [THEOREMS.md](./THEOREMS.md) |
| Trust boundary: axioms-as-narrative, scripts, `sorry`, QFT scope | [ASSUMPTIONS.md](./ASSUMPTIONS.md) |
| Single cross-problem narrative at **probe** level (no extra claims) | [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md) |
| What is proved vs Clay/Dojo **interface** | [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](./LEAN_DOJO_MILLENNIUM_ALIGNMENT.md), `Hqiv.Story.MassGapWiring` |
| Repo-wide audit ledger (stale refs, namespace drift) | [LEAN_CORPUS_AUDIT_2026-04-20.md](./LEAN_CORPUS_AUDIT_2026-04-20.md) |

**Maintainer rule (from [README.md](./README.md)):** user-facing formal claims → add a row in `THEOREMS.md`; new trust assumptions → extend `ASSUMPTIONS.md`. This file should stay a **router + divergence checklist**, not a second copy of either.

## HQIV-specific vs “generic textbook” (intentional)

These are **design commitments** in Lean + docs, not oversights:

0. **Patch ontology first (full contract: [PATCH_ONTOLOGY.md](./PATCH_ONTOLOGY.md)).** Fields, actions, and readouts attach to **discrete patches** (shells, `Fin 4` charts, accessible mode budgets). The **accessible patch net** is the **observable universe** in theory terms—not a fundamental smooth manifold. “Complete theory” means **patch-closed** (no observables outside causal patch data + explicit readout), **not** “proved continuum QFT.” Do not describe HQIV as “discrete approximation to continuum” unless you are explicitly discussing a **comparison** limit.

1. **Discrete null lattice first.** Counting and curvature imprint are tied to `OctonionicLightCone` combinatorics and the octonionic lift (`6^7 * sqrt(3)` normalization). Continuum calculus is **IR / readout language** over that ladder, not a claim of fundamental sub-Planck smoothness (see `ASSUMPTIONS.md` §1, §15-style caveats; expanded in `PATCH_ONTOLOGY.md`).

2. **Single `(α, γ)` pair.** `Hqiv.alpha = 3/5`, `Hqiv.gamma_HQIV = 2/5` are the **only** curvature-imprint / monogamy identifiers in-repo; forced by lattice structure (`AlphaGammaForcedByLattice`). Not a “fit two exponents” QFT counterterm menu (`ASSUMPTIONS.md` §1b).

3. **Quaternionic sanity limit ≠ canonical carrier.** Maxwell-on-`H` flat limits exist, but the **canonical** δ_E / shell imprint is octonionic; the rigid `1296` undershoot is proved as a comparison — do not silently swap blocks (`ASSUMPTIONS.md` §1 bullet 4; `THEOREMS.md` curvature rows).

4. **Finite accessible regions vs full textbook CCR QFT.** The repo explicitly does **not** treat global infinite-dimensional Wightman data as a prerequisite; exact CCR on fixed finite matrices is impossible (trace obstruction); patchwise scaffolds and **growing-cutoff limits** are the honest story (`ASSUMPTIONS.md` §2 long paragraph on `HorizonLimitedRenormLocality` / patch nets).

5. **Clay Millennium = existential witness bundle, not “HQIV proves Yang–Mills”.** Compatibility is with `lean-dojo/LeanMillenniumPrizeProblems`; bridge lemmas show what **would** suffice given a `QuantumYangMillsTheory` + gap — they do not manufacture that witness from Lie algebra closure alone (`MassGapWiring`, `THEOREMS.md` Clay table).

6. **SO(8) Lie closure ≠ linear span of fifteen matrices.** `G₂ ∪ {Δ}` span obstruction is documented beside the **positive** Lie-subalgebra closure result — avoid conflating “span” and “Lie-generated” (`ASSUMPTIONS.md` §5).

7. **Smeared fields can be minimal on purpose.** Story patch OVDs may use **origin jets** or fixed generators as scaffolding; **restriction / normalization** along the same auxiliary-field or phase cutout as GR / modified Maxwell (`SM_GR_Unification`, `ComptonIRWindow`, `AuxiliaryField`) is an explicit **downstream** bridge when you need dynamical alignment — not silently folded into every def (`Hqiv.Story.NonabelianSO8SmearedPatchField` module doc).

## “Audit the whole repo” — practical workflow

1. Pick a **build target** (`lakefile.toml` header comments + [README.md § Building](./README.md#building)) so “everything compiles” matches what you mean (`HQIVLEAN` ≠ `HQIVSO8Closure` ≠ `HQIVStrongColorSu3Certificate`). The last target bundles the optional `f^{abc}` simp table **and** the proved `3×3` chart Lie law (`StrongColorSu3LieChartLaw`; see `THEOREMS.md`).
2. Run a **mechanical sweep**: `sorry`, `admit`, `axiom` (excluding comment text), script-generated data paths — triage into `ASSUMPTIONS.md` §4–§5 style entries.
3. For each **physics claim** in a module doc, ask: is there a **Lean name** in `THEOREMS.md` or a **named `Prop` bundle**? If not, label it narrative / roadmap in prose.
4. When a chapter of the Story spine changes, update **`Hqiv/Story` chapter docs** + one line in `THEOREMS.md` if a new externally usable lemma landed.

This keeps “what is proved” and “what is motivation” **separated by file convention**, so you do not argue yourself into a corner by treating roadmap language as if it were `by exact?`.
