# P vs NP — HQIV narrative (furthest horizon; quantum path only)

This note is **documentation for agents**. It places **P vs NP** (the **seventh** Clay Millennium Prize Problem alongside the six “mathematical physics” threads) inside the same honesty frame as [MILLENNIUM_UNIFIED_NARRATIVE.md](../MILLENNIUM_UNIFIED_NARRATIVE.md): **probe language and future hooks**, not a complexity-class theorem in this repository.

**Formal standard:** Any eventual formal claim must align with [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems); see [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](../LEAN_DOJO_MILLENNIUM_ALIGNMENT.md).

---

## 1. Status (be blunt)

| Question | Answer in HQIV_LEAN |
|----------|---------------------|
| Is **P = NP** or **P ≠ NP** proved here? | **No.** |
| Is there a Lean proof about **Turing machines**, **SAT**, or **polynomial time** for this question? | **No** (not in scope of current `Hqiv/` targets). |
| Is there a **story** where HQIV’s **quantum computing simulator** layer could *eventually* inform intuition? | **Yes, narrative only** — see §2–3. |

Among the Millennium-scale threads documented for agents, **P vs NP is the furthest off**: there is no discrete zeta scaffold or fluid closure parallel to RH/NS/modular forms—only **optional** links through **quantum simulation** and **search** metaphors.

---

## 2. Narrative path (quantum simulator → “might be true” is **not** a theorem)

The **paper-level** idea (not Lean): if the HQIV program’s **informational** or **horizon** structure were ever to imply that **feasible** computation in nature does not coincide with classical **worst-case** complexity, that could **in principle** sit in the same conceptual space as discussions of **P vs NP**—but **only** after a precise reduction to the **formal** problem statement in Lean Dojo’s repo.

**Where the codebase actually touches “quantum” today (all classical Lean + numerical simulators):**

- **`Hqiv/QuantumComputing/LatticeNextPrimeQCAlgorithm.lean`** — proved **fragments** about gates, Fano-line probability mass, pipeline **stage-count** narrative; **not** a proof that the lattice-next-prime pipeline is in P or NP or BQP.
- **`Hqiv/QuantumComputing/SparseSimulationDensityCrossover.lean`**, **`OSHoracle.lean`**, **`DigitalQuantumSimulation.lean`**, **`DiscreteQuantumState.lean`** — scaffolding for **simulation** and **oracles**; **no** complexity separation results.
- **Python:** `hqvmpy` quantum simulators and oracles (see package `pyhqiv.quantum_simulator`, `quantum_oracles`) — **numerical**; not a proof.

So the “path via our quantum computing simulator” is: **a possible future alignment** between HQIV’s **simulation / search** story and **computational complexity**, **stated here so agents do not confuse simulation demos with Clay-level proofs**.

---

## 3. Ladder (Q0–Q4 — mostly empty; names only)

Work **in order** if this ever becomes a formal sub-project. Each step should produce **artifacts**; today most are **placeholders**.

| Milestone | Goal | Done when |
|-----------|------|-------------|
| **Q0 — Vocabulary** | “P, NP, polynomial time” used only in docs with **Clay/Lean Dojo** alignment. | This file + link from [MILLENNIUM_UNIFIED_NARRATIVE.md](../MILLENNIUM_UNIFIED_NARRATIVE.md). |
| **Q1 — Simulator inventory** | One table: Lean module ↔ Python ↔ **what is proved** vs **demo**. | Rows filled for `LatticeNextPrimeQCAlgorithm`, `SparseSimulationDensityCrossover`, `OSHoracle`; cite [QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md](../QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md). |
| **Q2 — Hypothesis bundle (optional)** | Explicit `Prop` record: “**Hypothetical** reduction from HQIV decision problem X to SAT” — **only** if X is defined. | New module **or** deferred; no `sorry` claiming P=NP. |
| **Q3 — Lean Dojo statement** | Import or **doc-only** equivalence map from HQIV claims to `LeanMillenniumPrizeProblems` P vs NP formulation. | Maintainer choice; dependency hygiene. |
| **Q4 — Claim discipline** | No README line implies P=NP without a theorem in Lean Dojo’s formalization. | Reviews + [THEOREMS.md](../THEOREMS.md) honesty. |

---

## 3b. Working **toward** any Clay-scale claim (allowed — how)

You **can** pursue this thread responsibly: build **real mathematics and definitions** that might one day connect to a formal P vs NP statement. What you **cannot** do is use `sorry` (or prose) as a stand-in for the hard step.

**Legitimate next work (examples):**

- **Prove small, checkable lemmas** already in scope: Fourier patch correlations, shell geometry, moiré–cusp / BST lemmas, concentration bounds — each with a complete proof.
- **Define** intermediate objects with precise types (e.g. a score on `Fin n`, a map to `O8`, a discrete gradient) and prove **conditional** implications: “if `Hypothesis H` then `PatchProperty P`” — where `H` is explicitly named, not smuggled as `sorry`.
- **Separate** “encoding 3SAT → \(M\)” (pure arithmetic, definable) from “\(M\)’s shell geometry decides satisfiability” (the conjectural bridge). Formalize only what is true; document the gap.
- **Align vocabulary** with Lean Dojo’s P vs NP formulation before any biconditional is even attempted ([LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](../LEAN_DOJO_MILLENNIUM_ALIGNMENT.md)).

**What counts as progress:** more **proved** glue, clearer **hypothesis** records, and **numerical / exploratory** scripts **labeled as non-proof** — not fewer sorries on a headline theorem.

**Octonion / SAT storyboard:** [OCTONION_SAT_PIPELINE.md](./OCTONION_SAT_PIPELINE.md) — narrative and open formal gaps; companion to Q2–Q4 above.

---

## 4. What agents must not say

- That the **quantum simulator** “shows” **P = NP** or **P ≠ NP**.
- That **sparse simulation** or **next-prime** circuits **collapse** classical complexity classes without a cited theorem.
- That HQIV is “closer” to resolving P vs NP than RH/NS **in Lean** — it is **further**, by design of this repo.

---

## 5. Related docs

| Doc | Role |
|-----|------|
| [QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md](../QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md) | Circuit metaphor for lattice next-prime; not complexity theory |
| [OCTONION_SAT_PIPELINE.md](./OCTONION_SAT_PIPELINE.md) | Octonion-shell / Fourier-patch **story** tied to a 3SAT encoding — **not** a Lean proof; explicit separation from P vs NP claims |
| [MILLENNIUM_UNIFIED_NARRATIVE.md](../MILLENNIUM_UNIFIED_NARRATIVE.md) | Unified probe narrative (now includes P vs NP as seventh thread, prose) |
| [LEAN_DOJO_MILLENNIUM_ALIGNMENT.md](../LEAN_DOJO_MILLENNIUM_ALIGNMENT.md) | Formalization compatibility |
