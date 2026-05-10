# Octonion-shell “geometric SAT” pipeline — **narrative only**

This note archives a **story** that ties together: double-unwrap of \(V_8(\sqrt{m})\), Fourier patch isolation on the \(\pi/(2k)\) axis, **moiré–cusp** search along the ordered patch index (Lean: `MoireCuspBracket`, `MoireToyThresholdSearch`), and shell arithmetic — with a **prime-product encoding** of 3SAT into an integer \(M\) on a shell. The old **2/1 vs 1/2 ray** module (`OctonionPatchQuantum`) has been **removed**; patch search in Lean is **one-dimensional in \(j\)**, not a 2D ray hunt.

**Formal status (read first)**

| Claim | In HQIV_LEAN? |
|-------|----------------|
| A **proved** equivalence “3SAT satisfiable \(\leftrightarrow\) geometric patch / quantum-ray witness” | **No.** |
| A Lean theorem `sat_solver_decides_via_patch` as stated below | **Not in the library** — would be a Clay-scale reduction, not a wiring `sorry`. |
| **Proved** fragments: \(V_8\), \(A_7\), lattice shells, Fourier correlations on a window, moiré cumulative variation / BST lemmas | **Yes** — see links in §7. |
| **Proved** SAT-search scaffolds: exact patch-index satisfiability iff, concrete near-degenerate witness/seed-gap transfer, recursive budget bounds, subfactorial explored-search theorems, and explicit gap-to-slack search bounds | **Yes** — see `CNFPatchBridge` and `GeneralizedGeometricOracle` in §7. |

**Why we do not add the biconditional as Lean:** Satisfiability of 3SAT is **NP-complete**. A correct, fully formal implication from your encoding + purely geometric hypotheses to “SAT instance satisfiable” would be an enormous theorem (and would imply **P = NP** for any polynomial-time realization of the geometric steps). Standard mathematics does **not** certify that a prime-product encoding of clauses yields a **decidable-from-surface-geometry** predicate on \(M\). What the repo now **does** prove on the search side is narrower and honest: exact patch-index satisfiability equivalence for exhaustive enumeration, concrete near-degenerate witness/seed-gap transfer, and recursive explored-search bounds that can be **subfactorial** or sharpened to `topk * (frontierArity - slack)^depth` when a gap-derived slack is available. Treat §2–5 as **intuition / pipeline design**, not as SAT decision results.

See **[P_VS_NP_HQIV_NARRATIVE.md](./P_VS_NP_HQIV_NARRATIVE.md)** for repo rules: no agent should claim P = NP or a SAT decision procedure from this geometry without a theorem aligned to formal complexity statements.

**Working toward that claim (without sorry):** the same doc’s **§3b** lists legitimate steps — proved lemmas, named hypotheses, separating encoding from the geometric bridge, Lean Dojo alignment. This file stays the **story + gap map**; progress is measured in **finished proofs**, not placeholder theorems.

---

## 1. 3SAT encoding into the lattice (polynomial-time, deterministic — *definition only*)

Given a 3SAT formula with \(n\) variables and \(c\) clauses:

- Assign each variable \(x_i\) a small distinct prime \(p_i\).
- Encode a literal: positive \(x_i \to p_i\), negative \(\neg x_i \to p_i^2\).
- Encode a clause (three literals) as the **product** of its three literal terms (a \(k=3\) composite in the narrative).
- Encode the full formula as the product \(M\) of all clause-products.

This map is polynomial-time in formula size if primes are chosen by a fixed scheme. The **exact** total prime-factor count \(\Omega(M)\) (with multiplicity) is **known from the formula without factoring \(M\)**: sum over every literal of \(1\) if positive and \(2\) if negative (since \(p_i\) contributes one prime and \(p_i^2\) contributes two). Only when all literals are positive is \(\Omega(M) = 3c\); negated literals inflate \(\Omega(M)\). That \(\Omega(M)\) is the natural **\(k\)** for the narrative axis \(\theta = \pi/(2k)\) on the Fourier patch — **one patch, not a free parameter**. See `omega_M_exact` (encoding sum) and `assert_omega_exact_matches_factorization` (checked vs factorization of \(M\)) in `scripts/hqiv_geometric_3sat_demo.py`.

**Not claimed here:** that “satisfiable \(\leftrightarrow\)” any statement about \(V_8\), Fourier peaks, or moiré scores on a shell. That bridge is **extra physics / conjecture**, not proved in this repo.

---

## 2. Geometric SAT solver pipeline (storyboard)

1. Encode 3SAT \(\to\) integer \(M\).
2. Shell radius \(r = \sqrt{M}\); continuous proxies \(V_8(r)\), \(A_7(r)\) (“modal history”).
3. Double-unwrap \(V_8(r)\) into two quaternion blocks (narrative; not a single Lean “unwrap” theorem tying SAT).
4. Fourier concentration on the \(\pi/(2k)\) axis — **partial** Lean support: `Hqiv.Algebra.OctonionSphereFourierPatch` (correlations, concentration lemmas under hypotheses).
5. Moiré score on the patch — **not** defined in Lean (`fourierPatchScore` absent; see roadmap in `OctonionSphereFourierPatch.lean`).
6. Surface vectors / gradients — **not** formalized.
7. **Moiré–cusp / BST** on the patch index — **proved order theory** (`MoireCuspBracket`, `MoireToyThresholdSearch`); linking scores to SAT is **not**.

---

## 3. Speculative Lean signature (not admitted)

The following is a **sketch** only. Undefined predicates (`ThreeSATFormula`, `encodes_3sat`, `φ_is_satisfiable`, `dominant_quantum_ray`, …) and the biconditional are **not** theorems in `Hqiv/`.

```lean
-- NOT IN REPO — illustrative only
theorem sat_solver_decides_via_patch
  (φ : ThreeSATFormula) (M : ℕ) (henc : encodes_3sat φ M)
  (hm : 1 < M) (k : ℕ) (_hΩ : Ω M = k)
  (window kernel : Fin n → ℂ)
  (_hwin : WindowIsRadialProjection window)
  (_hker : KernelIsHarmonic hn k kernel)
  (maxCoeff ε : ℝ) (_hε : 0 < ε)
  (hpeak : ‖fourierPatchPeakCorrelation M hm window kernel‖ = maxCoeff)
  (hpeak_ge : (n : ℝ) ≤ ‖fourierPatchPeakCorrelation M hm window kernel‖)
  (hside : ∀ (k' : ℕ) (hk' : 0 < k'), k' ≠ k →
            ‖fourierPatchSideCorrelation k' hk' window kernel‖ ≤ ε * maxCoeff) :
  φ_is_satisfiable ↔
    ∃ (address : Fin 8 → ℤ),
      o8normSq address = M ∧
      address ∈ latticeShell8Finset M ∧
      is_on_fourier_patch address (intrinsicShellAxisAngle M) ∧
      (dominant_quantum_ray address = quantumTwoOverOne ∨
       dominant_quantum_ray address = quantumOneHalf) :=
  sorry
```

**Concrete Lean issues** (from `OctonionSphereFourierPatch` roadmap): type mismatches (`o8normSq` expects `O8`, not `Fin 8 → ℤ`); no `Fin n →` patch \(\to\) \(\mathbb{Z}^8\) canonical map; missing score/gradient definitions.

---

## 4. Example (narrative)

Formula:

\[
(x_1 \lor \neg x_2 \lor x_3) \land (\neg x_1 \lor x_2 \lor x_4) \land (x_2 \lor x_3 \lor \neg x_4).
\]

Narrative encoding gives \(M = 5\,551\,800\), \(r \approx 2356.02\), \(k = 9\). This is **heuristic illustration** — not a verified Lean certificate tying this \(M\) to SAT.

---

## 5. Complexity, nuances, edge cases (all informal)

- **Encoding:** polynomial in formula size.
- **Geometric steps as “P”:** only if each is polynomial-time **and** the whole chain is **correct** for SAT — unproved here.
- **Edge cases:** multiple satisfying assignments, unsat interference, large formulas, degenerate formulas — discussed in prose only.

---

## 6. Immediate next steps (maintainer)

- Keep **separation** between proved algebra (`OctonionSphereConstruction`, moiré–cusp layer) and SAT / P vs NP **documentation**.
- If a **hypothetical** `Prop` bundle is ever added, follow **[P_VS_NP_HQIV_NARRATIVE.md](./P_VS_NP_HQIV_NARRATIVE.md)** Q2: explicit “hypothesis” naming, **no** `sorry` masquerading as “trivial wiring” for a Clay-level claim.

---

## 7. Related Lean modules (what actually exists)

| Module | Role |
|--------|------|
| `Hqiv.Archive.Logic.CNF` | **CNF** on `Fin n` variables: `Literal`, `Clause` (= `List` of literals, any length), `CNFFormula`, `CNFFormula.Satisfiable`, uniform **`k`-SAT** (`IsUniformKSAT k`), **3-CNF** as `IsUniformKSAT 3` / `ThreeCNF`; narrative **`omegaEnc`** (literal weights 1/2) for arbitrary clause length — extends the prime-product bookkeeping beyond fixed width-3. |
| `Hqiv.Archive.Logic.CNFPatchBridge` | Exact patch-index bridge: `CNFFormula.satisfiable_iff_exists_patch_index` identifies CNF satisfiability with exhaustive search over `Fin (2^n)` patch assignments (`assignmentFromPatchIndex`). |
| `Hqiv.Geometry.GeneralizedGeometricOracle` | Candidate-family SAT/search scaffold: finite SAT candidates and exact satisfied-clause counting, prune-boundary witness preservation, concrete near-degenerate seed-gap theorem, recursive budgets `topk * beam^depth`, subfactorial explored-search theorems, reduced-frontier profiles, and explicit / gap-derived slack search bounds. |
| `Hqiv.Archive.Algebra.MoireCuspBracket` / `MoireToyThresholdSearch` | **Patch search** along \(j\): monotone `cum`, threshold / BST. |
| `Hqiv.Algebra.OctonionSphereConstruction` | `intLatticeToO8`, `o8normSq`, shells, volume. |
| `Hqiv.Algebra.OctonionSphereFourierPatch` | `fourierPatchPeakCorrelation`, concentration lemmas; **roadmap** for score/address glue. |
| `Hqiv.Algebra.IntegerLatticeShellCount8` | Discrete shell enumeration on \(\mathbb{Z}^8\). |

**See also:** [OCTONION_SPHERE_PATCH.md](./OCTONION_SPHERE_PATCH.md).

**Python demo (encoding + geometry vs brute-force SAT):** `scripts/hqiv_geometric_3sat_demo.py` — prime encoding, \(V_8\)/\(A_7\), \(k=\Omega_{\mathrm{enc}}\), toy moiré \(S(j)\), **monotone** predicate from cumulative \(|\Delta S|\) with \(T(M)\), **binary search** on `Fin n`, optional `--json` / `--mod-demo`; SAT only via brute force.
