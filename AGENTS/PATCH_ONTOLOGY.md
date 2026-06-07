# Patch ontology — agent contract (do not lose the plot)

**Read this before** editing papers, simulators, cosmology pipelines, or QM/QFT bridge code. It is the **authoritative HQIV framing** for agents; companion prose lives in `papers/include/patch_theory_messaging.tex` (included in Lean-aligned manuscripts such as `tuft_sm_lagrangian`; **`HQIV/paper/main.tex` in the HQIV repo does not include it yet**).

**Maintainer rule:** if a PR or agent response implies “fundamental smooth spacetime,” “complete continuum QFT,” or “the universe is the FLRW background,” check against this file first.

---

## One-sentence thesis

**HQIV is patch-closed:** all physically observable structure lives on **discrete, horizon-limited patches** (shell ladder + finite charts + finite mode budgets). A fundamental continuum is **not required**; smooth fields and textbook QFT are **readout / comparison layers**. The **accessible patch (patch net)** is what we mean by the **observable universe** for theory purposes—not a mesh-refinement limit of a pre-existing manifold.

---

## What “patch” means in-repo

| Object | Lean / code locus | Role |
|--------|-------------------|------|
| Shell index \(m \in \mathbb{N}\) | `OctonionicLightCone`, `shell_shape`, `available_modes` | UV-complete counting on the null ladder |
| TUFT Beltrami chart row | `TuftShellChart.tuftHeavyChartShell`, `tuftHadronModeShell` | Hadron / vev spectroscopy (distinct name from `referenceM`; see [`TUFT_SHELL_ONTOLOGY.md`](./TUFT_SHELL_ONTOLOGY.md)) |
| Accessible mode budget | `accessibleModeBudgetUpToShell`, `LightConeMaxwellQFTBridge` | **Finite** causal bookkeeping up to shell \(M\) |
| Finite chart / corners | `patchChartPoint`, `patchEventChartFour`, `PatchQFTBridge` | Local QFT bookkeeping on \(\mathrm{Fin}\,4\) (and extensions) |
| SM anomaly traces | `AnomalyCancellation` | **Proved** cubic/mixed trace cancellation for explicit one-generation content \(\times 3\) |
| Patch topological discharge | `PatchTopologicalObstruction` | **Proved** single-sector: instanton, Pontryagin, first-Chern, \(U(1)\) winding \(=0\); \(\theta\)-independent on patch data |
| Patch support on modes | `HQIVFermionMode`, `HQIVBosonMode`, `hqivModeSpacelikeSep` | Observables carry **where** on the patch net they live |
| Finite QM core | `HorizonLimitedQM_QFT_Closure`, `DiscreteQuantumState` | Born, ledgers, normalization — **proved finite layer** |
| Continuum checklist | `HorizonContinuumClosureStatementCoreHQIV`, `HorizonLimitedRenormLocality` | **Named conjunction** discharged by witness bundles — **not** proved interacting continuum QFT |

**“Patch QFT”** means: patching rules, finite measurement ledgers, variational identities on the discrete spine—not “QFT = recovery of ordinary continuum QFT through an ultraviolet limit.”

---

## Gauge consistency: discharged vs continuum-only

| Obligation | Patch-level status | Lean anchor | Still open (continuum-only) |
|------------|-------------------|-------------|------------------------------|
| \(U(1)_Y^3\), grav–\(U(1)_Y\), \(SU(3)^2U(1)\), \(SU(2)^2U(1)\), \(SU(3)^3\) traces | **Proved** (explicit one-gen content \(\times 3\)) | `Hqiv/Algebra/AnomalyCancellation` | Path-integral / measure anomaly theorem |
| \(SU(2)_L^3\) (pseudoreal) | **Proved** \(=0\) | `su2_cubic_trace_*_zero` | — |
| Instanton / Pontryagin / first-Chern / \(U(1)\) winding on patch | **Discharged** (single sector, all \(=0\)) | `Hqiv/QuantumMechanics/PatchTopologicalObstruction` | BPST sectors, \(\theta\)-vacua on smooth bundles |
| Rapidity-phase Lorentz closure (`1+1` boosts; `3+1` embed) | **Proved** | `RapidityLorentzClosure` (`rapidity_lorentz_closure_discharged`) | Continuum interacting QFT / Wightman |
| Spatial-rotation Lorentz closure (`O(3)` on `Fin 3`; flyby/CMB/fluid axes) | **Proved** | `SpatialRotationLorentzClosure` (`spatial_rotation_lorentz_closure_discharged`, `full_lorentz_closure_discharged`) | Trajectory integration, J₂ numerics (Python) |
| Abelian patch commutator / microcausality hooks | **Proved** | `PatchQFTBridge`, `Chapter07_PatchQFT` | Full non-abelian holonomy on smooth manifolds |
| Exact CCR \([A,B]=I\) on fixed finite dim | **Obstruction proved** (cannot hold) | `CCRFiniteDimObstruction` | Global \(L^2\) CCR (not HQIV ontology) |
| Spin–statistics from triality + causality | **Constructive satisfaction** | `HQIV_satisfies_SpinStatistics_from_triality_and_causality` | Full Wightman spin–statistics |
| Strong-color chart Lie law \(f^{abc}\) | **Proved** (optional cert) | `StrongColorSu3LieChartLaw` | Continuum YM mass gap / Clay |
| CKM/PMNS from Fano cycle overlaps | **Scaffold only** | `HopfShellBeltramiMassBridge`, `ContinuousXiCoupling` | TUFT \(H^*(CP^4)\) form; PDG matrix fit — [CKM_PMNS_FANO_OVERLAP.md](./CKM_PMNS_FANO_OVERLAP.md) |
| Full Spin(8) outer automorphism triality | **Bookkeeping only** | `Triality.lean` (label cycle) | Mathlib-grade Spin(8) triality |

**Agent rule:** say **“discharged at patch level”** or **“proved finite traces”** for the left column; never collapse into “HQIV proves all of QFT is anomaly-free and instanton-free in the continuum.”

**Narrative (papers + agents):** At the finite patch level, HQIV proves SM cubic and mixed anomaly trace cancellation from explicit generation content, and discharges instanton, \(\theta\)-vacuum, first-Chern, and \(U(1)\)-winding obligations because the patch carrier has one topological sector and no continuum gauge measure. Continuum notation for SO(8), Hopf fibration, and Yang–Mills kinetics remains a comparison/translation layer; continuum instanton and measure-choice problems are **not load-bearing** on the proved discrete spine.

---

## Continuum is not required (what agents must not invert)

| Textbook default | HQIV default |
|------------------|--------------|
| Smooth \(\mathbb{R}^{1,3}\) (or Hilbert space) is fundamental | **Discrete ladder + finite patches** are fundamental |
| Continuum limit defines the theory | Continuum notation is a **translation layer** for literature comparison |
| Global Wightman / CCR data are prerequisites | **Finite accessible regions** + **limits as cutoff grows** (`ASSUMPTIONS.md` §2) |
| “Complete theory” = full GUT + interacting QFT | **Patch-closed** = no observables outside accessible patch data + readout maps |
| “Continuum extension is an open problem” | **Continuum is a calculation approximation**, not an open problem (see strict-mode rule below) |

When you see derivatives, charts, `AnalyticOn`, or FLRW in Lean or `main.tex`, read them as **IR / observer-readout over the ladder**, not as commitment to sub-Planck smoothness (`ASSUMPTIONS.md` §1, bullet on sub-Planck continuum).

**Lean honesty (do not oversell):** satisfying `continuum_many_body_closure_*` or `HorizonContinuumClosureStatementCoreHQIV` is **not** a proof of rigorous continuum quantum field theory. Scaffold and surrogate slots remain documented in `HorizonLimitedRenormLocality` and the octonion/QM paper appendix.

---

## Strict continuum-language rule (what to write, and what would destroy results)

Agents writing or editing prose, code comments, or paper text **must** use the following framing for any reference to a continuum or continuum limit:

1. **Default phrasing:** “A continuum is **not required** for this result”, or equivalently “the continuum form is an optional convenience for comparison with standard formulas”. Never write that the continuum form is an “open problem”, “TBD”, or “future work” unless what is being deferred is explicitly only the *comparison-layer derivation*, not the ontology.
2. **Strong-wording cases:** in places where the discrete index is *load-bearing*, write “a continuum version would destroy these results” (or paraphrase). Load-bearing examples include:
   - the curvature imprint \(\delta_E(m)\propto 1/(m+1)\) (taking \(m\to\infty\) sends \(\delta_E\to 0\) and erases the prediction);
   - the harmonic mass ladder \(m_\tau\to m_\mu\to m_e\) and Yukawa rules \(y_f=\sqrt{2}\,m_f/v\) built from `resonance_k_tau_mu`, `resonance_k_mu_e` (no integer ladder ⇒ no SM mass scaffold);
   - the lock-in vev \(v=\sqrt{\eta_{\rm paper}\,\Omega_k(m_{\rm lockin};m_{\rm lockin})}\) (which assumes a finite shell \(m_{\rm lockin}\));
   - the reference shell \(m=\mathrm{referenceM}=4\) (HQIV lock-in / proton witness pin) — no integer shell ⇒ no proton mass;
   - TUFT hadron excitations use **`tuftHadronModeShell`** on the heavy chart (`tuftHeavyChartShell + n + \ell\)); do not write “TUFT shell = referenceM” except as today's numeric bridge;
   - the rational coefficients \(\alpha=3/5\), \(\gamma=2/5\), \(\alpha_{\rm GUT}=1/(6\cdot 7)=1/42\) (these are stars-and-bars / cube-axis × octonion-imaginaries counts, not continuum limits).
3. **Calculation-approximation cases:** where continuum is only used to compare with textbook formulas (e.g. one-loop \(\beta\)-running form, smooth-manifold Maxwell, FLRW homogeneous channel), say “continuum approximation used for literature comparison; the discrete statement is the proved object”.
4. **Anti-patterns (rewrite on sight):**
   - “The continuum limit of this is an open problem.”
   - “We defer the continuum extension to future work.”
   - “A complete derivation requires the continuum limit.”
   - “Discrete approximates the continuum.” (The arrow goes the other way: continuum approximates the discrete.)

---

## Single principled exception: the \(\mathfrak{so}(8)\) closure as a de-facto continuum algebra from a discrete construction

There is **one** place where a continuous algebraic object appears intrinsically (not as a comparison layer): the Lie algebra \(\mathfrak{so}(8)\) obtained by closing \(G_2\cup\{\Delta\}\) under brackets (Lean: `Hqiv.SO8Closure`, `Hqiv.SO8ClosureInterface`, `Hqiv.Algebra.SO8ClosureAbstract`).

| Object | Ontological status |
|--------|--------------------|
| \(L(e_i)\), \(i=1,\dots,7\) (octonion left-mul matrices) | **Discrete** (finite Fano table; `OctonionLeftMultiplication`) |
| \(\Delta\) (phase-lift in \((e_1,e_7)\) plane) | **Discrete** (single \(\pi/2\) rotation, `Hqiv.Algebra.PhaseLiftDelta`) |
| 14 \(G_2\) generators from \([L(e_i),L(e_j)]\) | **Discrete** (finite commutator table) |
| 28-dim \(\mathfrak{so}(8)\) Lie algebra and \(\mathrm{SO}(8)\) Lie group | **De-facto continuum algebra** built from the above discrete data |
| \(\exp(t\,X)\in\mathrm{SO}(8)\) for \(X\in\mathfrak{so}(8)\) | Continuous in \(t\in\mathbb{R}\), but parameter-space only — **no continuum spacetime commitment** |

**Rule for agents:** when writing about \(\mathfrak{so}(8)\), \(\mathrm{SO}(8)\), \(G_2\), \(\Delta\), or any of their exponentials/representations, you may use continuous Lie-algebraic notation freely; it is the one place in HQIV where continuity is genuine, because the construction certifies it from discrete inputs. **Do not** use this exception to justify continuum spacetime, continuum QFT measures, smooth-manifold field equations, or sub-Planck refinements; those remain non-required (and in the load-bearing cases above, would destroy the results).

---

## Patch = observable universe (completeness in the right sense)

**Observable universe (HQIV sense):** the union of patches **causally accessible** to the fundamental observer—fixed by light-cone mode budgets, shell indices, and finite chart labels—not an infinite pre-given manifold with patches as approximate cells.

**“Complete theory” (allowed claim):**

- Every **defensible** prediction in the HQIV program should be expressible as a functional of **patch data** (shell ladder, mode budgets, octonion carrier, measurement ledger) plus **explicit readout** (lapse, CLASS homogeneous channel, comparison to CODATA, etc.).
- No **hidden** degrees of freedom are posited **outside** what causal accessibility and the discrete spine carry.
- Asymptotic formulas (Euler–Maclaurin, shell→harmonic ratio limits) summarize the ladder; they do **not** replace the patch as the ontology.

**“Complete theory” (disallowed or misleading without qualification):**

- “HQIV proves continuum QFT / Wightman axioms / full interacting renormalization.”
- “The universe **is** the homogeneous FLRW background used in CLASS” (that is a **volume-averaged readout channel**, not the patch net).
- “Sparse simulation on \(k\) terms is always exact” (exact only when gates are **patch-internal**; see below).

---

## Simulation and TrigSym (`TrigSym` repo)

The Python quantum simulator implements **patch-local digital evolution** on \((L+1)^2\) harmonic modes × \(\mathbb{R}^8\) octonion carriers (`TrigSym/README.md`).

| Situation | Agent reading |
|-----------|----------------|
| Full \((L+1)^2\) grid evolution | **Patch closure** when an operation is not closed on a smaller declared support—not worship of a continuum Hilbert space |
| Sparse / carrier fast paths | Valid when schedule is **patch-internal** (`GateKind`: diagonal, permutation, certified `local_mix`) |
| Aliasing / wrap / fold | Applying an operator that couples to modes **outside** the carried support—same as “physics outside the patch leaked back in” |
| Embedded \(2^n\) OpenQASM | Small **computational** subspace in a larger chart; not a claim that ontology is only \(2^n\) |
| `harmonic_dft_gate`, dense untyped gates | Typically **not** patch-internal; need full chart or prove invariant subspace |

**Extra dimensions (quaternions, etc.):** representation lifts (e.g. \(SO(3)\) via \(SU(2)\)) help avoid singularities; they **do not** automatically shrink required support unless the lifted state space is **closed** under the operators applied (\(PUP = UP\) on that support).

---

## Anti-patterns (agents should flag or rewrite)

1. **“Discrete approximates continuum.”** Prefer: **continuum translates discrete patch bookkeeping.**
2. **“Complete GUT / complete relativistic theory”** in abstract without **patch-closed** qualifier.
3. **Treating `HorizonContinuumClosureStatementCoreHQIV` as QFT proved.**
4. **Skipping gates in QASM benchmarks** then comparing to NumPy on the **full** circuit (see `TrigSym` basis_change triage).
5. **Fitting PDG masses and calling it “derived”** while also anchoring the same sector (see `ASSUMPTIONS.md` single scale witness).
6. **Assuming CLASS output is the fundamental state** rather than one homogeneous readout of patch-averaged channels.

---

## Paper and prose alignment

| Artifact | Patch messaging status |
|----------|------------------------|
| `papers/include/patch_theory_messaging.tex` | Canonical short **reader contract** (gauge consistency discharge + patch QFT; included in Lean-aligned `.tex` files) |
| `papers/paper/octonion_lightcone_to_oshoracle.tex` | Includes patch contract; honest finite vs continuum checklist |
| `HQIV/paper/main.tex` | **Often reads as continuum-first GUT**; abstract uses “complete grand-unified theory.” Agents editing there should apply [MAIN_PAPER_FLRW_LEAN_ALIGNMENT.md](./MAIN_PAPER_FLRW_LEAN_ALIGNMENT.md) **and** this file. |
| `AGENTS/MAIN_PAPER_FLRW_LEAN_ALIGNMENT.md` | FLRW/HQVM **algebraic** anchors—not patch ontology (complementary) |

**Suggested `main.tex` lead (authoring, not applied here):** early `\input` or paraphrase of `patch_theory_messaging.tex`; replace “complete GUT” with **patch-closed unified framework** where completeness is claimed; rename “discrete-to-continuous transition” → **continuum translation layer**.

---

## Related agent docs (read order)

1. **This file** — ontology and completeness vocabulary  
2. [STORY.md](./STORY.md) — router + intentional divergences from textbook defaults  
3. [ASSUMPTIONS.md](./ASSUMPTIONS.md) — trust boundary, continuum checklist, scale witness  
4. [THEOREMS.md](./THEOREMS.md) — what is actually proved (names)  
5. [MAIN_PAPER_FLRW_LEAN_ALIGNMENT.md](./MAIN_PAPER_FLRW_LEAN_ALIGNMENT.md) — when touching cosmology wording in `main.tex`  
6. [CKM_PMNS_FANO_OVERLAP.md](./CKM_PMNS_FANO_OVERLAP.md) — flavour mixing discharge programme (open scaffold)  
7. `TrigSym/README.md` — simulator honesty (sparse vs dense, embed scope)

**Interactive:** `sim/patch_qft_bridge.html` — mode budget, time-angle shell index, Minkowski intervals (aligns with `PatchQFTBridge` / `LightConeMaxwellQFTBridge`).

---

## Quick checklist before shipping agent work

- [ ] Claims use **patch-closed** / **accessible patch** / **finite layer** where “complete” or “QFT” appear  
- [ ] Continuum limits labeled **readout** or **calculation approximation**, **never** as “open problem” or “future work that completes the theory”  
- [ ] In load-bearing places (\(\delta_E(m)\), mass ladders, lock-in vev, proton anchor, \(\alpha=3/5\), \(\gamma=2/5\), \(\alpha_{\rm GUT}=1/42\)), add an explicit note such as “a continuum version would destroy these results”  
- [ ] References to \(\mathfrak{so}(8)\)/\(\mathrm{SO}(8)\)/\(G_2\)/\(\Delta\) and their exponentials use the **de-facto continuum algebra from discrete construction** framing (allowed; one principled exception)  
- [ ] Simulator scope matches **gate closure** on support (no silent aliasing)  
- [ ] Cosmology claims distinguish **patch ladder** vs **CLASS homogeneous channel**  
- [ ] New formal claims have a `THEOREMS.md` row; new trust boundaries extend `ASSUMPTIONS.md`
