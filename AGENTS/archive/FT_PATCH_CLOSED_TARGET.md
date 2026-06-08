# Fourier / patch — **closed targets** (no SAT)

This file does what the proof roadmap needs first: **name falsifiable statements** with exact Lean hooks, **before** any SAT bridge. If a target fails on the benchmark suite, you **stop** proving that variant.

---

## 0. Honest gap: toy score ≠ Lean Fourier sum

**Python** (`hqiv_geometric_3sat_demo.moire_score_samples`):

\[
S(j)=\sin(\phi + \theta j)\cdot \cos\!\Bigl(\frac{M \bmod (j+7)}{j+7}\Bigr),
\quad \theta=\frac{\pi}{2k_{\mathrm{enc}}},\ \phi = 2\pi \cdot \{V_8(\sqrt M)\}.
\]

**Lean** (`Hqiv.Algebra.OctonionSphereFourierPatch`):

- `fourierPatchPeakCorrelation` — **complex** sum of `window × κ × exp(i·axisAngle·j)` (DFT-style).
- `FourierPatchConcentration` — **peak vs side-lobe** bounds (`OtherCoeffsSmall`).

So: **Target 0** (prerequisite for a unified FT proof) is either:

- **(0a)** Replace / augment the toy so `S(j) = (wκ)`-correlation (e.g. `re` / `‖·‖`) for **named** `w, κ` satisfying `KernelIsHarmonic`, or  
- **(0b)** Prove nontrivial bounds **directly** on the **existing** `S(j)` as a signal model (harder, ad hoc).

**Partial (0a) (in repo):** `hqiv_geometric_3sat_demo` now exposes a **numeric mirror** of Lean’s peak sum — `fourier_patch_peak_correlation_complex(k_enc, n, w, κ)` — using the same intrinsic phasor `exp(i·π/(2k_enc)·j)` as `fourierPatchPeakCorrelation` / `axisAngle`. Helpers `kernel_harmonic_character_j`, `intrinsic_shell_phasor_j`, and `moire_combined_phasor` separate the **Lean layer** from the toy’s extra `cos` modulation; `moire_sine_factor_without_modulation` identifies `sin(φ+θj)` with `Im(exp(i(φ+θj)))`. The **full** toy `moire_score_samples` is still **not** equal to `re`/`im` of that peak sum until you fold the modulation into `w` or redefine `S`.

Until full (0a) or (0b) is settled, “FT finds the modes” as **one** closed-form object is still **story** for the modulated score.

### P-search vs witness existence (program; completeness still open)

Two different questions get layered:

1. **Search in P (patch order).** Monotone `cum[j]` + threshold ⇒ **BST** locates a crossing in **`O(log n_patch)`** predicate evaluations (Target B — order-theoretic, not SAT). Default `n_patch` scales **linearly with clause count**, not `2^n_vars`. So this layer is **not** “try all `2^n` assignments in disguise.”

2. **Witness existence (NP-type).** Whether a **satisfying assignment exists** is the formula’s SAT question. The **axis** `θ = π/(2k)` (proved hooks in `OctonionAxisAngles` / jerk layer) fixes **how** the score winds along `j`; it does **not**, by itself, prove that a witness must appear at a particular `j` or after finitely many **k**-labeled rotations.

**Intended analogy (factorization narrative):** try structured rotations / an increasing **`k`**-family of modes (like trial factors); **exhaust** that structured search and then **declare** the residual case (e.g. “prime” / UNSAT / out-of-model). That story is **sound** as a **procedure** once each check is cheap; **completeness** (“if a factor exists, this search finds it”) is exactly the **theorem** you still need: **if SAT, then** the witness lies **on the patch** (or in the declared rotation set) — the same class of statement as “answers live at the FT intersection,” not proved from the axis lemmas alone.

**What we already have:** polynomial-time **search mechanics** on the patch index and explicit **π/(2k)** algebra. **What remains:** a **single** formal bridge `∃ assignment` ⇒ `∃ j` (or `∃` rotation in the finite family) meeting your predicate — or a clearly **smaller** problem class where that is provable.

---

## 1. Closed Target A — **spectral concentration** (Lean-ready)

**Statement (qualitative):** For fixed `n`, window `w`, harmonic kernel `κ` at arity `k`, and shell `m` with `Ω m = k`, the **peak** Fourier correlation dominates **off-`k`** correlations:

- Formal bundle: `FourierPatchConcentration` in `OctonionSphereFourierPatch.lean`  
  (`fourier_patch_concentration` packages hypotheses).

**Falsify if:** For your chosen `(w, κ, m)`, ∃ `k' ≠ k`, `‖fourierPatchSideCorrelation k' …‖ > ε · ‖fourierPatchPeakCorrelation …‖`.

**Proof inputs already in library:** `KernelIsHarmonic`, `fourierPatchPeakCorrelation_eq_axisAngle` (phasor matches `π/(2k)` when `Ω m = k`), geometric-series orthogonality lemmas referenced in the module doc.

**Not in library:** Analytic **decay** of `w` and quantitative `ε` — those stay **hypotheses** until proved from a concrete window.

---

## 2. Closed Target B — **BST / cumulative variation** (mostly done)

**Statement:** For monotone `cum[j]` and threshold `T`, the **smallest** `j` with `cum[j] ≥ T` is unique in `Fin n` order; binary search (monotone predicate) returns that index.

- **Monotone `cum`:** `moireCumulativeAbsVariation_mono` (`MoireCuspBracket`).  
- **One-step crossing:** `moire_first_ge_threshold_eq_succ`, `moire_last_below_threshold_eq_pred`.  
- **Nonempty bracket:** `exists_isLeast_moire_cum_ge`, `exists_isGreatest_moire_cum_lt` (`MoireToyThresholdSearch`).

**Still missing:** A short Lean proof that **`binary_search_smallest_true`** (Python) equals `Finset.min'` / `IsLeast` — routine order theory.

**No SAT content.**

---

## 3. Closed Target C — **slope step (jerk) as discrete curvature**

**Statement (local):** Triangle bound on one step — already proved:

- `abs_moirePatchSlopeStep_le_add_adjacent_slopes` (`MoireCuspBracket`).

**Sinusoid + `Ω` (Lean):** For the **intrinsic-axis** model `S(j)=sin(α + intrinsicShellAxisAngle m · j)` with `Ω m = k`, `moirePatchSlopeStep` has the closed form in `moirePatchSlopeStep_sin_intrinsic_of_Omega`, and `moirePatchSlopeStep_sin_intrinsic_eq_zero_iff` characterizes zeros (`MoireJerkSphereModeBridge`). This does **not** identify the Python toy `S(j)` with that model without Target 0.

**Stronger (optional, testable on synthetics):** If `S` is a **single** discrete sinusoid on `Fin n` at frequency related to `θ`, then `max |Δ²S|` occurs near **phase alignment** / known index formula (pure discrete calculus — no CNF).

**Falsify if:** On synthetic single-frequency `S`, the argmax of `|moirePatchSlopeStep|` misses the predicted band (implement checker on random phases).

**Still not SAT.**

---

## 4. Shell / area bridge (long-run, name only)

**Conjecture shape (not a current theorem):** A quantitative inequality linking **‖fourierPatchPeakCorrelation‖** (or energy in the `k` harmonic of a lifted window) to **shell** data (`r₈(m)`, or continuous `A₇(√m)` / `V₈(√m)` proxies) for `m` tied to encoding.

**Status:** Narrative in `OCTONION_SPHERE_PATCH.md` / shell modules — **no** `FourierPatchConcentration`-level bundle yet. Treat as **Clay-scale glue** unless you add explicit `Prop` + numerical pipeline.

---

## 5. What to run

| Goal | Action |
|------|--------|
| Falsify spectral concentration for the **current** toy `S(j)` | `python3 scripts/ft_patch_closed_target_probe.py` (DFT energy diagnostic on `moire_score_samples`) |
| Prove BST = `min'` | Small Lean snippet in `MoireToyThresholdSearch` or separate file |
| Unify toy with Lean FT | Implement (0a): build `w, κ` from the same parameters as `S`, or redefine `S` from `re(peak sum)` |

---

## 6. Rule

**Do not** mix Targets A–C with SAT until at least one of them survives falsification on your **fixed** `(w, κ)` or **redefined** score. Otherwise you optimize a story that tests have already killed.
