# HEP decay readout — paper phrasing guide

**Scope:** `papers/hep_decay_readout/hqiv_hep_decay_readout_from_multichannel.tex` (Preprint v1) and companion reproducibility text.

**Parent contract:** [PATCH_ONTOLOGY.md](./PATCH_ONTOLOGY.md) — patch-closed ontology, continuum as comparison dictionary.

---

## Core principles (use consistently)

| Prefer | Avoid (unless qualified immediately) |
|--------|--------------------------------------|
| Readout from the **fixed / proved discrete** three-ledger **spine / carrier** | Unqualified “derived from first principles” |
| **Combinatorial derivation on the proved three-ledger carrier** / **within the HQIV discrete patch ontology** | “Derived from causal-set axioms” |
| **Quarantined comparison layer** | “Comparison layer” alone (always say *quarantined* when citing PDG/facility inputs) |
| **No per-channel form factors, partial-width tables, or PDG inputs enter the prediction path** | Implying PDG enters formulas |
| **Programmatically generated** from daughter pools + kinematic filter + ledger assignment + **property-generated spanning sets** | Manual channel tables / per-parent tuning |
| **Theorem of the monogamy bookkeeping / dimension-balance / unit-split on the fixed carrier** (for α, γ, f_EM, contact weights) | Adjustable multipliers / fitted Wilson coefficients |
| **Finite-patch readout calculation** | Continuum-QCD derivation |
| **First principles with respect to the discrete null-lattice carrier and three-ledger discipline** | “First-principles derivation of [observable]” without qualification |
| **Lean certificate: `theorem_name`; zero-sorry theorem in `Module.lean`** | Bare numeric coincidence |
| **HQIV-only slots** — genuine predictions of the discrete carrier | “Prediction targets” without falsifiability framing |
| **Obtained without using the PDG value as an input to the formula** | Silent agreement with PDG |

---

## Standard blocks (copy/adapt)

### Prediction path + quarantine

> The derivation proceeds along a fixed pipeline with no feedback from data: discrete null-lattice carrier (α = 3/5, γ = 2/5, referenceM = 4) → three non-interchangeable ledgers → spine-discharge contacts → width layer → normalization. All PDG values, facility thresholds, and global-fit CKM elements are confined to a **quarantined comparison layer** and never inserted into formulas or contact seeds.

### Honesty boundary

> The readout is first-principles **with respect to the discrete patch ontology and the proved three-ledger spine**. It is **not** a derivation from the continuum QCD Lagrangian, lattice matrix elements, or causal-set axioms alone without the octonionic/Fano seed and dimensional-balance inputs fixed upstream. Continuum language is a **translation dictionary** only.

### f_EM / J/ψ

> $f_{\mathrm{EM}} = 1/\gamma + 1 + \gamma/2 = 37/10$ is a **theorem of the monogamy bookkeeping on the fixed carrier** (Lean: `hiddenQuarkoniumEMContactFactor_eq_thirtyseven_tenths`). With pooling, $\mathcal{B}(J/\psi\to e^+e^-)\approx 5.97\%$ on the quarantined comparison layer.

### Isospin charge routing

> $\Delta m = I_3 \cdot \gamma \cdot \mathrm{nucleonIsospinGap\_MeV}$ (`isospinThirdChargeShiftMeV`; $= I_3 \cdot 2/5\,\mathrm{MeV}$ at lock-in). $I_3$ labels come from **catalog valence** (`baryonValenceIsospinThird` / `mesonValenceIsospinThird` → `isospinThirdSlotOfRational`), not PDG-key lookup tables. Breaks $^0/^\pm$ degeneracy without PDG mass injection.

### Excited mass panel (comparison metrics — do not overclaim σ)

> **Primary metric:** scale-free mass error $|\Delta|/M$ (mean **~0.23%**, median **~0.18%**, max **~0.77%** on open-$D^*$ ground at last export).
>
> **Generous listed σ** ($\sigma \ge 1\%$ of mass, assignment-level bands): **11/11 within 1σ**.
>
> **Listed PDG σ (strict, all 85):** $n_\sigma = \Delta/\sigma_{\mathrm{PDG}}$ — pulls dominated by Type A precision-tagged rows; use $|\Delta|/M$ there.
>
> **Outlier taxonomy:** Type A = σ ill-posed; Type B = TUFT chart granularity ($N(1440)$, $\Delta$, $\omega$); Type C = discharged γ-rational slot factors ($D^{*0}(2S)$, $\psi(2S)$, $\Upsilon(1S)$, $\Xi^*$). See `ExcitedMassComparisonHonesty.lean`.

### Charmed $\Xi_c'$ excitation

> Ground $\Xi_c$ plus $\Sigma_c$ hyperfine step net of shallow $\gamma/16$ radial slot: `charmedBaryonXiPrimeExcitationFactor = 1 + γ/6 − γ/16 = 25/24` (not a fitted offset).

### Consistency vs fit

> Close agreement on the curated panel is a **non-trivial consistency check** of the three-ledger discipline, not a post-hoc fit. Contact registry and ledger weights are **programmatically generated** from the same combinatorial rules as masses/widths in companion works—not adjusted per channel to match PDG.

### Reproducibility

> The one-command pipeline **regenerates the benchmark and readout export before any quarantined comparison-layer JSON is consulted** for pass/fail scoring.

---

## Do not use in user-facing paper text

- Changelog language: “we fixed Python”, “previously”, “before publication”, “promoted before publish”, “removed erroneous divisor”
- Process artifacts: “Python mirror bug”, “registry extension to close gaps” (say **discharged contact** / **theorem bundle** instead)
- Unqualified: “derives branching ratios from first principles”, “derived from axioms”

---

## Cross-links

- Lean capstone: `Hqiv/Physics/HepAnomalyDischarge.lean`, `HepExtendedAnomalyDischarge.lean`, `HepDecayReadout.lean`
- Reproducers: `papers/hep_decay_readout/scripts/hqiv_hep_readout_pipeline.py paper --strict`
- Bib key: `hqiv-hep-decay-paper` in `papers/references.bib`
