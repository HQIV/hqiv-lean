# Lightcone → fundamentals: derivation plan (and HQIV corrections)

This document is a **roadmap for agents**: how “standard” fundamental equations (kinetic theory, continuum balance laws, linear response, emergent bulk dynamics, scattering constraints, fermionic minimal coupling, information bounds) can be **anchored** to the two HQIV axioms—**discrete null lattice + octonion mode counting** and **informational-energy / horizon monogamy** (metric, φ ladder, γ split)—and where the repo already has **proved scaffolding** versus **hypothesis bundles** only. For the Maxwell thread, the current repo direction is **algebra-first**: `G₂ ∪ {Δ}` seed + extracted H-block + tipping/rapidity slot first, with `phi_of_T` only as a later projection layer.

**Honesty rule (same as [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md)):** name what is **proved in Lean**, what is **normative Python/paper closure**, and what remains **conjecture**. Do not merge marketing language with Mathlib theorems.

**Canonical constants:** $\alpha=3/5$, $\gamma=2/5$ — see [ASSUMPTIONS.md](./ASSUMPTIONS.md) §1b.

**Lean scaffold (defs + hypothesis bundles + GR re-exports):** `Hqiv/Physics/LightConeFundamentalsPillars.lean` — see [THEOREMS.md](./THEOREMS.md) row for `uvRegulatorShellBudget` / `BalancePillarWithHQIVGamma` / …

**Nearby ladders (do not duplicate):**

- Fluid / plasma / modified NS closure: [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md), [NAVIER_STOKES_HQIV_NARRATIVE.md](./NAVIER_STOKES_HQIV_NARRATIVE.md)
- Manifold-valued rapidity / Ricci-weighted δ_E / zeta: [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md)
- Maxwell / QFT bridge on finite patches: `Hqiv/Physics/LightConeMaxwellQFTBridge.lean`, `ContinuumManyBodyQFTScaffold.lean` (see [THEOREMS.md](./THEOREMS.md))
- SM–GR unification narrative: `Hqiv/Physics/SM_GR_Unification.lean`, `GRFromMaxwell.lean`

---

## 0. What “derived” means here

| Level | Meaning | Examples in repo |
|-------|---------|------------------|
| **L0 — Combinatorial / algebraic** | Identities from definitions on ℕ, ℝ, finite matrices | `OctonionicLightCone`, `AlphaGammaForcedByLattice`, mode budgets |
| **L1 — Chart / continuum identities** | Same structures embedded in analysis-style fields on stated domains | `OMaxwellAlgebraSeed`, `ModifiedMaxwell`, `ContinuumOmaxwellClosure`, `LightConeMaxwellQFTBridge` |
| **L2 — Effective closure** | Constitutive maps (transport, viscosity, ε(φ), μ(φ)) stated as **definitions + hypotheses** | `HQIVFluidClosureScaffold`, `pyhqiv.fluid` |
| **L3 — Classical PDE / global QFT** | Standard well-posedness or Wightman-style axioms | **Not** claimed here; milestones below stop at L2 unless noted |

**HQIV “corrections”** usually mean: prefactors or source terms controlled by **φ**, **Θ**, **δ̇θ′**, shell index $m$, or **horizon-dependent** curvature imprint—not arbitrary new parameters.

---

## 1. Pillar A — Relativistic kinetic theory (Boltzmann / Vlasov)

**Standard target:** phase-space density $f(x,p)$ with collision operator $C[f]$; conservation laws integrated to fluid dynamics.

**HQIV anchor:** modes are **counted** per shell $m$; causal access is **finite** along the cone (`accessibleModeBudgetUpToShell`-style statements). Kinetic theory is the natural language for **how shell-to-shell redistribution** produces entropy production and stress.

| Milestone | Goal | Lean / code touchpoints | Status |
|-----------|------|-------------------------|--------|
| **K0 — State space** | Define discrete velocity / momentum bins tied to shell index or a chosen rapidity chart | `SpatialSliceRapidityScaffold`, `AuxiliaryField.phi_of_T`, algebra-first Maxwell seed / tipping layer in `OMaxwellAlgebraSeed` | Partial (scaffold) |
| **K1 — Boltzmann form** | Write **symbolic** Boltzmann equation with collision term **labeled** “from horizon exchange” (not proved microscopic cross-section) | New `Prop` bundle or paper subsection; optional Python prototype | Open |
| **K2 — Hydrodynamic limit** | Chapman–Enskog / moment expansion → stress tensor + heat flux; **identify** transport coefficients with **HQIV closures** (φ, Θ, γ) | Bridges [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md) F2–F3 | Open (hypothesis layer) |

**Correction story:** collision strength or **mean free path** scales with **local horizon** data (Θ, Compton-style bridges) rather than a fixed external $\lambda_{\mathrm{mfp}}$.

---

## 2. Pillar B — Continuum balance laws (stress–energy, Navier–Stokes limit)

**Standard target:** $\nabla_\mu T^{\mu\nu} = 0$ (matter + fields), Navier–Stokes as a **viscous** limit of stress.

**HQIV anchor:** `Conservations`, `Action`, `Forces`; modified fluid scaffold (`HQIVFluidClosureScaffold`).

| Milestone | Goal | Touchpoints | Status |
|-----------|------|-------------|--------|
| **B0 — Named stress split** | EM + matter + **effective** HQIV stress from algebraic-slot / φ / δθ channels | `OMaxwellAlgebraSeed`, `ModifiedMaxwell`, `Forces` | Partial |
| **B1 — Modified momentum equation** | Closed form for $f$, $\mathbf g_{\mathrm{vac}}$, $\nu_{\mathrm{eddy}}$ | `HQIVFluidClosureScaffold`, `pyhqiv.fluid` | L2 closure (see fluid roadmap) |
| **B2 — Classical NS limit** | Sufficient conditions for reverting to incompressible NS | [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md) F4–F5 | Coefficients only; full PDE limit open |

**Correction story:** inertia factor, vacuum momentum source, eddy viscosity — already specified in [FLUID_OMAXWELL_ROADMAP.md](./FLUID_OMAXWELL_ROADMAP.md) §0.

---

## 3. Pillar C — Linear response (Kubo / Green–Kubo)

**Standard target:** conductivity, viscosity, susceptibilities from **equilibrium correlators** or small perturbations.

**HQIV anchor:** horizon monogamy split γ; fluctuations tied to **shell** transitions rather than an abstract thermal reservoir.

| Milestone | Goal | Touchpoints | Status |
|-----------|------|-------------|--------|
| **C0 — Linearized perturbations** | Consistent small-field expansion around a **lattice-indexed** background | `HQVMPerturbations` (metric), `HQIVPerturbationScaffold` (Θ = `T m`), plasma scalars | Partial — see [HQIV_PERTURBATION_THEORY_ROADMAP.md](./HQIV_PERTURBATION_THEORY_ROADMAP.md) |
| **C1 — Response kernels** | Define **formal** Kubo formulas with HQIV weighting (e.g. φ(m), δ_E(m)) | New scaffold module or AGENTS subsection after first numeric prototype | Open |
| **C2 — Cross-check** | Transport coefficients **consistent** with `ν_eddy` / plasma closures when parameters align | `HQIVFluidClosureScaffold`, `SchematicPlasmaCurrent` | Open |

**Correction story:** spectral weight is **UV-regulated** by accessible mode budgets (finite cone patches), not an infinite continuum prior.

---

## 4. Pillar D — Einstein / emergent bulk equations

**Standard target:** Einstein field equations $G_{\mu\nu} = 8\pi G\, T_{\mu\nu}$ (or derived analogue).

**HQIV anchor:** `GRFromMaxwell`, `SM_GR_Unification`; curvature imprint δ_E(m) and shell-wise **Ω_k** narrative.

| Milestone | Goal | Touchpoints | Status |
|-----------|------|-------------|--------|
| **D0 — Same-stress coupling** | Maxwell/O-Maxwell stress → sourced Einstein **as stated identities** on a chart | `GRFromMaxwell` | See [THEOREMS.md](./THEOREMS.md) |
| **D1 — Horizon sourcing** | Map **informational** monogamy / area scaling to **effective** stress (tensor-network / holographic **analogy**) | Paper-level; [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) for Ricci-weighted δ_E | Narrative + partial scaffolds |
| **D2 — Full emergence** | Derive **closed** Einstein equations from discrete dynamics alone | **Out of scope** for current Lean mission unless new axioms | Open |

**Correction story:** $G_{\mathrm{eff}}$ / imprint **α** ladders and horizon-dependent curvature (not a single global Ω_k for all observers).

---

## 5. Pillar E — Scattering, unitarity, analyticity

**Standard target:** optical theorem, $S$-matrix unitarity, dispersion relations.

**HQIV anchor:** **normalized** digital evolution (`DiscreteQuantumState`, `IsNormalized` in the octonion lightcone paper); finite-dimensional unitary blocks as **UV completion** of accessible patches.

| Milestone | Goal | Touchpoints | Status |
|-----------|------|-------------|--------|
| **E0 — Finite-sector unitarity** | Prove **norm preservation** on stated finite spaces | Octonionic lightcone / discrete quantum modules | See preprint + Lean names in paper |
| **E1 — Patch composition** | Consistent gluing of **accessible** regions (causal diamond budgets) | `LightConeMaxwellQFTBridge` | Partial |
| **E2 — Continuum S-matrix (comparison layer)** | Full continuum QFT scattering is **not required** by HQIV (patch-closed; see [PATCH_ONTOLOGY.md](./PATCH_ONTOLOGY.md)); kept only as a **calculation-approximation** target for comparison with textbook S-matrix formulas | N/A | Not claimed; not an HQIV open problem |

**Correction story:** **IR cutoff** = horizon; **UV cutoff** = shell/mode budget — unitarity holds **after** restricting to accessible sectors.

---

## 6. Pillar F — Dirac / fermions (minimal coupling)

**Standard target:** Dirac equation $ (i\gamma^\mu D_\mu - m)\psi = 0$.

**HQIV anchor:** SM embedding in octonions / SO(8), spin-statistics scaffolding, directional monogamy/redshift clustering in the continuum closure branch, resonance mass ladders (see `SMEmbedding`, `SpinStatistics`, `HorizonLimitedRenormLocality`, lepton/nucleon bridges in [THEOREMS.md](./THEOREMS.md)).

| Milestone | Goal | Touchpoints | Status |
|-----------|------|-------------|--------|
| **F0 — Gauge covariant derivative** | Same algebraic embedding used for YM | `SMEmbedding`, `PhaseLiftDelta` | Proved fragments |
| **F1 — Dirac equation as effective** | Statement on a chart with **HQIV** mass/phase **replacements** (continuum chart is a **calculation approximation**; see [PATCH_ONTOLOGY.md](./PATCH_ONTOLOGY.md)) | New module or extension of `Action` | Comparison-layer scaffold (L2) |
| **F2 — Mass spectrum** | Lock to **ladder** masses (no PDG fits per user rules) | `ChargedLeptonResonance`, nucleon modules | See ASSUMPTIONS |

**Correction story:** masses and phases from **shell resonance** conditions; not independent knobs.

---

## 7. Pillar G — Information bounds (Bekenstein, channels)

**Standard target:** entropy bounds, monogamy inequalities, channel capacities.

**HQIV anchor:** γ split; **mode counting**; horizon as IR regulator.

| Milestone | Goal | Touchpoints | Status |
|-----------|------|-------------|--------|
| **G0 — Counting entropy** | Entropy functional from **log of accessible microstates** on shells | Combinatorics in `OctonionicLightCone` | Algebraic |
| **G1 — Bekenstein-style bound** | State inequality linking **energy on shell** to **mode count** | Hypothesis bundle + dimensional analysis | Open |
| **G2 — Thermodynamics link** | Connect to existing thermo narrative (companion manuscript) | [ASSUMPTIONS.md](./ASSUMPTIONS.md) | Narrative |

**Correction story:** coefficients set by **(α, γ)** and octonion factor 8, not fitted.

---

## 8. Suggested work order (for agents)

1. **Lock vocabulary** across pillars: same symbols for φ, Θ, $\dot\delta\theta'$, shell $m$, and horizon proxies (already started in fluid roadmap).
2. **Kinetic (K0–K1)** before ambitious continuum theorems: discrete collision **semantics** prevent hand-waving about “thermalization.”
3. **Linear response (C0–C1)** after **B1** is stable: transport coefficients should **agree** with `ν_eddy` / plasma hypotheses in overlapping regimes.
4. **Einstein emergence (D1)** stays **paper-level** until [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) milestones advance Ricci-weighted δ_E / 3-manifold integrals.
5. **S-matrix (E2)** remains **out of scope** unless the project explicitly funds rigorous infinite-volume QFT.

---

## 9. Artifacts to produce when advancing this plan

| Artifact | Purpose |
|----------|---------|
| New Lean **hypothesis** bundles (`structure … where`) | Make gaps **typeable** (not only prose) |
| One **numeric** script per pillar (optional) | Kubo-like sanity checks, kinetic toy, etc. |
| One-line entries in [THEOREMS.md](./THEOREMS.md) | Only when a **new** proved lemma ships |
| Updates to [ASSUMPTIONS.md](./ASSUMPTIONS.md) | New `sorry`s, script trust, or explicit axioms |

---

## 10. Related O-Maxwell / fluid note (macroscopic MHD)

Macroscopic **MHD** (ideal/resistive) is a **composite** of Maxwell balance + fluid velocity + conductivity. In HQIV it should inherit **O-Maxwell** constitutive relations and the **modified fluid** layer; see `paper/HQIV_OMaxwell_fluid_chart.tex` and align any new MHD section with **Pillar B** and **Pillar A** above (derivation order: kinetic → fluid → MHD).
