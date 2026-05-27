# Roadmap: effective fluid / plasma ↔ O-Maxwell (status-tracked ladder)

This document is a **proof and implementation path** for agents: how the **HQIV modified fluid** story (inertia factor, vacuum source, eddy viscosity) could attach to **O-Maxwell + continuum closure** already in the library, and—only later—to **classical Navier–Stokes** as a limit. It mirrors the discipline of [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) and the **RH analogue ladder** (`lambdaHQIV`, Tao–Rodgers **packaging** in Lean, not a claim on classical `Λ`): **name what is proved vs what is hypothesis**.

**Paper-level NS background (not a Lean PDE):** [NAVIER_STOKES_HQIV_NARRATIVE.md](./NAVIER_STOKES_HQIV_NARRATIVE.md).

**Unified four-problem context (probe only):** [MILLENNIUM_UNIFIED_NARRATIVE.md](./MILLENNIUM_UNIFIED_NARRATIVE.md).

---

## 0. Effective narrative (what we are trying to formalize)

**Physical hierarchy (design language, not a single theorem):**

1. **Plasma / matter + fields** are governed by **inhomogeneous O-Maxwell** (and metric/auxiliary structure) in HQIV—see `OMaxwellAlgebraSeed`, `ModifiedMaxwell`, `ContinuumOmaxwellClosure`, `LightConeMaxwellQFTBridge` for what is actually **proved** at the level of chart identities and mode budgets.
2. **Collective modes** admit an **effective fluid** closure: momentum and stress as **coarse-grained** variables. In this theory, treating plasma as a **viscous fluid with HQIV transport** is intentionally **easier** than deriving **molecular viscosity** bottom-up from kinetic theory.
3. The **modified** fluid layer uses the same **auxiliary field** and **rapidity/clock** language as elsewhere: local **Θ**, **φ**, and **δ̇θ′** (or packaged equivalents) enter **inertia**, **vacuum momentum source**, and **eddy viscosity**—recovering **standard incompressible NS** only in a **stated limit** (laminar / large-acceleration / coherence choices).

**Reference implementation (Python):** `hqvmpy/src/pyhqiv/fluid.py` (re-exported from `pyhqiv`); legacy copy in `hqvmpy/bak/pyhqiv/fluid.py`. Intended **equations**:

- **Modified inertia:** \(f(a_{\mathrm{loc}},\varphi) = a_{\mathrm{loc}}/(a_{\mathrm{loc}}+\varphi/6)\) (clamped in code), so \(\rho f\,\mathrm D\mathbf v/\mathrm dt = \text{RHS}\) ⇔ \(\mathrm D\mathbf v/\mathrm dt = \text{RHS}/(\rho f)\).
- **Vacuum source:** \(\mathbf g_{\mathrm{vac}} = -\frac{\gamma}{6}\nabla(\varphi\,\dot\delta\theta')\).
- **Eddy viscosity:** \(\nu_{\mathrm{eddy}} = \gamma\,\Theta_{\mathrm{local}}\,|\dot\delta\theta'|\,\ell_{\mathrm{coh}}^2\,C\) with \(C\in[0,1]\) (coherence; **high coherence / plasma** narrated as \(C\approx 1\)).

Lean names the same objects in `Hqiv.Physics.HQIVFluidClosureScaffold` (**definitions + small algebra** only). O-Maxwell → fluid **derivations** remain future **hypothesis bundles** or limits.

---

## Status snapshot (now)

### In place (anchors agents can cite)

- **F0 — Vocabulary (done):** `Hqiv/Physics/HQIVFluidClosureScaffold.lean` — `hqivFluidInertiaFactor`, `hqivVacuumMomentumSource3`, `hqivEddyViscosity`, `hqivEddyViscosity_HQIV` + lemmas (`phi = 0` ⇒ `f = 1`, positivity, vacuum source vanishes when gradients vanish). **Not** NS PDEs.
- **F1 — Effective spec + tests (done):** `hqvmpy/src/pyhqiv/fluid.py` aligned with `gamma_hqiv()`; `hqvmpy/tests/test_fluid.py` (run: `PYTHONPATH=src python3 -m unittest tests.test_fluid`).
- **F2 — Attachment map (done, hypotheses only):** the **F2** section below, plus the same content in `HQIVFluidClosureScaffold.lean` and `pyhqiv.fluid` module docs. **No** new proved equalities between sectors.
- **F3 — Plasma-as-fluid closure (done):** `PlasmaFluidClosureAssumptions` + `nuTotal_eq_nuMol_add_hqivEddy` in Lean; `PlasmaFluidClosureHypothesis` + `holds()` in `pyhqiv.fluid`; §F3 below. **Not** kinetic derivation.
- **F4 — Classical NS coefficients (done, algebraic only):** `CoefficientsTowardClassicalNS` + example lemma in Lean; §F4 below. **Not** classical 3D NS well-posedness.
- **F4.5 — Action/O-Maxwell → HQIV DNS-shaped momentum bridge (done, reduced):** `HQIVFirstPrinciplesNSBridge` in `HQIVTurbulenceSimulatorScaffold.lean` proves that O-Maxwell action/EL chart data plus F2 chart identification, F3 scalar viscosity closure, and an explicit continuum balance hypothesis imply the HQIV lapse-modified DNS momentum component. `HQIVFirstPrinciplesNSBridgeCanonical` / `HQIVFirstPrinciplesNSBridgePlasmaAmp` discharge the F2 chart identification, shell/Debye closure, and plasma-coherence interval bookkeeping. **Not** molecular-viscosity derivation or PDE regularity.
- **O-Maxwell / continuum / QFT bridge:** chart-level lemmas and budgets (e.g. emergent Maxwell RHS, accessible shells)—see `THEOREMS.md` entries for `ContinuumOmaxwellClosure`, `LightConeMaxwellQFTBridge`; unification narrative in `SM_GR_Unification.lean` (O-Maxwell φ-corrections are **effective** coupling story, not NS).
- **Rapidity / slice scaffolding:** `SpatialSliceRapidityScaffold.lean` — lattice rapidity, shells, **probe** domains; **not** a 3D fluid theorem.
- **RH-style analogue boundary packaging:** `tempLadder` / `lambdaHQIV` scaffolds — **template** for “hypothesis fields → proved consequence in a toy bundle,” **not** classical RH or classical NS global regularity.

### Not in place (do not attribute to the repo)

- No **Lean** PDE for modified **or** classical **3D incompressible NS** global well-posedness.
- No **proved** derivation from **O-Maxwell + kinetic plasma** to molecular viscosity or the **closed** fluid system in §0. What is now proved is narrower but stronger than before: action/O-Maxwell chart data plus canonical HQIV closure/coherence constructions and one explicit continuum stress-balance hypothesis imply the HQIV DNS-shaped momentum equation.
- No **automatic** identification of \(\nu_{\mathrm{eddy}}\) with a **measured** viscosity; **C**, \(\ell_{\mathrm{coh}}\), and \(\Theta_{\mathrm{local}}\) remain **closure parameters** until tied to definitions.

### Plasma-first next steps (recommended order)

Work here multiplies across **O-Maxwell**, **fluid**, and **scripts**: same \(\gamma\), \(\varphi\), \(\Theta\), \(\delta\theta'\) slots as the rest of HQIV.

1. **Name \(\Theta_{\mathrm{local}}\) and \(\ell_{\mathrm{coh}}\) in Lean** — **done (bookkeeping):** `Θ_{\mathrm{local}} = T(m)` and \(\ell_{\mathrm{coh}}=\texttt{lambdaDebye}\) are wired into `hqivEddyViscosity_HQIV` via `hqivEddyViscosity_HQIV_shell_debye`, `PlasmaFluidClosureAssumptions.mk_shell_debye`, and `BalancePillarShellDebye` (`HQIVFluidClosureScaffold`, `LightConeFundamentalsPillars`). Next: choose **physical** horizon proxies beyond this identification, or **current**→stress coupling.
2. **Plasma current \(\to\) stress / closure** — **partial (bookkeeping):** `J_O_plasma_eq_schematic_on_em`, `abs_J_O_plasma_em`, and `coherenceFromPlasmaAmp` + `mk_shell_debye_plasmaAmp` tie the **same** scalar amplitude to Maxwell (`J`) and to F3 coherence `C` (still **not** a full stress tensor or momentum PDE).
3. **Python parity** — keep `pyhqiv.fluid` (and any alignment scripts) using the **same** symbols as `HQIVFluidClosureScaffold` for any new closure hooks; add tests when new hypotheses get numeric defaults.
4. **F2 chart regression** — when changing plasma or horizon proxies, re-run / extend `scripts/fluid_f2_chart_alignment.py` (and `paper/HQIV_OMaxwell_fluid_chart.tex` if the hypothesis map changes).

**Action ↔ fluid:** `ActionPlasmaBridge` (`L_O_source_general_J_O_plasma_plasmaProxyCoordUniform`, `plasma_action_coherence_same_schematic_core`) records that **`schematicPlasmaScalar j₀ r`** feeds both the gauge **J·A** sum and **`coherenceFromPlasmaAmp`** (via `|·|`). Derived packaging: `L_O_source_general_J_O_plasma_uniform_eq_j₀_mul_profile_mul_sum`, `coherenceFromPlasmaAmp_eq_min_mul_abs_j₀_profile`, `plasma_action_coherence_derived` (explicit **`plasmaRadialProfile r`** factor in both). Further: `L_O_source_general_J_O_plasma_uniform_add`, `hqivEddyViscosity_HQIV_shell_debye_plasmaAmp_eq_profile`, `nuTotal_eq_nuMol_add_shell_debye_plasmaAmp_profile`; full-density **`J₁+J₂`** bookkeeping in `Action` (`L_O_Maxwell_general_add_J`, `action_total_general_add_J`); coherence **`min`** monotonicity / case splits in `HQIVFluidClosureScaffold`; **`plasmaRadialProfile_le_one_of_nonneg`** when `r ≥ 0`.

**Defer:** F5 PDE analysis until the closure table above has stable definitions and explicit hypotheses agents can cite.

---

## Ladder (milestones — step by step)

Work **in order** when formalizing or implementing. Each step should produce **artifacts** (modules, tests, or doc updates) so the next step is not ambiguous.

| Milestone | Goal | Done when |
|-----------|------|-------------|
| **F0 — Lock vocabulary** | Same symbols in Lean, Python, and paper: \(\varphi\), \(\Theta\), \(\dot\delta\theta'\), \(\gamma\), optional coherence \(C\). | **Done:** `HQIVFluidClosureScaffold.lean` + `pyhqiv.fluid` (defaults use `gamma_hqiv`). |
| **F1 — Effective fluid spec** | Treat `fluid.py` as **normative** for the **modified momentum** split: \(\mathbf g_{\mathrm{vac}}\), \(f\), \(\nu_{\mathrm{eddy}}\), and RHS \(\Rightarrow\) acceleration via \(f\). | **Done:** `tests/test_fluid.py` (laminar \(f\to 1\), \(\mathbf g_{\mathrm{vac}}=\mathbf 0\) when \(\nabla\phi,\nabla\dot\theta'=0\), \(\nu_{\mathrm{eddy}}>0\)). |
| **F2 — O-Maxwell attachment points** | Map **currents / stress** and **φ-gradients** in existing O-Maxwell lemmas to **inputs** of \(\mathbf g_{\mathrm{vac}}\) and \(\nu_{\mathrm{eddy}}\) **as hypotheses** (not as proved equality). | **Done:** §F2 table + `HQIVFluidClosureScaffold.lean` + `pyhqiv.fluid` module docs; **typed bundle** `OMaxwellFluidChartHypothesis` + `chartSpatialPhiGradient` / `chartSpatialDotGradient` + `hqivVacuumMomentumSource3_of_OMaxwellFluidChartHypothesis` (chart point \(c\), fields \(\varphi_F,\dot F\), proxy \(E'\)). |
| **F3 — Plasma-as-fluid closure** | State explicitly: **two-fluid / MHD-style** effective equations **imply** a stress form \(\tau = \tau_{\mathrm{mol}} + \tau_{\mathrm{eddy}}\) with \(\nu_{\mathrm{eddy}}\) from §0. | **Done:** `PlasmaFluidClosureAssumptions` / `nuTotal_eq_nuMol_add_hqivEddy` (Lean); `PlasmaFluidClosureHypothesis` (Python). |
| **F4 — Classical NS limit** | Prove or assume **sufficient conditions** under which modified equations reduce to \(\partial_t \mathbf u + (\mathbf u\cdot\nabla)\mathbf u = -\nabla p + \nu\Delta\mathbf u\), \(\nabla\cdot\mathbf u=0\). | **Done (coefficients only):** `CoefficientsTowardClassicalNS` + sample lemma; full PDE limit still open — [NAVIER_STOKES_HQIV_NARRATIVE.md](./NAVIER_STOKES_HQIV_NARRATIVE.md). |
| **F4.5 — First-principles bridge** | Package action/O-Maxwell stationarity, F2 chart data, F3 closure, and continuum balance into the HQIV DNS-shaped momentum equation. | **Done (reduced):** `HQIVFirstPrinciplesNSBridge.to_dns_momentum_component`, `HQIVFirstPrinciplesNSBridgeCanonical`, `HQIVFirstPrinciplesNSBridgePlasmaAmp`, and `hqivLapseModifiedDNSAxiom_of_firstPrinciples`; F2/F3/coherence bookkeeping is discharged for canonical choices. |
| **F5 — PDE analysis (optional, hard)** | Weak solutions, energy estimates, **blow-up** or **regularity** in the **modified** system—**separate** from Milestones F0–F4. | Only after F0–F4 have **precise** PDE targets; otherwise **out of scope** for this repo’s current Lean mission. |

---

## F2 — O-Maxwell / plasma ↔ fluid inputs (hypothesis map)

This table is **agent glue**: where to look in Lean/Python when wiring the **effective fluid** closure (`hqivFluidInertiaFactor`, `hqivVacuumMomentumSource3`, `hqivEddyViscosity`, `pyhqiv.fluid`) to **fields + plasma**. Every row is a **candidate attachment** unless the Status column says otherwise. **Nothing here is a proved theorem** identifying the continuum with the fluid unknowns.

| Fluid input | Role in closure | Lean anchors | Python (`pyhqiv`) | Status / gap |
|-------------|-----------------|--------------|-------------------|--------------|
| **γ** | Prefactor in **g_vac** and **ν_eddy** | `Hqiv.gamma_HQIV` (`HQVMetric`), `gamma_eq_2_5` | `gamma_hqiv()` in `metric` | **Matched:** same constant 2/5. |
| **φ** | `f(a,φ)`, and **g_vac** via `φ ∇δ̇θ′` | `phi_of_T`, `phi_of_shell` (`AuxiliaryField`); continuum scalar `φF` and `coordsGradientComponents` in `ContinuumOmaxwellClosure` (`emergentMaxwellInhomogeneous_O_coordsField`); the Maxwell correction now uses the algebra-first slot `alpha * algebraicMaxwellCouplingLog ν * …` in `ModifiedMaxwell`, with `phi_of_T` recovered only through `AlgebraicMaxwellProjectionHypothesis` when needed | `phi_of_shell`, `phi_of_real_shell` (`auxiliary_field`); chart gradients via downstream callers | **Typed at one chart point:** `OMaxwellFluidChartHypothesis.phi_pointwise` (`phiFluid = φF c`) in `HQIVFluidClosureScaffold`. Still not a **global** field identification. |
| **∇φ** (3-vector) | **g_vac** term `δ̇θ′ ∇φ` | Default `grad_φ` is **placeholder 0** in `ModifiedMaxwell`; real slot is `coordsGradientComponents φF c ν` / `contravariantGradientComponentsAt` in `ContinuumOmaxwellClosure` (ν : `Fin 4`; spatial ν = 1,2,3) | `grad_phi()` in `modified_maxwell` is **placeholder** | **Typed:** `chartSpatialPhiGradient` + `OMaxwellFluidChartHypothesis.grad_phi_spatial` (`HQIVFluidClosureScaffold`). |
| **δ̇θ′** (time rate) | **g_vac** and **ν_eddy** (`|δ̇θ′|`) | `OMaxwellAlgebraSeed.delta_theta_prime E′` is **phase tipping** from local electric energy `E′`, **not** a time derivative; naming is aligned with the paper’s δθ′ channel and now sits with the algebra-first Maxwell seed layer | `delta_theta_prime(e_prime)` in `modified_maxwell` | **Typed bridge:** `OMaxwellFluidChartHypothesis.dotTheta_bridge` (`dotTheta = delta_theta_prime Eprime`). ∂ₜ semantics still **extra** if desired. |
| **∇δ̇θ′** | **g_vac** term `φ ∇δ̇θ′` | No first-class `∇(δ̇θ′)` field in Lean yet | Not in `modified_maxwell` | **Typed:** `chartSpatialDotGradient dotF` + `OMaxwellFluidChartHypothesis.grad_dot_spatial` — user-chosen scalar `dotF` on the chart. |
| **Θ_local** | **ν_eddy** | Local horizon: `AuxiliaryField` ladder; combinatorial `x_over_theta_from_horizons` (`lightcone`); metric/time-angle in `HQVMetric` / `Now` | `x_over_theta_from_horizons`, `compton_horizon_bridge` patterns | **Closure choice:** pick which horizon proxy equals **Θ_local** in ν_eddy. |
| **ℓ_coh** | **ν_eddy** | `SchematicPlasmaCurrent.lambdaDebye`, `plasmaRadialProfile` (Debye-style scale); **not** wired to fluid | No default in `fluid` | **Hypothesis:** e.g. ℓ_coh ∝ λ_D or integral scale; **not** proved. |
| **Plasma current J** | Future stress / coupling to O-Maxwell | `J_src` in `emergentMaxwellInhomogeneous_O_general`; `J_O_plasma` / `schematicPlasmaScalar` (`SchematicPlasmaCurrent`); doc: `ModifiedMaxwell` plasma-facing note | `current_o` (placeholder) | **Gap:** no theorem **J → τ_mol** or **J → ν_eddy**; F3 only **scalar** ν split + HQIV ν_eddy **hypothesis**. |
| **Coherence C** | **ν_eddy** prefactor ∈ [0,1] | Not formalized in Lean | `coherence_factor` argument in `eddy_viscosity` | **Phenomenological** (high-coherence plasma vs turbulence). |

**Read order for implementers:** `OMaxwellAlgebraSeed.lean` (seed set, H-block, `delta_theta_prime`, algebraic coupling slot) → `ModifiedMaxwell.lean` (O-equation on that seed) → `ContinuumOmaxwellClosure.lean` (φ gradients on charts) → `SchematicPlasmaCurrent.lean` (Debye-scale plasma scalar) → `HQIVFluidClosureScaffold.lean` (fluid defs).

**Paper + Python alignment:** `paper/HQIV_OMaxwell_fluid_chart.tex` (MHD composition + F2 hypothesis narrative); `scripts/fluid_f2_chart_alignment.py` (numeric mirror of `hqivVacuumMomentumSource3` and spatial gradient slots; optional `OMaxwellFluidChartHypothesisData` checks). The archived SAT note `paper/archive/MHD/mhd.tex` (**Mega Huge Deconstruction**) is unrelated to magnetohydrodynamics.

---

## F3 — Plasma-as-fluid closure (scalar stress split)

**Goal:** record the **closure assumptions** used when collective plasma modes are modeled as a fluid with **molecular** plus **eddy** viscosity, where the eddy piece uses §0’s HQIV formula.

| Artifact | Role |
|----------|------|
| `PlasmaFluidClosureAssumptions` (Lean) | **Props:** `ν_total = ν_mol + ν_eddy`, `ν_eddy = hqivEddyViscosity …`, `0 ≤ C ≤ 1`. |
| `nuTotal_eq_nuMol_add_hqivEddy` | Bookkeeping: total shear scalar equals mol + HQIV eddy. |
| `PlasmaFluidClosureHypothesis` / `holds()` (Python) | Same checks for numeric use. |

**Not claimed:** derivation from Vlasov–Maxwell, Braginskii coefficients, or O-Maxwell alone.

---

## F4 — Coefficient-level limit toward classical NS

**Goal:** isolate **algebraic** conditions under which modified-fluid **coefficients** match the usual Navier–Stokes **form** (before any PDE analysis).

| Artifact | Role |
|----------|------|
| `CoefficientsTowardClassicalNS` | `hqivFluidInertiaFactor aLoc phi = 1` and `gVac = 0`. |
| `hqivVacuumMomentumSource3_toward_classical_of_grad_zero` | Example: vanishing gradients ⇒ vacuum source `0`; with `aLoc=1`, `phi=0` ⇒ `f=1`. |

**Not claimed:** global smooth solutions, weak solutions, or blow-up for classical or modified 3D NS — see [NAVIER_STOKES_HQIV_NARRATIVE.md](./NAVIER_STOKES_HQIV_NARRATIVE.md).

---

## Honesty table (agents)

| Question | Answer |
|----------|--------|
| Does HQIV “solve” classical 3D NS? | **No** — see [NAVIER_STOKES_HQIV_NARRATIVE.md](./NAVIER_STOKES_HQIV_NARRATIVE.md). |
| Did Lean derive an NS-shaped equation from HQIV action data? | **Conditionally, yes:** `HQIVFirstPrinciplesNSBridgeCanonical` / `HQIVFirstPrinciplesNSBridgePlasmaAmp` prove the HQIV DNS-shaped momentum component from O-Maxwell action stationarity plus canonical HQIV closure/coherence constructions and the remaining explicit continuum stress-balance hypothesis. |
| Is \(\nu_{\mathrm{eddy}}\) derived from O-Maxwell in Lean? | **Not as a theorem** — F3 **packages** the HQIV eddy formula as explicit hypotheses; O-Maxwell → \(\nu_{\mathrm{eddy}}\) is still not proved. |
| Is `fluid.py` authoritative? | **Yes:** `hqvmpy/src/pyhqiv/fluid.py` (package `pyhqiv`); `bak/` is legacy. |
| Same logical shape as RH ladder? | **Yes:** hypothesis bundles + small proved consequences **where** definitions exist; **no** conflation with classical Millennium statements. |

---

## Maintainer actions

When a milestone lands materially: update this §Status snapshot, add a line to [THEOREMS.md](./THEOREMS.md) for new **proved** defs/lemmas, and extend [ASSUMPTIONS.md](./ASSUMPTIONS.md) for new **explicit** fluid or plasma closure assumptions.
