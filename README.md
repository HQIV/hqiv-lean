# HQIV_LEAN

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18899939.svg)](https://doi.org/10.5281/zenodo.18899939)

Formalisation of the HQIV (Horizon-Quantized Informational Vacuum) framework in Lean 4. The accompanying preprint is archived on Zenodo:

- **Preprint (Zenodo):** [zenodo.org/records/18899939](https://zenodo.org/records/18899939)
- **DOI:** [10.5281/zenodo.18899939](https://doi.org/10.5281/zenodo.18899939)
- **API documentation (GitHub Pages):** The [Lean docgen workflow](.github/workflows/lean_action_ci.yml) builds and deploys the API docs on each push to the default branch. Once enabled, they are published at [**disregardfiat.github.io/hqiv-lean/docs**](https://disregardfiat.github.io/hqiv-lean/docs), look for the hqiv section on the side.

**Agent / contributor docs (versioned):** curated theorem index ([`AGENTS/THEOREMS.md`](AGENTS/THEOREMS.md)) and assumptions / trust boundary ([`AGENTS/ASSUMPTIONS.md`](AGENTS/ASSUMPTIONS.md)). Other notes under `AGENTS/` may exist locally but are not tracked.

## CLASS numerical fork (Lean alignment)

The modified **CLASS** tree lives in the separate **`HQIV/class_hqiv`** checkout (not inside this Lean package). After edits there, `make` from `class_hqiv/`. See **`HQIV/class_hqiv/LEAN_ALIGNMENT.md`** for which C equations match `HQVMetric.lean` / `HQVMCLASSBridge.lean` / `HQVMDiscretePoisson.lean` / `HQVMConsistency.lean` and what is still missing (e.g. exact `ρ_crit′` for `H′`, lapse `HQVM_lapse`, discrete lattice).

## Building

**Default (CI and daily use):** builds **HQIVPhysics** (geometry + physics, no generator stack). Finishes in reasonable time.

```bash
lake build
```

- **Full build (with SO(8) closure):** for HQIVLEAN you must raise the stack limit, then:
  ```bash
  ulimit -s 65536
  lake build HQIVLEAN
  ```
  Or run `./scripts/build.sh HQIVLEAN`. The full build can take hours; CI uses the default (HQIVPhysics) only.

**Default build (HQIVPhysics)** includes geometry (`OctonionicLightCone`, `AuxiliaryField`, `HQVMetric`, `Now`, `UniverseAge`), `Conservations`, and physics (`Baryogenesis`, `ModifiedMaxwell`, `GRFromMaxwell`, `Forces`, `Action`, `CovariantSolution`, `SM_GR_Unification`). No generator stack. First run will build mathlib and can take 30–60+ minutes.

**ProofWidgets:** If the build fails with `ProofWidgets not up-to-date. Please run lake exe cache get`, the widget cache may be unavailable. A workaround is to comment out the `errorOnBuild` check in `.lake/packages/proofwidgets/lakefile.lean` (the block `if let some msg := get_config? errorOnBuild then error msg`) so the widget is built from source. Re-apply this change after `lake update` if the package is reset.
If you see errors like `failed to load header from ... setup.json: unexpected end of input`, the mathlib build cache may be corrupted; then run:

```bash
cd .lake/packages/mathlib && lake clean && cd ../../..
lake build
```  
**HQIVLEAN** (full build) adds the generator stack: `Generators`, `OctonionLeftMultiplication`, `GeneratorsFromAxioms`, `GeneratorsLieClosureData*`, `So8CoordMatrix`, `GeneratorsLieClosure`, `SO8Closure`. Scripts: `scripts/print_lie_bracket_closure.py --write`, `scripts/print_linear_independence.py [--write]`.

**100 % PROVED** (zero sorrys, zero extra axioms, zero matrix edits). Full Spin(8) closure + proton-to-Higgs prediction derived purely from the two HQIV axioms + concrete octonion tables.

**What traces to the light cone (single axiom, no arbitrary defs)**  
- **Single axiom:** New modes at shell m = 8 × stars-and-bars(m) = 4·(m+2)(m+1).  
- From that: `latticeSimplexCount`, `cumLatticeSimplexCount` (and closed form), `available_modes`, `new_modes`.  
- Temperature ladder T(m) = T_Pl/(m+1) (with T_Pl = 1 in natural units) and φ(m) = 2/T(m) are the lattice division rule and the paper’s φ = 2/Θ.  
- `shell_shape` is **proved** equal to (1/(m+1))(1 + α log(T_Pl/T(m))) so the curvature shape is derived from the temperature ladder, not an independent def.  
- Curvature integral, its divergence, divisibility (3∣…, 2∣…), and **α = 3/5 as a lattice ratio valid for every n and as the limit** of the discrete ratio (n+1)(n+2)(n+3)/(5·cum n). **Ω_k is dynamic and horizon-dependent:** `omega_k_at_horizon n N` is the curvature ratio at horizon N; spatial curvature between different horizons (e.g. quarks vs CMB LSS) is different even at time "now" — no single Ω_k without specifying the horizon.  
- **Analytic curvature:** The discrete curvature integral is proved to be sandwiched between the harmonic sum and (1+α log(n+1)) times the harmonic sum (`curvature_integral_ge_harmonic`, `curvature_integral_le_harmonic_mul_log`), so it grows like Θ(log n); no continuous integral axiom.  
- **S² / spherical harmonics bridge:** `SphericalHarmonicsBridge` proves the cumulative Laplace–Beltrami degeneracy `∑_{ℓ≤L}(2ℓ+1) = (L+1)²`, the telescoping identity `∑_{i≤M} new_modes i = available_modes M`, and the minimal shell with `available_modes m ≥ 64` (`m = 3`, value `80`). Module doc relates the octonion factor `4·(m+2)(m+1)` to continuum `S²` mode growth and distinguishes this combinatorial threshold from the archived Planck-volume τ-shell index (`archive/abandoned/GenerationResonanceTauHighestShell.lean`).  
- **Full SM symmetry and conservations from the same two axioms:** the octonionic generators close to Spin(8)/SO(8) and give the full Standard Model gauge structure; the HQVM metric + O-Maxwell action yield GR-from-Maxwell, varying G, and the SM couplings at "now" (α_EM, sin²θ_W, α_s, m_H, M_Z, M_GUT) **all as outputs** of the light-cone axiom plus the informational-energy/monogamy axiom (see `SM_GR_Unification`, `GRFromMaxwell`, `Conservations`, `Forces`). No extra field-theory parameters are assumed in Lean.
- **Universe age from the ADM lapse:** Proper time (wall-clock) and coordinate time (apparent age) are related by dτ = N dt with N = 1 + Φ + φ t (`UniverseAge`). A **local scale witness** (e.g. proton mass) fixes the current scale and thus the geometry, yielding exact wall-clock and apparent age; the witness is **free from CMB phase** (no birefringence from propagated photons) and **free from accelerated motion** (Sun, galaxy), since ages are defined in the fundamental observer's rest frame. T_CMB’s phase component is quantified in Lean; paper witnesses: wall-clock ≈ 51.2 Gyr, apparent ≈ 13.8 Gyr.

**Canonical HQIV constants (single α, single γ):** In the companion HQIV theory, **the** curvature-imprint exponent is **α = 3/5** and **the** monogamy split is **γ = 2/5** (with α + γ = 1 on the unit horizon split). Those are **not** a tunable pair of knobs in the formalism; their physical derivation is given in the companion HQIV manuscript and Brodie (2026), which this repo cites from the paper bibliography—not re-proved in Lean.

**What is *not* “external” in Lean:** The numeric identities are **proved**, not postulated without proof: the lattice ratio `(n+1)(n+2)(n+3)/(5·cum n)` equals **α for every** `n` (hockey-stick; `OctonionicLightCone.latticeAlphaRatio_eq_alpha`). The metric sector sets **γ := 1 − α** (`HQVMetric.gamma_HQIV`); **γ = 2/5** is `gamma_eq_2_5`. So the **only** `alpha` and `gamma_HQIV` in the codebase are these canonical values, wired to the same ladder as curvature / `G_eff`.

**Second HQIV axiom (metric; not stars-and-bars arithmetic):** The ADM lapse **N = 1 + Φ + φ t** and the HQVM line element are the **informational-energy / horizon-monogamy** specification in synchronous-comoving gauge (`HQVMetric.HQVM_lapse` and module doc). Lean **defines** N by that formula (the axiom’s ADM form) and proves consequences (Friedmann piece, spatial coefficients, perturbation calculus in `HQVMPerturbations`). **φ** is not a free knob: it is the lattice auxiliary field (e.g. φ(m) = 2/T(m) in `AuxiliaryField`). So the lapse is the second axiom made explicit in the metric — aligned with the paper — rather than an extra parameter beyond the two-axiom story.

**Conventions and pipeline splits**  
- **referenceM** = lockin = qcdShell + stepsFromQCDToLockin; discrete steps through baryogenesis (a few steps after T_lockin). Implemented combinatorially in `OctonionicLightCone` and used in `Baryogenesis`; detailed QCD overlap integrals remain in the Python/paper pipeline.  
- **Natural units:** T_Pl = 1, G₀ = H₀ = 1 (reference scale for dimensionless statements in Lean and CLASS alignment).

So: the **combinatorics, T-ladder, φ on shells, curvature shape, α from the lattice, horizon-dependent Ω_k (curvature ratio from shell integral), full Spin(8)/SM gauge structure, conserved currents, the curvature norm \(6^7\sqrt{3}\), and the SM + GR field equations and couplings at "now"** are all derived inside Lean from the same two HQIV axioms (discrete light cone + informational-energy/monogamy), with no extra dynamical parameters. Spatial curvature is different between any two horizons (e.g. QCD vs CMB LSS) even at time "now". Matter fraction and η are downstream of the SM embedding to SO(8).

### Roadmap: plasmas, modified inertia, and fermion ladders (observer-centric)

Physical regimes dominated by **plasmas** and by **modified inertia** are expected to matter a lot in HQIV; the formal stack is not trying to replay global GR perturbation theory, but it *is* set up so those effects route through the same horizon–octonion–φ machinery as fermion masses.

- **Plasmas** stress the collective **EM / O-Maxwell** layer: `ModifiedMaxwell` (emergent equation in **O**, reduction to H, 3D API; `emergentMaxwellInhomogeneous_O_general` for arbitrary `J_src`), `SchematicPlasmaCurrent` (Debye-style radial profile, `J_O_plasma`, `linearisedScalarPerturbation` = lapse × plasma with `phi_of_T Θ`, and `emergentMaxwell_plasma_uniform_t_flat_phi` linking the flat-φ skeleton to `-4π J`), `Action` (variational spine), and `Forces` (which octonion components become which sectors). Macroscopic **currents** are the natural place to replace placeholders such as `J_O` and to tie **horizon-dependent** curvature (`omega_k_at_horizon`, quark vs CMB horizons) to observable plasma environments without assuming a single global Ω_k.
- **Modified inertia** already appears in two Lean hooks: (1) **φ-aware corrections** in the emergent Maxwell skeleton (`phi_of_T`, `grad_φ` API in `ModifiedMaxwell`); (2) **lapse-rescaled quantum mechanics** via `HQVM_lapse` as `lapseFactor` / `lapseCorrectedHamiltonian` in `Schrodinger`. Tightening those links is how “inertia” changes propagate from the metric–informational sector into **mass scales**.
- **Priorities for closing the loop to matter:** the **charged-lepton** ladder (`ChargedLeptonResonance`, `LeptonGenerationLockin`, `DerivedGaugeAndLeptonSector`, anchors inside `SM_GR_Unification`) and the **quark** internal-harmonic ladder (`QuarkMetaResonance`, lock-in / top shell alignment in `SM_GR_Unification`) are the main formal targets: same φ and shell structure as the vacuum sector, but with explicit mass witnesses. Observer-centric linear response of the lapse (and `phi_of_T` increments) lives in `HQVMPerturbations` / `HQVMetricAnalytic` and is meant to complement—not replace—that fermion-focused work.

**What a conventional physicist would recognize as outputs of the single axiom**  
- **Spin(8)/Standard Model gauge sector**: full so(8) closure, G₂ ⊃ SU(3)\_c × SU(2)\_L × U(1)\_Y, three generations from triality, explicit SU(2)\_L and hypercharge generators, and SM branching rules, all traced back to counting over the octonionic light cone.  
- **Running couplings without SM β-functions**: the **canonical** HQIV α = 3/5 (see above) and α\_GUT = 1/42 from the lattice; the modified O-Maxwell equation and φ(m) ladder yield 1/α\_EM(M\_Z) ≈ 127.9, sin²θ\_W(M\_Z), α\_s(M\_Z), and the Higgs mass scale from the same curvature/φ machinery (`SM_GR_Unification`). **Same result as textbook 1-loop RG:** in `SM_GR_Unification` (Part A — *Traditional QFT as limits and matching*) the effective inverse coupling is proved to be bare `1/α_GUT` plus an explicit `ln(φ+1)` correction; integrated one-loop SM running is the same **affine** function of `ln μ`, and a linear change of log-coordinate plus one equivalent `b` reproduces identical increments `Δ(1/α)`. The continuum prototype `(f(x+ε)-f(x))/ε → f'(x)` is the analytic limit underlying the lattice variational derivative in `Action.lean`. Loops are not assumed; they are **matched** as bookkeeping when desired.  
- **GR from the same horizon structure**: the HQVM lapse N = 1 + Φ + φ t and O-Maxwell action give Friedmann + varying G\_eff(φ) and a horizon-dependent spatial curvature Ω\_k(n; N) computed from the discrete curvature integral (`GRFromMaxwell`, `UniverseAge`).  
- **Matter content and nucleon scales**: baryogenesis and η, the QCD transition shell, and proton/neutron masses (with error bars from T\_CMB and birefringence) are derived via the same shell/φ ladder and curvature norm (`Baryogenesis`, `SM_GR_Unification`).  
- **Spin–statistics link (abstract layer)**: a spin–statistics statement is formulated and satisfied in Lean (`SpinStatistics`), expressing that half-integer–spin modes (octonion 8s sector) anticommute while integer–spin modes commute, driven by Spin(8) triality plus null-lattice causality/monogamy.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.

**License note (March 2026)**  
This project is released under the MIT License **with an explicit Government Use Restriction**.  
Governments worldwide may **not** use, fork, or run this software without first purchasing a paid seat from me Steven Ettinger Jr. Seat availability and pricing are at my sole discretion.  
Individuals, companies, universities, and non-profits continue to enjoy full MIT rights.

