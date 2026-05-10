# Main paper ↔ Lean rigor (FLRW / HQVM node)

This note is for **authors and reviewers**: it ties FLRW-minded claims in the HQIV **main manuscript** (`paper/main.tex` in the HQIV paper repo—**that file is not tracked in HQIV_LEAN**) to **proved** Lean equivalences in this repository, and lists **paper-side** wording edits that would increase academic defensibility.

**Lean-only changes** for this pass live in `Hqiv/Geometry/HQVM_FLRW_PaperAlignment.lean` (imported from `HQIVLEAN.lean`). No edits were made to any `.tex` file here.

---

## 1. Repository sync

| Artifact | Location |
|----------|----------|
| Main paper | Intended: `paper/main.tex` (HQIV paper repository). **Not present** under `HQIV_LEAN/paper/` (this clone only has `octonion_lightcone_to_oshoracle.tex`, `HQIV_OMaxwell_fluid_chart.tex`). |
| Lean entry (new) | `Hqiv/Geometry/HQVM_FLRW_PaperAlignment.lean` |
| Lean depth (existing) | `Hqiv/Geometry/HQVMetric.lean` (`HQVM_Friedmann_eq`, `G_eff`, vacuum iff), `Hqiv/Physics/Action.lean` (`S_HQVM_grav`, `S_HQVM_grav_zero_iff_Friedmann`, `equations_from_action`), `Hqiv/Geometry/HQVMCLASSBridge.lean` (CLASS rescaling, Picard map, conformal \(H'\), perturbative lapse/spatial coefficients). |

When `main.tex` is available in a workspace, add a short `\paragraph{Lean anchors}` that cites the theorem names below (copy from `THEOREMS.md` after the next refresh).

---

## 2. What Lean actually proves (vs “full FLRW”)

| Paper-style statement | Lean anchor | Honest scope |
|----------------------|-------------|--------------|
| Gravitational stationarity \(S_{\mathrm{grav}}=0\) ⇔ HQVM Friedmann constraint | `Hqiv.S_HQVM_grav_zero_iff_Friedmann` / `Hqiv.paper_FLRW_node_Sgrav_iff_Friedmann` | Single **homogeneous** \(\phi\) channel matching `S_HQVM_grav` definition; not a 3+1 Einstein initial-value proof. |
| HQVM Friedmann ⇔ CLASS-style \(H^2\) rescaling with \(\rho_{\mathrm{crit}}=8\pi\rho_{\mathrm{tot}}/3\) | `Hqiv.HQVM_Friedmann_eq_iff_CLASS_H_squared` / `_rational` | **Algebraic** equivalence at fixed \(\gamma=2/5\); not CLASS file I/O. |
| One-line “main paper” chain \(S_{\mathrm{grav}}=0 \Leftrightarrow \phi^2 = \frac{15}{13} G_{\mathrm{eff}}(\phi)\,\rho_{\mathrm{crit}}\) | `Hqiv.paper_FLRW_node_Sgrav_iff_CLASS_H2_rational` | Packages the two iff steps. |
| With \(\phi\ge0\), \(G_{\mathrm{eff}}(\phi)=\phi^\alpha\) | `Hqiv.paper_FLRW_node_Sgrav_iff_CLASS_H2_rational_Geff_power` | Uses `G_eff_eq`; \(\alpha=3/5\) is `Hqiv.alpha`. |
| Textbook flat \(3H^2=8\pi\rho\) ⇔ \(H^2=\rho_{\mathrm{crit}}\) at \(G=1\) | `Hqiv.paper_standard_flat_GR_H2_iff_CLASS_rhoCrit` (= `HQVM_CLASS_GR_flat_H_sq_iff`) | **Classical normalization** bridge; not “HQVM replaces ΛCDM”. |
| Vacuum: \(\rho_m=\rho_r=0 \Rightarrow S_{\mathrm{grav}}=0 \Leftrightarrow \phi=0\) | `Hqiv.paper_FLRW_node_Sgrav_vacuum_iff_phi_zero` | Matches `HQVM_Friedmann_eq_vacuum_iff`. |
| O-Maxwell + Friedmann in one `equations_from_action` bundle | `Hqiv.equations_from_action` | Second conjunct is **default** `J_O` / placeholder `A_O` bookkeeping—not observational CMB physics. |

**Not in scope without new axioms:** gauge-invariant growth equations, tight FLRW + perturbation **uniqueness**, photon polarization, baryon/CDM fluid **coupled** Boltzmann, MCMC “attack” on Planck chains inside Lean.

---

## 3. Suggested **paper** edits (apply in `main.tex` when editing there)

These are **authoring** recommendations only (not applied in this repo).

1. **Lead every FLRW comparison with “homogeneous \(\phi\) channel / single-node constraint.”** Avoid phrasing that sounds like a full competing numerical cosmology unless you also cite external CLASS/CAMB runs and likelihoods.

2. **Separate three layers** in notation: (i) **standard** flat \(3H^2=8\pi\rho\); (ii) **HQVM** \((3-\gamma)\phi^2 = 8\pi G_{\mathrm{eff}}(\phi)(\rho_m+\rho_r)\); (iii) **CLASS code normalization** \(H^2=(3/(3-\gamma))G_{\mathrm{eff}}\rho_{\mathrm{crit}}\). Point to Lean `HQVM_Friedmann_eq_iff_CLASS_H_squared` for (ii)↔(iii).

3. **Where the paper “attacks” FLRW**, prefer **“same normalization / rescaling / limit”** over **“disproves”**: reviewers read “attack” as **data + likelihood** unless you show explicit tension metrics.

4. **CMB / \(\beta\) / birefringence hooks:** keep the existing honesty clause (central values vs full hierarchical posterior); Lean has bookkeeping hooks elsewhere—cite them as **falsifiable identities**, not as posterior replacements.

5. **Add a boxed “Lean citation” paragraph** listing: `paper_FLRW_node_Sgrav_iff_CLASS_H2_rational`, `HQVM_Friedmann_eq_difference_phi_plus` (finite \(\delta\phi\) at fixed \(\rho\)), and `HQVM_CLASS_GR_flat_H_sq_iff` for the GR limit table.

6. **NS / fluid cross-refs:** if `main.tex` mentions Navier–Stokes, add a sentence that **Millennium NS** (3D incompressible \(\mathbb{R}^3\)) is **not** what `HQIVFluidClosureScaffold` proves; link to `AGENTS/FLUID_OMAXWELL_ROADMAP.md` F4/F5 scope.

---

## 4. `THEOREMS.md` maintenance

Add (or merge) a row under the metric/cosmology heading for:

`Hqiv.paper_FLRW_node_Sgrav_iff_Friedmann` / `paper_FLRW_node_Sgrav_iff_CLASS_H2_rational` / `paper_FLRW_node_Sgrav_iff_CLASS_H2_rational_Geff_power` / `paper_standard_flat_GR_H2_iff_CLASS_rhoCrit` / `paper_FLRW_node_Sgrav_vacuum_iff_phi_zero`

with one-line scope: **single-node HQVM gravitational action stationarity ↔ Friedmann ↔ CLASS-style \(H^2\); standard flat GR normalization bridge; vacuum.**

---

## 5. Build

`HQIVLEAN` uses an explicit `globs` list in `lakefile.toml`. New modules imported from `HQIVLEAN.lean` must be added there (e.g. `Hqiv.Geometry.HQVM_FLRW_PaperAlignment`); then `lake build HQIVLEAN` succeeds.
