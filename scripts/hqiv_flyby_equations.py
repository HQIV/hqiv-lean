"""
Locked equation sheet for HQIV orbital flyby calculator.

Single source for LaTeX / paper / `--equations` CLI.
Implementation: hqiv_orbital_flyby_omaxwell.py
Lean: Hqiv/Physics/OrbitalFlybyScaffold.lean, HQIVFluidClosureScaffold.lean
Paper: papers/hqiv_orbital_flyby_anomaly.tex
"""

from __future__ import annotations

# Paper table 1 nominal coupling (documented in hqiv_orbital_flyby_anomaly.tex §5)
PAPER_NOMINAL_COUPLING = {
    "vacuum_scale": 50.0,
    "metric_phi_scale": 5.0,
    "geff_on_newton": True,
    "geff_as_time_factor": True,
    "paper_inertia_screen": True,
    "modified_inertia_geodesic": True,
    "lapse_drag_phi": True,
    "horizon_repartition": True,
    "horizon_metric_channel": True,
    "suppress_vacuum_spin_coupling": True,
    "lapse_drag_colatitude": True,
    "lapse_drag_lense_thirring": True,
    "annual_lapse_phi": False,
    "galactic_disk_lapse_phi": True,
    "angular_momentum_screen": True,
    "orbital_angular_rindler": True,
    "velocity_screen": True,
}

EQUATION_SHEET_LATEX = r"""
\section*{Locked HQIV flyby equations (calculator v1)}

\subsection*{Classical baseline}
\begin{align}
  \mathbf{a}_{\rm N} &= -\frac{GM}{r^3}\mathbf{r}, \\
  \mathbf{a}_{J_2} &= -\frac{3}{2}\frac{J_2 GM R_{\oplus}^2}{r^5}
    \begin{pmatrix} x(5z^2/r^2-1) \\ y(5z^2/r^2-1) \\ z(5z^2/r^2-3) \end{pmatrix},\\
  \mathbf{a}_{3{\rm b}} &=
    \sum_{B\in\{\odot,\mathrm{Moon}\}} GM_B
    \left(\frac{\mathbf{R}_B-\mathbf{r}}{|\mathbf{R}_B-\mathbf{r}|^3}
    -\frac{\mathbf{R}_B}{|\mathbf{R}_B|^3}\right).
\end{align}
The Sun/Moon term is a classical differential tide in Earth-centred runs; it is not an HQIV
coupling. Hyperbolic seed: $|\mathbf{h}|=b v_\infty$, $v^2/2 - GM/r = v_\infty^2/2$.
Asymptotic readout: $v_{\infty,{\rm shell}} = \sqrt{v^2 - 2GM/r}$; $\Delta v = v_{\infty,{\rm out}}-v_{\infty,{\rm in}}$.

\subsection*{HQIV constants (Lean)}
\begin{align}
  \alpha &= 3/5, \quad \gamma = 2/5, \quad \varphi(m)=2(m+1), \quad m_\oplus=4, \\
  \varphi_{\rm hom} &\approx 2cH_0 \quad \text{(SI acceleration scale)}, \\
  \varphi_{\rm loc}(\mathbf{r}) &= \varphi_{\rm hom}\,\frac{\varphi(m_\oplus)/(1+|r|/R_\oplus)}{\varphi(m_\oplus)},\\
  \epsilon_{\rm spin}(\mathbf r,\mathbf v) &= \frac{2\Omega R_\oplus}{c}
    \left(\frac{R_\oplus}{r}\right)^2\sin^2\theta\,
    |\hat{\mathbf v}\cdot\hat{\boldsymbol\phi}|,\qquad
  \epsilon_{\rm yr} &= \frac{v_\oplus}{c}\,\hat{\mathbf v}\cdot\hat{\mathbf v}_{\oplus}(t_{\rm flyby}),\\
  f_{\rm disk} &= \frac{M_{\rm disk}(<R_0)}{v_c^2 R_0/G},\qquad
  D_R = 1+\frac{\gamma}{2}\left(\frac{c}{v_c}\right)^2,\\
  \epsilon_{\rm gal}(t) &= \frac{2(v_c/c) f_{\rm disk}}{D_R}
    \frac{v_\oplus}{v_c}\,\hat{\mathbf v}_{\oplus}(t)\cdot\hat{\mathbf v}_{\rm gal},\\
  \varphi_{\rm eff,full} &= \varphi_{\rm loc} + 6a_{\rm loc}\max(0,\epsilon_{\rm spin}
    + \epsilon_{\rm gal} + \lambda_{\rm yr}\epsilon_{\rm yr}),\\
  \varphi_{\rm eff,part} &= \varphi_{\rm loc}\quad\text{(particle geodesic / metric split)}.
\end{align}
Repartitioned runs: $f_{\rm part}=f(a,\varphi_{\rm eff,part})$, metric slot
$\mathbf{a}_{\rm hor}=\mathbf{a}_{\rm GR}/f_{\rm part}\,(f_{\rm part}/f_{\rm full}-1)$ split into
isotropic $(1-\lambda)$ and L-T $\lambda$ along $\hat{\boldsymbol\omega}\times\hat{\mathbf r}$, with
$\lambda=\gamma\sin^2\theta\,\rho_{\rm pol}$ derived ($\gamma=2/5$, $\rho_{\rm pol}=1-(h_z/h_{\rm ref})^2$).
$G_{\rm eff}$ and O-Maxwell use $(1-f_{\rm full})$; total $\mathbf a$ scaled by $G_{\rm eff}$ last.

\subsection*{Modified inertia (Brodie / main.tex geodesic)}
\begin{align}
  f(a,\varphi) &= \frac{a}{a+\varphi/6}, \qquad
  m_i = m_g f,\qquad \mathbf{a} = \frac{\mathbf{a}_{\rm GR}}{f_{\rm blend}}
  \quad\text{(particle action } S=-m_g\int f\,ds\text{)}.
\end{align}
Chart slots (O-Maxwell) additionally $\propto (1-f)$ and $(1-\beta^2)$.
Direction-dependent $f_{\rm blend}$ (angular momentum + oblate latitude):
\begin{align}
  \boldsymbol\omega_{\rm orb} &= \frac{\mathbf r\times\mathbf v}{r^2},\qquad
  \boldsymbol\alpha_{\rm orb}
    = \frac{\mathbf r\times\mathbf a_{\rm GR}}{r^2}
      -2\frac{\mathbf r\cdot\mathbf v}{r^2}\boldsymbol\omega_{\rm orb},\\
  a_{\rm ang} &= r\,|\boldsymbol\alpha_{\rm orb}|,\\
  a_{\rm eq} &= |g| + \left(\frac{h^2}{r^3}+a_{\rm ang}\right)
    \left(\frac{h_z}{h}\right)^2, \quad
  h_z = |(\mathbf{r}\times\mathbf{v})_z|, \\
  \rho_{\rm pol} &= 1-(h_z/h_{\rm ref})^2, \quad h_{\rm ref}=bv_\infty, \\
  h_{z,{\rm eff,asym}}^2 &= h_z^2+\frac{h_{\rm ref}^2}{(m+1)^2},\quad
  h_{z,{\rm eff,loc}}^2 = h_z^2+\frac{h^2}{(m+1)^2}, \\
  \varphi_{\rm pol} &= \varphi_{\rm eff}\Bigl(1+\rho_{\rm pol}\,
    \max\bigl(\bigl[\tfrac{h_{\rm ref}^2}{h_{z,{\rm eff,asym}}^2}-1\bigr]_+,
    \bigl[\tfrac{h^2}{h_{z,{\rm eff,loc}}^2}-1\bigr]_+\bigr)\Bigr), \\
  f_{\rm blend} &= \sin^2\theta\, f(a_{\rm eq},\varphi_{\rm eff})
    + \cos^2\theta\, f(|g|,\varphi_{\rm pol}), \\
  w_{\rm L} &= 1-f_{\rm blend}, \quad \sin^2\theta = 1-(z/r)^2.
\end{align}
Screened coupling: $G_{\rm eff}/G_0 = 1 + \bigl((\varphi/\varphi_{\rm ref})^\alpha-1\bigr)\,w$.

\subsection*{O-Maxwell perturbation (chart)}
\begin{align}
  \mathbf{g}_{\rm vac} &= -\frac{\gamma}{6}\bigl(\varphi\,\nabla\dot\theta' + \dot\theta'\,\nabla\varphi\bigr), \\
  \mathbf{a}_\varphi &= \frac{\alpha}{4\pi}\ln(\varphi+1)\,\nabla\varphi, \\
  \mathbf{a}_{\rm HQIV} &= w_{\rm L}(1-\beta^2)\bigl(\kappa_{\rm vac}\mathbf{g}_{\rm vac}
    + \kappa_\varphi\mathbf{a}_\varphi\bigr), \quad \beta=|\mathbf{v}|/c.
\end{align}
"""

EQUATION_SHEET_MARKDOWN = """
# HQIV orbital flyby — locked equations (v1)

**Code:** `scripts/hqiv_orbital_flyby_omaxwell.py`  
**Lean:** `Hqiv/Physics/OrbitalFlybyScaffold.lean`  
**Paper:** `papers/hqiv_orbital_flyby_anomaly.tex`

## Classical
- Newton + J₂ (spin-aligned z)
- Earth runs include Sun/Moon third-body differential tides by default
- Δv from vis-viva asymptotic speeds at r > 40 R⊕

## HQIV screen
- f(a,φ) = a/(a+φ/6), w = 1−f
- L-dependent blend (h_z, colatitude θ)
- co-spinning mass-horizon Doppler shift ε_spin ∝ (2ΩR/c) sin²θ |v̂·φ̂|
- orbital angular Rindler scale a_ang = r|dω_orb/dt| in the local inertia scale
- G_eff screened by w; O-Maxwell slots scaled by w(1−β²)

## Nominal paper coupling
- vacuum_scale=50, metric_phi_scale=5 (SI bridge; not fitted to PDG)
"""


def print_equations(fmt: str = "latex") -> None:
    if fmt == "latex":
        print(EQUATION_SHEET_LATEX)
    elif fmt == "md":
        print(EQUATION_SHEET_MARKDOWN)
    else:
        raise ValueError(f"unknown format {fmt!r}")


def paper_coupling_from_dict() -> object:
    """Build `HQIVOrbitCoupling` for the paper's nominal row (import deferred)."""
    import hqiv_orbital_flyby_omaxwell as orb

    c = PAPER_NOMINAL_COUPLING
    return orb.HQIVOrbitCoupling(
        vacuum_scale=float(c["vacuum_scale"]),
        metric_phi_scale=float(c["metric_phi_scale"]),
        geff_on_newton=bool(c["geff_on_newton"]),
        geff_as_time_factor=bool(c.get("geff_as_time_factor", True)),
        paper_inertia_screen=bool(c["paper_inertia_screen"]),
        modified_inertia_geodesic=bool(c.get("modified_inertia_geodesic", True)),
        lapse_drag_phi=bool(c.get("lapse_drag_phi", True)),
        horizon_repartition=bool(c.get("horizon_repartition", True)),
        horizon_metric_channel=bool(c.get("horizon_metric_channel", True)),
        suppress_vacuum_spin_coupling=bool(c.get("suppress_vacuum_spin_coupling", True)),
        annual_lapse_phi=bool(c.get("annual_lapse_phi", False)),
        galactic_disk_lapse_phi=bool(c.get("galactic_disk_lapse_phi", True)),
        angular_momentum_screen=bool(c["angular_momentum_screen"]),
        orbital_angular_rindler=bool(c.get("orbital_angular_rindler", True)),
        velocity_screen=bool(c["velocity_screen"]),
    )


def format_paper_table_latex(rows: list[dict[str, object]]) -> str:
    """LaTeX `tabular` rows for \\input in hqiv_orbital_flyby_anomaly.tex."""
    lines = [
        r"\begin{tabular}{@{}lrrrrr@{}}",
        r"\toprule",
        r"Case & Lit.\ [mm/s] & $r_{\rm CA}$ [km] & $\langle 1{-}f\rangle_{\rm out}$ & "
        r"$\Delta v_{\rm cls}$ & HQIV$-$cls \\",
        r"\midrule",
    ]
    for row in rows:
        lit = row.get("reported_anomaly_mm_s")
        lit_s = f"{float(lit):.2f}" if lit is not None else "---"
        sw = row.get("mean_one_minus_f_out", float("nan"))
        sw_s = f"{sw:.2e}" if sw == sw else "---"
        lines.append(
            f"{row['case_id'].replace('_', r'\_')} & {lit_s} & "
            f"{float(row['r_ca_km']):.0f} & {sw_s} & "
            f"{float(row['classical_delta_v_mm_s']):.2f} & "
            f"{float(row['hqiv_minus_classical_mm_s']):.2f} \\\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabular}"])
    return "\n".join(lines)
