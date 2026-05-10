"""Run O-Maxwell torus ODE benchmark on the 5-molecule suite."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from omaxwell_torus_ode import (
    BondGeometry,
    FragmentConfig,
    MoleculeConfig,
    ODESettings,
    integrate_molecule,
    molecule_bond_surplus_ev,
    solve_equilibrium_radius,
)


@dataclass(frozen=True)
class Case:
    name: str
    molecule: MoleculeConfig
    reference_ev: float


CASES: tuple[Case, ...] = (
    Case(
        "H2 dissociation",
        MoleculeConfig(
            "H2",
            (FragmentConfig("H", 1, 1), FragmentConfig("H", 1, 1)),
            (BondGeometry(0, 1, 0.7414),),
            4.478,
            "NIST / W4-17",
        ),
        4.478,
    ),
    Case(
        "LiH dissociation",
        MoleculeConfig(
            "LiH",
            (FragmentConfig("Li", 3, 3), FragmentConfig("H", 1, 1)),
            (BondGeometry(0, 1, 1.5956),),
            2.515,
            "W4-17/GMTKN55",
        ),
        2.515,
    ),
    Case(
        "HF dissociation",
        MoleculeConfig(
            "HF",
            (FragmentConfig("F", 9, 9), FragmentConfig("H", 1, 1)),
            (BondGeometry(0, 1, 0.9168),),
            5.87,
            "W4-17/GMTKN55",
        ),
        5.87,
    ),
    Case(
        "H2O atomization",
        MoleculeConfig(
            "H2O",
            (
                FragmentConfig("O", 8, 8),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
            ),
            (BondGeometry(0, 1, 0.9572), BondGeometry(0, 2, 0.9572)),
            9.51,
            "W4-17/GMTKN55",
        ),
        9.51,
    ),
    Case(
        "CH4 atomization",
        MoleculeConfig(
            "CH4",
            (
                FragmentConfig("C", 6, 6),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
            ),
            (
                BondGeometry(0, 1, 1.09),
                BondGeometry(0, 2, 1.09),
                BondGeometry(0, 3, 1.09),
                BondGeometry(0, 4, 1.09),
            ),
            17.0,
            "W4-17/GMTKN55",
        ),
        17.0,
    ),
)


def run_cases(cases: Iterable[Case]) -> list[dict[str, float | str]]:
    rows = []
    settings_nuclear = ODESettings(
        dt=0.02, steps=35, eps=3e-4, damping=0.05, m_shell=4, s7_penalty=1.0, potential_mode="nuclear_only"
    )
    settings_joint = ODESettings(
        dt=0.02, steps=35, eps=3e-4, damping=0.05, m_shell=4, s7_penalty=1.0, potential_mode="joint_horizon"
    )
    settings_eq = ODESettings(
        dt=0.01,
        steps=35,
        eps=3e-4,
        damping=0.20,
        m_shell=4,
        s7_penalty=1.0,
        potential_mode="joint_horizon",
        equilibrium_tol=1e-4,
        force_tol=0.10,
        force_tol_practical=8.5,
        equilibrium_eps=2e-5,
        armijo_c=1e-4,
        armijo_rho=0.5,
        line_search_max_iter=40,
        line_search_alpha0=0.35,
    )
    h2_static = molecule_bond_surplus_ev(CASES[0].molecule)
    h2_nuclear = integrate_molecule(CASES[0].molecule, settings_nuclear)["final_energy_ev"]
    h2_joint = integrate_molecule(CASES[0].molecule, settings_joint)["final_energy_ev"]
    scale_static = CASES[0].reference_ev / h2_static
    scale_nuclear = CASES[0].reference_ev / h2_nuclear
    scale_joint = CASES[0].reference_ev / h2_joint
    for c in cases:
        e_static = molecule_bond_surplus_ev(c.molecule) * scale_static
        e_nuclear = integrate_molecule(c.molecule, settings_nuclear)["final_energy_ev"] * scale_nuclear
        e_joint = integrate_molecule(c.molecule, settings_joint)["final_energy_ev"] * scale_joint
        eq = solve_equilibrium_radius(c.molecule, settings_eq, max_steps=600)
        rows.append(
            {
                "name": c.name,
                "static_scaled_ev": e_static,
                "nuclear_scaled_ev": e_nuclear,
                "joint_scaled_ev": e_joint,
                "reference_ev": c.reference_ev,
                "static_error_pct": 100.0 * (e_static - c.reference_ev) / c.reference_ev,
                "nuclear_error_pct": 100.0 * (e_nuclear - c.reference_ev) / c.reference_ev,
                "joint_error_pct": 100.0 * (e_joint - c.reference_ev) / c.reference_ev,
                "x_eq_lattice": eq["x_eq_lattice"],
                "eq_speed": eq["speed"],
                "eq_force_norm": eq["force_norm"],
                "eq_force_norm_after_backtrack": eq["eq_force_norm_after_backtrack"],
                "last_line_search_alpha": eq["last_line_search_alpha"],
                "eq_converged": eq["converged"],
                "eq_converged_practical": eq["converged_practical"],
                "eq_outer_steps": eq["outer_steps"],
                "eq_fd_eps": eq["equilibrium_fd_eps"],
            }
        )
    return rows


def main() -> None:
    rows = run_cases(CASES)
    print("5-molecule comparison (H2 anchored)")
    print(
        "name\tstatic_scaled_eV\tnuclear_ode_scaled_eV\tjoint_ode_scaled_eV\treference_eV\t"
        "static_err_%\tnuclear_err_%\tjoint_err_%\tx_eq_lattice\teq_speed\teq_force_norm\t"
        "eq_force_after_bt\tlast_alpha\tconverged\tconv_practical\touter_steps\teq_fd_eps"
    )
    for r in rows:
        print(
            f"{r['name']}\t{r['static_scaled_ev']:.12f}\t"
            f"{r['nuclear_scaled_ev']:.12f}\t{r['joint_scaled_ev']:.12f}\t"
            f"{r['reference_ev']:.6f}\t{r['static_error_pct']:.6f}\t"
            f"{r['nuclear_error_pct']:.6f}\t{r['joint_error_pct']:.6f}\t"
            f"{r['x_eq_lattice']:.6f}\t{r['eq_speed']:.6e}\t{r['eq_force_norm']:.6e}\t"
            f"{r['eq_force_norm_after_backtrack']:.6e}\t{r['last_line_search_alpha']:.6e}\t"
            f"{r['eq_converged']}\t{r['eq_converged_practical']}\t{r['eq_outer_steps']:.0f}\t{r['eq_fd_eps']:.2e}"
        )


if __name__ == "__main__":
    main()
