#!/usr/bin/env python3
"""Canonical half-filled 2-site Hubbard dimer in the 4-state N=2 subspace.

Basis:
  0: |↑↓,0>
  1: |0,↑↓>
  2: |↑,↓>
  3: |↓,↑>

Hamiltonian:
    [ U,  0, -t,  t]
    [ 0,  U, -t,  t]
    [-t, -t,  0,  0]
    [ t,  t,  0,  0]

This model restores the charge-fluctuation pathways needed for the AF singlet
ground state in the repulsive regime.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

_SCRIPTS = Path(__file__).resolve().parent
_CORE_MOD = _SCRIPTS / "qm_general_finite_core.py"
_CORE_SPEC = importlib.util.spec_from_file_location("qm_general_finite_core", _CORE_MOD)
assert _CORE_SPEC and _CORE_SPEC.loader
_core = importlib.util.module_from_spec(_CORE_SPEC)
_CORE_SPEC.loader.exec_module(_core)


def phi_of_shell(m: int) -> float:
    return _core.phi_of_shell(m)


def lambda_shell(m: int, lambda0: float = 1.0, coherence: float = 1.0) -> float:
    return _core.shell_coupling(m, lambda0=lambda0, coherence=coherence)


def hubbard_half_filled_hamiltonian(t_hop: float, U: float) -> np.ndarray:
    return base_half_filled_model(t_hop).with_interaction(interaction_operator(), U).H


def base_kinetic_hamiltonian(t_hop: float) -> np.ndarray:
    return np.array(
        [
            [0.0, 0.0, -t_hop, t_hop],
            [0.0, 0.0, -t_hop, t_hop],
            [-t_hop, -t_hop, 0.0, 0.0],
            [t_hop, t_hop, 0.0, 0.0],
        ],
        dtype=np.complex128,
    )


def interaction_operator() -> np.ndarray:
    return np.diag([1.0, 1.0, 0.0, 0.0]).astype(np.complex128)


def base_half_filled_model(t_hop: float) -> "_core.FiniteManyBodyModel":
    return _core.FiniteManyBodyModel(base_kinetic_hamiltonian(t_hop), observables())


def half_filled_model(t_hop: float, U: float) -> "_core.FiniteManyBodyModel":
    return base_half_filled_model(t_hop).with_interaction(interaction_operator(), U)


def exp_iHt(H: np.ndarray, t: float) -> np.ndarray:
    e, v = np.linalg.eigh(H)
    phase = np.exp(-1j * t * e)
    return (v * phase) @ v.conj().T


def observables() -> dict[str, np.ndarray]:
    # Total double occupancy D = n1_up*n1_dn + n2_up*n2_dn.
    d_total = np.diag([1.0, 1.0, 0.0, 0.0]).astype(np.complex128)
    d_per_site = 0.5 * d_total
    # S1·S2 on singly-occupied sector; zero on doublon-hole states.
    sdot = np.array(
        [
            [0.0, 0.0, 0.0, 0.0],
            [0.0, 0.0, 0.0, 0.0],
            [0.0, 0.0, -0.25, 0.5],
            [0.0, 0.0, 0.5, -0.25],
        ],
        dtype=np.complex128,
    )
    return {
        "double_occupancy_total": d_total,
        "double_occupancy_per_site": d_per_site,
        "spin_correlation": sdot,
    }


def expectation(psi: np.ndarray, op: np.ndarray) -> float:
    v = np.asarray(psi, dtype=np.complex128).reshape(-1)
    return float(np.real_if_close(np.vdot(v, op @ v)))


def eigensystem(H: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    e, v = np.linalg.eigh(H)
    order = np.argsort(e)
    return e[order], v[:, order]


def ground_observables(H: np.ndarray) -> dict[str, float]:
    model = _core.FiniteManyBodyModel(np.asarray(H, dtype=np.complex128), observables())
    out = model.ground_observables()
    return {
        "ground_energy": out["ground_energy"],
        "gap": out["gap"],
        "double_occupancy_total": out["double_occupancy_total"],
        "double_occupancy_per_site": out["double_occupancy_per_site"],
        "spin_correlation": out["spin_correlation"],
    }


def thermal_observables(H: np.ndarray, beta: float) -> dict[str, float]:
    model = _core.FiniteManyBodyModel(np.asarray(H, dtype=np.complex128), observables())
    th = model.thermal_observables(beta=beta)
    return {
        "beta": th["beta"],
        "partition_function": th["partition_function"],
        "thermal_energy": th["thermal_energy"],
        "thermal_double_occupancy_total": th["thermal_double_occupancy_total"],
        "thermal_spin_correlation": th["thermal_spin_correlation"],
    }


def singlet_initial_state() -> np.ndarray:
    return np.array([0.0, 0.0, 1.0 / math.sqrt(2.0), -1.0 / math.sqrt(2.0)], dtype=np.complex128)


def finite_time_observables(H: np.ndarray, time: float) -> dict[str, float]:
    ops = observables()
    psi_t = exp_iHt(H, time) @ singlet_initial_state()
    return {
        "time": time,
        "double_occupancy_total_t": expectation(psi_t, ops["double_occupancy_total"]),
        "spin_correlation_t": expectation(psi_t, ops["spin_correlation"]),
    }


def closed_form_eigenvalues(t_hop: float, U: float) -> np.ndarray:
    s = math.sqrt(U * U + 16.0 * t_hop * t_hop)
    vals = np.array(
        [
            0.0,
            U,
            0.5 * (U - s),
            0.5 * (U + s),
        ],
        dtype=np.float64,
    )
    return np.sort(vals)


def run_demo(m: int, t_hop: float, lambda0: float, coherence: float, time: float, beta: float) -> dict[str, Any]:
    params = _core.ShellCoherenceParams(lambda0=lambda0, kappa=1.0, plasma_scalar_abs=coherence)
    U = params.coupling(m)
    model = half_filled_model(t_hop=t_hop, U=U)
    H = model.H
    e = np.sort(np.linalg.eigvalsh(H))
    g = ground_observables(H)
    ft = finite_time_observables(H, time=time)
    th = thermal_observables(H, beta=beta)
    return {
        "model": "hubbard_dimer_half_filled_canonical",
        "shell_m": m,
        "phi_of_shell": phi_of_shell(m),
        "U_shell": U,
        "t_hop": t_hop,
        "eigenvalues": [float(x) for x in e.tolist()],
        "closed_form_eigenvalues": [float(x) for x in closed_form_eigenvalues(t_hop, U).tolist()],
        **g,
        **ft,
        **th,
    }


def shell_scan(
    m_start: int,
    m_end: int,
    t_hop: float,
    lambda0: float,
    coherence: float,
    time: float,
    beta: float,
) -> dict[str, Any]:
    rows: list[dict[str, float | int]] = []
    for m in range(m_start, m_end + 1):
        out = run_demo(m=m, t_hop=t_hop, lambda0=lambda0, coherence=coherence, time=time, beta=beta)
        rows.append(
            {
                "m": m,
                "phi_of_shell": float(out["phi_of_shell"]),
                "U_shell": float(out["U_shell"]),
                "ground_energy": float(out["ground_energy"]),
                "gap": float(out["gap"]),
                "double_occupancy_total": float(out["double_occupancy_total"]),
                "spin_correlation": float(out["spin_correlation"]),
                "thermal_double_occupancy_total": float(out["thermal_double_occupancy_total"]),
                "thermal_spin_correlation": float(out["thermal_spin_correlation"]),
                "thermal_energy": float(out["thermal_energy"]),
            }
        )
    return {
        "model": "hubbard_dimer_half_filled_canonical",
        "scan_kind": "shell_index_sweep",
        "m_start": m_start,
        "m_end": m_end,
        "t_hop": t_hop,
        "lambda0": lambda0,
        "coherence": coherence,
        "time": time,
        "beta": beta,
        "rows": rows,
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--m", type=int, default=4)
    p.add_argument("--t-hop", type=float, default=1.0)
    p.add_argument("--lambda0", type=float, default=0.8)
    p.add_argument("--coherence", type=float, default=1.0)
    p.add_argument("--time", type=float, default=math.pi / 5.0)
    p.add_argument("--beta", type=float, default=1.0, help="inverse temperature for thermal observables")
    p.add_argument("--scan-m-start", type=int, default=2)
    p.add_argument("--scan-m-end", type=int, default=8)
    p.add_argument("--json-out", metavar="PATH")
    p.add_argument("--scan-json-out", metavar="PATH")
    args = p.parse_args()

    out = run_demo(
        m=args.m,
        t_hop=args.t_hop,
        lambda0=args.lambda0,
        coherence=args.coherence,
        time=args.time,
        beta=args.beta,
    )
    text = json.dumps(out, indent=2, sort_keys=True)
    if args.json_out:
        path = Path(args.json_out)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text + "\n", encoding="utf-8")
    else:
        print(text)

    if args.scan_json_out:
        scan = shell_scan(
            m_start=args.scan_m_start,
            m_end=args.scan_m_end,
            t_hop=args.t_hop,
            lambda0=args.lambda0,
            coherence=args.coherence,
            time=args.time,
            beta=args.beta,
        )
        path = Path(args.scan_json_out)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(scan, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
