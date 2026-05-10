#!/usr/bin/env python3
"""Finite 4D Hubbard-dimer-inspired toy (two-site, spin-1/2 reduced sector).

Hamiltonian:
`H = -t (σx ⊗ I + I ⊗ σx) + λ (σz ⊗ σz)`.

Canonical observables:
- double occupancy proxy:
  `(1/4) (I - σz⊗I - I⊗σz + σz⊗σz)`
- spin correlation:
  `S1·S2 = (1/4)(σx⊗σx + σy⊗σy + σz⊗σz)`
- spectral gap:
  `E1 - E0` from sorted eigenvalues.

Shell hook:
`lambda_shell(m) = lambda0 * coherence * phi_of_shell(m) / phi_of_shell(4)`,
with `phi_of_shell(m) = 2(m+1)`.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


def phi_of_shell(m: int) -> float:
    return 2.0 * (float(m) + 1.0)


def lambda_shell(m: int, lambda0: float = 1.0, coherence: float = 1.0) -> float:
    """Shell-coupled interaction strength, anchored so `lambda_shell(4)=lambda0*coherence`."""
    denom = phi_of_shell(4)
    if denom <= 0.0:
        raise ValueError("invalid shell normalization")
    return lambda0 * coherence * (phi_of_shell(m) / denom)


def kronecker_sum(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Return `kron(a, I) + kron(I, b)`."""
    na, nb = a.shape[0], b.shape[0]
    if a.shape != (na, na) or b.shape != (nb, nb):
        raise ValueError("a and b must be square")
    return np.kron(a, np.eye(nb, dtype=np.complex128)) + np.kron(np.eye(na, dtype=np.complex128), b)


def exp_iHt(H: np.ndarray, t: float) -> np.ndarray:
    """`U(t) = exp(-i H t)` via eigendecomposition for Hermitian H."""
    e, v = np.linalg.eigh(H)
    phase = np.exp(-1j * t * e)
    return (v * phase) @ v.conj().T


def hubbard_dimer_hamiltonian(t_hop: float, lam: float) -> np.ndarray:
    sx, _, sz = pauli_triplet()
    h0 = -t_hop * kronecker_sum(sx, sx)
    vzz = np.kron(sz, sz)
    return h0 + lam * vzz


def spectrum(H: np.ndarray) -> list[float]:
    return [float(x) for x in np.sort(np.linalg.eigvalsh(H)).tolist()]


def populations(psi: np.ndarray) -> list[float]:
    w = np.asarray(psi, dtype=np.complex128).ravel()
    p = np.abs(w) ** 2
    s = float(np.sum(p))
    if s <= 0.0:
        return [1.0 / len(w)] * len(w)
    return [float(x / s) for x in p]


def pauli_triplet() -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    sx = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128)
    sy = np.array([[0.0, -1.0j], [1.0j, 0.0]], dtype=np.complex128)
    sz = np.array([[1.0, 0.0], [0.0, -1.0]], dtype=np.complex128)
    return sx, sy, sz


def observables() -> dict[str, np.ndarray]:
    sx, sy, sz = pauli_triplet()
    i2 = np.eye(2, dtype=np.complex128)
    double_occ = 0.25 * (np.eye(4, dtype=np.complex128) - np.kron(sz, i2) - np.kron(i2, sz) + np.kron(sz, sz))
    spin_corr = 0.25 * (np.kron(sx, sx) + np.kron(sy, sy) + np.kron(sz, sz))
    return {"double_occupancy_proxy": double_occ, "spin_correlation": spin_corr}


def expectation(psi: np.ndarray, op: np.ndarray) -> float:
    v = np.asarray(psi, dtype=np.complex128).reshape(-1)
    val = np.vdot(v, op @ v)
    return float(np.real_if_close(val))


def eigensystem(H: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    e, v = np.linalg.eigh(H)
    order = np.argsort(e)
    return e[order], v[:, order]


def ground_observables(H: np.ndarray) -> dict[str, float]:
    e, v = eigensystem(H)
    psi_g = v[:, 0]
    ops = observables()
    gap = float(e[1] - e[0]) if len(e) > 1 else 0.0
    return {
        "ground_energy": float(e[0]),
        "gap": gap,
        "double_occupancy_proxy": expectation(psi_g, ops["double_occupancy_proxy"]),
        "spin_correlation": expectation(psi_g, ops["spin_correlation"]),
    }


def half_filling_singlet_state() -> np.ndarray:
    # Basis order for kron(local, local): |uu>, |ud>, |du>, |dd>.
    psi = np.array([0.0, 1.0 / math.sqrt(2.0), -1.0 / math.sqrt(2.0), 0.0], dtype=np.complex128)
    return psi


def finite_time_observables(H: np.ndarray, time: float) -> dict[str, float]:
    ops = observables()
    psi0 = half_filling_singlet_state()
    psi_t = exp_iHt(H, time) @ psi0
    return {
        "time": time,
        "double_occupancy_proxy_t": expectation(psi_t, ops["double_occupancy_proxy"]),
        "spin_correlation_t": expectation(psi_t, ops["spin_correlation"]),
    }


def shell_scan(
    m_start: int,
    m_end: int,
    t_hop: float,
    lambda0: float,
    coherence: float,
    time: float,
) -> dict[str, Any]:
    rows: list[dict[str, float | int]] = []
    for m in range(m_start, m_end + 1):
        lam = lambda_shell(m, lambda0=lambda0, coherence=coherence)
        H = hubbard_dimer_hamiltonian(t_hop=t_hop, lam=lam)
        g = ground_observables(H)
        ft = finite_time_observables(H, time=time)
        rows.append(
            {
                "m": m,
                "phi_of_shell": phi_of_shell(m),
                "lambda_shell": lam,
                "ground_energy": g["ground_energy"],
                "gap": g["gap"],
                "double_occupancy_proxy": g["double_occupancy_proxy"],
                "spin_correlation": g["spin_correlation"],
                "double_occupancy_proxy_t": ft["double_occupancy_proxy_t"],
                "spin_correlation_t": ft["spin_correlation_t"],
            }
        )
    return {
        "model": "hubbard_dimer_reduced_spin_sector",
        "scan_kind": "shell_index_sweep",
        "m_start": m_start,
        "m_end": m_end,
        "t_hop": t_hop,
        "lambda0": lambda0,
        "coherence": coherence,
        "time": time,
        "rows": rows,
    }


def run_demo(m: int, t_hop: float, lambda0: float, coherence: float, time: float) -> dict[str, Any]:
    lam = lambda_shell(m, lambda0=lambda0, coherence=coherence)
    H = hubbard_dimer_hamiltonian(t_hop=t_hop, lam=lam)
    g = ground_observables(H)
    ft = finite_time_observables(H, time=time)
    return {
        "model": "hubbard_dimer_reduced_spin_sector",
        "shell_m": m,
        "phi_of_shell": phi_of_shell(m),
        "lambda_shell": lam,
        "t_hop": t_hop,
        "eigenvalues": spectrum(H),
        "ground_energy": g["ground_energy"],
        "gap": g["gap"],
        "double_occupancy_proxy": g["double_occupancy_proxy"],
        "spin_correlation": g["spin_correlation"],
        **ft,
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--m", type=int, default=4, help="shell index")
    p.add_argument("--t-hop", type=float, default=1.0, help="hopping strength")
    p.add_argument("--lambda0", type=float, default=0.8, help="base interaction amplitude")
    p.add_argument("--coherence", type=float, default=1.0, help="coherence multiplier")
    p.add_argument("--time", type=float, default=math.pi / 5.0, help="finite-time observable probe time")
    p.add_argument("--scan-m-start", type=int, default=2, help="shell scan start index")
    p.add_argument("--scan-m-end", type=int, default=8, help="shell scan end index")
    p.add_argument("--json-out", metavar="PATH", help="write output JSON to PATH")
    p.add_argument(
        "--scan-json-out",
        metavar="PATH",
        help="write shell-scan JSON (m_start..m_end) to PATH",
    )
    args = p.parse_args()

    out = run_demo(
        m=args.m,
        t_hop=args.t_hop,
        lambda0=args.lambda0,
        coherence=args.coherence,
        time=args.time,
    )
    text = json.dumps(out, indent=2, sort_keys=True)
    if args.json_out:
        out_path = Path(args.json_out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as f:
            f.write(text + "\n")
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
        )
        scan_text = json.dumps(scan, indent=2, sort_keys=True)
        scan_path = Path(args.scan_json_out)
        scan_path.parent.mkdir(parents=True, exist_ok=True)
        with open(scan_path, "w", encoding="utf-8") as f:
            f.write(scan_text + "\n")


if __name__ == "__main__":
    main()
