#!/usr/bin/env python3
"""Finite-dimensional two-subsystem toy: Kronecker-sum Hamiltonian and Schrödinger evolution.

Formal Lean counterpart: `Hqiv.QuantumMechanics.FiniteManyBodyTensorScaffold`
(`tensorKroneckerSumMatrix`, `finTensorIndexEquiv`).

We use `numpy.kron` in the standard order `kron(Ha, Ib) + kron(Ia, Hb)`, matching the
non-interacting many-body template before adding interaction terms or HQIV shell factors.
"""

from __future__ import annotations

import argparse
import json
import math
from typing import Any

import numpy as np


def kronecker_sum(Ha: np.ndarray, Hb: np.ndarray) -> np.ndarray:
    """Return `kron(Ha, I) + kron(I, Hb)` for square Hermitian `Ha`, `Hb`."""
    na, nb = Ha.shape[0], Hb.shape[0]
    if Ha.shape != (na, na) or Hb.shape != (nb, nb):
        raise ValueError("Ha and Hb must be square")
    ida = np.eye(na, dtype=np.complex128)
    idb = np.eye(nb, dtype=np.complex128)
    return np.kron(Ha, idb) + np.kron(ida, Hb)


def exp_iHt(H: np.ndarray, t: float) -> np.ndarray:
    """`U(t) = exp(-i H t)` for Hermitian `H` via an eigen-decomposition."""
    e, v = np.linalg.eigh(H)
    phase = np.exp(-1j * t * e)
    return (v * phase) @ v.conj().T


def populations(psi: np.ndarray) -> list[float]:
    z = np.asarray(psi, dtype=np.complex128).ravel()
    p = np.abs(z) ** 2
    s = float(np.sum(p))
    if s <= 0.0:
        return [1.0 / len(z)] * len(z)
    return [float(x / s) for x in p]


def demo_two_qubit_zz() -> dict[str, Any]:
    """Ha = Z, Hb = Z (Pauli matrices); spectrum is {-2, 0, 0, 2} with multiplicities."""
    sz = np.array([[1.0, 0.0], [0.0, -1.0]], dtype=np.complex128)
    h = kronecker_sum(sz, sz)
    e = np.linalg.eigvalsh(h)
    t = math.pi / 4.0
    u = exp_iHt(h, t)
    psi0 = np.array([1.0, 0.0, 0.0, 0.0], dtype=np.complex128)
    psi_t = u @ psi0
    return {
        "model": "two_qubit_sigma_z_sum",
        "eigenvalues": [float(x) for x in sorted(e.tolist())],
        "time": t,
        "populations_t": populations(psi_t),
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--json-out",
        metavar="PATH",
        help="Write experiment summary JSON to PATH (stdout if omitted)",
    )
    args = p.parse_args()
    out = demo_two_qubit_zz()
    text = json.dumps(out, indent=2, sort_keys=True)
    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as f:
            f.write(text + "\n")
    else:
        print(text)


if __name__ == "__main__":
    main()
