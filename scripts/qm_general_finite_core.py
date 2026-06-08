#!/usr/bin/env python3
"""General finite-dimensional many-body core utilities.

This is the reusable Python backbone for finite Hermitian models:
- eigensystem / expectation / thermal averages
- shell-coherence coupling helpers
- model-level helper class reusable by dimer/atom/molecule toys.
"""

from __future__ import annotations

from typing import Any

import numpy as np


def phi_of_shell(m: int) -> float:
    return 2.0 * (float(m) + 1.0)


def coherence_from_plasma_amp(kappa: float, plasma_scalar_abs: float) -> float:
    return float(min(1.0, kappa * abs(plasma_scalar_abs)))


def shell_coupling(m: int, lambda0: float, coherence: float) -> float:
    return lambda0 * coherence * (phi_of_shell(m) / phi_of_shell(4))


class ShellCoherenceParams:
    def __init__(self, lambda0: float, kappa: float, plasma_scalar_abs: float) -> None:
        self.lambda0 = float(lambda0)
        self.kappa = float(kappa)
        self.plasma_scalar_abs = float(plasma_scalar_abs)

    @property
    def coherence(self) -> float:
        return coherence_from_plasma_amp(self.kappa, self.plasma_scalar_abs)

    def coupling(self, m: int) -> float:
        return shell_coupling(m, self.lambda0, self.coherence)


class FiniteManyBodyModel:
    def __init__(self, H: np.ndarray, observables: dict[str, np.ndarray] | None = None) -> None:
        Hc = np.asarray(H, dtype=np.complex128)
        if Hc.ndim != 2 or Hc.shape[0] != Hc.shape[1]:
            raise ValueError("H must be square")
        self.H = Hc
        self.n = Hc.shape[0]
        self.observables: dict[str, np.ndarray] = observables or {}

    def with_interaction(self, V: np.ndarray, g: float) -> "FiniteManyBodyModel":
        Vc = np.asarray(V, dtype=np.complex128)
        if Vc.shape != self.H.shape:
            raise ValueError("interaction shape mismatch")
        return FiniteManyBodyModel(self.H + g * Vc, dict(self.observables))

    def eigensystem(self) -> tuple[np.ndarray, np.ndarray]:
        e, v = np.linalg.eigh(self.H)
        order = np.argsort(e)
        return e[order], v[:, order]

    @staticmethod
    def expectation(psi: np.ndarray, op: np.ndarray) -> float:
        v = np.asarray(psi, dtype=np.complex128).reshape(-1)
        return float(np.real_if_close(np.vdot(v, op @ v)))

    def ground_observables(self) -> dict[str, float]:
        e, v = self.eigensystem()
        psi0 = v[:, 0]
        out: dict[str, float] = {
            "ground_energy": float(e[0]),
            "gap": float(e[1] - e[0]) if len(e) > 1 else 0.0,
        }
        for k, O in self.observables.items():
            out[k] = self.expectation(psi0, O)
        return out

    def thermal_observables(self, beta: float) -> dict[str, float]:
        if beta < 0.0:
            raise ValueError("beta must be nonnegative")
        e, v = self.eigensystem()
        e0 = float(e[0])
        w = np.exp(-beta * (e - e0))
        Z = float(np.sum(w))
        if Z <= 0.0:
            raise ValueError("invalid partition function")
        p = w / Z

        out: dict[str, float] = {
            "beta": float(beta),
            "partition_function": Z,
            "thermal_energy": float(np.dot(p, np.asarray(e, dtype=float))),
        }
        for k, O in self.observables.items():
            vals = np.array([self.expectation(v[:, i], O) for i in range(v.shape[1])], dtype=float)
            out[f"thermal_{k}"] = float(np.dot(p, vals))
        return out

    def summary(self, beta: float | None = None) -> dict[str, Any]:
        out = self.ground_observables()
        if beta is not None:
            out.update(self.thermal_observables(beta))
        return out
