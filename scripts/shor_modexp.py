#!/usr/bin/env python3
"""
Controlled modular multiplication / exponentiation for Shor period finding.

Adapted from the Qiskit-based implementation in ``mqt.bench.benchmarks.shor``
(Apache-2.0, IBM/Qiskit lineage). Exposes a counting-register width parameter so
textbook (2L) and orthogonal-diagonal (L) schedules share the same arithmetic core.

Disk cache under ``HQIV_LEAN/scripts/.cache/modexp/`` speeds repeated benchmark runs.
"""

from __future__ import annotations

import hashlib
import math
import pickle
from pathlib import Path
from typing import TYPE_CHECKING, Any

import numpy as np

if TYPE_CHECKING:
    from numpy.typing import NDArray
    from qiskit.circuit import QuantumCircuit

_CACHE_DIR = Path(__file__).resolve().parent / ".cache" / "modexp"
_MEMORY_CACHE: dict[str, Any] = {}


def num_bits_for_modulus(n: int) -> int:
    """Bits in the modulus register (matches standard Shor sizing)."""
    return max(2, n).bit_length()


def choose_coprime_base(n: int, start: int = 2) -> int:
    """Smallest base ≥ ``start`` with gcd(a, n) = 1."""
    a = max(2, start)
    while a < n:
        if math.gcd(a, n) == 1:
            return a
        a += 1
    raise ValueError(f"no coprime base below n={n}")


def _cache_key(modulus: int, base: int, num_counting_qubits: int, decompose_reps: int) -> str:
    raw = f"{modulus}:{base}:{num_counting_qubits}:{decompose_reps}"
    return hashlib.sha256(raw.encode()).hexdigest()[:24]


def clear_modexp_cache() -> None:
    """Clear in-memory and on-disk mod-exp cache."""
    _MEMORY_CACHE.clear()
    if _CACHE_DIR.is_dir():
        for p in _CACHE_DIR.glob("*.pkl"):
            p.unlink()


class ModularShorArithmetic:
    """Fourier-space modular add / multiply / exponentiation building blocks."""

    @staticmethod
    def _get_angles(a: int, n_bits: int) -> NDArray[np.float64]:
        bits_little_endian = (f"{a:b}".zfill(n_bits))[::-1]
        angles = np.zeros(n_bits)
        for i in range(n_bits):
            for j in range(i + 1):
                k = i - j
                if bits_little_endian[j] == "1":
                    angles[i] += 2.0**-k
        return angles * np.pi

    @staticmethod
    def _phi_add_gate(angles: NDArray[np.float64] | Any) -> QuantumCircuit:
        from qiskit.circuit import QuantumCircuit

        circuit = QuantumCircuit(len(angles), name="phi_add_a")
        for i, angle in enumerate(angles):
            circuit.p(angle, i)
        return circuit

    def _double_controlled_phi_add_mod_n(
        self,
        angles: NDArray[np.float64] | Any,
        c_phi_add_n: QuantumCircuit,
        iphi_add_n: QuantumCircuit,
        qft: QuantumCircuit,
        iqft: QuantumCircuit,
    ) -> QuantumCircuit:
        from qiskit.circuit import QuantumCircuit, QuantumRegister

        ctrl_qreg = QuantumRegister(2, "ctrl")
        b_qreg = QuantumRegister(len(angles), "b")
        flag_qreg = QuantumRegister(1, "flag")

        circuit = QuantumCircuit(ctrl_qreg, b_qreg, flag_qreg, name="ccphi_add_a_mod_N")

        cc_phi_add_a = self._phi_add_gate(angles).control(2)
        cc_iphi_add_a = cc_phi_add_a.inverse()

        circuit.compose(cc_phi_add_a, [*ctrl_qreg, *b_qreg], inplace=True)
        circuit.compose(iphi_add_n, b_qreg, inplace=True)
        circuit.compose(iqft, b_qreg, inplace=True)
        circuit.cx(b_qreg[-1], flag_qreg[0])
        circuit.compose(qft, b_qreg, inplace=True)
        circuit.compose(c_phi_add_n, [*flag_qreg, *b_qreg], inplace=True)
        circuit.compose(cc_iphi_add_a, [*ctrl_qreg, *b_qreg], inplace=True)
        circuit.compose(iqft, b_qreg, inplace=True)
        circuit.x(b_qreg[-1])
        circuit.cx(b_qreg[-1], flag_qreg[0])
        circuit.x(b_qreg[-1])
        circuit.compose(qft, b_qreg, inplace=True)
        circuit.compose(cc_phi_add_a, [*ctrl_qreg, *b_qreg], inplace=True)
        return circuit

    def _controlled_multiple_mod_n(
        self,
        n_bits: int,
        modulus: int,
        multiplier: int,
        c_phi_add_n: QuantumCircuit,
        iphi_add_n: QuantumCircuit,
        qft: QuantumCircuit,
        iqft: QuantumCircuit,
    ) -> QuantumCircuit:
        from qiskit.circuit import ParameterVector, QuantumCircuit, QuantumRegister

        ctrl_qreg = QuantumRegister(1, "ctrl")
        x_qreg = QuantumRegister(n_bits, "x")
        b_qreg = QuantumRegister(n_bits + 1, "b")
        flag_qreg = QuantumRegister(1, "flag")

        circuit = QuantumCircuit(ctrl_qreg, x_qreg, b_qreg, flag_qreg, name="cmult_a_mod_N")

        angle_params = ParameterVector("angles", length=n_bits + 1)
        modulo_adder = self._double_controlled_phi_add_mod_n(
            angle_params, c_phi_add_n, iphi_add_n, qft, iqft
        )

        def append_adder(adder: QuantumCircuit, constant: int, idx: int) -> None:
            partial = (pow(2, idx, modulus) * constant) % modulus
            ang = self._get_angles(partial, n_bits + 1)
            bound = adder.assign_parameters({angle_params: ang})
            circuit.append(bound, [*ctrl_qreg, x_qreg[idx], *b_qreg, *flag_qreg])

        circuit.compose(qft, b_qreg, inplace=True)
        for i in range(n_bits):
            append_adder(modulo_adder, multiplier, i)
        circuit.compose(iqft, b_qreg, inplace=True)
        for i in range(n_bits):
            circuit.cswap(ctrl_qreg, x_qreg[i], b_qreg[i])
        circuit.compose(qft, b_qreg, inplace=True)

        inv = pow(multiplier, -1, modulus)
        modulo_adder_inv = modulo_adder.inverse()
        for i in reversed(range(n_bits)):
            append_adder(modulo_adder_inv, inv, i)
        circuit.compose(iqft, b_qreg, inplace=True)
        return circuit

    def power_mod_n(
        self,
        modulus: int,
        base: int,
        *,
        num_counting_qubits: int,
        decompose_reps: int = 2,
    ) -> QuantumCircuit:
        from qiskit.circuit import QuantumCircuit, QuantumRegister
        from qiskit.synthesis import synth_qft_full

        n_bits = num_bits_for_modulus(modulus)
        if num_counting_qubits < 1:
            raise ValueError("num_counting_qubits must be positive")

        up = QuantumRegister(num_counting_qubits, "count")
        down = QuantumRegister(n_bits, "work")
        aux = QuantumRegister(n_bits + 2, "aux")

        circuit = QuantumCircuit(up, down, aux, name=f"modexp_{base}^x_mod_{modulus}")

        qft = synth_qft_full(n_bits + 1, do_swaps=False)
        iqft = qft.inverse()

        phi_add_n = self._phi_add_gate(self._get_angles(modulus, n_bits + 1))
        iphi_add_n = phi_add_n.inverse()
        c_phi_add_n = phi_add_n.control(1)

        for i in range(num_counting_qubits):
            partial_a = pow(base, 2**i, modulus)
            mult = self._controlled_multiple_mod_n(
                n_bits, modulus, partial_a, c_phi_add_n, iphi_add_n, qft, iqft
            )
            mult_d = mult.decompose(reps=decompose_reps) if decompose_reps > 0 else mult
            circuit.compose(mult_d, [up[i], *down, *aux], inplace=True)

        return circuit


def build_modular_exponentiation(
    n: int,
    a: int | None = None,
    *,
    num_counting_qubits: int | None = None,
    decompose_reps: int = 2,
    use_cache: bool = True,
) -> QuantumCircuit:
    """Return a circuit block implementing controlled ``a^x mod n``."""
    if n < 3:
        raise ValueError(f"modulus must be ≥ 3, got {n}")
    base = a if a is not None else choose_coprime_base(n)
    if not (1 < base < n and math.gcd(base, n) == 1):
        raise ValueError(f"invalid base a={base} for n={n}")

    n_bits = num_bits_for_modulus(n)
    count = num_counting_qubits if num_counting_qubits is not None else 2 * n_bits
    key = _cache_key(n, base, count, decompose_reps)

    if use_cache and key in _MEMORY_CACHE:
        return _MEMORY_CACHE[key].copy()

    _CACHE_DIR.mkdir(parents=True, exist_ok=True)
    disk = _CACHE_DIR / f"{key}.pkl"
    if use_cache and disk.is_file():
        qc = pickle.loads(disk.read_bytes())
        _MEMORY_CACHE[key] = qc
        return qc.copy()

    qc = ModularShorArithmetic().power_mod_n(
        n, base, num_counting_qubits=count, decompose_reps=decompose_reps
    )
    if use_cache:
        _MEMORY_CACHE[key] = qc
        disk.write_bytes(pickle.dumps(qc))
    return qc.copy()


def modexp_transpiled_signature(
    n: int,
    a: int,
    *,
    num_counting_qubits: int,
    decompose_reps: int,
    opt_level: int = 1,
    use_cache: bool = True,
) -> tuple[int, int]:
    """Transpiled (qubits, depth) for mod-exp block only — count-only helper."""
    from qiskit import transpile

    qc = build_modular_exponentiation(
        n,
        a,
        num_counting_qubits=num_counting_qubits,
        decompose_reps=decompose_reps,
        use_cache=use_cache,
    )
    t = transpile(qc, optimization_level=opt_level, seed_transpiler=0)
    return t.num_qubits, t.depth()
