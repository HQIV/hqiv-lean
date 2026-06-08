#!/usr/bin/env python3
"""
HQIV molecular benchmarks: H₂ (NumPy integrals + NumPy FCI) vs LiH (STO-3G).

H₂ uses ``hqiv_molecular_hamiltonian.example_h2_sto3g_fci`` (s-only contracted
Gaussians + dense FCI).

LiH uses ``hqiv_cartesian_gaussian.example_lih_sto3g_fci``: same FCI driver, but
**Libcint-quality ERIs** when PySCF is available (``eri_backend: pyscf``); otherwise
``eri_backend: numpy_fd`` (finite-difference Cartesian ERIs — fine for overlap /
core Hamiltonian checks, not for quantitative Li p-shell benchmarks).
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import hqiv_cartesian_gaussian as cg  # noqa: E402
import hqiv_molecular_hamiltonian as hm  # noqa: E402


def main() -> None:
    h2 = hm.example_h2_sto3g_fci(1.4)
    print("H2 STO-3G @ R = 1.4 Bohr (NumPy integrals + NumPy FCI)")
    for k, v in h2.items():
        print(f"  {k}: {v}")

    print()
    lih = cg.example_lih_sto3g_fci(3.015)
    print("LiH STO-3G @ R = 3.015 Bohr (full CI, 6 spatial AOs)")
    for k, v in lih.items():
        print(f"  {k}: {v}")
    if lih.get("eri_backend") == "numpy_fd":
        print()
        print(
            "  Tip: run this script with PySCF (e.g. .venv_qc/bin/python) for Libcint ERIs "
            "and literature-aligned LiH energies."
        )


if __name__ == "__main__":
    main()
