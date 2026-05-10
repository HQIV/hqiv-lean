#!/usr/bin/env python3
"""
Exploratory HQIV-style toy: **spin, charge, mass** first — shell index optional.

Narrative (see conversation):
  • Horizons carry standing-wave / mode content; **spin** is the binary that lets
    identical fermions **pair** (singlet) or **avoid** (Pauli).
  • **Charge** sets Coulomb channels; **mass** sets inertia and **reduced mass**
    for composite motion (isotopes: same Q, different M).
  • **Shell** is *not* the user-facing quantum number here; if it appears, it is
    only a coarse **resolution / truncation** stand-in.

This script is intentionally small and dependency-free (stdlib + math only).
It does not solve Schrödinger; it **enumerates** compatibility rules and prints
tables so you can see how the pieces combine.

Run:  python3 scripts/hqiv_spin_charge_mass_explore.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from itertools import product


# ---------------------------------------------------------------------------
# Core carriers: charge (in units of e), mass (electron mass = 1 in a.u.), spin


@dataclass(frozen=True)
class Species:
    """A particle species labeled by intrinsic quantum numbers we care about."""

    name: str
    charge_e: float  # in units of elementary charge e
    mass_au: float  # relative to m_e = 1 (atomic unit of mass for electrons)
    spin_j: float  # total spin quantum number j (0, 1/2, 1, ...)


def reduced_mass_au(m1: float, m2: float) -> float:
    """μ = m1*m2/(m1+m2) with masses in the same unit (e.g. atomic units, m_e=1)."""
    return (m1 * m2) / (m1 + m2)


# ---------------------------------------------------------------------------
# Electron / nuclei for isotope geometry (mass drives μ; charge Z drives Coulomb scale)


M_ELECTRON = 1.0

# Nucleus mass in atomic units (m_e = 1); same convention as hqiv_isotope_hydrogenic_scales.py
M_NUCLEUS_AU = {
    "p/¹H": 1836.15267343,
    "d/²H": 3670.4829652,
    "t/³H": 5496.92129,
}


def mu_electron_nucleus(label: str) -> float:
    """Reduced mass of electron + nucleus (hydrogenic)."""
    m_n = M_NUCLEUS_AU[label]
    return reduced_mass_au(M_ELECTRON, m_n)


# ---------------------------------------------------------------------------
# Spin-1/2: projections ±1/2; pairing into spin singlet S=0


def fermion_spin_projections() -> tuple[float, float]:
    return (-0.5, 0.5)


def singlet_pair_ok(ms_a: float, ms_b: float, tol: float = 1e-9) -> bool:
    """Two spin-1/2 form J=0 (singlet) iff m_s1 + m_s2 = 0."""
    return abs(ms_a + ms_b) < tol


def triplet_pairs() -> list[tuple[float, float]]:
    """Triplet S=1: (-1/2,-1/2), (1/2,1/2), and symmetric (+,-) with phase — list m_s pairs."""
    return [(-0.5, -0.5), (0.5, 0.5)]


# ---------------------------------------------------------------------------
# Toy: two electrons in same spatial orbital → Pauli: must be singlet (opposite spin)


@dataclass(frozen=True)
class SpatialOrbital:
    """A single spatial mode (label only — no shell index required)."""

    tag: str


@dataclass(frozen=True)
class ElectronState:
    """One electron: spatial orbital + spin projection (m_s = ±1/2)."""

    orbital: SpatialOrbital
    m_s: float


def pauli_two_electrons_same_orbital(states: tuple[ElectronState, ElectronState]) -> bool:
    """Allowed only if spatial orbitals equal implies spins opposite (singlet)."""
    a, b = states
    if a.orbital.tag != b.orbital.tag:
        return True
    return singlet_pair_ok(a.m_s, b.m_s) and not (abs(a.m_s - b.m_s) < 1e-9)


def enumerate_two_electron_determinants(orb: SpatialOrbital) -> list[tuple[ElectronState, ElectronState]]:
    """All ordered pairs of (orb, m_s); filter Pauli for same orbital."""
    ms = fermion_spin_projections()
    pairs: list[tuple[ElectronState, ElectronState]] = []
    for m1, m2 in product(ms, repeat=2):
        p = (ElectronState(orb, m1), ElectronState(orb, m2))
        if pauli_two_electrons_same_orbital(p):
            pairs.append(p)
    return pairs


# ---------------------------------------------------------------------------
# Standing wave on a horizon: use **radial quantum number n** (spectroscopic), not shell m


def hydrogenic_energy_au(mu: float, z: float, n: int) -> float:
    """Non-relativistic hydrogenic levels: E_n = - μ Z² / (2 n²) in Hartree (a.u.)."""
    if n < 1:
        raise ValueError("n >= 1")
    return -mu * z * z / (2.0 * n * n)


def standing_wave_label(n: int, ell: int) -> str:
    """Spectroscopic-style label (n, ℓ) — still no horizon shell index."""
    s_letters = "spdfghiklmnoqrtuvwxyz"
    L = s_letters[ell] if ell < len(s_letters) else f"L={ell}"
    return f"{n}{L}"


# ---------------------------------------------------------------------------
# "How the cards fall": print blocks


def section(title: str) -> None:
    print()
    print("=" * 60)
    print(title)
    print("=" * 60)


def main() -> None:
    section("1) Species table (charge, mass, spin) — primary labels")
    catalog = [
        Species("electron", -1.0, M_ELECTRON, 0.5),
        Species("proton", 1.0, M_NUCLEUS_AU["p/¹H"], 0.5),
        Species("deuteron", 1.0, M_NUCLEUS_AU["d/²H"], 1.0),  # approximate j for display
    ]
    for s in catalog:
        print(f"  {s.name:10}  Q={s.charge_e:+.0f}e  M={s.mass_au:.4f} m_e  j={s.spin_j}")

    section("2) Isotope geometry: same Z, different nucleus mass → different μ (electron–nucleus)")
    z_h = 1.0
    for lbl in M_NUCLEUS_AU:
        mu = mu_electron_nucleus(lbl)
        e1 = hydrogenic_energy_au(mu, z_h, 1)
        print(f"  {lbl:8}  μ={mu:.9f}  E(n=1)={e1:.8f} Ha")

    section("3) Spin pairing: two spin-1/2 electrons — singlet vs triplet (m_s pairs)")
    print("  Singlet S=0 (opposite m_s):", [(a, b) for a in fermion_spin_projections() for b in fermion_spin_projections() if singlet_pair_ok(a, b)])
    print("  Triplet m_s pairs (same orbital, symmetric spin part):", triplet_pairs())

    section("4) Pauli: two electrons in the **same** spatial orbital — only singlet survives")
    orb = SpatialOrbital("φ0")
    allowed = enumerate_two_electron_determinants(orb)
    print(f"  Orbital: {orb.tag}")
    for p in allowed:
        print(f"    allowed: m_s=({p[0].m_s:+.1f}, {p[1].m_s:+.1f})")

    section("5) Standing waves: hydrogenic levels by **n** (not shell index m)")
    mu_p = mu_electron_nucleus("p/¹H")
    for n in range(1, 5):
        e = hydrogenic_energy_au(mu_p, 1.0, n)
        # One label per n at ℓ=0 (s); full multiplet would list ℓ = 0..n−1
        print(f"  n={n}  E_n={e:.8f} Ha   ns = {standing_wave_label(n, 0)}")

    section("6) Charge–charge Coulomb scale (toy): U ∝ Q1 Q2 / r (arbitrary r=1 a.u.)")
    r = 1.0
    pairs_species = [
        ("e-e", -1.0, -1.0),
        ("e-p", -1.0, 1.0),
        ("p-p", 1.0, 1.0),
    ]
    for name, q1, q2 in pairs_species:
        u = q1 * q2 / r
        print(f"  {name:6}  Q1Q2/r = {u:+.4f} (toy: charges in e, r in Bohr)")

    section("7) Epilogue — what this script did *not* do")
    print(
        "  • No horizon shell index m as a user input.\n"
        "  • Mass and charge set isotopes and Coulomb; spin sets pairing/Pauli.\n"
        "  • Radial label n is spectroscopic; map n ↔ ladder resolution only when you\n"
        "    choose a bridge (future work)."
    )


if __name__ == "__main__":
    main()
