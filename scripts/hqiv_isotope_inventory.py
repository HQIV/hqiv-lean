#!/usr/bin/env python3
"""
Lean-backed isotope inventory for HQIV chemistry scaffolding (s and p Gaussian scales).

**Lean references** (authoritative definitions; this script mirrors the *formulas*, not Lean extraction):

  • ``Hqiv/Physics/BoundStates.lean`` — ``alphaEffAtShell``, ``expectedGroundEnergyAtShell``
  • ``Hqiv/Geometry/AuxiliaryField.lean`` — ``phi_of_shell`` (φ(m) = 2(m+1))
  • ``Hqiv/Geometry/OctonionicLightCone.lean`` — ``alpha = 3/5``, bare ``1/α_GUT = 42``

**Reduced mass** μ (atomic units, m_e = 1): μ = M / (M + 1) with M = m_nucleus / m_e.
  Masses are CODATA/NIST-style constants (isotope labels → M), not PDG particle tables.

**s-type GTO** (unnormalized ``exp(-α r²)`` width): α_s ~ 1 / (2 a₀²) with a₀ = 1/(μ Z) for a
standard Coulomb length, and the same variance match on a₀^HQIV = 1/(μ Z α_eff(m)) for the
shell-modulated HQIV length (see ``hqiv_isotope_hydrogenic_scales.py``).

**p-type GTO** (Cartesian radial factor ``x, y, or z`` times the same Gaussian): we attach a
**hydrogenic length ratio** between the first ℓ=1 shell (n=2, 2p) and the 1s Coulomb
expectation radii in the *same* μ, Z scaled Bohr system:

    ⟨r⟩_{1s} / a_B = 3/2 ,   ⟨r⟩_{2p} / a_B = 5/2   ⇒   ⟨r⟩_{2p} / ⟨r⟩_{1s} = 5/3

with a_B = 1/(μ Z) in atomic units. We set a characteristic p scale
``a_p = (5/3) * a₀`` and use α_p ~ 1/(2 a_p²) parallel to the s convention. The same ratio is
applied to a₀^HQIV when emitting HQIV-tagged p widths (geometric factor only; ℓ enters through
this ratio, not through a separate Lean def).

Outputs: human table by default, optional ``--json`` for machine-readable inventory.

Usage:
  python3 scripts/hqiv_isotope_inventory.py
  python3 scripts/hqiv_isotope_inventory.py --json
  python3 scripts/hqiv_isotope_inventory.py --shells 0,1,4 --isotopes ¹H,²H,⁴He
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

# Reuse hydrogenic kernel + hydrogen isotope masses
sys.path.insert(0, str(Path(__file__).resolve().parent))
import hqiv_isotope_hydrogenic_scales as hs  # noqa: E402

# ---------------------------------------------------------------------------
# Optional isotope table (extend as needed). Masses: m_nucleus / m_e (approximate CODATA).


@dataclass(frozen=True)
class IsotopeSpec:
    symbol: str
    z: int
    a: int
    m_nucleus_over_me: float
    note: str = ""


# fmt: off
DEFAULT_ISOTOPES: tuple[IsotopeSpec, ...] = (
    IsotopeSpec("¹H",   1, 1, 1836.15267343, "proton mass"),
    IsotopeSpec("²H",   1, 2, 3670.4829652, "deuteron"),
    IsotopeSpec("³H",   1, 3, 5496.92129, "triton"),
    IsotopeSpec("³He",  2, 3, 5497.884890, "helion"),
    IsotopeSpec("⁴He",  2, 4, 7294.29954142, "α particle"),
    IsotopeSpec("⁶Li",  3, 6, 10989.159, "approx nucleus"),
    IsotopeSpec("⁷Li",  3, 7, 12752.16, "approx nucleus"),
)
# fmt: on

# Hydrogenic ⟨r⟩_{2p} / ⟨r⟩_{1s} for same Z, μ (Coulomb, nonrelativistic).
P_TO_S_LENGTH_RATIO_2P_1S = 5.0 / 3.0

LEAN_MODULE_REFS = (
    "Hqiv/Physics/BoundStates.lean",
    "Hqiv/Geometry/AuxiliaryField.lean",
    "Hqiv/Geometry/OctonionicLightCone.lean",
)


@dataclass(frozen=True)
class InventoryEntry:
    symbol: str
    z: int
    a: int
    m_shell: int
    phi_m: float
    alpha_eff: float
    one_over_alpha_eff: float
    mu: float
    e0_bohr_hartree: float
    e0_hqiv_hartree: float
    a0_standard_au: float
    gto_alpha_s_standard: float
    a0_hqiv_au: float
    gto_alpha_s_hqiv: float
    p_length_ratio_hydrogenic_2p_over_1s: float
    a_p_standard_au: float
    gto_alpha_p_standard: float
    a_p_hqiv_au: float
    gto_alpha_p_hqiv: float


def reduced_mass_au(m_over_me: float) -> float:
    return hs.reduced_mass_au(m_over_me)


def build_entry(spec: IsotopeSpec, m_shell: int, c: float = 1.0) -> InventoryEntry:
    mu = reduced_mass_au(spec.m_nucleus_over_me)
    z = spec.z
    phi_m = hs.phi_of_shell(m_shell)
    ae = hs.alpha_eff_at_shell(m_shell, c)
    inv = hs.one_over_alpha_eff_at_shell(m_shell, c)
    e_bohr = -mu * float(z * z) / 2.0
    e_hqiv = hs.expected_ground_energy_at_shell(m_shell, z, mu, c)
    a0_std = hs.bohr_radius_standard_au(z, mu)
    ga_s_std = hs.s_gaussian_exponent_from_length(a0_std)
    a0_hq = hs.effective_bohr_radius_hqiv_au(m_shell, z, mu, c)
    ga_s_hq = hs.s_gaussian_exponent_from_length(a0_hq)

    r_ps = P_TO_S_LENGTH_RATIO_2P_1S
    a_p_std = r_ps * a0_std
    a_p_hq = r_ps * a0_hq
    ga_p_std = hs.s_gaussian_exponent_from_length(a_p_std)
    ga_p_hq = hs.s_gaussian_exponent_from_length(a_p_hq)

    return InventoryEntry(
        symbol=spec.symbol,
        z=z,
        a=spec.a,
        m_shell=m_shell,
        phi_m=phi_m,
        alpha_eff=ae,
        one_over_alpha_eff=inv,
        mu=mu,
        e0_bohr_hartree=e_bohr,
        e0_hqiv_hartree=e_hqiv,
        a0_standard_au=a0_std,
        gto_alpha_s_standard=ga_s_std,
        a0_hqiv_au=a0_hq,
        gto_alpha_s_hqiv=ga_s_hq,
        p_length_ratio_hydrogenic_2p_over_1s=r_ps,
        a_p_standard_au=a_p_std,
        gto_alpha_p_standard=ga_p_std,
        a_p_hqiv_au=a_p_hq,
        gto_alpha_p_hqiv=ga_p_hq,
    )


def run_inventory(
    shells: tuple[int, ...],
    isotope_filter: set[str] | None,
    c: float,
) -> list[InventoryEntry]:
    specs = DEFAULT_ISOTOPES
    if isotope_filter is not None:
        specs = tuple(s for s in specs if s.symbol in isotope_filter)
        missing = isotope_filter - {s.symbol for s in specs}
        if missing:
            raise ValueError(f"Unknown isotope symbols: {sorted(missing)}")
    out: list[InventoryEntry] = []
    for spec in specs:
        for m in shells:
            out.append(build_entry(spec, m, c=c))
    return out


def print_table(entries: list[InventoryEntry]) -> None:
    print("HQIV isotope inventory (Lean formula mirror; see module docstring)")
    print("Lean modules:", ", ".join(LEAN_MODULE_REFS))
    print(f"α_lattice = {hs.ALPHA_HQIV}  1/α_GUT bare = {hs.ONE_OVER_ALPHA_BARE}")
    print()
    for m in sorted({e.m_shell for e in entries}):
        sub = [e for e in entries if e.m_shell == m]
        print(f"=== shell m = {m}  (φ(m) = {hs.phi_of_shell(m):.6g}) ===")
        for e in sub:
            print(
                f"{e.symbol}  Z={e.z} A={e.a}  μ={e.mu:.9f}  "
                f"α_eff={e.alpha_eff:.10f}  E0(Bohr)={e.e0_bohr_hartree:.8f} Ha  "
                f"E0(HQIV)={e.e0_hqiv_hartree:.6e} Ha"
            )
            print(
                f"      s: a0(std)={e.a0_standard_au:.6f}  α_GTO(s,std)={e.gto_alpha_s_standard:.8f}  "
                f"|  a0(HQIV)={e.a0_hqiv_au:.6f}  α_GTO(s,HQIV)={e.gto_alpha_s_hqiv:.8f}"
            )
            print(
                f"      p: ratio ⟨r⟩_2p/⟨r⟩_1s = {e.p_length_ratio_hydrogenic_2p_over_1s:.6f}  "
                f"a_p(std)={e.a_p_standard_au:.6f}  α_GTO(p,std)={e.gto_alpha_p_standard:.8f}  "
                f"a_p(HQIV)={e.a_p_hqiv_au:.6f}  α_GTO(p,HQIV)={e.gto_alpha_p_hqiv:.8f}"
            )
        print()


def main() -> None:
    ap = argparse.ArgumentParser(description="Lean-backed isotope inventory (s + p GTO scales).")
    ap.add_argument(
        "--shells",
        type=str,
        default="0,1,4",
        help="Comma-separated shell indices m (default: 0,1,4)",
    )
    ap.add_argument(
        "--isotopes",
        type=str,
        default="",
        help="Comma-separated isotope symbols to include (default: all built-in)",
    )
    ap.add_argument("--c", type=float, default=1.0, help="Shell ladder constant c (Lean default 1).")
    ap.add_argument("--json", action="store_true", help="Emit JSON instead of a text table.")
    args = ap.parse_args()

    shells = tuple(int(x.strip()) for x in args.shells.split(",") if x.strip())
    if not shells:
        raise SystemExit("No shells given.")
    iso_set: set[str] | None = None
    if args.isotopes.strip():
        iso_set = {x.strip() for x in args.isotopes.split(",") if x.strip()}

    entries = run_inventory(shells, iso_set, c=args.c)
    if args.json:
        payload = {
            "lean_module_refs": list(LEAN_MODULE_REFS),
            "alpha_hqiv": hs.ALPHA_HQIV,
            "one_over_alpha_bare": hs.ONE_OVER_ALPHA_BARE,
            "p_length_note": (
                "a_p = (5/3) * a0 from hydrogenic <r>_{2p}/<r>_{1s}; "
                "α_GTO = 1/(2 a_p^2) same convention as s."
            ),
            "entries": [asdict(e) for e in entries],
        }
        print(json.dumps(payload, indent=2))
    else:
        print_table(entries)


if __name__ == "__main__":
    main()
