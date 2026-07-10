#!/usr/bin/env python3
"""
Contact force / Hessian / discrete phonon / crystal spectral-gap readouts.

Lean:
  ``Hqiv.QuantumChemistry.PhaseElasticity``
    — contactForceFromLogDress, contactHessianNm, discretePhononWavenumberCm1
  ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``
    — crystalSpectralGap

Same matrix spine as molecular spectra: binding depth D and contact length r
already fix the Morse backbone k = 2D/r².  Force and phonon slots are
log-derivatives of that dress product; the crystal gap is the preferred-axis
spectral gap of contact polarities dressed by Clausius–Mossotti × ionic softener.

No fitted coefficients; NIST / handbook values are comparison-only.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_contact_force_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_contact_force_readout.py --json-out data/contact_force_hessian_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any, Sequence

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_allotrope_network as an
import hqiv_crystal_fracture_witness as cfw
import hqiv_dynamic_binding_chart as dbc
import hqiv_ionic_bond_network as ibn
import hqiv_lean_physics_primitives as lean
import hqiv_metallic_bond_network as mbn
import hqiv_molecular_spectroscopy as ms
import hqiv_preferred_axis_dress as pad
import hqiv_selection_weights as sw
import hqiv_voltage_generation_ledger as vgl
from hqiv_lab.crystal_geometry import (
    clausius_mossotti_optical_weight,
    covalent_network_em_packing_dress,
    ionic_is_hydride_pair,
)

EV_J = ms.EV_J
ANGSTROM_M = ms.ANGSTROM_M
AMU_KG = ms.AMU_KG
C_CM_S = ms.C_CM_S
STRONG = lean.STRONG_CHANNEL_FRACTION
MORSE_BACKBONE_LOG_LENGTH_DERIV = 2.0
RYDBERG_EV = 13.605693122994
BOHR_ANGSTROM = 0.529177210903

DEFAULT_JSON = _REPO_ROOT / "data" / "contact_force_hessian_audit.json"

# Quarantine-only handbook optical-gap / phonon scales (eV, cm⁻¹) — never inputs.
NIST_COMPARISON: dict[str, dict[str, float]] = {
    "NaCl": {"optical_gap_eV": 8.5, "omega_TO_cm1": 164.0},
    "LiF": {"optical_gap_eV": 13.6, "omega_TO_cm1": 307.0},
    "Si": {"optical_gap_eV": 1.12, "omega_TO_cm1": 520.0},
    "Cu": {"optical_gap_eV": 0.0, "omega_TO_cm1": 240.0},
}


def contact_force_from_log_dress(
    binding_ev: float,
    contact_dist_ang: float,
    log_deriv: float = MORSE_BACKBONE_LOG_LENGTH_DERIV,
) -> float:
    """Lean ``contactForceFromLogDress`` [N]."""
    if contact_dist_ang <= 0.0:
        return 0.0
    return (
        STRONG
        * (binding_ev * EV_J)
        / (contact_dist_ang * ANGSTROM_M)
        * abs(float(log_deriv))
    )


def contact_force_morse_backbone(binding_ev: float, contact_dist_ang: float) -> float:
    """Lean ``contactForceMorseBackbone``."""
    return contact_force_from_log_dress(
        binding_ev, contact_dist_ang, MORSE_BACKBONE_LOG_LENGTH_DERIV
    )


def contact_hessian_n_m(binding_ev: float, contact_dist_ang: float) -> float:
    """Lean ``contactHessianNm`` = length-scaled Morse k = 2D/r² [N/m]."""
    if contact_dist_ang <= 0.0:
        return 0.0
    r_m = contact_dist_ang * ANGSTROM_M
    return 2.0 * (binding_ev * EV_J) / (r_m * r_m)


def optical_phonon_hessian_softener(
    n_coord: float,
    *,
    hydride: bool = False,
    apply_softener: bool = True,
) -> float:
    """
    Lean ``opticalPhononHessianSoftener``:
    ``s = (4/8)·γ / max(CN_eff, 1)`` with ``CN_eff = 1`` for hydrides.

    Ionic / hydride optical TO slot; covalent / metallic pass ``apply_softener=False``.
    """
    if not apply_softener:
        return 1.0
    cn_eff = 1.0 if hydride else max(float(n_coord), 1.0)
    return STRONG * lean.GAMMA / cn_eff


def contact_hessian_optical_n_m(
    binding_ev: float,
    contact_dist_ang: float,
    *,
    n_coord: float = 6.0,
    hydride: bool = False,
    apply_softener: bool = True,
) -> float:
    """Lean ``contactHessianOpticalNm``."""
    return contact_hessian_n_m(binding_ev, contact_dist_ang) * optical_phonon_hessian_softener(
        n_coord, hydride=hydride, apply_softener=apply_softener
    )


def discrete_phonon_omega_rad(hessian_n_m: float, reduced_mass_amu: float) -> float:
    """Lean ``discretePhononOmegaRad`` [rad/s]."""
    if hessian_n_m <= 0.0 or reduced_mass_amu <= 0.0:
        return 0.0
    return math.sqrt(hessian_n_m / (reduced_mass_amu * AMU_KG))


def discrete_phonon_wavenumber_cm1(hessian_n_m: float, reduced_mass_amu: float) -> float:
    """Lean ``discretePhononWavenumberCm1`` — same SI bridge as molecular ωₑ."""
    omega = discrete_phonon_omega_rad(hessian_n_m, reduced_mass_amu)
    if omega <= 0.0:
        return 0.0
    return omega / (2.0 * math.pi * C_CM_S)


def crystal_spectral_gap(
    contact_polarities: Sequence[float],
    n_dielectric: float,
    ionic_character: float,
) -> float:
    """
    Lean ``crystalSpectralGap``:
    g · max(CM(n), 0) · ionicOpticalGapSoftener(δ²).
    """
    g = pad.preferred_axis_spectral_gap(list(contact_polarities))
    cm = max(clausius_mossotti_optical_weight(n_dielectric), 0.0)
    soft = vgl.ionic_optical_gap_softener(ionic_character)
    return g * cm * soft


def covalent_network_binding_ev(z: int, bond_ang: float, coordination: int = 4) -> float:
    """Characteristic network contact depth from allotrope geometry (no NIST pin)."""
    order = max(float(an.network_bond_order(z, coordination)), 1.0)
    return (
        order
        * RYDBERG_EV
        * lean.ALPHA
        * (1.0 + STRONG)
        / (1.0 + max(bond_ang, 1e-9) / BOHR_ANGSTROM)
    )


def readout_bundle(
    *,
    name: str,
    crystal_kind: str,
    binding_ev: float,
    contact_dist_ang: float,
    n_coord: float,
    z_i: int,
    z_j: int,
    n_dielectric: float,
    contact_polarities: Sequence[float] | None = None,
) -> dict[str, Any]:
    """Full force / Hessian / phonon / gap bundle for one contact."""
    ionic = sw.bond_ionic_character(z_i, z_j)
    pols = list(contact_polarities) if contact_polarities is not None else [
        pad.bond_polarity(z_i, z_j)
    ]
    # Metallic / homopolar networks: equal polarities → g = 0.
    if crystal_kind == "metallic":
        pols = [0.0] * max(int(n_coord), 1)
    elif crystal_kind == "covalent_network" and z_i == z_j:
        pols = [0.0] * max(int(n_coord), 1)

    force_n = contact_force_morse_backbone(binding_ev, contact_dist_ang)
    hess_raw = contact_hessian_n_m(binding_ev, contact_dist_ang)
    hydride = ionic_is_hydride_pair(z_i, z_j)
    # Optical / TO slot: lattice softener on ionic + hydride; identity on covalent/metal.
    apply_soft = crystal_kind == "ionic" or hydride
    soft = optical_phonon_hessian_softener(
        n_coord, hydride=hydride, apply_softener=apply_soft
    )
    hess = hess_raw * soft
    mu = ms.reduced_mass_amu(z_i, z_j)
    omega_cm1 = discrete_phonon_wavenumber_cm1(hess, mu)
    gap = crystal_spectral_gap(pols, n_dielectric, ionic)
    stiff = cfw.contact_binding_stiffness_pa(binding_ev, contact_dist_ang)

    row: dict[str, Any] = {
        "name": name,
        "crystal_kind": crystal_kind,
        "binding_ev_per_contact": binding_ev,
        "contact_dist_angstrom": contact_dist_ang,
        "coordination": n_coord,
        "z_i": z_i,
        "z_j": z_j,
        "reduced_mass_amu": mu,
        "bond_ionic_character": ionic,
        "n_dielectric": n_dielectric,
        "contact_polarities": pols,
        "preferred_axis_spectral_gap": pad.preferred_axis_spectral_gap(pols),
        "clausius_mossotti_weight": clausius_mossotti_optical_weight(n_dielectric),
        "ionic_optical_gap_softener": vgl.ionic_optical_gap_softener(ionic),
        "optical_phonon_hessian_softener": soft,
        "hydride_route": hydride,
        "contact_force_N": force_n,
        "contact_hessian_raw_N_m": hess_raw,
        "contact_hessian_N_m": hess,
        "discrete_phonon_cm1": omega_cm1,
        "crystal_spectral_gap": gap,
        "contact_binding_stiffness_Pa": stiff,
        "morse_backbone_log_length_deriv": MORSE_BACKBONE_LOG_LENGTH_DERIV,
        "strong_channel_fraction": STRONG,
    }
    ref = NIST_COMPARISON.get(name)
    if ref is not None:
        row["nist_comparison_quarantine"] = dict(ref)
        if ref.get("omega_TO_cm1", 0.0) > 0.0 and omega_cm1 > 0.0:
            row["phonon_comparison_ratio"] = omega_cm1 / ref["omega_TO_cm1"]
        row["optical_slot"] = gap
    return row


def ionic_row(salt: ibn.IonicSalt, n_dielectric: float) -> dict[str, Any]:
    bind = ibn.ionic_lattice_binding_ev_per_contact(
        salt.cation,
        salt.anion,
        distance_angstrom=salt.lattice_bond_angstrom,
    )
    return readout_bundle(
        name=salt.name,
        crystal_kind="ionic",
        binding_ev=bind,
        contact_dist_ang=salt.lattice_bond_angstrom,
        n_coord=float(salt.coordination),
        z_i=salt.cation.z_nuclear,
        z_j=salt.anion.z_nuclear,
        n_dielectric=n_dielectric,
        contact_polarities=[
            pad.bond_polarity(salt.cation.z_nuclear, salt.anion.z_nuclear)
        ],
    )


def metallic_row(lattice: mbn.MetallicLattice) -> dict[str, Any]:
    bind = mbn.metallic_lattice_binding_ev_per_contact(
        lattice.metal,
        distance_angstrom=lattice.nearest_neighbor_angstrom,
        coordination=lattice.coordination,
    )
    z = lattice.metal.z_nuclear
    return readout_bundle(
        name=lattice.name,
        crystal_kind="metallic",
        binding_ev=bind,
        contact_dist_ang=lattice.nearest_neighbor_angstrom,
        n_coord=float(lattice.coordination),
        z_i=z,
        z_j=z,
        n_dielectric=1.0,
    )


def covalent_row(z: int, name: str, n_dielectric: float) -> dict[str, Any]:
    dressed = covalent_network_em_packing_dress(z, coordination=4, em_feedback=True)
    r = float(dressed["bond_length_angstrom"])
    bind = covalent_network_binding_ev(z, r, coordination=4)
    return readout_bundle(
        name=name,
        crystal_kind="covalent_network",
        binding_ev=bind,
        contact_dist_ang=r,
        n_coord=4.0,
        z_i=z,
        z_j=z,
        n_dielectric=n_dielectric,
    )


def _benchmark_by_name(name: str) -> dbc.MoleculeBenchmark | None:
    for bench in dbc.ALL_MOLECULE_BENCHMARKS:
        if bench.name == name:
            return bench
    return None


def diatomic_gas_row(name: str) -> dict[str, Any] | None:
    """Gas-phase Morse force/phonon from the spectroscopy panel (same k spine)."""
    bench = _benchmark_by_name(name)
    if bench is None or len(bench.fragments) < 2:
        return None
    result = ms.evaluate_diatomic(bench)
    d_e = float(result.D_e_ev)
    r_e = float(result.r_e_angstrom)
    z_i = bench.fragments[0].z_nuclear
    z_j = bench.fragments[1].z_nuclear
    k = contact_hessian_n_m(d_e, r_e)
    mu = ms.reduced_mass_amu(z_i, z_j)
    ionic = sw.bond_ionic_character(z_i, z_j)
    pols = [pad.bond_polarity(z_i, z_j)]
    omega_phonon = discrete_phonon_wavenumber_cm1(k, mu)
    nist = ms.NIST_COMPARISON.get(name, {})
    return {
        "name": name,
        "crystal_kind": "gas_diatomic",
        "binding_ev_per_contact": d_e,
        "contact_dist_angstrom": r_e,
        "coordination": 1.0,
        "z_i": z_i,
        "z_j": z_j,
        "reduced_mass_amu": mu,
        "bond_ionic_character": ionic,
        "contact_force_N": contact_force_morse_backbone(d_e, r_e),
        "contact_hessian_N_m": k,
        "discrete_phonon_cm1": omega_phonon,
        "spectroscopy_omega_e_cm1": float(result.omega_e_cm1),
        "crystal_spectral_gap": crystal_spectral_gap(pols, 1.0, ionic),
        "preferred_axis_spectral_gap": pad.preferred_axis_spectral_gap(pols),
        "nist_omega_e_cm1": nist.get("omega_e"),
        "phonon_vs_omega_e_ratio": (
            omega_phonon / nist["omega_e"] if nist.get("omega_e", 0) > 0 else None
        ),
        "phonon_vs_spectroscopy_ratio": (
            omega_phonon / result.omega_e_cm1 if result.omega_e_cm1 > 0 else None
        ),
    }


def build_audit() -> dict[str, Any]:
    salts = [
        (ibn.NACL_SALT, 1.544),
        (ibn.LIF_SALT, 1.392),
        (ibn.NAF_SALT, 1.325),
        (ibn.KCL_SALT, 1.490),
    ]
    metals = [mbn.CU_LATTICE, mbn.AL_LATTICE, mbn.LI_LATTICE, mbn.NA_LATTICE]
    covalent = [(14, "Si", 3.42), (32, "Ge", 4.0)]
    gas = ["H2", "HF", "N2", "CO", "LiF", "NaCl"]

    crystal_rows = [ionic_row(s, n) for s, n in salts]
    crystal_rows.extend(metallic_row(m) for m in metals)
    for z, name, n in covalent:
        crystal_rows.append(covalent_row(z, name, n))

    gas_rows: list[dict[str, Any]] = []
    for name in gas:
        row = diatomic_gas_row(name)
        if row is not None:
            gas_rows.append(row)

    identity = {
        "force_zero_at_r0": contact_force_morse_backbone(1.0, 0.0) == 0.0,
        "hessian_zero_at_r0": contact_hessian_n_m(1.0, 0.0) == 0.0,
        "crystal_gap_nil": crystal_spectral_gap([], 1.5, 0.3) == 0.0,
        "crystal_gap_homopolar": crystal_spectral_gap([0.0, 0.0, 0.0], 3.42, 0.0)
        == 0.0,
        "crystal_gap_zero_ionic_softener": abs(vgl.ionic_optical_gap_softener(0.0) - 1.0)
        < 1e-15,
    }

    return {
        "source": "scripts/hqiv_contact_force_readout.py",
        "lean_modules": [
            "Hqiv.QuantumChemistry.PhaseElasticity",
            "Hqiv.QuantumChemistry.OutsideContactReducedDeltas",
        ],
        "formula": {
            "force_N": "strong · (D/r) · |∂log E/∂log r|  with |∂log E/∂log r|=2 (Morse)",
            "hessian_N_m": "2 D / r²  (lengthScaledForceConstant in SI)",
            "phonon_cm1": "√(k/μ) / (2π c)  — same bridge as molecular ωₑ",
            "crystal_spectral_gap": "g_axis · max(CM(n),0) · ionicOpticalGapSoftener(δ²)",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "crystal_rows": crystal_rows,
        "gas_diatomic_rows": gas_rows,
        "comparison_policy": "NIST/handbook optical-gap and phonon scales are quarantine only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json-out",
        type=Path,
        default=DEFAULT_JSON,
        help="Write audit JSON (default: data/contact_force_hessian_audit.json)",
    )
    args = parser.parse_args()
    payload = build_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_checks: {payload['all_identity_checks_pass']}")
    for row in payload["crystal_rows"]:
        print(
            f"  {row['name']:6} F={row['contact_force_N']:.3e} N  "
            f"k={row['contact_hessian_N_m']:.1f} N/m  "
            f"ω={row['discrete_phonon_cm1']:.1f} cm⁻¹  "
            f"gap={row['crystal_spectral_gap']:.4f}"
        )
    for row in payload["gas_diatomic_rows"]:
        print(
            f"  gas {row['name']:6} ω_phonon={row['discrete_phonon_cm1']:.1f}  "
            f"ω_e={row['spectroscopy_omega_e_cm1']:.1f}  "
            f"ratio_vs_spec={row.get('phonon_vs_spectroscopy_ratio')}"
        )


if __name__ == "__main__":
    main()
