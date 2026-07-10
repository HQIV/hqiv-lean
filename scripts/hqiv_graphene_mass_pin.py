#!/usr/bin/env python3
"""
Graphene / diamond carbon fork with mass as scale anchor + EM (BE) feedback.

Geometry (bond order, angle, bare length) is derived from Z=6 and coordination.
Carbon mass is an in-situ scale anchor for packing → density — not a freeze of
the outside ledger.  The electric / BE dress

  em = outsideEmChannel(n_CC)

feeds back into the contact length

  r_eff = r_bare · em^α    (α = 3/5)

so densities become mass × dressed packing (Lean ``contactLengthFromEmFeedback``,
``volumetricDensityWithEmFeedback``).  At em = 1 this recovers the frozen mass-pin.

Graphite 3D density is deliberately *not* claimed: the c-axis interlayer is a
second pin we do not inject here.

Comparison numbers (CRC/NIST bond lengths, handbook densities) are quarantine
only — they never enter the solve.

Lean anchors:
  Hqiv.QuantumChemistry.AllotropeNetwork
  Hqiv.QuantumChemistry.CrystalContactGeometry
  Hqiv.QuantumChemistry.OutsideContactReducedDeltas
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_allotrope_network as an
import hqiv_molecular_spectroscopy as ms
import hqiv_outside_contact_ledger as ocl
import hqiv_two_way_feedback_dynamics as twf
from hqiv_lab.crystal_geometry import (
    AVOGADRO,
    closed_atomic_mass_amu,
    covalent_network_em_packing_dress,
    diamond_cubic_density_g_cm3,
    diamond_cubic_lattice_parameter_angstrom,
)

Z_CARBON = 6


def carbon_em_dress() -> dict[str, float]:
    """Shared C–C electric / BE channel (Lean ``outsideEmChannel``)."""
    n = ms.curvature_dielectric_ratio(Z_CARBON, Z_CARBON)
    feedback = twf.em_feedback_from_dielectric(n)
    return {
        "n_curvature_dielectric": n,
        "clausius_mossotti_s": ms.concentration_weight(n),
        "em": feedback.em,
        "r_scale": feedback.length_scale,
        "rho_scale": feedback.volumetric_density_scale,
        "sigma_scale": feedback.areal_density_scale,
        "binding_inverse_length_scale": feedback.inverse_length_binding_scale,
        "stiffness_scale": feedback.stiffness_scale,
    }


def contact_length_from_em_feedback(r_bare: float, em: float) -> float:
    """Lean ``contactLengthFromEmFeedback``: r_eff = r_bare · em^α."""
    return twf.EmLengthFeedback(em).dress_length(r_bare)


def volumetric_density_em_feedback_factor(em: float) -> float:
    """Lean ``volumetricDensityEmFeedbackFactor``: (em^α)^(-3)."""
    return twf.EmLengthFeedback(em).volumetric_density_scale


def areal_density_em_feedback_factor(em: float) -> float:
    """Lean ``arealDensityEmFeedbackFactor``: (em^α)^(-2)."""
    return twf.EmLengthFeedback(em).areal_density_scale

# Quarantine comparisons — never used as inputs.
COMPARISON = {
    "graphene_bond_angstrom": 1.421,
    "graphene_lattice_a_angstrom": 2.46,
    "graphene_areal_density_mg_m2": 0.77,  # ~0.77 mg/m² ≈ 7.7e-7 kg/m²
    "diamond_bond_angstrom": 1.544,
    "diamond_density_g_cm3": 3.51,
    "diamond_lattice_a_angstrom": 3.567,
}


def carbon_mass_pin_amu(*, mode: str = "known_12") -> dict[str, Any]:
    """
    Single external pin options.

    ``known_12`` — inject the textbook carbon mass 12 amu (the pin the user asked for).
    ``derived``  — HQIV closed atomic mass from Z (no external mass table).
    """
    derived = float(closed_atomic_mass_amu(Z_CARBON))
    if mode == "derived":
        return {
            "mode": "derived",
            "mass_amu": derived,
            "pin_policy": "HQIV closed mass from Z; no external mass inject",
            "derived_amu": derived,
        }
    if mode == "known_12":
        return {
            "mode": "known_12",
            "mass_amu": 12.0,
            "pin_policy": "single external pin: carbon mass = 12 amu",
            "derived_amu": derived,
        }
    raise ValueError(f"unknown mass pin mode {mode!r}")


def honeycomb_lattice_a_angstrom(bond_angstrom: float) -> float:
    """Graphene lattice constant ``a = r · √3`` from nearest-neighbour bond length."""
    return float(bond_angstrom) * math.sqrt(3.0)


def honeycomb_unit_cell_area_ang2(bond_angstrom: float) -> float:
    """Primitive honeycomb cell area ``(√3/2) a²`` with ``a = r√3`` → ``(3√3/2) r²``."""
    a = honeycomb_lattice_a_angstrom(bond_angstrom)
    return 0.5 * math.sqrt(3.0) * a * a


def graphene_areal_density(
    mass_amu: float,
    bond_angstrom: float,
) -> dict[str, float]:
    """
    Two atoms per honeycomb primitive cell.

    Returns areal density in several unit systems for readability.
    """
    area_ang2 = honeycomb_unit_cell_area_ang2(bond_angstrom)
    area_cm2 = area_ang2 * 1e-16
    mass_g = 2.0 * mass_amu / AVOGADRO
    sigma_g_cm2 = mass_g / max(area_cm2, 1e-40)
    # 1 g/cm² = 10⁴ g/m² = 10⁷ mg/m² = 10 kg/m²
    sigma_mg_m2 = sigma_g_cm2 * 1e7
    sigma_kg_m2 = sigma_g_cm2 * 10.0
    # 1 nm² = 100 Å²; two atoms per primitive cell
    atoms_per_nm2 = 2.0 * 100.0 / max(area_ang2, 1e-30)
    return {
        "unit_cell_area_angstrom2": area_ang2,
        "atoms_per_cell": 2.0,
        "areal_density_g_cm2": sigma_g_cm2,
        "areal_density_kg_m2": sigma_kg_m2,
        "areal_density_mg_m2": sigma_mg_m2,
        "atoms_per_nm2": atoms_per_nm2,
    }


def carbon_allotrope_row(
    *,
    name: str,
    coordination: int,
    mass_amu: float,
    use_inert_core: bool = True,
    em_feedback: bool = True,
) -> dict[str, Any]:
    """One carbon network motif: geometry from Z,k; mass anchor; optional EM length feedback."""
    z = Z_CARBON
    order = an.network_bond_order(z, coordination)
    angle = an.network_bond_angle_deg(z, coordination)
    dress = covalent_network_em_packing_dress(
        z,
        coordination=coordination,
        packed=False,
        em_feedback=em_feedback,
    )
    r_bare = float(dress["bond_length_bare_angstrom"])
    r = float(dress["bond_length_angstrom"])
    if not use_inert_core:
        # Diagnostic: drop inert-core elongation, keep the same EM/open packing dress.
        r_bare = an.network_bond_length_angstrom(z, coordination)
        if em_feedback:
            em_info = carbon_em_dress()
            feedback = twf.EmLengthFeedback(em_info["em"])
            packing = float(dress["network_open_channel_packing_scale"] or 1.0)
            r = feedback.dress_length(r_bare) * packing
            dress = {
                **dress,
                "bond_length_bare_angstrom": r_bare,
                "bond_length_angstrom": r,
                "em_dress": em_info,
                "feedback_scales": feedback.to_dict(),
            }
        else:
            r = r_bare
            dress = {
                **dress,
                "bond_length_bare_angstrom": r_bare,
                "bond_length_angstrom": r,
                "network_open_channel_packing_scale": 1.0,
                "em_dress": {"em": 1.0, "note": "feedback off"},
                "feedback_scales": twf.EmLengthFeedback(1.0).to_dict(),
                "shell_projection": None,
            }
    row: dict[str, Any] = {
        "name": name,
        "Z": z,
        "coordination": coordination,
        "bond_order": order,
        "bond_angle_deg": angle,
        "bond_length_bare_angstrom": r_bare,
        "bond_length_angstrom": r,
        "em_feedback": em_feedback,
        "em_dress": dress["em_dress"] if em_feedback else {"em": 1.0, "note": "feedback off"},
        "feedback_scales": dress["feedback_scales"],
        "shell_projection": dress["shell_projection"],
        "network_open_channel_packing_scale": dress["network_open_channel_packing_scale"],
        "geometry_route": (
            "covalent_network_inert_core" if use_inert_core else "allotrope_network_bare"
        ),
        "mass_pin_amu": mass_amu,
    }

    if coordination == 3:
        a = honeycomb_lattice_a_angstrom(r)
        areal = graphene_areal_density(mass_amu, r)
        areal_frozen = graphene_areal_density(mass_amu, r_bare)
        row.update(
            {
                "motif": "honeycomb_sheet",
                "lattice_a_angstrom": a,
                **areal,
                "areal_density_frozen_mg_m2": areal_frozen["areal_density_mg_m2"],
                "volumetric_density_g_cm3": None,
                "note": (
                    "2D sheet: mass anchor × EM-dressed packing; "
                    "graphite c-axis needs a second pin"
                ),
            }
        )
        row["comparison_quarantine"] = {
            "bond_angstrom": COMPARISON["graphene_bond_angstrom"],
            "bond_error_pct": 100.0
            * (r - COMPARISON["graphene_bond_angstrom"])
            / COMPARISON["graphene_bond_angstrom"],
            "bond_error_pct_frozen": 100.0
            * (r_bare - COMPARISON["graphene_bond_angstrom"])
            / COMPARISON["graphene_bond_angstrom"],
            "lattice_a_angstrom": COMPARISON["graphene_lattice_a_angstrom"],
            "lattice_a_error_pct": 100.0
            * (a - COMPARISON["graphene_lattice_a_angstrom"])
            / COMPARISON["graphene_lattice_a_angstrom"],
            "areal_density_mg_m2": COMPARISON["graphene_areal_density_mg_m2"],
            "areal_density_error_pct": 100.0
            * (areal["areal_density_mg_m2"] - COMPARISON["graphene_areal_density_mg_m2"])
            / COMPARISON["graphene_areal_density_mg_m2"],
            "areal_density_error_pct_frozen": 100.0
            * (
                areal_frozen["areal_density_mg_m2"]
                - COMPARISON["graphene_areal_density_mg_m2"]
            )
            / COMPARISON["graphene_areal_density_mg_m2"],
        }
    elif coordination == 4:
        a = diamond_cubic_lattice_parameter_angstrom(r)
        rho = diamond_cubic_density_g_cm3(mass_amu, r)
        rho_frozen = diamond_cubic_density_g_cm3(mass_amu, r_bare)
        row.update(
            {
                "motif": "diamond_cubic",
                "lattice_a_angstrom": a,
                "volumetric_density_g_cm3": rho,
                "volumetric_density_frozen_g_cm3": rho_frozen,
                "areal_density_mg_m2": None,
                "note": (
                    "3D density from mass anchor × EM-dressed diamond-cubic packing"
                ),
            }
        )
        row["comparison_quarantine"] = {
            "bond_angstrom": COMPARISON["diamond_bond_angstrom"],
            "bond_error_pct": 100.0
            * (r - COMPARISON["diamond_bond_angstrom"])
            / COMPARISON["diamond_bond_angstrom"],
            "bond_error_pct_frozen": 100.0
            * (r_bare - COMPARISON["diamond_bond_angstrom"])
            / COMPARISON["diamond_bond_angstrom"],
            "lattice_a_angstrom": COMPARISON["diamond_lattice_a_angstrom"],
            "lattice_a_error_pct": 100.0
            * (a - COMPARISON["diamond_lattice_a_angstrom"])
            / COMPARISON["diamond_lattice_a_angstrom"],
            "density_g_cm3": COMPARISON["diamond_density_g_cm3"],
            "density_error_pct": 100.0
            * (rho - COMPARISON["diamond_density_g_cm3"])
            / COMPARISON["diamond_density_g_cm3"],
            "density_error_pct_frozen": 100.0
            * (rho_frozen - COMPARISON["diamond_density_g_cm3"])
            / COMPARISON["diamond_density_g_cm3"],
        }
    else:
        row["motif"] = f"coordination_{coordination}"
        row["note"] = "density packing not defined for this motif in this script"

    # Motif ledger keeps em open (not dilute freeze)
    em_dress = dress["em_dress"] if isinstance(dress.get("em_dress"), dict) else {}
    ledger = ocl.outside_contact_ledger_from_channels(
        n_dielectric=float(em_dress.get("n_curvature_dielectric", 1.0))
        if em_feedback
        else 1.0,
        geff_sum=0.0,
        surplus=1.0,
    )
    row["outside_contact_ledger"] = ledger.to_dict()
    return row


def build_payload(
    *,
    mass_mode: str = "known_12",
    use_inert_core: bool = True,
    em_feedback: bool = True,
) -> dict[str, Any]:
    pin = carbon_mass_pin_amu(mode=mass_mode)
    mass = pin["mass_amu"]
    em_info = carbon_em_dress()
    rows = [
        carbon_allotrope_row(
            name="graphene (sp2 honeycomb)",
            coordination=3,
            mass_amu=mass,
            use_inert_core=use_inert_core,
            em_feedback=em_feedback,
        ),
        carbon_allotrope_row(
            name="diamond (sp3)",
            coordination=4,
            mass_amu=mass,
            use_inert_core=use_inert_core,
            em_feedback=em_feedback,
        ),
        carbon_allotrope_row(
            name="carbyne (sp)",
            coordination=2,
            mass_amu=mass,
            use_inert_core=use_inert_core,
            em_feedback=em_feedback,
        ),
    ]
    graphene = rows[0]
    diamond = rows[1]
    fork = {
        "angle_graphene_deg": graphene.get("bond_angle_deg"),
        "angle_diamond_deg": diamond.get("bond_angle_deg"),
        "bond_order_graphene": graphene["bond_order"],
        "bond_order_diamond": diamond["bond_order"],
        "bond_length_ratio_graphene_over_diamond": (
            graphene["bond_length_angstrom"] / diamond["bond_length_angstrom"]
        ),
        "density_observable": {
            "graphene_areal_mg_m2": graphene.get("areal_density_mg_m2"),
            "diamond_volumetric_g_cm3": diamond.get("volumetric_density_g_cm3"),
            "graphene_areal_frozen_mg_m2": graphene.get("areal_density_frozen_mg_m2"),
            "diamond_volumetric_frozen_g_cm3": diamond.get(
                "volumetric_density_frozen_g_cm3"
            ),
        },
        "em_feedback": {
            **em_info,
            "enabled": em_feedback,
            "r_scale": em_info["r_scale"] if em_feedback else 1.0,
            "rho_scale": em_info["rho_scale"] if em_feedback else 1.0,
            "sigma_scale": em_info["sigma_scale"] if em_feedback else 1.0,
            "binding_inverse_length_scale": (
                em_info["binding_inverse_length_scale"] if em_feedback else 1.0
            ),
            "stiffness_scale": em_info["stiffness_scale"] if em_feedback else 1.0,
        },
        "claim": (
            "Mass is an in-situ scale anchor; EM/BE dress feeds back into contact "
            "length as r → r·em^α·(1 + base·open²), so densities are mass × "
            "shell-dressed packing. Angles/orders stay exact; shared em cancels "
            "in the graphene/diamond length ratio while open-channel packing "
            "remains motif-local."
        ),
    }
    return {
        "source": "scripts/hqiv_graphene_mass_pin.py",
        "parameter_policy": (
            "mass = scale anchor; em = outsideEmChannel(n_CC) length feedback; "
            "geometry from Z,k"
        ),
        "input_policy": "CRC/NIST lengths and handbook densities are comparison quarantine",
        "mass_pin": pin,
        "use_inert_core_elongation": use_inert_core,
        "em_feedback_enabled": em_feedback,
        "fork": fork,
        "rows": rows,
    }


def _fmt_pct(x: float | None) -> str:
    if x is None:
        return "—"
    return f"{x:+.2f}%"


def print_report(payload: dict[str, Any]) -> None:
    pin = payload["mass_pin"]
    emf = payload["fork"]["em_feedback"]
    print("=== Carbon mass anchor + EM/BE feedback (graphene ↔ diamond) ===")
    print(f"pin: {pin['pin_policy']}")
    print(
        f"mass = {pin['mass_amu']:.6f} amu"
        + (f"  (HQIV derived {pin['derived_amu']:.6f})" if pin["mode"] == "known_12" else "")
    )
    print(
        f"EM feedback: {'ON' if payload['em_feedback_enabled'] else 'OFF'}"
        f"  em={emf['em']:.4f}  r×={emf['r_scale']:.4f}"
        f"  ρ×={emf['rho_scale']:.4f}  σ×={emf['sigma_scale']:.4f}"
    )
    print(f"inert-core elongation: {payload['use_inert_core_elongation']}")
    print()
    for row in payload["rows"]:
        if row["coordination"] not in (3, 4):
            continue
        print(f"-- {row['name']}  (k={row['coordination']}, p={row['bond_order']:.4f})")
        print(
            f"   r_bare = {row['bond_length_bare_angstrom']:.4f} Å"
            f"   r_eff = {row['bond_length_angstrom']:.4f} Å"
            f"   θ = {row.get('bond_angle_deg')}"
        )
        cq = row.get("comparison_quarantine") or {}
        if row["coordination"] == 3:
            print(
                f"   σ = {row['areal_density_mg_m2']:.4f} mg/m²"
                f"   (frozen {row.get('areal_density_frozen_mg_m2'):.4f})"
            )
            print(
                f"   quarantine Δr {_fmt_pct(cq.get('bond_error_pct'))}"
                f"  (frozen {_fmt_pct(cq.get('bond_error_pct_frozen'))})"
                f"  Δσ {_fmt_pct(cq.get('areal_density_error_pct'))}"
                f"  (frozen {_fmt_pct(cq.get('areal_density_error_pct_frozen'))})"
            )
        else:
            print(
                f"   ρ = {row['volumetric_density_g_cm3']:.4f} g/cm³"
                f"   (frozen {row.get('volumetric_density_frozen_g_cm3'):.4f})"
            )
            print(
                f"   quarantine Δr {_fmt_pct(cq.get('bond_error_pct'))}"
                f"  (frozen {_fmt_pct(cq.get('bond_error_pct_frozen'))})"
                f"  Δρ {_fmt_pct(cq.get('density_error_pct'))}"
                f"  (frozen {_fmt_pct(cq.get('density_error_pct_frozen'))})"
            )
        print()
    fork = payload["fork"]
    print("fork summary:")
    print(
        f"  θ graphene/diamond = {fork['angle_graphene_deg']:.4f}°"
        f" / {fork['angle_diamond_deg']:.4f}°"
    )
    print(
        f"  r_graphene / r_diamond = {fork['bond_length_ratio_graphene_over_diamond']:.4f}"
    )
    print(
        f"  σ_graphene = {fork['density_observable']['graphene_areal_mg_m2']:.4f} mg/m²"
        f"   ρ_diamond = {fork['density_observable']['diamond_volumetric_g_cm3']:.4f} g/cm³"
    )
    print(f"  {fork['claim']}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mass-mode",
        choices=("known_12", "derived"),
        default="known_12",
        help="carbon mass pin: textbook 12 amu (default) or HQIV derived closed mass",
    )
    parser.add_argument(
        "--bare",
        action="store_true",
        help="skip covalent-network inert-core elongation (allotrope bare length)",
    )
    parser.add_argument(
        "--no-em-feedback",
        action="store_true",
        help="freeze EM channel (old mass-pin-only behaviour)",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="optional JSON witness path",
    )
    args = parser.parse_args()
    payload = build_payload(
        mass_mode=args.mass_mode,
        use_inert_core=not args.bare,
        em_feedback=not args.no_em_feedback,
    )
    print_report(payload)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"\nwrote {args.json_out}")


if __name__ == "__main__":
    main()
