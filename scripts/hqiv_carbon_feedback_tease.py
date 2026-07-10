#!/usr/bin/env python3
"""
Tease outside-contact / voltage feedback on the carbon allotrope fork.

Lean: ``Hqiv.QuantumChemistry.CarbonAllotropeFeedback``
  (plus OutsideContactLedger / VoltageGenerationLedger).

Proved identities applied here:
  * grapheneBondOrder = 4/3, diamondBondOrder = 1
  * grapheneCoordinationExcess = 1/4, diamond = 0
  * graphene localDefect dress = 21/20; diamond = 1
  * C–C preferred-axis / chemo / bulk@ξ₅ / mass-pin electro = 1
  * tribo at g=0 reduces to localDefect
  * condensed unstressed dress = em × localDefect (φ=0)

The mass-pin witness freezes every ledger channel at dilute / unstressed identity.
This script reopens those channels one at a time with carbon-natural stresses.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_allotrope_network as an
import hqiv_homogeneous_curvature_feedback as hcf
import hqiv_lean_physics_primitives as lean
import hqiv_molecular_spectroscopy as ms
import hqiv_nbody_second_order as nso
import hqiv_outside_contact_ledger as ocl
import hqiv_preferred_axis_dress as pad
import hqiv_voltage_generation_ledger as vgl
from hqiv_lab.crystal_geometry import (
    covalent_network_bond_length_angstrom,
    expected_contact_xi_for_crystal,
)

Z_C = 6
COMPARISON_R = {"graphene": 1.421, "diamond": 1.544}


@dataclass(frozen=True)
class CarbonMotif:
    name: str
    coordination: int
    label: str

    @property
    def bond_order(self) -> float:
        return an.network_bond_order(Z_C, self.coordination)

    @property
    def bond_angstrom(self) -> float:
        return covalent_network_bond_length_angstrom(
            Z_C, coordination=self.coordination, packed=False
        )

    @property
    def angle_deg(self) -> float | None:
        return an.network_bond_angle_deg(Z_C, self.coordination)


GRAPHENE = CarbonMotif("graphene", 3, "sp2 honeycomb")
DIAMOND = CarbonMotif("diamond", 4, "sp3 diamond-cubic")


def carbon_dielectric() -> dict[str, float]:
    n = ms.curvature_dielectric_ratio(Z_C, Z_C)
    return {
        "n_curvature_dielectric": n,
        "clausius_mossotti_s": ms.concentration_weight(n),
    }


def carbon_xi() -> float:
    return expected_contact_xi_for_crystal(
        crystal_kind="covalent_network", z_values=(Z_C,)
    )


def length_residual_fraction(motif: CarbonMotif) -> float:
    """|r_hqiv − r_lab| / r_lab — quarantine diagnostic, not a derivation input."""
    r_lab = COMPARISON_R[motif.name]
    return abs(motif.bond_angstrom - r_lab) / r_lab


def coordination_excess(motif: CarbonMotif, *, reference_k: float = 4.0) -> float:
    """
    Lean ``coordinationExcessVsReference`` / ``grapheneCoordinationExcess``.

    Diamond at k=4 is the reference (δ=0).  Graphene at k=3 carries
    δ = |4−3|/4 = 1/4 — a sheet is under-coordinated vs the sp³ network.
    """
    return abs(float(motif.coordination) - reference_k) / max(reference_k, 1.0)


def assert_lean_carbon_identities() -> None:
    """Guardrails matching ``CarbonAllotropeFeedback.lean`` (no fitted coeffs)."""
    assert abs(an.network_bond_order(Z_C, 3) - 4.0 / 3.0) < 1e-12
    assert abs(an.network_bond_order(Z_C, 4) - 1.0) < 1e-12
    assert abs(coordination_excess(GRAPHENE) - 0.25) < 1e-12
    assert abs(coordination_excess(DIAMOND) - 0.0) < 1e-12
    g_local = ocl.outside_local_channel(0.25)
    d_local = ocl.outside_local_channel(0.0)
    assert abs(g_local - 21.0 / 20.0) < 1e-12
    assert abs(d_local - 1.0) < 1e-12
    assert abs(pad.preferred_axis_spectral_gap([pad.bond_polarity(Z_C, Z_C)]) - 0.0) < 1e-12
    assert abs(carbon_xi() - 5.0) < 1e-12
    casimir = lean.curvature_budget_local_global_at_xi(carbon_xi())
    assert abs(casimir - 1.0) < 1e-12
    assert abs(ocl.outside_bulk_channel(casimir, 1.0) - 1.0) < 1e-12
    base = vgl.electro_contact_dress(
        ocl.dilute_gas_outside_contact_ledger(0.0, 1.0),
        vgl.unstressed_voltage_generation_ledger(),
    )
    assert abs(base - 1.0) < 1e-12
    assert abs(vgl.tribo_voltage_channel(0.0, 0.25) - g_local) < 1e-12
    assert abs(vgl.tribo_voltage_channel(0.0, 0.0) - 1.0) < 1e-12


def carbon_bulk_target() -> float:
    """Lean ``carbonBulkTarget`` = Casimir local/global at ξ_C (= 1)."""
    return lean.curvature_budget_local_global_at_xi(carbon_xi())


def baseline_ledger(*, geff_sum: float = 0.0, surplus: float = 1.0) -> ocl.OutsideContactLedger:
    return ocl.dilute_gas_outside_contact_ledger(geff_sum, surplus)


def channel_scan_for_motif(
    motif: CarbonMotif,
    *,
    strain: float = 0.02,
    photon_excess: float = 0.05,
    release_contrast: float = 0.05,
    phase_rate: float = 0.02,
    phi_epsilon: float = 1e-6,
    rho_bulk: float = 1.0,
) -> dict[str, Any]:
    """Open each feedback channel alone, then a combined condensed+driven pack."""
    xi = carbon_xi()
    diel = carbon_dielectric()
    n = diel["n_curvature_dielectric"]
    delta = coordination_excess(motif)
    g_axis = pad.preferred_axis_spectral_gap([pad.bond_polarity(Z_C, Z_C)])
    # Homogeneous network: no bond-summed G_eff participation in this tease
    geff_sum, surplus = 0.0, 1.0
    base_out = baseline_ledger(geff_sum=geff_sum, surplus=surplus)
    base_v = vgl.unstressed_voltage_generation_ledger()
    base_dress = vgl.electro_contact_dress(base_out, base_v)

    # Lean ``carbonBulkTarget``: Casimir local/global at ξ_C (=1), not κ(ξ) chart bulk.
    bulk_target = carbon_bulk_target()
    hyper = nso.graph_hyperclosure_weak(motif.coordination)

    def pack(
        name: str,
        outside: ocl.OutsideContactLedger,
        voltage: vgl.VoltageGenerationLedger,
        *,
        note: str,
    ) -> dict[str, Any]:
        dress = vgl.electro_contact_dress(outside, voltage)
        return {
            "channel": name,
            "note": note,
            "outside": outside.to_dict(),
            "voltage": voltage.to_dict(),
            "electro_contact_dress": dress,
            "dress_over_baseline": dress / base_dress,
            "preferred_axis_gap": g_axis,
            "graph_hyperclosure_weak": hyper,
            "full_optional_times_axis": dress * hyper,  # c2=vev=1 at lock; g=0
        }

    rows: list[dict[str, Any]] = []

    # --- frozen mass-pin baseline ---
    rows.append(
        pack(
            "baseline_dilute_unstressed",
            base_out,
            base_v,
            note="mass-pin assay: all environment + EMF channels at identity",
        )
    )

    # --- outside channels one at a time ---
    rows.append(
        pack(
            "em_only",
            ocl.outside_contact_ledger_from_channels(
                n_dielectric=n,
                geff_sum=geff_sum,
                surplus=surplus,
            ),
            base_v,
            note=f"C–C curvature dielectric n={n:.4f} opens em; bulk/local/grav stay 1",
        )
    )
    rows.append(
        pack(
            "bulk_only_rho1",
            ocl.outside_contact_ledger_from_channels(
                bulk_target=bulk_target,
                rho_bulk=rho_bulk,
                geff_sum=geff_sum,
                surplus=surplus,
            ),
            base_v,
            note=(
                f"ξ_C={xi:.1f} has Casimir B=1 (Lean carbonBulkTarget), "
                f"so bulk(ρ={rho_bulk}) stays identity"
            ),
        )
    )
    rows.append(
        pack(
            "localDefect_only",
            ocl.outside_contact_ledger_from_channels(
                coordination_excess=delta,
                geff_sum=geff_sum,
                surplus=surplus,
            ),
            base_v,
            note=(
                f"δ=|k−4|/4={delta:.4f} vs diamond reference; "
                f"excess={hcf.local_curvature_defect_excess(delta):.4f}"
            ),
        )
    )
    rows.append(
        pack(
            "grav_only_earth_eps",
            ocl.outside_contact_ledger_from_channels(
                phi_epsilon=phi_epsilon,
                geff_sum=geff_sum,
                surplus=surplus,
            ),
            base_v,
            note=f"Earth-scale φ_ε={phi_epsilon:g} — tiny Ricci/grav bump",
        )
    )

    # --- voltage channels one at a time ---
    rows.append(
        pack(
            "piezo_only",
            base_out,
            vgl.voltage_generation_ledger_from_stresses(
                strain_fraction=strain, n_dielectric=n
            ),
            note=f"strain={strain:.3f} × dielectric response (piezo)",
        )
    )
    rows.append(
        pack(
            "photo_only",
            base_out,
            vgl.voltage_generation_ledger_from_stresses(
                photon_phase_excess=photon_excess, n_dielectric=n
            ),
            note=f"photon-phase excess={photon_excess:.3f}",
        )
    )
    rows.append(
        pack(
            "thermo_only",
            base_out,
            vgl.voltage_generation_ledger_from_stresses(
                release_contrast=release_contrast
            ),
            note=f"ξ-release / ΔT contrast={release_contrast:.3f}",
        )
    )
    rows.append(
        pack(
            "faraday_only",
            base_out,
            vgl.voltage_generation_ledger_from_stresses(
                phase_rate_fraction=phase_rate
            ),
            note=f"phase-rate fraction={phase_rate:.3f}",
        )
    )
    rows.append(
        pack(
            "chemo_only",
            base_out,
            vgl.voltage_generation_ledger_from_stresses(ionic_asymmetry=0.0),
            note="homonuclear C–C ⇒ ionic asymmetry 0 ⇒ chemo identity",
        )
    )
    rows.append(
        pack(
            "tribo_only",
            base_out,
            vgl.voltage_generation_ledger_from_stresses(
                axis_gap=g_axis, coordination_excess=delta
            ),
            note="g=0 on C–C; tribo reduces to localDefect factor on the voltage side",
        )
    )

    # --- length residual as a diagnostic piezo stress (not a derivation pin) ---
    resid = length_residual_fraction(motif)
    rows.append(
        pack(
            "piezo_from_length_residual_diagnostic",
            base_out,
            vgl.voltage_generation_ledger_from_stresses(
                strain_fraction=resid, n_dielectric=n
            ),
            note=(
                f"quarantine |Δr|/r_lab={resid:.4f} fed as piezo stress — "
                "shows how large a strain-like feedback would need to be to hear "
                "the length residual; not an input to the solve"
            ),
        )
    )

    # --- combined: condensed sheet/crystal + mild drive ---
    combined_out = ocl.outside_contact_ledger_from_channels(
        phi_epsilon=phi_epsilon,
        n_dielectric=n,
        bulk_target=bulk_target,
        rho_bulk=rho_bulk,
        coordination_excess=delta,
        geff_sum=geff_sum,
        surplus=surplus,
    )
    combined_v = vgl.voltage_generation_ledger_from_stresses(
        strain_fraction=strain,
        photon_phase_excess=photon_excess,
        release_contrast=release_contrast,
        phase_rate_fraction=phase_rate,
        n_dielectric=n,
        axis_gap=g_axis,
        coordination_excess=delta,
    )
    rows.append(
        pack(
            "combined_condensed_plus_mild_drive",
            combined_out,
            combined_v,
            note=(
                "em + localDefect + tiny grav + piezo/photo/thermo/faraday/tribo; "
                "bulk still identity at ξ_C"
            ),
        )
    )

    return {
        "motif": motif.name,
        "label": motif.label,
        "coordination": motif.coordination,
        "bond_order": motif.bond_order,
        "bond_angstrom": motif.bond_angstrom,
        "bond_angle_deg": motif.angle_deg,
        "xi_contact": xi,
        "dielectric": diel,
        "coordination_excess_vs_diamond": delta,
        "length_residual_fraction_quarantine": resid,
        "baseline_electro_contact_dress": base_dress,
        "channels": rows,
    }


def fork_summary(g_row: dict[str, Any], d_row: dict[str, Any]) -> dict[str, Any]:
    """Compare graphene vs diamond channel-by-channel."""
    g_map = {c["channel"]: c for c in g_row["channels"]}
    d_map = {c["channel"]: c for c in d_row["channels"]}
    diffs = []
    for name in g_map:
        gd = g_map[name]["electro_contact_dress"]
        dd = d_map[name]["electro_contact_dress"]
        diffs.append(
            {
                "channel": name,
                "graphene_dress": gd,
                "diamond_dress": dd,
                "graphene_over_diamond": gd / dd if dd else None,
                "graphene_over_baseline": g_map[name]["dress_over_baseline"],
                "diamond_over_baseline": d_map[name]["dress_over_baseline"],
            }
        )
    return {
        "exact_shared": {
            "angle_graphene_deg": g_row["bond_angle_deg"],
            "angle_diamond_deg": d_row["bond_angle_deg"],
            "bond_order_graphene": g_row["bond_order"],
            "bond_order_diamond": d_row["bond_order"],
            "preferred_axis_gap_CC": 0.0,
            "chemo_CC": 1.0,
            "bulk_at_xi5": 1.0,
        },
        "channel_diffs": diffs,
        "lesson": (
            "Exact slots stay exact (angles, orders, g=0, chemo=1, bulk@ξ5=1). "
            "Feedback that actually moves the dress is em (shared), localDefect "
            "(graphene≠diamond), and stressed voltage routes. "
            "Mass pinning freezes all of these; reopening them is the coupling "
            "chemistry cannot see from mass+density alone."
        ),
    }


def build_payload(**stress_kw: float) -> dict[str, Any]:
    assert_lean_carbon_identities()
    g = channel_scan_for_motif(GRAPHENE, **stress_kw)
    d = channel_scan_for_motif(DIAMOND, **stress_kw)
    return {
        "source": "scripts/hqiv_carbon_feedback_tease.py",
        "parameter_policy": "no fitted coefficients; stresses are assay conditions",
        "input_policy": "CRC bond lengths only as quarantine residual diagnostics",
        "foundation": {
            "alpha": lean.ALPHA,
            "gamma": lean.GAMMA,
            "strong_channel_fraction": lean.STRONG_CHANNEL_FRACTION,
            "xi_carbon": carbon_xi(),
            "dielectric_CC": carbon_dielectric(),
        },
        "stress_defaults": {
            "strain": stress_kw.get("strain", 0.02),
            "photon_excess": stress_kw.get("photon_excess", 0.05),
            "release_contrast": stress_kw.get("release_contrast", 0.05),
            "phase_rate": stress_kw.get("phase_rate", 0.02),
            "phi_epsilon": stress_kw.get("phi_epsilon", 1e-6),
            "rho_bulk": stress_kw.get("rho_bulk", 1.0),
        },
        "graphene": g,
        "diamond": d,
        "fork": fork_summary(g, d),
    }


def print_report(payload: dict[str, Any]) -> None:
    print("=== Carbon feedback tease (reopen ledger channels) ===")
    f = payload["foundation"]
    print(
        f"ξ_C={f['xi_carbon']:.1f}  n_CC={f['dielectric_CC']['n_curvature_dielectric']:.4f}"
        f"  s={f['dielectric_CC']['clausius_mossotti_s']:.4f}"
        f"  α={f['alpha']} γ={f['gamma']} 4/8={f['strong_channel_fraction']}"
    )
    print()
    for key in ("graphene", "diamond"):
        row = payload[key]
        print(
            f"-- {row['motif']}  k={row['coordination']}  p={row['bond_order']:.4f}"
            f"  r={row['bond_angstrom']:.4f} Å  θ={row['bond_angle_deg']}"
            f"  δ={row['coordination_excess_vs_diamond']:.4f}"
        )
        for c in row["channels"]:
            if c["channel"] == "baseline_dilute_unstressed":
                continue
            # skip pure identities in the short print
            if abs(c["dress_over_baseline"] - 1.0) < 1e-12 and c["channel"] in {
                "chemo_only",
                "bulk_only_rho1",
                "grav_only_earth_eps",
            }:
                if c["channel"] == "bulk_only_rho1":
                    print(f"   {c['channel']:40s}  ×{c['dress_over_baseline']:.6f}  (identity — {c['note'][:60]})")
                continue
            print(
                f"   {c['channel']:40s}  ×{c['dress_over_baseline']:.6f}"
                f"  dress={c['electro_contact_dress']:.6f}"
            )
        print()

    print("fork: graphene / diamond dress ratios (channels that differ)")
    for d in payload["fork"]["channel_diffs"]:
        ratio = d["graphene_over_diamond"]
        if ratio is None or abs(ratio - 1.0) < 1e-12:
            continue
        print(
            f"   {d['channel']:40s}  gr/dia={ratio:.6f}"
            f"  (gr ×{d['graphene_over_baseline']:.4f}, dia ×{d['diamond_over_baseline']:.4f})"
        )
    print()
    print(payload["fork"]["lesson"])


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--strain", type=float, default=0.02)
    p.add_argument("--photon-excess", type=float, default=0.05)
    p.add_argument("--release-contrast", type=float, default=0.05)
    p.add_argument("--phase-rate", type=float, default=0.02)
    p.add_argument("--json-out", type=Path, default=None)
    args = p.parse_args()
    payload = build_payload(
        strain=args.strain,
        photon_excess=args.photon_excess,
        release_contrast=args.release_contrast,
        phase_rate=args.phase_rate,
    )
    print_report(payload)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"\nwrote {args.json_out}")


if __name__ == "__main__":
    main()
