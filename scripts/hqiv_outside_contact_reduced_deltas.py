#!/usr/bin/env python3
"""
Reduced outside-contact deltas.

Lean: ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas``

Bookkeeping collapse for condensed / interface assays:

  M_out = A_ambient · W_wall · Δ_motif

* Shared ambient — gravity φ and bulk ρ are lab-scale, same for every motif.
* Dry-wall spectrum — wall / substrate is preferred-axis gap (or explicit wall
  excess) of the *wall*, not a per-molecule fit.
* Motif-local deltas — the small residual set: em (or spectroscopy pin s*),
  network coordination excess, bond-summed contact surplus.

Gravity need not be quarantined motif-by-motif; wall is one spectrum; comparisons
reduce to Δ_motif ratios.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_lean_physics_primitives as lean
import hqiv_molecular_spectroscopy as ms
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_outside_contact_ledger as ocl
import hqiv_preferred_axis_dress as pad
import hqiv_voltage_generation_ledger as vgl

STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA


@dataclass(frozen=True)
class SharedAmbient:
    """Lean ``SharedAmbient``."""

    phi_epsilon: float = 0.0
    bulk_target: float = 1.0
    rho_bulk: float = 0.0

    @property
    def dress(self) -> float:
        """Lean ``sharedAmbientDress``."""
        return notd.outside_gravity_geff_modulator(self.phi_epsilon) * ocl.outside_bulk_channel(
            self.bulk_target, self.rho_bulk
        )


@dataclass(frozen=True)
class DryWallSpectrum:
    """Lean ``DryWallSpectrum``."""

    wall_polarities: tuple[float, ...] = ()
    wall_coordination_excess: float = 0.0

    @property
    def spectral_gap(self) -> float:
        """Lean ``dryWallSpectralGap``."""
        return pad.preferred_axis_spectral_gap(list(self.wall_polarities))

    @property
    def defect_stress(self) -> float:
        """Lean ``dryWallDefectStress``."""
        return max(self.wall_coordination_excess, self.spectral_gap)

    @property
    def dress(self) -> float:
        """Lean ``dryWallDress``."""
        return ocl.outside_local_channel(self.defect_stress)


@dataclass(frozen=True)
class MotifLocalDelta:
    """Lean ``MotifLocalDelta`` — the small residual set."""

    n_dielectric: float = 1.0
    coordination_excess: float = 0.0
    geff_sum: float = 0.0
    surplus: float = 1.0

    @property
    def dress(self) -> float:
        """Lean ``motifLocalDress``."""
        return (
            ocl.outside_em_channel(self.n_dielectric)
            * ocl.outside_local_channel(self.coordination_excess)
            * ocl.outside_contact_channel(self.geff_sum, self.surplus)
        )


DILUTE_AMBIENT = SharedAmbient()
PRISTINE_WALL = DryWallSpectrum()
DILUTE_MOTIF = MotifLocalDelta()


def dry_wall_tribo_channel(wall: DryWallSpectrum) -> float:
    """Lean ``dryWallTriboChannel``."""
    return vgl.tribo_voltage_channel(wall.spectral_gap, wall.defect_stress)


def reduced_outside_dress(
    ambient: SharedAmbient,
    wall: DryWallSpectrum,
    motif: MotifLocalDelta,
) -> float:
    """Lean ``reducedOutsideDress``."""
    return ambient.dress * wall.dress * motif.dress


def outside_ledger_from_reduced(
    ambient: SharedAmbient,
    wall: DryWallSpectrum,
    motif: MotifLocalDelta,
) -> ocl.OutsideContactLedger:
    """Lean ``outsideContactLedgerFromReduced``."""
    return ocl.OutsideContactLedger(
        grav=notd.outside_gravity_geff_modulator(ambient.phi_epsilon),
        em=ocl.outside_em_channel(motif.n_dielectric),
        bulk=ocl.outside_bulk_channel(ambient.bulk_target, ambient.rho_bulk),
        local_defect=ocl.outside_local_channel(
            wall.defect_stress + motif.coordination_excess
        ),
        contact=ocl.outside_contact_channel(motif.geff_sum, motif.surplus),
    )


def spectral_concentration_weight(
    omega_pin: float,
    omega_diffuse: float,
    omega_concentrated: float,
) -> float:
    """Lean ``spectralConcentrationWeight`` — invert A=ω* inside the bracket."""
    if omega_diffuse <= 0.0 or omega_concentrated <= omega_diffuse:
        return 0.0
    ratio_pin = max(omega_pin / omega_diffuse, 1e-30)
    ratio_br = max(omega_concentrated / omega_diffuse, 1e-30)
    s = math.log(ratio_pin) / math.log(ratio_br)
    return max(0.0, min(1.0, s))


def outside_em_from_concentration_weight(s: float) -> float:
    """Lean ``outsideEmFromConcentrationWeight``."""
    return 1.0 + STRONG * max(0.0, min(1.0, s))


def motif_dress_from_spectral_weight(
    s: float,
    delta: float,
    geff_sum: float = 0.0,
    surplus: float = 1.0,
) -> float:
    """Lean ``motifLocalDressFromSpectralWeight``."""
    return (
        outside_em_from_concentration_weight(s)
        * ocl.outside_local_channel(delta)
        * ocl.outside_contact_channel(geff_sum, surplus)
    )


def carbon_motif_deltas(*, n_dielectric: float | None = None) -> dict[str, MotifLocalDelta]:
    """Graphene / diamond motif-local deltas (shared ambient & wall cancel in ratios)."""
    n = (
        ms.curvature_dielectric_ratio(6, 6)
        if n_dielectric is None
        else float(n_dielectric)
    )
    return {
        "graphene": MotifLocalDelta(n_dielectric=n, coordination_excess=0.25),
        "diamond": MotifLocalDelta(n_dielectric=n, coordination_excess=0.0),
    }


def demo_payload(
    *,
    phi_epsilon: float = 0.0,
    rho_bulk: float = 1.0,
    wall_excess: float = 0.0,
    wall_polarities: Sequence[float] = (),
) -> dict[str, Any]:
    # Casimir bulk target at ξ=5 is 1 (Lean carbonBulkTarget)
    ambient = SharedAmbient(
        phi_epsilon=phi_epsilon,
        bulk_target=lean.curvature_budget_local_global_at_xi(5.0),
        rho_bulk=rho_bulk,
    )
    wall = DryWallSpectrum(
        wall_polarities=tuple(float(p) for p in wall_polarities),
        wall_coordination_excess=wall_excess,
    )
    motifs = carbon_motif_deltas()
    rows = []
    for name, motif in motifs.items():
        red = reduced_outside_dress(ambient, wall, motif)
        ledger = outside_ledger_from_reduced(ambient, wall, motif)
        rows.append(
            {
                "motif": name,
                "motif_local": asdict(motif) | {"dress": motif.dress},
                "reduced_outside_dress": red,
                "ledger": ledger.to_dict(),
                "electro_unstressed": vgl.electro_contact_dress(
                    ledger, vgl.unstressed_voltage_generation_ledger()
                ),
            }
        )
    g, d = rows[0], rows[1]
    return {
        "source": "scripts/hqiv_outside_contact_reduced_deltas.py",
        "lean_module": "Hqiv.QuantumChemistry.OutsideContactReducedDeltas",
        "policy": (
            "Gravity/bulk shared; wall = dry-wall spectrum; "
            "motif deltas = em × network δ × contact only"
        ),
        "ambient": asdict(ambient) | {"dress": ambient.dress},
        "wall": {
            "wall_polarities": list(wall.wall_polarities),
            "wall_coordination_excess": wall.wall_coordination_excess,
            "spectral_gap": wall.spectral_gap,
            "defect_stress": wall.defect_stress,
            "dress": wall.dress,
        },
        "rows": rows,
        "fork": {
            "graphene_over_diamond_reduced": g["reduced_outside_dress"]
            / d["reduced_outside_dress"],
            "graphene_over_diamond_motif_only": g["motif_local"]["dress"]
            / d["motif_local"]["dress"],
            "expected_lean_ratio": 21.0 / 20.0,
            "ambient_cancels": abs(ambient.dress) > 0,
            "wall_cancels": abs(wall.dress) > 0,
            "lesson": (
                "Shared ambient and dry-wall factor out of the graphene/diamond "
                "ratio; only motif-local δ = 1/4 remains (21/20)."
            ),
        },
        "identities": {
            "dilute_pristine": reduced_outside_dress(
                DILUTE_AMBIENT, PRISTINE_WALL, DILUTE_MOTIF
            ),
            "unit_wall_dress": DryWallSpectrum(wall_coordination_excess=1.0).dress,
            "unit_wall_expected": 1.0 + GAMMA * STRONG,
        },
    }


def print_report(payload: dict[str, Any]) -> None:
    print("=== Reduced outside-contact deltas ===")
    print(f"policy: {payload['policy']}")
    a = payload["ambient"]
    w = payload["wall"]
    print(
        f"ambient: φ={a['phi_epsilon']:g} ρ={a['rho_bulk']:g}  dress={a['dress']:.6f}"
    )
    print(
        f"wall: δ={w['wall_coordination_excess']:g} g={w['spectral_gap']:.4f}"
        f"  dress={w['dress']:.6f}"
    )
    print()
    for row in payload["rows"]:
        m = row["motif_local"]
        print(
            f"-- {row['motif']:8s}  em×δ×contact={m['dress']:.6f}"
            f"  reduced={row['reduced_outside_dress']:.6f}"
            f"  (δ={m['coordination_excess']})"
        )
    f = payload["fork"]
    print()
    print(
        f"fork ratio reduced={f['graphene_over_diamond_reduced']:.6f}"
        f"  motif-only={f['graphene_over_diamond_motif_only']:.6f}"
        f"  Lean 21/20={f['expected_lean_ratio']:.6f}"
    )
    print(f"  {f['lesson']}")
    ids = payload["identities"]
    print(
        f"guards: dilute×pristine={ids['dilute_pristine']:.6f}"
        f"  unit-wall={ids['unit_wall_dress']:.6f}"
        f" (expect {ids['unit_wall_expected']:.6f})"
    )


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--phi", type=float, default=0.0)
    p.add_argument("--rho", type=float, default=1.0)
    p.add_argument("--wall-excess", type=float, default=0.0)
    p.add_argument(
        "--wall-polarities",
        type=float,
        nargs="*",
        default=[],
        help="dry-wall polarity spectrum (preferred-axis gap)",
    )
    p.add_argument("--json-out", type=Path, default=None)
    args = p.parse_args()
    payload = demo_payload(
        phi_epsilon=args.phi,
        rho_bulk=args.rho,
        wall_excess=args.wall_excess,
        wall_polarities=args.wall_polarities,
    )
    print_report(payload)
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"\nwrote {args.json_out}")


if __name__ == "__main__":
    main()
