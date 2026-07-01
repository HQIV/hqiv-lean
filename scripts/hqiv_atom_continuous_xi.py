#!/usr/bin/env python3
"""
Continuous ξ readouts for atom electronic discharge shells.

Integer Compton shell `m` samples ξ = m+1 on the HQIV curvature ladder
(`hqiv_shell_shape_geometry`). Used by the atom construction witness panel —
not a fit to NIST; comparison stays quarantined in `AtomComparisonLayer`.

Run:
  python3 scripts/hqiv_atom_continuous_xi.py --z 8
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Any

import hqiv_shell_shape_geometry as ssg


@dataclass(frozen=True)
class ShellXiReadout:
    m: int
    xi: float
    phi: float
    shell_shape: float
    one_over_alpha_eff: float
    alpha_eff: float
    detuned_surface: float

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def shell_xi_readout(m: int, *, c: float = 1.0) -> ShellXiReadout:
    xi = ssg.xi_from_m(float(m))
    inv_ae = ssg.one_over_alpha_eff_xi(xi, c=c)
    return ShellXiReadout(
        m=m,
        xi=xi,
        phi=ssg.phi_of_xi(xi),
        shell_shape=ssg.shell_shape_at_xi(xi),
        one_over_alpha_eff=inv_ae,
        alpha_eff=1.0 / inv_ae,
        detuned_surface=ssg.detuned_surface_xi(xi),
    )


def shells_xi_panel(shells: tuple[int, ...], *, c: float = 1.0) -> list[ShellXiReadout]:
    return [shell_xi_readout(m, c=c) for m in shells]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--z", type=int, default=1)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    import hqiv_atom_construction as ac

    shells = tuple(ac.atom_electron_shells(args.z))
    panel = [r.to_dict() for r in shells_xi_panel(shells)]
    if args.json:
        print(json.dumps({"Z": args.z, "shells": panel}, indent=2))
    else:
        print(f"Z={args.z}  discharge shells {shells}")
        for row in panel:
            print(
                f"  m={row['m']}  ξ={row['xi']:.3f}  "
                f"σ(ξ)={row['shell_shape']:.6f}  1/α_eff={row['one_over_alpha_eff']:.4f}"
            )


if __name__ == "__main__":
    main()
