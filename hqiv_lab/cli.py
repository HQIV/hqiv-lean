#!/usr/bin/env python3
"""CLI for HQIV materials lab."""

from __future__ import annotations

import argparse
import json
import sys

from hqiv_lab.lab import MaterialsLab


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="HQIV chem & materials lab")
    parser.add_argument("molecule", help="Formula or GMTKN55 name (e.g. H2O, CH4)")
    parser.add_argument("--temperature-K", type=float, default=None)
    parser.add_argument(
        "--at-melt",
        action="store_true",
        default=True,
        help="Use species melt witness T (default on for panel species)",
    )
    parser.add_argument("--reference-T", action="store_true", help="Force T=273.15 K")
    parser.add_argument("--allotropes-only", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--phase", choices=("solid", "liquid"), default="solid")
    args = parser.parse_args(argv)

    from hqiv_lab.species_panel import panel_entry

    t_k = args.temperature_K
    if t_k is None:
        if args.reference_T:
            t_k = 273.15
        elif args.at_melt:
            try:
                t_k = panel_entry(args.molecule).witness_temperature_k
            except KeyError:
                t_k = 273.15
        else:
            t_k = 273.15

    lab = MaterialsLab()
    try:
        spec = lab.spec_from_formula(args.molecule)
    except KeyError:
        spec = lab.spec_from_name(args.molecule)

    if args.allotropes_only:
        cands = lab.derive_allotropes(spec, temperature_k=t_k)
        payload = {"molecule": spec.name, "allotropes": [c.to_dict() for c in cands]}
    else:
        payload = lab.readout(
            spec,
            temperature_k=t_k,
            phase=args.phase,
            include_response=not args.allotropes_only,
        )

    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        mono = payload.get("monomer") or payload["allotropes"][0]
        if "monomer" in payload:
            print(f"{payload['molecule']}  motif={payload['monomer']['motif']}")
            pref = payload["preferred_allotrope"]
            if pref:
                print(f"  preferred: {pref['label']}  ρ={pref['density_g_cm3']:.4f} g/cm³  score={pref['score']:.3f}")
            for c in payload["allotropes"]:
                print(f"    {c['label']:12} ρ={c['density_g_cm3']:.4f}  score={c['score']:.3f}  {c['description']}")
            if "material_response" in payload:
                mr = payload["material_response"]
                print(f"  n={mr['refractive_index']:.4f}  k_th={mr['thermal_conductivity_W_mK']:.3f} W/(m·K)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
