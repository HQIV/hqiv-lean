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
    parser.add_argument("--temperature-K", type=float, default=273.15)
    parser.add_argument("--allotropes-only", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--phase", choices=("solid", "liquid"), default="solid")
    args = parser.parse_args(argv)

    lab = MaterialsLab()
    try:
        spec = lab.spec_from_formula(args.molecule)
    except KeyError:
        spec = lab.spec_from_name(args.molecule)

    if args.allotropes_only:
        cands = lab.derive_allotropes(spec, temperature_k=args.temperature_K)
        payload = {"molecule": spec.name, "allotropes": [c.to_dict() for c in cands]}
    else:
        payload = lab.readout(
            spec,
            temperature_k=args.temperature_K,
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
