#!/usr/bin/env python3
"""Patch `data/hqiv_witnesses.json` with TUFT T10 neutrino masses + PMNS readout."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import hqiv_tuft_neutrino_bridge as bridge
import hqiv_tuft_mass_spectrum_pdg_eval as tmse

_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = _ROOT / "data" / "hqiv_witnesses.json"


def patch_witness_json(path: Path = DEFAULT_JSON) -> dict:
    raw: dict = {}
    if path.exists():
        raw = json.loads(path.read_text(encoding="utf-8"))
    for key in ("m_nu_e", "m_nu_mu", "m_nu_tau"):
        raw.pop(key, None)
    nu = bridge.model_tuft_outer_t8_t10(tmse.XI_LOCKIN)
    pmns = bridge.t10_pmns_readout()
    ang = pmns["pmns_angles_rad"]
    raw.update(
        {
            "neutrino_source": "tuft_outer_t8_t10",
            "nu_m1_MeV": nu.m1_mev,
            "nu_m2_MeV": nu.m2_mev,
            "nu_m3_MeV": nu.m3_mev,
            "nu_sum_MeV": nu.m1_mev + nu.m2_mev + nu.m3_mev,
            "pmns_theta12_rad": ang["theta12_rad"],
            "pmns_theta23_rad": ang["theta23_rad"],
            "pmns_theta13_rad": ang["theta13_rad"],
            "pmns_delta_rad": ang["delta_rad"],
            "m_nu_e_derived_status": "retired",
        }
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(raw, indent=2) + "\n", encoding="utf-8")
    return raw


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    raw = patch_witness_json(args.json)
    print(f"Patched neutrino witnesses in {args.json}")
    print(
        f"  Σm_ν = {raw['nu_sum_MeV']:.6g} MeV "
        f"({raw['nu_sum_MeV'] * 1e6:.4g} eV cap diagnostic)"
    )


if __name__ == "__main__":
    main()
