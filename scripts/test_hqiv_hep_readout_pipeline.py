#!/usr/bin/env python3
"""Smoke tests for hqiv_hep_readout_pipeline.py."""

from __future__ import annotations

import json
import math

import hqiv_hep_readout_pipeline as pipe


def test_resolve_facility_and_phi_discharge() -> None:
    inp = pipe.ColliderLocalInput(facility="SPS_p_beam_400GeV", environment="lab")
    result = pipe.run_local_readout(inp, parents=("phi",))
    table = result.parent_tables["phi"]
    assert len(table) == 2
    kk = next(r for r in table if r["daughters"] == ["K_plus", "K_minus"])
    assert math.isclose(kk["branching_ratio"], 0.84, rel_tol=1e-6)
    assert math.isclose(kk["spine_discharge_weight"], 21.0 / 25.0, rel_tol=1e-9)


def test_beam_mix_and_collider_env() -> None:
    inp = pipe.ColliderLocalInput(
        beam_id="p",
        beam_kinetic_energy_gev=24.0,
        target_id="p",
        beam_mix="p:0.9,pi+:12@0.1",
        environment="collider_hadron",
        magnetic_field_tesla=4.0,
        comoving_stream_fraction=0.5,
    )
    env = pipe.resolve_environment(inp)
    assert env.weak_width_factor() > 1.0
    setup = pipe.resolve_beam_setup(inp)
    assert setup.beam_mix


def test_paper_reproduce_smoke() -> None:
    manifest = pipe.reproduce_paper(strict=False, skip_tests=True, skip_collider_witnesses=True)
    assert manifest["ok"] is True
    assert not manifest["errors"]
    bench = json.loads((pipe.ROOT / "data" / "hep_decay_benchmark.json").read_text())
    assert bench["summary"]["fail"] == 0


if __name__ == "__main__":
    test_resolve_facility_and_phi_discharge()
    test_beam_mix_and_collider_env()
    test_paper_reproduce_smoke()
    print("test_hqiv_hep_readout_pipeline: OK")
