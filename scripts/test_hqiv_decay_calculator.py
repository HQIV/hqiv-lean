#!/usr/bin/env python3
"""Tests for unified HQIV decay calculator."""

from __future__ import annotations

import hqiv_decay_calculator as calc
import hqiv_hep_decay_chain as hep


def test_beam_mix_parse() -> None:
    mix = hep.parse_beam_mix("p:0.8,pi+:0.2@12", default_energy_gev=400.0)
    assert len(mix) == 2
    assert abs(sum(c.fraction for c in mix) - 1.0) < 1e-9
    assert mix[1].kinetic_energy_gev == 12.0
    assert abs(mix[1].fraction - 0.2) < 1e-9


def test_neutron_nuclear_bridge() -> None:
    env = hep.ExperimentEnvironment()
    n = hep.build_particle("n")
    edges = hep.edges_from_particle(n, env=env)
    assert edges
    assert edges[0].daughters[0].species_id == "p"
    assert edges[0].half_life_s > 100.0


def test_beam_dump_includes_neutron_chain() -> None:
    result = hep.run_experiment(
        hep.FACILITY_PRESETS["PS_p_beam_dump_24GeV"],
        include_beam_dump=True,
        max_depth=3,
    )
    root_ids = {r.particle.species_id for r in result.root_nodes}
    assert "n" in root_ids


def test_discharge_command() -> None:
    code = calc.main(["discharge", "--facility", "SPS_p_beam_400GeV", "--max-depth", "3"])
    assert code == 0


def test_nuclear_subcommand() -> None:
    code = calc.main(["nuclear", "--seed", "n", "--max-depth", "2"])
    assert code == 0


if __name__ == "__main__":
    test_beam_mix_parse()
    test_neutron_nuclear_bridge()
    test_beam_dump_includes_neutron_chain()
    test_discharge_command()
    test_nuclear_subcommand()
    print("test_hqiv_decay_calculator: OK")
