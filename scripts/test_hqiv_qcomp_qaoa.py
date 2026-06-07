#!/usr/bin/env python3
"""Tests for HQIV QComp QAOA chemistry pipeline."""

from __future__ import annotations

import math

import hqiv_qcomp_qaoa as qaoa


def test_h2o_readout_has_per_bond_arrays() -> None:
    spec = qaoa.spec_from_molecule("H2O", bond_length_bits=2, angle_bits=2)
    geom = {d.name: d.reference_val for d in spec.dofs}
    r = qaoa.evaluate_geometry(spec, geom)
    assert len(r["bond_lengths_angstrom"]) == 2
    assert len(r["binding_energy_per_bond_ev"]) == 2
    assert abs(sum(r["binding_energy_per_bond_ev"]) - r["binding_energy_total_ev"]) < 0.01
    assert r["centre_angle_deg"] is not None


def test_brute_force_improves_or_matches_reference() -> None:
    spec = qaoa.spec_from_molecule("H2", bond_length_bits=2, angle_bits=1)
    ref = qaoa.run_reference_readout(spec)
    bf = qaoa.run_brute_force(spec)
    assert bf["readout"]["binding_energy_total_ev"] >= ref["readout"]["binding_energy_total_ev"] - 0.5


def test_qaoa_runs_on_h2o() -> None:
    spec = qaoa.spec_from_molecule("H2O", bond_length_bits=2, angle_bits=2)
    out = qaoa.run_classical_qaoa(spec, p_layers=1, maxiter=20)
    assert out["readout"]["binding_energy_total_ev"] > 0.0
    assert len(out["readout"]["binding_energy_per_bond_ev"]) == 2
    assert abs(out["readout"]["error_pct"]) < 20.0


if __name__ == "__main__":
    test_h2o_readout_has_per_bond_arrays()
    test_brute_force_improves_or_matches_reference()
    test_qaoa_runs_on_h2o()
    print("test_hqiv_qcomp_qaoa: OK")
