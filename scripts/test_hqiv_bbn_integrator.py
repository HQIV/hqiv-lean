#!/usr/bin/env python3
"""Tests for faithful BBN integrator and condition-dependent decay."""

from __future__ import annotations

import math
import unittest

import hqiv_bbn_abundances as bbn
import hqiv_bbn_condition_decay as decay
import hqiv_bbn_integrator as integrator


class TestBBNConditionDecay(unittest.TestCase):
    ETA = 6.1e-10
    M_P = 938.272
    Q_NP = 1.293

    def test_lockin_formation_and_capture_positive(self) -> None:
        lockin = decay.LockinNetworkQ.from_proton_mass(self.M_P)
        self.assertGreater(lockin.Q_form_be7, 0.0)
        self.assertGreater(lockin.Q_capture_be7_li7, 0.0)
        self.assertGreater(lockin.Q_li, lockin.Q_be)

    def test_lockin_q_matches_canonical_mass_ledger(self) -> None:
        import hqiv_dynamic_nucleon_pn as pn

        lockin = decay.LockinNetworkQ.from_proton_mass(self.M_P)
        self.assertAlmostEqual(lockin.Q_D, pn.cluster_binding_canonical_mev(2, 1), places=6)
        self.assertAlmostEqual(lockin.Q_4, pn.cluster_binding_canonical_mev(4, 2), places=6)
        self.assertAlmostEqual(lockin.Q_3, pn.cluster_binding_canonical_mev(3, 2), places=6)

    def test_canonical_binding_matches_mass_ledger(self) -> None:
        import hqiv_dynamic_nucleon_pn as pn

        for A, Z in ((2, 1), (3, 1), (3, 2), (4, 2)):
            b_can = pn.cluster_binding_canonical_mev(A, Z)
            b_mass = pn.cluster_binding_from_mass_ledger(A, Z)
            self.assertAlmostEqual(b_can, b_mass, places=6)

    def test_release_softens_resonance_width_at_high_t(self) -> None:
        total_8be = bbn.cluster_binding_network_mev(4, 8, Z=4)
        w_hot = decay.resonance_width_erosion_at_T(1.0, 4, 2, total_8be)
        w_cold = decay.resonance_width_erosion_at_T(0.01, 4, 2, total_8be)
        self.assertGreater(w_hot, 0.0)
        self.assertGreater(w_hot, w_cold)

    def test_trimer_width_positive_and_temperature_scaled(self) -> None:
        import hqiv_curvature_binding_core as cbc

        total = bbn.cluster_binding_network_mev(4, 3, Z=2)
        w_lock = cbc.trimer_resonance_width_mev(4, 3, 2, total)
        self.assertGreater(w_lock, 0.0)
        w_hot = decay.trimer_resonance_width_at_T(1.0, 4, 3, 2, total)
        w_cold = decay.trimer_resonance_width_at_T(0.01, 4, 3, 2, total)
        self.assertGreater(w_hot, w_cold)

    def test_stoichiometric_couples_d_and_he3(self) -> None:
        cond = decay.BBNCondition(
            T_MeV=0.15, eta=self.ETA, m_nucleon=self.M_P, Q_np=self.Q_NP
        )
        sto = decay.deuterium_stoichiometric_abundances_at_T(cond)
        self.assertLess(sto.He3_over_H, sto.He3_inventory_for_be7)
        self.assertGreaterEqual(sto.D_over_H, sto.D_seed_uncoupled)
        self.assertGreater(sto.D_np_capture, 0.0)
        self.assertGreater(sto.branch_np_to_d, 0.0)

    def test_np_to_d_gate_active_in_synthesis_band(self) -> None:
        self.assertEqual(
            decay.np_to_deuterium_synthesis_gate(0.5, self.ETA, self.Q_NP), 1.0
        )
        self.assertGreater(
            decay.np_to_deuterium_synthesis_gate(0.05, self.ETA, self.Q_NP), 0.0
        )
        self.assertLess(
            decay.np_to_deuterium_synthesis_gate(0.05, self.ETA, self.Q_NP), 1.0
        )

    def test_synthesis_d_tail_gate_unity_at_mid_and_fades_to_bottleneck(self) -> None:
        mid = decay.synthesis_d_window_peak_mev()
        T_bn = decay.synthesis_window_end_mev(self.ETA, self.Q_NP)
        self.assertAlmostEqual(
            decay.synthesis_d_window_tail_gate(mid, self.ETA, self.Q_NP), 1.0
        )
        self.assertAlmostEqual(
            decay.synthesis_d_window_tail_gate(mid + 0.1, self.ETA, self.Q_NP), 1.0
        )
        self.assertAlmostEqual(
            decay.synthesis_d_window_tail_gate(T_bn, self.ETA, self.Q_NP), 0.0
        )
        mid_tail = 0.5 * (T_bn + mid)
        g = decay.synthesis_d_window_tail_gate(mid_tail, self.ETA, self.Q_NP)
        self.assertGreater(g, 0.0)
        self.assertLess(g, 1.0)
        self.assertAlmostEqual(g, 0.5, places=6)

    def test_synthesis_window_low_is_bottleneck_not_hard_floor(self) -> None:
        T_bn = decay.synthesis_window_end_mev(self.ETA, self.Q_NP)
        _, T_lo = decay.synthesis_d_window_bounds_mev(self.ETA, self.Q_NP)
        self.assertAlmostEqual(T_lo, T_bn, places=6)
        self.assertLess(T_lo, decay.synthesis_d_window_peak_mev())

    def test_he3_gate_peaks_in_synthesis_window(self) -> None:
        self.assertEqual(decay.he3_synthesis_gate(1.0), 0.0)
        self.assertGreater(decay.he3_synthesis_gate(0.15), 0.0)
        self.assertEqual(decay.he3_synthesis_gate(0.01), 0.0)

    def test_condition_row_has_c2_suppression_in_bottleneck(self) -> None:
        lockin = decay.LockinNetworkQ.from_proton_mass(self.M_P)
        row = decay.condition_decay_row(
            decay.BBNCondition(
                T_MeV=0.1, eta=self.ETA, m_nucleon=self.M_P, Q_np=self.Q_NP
            ),
            lockin,
        )
        self.assertGreater(row.c2_suppression, 0.0)
        self.assertLess(row.c2_suppression, 1.0)

    def test_free_neutron_tau_ratio_at_bbn_gt_one(self) -> None:
        env = decay.free_neutron_weak_environment_at_T(0.715)
        self.assertGreater(env.tau_ratio_vs_lockin, 1.0)
        self.assertGreater(env.outside_lifetime_ratio, 1.0)
        self.assertGreater(env.weak_width_factor, 1.0)

    def test_curvature_raises_yp_vs_bare(self) -> None:
        lockin = decay.LockinNetworkQ.from_proton_mass(self.M_P)
        on = decay.y_p_with_free_neutron_curvature(
            self.ETA, self.Q_NP, lockin.Q_D, use_curvature=True
        )
        off = decay.y_p_with_free_neutron_curvature(
            self.ETA, self.Q_NP, lockin.Q_D, use_curvature=False
        )
        self.assertGreater(on.Y_p, off.Y_p)
        self.assertGreater(on.delta_Y_p, 0.0)
        self.assertGreater(on.T_freeze_effective_MeV, on.T_freeze_bare_MeV)


class TestBBNIntegrator(unittest.TestCase):
    def test_integrator_readout_order_of_magnitude(self) -> None:
        payload = integrator.run_bbn_integrator()
        r = payload["abundance_readout"]
        self.assertAlmostEqual(r["Y_p"], 0.244, delta=0.008)
        self.assertTrue(r.get("free_neutron_curvature"))
        self.assertGreater(r["D_over_H"], 2.0e-5)
        self.assertLess(r["D_over_H"], 3.0e-5)
        obs_dh = integrator.OBS_DH
        self.assertLess(abs(r["D_over_H"] - obs_dh), 3.0 * integrator.OBS_DH_SIGMA)
        self.assertGreater(r["He3_over_H"], 5e-6)
        self.assertLess(r["He3_over_H"], 3e-5)
        self.assertGreater(r["Li7_over_H"], 1e-10)
        self.assertLess(r["Li7_over_H"], 5e-10)
        self.assertLess(r["Be7_over_H"], r["Li7_over_H"])

    def test_he3_stratified_lowers_he3_vs_unstratified(self) -> None:
        cfg_on = integrator.BBNIntegratorConfig(he3_stratified=True)
        cfg_off = integrator.BBNIntegratorConfig(he3_stratified=False)
        on = integrator.run_bbn_integrator(cfg_on)["abundance_readout"]["He3_over_H"]
        off = integrator.run_bbn_integrator(cfg_off)["abundance_readout"]["He3_over_H"]
        self.assertLess(on, off)
        self.assertGreater(on, 0.0)

    def test_stoichiometric_raises_d_vs_partition_only(self) -> None:
        sto = integrator.run_bbn_integrator(
            integrator.BBNIntegratorConfig(stoichiometric_d_budget=True)
        )["abundance_readout"]["D_over_H"]
        part = integrator.run_bbn_integrator(
            integrator.BBNIntegratorConfig(stoichiometric_d_budget=False)
        )["abundance_readout"]["D_over_H"]
        self.assertGreaterEqual(sto, part * 0.98)

    def test_neutron_curvature_can_disable(self) -> None:
        on = integrator.run_bbn_integrator(integrator.BBNIntegratorConfig(use_free_neutron_curvature=True))
        off = integrator.run_bbn_integrator(integrator.BBNIntegratorConfig(use_free_neutron_curvature=False))
        self.assertGreater(on["abundance_readout"]["D_over_H"], off["abundance_readout"]["D_over_H"])

    def test_synthesis_window_raises_d_vs_full_tail(self) -> None:
        on = integrator.run_bbn_integrator(
            integrator.BBNIntegratorConfig(use_synthesis_d_window=True)
        )["abundance_readout"]["D_over_H"]
        off = integrator.run_bbn_integrator(
            integrator.BBNIntegratorConfig(use_synthesis_d_window=False)
        )["abundance_readout"]["D_over_H"]
        self.assertGreater(on, off * 1.5)

    def test_coupled_inventory_raises_d_and_yp(self) -> None:
        on = integrator.run_bbn_integrator(
            integrator.BBNIntegratorConfig(
                use_free_neutron_curvature=True,
                use_coupled_neutron_inventory=True,
            )
        )["abundance_readout"]
        off = integrator.run_bbn_integrator(
            integrator.BBNIntegratorConfig(
                use_free_neutron_curvature=False,
                use_coupled_neutron_inventory=True,
            )
        )["abundance_readout"]
        self.assertGreater(on["D_over_H"], off["D_over_H"])
        self.assertGreater(on["delta_D_over_H_curvature"], 0.0)

    def test_witness_has_decay_key_epochs(self) -> None:
        payload = integrator.run_bbn_integrator()
        keys = payload["condition_decay_key_epochs"]
        self.assertEqual(len(keys), 5)
        temps = [row["condition"]["T_MeV"] for row in keys]
        self.assertTrue(all(math.isfinite(T) for T in temps))

    def test_witness_matches_integrator_lean_audit_faithful_row(self) -> None:
        import json
        from pathlib import Path

        import hqiv_integrator_lean_audit as audit

        payload = integrator.run_bbn_integrator()
        audit_payload = audit.build_payload(400)
        row = audit_payload["faithful_bbn_integrator"]
        spine = audit_payload["stoichiometric_spine"]
        r = payload["abundance_readout"]
        self.assertAlmostEqual(row["Yp"], r["Y_p"], places=12)
        self.assertAlmostEqual(row["D_over_H"], r["D_over_H"], places=12)
        self.assertAlmostEqual(row["He3_over_H"], r["He3_over_H"], places=12)
        self.assertAlmostEqual(row["Li7_over_H"], r["Li7_over_H"], places=12)
        self.assertEqual(spine["constants"]["bbnHe3SynthesisMidMeV"], decay.HE3_SYNTH_MID_MEV)
        self.assertAlmostEqual(
            spine["gate_samples_at_T_0p2_MeV"]["bbnSynthesisDWindowTailGate"],
            decay.synthesis_d_window_tail_gate(
                0.2, integrator.BBNIntegratorConfig().eta, 1.293
            ),
        )

        on_disk = json.loads(
            (Path(__file__).resolve().parents[1] / "data" / "bbn_integrator.json").read_text()
        )
        disk = on_disk["abundance_readout"]
        self.assertAlmostEqual(disk["Y_p"], r["Y_p"], places=10)
        self.assertTrue(math.isclose(disk["D_over_H"], r["D_over_H"], rel_tol=0, abs_tol=1e-12))


if __name__ == "__main__":
    unittest.main()
