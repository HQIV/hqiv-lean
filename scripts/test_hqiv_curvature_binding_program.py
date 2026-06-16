#!/usr/bin/env python3
"""Tests for curvature-first binding (G_eff spine)."""

from __future__ import annotations

import unittest

import hqiv_bbn_abundances as bbn
import hqiv_curvature_binding_core as cbc
import hqiv_curvature_binding_program as cbp
import hqiv_nuclear_curvature_binding as ncur
import hqiv_nuclear_inside_outside_binding as niob


class TestCurvatureBindingCore(unittest.TestCase):
    def test_g_eff_matches_lean_alpha(self) -> None:
        eta = 0.5
        self.assertAlmostEqual(cbc.g_eff(eta), eta ** (3.0 / 5.0), places=9)

    def test_outside_lean_formula_a_le_4(self) -> None:
        m = 4
        A = 4
        m_cluster = ncur.nucleus_curvature_shell(A)
        outside, geff, _, units = cbc.outside_nuclear_binding_curvature_mev(
            m, A, 2, m_cluster=m_cluster
        )
        trace = niob.nucleon_trace_binding_mev(m)
        vc = bbn.valley_count(A, 2)
        self.assertEqual(units, float(vc))
        self.assertAlmostEqual(outside, geff * trace * vc, places=6)

    def test_inside_plus_outside_equals_total(self) -> None:
        m = 4
        A = 4
        m_cluster = ncur.nucleus_curvature_shell(A)
        total, inside, outside, _, _, _ = cbc.cluster_binding_curvature_mev(
            m, A, 2, m_cluster=m_cluster
        )
        self.assertAlmostEqual(total, inside + outside, places=9)
        self.assertGreater(inside, 0.0)
        self.assertGreater(outside, 0.0)

    def test_deuteron_network_near_pdg(self) -> None:
        row = cbp.build_curvature_row(2, 1, "²H")
        self.assertIsNotNone(row.pdg_binding_total_mev)
        assert row.pdg_binding_total_mev is not None
        err = abs(row.total_curvature_mev - row.pdg_binding_total_mev)
        self.assertLess(err / row.pdg_binding_total_mev, 0.15)

    def test_he4_network_closes_gap_vs_bare_curvature(self) -> None:
        row = cbp.build_curvature_row(4, 2, "⁴He")
        bare_total, _, bare_out, _, _, _ = cbc.cluster_binding_curvature_mev(4, 4, 2)
        self.assertGreater(row.total_curvature_mev, bare_total * 2.0)
        self.assertGreater(row.outside_gamma_network_mev, 0.0)
        self.assertGreater(row.outside_tetra_closure_mev, 0.0)

    def test_mass_deficit_factor_at_least_one(self) -> None:
        row = cbp.build_curvature_row(4, 2, "⁴He")
        self.assertGreaterEqual(row.mass_deficit_factor, 1.0)

    def test_spin_magnetic_residual_closes_he4(self) -> None:
        row = cbp.build_curvature_row(4, 2, "⁴He")
        self.assertIsNotNone(row.pdg_binding_total_mev)
        assert row.pdg_binding_total_mev is not None
        err = abs(row.total_curvature_mev - row.pdg_binding_total_mev)
        self.assertLess(err / row.pdg_binding_total_mev, 0.08)

    def test_li5_incremental_not_overshooting(self) -> None:
        row = cbp.build_curvature_row(5, 3, "⁵Li")
        self.assertIsNotNone(row.pdg_binding_total_mev)
        assert row.pdg_binding_total_mev is not None
        err = abs(row.total_curvature_mev - row.pdg_binding_total_mev)
        self.assertLess(err / row.pdg_binding_total_mev, 0.05)

    def test_li6_near_pdg(self) -> None:
        row = cbp.build_curvature_row(6, 3, "⁶Li")
        self.assertIsNotNone(row.pdg_binding_total_mev)
        assert row.pdg_binding_total_mev is not None
        err = abs(row.total_curvature_mev - row.pdg_binding_total_mev)
        self.assertLess(err / row.pdg_binding_total_mev, 0.04)

    def test_post_alpha_incremental_geometry_excludes_cap(self) -> None:
        import hqiv_post_alpha_binding_program as pap

        m = cbp.M_SHELL
        full_geom = pap.post_alpha_geometric_touch_energy(m, 7, 3)
        inc_geom = pap.post_alpha_incremental_geometric_touch_energy_r2(m, 7, 3)
        cap = pap.post_alpha_alpha_core_geometric_energy(m, 7, 3)
        self.assertLess(inc_geom, full_geom)
        self.assertAlmostEqual(inc_geom + cap, full_geom, places=6)

    def test_bbn_network_q_matches_row(self) -> None:
        import hqiv_bbn_abundances as bbn

        m = cbp.M_SHELL
        q_d, q_4, _q_3, _q_7 = bbn.lockin_binding_q_network(938.27208816)
        row_d = cbp.build_curvature_row(2, 1, "²H", earth_mass_chart=False)
        row_he = cbp.build_curvature_row(4, 2, "⁴He", earth_mass_chart=False)
        self.assertAlmostEqual(q_d, row_d.total_curvature_mev, places=3)
        self.assertAlmostEqual(q_4, row_he.total_curvature_mev, places=3)

    def test_post_alpha_contact_units_positive(self) -> None:
        units = cbc.post_alpha_curvature_contact_units(12, 6)
        self.assertGreater(units, 0.0)

    def test_trimer_resonance_width_for_he3(self) -> None:
        import hqiv_curvature_binding_core as cbc

        total = bbn.cluster_binding_network_mev(4, 3, Z=2)
        width = cbc.trimer_resonance_width_mev(4, 3, 2, total)
        self.assertGreater(width, 0.0)
        self.assertLess(width, total)

    def test_li7_far_neutron_closes_gap(self) -> None:
        row = cbp.build_curvature_row(7, 3, "⁷Li")
        self.assertIsNotNone(row.pdg_binding_total_mev)
        assert row.pdg_binding_total_mev is not None
        err = abs(row.total_curvature_mev - row.pdg_binding_total_mev)
        self.assertLess(err / row.pdg_binding_total_mev, 0.02)

    def test_be8_multi_alpha_near_pdg(self) -> None:
        row = cbp.build_curvature_row(8, 4, "⁸Be")
        self.assertIsNotNone(row.pdg_binding_total_mev)
        assert row.pdg_binding_total_mev is not None
        err = abs(row.total_curvature_mev - row.pdg_binding_total_mev)
        self.assertLess(err / row.pdg_binding_total_mev, 0.02)

    def test_panel_mean_error_below_one_percent(self) -> None:
        rows = [
            cbp.build_curvature_row(a, z, n)
            for a, z, n in cbp.DEFAULT_PANEL
        ]
        errs = []
        for row in rows:
            if row.pdg_binding_total_mev is None:
                continue
            errs.append(
                abs(row.total_curvature_mev - row.pdg_binding_total_mev)
                / row.pdg_binding_total_mev
            )
        self.assertLess(sum(errs) / len(errs), 0.013)

    def test_c12_multi_alpha_near_pdg(self) -> None:
        row = cbp.build_curvature_row(12, 6, "¹²C")
        self.assertIsNotNone(row.pdg_binding_total_mev)
        assert row.pdg_binding_total_mev is not None
        err = abs(row.total_curvature_mev - row.pdg_binding_total_mev)
        self.assertLess(err / row.pdg_binding_total_mev, 0.02)

    def test_he3_coulomb_splits_from_triton(self) -> None:
        row_h = cbp.build_curvature_row(3, 1, "³H")
        row_he = cbp.build_curvature_row(3, 2, "³He")
        self.assertIsNotNone(row_h.pdg_binding_total_mev)
        self.assertIsNotNone(row_he.pdg_binding_total_mev)
        assert row_h.pdg_binding_total_mev is not None
        assert row_he.pdg_binding_total_mev is not None
        self.assertGreater(row_h.total_curvature_mev, row_he.total_curvature_mev)
        err = abs(row_he.total_curvature_mev - row_he.pdg_binding_total_mev)
        self.assertLess(err / row_he.pdg_binding_total_mev, 0.02)

    def test_o16_multi_alpha_near_pdg(self) -> None:
        row = cbp.build_curvature_row(16, 8, "¹⁶O")
        self.assertIsNotNone(row.pdg_binding_total_mev)
        assert row.pdg_binding_total_mev is not None
        err = abs(row.total_curvature_mev - row.pdg_binding_total_mev)
        self.assertLess(err / row.pdg_binding_total_mev, 0.02)

    def test_earth_k_mass_chart_scales_outside_only(self) -> None:
        import hqiv_nuclear_outside_temperature_dynamics as notd

        env = notd.LabOutsideEnvironment(gravity_tier="full")
        k = env.outside_closure_k_mass_chart()
        row_earth = cbp.build_curvature_row(4, 2, "⁴He", earth_mass_chart=True, lab_env=env)
        row_vac = cbp.build_curvature_row(4, 2, "⁴He", earth_mass_chart=False)
        self.assertIsNotNone(row_earth.outside_closure_k_mass_chart)
        self.assertAlmostEqual(row_earth.outside_closure_k_mass_chart, k, places=9)
        self.assertAlmostEqual(row_earth.inside_mev, row_vac.inside_mev, places=9)
        self.assertAlmostEqual(row_earth.outside_mev_chart, row_vac.outside_mev, places=4)
        self.assertAlmostEqual(row_earth.outside_mev, row_earth.outside_mev_chart * k, places=6)
        self.assertGreater(row_earth.outside_mev, row_vac.outside_mev)
        self.assertAlmostEqual(
            row_earth.total_curvature_mev,
            row_earth.inside_mev + row_earth.outside_mev,
            places=9,
        )


if __name__ == "__main__":
    unittest.main()
