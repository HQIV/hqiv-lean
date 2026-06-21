#!/usr/bin/env python3
"""Spot checks: Python readout mirrors Lean `HepDecayReadout.lean` formulas."""

from __future__ import annotations

import unittest

import hqiv_hep_decay_chain as hep
import hqiv_hep_decay_readout as hdr
import hqiv_lean_physics_primitives as lean


class TestHepDecayReadout(unittest.TestCase):
    def test_chiral_factor(self) -> None:
        self.assertAlmostEqual(hdr.CHIRAL_PSEUDOSCALAR_FACTOR, (4.0 / 9.0) ** 2)
        self.assertAlmostEqual(hdr.PION_DECAY_CONSTANT_RATIO, 2.0 / 3.0)

    def test_ckm_hierarchy(self) -> None:
        us = hdr.ckm_slot_us_squared()
        cd = hdr.ckm_slot_cd_squared()
        cb = hdr.ckm_slot_cb_squared()
        self.assertAlmostEqual(us, lean.GAMMA / 8.0)
        self.assertAlmostEqual(cd, lean.GAMMA / 16.0)
        self.assertAlmostEqual(cb, lean.GAMMA / 32.0)
        self.assertLess(cd, us)
        self.assertLess(cb, cd)

    def test_outside_mass_dressing_rationals(self) -> None:
        self.assertAlmostEqual(hdr.open_charm_outside_mass_dressing(), 21.0 / 20.0)
        self.assertAlmostEqual(hdr.charmed_baryon_outside_mass_dressing(), 43.0 / 40.0)
        self.assertAlmostEqual(hdr.open_bottom_outside_mass_dressing(), 41.0 / 40.0)
        self.assertAlmostEqual(hdr.bottom_baryon_outside_mass_dressing(), 53.0 / 50.0)
        self.assertAlmostEqual(hdr.hidden_quarkonium_outside_mass_dressing(), 41.0 / 40.0)
        self.assertAlmostEqual(hdr.chiral_pseudoscalar_outside_mass_dressing(), 81.0 / 80.0)
        self.assertAlmostEqual(hdr.strange_baryon_octet_outside_mass_dressing(), 79.0 / 80.0)
        self.assertAlmostEqual(
            hdr.hidden_strangeness_vector_outside_mass_dressing(), 61.0 / 60.0
        )

    def test_hidden_quarkonium_contact_factor(self) -> None:
        self.assertAlmostEqual(
            hdr.hidden_quarkonium_em_contact_factor(),
            37.0 / 10.0,
        )

    def test_hidden_quarkonium_em_contact_from_spine_slots(self) -> None:
        self.assertAlmostEqual(
            hdr.hidden_quarkonium_em_contact_from_spine_slots(),
            hdr.bottom_external_weak_contact() + lean.GAMMA / 2.0,
        )
        self.assertAlmostEqual(
            hdr.hidden_quarkonium_em_contact_from_spine_slots(),
            hdr.hidden_quarkonium_em_contact_factor(),
        )
        self.assertAlmostEqual(hdr.bottom_external_weak_contact(), 7.0 / 2.0)
        self.assertAlmostEqual(hdr.hidden_quarkonium_em_contact_full_fano_return(), 39.0 / 10.0)

    def test_hidden_quarkonium_em_contact_not_pdg_reverse_engineered(self) -> None:
        fit = hdr.hidden_quarkonium_em_contact_pdg_reverse_engineered()
        derived = hdr.hidden_quarkonium_em_contact_factor()
        self.assertAlmostEqual(fit, 3.47, places=2)
        self.assertNotAlmostEqual(derived, fit, places=2)
        self.assertAlmostEqual(derived, 3.7, places=2)

    def _jpsi_ee_branching(self, contact: float) -> float:
        from unittest.mock import patch

        env = hep.ExperimentEnvironment()
        p = hep.build_particle("Jpsi")
        with patch.object(
            hdr,
            "hidden_quarkonium_em_contact_factor",
            return_value=contact,
        ):
            edges = hep.edges_from_particle(p, env=env)
        total = sum(e.width_per_s for e in edges if e.width_per_s > 0)
        ee = [
            e
            for e in edges
            if e.mode.channel == "electromagnetic"
            and any(d.species_id in ("e+", "e_plus") for d in e.daughters)
        ]
        w_ee = sum(e.width_per_s for e in ee)
        return w_ee / total

    def test_jpsi_em_branching_follows_gamma_contact_not_fit(self) -> None:
        leading = self._jpsi_ee_branching(1.0)
        derived = self._jpsi_ee_branching(hdr.hidden_quarkonium_em_contact_factor())
        full_fano = self._jpsi_ee_branching(hdr.hidden_quarkonium_em_contact_full_fano_return())
        fit = self._jpsi_ee_branching(hdr.hidden_quarkonium_em_contact_pdg_reverse_engineered())
        self.assertAlmostEqual(leading, 0.01767, places=3)
        self.assertAlmostEqual(derived, 0.05968, places=3)
        self.assertGreater(full_fano, derived)
        self.assertAlmostEqual(full_fano, 0.0625, places=3)
        self.assertNotAlmostEqual(fit, derived, places=3)
        self.assertAlmostEqual(fit, 0.0564, places=3)

    def test_bottom_baryon_multiplet_scaffold(self) -> None:
        self.assertAlmostEqual(hdr.bottom_baryon_sigma_hyperfine_weight(), 31.0 / 30.0)
        self.assertEqual(hdr.bottom_baryon_strange_count("lambda"), 0)
        self.assertEqual(hdr.bottom_baryon_strange_count("sigma"), 0)
        self.assertEqual(hdr.bottom_baryon_strange_count("xi"), 1)
        self.assertEqual(hdr.bottom_baryon_strange_count("omega"), 2)

    def test_bottom_baryon_multiplet_masses(self) -> None:
        xi = lean.XI_LOCKIN
        m_pi = hep._chiral_pseudoscalar_mass_mev("pi_plus", xi=xi) or 139.0
        m_k = hep._chiral_pseudoscalar_mass_mev("K_plus", xi=xi) or 486.0
        m_p = hep.particle_mass_mev("p", xi=xi)
        for sid, mult in (
            ("lambda_b", "lambda"),
            ("sigma_b", "sigma"),
            ("xi_b", "xi"),
            ("omega_b", "omega"),
        ):
            via_hdr = hdr.heavy_species_mass_mev(
                "bottom_baryon",
                m_pi_mev=m_pi,
                m_k_mev=m_k,
                m_proton_mev=m_p,
                n_charm=0,
                n_strange=0,
                multiplet=mult,  # type: ignore[arg-type]
            )
            via_chain = hep.particle_mass_mev(sid, xi=xi)
            self.assertIsNotNone(via_chain, msg=sid)
            self.assertAlmostEqual(via_hdr, via_chain, delta=0.5, msg=sid)

    def test_charmed_baryon_xi_prime_excitation_factor(self) -> None:
        self.assertAlmostEqual(hdr.charmed_baryon_xi_prime_excitation_factor(), 25.0 / 24.0)
        self.assertAlmostEqual(
            hdr.charmed_baryon_xi_prime_excitation_factor(),
            hdr.charmed_baryon_sigma_hyperfine_weight() - lean.GAMMA / 16.0,
        )

    def test_hidden_bottom_radial_excitation(self) -> None:
        self.assertAlmostEqual(
            hdr.hidden_bottom_quarkonium_excitation_factor(1), 1.0 + lean.GAMMA / 6.0
        )
        self.assertAlmostEqual(
            hdr.hidden_bottom_quarkonium_excitation_factor(2),
            1.0 + lean.GAMMA / 6.0 + lean.GAMMA / 12.0,
        )
        self.assertAlmostEqual(hdr.nucleon_resonance_1535_mass_factor(), 101.0 / 100.0)
        self.assertAlmostEqual(hdr.nucleon_resonance_1680_mass_factor(), 139.0 / 140.0)
        self.assertAlmostEqual(hdr.nucleon_resonance_1710_mass_factor(), 69.0 / 70.0)
        self.assertAlmostEqual(hdr.lambda_strange_orbital_mass_factor(), 697.0 / 700.0)

    def test_decuplet_strange_orbital_multiplet(self) -> None:
        xi = lean.XI_LOCKIN
        m_pi = hep._chiral_pseudoscalar_mass_mev("pi_plus", xi=xi) or 139.0
        m_k = hep._chiral_pseudoscalar_mass_mev("K_plus", xi=xi) or 486.0
        scaffold = 1384.0
        xi_mass = hdr.decuplet_strange_orbital_multiplet_mass_mev(
            scaffold, m_k, m_pi, 2
        )
        self.assertGreater(xi_mass, scaffold)
        self.assertAlmostEqual(
            hdr.charmed_tetraquark_open_vector_excited_factor(),
            hdr.hidden_strangeness_vector_outside_mass_dressing(),
        )
        self.assertAlmostEqual(hdr.charmed_pentaquark_orbit_split_factor(), 71.0 / 70.0)

    def test_heavy_masses_match_chain(self) -> None:
        xi = lean.XI_LOCKIN
        m_pi = hep._chiral_pseudoscalar_mass_mev("pi_plus", xi=xi) or 139.0
        m_k = hep._chiral_pseudoscalar_mass_mev("K_plus", xi=xi) or 486.0
        m_p = hep.particle_mass_mev("p", xi=xi)
        for sid, kind, kw in (
            ("D_plus", "open_charm", {"n_charm": 1, "n_strange": 0}),
            ("Jpsi", "hidden_charm", {"n_charm": 2, "n_strange": 0}),
            ("B_plus", "open_bottom", {"n_charm": 0, "n_strange": 0}),
            ("Upsilon", "hidden_bottom", {"n_charm": 0, "n_strange": 0}),
        ):
            via_hdr = hdr.heavy_species_mass_mev(
                kind,  # type: ignore[arg-type]
                m_pi_mev=m_pi,
                m_k_mev=m_k,
                m_proton_mev=m_p,
                **kw,
            )
            via_chain = hep.particle_mass_mev(sid, xi=xi)
            self.assertAlmostEqual(via_hdr, via_chain, delta=0.5, msg=sid)
        mult = hdr.CHARMED_BARYON_MULTIPLET_BY_SPECIES["lambda_c"]
        via_hdr_lc = hdr.charmed_baryon_multiplet_mass_mev(m_p, m_k, m_pi, mult, n_charm=1)
        via_chain_lc = hep.particle_mass_mev("lambda_c", xi=xi)
        self.assertAlmostEqual(via_hdr_lc, via_chain_lc, delta=0.5, msg="lambda_c")


if __name__ == "__main__":
    unittest.main()
