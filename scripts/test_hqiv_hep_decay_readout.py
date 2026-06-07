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

    def test_hidden_quarkonium_contact_factor(self) -> None:
        self.assertAlmostEqual(
            hdr.hidden_quarkonium_em_contact_factor(),
            39.0 / 10.0,
        )

    def test_heavy_masses_match_chain(self) -> None:
        xi = lean.XI_LOCKIN
        m_pi = hep._chiral_pseudoscalar_mass_mev("pi_plus", xi=xi) or 139.0
        m_k = hep._chiral_pseudoscalar_mass_mev("K_plus", xi=xi) or 486.0
        m_p = hep.particle_mass_mev("p", xi=xi)
        for sid, kind, kw in (
            ("D_plus", "open_charm", {"n_charm": 1, "n_strange": 0}),
            ("Jpsi", "hidden_charm", {"n_charm": 2, "n_strange": 0}),
            ("lambda_c", "charmed_baryon", {"n_charm": 1, "n_strange": 0}),
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


if __name__ == "__main__":
    unittest.main()
