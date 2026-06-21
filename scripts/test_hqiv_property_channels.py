#!/usr/bin/env python3
"""Property-channel routing (no nominal-species tables in the router)."""

from __future__ import annotations

import unittest

import hqiv_hep_decay_readout as hdr
import hqiv_hep_decay_ledger_contact as ledger
import hqiv_property_channels as pc
import hqiv_spine_discharge_weight as sdw


class TestWeakPropertyChannels(unittest.TestCase):
    def test_lambda_neutral_baryon_outlet(self) -> None:
        edge = pc.classify_weak_edge("lambda", ("n", "pi_zero"))
        self.assertIsNotNone(edge)
        assert edge is not None
        self.assertEqual(edge.outlet, "isospin_half_neutral_pion_baryon")
        kind = pc.derive_weak_contact_kind("lambda", ("n", "pi_zero"))
        self.assertEqual(kind, "light_baryon_neutral_isospin_outlet")
        self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 0.75)

    def test_lambda_charged_outlet(self) -> None:
        edge = pc.classify_weak_edge("lambda", ("p", "pi_minus"))
        self.assertEqual(edge.outlet, "isospin_half_charged_hadronic")
        self.assertEqual(
            pc.derive_weak_contact_kind("lambda", ("p", "pi_minus")),
            "isospin_half_weak",
        )

    def test_K_plus_monogamy_outlets(self) -> None:
        charged = pc.classify_weak_edge("K_plus", ("pi_plus",))
        neutral = pc.classify_weak_edge("K_plus", ("pi_zero",))
        self.assertEqual(charged.outlet, "kaon_hadronic_monogamy_charged")
        self.assertEqual(neutral.outlet, "kaon_hadronic_monogamy_neutral")

    def test_K_plus_semileptonic_property(self) -> None:
        edge = pc.classify_weak_edge("K_plus", ("mu_plus",))
        self.assertEqual(edge.outlet, "semileptonic_visible_lepton")

    def test_lambda_c_two_body_property(self) -> None:
        import hqiv_hep_patch_species as hps

        parent = hps.patch_from_species_id("lambda_c")
        assert parent is not None
        self.assertTrue(pc.charmed_baryon_two_body_discharge(parent, ("p", "pi_zero")))
        self.assertTrue(pc.charmed_baryon_two_body_discharge(parent, ("n", "K_plus")))
        self.assertFalse(pc.charmed_baryon_two_body_discharge(parent, ("p", "K_minus")))

    def test_Bs_two_body_property(self) -> None:
        import hqiv_hep_patch_species as hps

        parent = hps.patch_from_species_id("Bs")
        assert parent is not None
        self.assertTrue(pc.bottom_strange_two_body_discharge(parent, ("phi", "phi")))
        self.assertTrue(pc.bottom_strange_two_body_discharge(parent, ("Ds_plus", "K_minus")))
        edge = pc.classify_weak_edge("Bs", ("Ds_plus", "K_minus"))
        self.assertEqual(edge.outlet, "bottom_strange_open_charm")

    def test_B0_neutral_spectator_exact_tag(self) -> None:
        import hqiv_hep_patch_species as hps

        parent = hps.patch_from_species_id("B0")
        assert parent is not None
        self.assertTrue(pc._bottom_neutral_spectator(parent, ("D0", "pi_zero")))
        self.assertFalse(pc._bottom_neutral_spectator(parent, ("D_plus", "pi_zero")))
        obs = sdw.discharge_observables("B0", "weak", ("D_plus", "pi_zero"))
        self.assertEqual(obs.neutral_spectator, 0)
        self.assertEqual(obs.finite_channel_completion, 1)

    def test_ledger_matches_property_router(self) -> None:
        rows = (
            ("lambda", "weak", ("p", "pi_minus"), "isospin_half_weak"),
            ("lambda", "weak", ("n", "pi_zero"), "light_baryon_neutral_isospin_outlet"),
            ("K_plus", "weak", ("mu_plus",), "semileptonic_neutrino_channel_completion"),
            ("D_plus", "weak", ("mu_plus",), "open_charm_semileptonic_neutrino_completion"),
            ("D_plus", "weak", ("K_minus", "pi_plus"), "open_charm_hadronic_monogamy_exclusion"),
            ("lambda_c", "weak", ("mu_plus",), "open_charm_semileptonic_neutrino_completion"),
            ("phi", "strong", ("K_plus", "K_minus"), "hidden_strangeness_kk_retention"),
        )
        for parent, channel, ds, kind in rows:
            self.assertEqual(
                ledger.derive_open_flavour_contact_kind(parent, channel, ds),
                kind,
                msg=f"{parent} {ds}",
            )


class TestSpineFromPropertyChannels(unittest.TestCase):
    def test_spine_lambda_npi0_matches_routing(self) -> None:
        w = sdw.spine_discharge_weight("lambda", "weak", ("n", "pi_zero"))
        kind = ledger.derive_open_flavour_contact_kind("lambda", "weak", ("n", "pi_zero"))
        self.assertAlmostEqual(w, hdr.open_flavour_contact_weight(kind))

    def test_spine_observables_lambda_no_monogamy(self) -> None:
        obs = sdw.discharge_observables("lambda", "weak", ("p", "pi_minus"))
        self.assertEqual(obs.monogamy_competition, 0)
        self.assertEqual(obs.charged_isospin_outlet, 1)


class TestKinematicReferenceFromProperties(unittest.TestCase):
    def test_kaon_lepton_reference_by_q3(self) -> None:
        import hqiv_hep_patch_species as hps

        kplus = hps.patch_from_species_id("K_plus")
        kminus = hps.patch_from_species_id("K_minus")
        assert kplus is not None and kminus is not None
        self.assertEqual(pc.certified_light_weak_kinematic_reference(kplus), ("mu_plus",))
        self.assertEqual(pc.certified_light_weak_kinematic_reference(kminus), ("mu_minus",))


if __name__ == "__main__":
    unittest.main()
