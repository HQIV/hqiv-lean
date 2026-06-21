#!/usr/bin/env python3
"""Valence-derived isospin slots mirror Lean `HepDecayReadout` valence theorems."""

from __future__ import annotations

import unittest

import hqiv_hep_valence_isospin as hvi


class TestHepValenceIsospin(unittest.TestCase):
    def test_baryon_sigma_c_multiplet(self) -> None:
        for key, slot in (
            ("Sigma_c+", "plus"),
            ("Sigma_c0", "zero"),
            ("Sigma_c-", "minus"),
        ):
            got = hvi.isospin_third_slot_for_entry({"key": key, "config_id": None})
            self.assertEqual(got, slot, msg=key)

    def test_baryon_xi_c_isospin(self) -> None:
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "Xi_c+", "config_id": None}),
            "halfPlus",
        )
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "Xi_c0", "config_id": None}),
            "halfMinus",
        )

    def test_meson_open_heavy_isospin(self) -> None:
        for key, slot in (
            ("D+", "halfPlus"),
            ("D0", "halfMinus"),
            ("B+", "halfPlus"),
            ("B0", "halfMinus"),
        ):
            got = hvi.isospin_third_slot_for_entry({"key": key, "config_id": None})
            self.assertEqual(got, slot, msg=key)

    def test_light_vector_isospin_overrides(self) -> None:
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "rho0", "config_id": None}),
            "zero",
        )
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "omega", "config_id": None}),
            "zero",
        )
        self.assertEqual(
            hvi.isospin_third_slot_for_entry({"key": "K*+", "config_id": None}),
            "halfPlus",
        )

    def test_bottom_sigma_multiplet(self) -> None:
        for key, slot in (
            ("Sigma_b+", "plus"),
            ("Sigma_b0", "zero"),
            ("Sigma_b-", "minus"),
        ):
            got = hvi.isospin_third_slot_for_entry({"key": key, "config_id": None})
            self.assertEqual(got, slot, msg=key)

    def test_valence_i3_arithmetic(self) -> None:
        dsc = [("d", "quark"), ("s", "quark"), ("c", "quark")]
        usc = [("u", "quark"), ("s", "quark"), ("c", "quark")]
        self.assertAlmostEqual(hvi.valence_isospin_third(dsc, structure="baryon"), -0.5)
        self.assertAlmostEqual(hvi.valence_isospin_third(usc, structure="baryon"), 0.5)
        self.assertEqual(hvi.isospin_third_slot_from_valence(dsc, structure="baryon"), "halfMinus")
        self.assertEqual(hvi.isospin_third_slot_from_valence(usc, structure="baryon"), "halfPlus")


if __name__ == "__main__":
    unittest.main()
