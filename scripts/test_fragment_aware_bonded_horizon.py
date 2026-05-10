"""Tests for fragment-aware bonded-horizon prototype."""

from __future__ import annotations

import unittest

from fragment_aware_bonded_horizon import (
    BondGeometry,
    FragmentConfig,
    MoleculeConfig,
    molecule_surplus_fragment_aware_ev,
)


class TestFragmentAwareBondedHorizon(unittest.TestCase):
    def test_h2_runs(self) -> None:
        h2 = MoleculeConfig(
            "H2",
            (FragmentConfig("H", 1, 1), FragmentConfig("H", 1, 1)),
            (BondGeometry(0, 1, 0.7414),),
            4.478,
            "ref",
        )
        val = molecule_surplus_fragment_aware_ev(h2)
        self.assertGreater(val, 0.0)

    def test_degeneracy_breaks_between_hf_and_h2o(self) -> None:
        hf = MoleculeConfig(
            "HF",
            (FragmentConfig("F", 9, 9), FragmentConfig("H", 1, 1)),
            (BondGeometry(0, 1, 0.9168),),
            5.87,
            "ref",
        )
        h2o = MoleculeConfig(
            "H2O",
            (
                FragmentConfig("O", 8, 8),
                FragmentConfig("H", 1, 1),
                FragmentConfig("H", 1, 1),
            ),
            (BondGeometry(0, 1, 0.9572), BondGeometry(0, 2, 0.9572)),
            9.51,
            "ref",
        )
        self.assertNotAlmostEqual(
            molecule_surplus_fragment_aware_ev(hf),
            molecule_surplus_fragment_aware_ev(h2o),
            places=8,
        )


if __name__ == "__main__":
    unittest.main()
