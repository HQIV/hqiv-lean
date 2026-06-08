"""Tests for `nuclear_torus_casimir_float` (Python mirror of Lean S⁷ + associator perturbation)."""

from __future__ import annotations

import unittest


class TestNuclearTorusCasimirFloat(unittest.TestCase):
    def test_lambda_sum_four_matches_lean(self) -> None:
        from nuclear_torus_casimir_float import noninteracting_fermion_lambda_sum, occupation_list

        self.assertEqual(noninteracting_fermion_lambda_sum(4), 21)
        self.assertEqual(occupation_list(4), [0, 1, 1, 1])

    def test_perturbed_four(self) -> None:
        from nuclear_torus_casimir_float import perturbed_casimir_energy, octonion_associator_norm_sq
        from nuclear_torus_casimir_float import nuclear_torus_f, nuclear_torus_x, nuclear_torus_l
        from nuclear_torus_casimir_float import DEFAULT_UUD_ANGLES_RAD

        f, x, l = (
            nuclear_torus_f(DEFAULT_UUD_ANGLES_RAD),
            nuclear_torus_x(DEFAULT_UUD_ANGLES_RAD),
            nuclear_torus_l(DEFAULT_UUD_ANGLES_RAD),
        )
        a = octonion_associator_norm_sq(f, x, l)
        self.assertAlmostEqual(a, 2.0, places=12)
        self.assertAlmostEqual(perturbed_casimir_energy(4), 21.0 + 3.0 * 2.0, places=10)

    def test_first_eight_ips_length(self) -> None:
        from nuclear_torus_casimir_float import first_perturbed_ionization_ips_ev

        rows = first_perturbed_ionization_ips_ev(8)
        self.assertEqual(len(rows), 8)
        self.assertEqual(rows[0]["Z"], 1)


if __name__ == "__main__":
    unittest.main()
