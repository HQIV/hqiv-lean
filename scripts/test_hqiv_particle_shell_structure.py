#!/usr/bin/env python3
"""Tests: periodic-table shell structure derived from two axiom-level multiplicities."""

from __future__ import annotations

import unittest

import hqiv_particle_shell_structure as pss


class LonePairPartitionTests(unittest.TestCase):
    """Lone pairs / domains forced by the electron budget, not a Lewis input."""

    def test_lone_pairs_match_known_atoms(self) -> None:
        # C,N,O,F,Ne at default (capacity) bonding
        self.assertEqual(pss.lone_pair_count(6), 0)
        self.assertEqual(pss.lone_pair_count(7), 1)
        self.assertEqual(pss.lone_pair_count(8), 2)
        self.assertEqual(pss.lone_pair_count(9), 3)
        self.assertEqual(pss.lone_pair_count(10), 4)

    def test_right_side_all_four_domains(self) -> None:
        for z in (6, 7, 8, 9, 10):
            self.assertEqual(pss.steric_domain_count(z), 4)

    def test_left_side_domains_equal_valence(self) -> None:
        self.assertEqual(pss.steric_domain_count(4), 2)  # Be linear
        self.assertEqual(pss.steric_domain_count(5), 3)  # B trigonal

    def test_electron_budget_closes(self) -> None:
        # 2*lone_pairs + bonds == bonding valence for every main-group atom
        for z in range(3, 11):
            v = pss.bonding_valence_electron_count(z)
            b = pss.bonding_capacity(z)
            self.assertEqual(2 * pss.lone_pair_count(z, b) + b, v)

    def test_leftover_is_always_even(self) -> None:
        for z in range(3, 11):
            v = pss.bonding_valence_electron_count(z)
            b = pss.bonding_capacity(z)
            self.assertEqual((v - b) % 2, 0)


class MultiplicityTests(unittest.TestCase):
    def test_monogamy_pairing_is_two(self) -> None:
        self.assertEqual(pss.MONOGAMY_PAIR_MULTIPLICITY, 2)

    def test_angular_degeneracy_is_two_l_plus_one(self) -> None:
        self.assertEqual([pss.angular_degeneracy(l) for l in range(4)], [1, 3, 5, 7])

    def test_subshell_capacity_is_pairing_times_degeneracy(self) -> None:
        # s,p,d,f = 2,6,10,14 = 2(2l+1)
        self.assertEqual([pss.subshell_capacity(l) for l in range(4)], [2, 6, 10, 14])

    def test_octet_is_s_plus_p_closure(self) -> None:
        # the octet 8 is DERIVED, not a literal: cap(s)+cap(p) = 2+6
        self.assertEqual(pss.octet_capacity(), 8)
        self.assertEqual(pss.octet_capacity(), pss.subshell_capacity(0) + pss.subshell_capacity(1))


class PeriodicTableTests(unittest.TestCase):
    def test_noble_gas_closures_match_real_table(self) -> None:
        # He,Ne,Ar,Kr,Xe,Rn,Og from Madelung filling with derived capacities
        self.assertEqual(pss.noble_gas_closures(), [2, 10, 18, 36, 54, 86, 118])

    def test_madelung_order_starts_correctly(self) -> None:
        # 1s,2s,2p,3s,3p,4s,3d,4p,... by (n+l) then n
        self.assertEqual(
            pss.madelung_fill_order()[:8],
            [(1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (3, 2), (4, 1)],
        )

    def test_valence_matches_real_periodic_table(self) -> None:
        # independent ground truth: electrons outside the previous real noble gas
        # H..Ar (Z 1..18) then spot checks for K, Ca, Br, Xe
        reference = {
            1: 1, 2: 2,  # H, He
            3: 1, 4: 2, 5: 3, 6: 4, 7: 5, 8: 6, 9: 7, 10: 8,  # Li..Ne
            11: 1, 12: 2, 13: 3, 14: 4, 15: 5, 16: 6, 17: 7, 18: 8,  # Na..Ar
            19: 1, 20: 2,  # K, Ca (outside Ar core 18)
            35: 17, 36: 18,  # Br, Kr (outside Ar core 18)
            54: 18,  # Xe (outside Kr core 36)
        }
        for z, v in reference.items():
            self.assertEqual(pss.valence_electron_count(z), v, msg=f"valence at Z={z}")

    def test_max_bond_order_is_p_shell_degeneracy(self) -> None:
        # the triple-bond ceiling is the p-shell angular degeneracy (sigma + 2 pi)
        self.assertEqual(pss.max_bond_order(), 3)
        self.assertEqual(pss.max_bond_order(), pss.angular_degeneracy(1))


class BondingCapacityTests(unittest.TestCase):
    def test_capacity_is_bonds_to_nearest_closed_shell(self) -> None:
        # min(valence, octet - valence): symmetric about the half-filled shell
        cap = {1: 1, 6: 4, 7: 3, 8: 2, 9: 1, 3: 1, 4: 2, 5: 3, 10: 0}
        for z, c in cap.items():
            self.assertEqual(pss.bonding_capacity(z), c, msg=f"cap at Z={z}")

    def test_left_and_right_sides_mirror(self) -> None:
        # Li(1)↔F(1), Be(2)↔O(2), B(3)↔N(3): donate-or-accept symmetry
        self.assertEqual(pss.bonding_capacity(3), pss.bonding_capacity(9))
        self.assertEqual(pss.bonding_capacity(4), pss.bonding_capacity(8))
        self.assertEqual(pss.bonding_capacity(5), pss.bonding_capacity(7))

    def test_outer_principal_valence_post_d(self) -> None:
        # Noble residual ≠ bonding V past closed d: Ge/Ga/Sn use outer s+p.
        self.assertEqual(pss.valence_electron_count(32), 14)
        self.assertEqual(pss.outer_principal_valence(32), 4)
        self.assertEqual(pss.bonding_valence_electron_count(32), 4)
        self.assertEqual(pss.bonding_capacity(32), 4)
        self.assertEqual(pss.bonding_capacity(31), 3)  # Ga
        self.assertEqual(pss.bonding_capacity(50), 4)  # Sn
        # Open d keeps peel capacity 0 (Fe); closed d¹⁰s² Zn is p-block cap=2.
        self.assertEqual(pss.bonding_capacity(26), 0)
        self.assertEqual(pss.bonding_capacity(29), 0)  # Cu open d
        self.assertEqual(pss.bonding_capacity(30), 2)  # Zn

    def test_geometric_bond_order_unifies_homo_and_hetero(self) -> None:
        import math
        # homonuclear collapses to cap (sqrt(c*c)=c): N2=3, O2=2, F2=1
        self.assertAlmostEqual(pss.geometric_bond_order(3, 3), 3.0)
        self.assertAlmostEqual(pss.geometric_bond_order(2, 2), 2.0)
        self.assertAlmostEqual(pss.geometric_bond_order(1, 1), 1.0)
        # heteronuclear interpolates: CO sqrt(8), NO sqrt(6)
        self.assertAlmostEqual(pss.geometric_bond_order(4, 2), math.sqrt(8.0))
        self.assertAlmostEqual(pss.geometric_bond_order(3, 2), math.sqrt(6.0))

    def test_geometric_bond_order_capped_at_triple(self) -> None:
        # CN sqrt(12) > 3 -> clamped to the p-shell triple ceiling
        self.assertEqual(pss.geometric_bond_order(4, 3), 3.0)

    def test_generation_is_network_step_distance(self) -> None:
        # g = n + l (radial step = angular step): same shape as the shell network
        self.assertEqual(pss.shell_generation(1, 0), 1)  # 1s
        self.assertEqual(pss.shell_generation(2, 1), 3)  # 2p
        self.assertEqual(pss.shell_generation(3, 0), 3)  # 3s (same generation as 2p)

    def test_generation_capacities_are_janet_periods_with_doubling(self) -> None:
        # 2*ceil(g/2)^2 = the left-step periods, each value appearing twice (the doubling)
        self.assertEqual(pss.left_step_period_lengths(), [2, 2, 8, 8, 18, 18, 32, 32])

    def test_doubling_is_floor_ceil_pairing(self) -> None:
        # generations 2k-1 and 2k share the same capacity 2k^2
        for k in range(1, 5):
            self.assertEqual(pss.generation_capacity(2 * k - 1), 2 * k * k)
            self.assertEqual(pss.generation_capacity(2 * k), 2 * k * k)

    def test_principal_shell_capacity_is_two_n_squared(self) -> None:
        # Sum_{l<n} 2(2l+1) = 2 n^2 (the 2n^2 rule, particle-derived)
        for n in range(1, 6):
            total = sum(pss.subshell_capacity(l) for l in range(n))
            self.assertEqual(total, 2 * n * n)


if __name__ == "__main__":
    unittest.main()
