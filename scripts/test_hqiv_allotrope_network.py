#!/usr/bin/env python3
"""Tests for HQIV intramolecular allotrope networks (first-principles, no fitted constants)."""

from __future__ import annotations

import math
import unittest

import hqiv_allotrope_network as an


class AllotropeCapacityTests(unittest.TestCase):
    def test_octet_capacity_is_eight_minus_valence(self) -> None:
        # shared-pair budget to complete the octet: C 4, N 3, O 2, S 2
        self.assertEqual(an.octet_shared_pair_capacity(6), 4)
        self.assertEqual(an.octet_shared_pair_capacity(7), 3)
        self.assertEqual(an.octet_shared_pair_capacity(8), 2)
        self.assertEqual(an.octet_shared_pair_capacity(16), 2)

    def test_bond_order_is_capacity_over_coordination(self) -> None:
        # diamond k=4 → 1, graphite k=3 → 4/3, carbyne k=2 → 2
        self.assertAlmostEqual(an.network_bond_order(6, 4), 1.0)
        self.assertAlmostEqual(an.network_bond_order(6, 3), 4.0 / 3.0)
        self.assertAlmostEqual(an.network_bond_order(6, 2), 2.0)

    def test_hydrogen_pinning_conserves_capacity(self) -> None:
        # benzene ring C: cap 4, one C–H pinned, two ring bonds → (4−1)/2 = 3/2 offer
        self.assertAlmostEqual(an.heavy_bond_capacity_offer(6, heavy_coordination=2, hydrogen_bonds=1), 1.5)
        # no hydrogen → reduces to the symmetric cap/k offer
        self.assertAlmostEqual(
            an.heavy_bond_capacity_offer(6, heavy_coordination=3, hydrogen_bonds=0),
            an.atom_per_bond_capacity_offer(6, 3),
        )


class AromaticNetworkTests(unittest.TestCase):
    def _ring(self, z_ring, h_on):
        n = len(z_ring)
        z = list(z_ring)
        edges = [(i, (i + 1) % n) for i in range(n)]
        for i, has_h in enumerate(h_on):
            if has_h:
                edges.append((i, len(z)))
                z.append(1)
        return z, edges

    def test_benzene_ring_is_aromatic_one_and_a_half(self) -> None:
        z, e = self._ring([6] * 6, [True] * 6)
        net = an.analyze_network("benzene", z, e)
        cc = [b.bond_order for b in net.bonds if b.z_i == 6 and b.z_j == 6]
        self.assertEqual(len(cc), 6)
        for order in cc:
            self.assertAlmostEqual(order, 1.5)

    def test_benzene_ch_bonds_are_single(self) -> None:
        z, e = self._ring([6] * 6, [True] * 6)
        net = an.analyze_network("benzene", z, e)
        ch = [b.bond_order for b in net.bonds if 1 in (b.z_i, b.z_j)]
        self.assertEqual(len(ch), 6)
        for order in ch:
            self.assertAlmostEqual(order, 1.0)

    def test_benzene_centres_are_sp2_120(self) -> None:
        z, e = self._ring([6] * 6, [True] * 6)
        net = an.analyze_network("benzene", z, e)
        for a in net.central_angles_deg:
            self.assertAlmostEqual(a, 120.0, places=3)


class BondCouplingTests(unittest.TestCase):
    """Bond order = saturated 2×2 coupling, not a posited geometric mean."""

    def test_geometric_mean_saturates_det_zero(self) -> None:
        for oi, oj in [(1.0, 1.0), (2.0, 1.0), (4.0, 2.0), (1.5, 1.5)]:
            b = an.coherent_bond_order(oi, oj)
            self.assertAlmostEqual(an.bond_channel_determinant(oi, oj, b), 0.0, places=12)

    def test_sub_saturated_sharing_has_positive_det(self) -> None:
        # any coherence < 1 leaves an open (PSD, det>0) channel — fewer fully-shared pairs
        oi, oj = 4.0, 2.0
        m = an.bond_coupling_matrix(oi, oj, coherence=0.5)
        b = m[0][1]
        self.assertLess(b, an.coherent_bond_order(oi, oj))
        self.assertGreater(an.bond_channel_determinant(oi, oj, b), 0.0)

    def test_homonuclear_collapses_to_offer(self) -> None:
        for o in [1.0, 1.5, 2.0, 3.0]:
            self.assertAlmostEqual(an.coherent_bond_order(o, o), o, places=12)

    def test_order_never_exceeds_geometric_mean(self) -> None:
        # Cauchy–Schwarz bound: coupling can't beat the geometric mean
        for c in [0.0, 0.3, 0.7, 1.0]:
            b = an.bond_coupling_matrix(4.0, 2.0, coherence=c)[0][1]
            self.assertLessEqual(b, an.coherent_bond_order(4.0, 2.0) + 1e-12)


class BalancedContactTests(unittest.TestCase):
    """The VSEPR angle is an OUTPUT of balance (∑v=0) + symmetry, not an input."""

    def test_measured_cos_matches_derived(self) -> None:
        for d in range(2, 8):
            self.assertAlmostEqual(an.measured_contact_cos(d), an.balanced_unit_contact_cos(d), places=9)
            self.assertAlmostEqual(an.balanced_unit_contact_cos(d), -1.0 / (d - 1), places=12)

    def test_constructed_frame_is_in_equilibrium(self) -> None:
        for d in range(2, 8):
            self.assertAlmostEqual(an.balance_residual_norm(d), 0.0, places=9)

    def test_canonical_angles_emerge(self) -> None:
        self.assertAlmostEqual(an.ideal_hybridization_angle_deg(2), 180.0, places=6)
        self.assertAlmostEqual(an.ideal_hybridization_angle_deg(3), 120.0, places=6)
        self.assertAlmostEqual(an.ideal_hybridization_angle_deg(4), 109.4712, places=3)


class RingStrainTests(unittest.TestCase):
    def test_polygon_interior_angles(self) -> None:
        self.assertAlmostEqual(an.polygon_interior_angle_deg(3), 60.0)
        self.assertAlmostEqual(an.polygon_interior_angle_deg(5), 108.0)
        self.assertAlmostEqual(an.polygon_interior_angle_deg(6), 120.0)

    def test_sp2_hexagon_is_strain_free(self) -> None:
        # benzene: trigonal 120° matches the hexagon interior exactly
        self.assertAlmostEqual(an.ring_angular_strain_deg(6, 3), 0.0, places=6)

    def test_sp3_pentagon_is_nearly_strain_free(self) -> None:
        # furanose: tetrahedral 109.47° vs pentagon 108° ≈ 1.47°
        self.assertLess(abs(an.ring_angular_strain_deg(5, 4)), 2.0)

    def test_minimal_strain_ring_sizes(self) -> None:
        self.assertEqual(an.minimal_strain_ring_size(3), 6)  # sp2 → benzene six-ring
        self.assertEqual(an.minimal_strain_ring_size(4), 5)  # sp3 → furanose five-ring

    def test_coordination_spectrum_is_the_allotrope_family(self) -> None:
        # carbon admits k = 2,3,4 (carbyne/graphite/diamond): 1 ≤ cap/k ≤ 3
        self.assertEqual(an.allowed_coordinations(6), (2, 3, 4))
        # nitrogen admits k = 1,2,3 (N2 triple, azo 1.5, trivalent single)
        self.assertEqual(an.allowed_coordinations(7), (1, 2, 3))
        # oxygen admits k = 1,2 (O2 double, single-bond network)
        self.assertEqual(an.allowed_coordinations(8), (1, 2))


class AllotropeAngleTests(unittest.TestCase):
    def test_carbon_angles_are_exact_vsepr(self) -> None:
        # the σ-framework angles are exact: sp³ 109.47°, sp² 120°, sp 180°
        self.assertAlmostEqual(an.network_bond_angle_deg(6, 4), math.degrees(math.acos(-1.0 / 3.0)), places=6)
        self.assertAlmostEqual(an.network_bond_angle_deg(6, 3), 120.0, places=6)
        self.assertAlmostEqual(an.network_bond_angle_deg(6, 2), 180.0, places=6)

    def test_sulfur_ring_angle_is_tetrahedral_from_two_lone_pairs(self) -> None:
        # S8: k=2 bonds + 2 lone pairs = 4 domains → 109.47° (real S8 ≈ 108°)
        self.assertEqual(an.network_lone_pair_count(16, 2), 2)
        self.assertAlmostEqual(an.network_bond_angle_deg(16, 2), math.degrees(math.acos(-1.0 / 3.0)), places=6)

    def test_diatomic_has_no_angle(self) -> None:
        # a single bond (k=1) has no angle
        self.assertIsNone(an.network_bond_angle_deg(8, 1))
        self.assertIsNone(an.network_bond_angle_deg(7, 1))


class AllotropeLengthTests(unittest.TestCase):
    def test_higher_bond_order_contracts_the_bond(self) -> None:
        # carbon: diamond (bo 1) longer than graphite (bo 4/3) longer than carbyne (bo 2)
        r4 = an.network_bond_length_angstrom(6, 4)
        r3 = an.network_bond_length_angstrom(6, 3)
        r2 = an.network_bond_length_angstrom(6, 2)
        self.assertGreater(r4, r3)
        self.assertGreater(r3, r2)

    def test_length_scale_law_matches_integer_multiple_bonds(self) -> None:
        # with a single-bond reference the contraction law reproduces double/triple ratios:
        # double ~0.89, triple ~0.80 (validated against C single/double/triple 1.54/1.34/1.20)
        self.assertAlmostEqual(an.fractional_length_scale(2.0), 1.0 / (1.0 + 0.5 / 4.0), places=9)
        self.assertAlmostEqual(an.fractional_length_scale(1.0), 1.0)
        # graphite/diamond ratio is a clean (base-free) prediction in the right direction
        ratio = an.network_bond_length_angstrom(6, 3) / an.network_bond_length_angstrom(6, 4)
        self.assertLess(ratio, 1.0)
        self.assertGreater(ratio, 0.90)

    def test_period3_length_flagged_unreliable(self) -> None:
        # absolute length only trustworthy for period ≤ 2 (nested-WF radius gap above)
        self.assertTrue(an.length_is_reliable(6))
        self.assertFalse(an.length_is_reliable(16))


class BondResolvedTests(unittest.TestCase):
    def test_per_bond_offer_is_capacity_over_own_coordination(self) -> None:
        # terminal O (k=1) offers its full capacity 2; central O (k=2) offers 1
        self.assertAlmostEqual(an.atom_per_bond_capacity_offer(8, 1), 2.0)
        self.assertAlmostEqual(an.atom_per_bond_capacity_offer(8, 2), 1.0)

    def test_symmetric_bond_reduces_to_cap_over_k(self) -> None:
        # geometric mean of two equal offers is the common cap/k (diamond, graphite, O2)
        for z, k in [(6, 4), (6, 3), (8, 1)]:
            self.assertAlmostEqual(
                an.resolved_bond_order(z, k, z, k), an.network_bond_order(z, k)
            )

    def test_ozone_bond_order_is_geometric_mean_between_single_and_double(self) -> None:
        # O3: terminal offer 2, central offer 1 -> sqrt(2) ~ 1.41, strictly in (1, 2)
        bo = an.resolved_bond_order(8, 1, 8, 2)
        self.assertAlmostEqual(bo, math.sqrt(2.0))
        self.assertGreater(bo, 1.0)
        self.assertLess(bo, 2.0)

    def test_co2_resolves_to_double_bonds(self) -> None:
        # C(k=2) offers 4/2=2, O(k=1) offers 2/1=2 -> sqrt(4)=2 (O=C=O)
        self.assertAlmostEqual(an.resolved_bond_order(6, 2, 8, 1), 2.0)

    def test_geometric_mean_brackets_the_two_offers(self) -> None:
        # min(offer_i, offer_j) <= bond order <= max(offer_i, offer_j)
        oi = an.atom_per_bond_capacity_offer(8, 1)
        oj = an.atom_per_bond_capacity_offer(8, 2)
        bo = an.resolved_bond_order(8, 1, 8, 2)
        self.assertGreaterEqual(bo, min(oi, oj))
        self.assertLessEqual(bo, max(oi, oj))

    def test_network_coordination_is_graph_degree(self) -> None:
        # O3 / CO2 chain: terminal degree 1, central degree 2
        ro = an.analyze_network("O3", [8, 8, 8], [(0, 1), (1, 2)])
        self.assertEqual(ro.coordinations, (1, 2, 1))

    def test_co2_central_angle_is_linear(self) -> None:
        ro = an.analyze_network("CO2", [8, 6, 8], [(0, 1), (1, 2)])
        self.assertEqual(len(ro.central_angles_deg), 1)
        self.assertAlmostEqual(ro.central_angles_deg[0], 180.0, places=6)


class AllotropePayloadTests(unittest.TestCase):
    def setUp(self) -> None:
        self.payload = an.build_payload()
        self.rows = self.payload["rows"]

    def test_no_fitted_coefficients_policy(self) -> None:
        self.assertEqual(self.payload["parameter_policy"], "no_fitted_coefficients")

    def test_networks_resolve_ozone_and_co2(self) -> None:
        nets = {n["name"]: n for n in self.payload["networks"]}
        self.assertIn("O3 ozone (bent)", nets)
        self.assertLess(abs(nets["O3 ozone (bent)"]["bond_order"] - math.sqrt(2.0)), 1e-9)
        self.assertLess(abs(nets["CO2 (O=C=O)"]["bond_order"] - 2.0), 1e-9)
        self.assertLess(abs(nets["CO2 (O=C=O)"]["angle_error_deg"]), 1e-6)

    def test_carbon_allotropes_present_with_exact_angles(self) -> None:
        carbon = {r["name"]: r for r in self.rows if r["element_z"] == 6}
        self.assertIn("diamond (sp3)", carbon)
        self.assertIn("graphite/graphene (sp2)", carbon)
        # diamond 109.47° vs the rounded 109.5° guardrail; graphite exact 120°
        self.assertLess(abs(carbon["diamond (sp3)"]["angle_error_deg"]), 0.05)
        self.assertLess(abs(carbon["graphite/graphene (sp2)"]["angle_error_deg"]), 0.01)


if __name__ == "__main__":
    unittest.main()
