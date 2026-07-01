#!/usr/bin/env python3
"""Tests for the nucleon magnetic-moment readout (derived-chemistry network on the quark graph)."""

from __future__ import annotations

import unittest
from fractions import Fraction

import hqiv_nucleon_em_readout as nem


class TestQuarkCharges(unittest.TestCase):
    def test_gell_mann_nishijima_light_quarks(self) -> None:
        self.assertEqual(nem.quark_charge("u"), Fraction(2, 3))
        self.assertEqual(nem.quark_charge("d"), Fraction(-1, 3))
        self.assertEqual(nem.quark_charge("s"), Fraction(-1, 3))

    def test_proton_charge_sums_to_one(self) -> None:
        q = sum(nem.quark_charge(f) for f in ("u", "u", "d"))
        self.assertEqual(q, Fraction(1))

    def test_neutron_charge_sums_to_zero(self) -> None:
        q = sum(nem.quark_charge(f) for f in ("u", "d", "d"))
        self.assertEqual(q, Fraction(0))


class TestSpinCoupling(unittest.TestCase):
    def test_diquark_spectator_weights(self) -> None:
        # Spin-1 doubled pair + spin-½ spectator → (+4/3, −1/3) from Clebsch² weights (2/3, 1/3).
        w_pair, w_odd = nem.spin1_diquark_spectator_weights()
        self.assertEqual(w_pair, Fraction(4, 3))
        self.assertEqual(w_odd, Fraction(-1, 3))

    def test_magneton_unit_is_trace_weight(self) -> None:
        # μ_q = 3 μ_N bare, the same weight-3 carrier count as E_bind = 3·bindingCoupling.
        self.assertEqual(nem.CONSTITUENT_MAGNETON_UNITS, Fraction(3))


class TestOctonionicDressing(unittest.TestCase):
    def test_dressing_is_one_plus_alpha_over_eight(self) -> None:
        # Monogamy α=3/5 spread over the 8 octonion directions; carrier's real axis share α/8.
        self.assertAlmostEqual(nem.MONOGAMY_ALPHA, 0.6, places=12)
        self.assertEqual(nem.OCTONION_CARRIER_DIM, 8)
        self.assertAlmostEqual(nem.CONSTITUENT_DRESSING, 1.0 + 0.6 / 8.0, places=12)

    def test_constituent_mass_is_dressed_bare(self) -> None:
        self.assertAlmostEqual(
            nem.constituent_quark_mass_mev(),
            nem.bare_constituent_quark_mass_mev() * nem.CONSTITUENT_DRESSING,
            places=9,
        )
        # ~336 MeV, between the bare m_N/3 and the textbook constituent value.
        self.assertGreater(nem.constituent_quark_mass_mev(), 330.0)
        self.assertLess(nem.constituent_quark_mass_mev(), 340.0)


class TestNucleonMoments(unittest.TestCase):
    def test_bare_proton_is_three_magnetons(self) -> None:
        # Undressed (dressing=1) recovers the parameter-free structural value exactly.
        self.assertAlmostEqual(nem.proton_moment(dressing=1.0).mu_mu_n, 3.0, places=12)

    def test_bare_neutron_is_minus_two_magnetons(self) -> None:
        # Net-neutral object carries a nonzero (negative) moment — emergent from the charged graph.
        self.assertAlmostEqual(nem.neutron_moment(dressing=1.0).mu_mu_n, -2.0, places=12)

    def test_ratio_is_minus_three_halves(self) -> None:
        # Dressing cancels in the ratio — parameter-free regardless of m_q.
        self.assertAlmostEqual(nem.proton_neutron_ratio(), -1.5, places=12)

    def test_dressed_proton_within_half_percent_of_pdg(self) -> None:
        err = abs(nem.proton_moment().mu_mu_n - nem.PDG_MU_PROTON_MU_N) / nem.PDG_MU_PROTON_MU_N
        self.assertLess(err, 0.005)

    def test_dressed_neutron_within_three_percent_of_pdg(self) -> None:
        err = abs(nem.neutron_moment().mu_mu_n - nem.PDG_MU_NEUTRON_MU_N) / abs(nem.PDG_MU_NEUTRON_MU_N)
        self.assertLess(err, 0.03)

    def test_ratio_within_three_percent_of_pdg(self) -> None:
        pdg_ratio = nem.PDG_MU_PROTON_MU_N / nem.PDG_MU_NEUTRON_MU_N
        err = abs(nem.proton_neutron_ratio() - pdg_ratio) / abs(pdg_ratio)
        self.assertLess(err, 0.03)

    def test_proton_moment_positive_neutron_negative(self) -> None:
        self.assertGreater(nem.proton_moment().mu_mu_n, 0.0)
        self.assertLess(nem.neutron_moment().mu_mu_n, 0.0)


class TestOctetClosedForm(unittest.TestCase):
    def test_octet_reproduces_nucleon(self) -> None:
        self.assertAlmostEqual(nem.octet_baryon_moment_mu_n("p"), nem.proton_moment().mu_mu_n, places=12)
        self.assertAlmostEqual(nem.octet_baryon_moment_mu_n("n"), nem.neutron_moment().mu_mu_n, places=12)

    def test_lambda_anchor_is_exact(self) -> None:
        # Λ moment = μ_s is the strange anchor, so it reproduces the anchored value exactly.
        self.assertAlmostEqual(
            nem.octet_baryon_moment_mu_n("Lambda"), nem.PDG_MU_OCTET_MU_N["Lambda"], places=12
        )

    def test_sigma_lambda_transition_is_parameter_free_closed_form(self) -> None:
        # |μ(Σ⁰→Λ)| = √3 / (1 + α/8), light sector only (no strange mass).
        import math

        self.assertAlmostEqual(
            nem.sigma_lambda_transition_mu_n(), math.sqrt(3.0) / nem.CONSTITUENT_DRESSING, places=12
        )
        err = abs(nem.sigma_lambda_transition_mu_n() - 1.61) / 1.61
        self.assertLess(err, 0.003)  # 0.08% vs PDG, parameter-free

    def test_isovector_within_one_and_half_percent(self) -> None:
        # μ_p − μ_n cancels the strange mass and the dressing-common piece → parameter-free.
        err = abs(nem.proton_neutron_isovector() - 4.706) / 4.706
        self.assertLess(err, 0.015)

    def test_hyperons_carry_additive_model_breaking(self) -> None:
        # Strange-rich baryons are predicted (Λ-anchored) but with the known ~10-22% spread.
        for name in ("Sigma+", "Sigma-", "Xi0", "Xi-"):
            pred = nem.octet_baryon_moment_mu_n(name)
            pdg = nem.PDG_MU_OCTET_MU_N[name]
            self.assertEqual(pred < 0, pdg < 0)  # sign always correct
            self.assertLess(abs(pred - pdg) / abs(pdg), 0.25)


class TestSecondOrderDecomposition(unittest.TestCase):
    def test_residual_splits_into_two_channels(self) -> None:
        d = nem.second_order_decomposition()
        # Isoscalar is the dominant miss (+~5.7%); isovector is small (-~1.2%).
        self.assertGreater(d.isoscalar_residual, 0.04)
        self.assertLess(d.isoscalar_residual, 0.07)
        self.assertGreater(d.isovector_residual, -0.02)
        self.assertLess(d.isovector_residual, 0.0)

    def test_proton_cancellation_neutron_addition(self) -> None:
        d = nem.second_order_decomposition()
        # μ_p: the two channel shifts cancel (|err| small); μ_n: they add (|err| larger).
        self.assertLess(abs(d.proton_error), 0.01)
        self.assertGreater(abs(d.neutron_error), 0.04)
        # μ_n error is ~25x the proton error — the accidental cancellation is real.
        self.assertGreater(abs(d.neutron_error) / abs(d.proton_error), 10.0)


if __name__ == "__main__":
    unittest.main()
