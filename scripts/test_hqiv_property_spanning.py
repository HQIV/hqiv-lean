#!/usr/bin/env python3
"""Property-generated spanning sets agree with Lean regression oracles."""

from __future__ import annotations

import unittest

import hqiv_hep_decay_certificates as cert
import hqiv_hep_patch_species as hps
import hqiv_property_spanning as ps


def _patch_keys(modes: tuple[tuple[str, ...], ...]) -> frozenset:
    return frozenset(ps._span_dedup_key(m) for m in modes)


class TestPropertyWeakSpanning(unittest.TestCase):
    def _assert_span_matches_oracle(self, parent_id: str, oracle: tuple[tuple[str, ...], ...]) -> None:
        parent = hps.patch_from_species_id(parent_id)
        assert parent is not None
        span = ps.enumerate_weak_span(parent)
        self.assertEqual(_patch_keys(span), _patch_keys(oracle), parent_id)
        self.assertEqual(_patch_keys(cert.certified_weak_tuples(parent) or ()), _patch_keys(oracle))

    def test_lambda_weak(self) -> None:
        self._assert_span_matches_oracle("lambda", cert.LAMBDA_WEAK)

    def test_K_plus_weak(self) -> None:
        self._assert_span_matches_oracle("K_plus", cert.K_PLUS_WEAK)

    def test_K0_weak(self) -> None:
        self._assert_span_matches_oracle("K0", cert.K0_WEAK)

    def test_K_minus_weak(self) -> None:
        self._assert_span_matches_oracle("K_minus", cert.K_MINUS_WEAK)

    def test_lambda_c_weak(self) -> None:
        self._assert_span_matches_oracle("lambda_c", cert.LAMBDA_C_WEAK)

    def test_Bs_weak(self) -> None:
        self._assert_span_matches_oracle("Bs", cert.BS_WEAK)

    def test_Ds_weak(self) -> None:
        self._assert_span_matches_oracle("Ds_plus", cert.DS_WEAK)

    def test_xi_c_weak(self) -> None:
        self._assert_span_matches_oracle("xi_c", cert.XI_C_WEAK)

    def test_D_plus_weak(self) -> None:
        self._assert_span_matches_oracle("D_plus", cert.D_PLUS_WEAK)

    def test_D0_weak(self) -> None:
        self._assert_span_matches_oracle("D0", cert.D0_WEAK)

    def test_B_plus_weak(self) -> None:
        self._assert_span_matches_oracle("B_plus", cert.B_PLUS_WEAK)

    def test_B0_weak(self) -> None:
        self._assert_span_matches_oracle("B0", cert.B0_WEAK)


class TestPropertyStrongSpanning(unittest.TestCase):
    def _assert_span_matches_oracle(self, parent_id: str, oracle: tuple[tuple[str, ...], ...]) -> None:
        parent = hps.patch_from_species_id(parent_id)
        assert parent is not None
        span = ps.enumerate_strong_span(parent)
        self.assertEqual(_patch_keys(span), _patch_keys(oracle), parent_id)

    def test_phi_strong(self) -> None:
        self._assert_span_matches_oracle("phi", cert.PHI_STRONG)

    def test_rho_zero_strong(self) -> None:
        self._assert_span_matches_oracle("rho_zero", cert.RHO_ZERO_STRONG)

    def test_delta_p_strong(self) -> None:
        self._assert_span_matches_oracle("delta_p", cert.DELTA_P_STRONG)

    def test_sigma_plus_strong(self) -> None:
        self._assert_span_matches_oracle("sigma_plus", cert.SIGMA_PLUS_STRONG)

    def test_xi_minus_strong(self) -> None:
        self._assert_span_matches_oracle("xi_minus", cert.XI_MINUS_STRONG)


class TestPropertyQuarkoniumCascade(unittest.TestCase):
    def test_upsilon_neutral_cascade(self) -> None:
        parent = hps.patch_from_species_id("Upsilon")
        assert parent is not None
        span = ps.enumerate_quarkonium_cascade_span(parent)
        self.assertEqual(_patch_keys(span), _patch_keys(cert.UPSILON_NEUTRAL_CASCADE))


if __name__ == "__main__":
    unittest.main()
