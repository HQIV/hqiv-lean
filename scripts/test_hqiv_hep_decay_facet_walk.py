#!/usr/bin/env python3
"""Tests for geometry-first HEP decay facet walks (OSH sparse register)."""

from __future__ import annotations

import math
import unittest

import hqiv_hep_decay_certificates as cert
import hqiv_hep_decay_facet_walk as fw
import hqiv_hep_patch_species as hps


class TestLedgerFacetEnumeration(unittest.TestCase):
    def test_lambda_weak_two_paths(self) -> None:
        paths = fw.enumerate_facet_paths("lambda", "weak")
        keys = {tuple(p.daughter_ids) for p in paths}
        self.assertEqual(keys, {("p", "pi_minus"), ("n", "pi_zero")})
        for p in paths:
            self.assertGreater(p.contact_weight, 0.0)

    def test_K_plus_weak_sparse_three(self) -> None:
        paths = fw.enumerate_facet_paths("K_plus", "weak")
        keys = {tuple(p.daughter_ids) for p in paths}
        self.assertEqual(
            keys,
            {("pi_plus",), ("pi_zero",), ("pi_plus", "pi_zero", "pi_zero")},
        )

    def test_rho_zero_strong_single_channel(self) -> None:
        paths = fw.enumerate_facet_paths("rho_zero", "strong")
        self.assertEqual(len(paths), 1)
        self.assertEqual(tuple(sorted(paths[0].daughter_ids)), ("pi_minus", "pi_plus"))

    def test_facet_paths_match_lean_lambda_certificate(self) -> None:
        parent = hps.patch_from_species_id("lambda")
        self.assertIsNotNone(parent)
        tuples = cert.certified_weak_tuples(parent)
        self.assertIsNotNone(tuples)
        facet_keys = {
            tuple(sorted(p.daughter_ids))
            for p in fw.enumerate_facet_paths("lambda", "weak")
        }
        cert_keys = {tuple(sorted(t)) for t in tuples}
        self.assertEqual(facet_keys, cert_keys)


class TestOSHFacetWalk(unittest.TestCase):
    def test_lambda_walk_produces_peaks(self) -> None:
        res = fw.run_facet_walk("lambda", "weak", osh_steps=1)
        self.assertIsNotNone(res)
        assert res is not None
        self.assertEqual(len(res.paths), 2)
        self.assertGreaterEqual(len(res.peaks), 1)
        self.assertLessEqual(res.support_len, 2 * len(res.paths) + 4)
        br_sum = sum(m["relative_branch"] for m in res.modes_payload())
        self.assertAlmostEqual(br_sum, 1.0, places=6)

    def test_encode_path_injective_on_lambda(self) -> None:
        res = fw.run_facet_walk("lambda", "weak")
        assert res is not None
        flats = [fw.encode_path_flat(i, L=res.L, channel="weak") for i in range(len(res.paths))]
        self.assertEqual(len(flats), len(set(flats)))

    def test_compare_lambda_multichannel_agrees(self) -> None:
        diag = fw.compare_with_multichannel("lambda", "weak")
        self.assertEqual(diag["only_facet"], [])
        self.assertEqual(diag["only_multichannel"], [])
        self.assertEqual(len(diag["intersection"]), 2)

    def test_24_qubit_budget_not_exceeded(self) -> None:
        res = fw.run_facet_walk("K_plus", "weak", max_qubits=24)
        self.assertIsNotNone(res)
        assert res is not None
        # Sparse support stays far below 2^24.
        self.assertLess(res.support_len, 1 << 12)


class TestMixedRadixLedger(unittest.TestCase):
    def test_ledger_mixed_radix_injective_sample(self) -> None:
        import hqiv_hep_multichannel_expansion as mc

        ledgers = [
            mc.HadronLedger(3, 0, 0, 0, 0),
            mc.HadronLedger(0, -1, 0, 0, 3),
            mc.HadronLedger(0, 1, 0, 0, 0),
        ]
        tags = [fw._ledger_mixed_radix(l) for l in ledgers]
        self.assertEqual(len(tags), len(set(tags)))


if __name__ == "__main__":
    unittest.main()
