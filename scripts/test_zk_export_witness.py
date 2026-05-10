#!/usr/bin/env python3
"""Sanity checks for zk_factor_steps/export_witness.py."""

from __future__ import annotations

import sys
import unittest
from fractions import Fraction
from pathlib import Path

_ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(_ROOT / "zk_factor_steps"))
sys.path.insert(0, str(_ROOT))

import export_witness as ez  # noqa: E402


class TestZkExportWitness(unittest.TestCase):
    def test_large_example_step_and_factor_bits(self) -> None:
        """Semiprime 118472447 = 9319 * 12713 (~14-bit factors); mask step 25."""
        payload = ez.export_payload(
            ez.EXAMPLE_LARGE_N,
            curvature=Fraction(0, 1),
            phi=ez.EXAMPLE_LARGE_PHI,
            t=ez.EXAMPLE_LARGE_T,
            window=ez.EXAMPLE_LARGE_WINDOW,
            arity=2,
            omega_mode="rational",
            omega_imprint=None,
            phase_shell_mode="n",
            max_steps=64,
        )
        self.assertEqual(payload["meta"]["n"], 118472447)
        self.assertEqual(payload["meta"]["factor_d"], 9319)
        self.assertEqual(payload["meta"]["step_index"], 25)
        self.assertGreater(payload["meta"]["factor_d"].bit_length(), 10)
        self.assertEqual(payload["circom_input"]["step_index"], "25")

    def test_toy_221_still_reproducible(self) -> None:
        payload = ez.export_payload(
            221,
            curvature=Fraction(0, 1),
            phi=1.0,
            t=1.0,
            window=8,
            arity=2,
            omega_mode="rational",
            omega_imprint=None,
            phase_shell_mode="n",
            max_steps=64,
        )
        self.assertEqual(payload["meta"]["factor_d"], 13)
        self.assertEqual(payload["meta"]["step_index"], 12)


if __name__ == "__main__":
    unittest.main()
