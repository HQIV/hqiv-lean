"""
**Optional** regression: literal-sum Ω vs trial-division count on **small M** only.

Not part of the default suite — run manually when you want this cross-check::

  python3 scripts/test_hqiv_geometric_3sat_optional_omega_trial_div.py

Uses :func:`hqiv_geometric_3sat_demo.omega_big_omega_factorization` (trial division on ``M``).
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

_DEMO = Path(__file__).resolve().parent / "hqiv_geometric_3sat_demo.py"
_spec = importlib.util.spec_from_file_location("hqiv_geometric_3sat_demo", _DEMO)
_demo = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
sys.modules["hqiv_geometric_3sat_demo"] = _demo
_spec.loader.exec_module(_demo)


def test_encoding_omega_matches_trial_div_count_tiny_m() -> None:
    unsat = _demo.Formula3SAT(
        num_vars=1,
        clauses=(
            (_demo.Literal(0, False), _demo.Literal(0, False), _demo.Literal(0, False)),
            (_demo.Literal(0, True), _demo.Literal(0, True), _demo.Literal(0, True)),
        ),
    )
    Mu, _, _ = _demo.encode_formula_to_M(unsat)
    _demo.assert_omega_exact_matches_factorization(Mu, unsat)

    sat_one = _demo.Formula3SAT(
        num_vars=1,
        clauses=((_demo.Literal(0, False), _demo.Literal(0, False), _demo.Literal(0, False)),),
    )
    Ms, _, _ = _demo.encode_formula_to_M(sat_one)
    _demo.assert_omega_exact_matches_factorization(Ms, sat_one)


if __name__ == "__main__":
    test_encoding_omega_matches_trial_div_count_tiny_m()
    print("optional omega trial-div check: OK")
