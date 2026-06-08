"""Smoke test for ``hqiv_satcomp_benchmark.parse_dimacs_3cnf``."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from pathlib import Path

_scripts = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("hqiv_satcomp_benchmark", _scripts / "hqiv_satcomp_benchmark.py")
_mod = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
sys.modules["hqiv_satcomp_benchmark"] = _mod
_spec.loader.exec_module(_mod)
_g3 = _mod._g3


def test_parse_dimacs_tiny_3cnf() -> None:
    cnf = """c tiny
p cnf 2 2
1 2 -3 0
-1 -2 3 0
"""
    # Wrong: 3 vars in header but 2 vars - fix to valid 3-CNF on 3 vars
    cnf = """c tiny
p cnf 3 2
1 2 -3 0
-1 -2 3 0
"""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".cnf", delete=False) as f:
        f.write(cnf)
        p = Path(f.name)
    try:
        fm = _mod.parse_dimacs_3cnf(p)
        assert fm.num_vars == 3
        assert len(fm.clauses) == 2
        sat, _ = _g3.is_satisfiable_bruteforce(fm)
        assert sat is True
    finally:
        p.unlink(missing_ok=True)


def test_shipped_samples_sat_unsat() -> None:
    """Regression: bundled 3-CNF under data/sat_benchmarks/samples/."""
    root = Path(__file__).resolve().parents[1]
    sat_path = root / "data" / "sat_benchmarks" / "samples" / "sample_sat.cnf"
    unsat_path = root / "data" / "sat_benchmarks" / "samples" / "sample_unsat_3var_8clause.cnf"
    if not sat_path.is_file() or not unsat_path.is_file():
        return

    fm_s = _mod.parse_dimacs_3cnf(sat_path)
    s, _ = _g3.is_satisfiable_bruteforce(fm_s)
    assert s is True

    fm_u = _mod.parse_dimacs_3cnf(unsat_path)
    u, _ = _g3.is_satisfiable_bruteforce(fm_u)
    assert u is False


def test_bench_one_safe_ok_field() -> None:
    root = Path(__file__).resolve().parents[1]
    p = root / "data" / "sat_benchmarks" / "samples" / "sample_sat.cnf"
    if not p.is_file():
        return
    r = _mod._bench_one_safe(p, bruteforce_max_vars=22)
    assert r.get("ok") is True
    assert r["sat_bruteforce"] is True


if __name__ == "__main__":
    test_parse_dimacs_tiny_3cnf()
    test_shipped_samples_sat_unsat()
    test_bench_one_safe_ok_field()
    print("ok")
