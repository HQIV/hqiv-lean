#!/usr/bin/env python3
"""
Algebraic mass-operator probes on the HQIV Kronecker γ / `Cl(0,6)` spinor model.

* **ρ:** single-generator masks `2^k` and monomials match Lean `spinorGammaMonomialMat` /
  `cl06StandardSpinorRho` on `ι(eₖ)`.
* **φ ladder:** matches `phi_of_shell m = phiTemperatureCoeff * (m+1)` from
  `Hqiv/Geometry/AuxiliaryField.lean` / `HarmonicLadderGlobalDetuning` (`phiTemperatureCoeff = 2`).
  Use `--phi-mode shell --phi-shell m` so the additive shift is `φ(m)` (not a free knob).
* **Triality (monomial ℝ⁶⁴ basis):** orthogonal projectors onto column spans of `V` restricted to
  monomial indices grouped by `j % 3` or `popcount(j) % 3`, then score **per-channel** largest
  singular values of `P T P` (for 64×64 `T`, or `T =` left-mult lift of an 8×8 `H`).
* **8×8 secondary metrics** (internal diagnostics): `trace`, `det`, `condition_number`,
  `frobenius_norm_off_diagonal`.

Lean anchors (`Hqiv/Physics/MassFromSpinorRho.lean`):
`spinorBivectorCommutatorSqSumMat`, `manifoldMassOp8`, `manifoldMassOp64LeftMult`.

**Manifold operator:** `ζ_c·α·sym(γᵢγⱼ) + λ·ζ_p·(φ(m)/6)·Δ` (`α = 3/5`, unit `Δ`).  Default pair `(i,j)=(0,1)`,
`λ = 1`, `ζ_c = ζ_p = 1`.  Use `--manifold-bivector-sweep` for all `0 ≤ i < j ≤ 5`, or
`--manifold-pairs "0,1;1,5;0,5"`.  `--lambda-mix` / `--lambda-sweep` tune the Δ coupling.
`--zeta-curvature` / `--zeta-phase` attach `ζ(3)` or `ζ(8)` from `mpmath` (fallback hard-coded).

**Primary ranking:** default `--comparison-mode hqiv --rank-metric hqiv_internal` uses only internal
spectral shape, shell scale, and triality-projected diagnostics. External PDG-style mass yardsticks are
available only with `--comparison-mode external`; they are comparison outputs, not promoted HQIV
selection criteria.

Examples:

    python3 scripts/spinor_mass_operator_reality_probe.py --score ratio
    python3 scripts/spinor_mass_operator_reality_probe.py --comparison-mode external --rank-metric tri_mod3_quark --score ratio
    python3 scripts/spinor_mass_operator_reality_probe.py --phi-mode shell --phi-shell 4 --manifold-bivector-sweep --lambda-sweep 0.5,1.0,1.5
    python3 scripts/spinor_mass_operator_reality_probe.py --manifold-pairs "1,5;0,5" --zeta-phase z3
    python3 scripts/spinor_mass_operator_reality_probe.py --json --phi-sweep --phi-sweep-max 6
"""

from __future__ import annotations

import argparse
import importlib.util
import itertools
import json
import math
import sys
from functools import partial
from pathlib import Path
from typing import Any, Callable, Literal

import numpy as np

# --- HQIV auxiliary φ (same closed form as Lean `phi_of_shell_closed_form`) ------------

PHI_TEMPERATURE_COEFF: float = 2.0

# Curvature imprint α = 3/5 (`Hqiv.Geometry.OctonionicLightCone.alpha_eq_3_5`).
ALPHA_CURVATURE: float = 3.0 / 5.0

# Lock-in reference shell (`Hqiv.referenceM = 4`), used only for internal scale diagnostics.
REFERENCE_SHELL_M: int = 4

ComparisonMode = Literal["hqiv", "external"]


def phi_of_shell(m: int) -> float:
    """φ(m) = phiTemperatureCoeff * (m + 1), shell index `m : ℕ`."""
    return PHI_TEMPERATURE_COEFF * float(m + 1)


def zeta_constants() -> tuple[float, float]:
    """(ζ(3), ζ(8)) for optional curvature/phase scaling."""
    try:
        import mpmath as mp  # type: ignore

        return float(mp.zeta(3)), float(mp.zeta(8))
    except Exception:
        return 1.2020569031595942, 1.004077356197935


def zeta_multiplier(flag: str) -> float:
    """`none` → 1; `z3` / `z8` → ζ(3) / ζ(8)."""
    z3, z8 = zeta_constants()
    if flag in ("", "none"):
        return 1.0
    if flag == "z3":
        return z3
    if flag == "z8":
        return z8
    raise ValueError(f"unknown zeta flag: {flag!r}")


def parse_ij_pairs(s: str | None, sweep_all: bool) -> list[tuple[int, int]]:
    if sweep_all:
        return [(i, j) for i in range(6) for j in range(i + 1, 6)]
    if not s or not s.strip():
        return [(0, 1)]
    out: list[tuple[int, int]] = []
    for part in s.split(";"):
        part = part.strip()
        if not part:
            continue
        a, b = part.split(",")
        ij = (int(a.strip()), int(b.strip()))
        if ij[0] == ij[1] or not (0 <= ij[0] < 6 and 0 <= ij[1] < 6):
            raise ValueError(f"invalid bivector pair: {part!r}")
        i, j = min(ij), max(ij)
        out.append((i, j))
    return out


def parse_lambda_list(sweep_s: str | None, single: float) -> list[float]:
    if sweep_s and sweep_s.strip():
        return [float(x.strip()) for x in sweep_s.split(",") if x.strip()]
    return [float(single)]


# --- External yardsticks (GeV; opt-in only, never a promoted HQIV selector) ----------

PDG_QUARK_GEV = {
    "up": 2.16e-3,
    "charm": 1.27,
    "top": 172.57,
    "down": 4.67e-3,
    "strange": 0.0934,
    "bottom": 4.18,
}

PDG_LEPTON_GEV = {
    "electron": 0.000511,
    "muon": 0.10566,
    "tau": 1.77686,
}

PDG_NU_ROUGH_GEV = {
    "nu1": 1e-11,
    "nu2": 8e-4 * 1e-9,
    "nu3": 0.05 * 1e-9,
}


def _log_triple(a: float, b: float, c: float) -> np.ndarray:
    v = np.array([math.log(a), math.log(b), math.log(c)], dtype=np.float64)
    return v - v.mean()


def best_perm_score(ref: np.ndarray, cand: np.ndarray) -> tuple[float, tuple[int, ...]]:
    best = float("inf")
    best_p: tuple[int, ...] = (0, 1, 2)
    for p in itertools.permutations((0, 1, 2)):
        d = ref - cand[list(p)]
        s = float(np.linalg.norm(d))
        if s < best:
            best = s
            best_p = p
    return best, best_p


def top3_singular_values(S: np.ndarray) -> np.ndarray:
    s = np.linalg.svd(S, compute_uv=False)
    s.sort()
    return s[-3:]


def ratio_pair_log_score(
    sig: np.ndarray,
    m_light: float,
    m_mid: float,
    m_heavy: float,
) -> float:
    s = np.sort(np.clip(sig, 1e-300, None))
    s1, s2, s3 = float(s[0]), float(s[1]), float(s[2])
    if s3 <= 0:
        return float("inf")
    pred = np.array([math.log(s2 / s3), math.log(s1 / s3)], dtype=np.float64)
    ref = np.array(
        [math.log(m_mid / m_heavy), math.log(m_light / m_heavy)], dtype=np.float64
    )
    return float(np.linalg.norm(pred - ref))


def hqiv_internal_spectral_scores(sig: np.ndarray, *, phi_scale: float) -> dict[str, float]:
    """Internal, dimensionless diagnostics with no external mass tables."""
    s = np.sort(np.clip(np.asarray(sig, dtype=np.float64), 1e-300, None))
    if s.size == 0:
        return {
            "hqiv_internal_score": float("inf"),
            "hqiv_log_spread": float("inf"),
            "hqiv_shell_scale_score": float("inf"),
        }
    top = s[-min(3, s.size) :]
    logs = np.log(top)
    centered = logs - logs.mean()
    spread = float(np.linalg.norm(centered))
    shell_scale = max(abs(float(phi_scale)), phi_of_shell(REFERENCE_SHELL_M), 1.0)
    geomean = float(math.exp(float(logs.mean())))
    shell_scale_score = abs(math.log(max(geomean, 1e-300) / shell_scale))
    return {
        "hqiv_internal_score": spread + 0.1 * shell_scale_score,
        "hqiv_log_spread": spread,
        "hqiv_shell_scale_score": shell_scale_score,
    }


def secondary_metrics_8x8(H: np.ndarray) -> dict[str, float]:
    """Diagnostics on ℝ⁸×⁸ operators (ρ-native tiebreakers)."""
    tr = float(np.trace(H))
    dt = float(np.linalg.det(H))
    off = H.copy()
    np.fill_diagonal(off, 0.0)
    fro_off = float(np.linalg.norm(off, ord="fro"))
    w = np.linalg.svd(H, compute_uv=False)
    smin = float(np.min(np.abs(w[np.abs(w) > 1e-15])))
    smax = float(np.max(np.abs(w)))
    cond = float("inf") if smin < 1e-15 else smax / smin
    return {
        "trace": tr,
        "det": dt,
        "condition_number": cond,
        "frobenius_norm_off_diagonal": fro_off,
    }


def triality_channel_label(j: int, split: Literal["mod3", "hamming3"]) -> int:
    if split == "mod3":
        return j % 3
    return _popcount6(j) % 3


def _popcount6(x: int) -> int:
    c = 0
    while x:
        c += x & 1
        x >>= 1
    return c


def triality_projectors_from_V(
    Vcols: np.ndarray, split: Literal["mod3", "hamming3"]
) -> list[np.ndarray]:
    """Orthogonal projectors `P_r` onto span of monomial columns in channel `r` (uses LI / full column rank per block)."""
    out: list[np.ndarray] = []
    for r in range(3):
        idx = [j for j in range(64) if triality_channel_label(j, split) == r]
        if not idx:
            out.append(np.zeros((64, 64), dtype=np.float64))
            continue
        A = Vcols[:, idx]
        q, _ = np.linalg.qr(A, mode="reduced")
        pr = q @ q.T
        out.append(pr)
    return out


def left_mult_matrix_64(H: np.ndarray, mats64: np.ndarray) -> np.ndarray:
    """64×64 matrix of `M ↦ H M` in row-major monomial coordinates."""
    return np.column_stack([row_major_flat(H @ mats64[j]) for j in range(64)])


def largest_singular_value(S: np.ndarray) -> float:
    if S.size == 0:
        return 0.0
    w = np.linalg.svd(S, compute_uv=False)
    return float(np.max(w)) if w.size else 0.0


def triality_triple_scores(
    T: np.ndarray,
    projectors: list[np.ndarray],
    *,
    phi_scale: float,
    comparison_mode: ComparisonMode,
) -> dict[str, Any]:
    """Largest SV of each projected block; external mass-table comparisons are opt-in."""
    n = T.shape[0]
    tb = T + float(phi_scale) * np.eye(n, dtype=np.float64)
    sigs = []
    for pr in projectors:
        blk = pr @ tb @ pr
        sigs.append(largest_singular_value(blk))
    ev = np.array(sorted(sigs), dtype=np.float64)
    internal = hqiv_internal_spectral_scores(ev, phi_scale=phi_scale)
    if np.any(ev <= 0) or ev.size < 3:
        out = {
            "largest_sv": sigs,
            **internal,
        }
        if comparison_mode == "external":
            out.update(
                {
                    "quark_perm": float("inf"),
                    "quark_ratio": float("inf"),
                    "lepton_perm": float("inf"),
                    "lepton_ratio": float("inf"),
                }
            )
        return out
    out = {
        "largest_sv": sigs,
        **internal,
    }
    if comparison_mode == "external":
        eps = 1e-300
        le = np.log(ev + eps) - np.log(ev + eps).mean()
        u, c, t = PDG_QUARK_GEV["up"], PDG_QUARK_GEV["charm"], PDG_QUARK_GEV["top"]
        e, mu, tau = (
            PDG_LEPTON_GEV["electron"],
            PDG_LEPTON_GEV["muon"],
            PDG_LEPTON_GEV["tau"],
        )
        ref_u = _log_triple(u, c, t)
        ref_l = _log_triple(e, mu, tau)
        sq, pq = best_perm_score(ref_u, le)
        sl, pl = best_perm_score(ref_l, le)
        out.update(
            {
                "quark_perm": sq,
                "quark_ratio": ratio_pair_log_score(ev, u, c, t),
                "lepton_perm": sl,
                "lepton_ratio": ratio_pair_log_score(ev, e, mu, tau),
                "perm_up": list(pq),
                "perm_lepton": list(pl),
            }
        )
    return out


def score_operator(
    S: np.ndarray, *, phi_scale: float, comparison_mode: ComparisonMode
) -> dict[str, Any]:
    n = S.shape[0]
    sb = S + float(phi_scale) * np.eye(n, dtype=np.float64)
    ev = top3_singular_values(sb)
    internal = hqiv_internal_spectral_scores(ev, phi_scale=phi_scale)
    eps = 1e-300
    if np.any(ev <= 0):
        out = {
            "singular_values": ev.tolist(),
            "phi_scale": phi_scale,
            "comparison_mode": comparison_mode,
            "note": "degenerate_spectrum",
            **internal,
        }
        if comparison_mode == "external":
            out.update(
                {
                    "quark_perm_sum": float("inf"),
                    "quark_ratio_sum": float("inf"),
                    "lepton_perm_sum": float("inf"),
                    "lepton_ratio_sum": float("inf"),
                    "nu_perm_sum": float("inf"),
                    "nu_ratio_sum": float("inf"),
                }
            )
        return out

    out = {
        "singular_values": ev.tolist(),
        "phi_scale": phi_scale,
        "comparison_mode": comparison_mode,
        **internal,
    }
    if comparison_mode != "external":
        return out

    le = np.log(ev + eps)
    le = le - le.mean()

    ref_up = _log_triple(PDG_QUARK_GEV["up"], PDG_QUARK_GEV["charm"], PDG_QUARK_GEV["top"])
    ref_dn = _log_triple(
        PDG_QUARK_GEV["down"], PDG_QUARK_GEV["strange"], PDG_QUARK_GEV["bottom"]
    )
    su, pu = best_perm_score(ref_up, le)
    sd, pd = best_perm_score(ref_dn, le)
    q_perm = su + sd

    u, c, t = PDG_QUARK_GEV["up"], PDG_QUARK_GEV["charm"], PDG_QUARK_GEV["top"]
    d, s, b = PDG_QUARK_GEV["down"], PDG_QUARK_GEV["strange"], PDG_QUARK_GEV["bottom"]
    q_ratio = ratio_pair_log_score(ev, u, c, t) + ratio_pair_log_score(ev, d, s, b)

    e, mu, tau = (
        PDG_LEPTON_GEV["electron"],
        PDG_LEPTON_GEV["muon"],
        PDG_LEPTON_GEV["tau"],
    )
    ref_l = _log_triple(e, mu, tau)
    sl, pl = best_perm_score(ref_l, le)
    l_ratio = ratio_pair_log_score(ev, e, mu, tau)

    n1, n2, n3 = PDG_NU_ROUGH_GEV["nu1"], PDG_NU_ROUGH_GEV["nu2"], PDG_NU_ROUGH_GEV["nu3"]
    ref_n = _log_triple(n1, n2, n3)
    sn, pn = best_perm_score(ref_n, le)
    n_ratio = ratio_pair_log_score(ev, n1, n2, n3)

    out.update(
        {
        "quark_perm_sum": q_perm,
        "quark_ratio_sum": q_ratio,
        "perm_up": list(pu),
        "perm_down": list(pd),
        "lepton_perm_sum": sl,
        "lepton_ratio_sum": l_ratio,
        "perm_lepton": list(pl),
        "nu_perm_sum": sn,
        "nu_ratio_sum": n_ratio,
        "perm_nu": list(pn),
        }
    )
    return out


def dim_label(shape: tuple[int, ...]) -> str:
    if shape == (3, 3):
        return "3"
    if shape == (8, 8):
        return "8"
    if shape == (64, 64):
        return "64"
    return f"{shape[0]}x{shape[1]}"


def tiebreak_8x8(sec: dict[str, float]) -> float:
    """Lexicographic scalar for sorting (smaller preferred): cond, -|trace|, fro_off."""
    c = sec["condition_number"]
    if math.isinf(c):
        c = 1e300
    return c + 0.01 * abs(sec["trace"]) + 0.001 * sec["frobenius_norm_off_diagonal"]


def primary_rank_value(r: dict[str, Any], metric: str) -> float:
    """Lower is better. Uses triality keys from `enrich_method_row` (`tri_mod3_*`, `tri_ham_*`)."""

    def g(key: str) -> float:
        v = r.get(key)
        if v is None:
            return 1e300
        if isinstance(v, float) and math.isnan(v):
            return 1e300
        x = float(v)
        return 1e300 if math.isinf(x) and x > 0 else x

    if metric == "hqiv_internal":
        return g("hqiv_internal_score")
    if metric == "tri_mod3_internal":
        return g("tri_mod3_hqiv_internal_score")
    if metric == "tri_ham_internal":
        return g("tri_ham_hqiv_internal_score")
    if metric == "tri_both_internal":
        return g("tri_mod3_hqiv_internal_score") + g("tri_ham_hqiv_internal_score")
    if metric == "quark_ratio":
        return g("quark_ratio_sum")
    if metric == "tri_mod3_quark":
        return g("tri_mod3_quark_ratio")
    if metric == "tri_ham_quark":
        return g("tri_ham_quark_ratio")
    if metric == "tri_both_quark":
        return g("tri_mod3_quark_ratio") + g("tri_ham_quark_ratio")
    if metric == "tri_mod3_lepton":
        return g("tri_mod3_lepton_ratio")
    if metric == "tri_ham_lepton":
        return g("tri_ham_lepton_ratio")
    if metric == "tri_combo_qlep":
        return g("tri_mod3_quark_ratio") + g("tri_mod3_lepton_ratio")
    if metric == "tri_allfour":
        return (
            g("tri_mod3_quark_ratio")
            + g("tri_ham_quark_ratio")
            + g("tri_mod3_lepton_ratio")
            + g("tri_ham_lepton_ratio")
        )
    if metric == "lep_nu_global":
        return g("lepton_ratio_sum") + g("nu_ratio_sum")
    raise ValueError(f"unknown rank metric: {metric!r}")


# --- spinor core loader --------------------------------------------------------------

def _load_spinor_module():
    root = Path(__file__).resolve().parents[1]
    path = root / "scripts" / "spinor_monomial_gram_det_mod101.py"
    spec = importlib.util.spec_from_file_location("spinor_monomial_gram_det_mod101", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def monomial_arrays_float(sg) -> np.ndarray:
    mats = [np.array(sg.monomial_mat(m), dtype=np.float64) for m in range(64)]
    return np.stack(mats, axis=0)


def row_major_flat(M: np.ndarray) -> np.ndarray:
    return M.reshape(64, order="C")


def build_W_float(sg) -> np.ndarray:
    return np.array(sg.gram_W(), dtype=np.float64)


def method_W(W: np.ndarray) -> np.ndarray:
    return W


def method_W_sq(W: np.ndarray) -> np.ndarray:
    return W @ W


def method_coord_Gram(Vcols: np.ndarray) -> np.ndarray:
    return Vcols.T @ Vcols


def method_sandwich_kron(mats6: np.ndarray) -> np.ndarray:
    h = np.zeros((64, 64), dtype=np.float64)
    for k in range(6):
        g = mats6[k]
        kron = np.kron(g.T, g)
        h += kron
    return (h + h.T) * 0.5


def method_commutator_frob_Gram(mats: np.ndarray) -> np.ndarray:
    n = 64
    c = np.zeros((n, n), dtype=np.float64)
    for i in range(n):
        for j in range(i, n):
            com = mats[i] @ mats[j] - mats[j] @ mats[i]
            f = float(np.sum(com * com))
            c[i, j] = f
            c[j, i] = f
    return c


def method_triality_block_W(W: np.ndarray, mod: int = 3) -> np.ndarray:
    b = np.zeros((3, 3), dtype=np.float64)
    cnt = np.zeros((3, 3), dtype=np.int32)
    for i in range(64):
        for j in range(64):
            a, bb = i % mod, j % mod
            b[a, bb] += W[i, j]
            cnt[a, bb] += 1
    b /= np.maximum(cnt, 1)
    return b


def method_hamming_mod3_block_W(W: np.ndarray) -> np.ndarray:
    b = np.zeros((3, 3), dtype=np.float64)
    cnt = np.zeros((3, 3), dtype=np.int32)
    for i in range(64):
        for j in range(64):
            a, bb = _popcount6(i) % 3, _popcount6(j) % 3
            b[a, bb] += W[i, j]
            cnt[a, bb] += 1
    b /= np.maximum(cnt, 1)
    return b


def method_sum_gamma_sq(mats6: np.ndarray) -> np.ndarray:
    s = np.zeros((8, 8), dtype=np.float64)
    for k in range(6):
        g = mats6[k]
        s += g @ g
    return s


def method_sym_triple_product_012(mats6: np.ndarray) -> np.ndarray:
    p = mats6[0] @ mats6[1] @ mats6[2]
    return (p + p.T) * 0.5


def rho_pseudoscalar_all6(mats64: np.ndarray) -> np.ndarray:
    return mats64[63].copy()


def rho_bivector_commutator_sq_sum(mats6: np.ndarray) -> np.ndarray:
    s = np.zeros((8, 8), dtype=np.float64)
    for k in range(6):
        for l in range(k + 1, 6):
            c = mats6[k] @ mats6[l] - mats6[l] @ mats6[k]
            s += c @ c.T
    return s


def rho_minus_volume_squared(mats64: np.ndarray) -> np.ndarray:
    p = rho_pseudoscalar_all6(mats64)
    return -p @ p


def rho_scalar_plus_raw_volume(mats64: np.ndarray, c: float) -> np.ndarray:
    p = rho_pseudoscalar_all6(mats64)
    return np.eye(8, dtype=np.float64) + float(c) * p


# --- Manifold-derived mass operator (α + φ ladder + Δ + ρ on ℝ⁸) -------------------


def phase_lift_delta_matrix() -> np.ndarray:
    """Unit Δ: rotation in (e₁,e₇); matches `Hqiv/GeneratorsFromAxioms.lean` `phaseLiftDelta`."""
    d = np.zeros((8, 8), dtype=np.float64)
    d[1, 7] = -1.0
    d[7, 1] = 1.0
    return d


def manifold_curvature_sym_gamma_ij(mats6: np.ndarray, i: int, j: int) -> np.ndarray:
    """Symmetrized γᵢγⱼ = (γᵢγⱼ + γⱼγᵢ)/2 for distinct `i,j ∈ {0,…,5}`."""
    if i == j:
        raise ValueError("manifold_curvature_sym_gamma_ij requires i ≠ j")
    gi, gj = mats6[i], mats6[j]
    return (gi @ gj + gj @ gi) / 2.0


def manifold_mass_op_8(
    mats6: np.ndarray,
    shell_m: int,
    i: int,
    j: int,
    *,
    lambda_mix: float = 1.0,
    zeta_curv: float = 1.0,
    zeta_phase: float = 1.0,
) -> np.ndarray:
    r"""
    `ζ_c·α·sym(γᵢγⱼ) + λ·ζ_p·(φ(m)/6)·Δ` on ℝ⁸.

    Lean baseline `manifoldMassOp8` is `(i,j,λ,ζ)=(0,1,1,1)` with `ζ_c = ζ_p = 1`
    (`Hqiv.Physics.MassFromSpinorRho.manifoldMassOp8`).
    """
    phi = phi_of_shell(shell_m)
    curv = ALPHA_CURVATURE * float(zeta_curv) * manifold_curvature_sym_gamma_ij(mats6, i, j)
    phase = (
        float(lambda_mix)
        * float(zeta_phase)
        * (phi / 6.0)
        * phase_lift_delta_matrix()
    )
    return curv + phase


def manifold_mass_op_64_left_mult(
    mats6: np.ndarray,
    mats64: np.ndarray,
    shell_m: int,
    i: int,
    j: int,
    *,
    lambda_mix: float = 1.0,
    zeta_curv: float = 1.0,
    zeta_phase: float = 1.0,
) -> np.ndarray:
    """Left-multiplication by `manifold_mass_op_8` in row-major monomial coordinates (64×64)."""
    h8 = manifold_mass_op_8(
        mats6, shell_m, i, j, lambda_mix=lambda_mix, zeta_curv=zeta_curv, zeta_phase=zeta_phase
    )
    return left_mult_matrix_64(h8, mats64)


def resolve_phi_scale(
    phi_mode: str, *, phi_manual: float, phi_shell: int
) -> tuple[float, dict[str, Any]]:
    if phi_mode == "none":
        return 0.0, {"phi_mode": "none"}
    if phi_mode == "manual":
        return float(phi_manual), {"phi_mode": "manual", "phi_manual": phi_manual}
    if phi_mode == "shell":
        ph = phi_of_shell(phi_shell)
        return ph, {
            "phi_mode": "shell",
            "phi_shell_index": phi_shell,
            "phi_of_shell_value": ph,
            "phiTemperatureCoeff": PHI_TEMPERATURE_COEFF,
        }
    raise ValueError(phi_mode)


def enrich_method_row(
    name: str,
    S: np.ndarray,
    *,
    phi_scale: float,
    comparison_mode: ComparisonMode,
    mats64: np.ndarray,
    Vcols: np.ndarray,
    proj_mod: list[np.ndarray],
    proj_ham: list[np.ndarray],
) -> dict[str, Any]:
    # Manifold operators already embed `φ(m)`; do not add a second φ·I shift here.
    add_phi = 0.0 if name.startswith("manifold_") else float(phi_scale)
    sc = score_operator(S, phi_scale=add_phi, comparison_mode=comparison_mode)
    sc["method"] = name
    sc["matrix_shape"] = f"{S.shape[0]}x{S.shape[1]}"
    sc["dim"] = dim_label(S.shape)

    if S.shape == (8, 8):
        sec = secondary_metrics_8x8(S)
        sc["secondary_8x8"] = sec
        sc["tiebreak_8x8"] = tiebreak_8x8(sec)
        t64 = left_mult_matrix_64(S, mats64)
        tm = triality_triple_scores(
            t64, proj_mod, phi_scale=add_phi, comparison_mode=comparison_mode
        )
        th = triality_triple_scores(
            t64, proj_ham, phi_scale=add_phi, comparison_mode=comparison_mode
        )
        for k, v in tm.items():
            sc[f"tri_mod3_{k}"] = v
        for k, v in th.items():
            sc[f"tri_ham_{k}"] = v
    elif S.shape == (64, 64):
        sc["secondary_8x8"] = None
        sc["tiebreak_8x8"] = None
        tm = triality_triple_scores(
            S, proj_mod, phi_scale=add_phi, comparison_mode=comparison_mode
        )
        th = triality_triple_scores(
            S, proj_ham, phi_scale=add_phi, comparison_mode=comparison_mode
        )
        for k, v in tm.items():
            sc[f"tri_mod3_{k}"] = v
        for k, v in th.items():
            sc[f"tri_ham_{k}"] = v
    else:
        sc["secondary_8x8"] = None
        sc["tiebreak_8x8"] = None
    return sc


def run_all(
    *,
    phi_scale: float,
    phi_meta: dict[str, Any],
    phi_sweep_max: int | None,
    shell_index: int,
    manifold_pairs: list[tuple[int, int]],
    lambda_list: list[float],
    zeta_curv: float,
    zeta_phase: float,
    rank_metric: str,
    comparison_mode: ComparisonMode,
) -> dict[str, Any]:
    sg = _load_spinor_module()
    w = build_W_float(sg)
    mats64 = monomial_arrays_float(sg)
    mats6 = np.stack([mats64[1 << k] for k in range(6)], axis=0)
    vcols = np.column_stack([row_major_flat(mats64[i]) for i in range(64)])
    err = float(np.max(np.abs(vcols.T @ vcols - 8.0 * w)))
    if err > 1e-9:
        raise RuntimeError(f"V.T V != 8 W (max abs err {err})")

    proj_mod = triality_projectors_from_V(vcols, "mod3")
    proj_ham = triality_projectors_from_V(vcols, "hamming3")

    def builders_for(sh: int) -> dict[str, Callable[[], np.ndarray]]:
        """`sh` is the shell index `m` for `φ(m)` inside manifold operators."""
        bd: dict[str, Callable[[], np.ndarray]] = {}
        for ii, jj in manifold_pairs:
            for lam in lambda_list:
                nm8 = f"manifold_8_i{ii}j{jj}_lm{lam}"
                bd[nm8] = lambda ii=ii, jj=jj, lam=lam: manifold_mass_op_8(
                    mats6,
                    sh,
                    ii,
                    jj,
                    lambda_mix=lam,
                    zeta_curv=zeta_curv,
                    zeta_phase=zeta_phase,
                )
                nm64 = f"manifold_64_i{ii}j{jj}_lm{lam}"
                bd[nm64] = lambda ii=ii, jj=jj, lam=lam: manifold_mass_op_64_left_mult(
                    mats6,
                    mats64,
                    sh,
                    ii,
                    jj,
                    lambda_mix=lam,
                    zeta_curv=zeta_curv,
                    zeta_phase=zeta_phase,
                )
        bd.update(
            {
                "W_normalized_frob_gram": partial(method_W, w / np.max(np.diag(w))),
                "W_raw_integer_scale": partial(method_W, w),
                "W_squared": partial(method_W_sq, w),
                "coord_Gram_VtV_8W": partial(method_coord_Gram, vcols),
                "sandwich_kron_sum_GTG": partial(method_sandwich_kron, mats6),
                "commutator_frob_Gram_64": partial(method_commutator_frob_Gram, mats64),
                "triality_mod3_block_average_W": partial(method_triality_block_W, w, 3),
                "triality_hamming_mod3_block_W": partial(method_hamming_mod3_block_W, w),
                "sum_gamma_sq_8x8": partial(method_sum_gamma_sq, mats6),
                "sym_triple_product_gamma012_8x8": partial(
                    method_sym_triple_product_012, mats6
                ),
                "rho_bivector_commutator_sq_sum_8x8": partial(
                    rho_bivector_commutator_sq_sum, mats6
                ),
                "rho_minus_volume_squared_8x8": partial(rho_minus_volume_squared, mats64),
                "rho_pseudoscalar_raw_8x8": partial(rho_pseudoscalar_all6, mats64),
                "rho_I_plus_0p1_raw_volume": partial(rho_scalar_plus_raw_volume, mats64, 0.1),
            }
        )
        return bd

    builders = builders_for(shell_index)

    rows: list[dict[str, Any]] = []
    for name, fn in builders.items():
        s = fn()
        rows.append(
            enrich_method_row(
                name,
                s,
                phi_scale=phi_scale,
                comparison_mode=comparison_mode,
                mats64=mats64,
                Vcols=vcols,
                proj_mod=proj_mod,
                proj_ham=proj_ham,
            )
        )

    def sk_perm(r: dict[str, Any]) -> float:
        return float(r.get("quark_perm_sum", 1e300))

    def sk_ratio(r: dict[str, Any]) -> float:
        return float(r.get("quark_ratio_sum", 1e300))

    def sk_hqiv(r: dict[str, Any]) -> float:
        return float(r.get("hqiv_internal_score", 1e300))

    def sk_primary(r: dict[str, Any]) -> float:
        return primary_rank_value(r, rank_metric)

    def sk_dim8_ratio_tie(r: dict[str, Any]) -> tuple[float, float]:
        if r["dim"] != "8":
            return (1e300, 0.0)
        return (float(r["quark_ratio_sum"]), float(r.get("tiebreak_8x8") or 1e300))

    def sk_dim8_primary_tie(r: dict[str, Any]) -> tuple[float, float]:
        if r["dim"] != "8":
            return (1e300, 0.0)
        return (sk_primary(r), float(r.get("tiebreak_8x8") or 1e300))

    out: dict[str, Any] = {
        "VtV_minus_8W_max_abs": err,
        "phi_scale": phi_scale,
        "phi_meta": phi_meta,
        "manifold_shell_index": shell_index,
        "manifold_phi_internal": phi_of_shell(shell_index),
        "manifold_pairs": [[a, b] for a, b in manifold_pairs],
        "manifold_lambda_list": lambda_list,
        "manifold_zeta_curvature": zeta_curv,
        "manifold_zeta_phase": zeta_phase,
        "rank_metric": rank_metric,
        "comparison_mode": comparison_mode,
        "reference_shell_m": REFERENCE_SHELL_M,
        "ranked_hqiv_internal": sorted(rows, key=sk_hqiv),
        "ranked_primary": sorted(rows, key=sk_primary),
        "ranked_primary_dim8": sorted(
            [r for r in rows if r["dim"] == "8"], key=sk_dim8_primary_tie
        ),
        "ranked_primary_dim64": sorted(
            [r for r in rows if r["dim"] == "64"], key=sk_primary
        ),
    }
    if comparison_mode == "external":
        out.update(
            {
                "pdg_quark_GeV": PDG_QUARK_GEV,
                "pdg_lepton_GeV": PDG_LEPTON_GEV,
                "pdg_nu_rough_GeV": PDG_NU_ROUGH_GEV,
                "ranked_quark_perm": sorted(rows, key=sk_perm),
                "ranked_quark_ratio": sorted(rows, key=sk_ratio),
                "ranked_quark_ratio_dim8": sorted(
                    [r for r in rows if r["dim"] == "8"], key=sk_dim8_ratio_tie
                ),
                "ranked_quark_ratio_dim64": sorted(
                    [r for r in rows if r["dim"] == "64"], key=sk_ratio
                ),
                "ranked_tri_mod3_quark_ratio": sorted(
                    rows, key=lambda r: float(r.get("tri_mod3_quark_ratio", 1e300))
                ),
            }
        )

    if phi_sweep_max is not None:
        sweep: list[dict[str, Any]] = []
        for m in range(phi_sweep_max + 1):
            ph = phi_of_shell(m)
            rows_m: list[dict[str, Any]] = []
            b_m = builders_for(m)
            for name, fn in b_m.items():
                s = fn()
                rows_m.append(
                    enrich_method_row(
                        name,
                        s,
                        phi_scale=ph,
                        comparison_mode=comparison_mode,
                        mats64=mats64,
                        Vcols=vcols,
                        proj_mod=proj_mod,
                        proj_ham=proj_ham,
                    )
                )
            sweep.append(
                {
                    "shell_m": m,
                    "phi_of_shell": ph,
                    "best_hqiv_internal": min(rows_m, key=sk_hqiv)["method"],
                    "best_primary": min(rows_m, key=sk_primary)["method"],
                }
            )
            if comparison_mode == "external":
                sweep[-1]["best_quark_ratio"] = min(rows_m, key=sk_ratio)["method"]
                sweep[-1]["best_tri_mod3_quark_ratio"] = min(
                    rows_m,
                    key=lambda r: float(r.get("tri_mod3_quark_ratio", 1e300)),
                )["method"]
        out["phi_shell_sweep"] = sweep

    return out


def print_human(out: dict[str, Any], *, score: str) -> None:
    print("spinor_mass_operator_reality_probe")
    print(f"check V.T@V = 8W: max|diff| = {out['VtV_minus_8W_max_abs']:.3e}")
    print(
        "manifold: shell m =",
        out.get("manifold_shell_index"),
        "internal φ(m) =",
        out.get("manifold_phi_internal"),
    )
    print("manifold pairs:", out.get("manifold_pairs"), "| λ list:", out.get("manifold_lambda_list"))
    print(
        "ζ curvature ×",
        out.get("manifold_zeta_curvature"),
        "| ζ phase ×",
        out.get("manifold_zeta_phase"),
    )
    print("primary rank metric:", out.get("rank_metric"))
    print("comparison mode:", out.get("comparison_mode", "hqiv"))
    print("phi:", out.get("phi_meta"), "| additive I scale:", out["phi_scale"])
    print()

    def hqiv_line(r: dict[str, Any]) -> str:
        tri_mod = r.get("tri_mod3_hqiv_internal_score", float("nan"))
        tri_ham = r.get("tri_ham_hqiv_internal_score", float("nan"))
        return (
            f"{r['method']:<40} dim={r['dim']:>2}  "
            f"hqiv={r.get('hqiv_internal_score', float('nan')):8.4f}  "
            f"spread={r.get('hqiv_log_spread', float('nan')):8.4f}  "
            f"scale={r.get('hqiv_shell_scale_score', float('nan')):8.4f}  "
            f"tri_mod3={tri_mod:8.4f} tri_ham={tri_ham:8.4f}"
        )

    if out.get("comparison_mode", "hqiv") != "external":
        print("=== HQIV-internal leaderboard (no external mass-table yardsticks) ===")
        for r in out["ranked_primary"][:14]:
            print(hqiv_line(r))
        print("best primary:", out["ranked_primary"][0]["method"])
        print()
        print("--- dim 8: primary metric + secondary diagnostics ---")
        for r in out["ranked_primary_dim8"]:
            sec = r.get("secondary_8x8") or {}
            print(
                f"{r['method']:<38} hqiv={primary_rank_value(r, str(out.get('rank_metric'))):7.3f}  "
                f"tr={sec.get('trace', float('nan')):8.3f}  "
                f"det={sec.get('det', float('nan')):8.3f}  "
                f"cond={sec.get('condition_number', float('nan')):10.3g}  "
                f"fro_off={sec.get('frobenius_norm_off_diagonal', float('nan')):7.3f}"
            )
        if out.get("phi_shell_sweep"):
            print()
            print("=== φ(m)=2(m+1) shell sweep (internal best method names) ===")
            for s in out["phi_shell_sweep"]:
                print(
                    f"  m={s['shell_m']}  φ={s['phi_of_shell']:.4g}  "
                    f"best_primary={s.get('best_primary', '?')}  "
                    f"best_hqiv={s.get('best_hqiv_internal', '?')}"
                )
        return

    def row_line(r: dict[str, Any], use_ratio: bool) -> str:
        dim = r["dim"]
        if use_ratio:
            q, l, n = r["quark_ratio_sum"], r["lepton_ratio_sum"], r["nu_ratio_sum"]
        else:
            q, l, n = r["quark_perm_sum"], r["lepton_perm_sum"], r["nu_perm_sum"]
        return f"{r['method']:<42} dim={dim:>2}  q={q:8.4f}  lep={l:8.4f}  nu={n:8.4f}"

    def primary_detail_line(r: dict[str, Any]) -> str:
        rm = str(out.get("rank_metric", "tri_mod3_quark"))
        pri = primary_rank_value(r, rm)
        tmq = r.get("tri_mod3_quark_ratio", float("nan"))
        thq = r.get("tri_ham_quark_ratio", float("nan"))
        tml = r.get("tri_mod3_lepton_ratio", float("nan"))
        thl = r.get("tri_ham_lepton_ratio", float("nan"))
        return (
            f"{r['method']:<40} dim={r['dim']:>2}  pri({rm})={pri:8.4f}  "
            f"q={r['quark_ratio_sum']:.4f} lep={r['lepton_ratio_sum']:.4f} nu={r['nu_ratio_sum']:.4f}  "
            f"tri_mod3_q={tmq:.4f} tri_ham_q={thq:.4f}  tri_mod3_lep={tml:.4f} tri_ham_lep={thl:.4f}"
        )

    if score in ("perm", "both"):
        print("=== Quark sector: permutation score (lower q better) ===")
        for r in out["ranked_quark_perm"][:12]:
            print(row_line(r, use_ratio=False))
        print("best (perm):", out["ranked_quark_perm"][0]["method"])
        print()

    if score in ("ratio", "both"):
        rm = str(out.get("rank_metric", "tri_mod3_quark"))
        print(f"=== Primary leaderboard: {rm} (lower better) ===")
        for r in out["ranked_primary"][:14]:
            print(primary_detail_line(r))
        print("best primary:", out["ranked_primary"][0]["method"])
        print()
        print("=== Ratio-only global top-3 SV (quark_ratio_sum) ===")
        for r in out["ranked_quark_ratio"][:12]:
            print(row_line(r, use_ratio=True))
        print("best quark ratio:", out["ranked_quark_ratio"][0]["method"])
        print()
        print("=== Triality-projected (mod 3 index) — tri_mod3_quark_ratio ===")
        key = "tri_mod3_quark_ratio"
        tri_sorted = sorted(out["ranked_quark_ratio"], key=lambda r: float(r.get(key, 1e300)))
        for r in tri_sorted[:10]:
            tr = r.get(key, float("nan"))
            print(f"{r['method']:<42}  tri_q_ratio={tr:8.4f}")
        print()
        print("--- dim 8: primary metric + secondary tiebreak (cond, |trace|, fro_off) ---")
        for r in out["ranked_primary_dim8"]:
            sec = r.get("secondary_8x8") or {}
            tb = r.get("tiebreak_8x8", float("nan"))
            pr = primary_rank_value(r, rm)
            print(
                f"{r['method']:<38} pri={pr:7.3f}  q_ratio={r['quark_ratio_sum']:7.3f}  "
                f"tr={sec.get('trace', float('nan')):8.3f}  "
                f"det={sec.get('det', float('nan')):8.3f}  "
                f"cond={sec.get('condition_number', float('nan')):10.3g}  "
                f"fro_off={sec.get('frobenius_norm_off_diagonal', float('nan')):7.3f}  "
                f"tie={tb:8.3f}"
            )
        print()
        print("--- dim 8: global quark ratio + secondary tiebreak ---")
        for r in out["ranked_quark_ratio_dim8"]:
            sec = r.get("secondary_8x8") or {}
            tb = r.get("tiebreak_8x8", float("nan"))
            print(
                f"{r['method']:<40} q_ratio={r['quark_ratio_sum']:7.3f}  "
                f"tr={sec.get('trace', float('nan')):8.3f}  "
                f"det={sec.get('det', float('nan')):8.3f}  "
                f"cond={sec.get('condition_number', float('nan')):10.3g}  "
                f"fro_off={sec.get('frobenius_norm_off_diagonal', float('nan')):7.3f}  "
                f"tie={tb:8.3f}"
            )
        if out.get("phi_shell_sweep"):
            print()
            print("=== φ(m)=2(m+1) shell sweep (best method names) ===")
            for s in out["phi_shell_sweep"]:
                print(
                    f"  m={s['shell_m']}  φ={s['phi_of_shell']:.4g}  "
                    f"best_primary={s.get('best_primary', '?')}  "
                    f"best_ratio={s['best_quark_ratio']}  best_tri_mod3={s['best_tri_mod3_quark_ratio']}"
                )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true")
    ap.add_argument(
        "--score",
        choices=("perm", "ratio", "both"),
        default="both",
    )
    ap.add_argument(
        "--comparison-mode",
        choices=("hqiv", "external"),
        default="hqiv",
        help="hqiv: internal spectral/shell diagnostics only; external: opt-in mass-table yardsticks",
    )
    ap.add_argument(
        "--phi-mode",
        choices=("none", "manual", "shell"),
        default="manual",
        help="shell: use φ(m)=2(m+1) at `--phi-shell`; none: 0; manual: use `--phi`",
    )
    ap.add_argument("--phi", type=float, default=0.0, help="used when --phi-mode manual")
    ap.add_argument(
        "--phi-shell",
        type=int,
        default=4,
        help="shell index m for φ(m) when --phi-mode shell",
    )
    ap.add_argument(
        "--phi-sweep",
        action="store_true",
        help="include JSON `phi_shell_sweep` for m=0..max (see --phi-sweep-max)",
    )
    ap.add_argument("--phi-sweep-max", type=int, default=6)
    ap.add_argument(
        "--manifold-shell",
        type=int,
        default=None,
        help="shell index m for manifold_mass_op internal φ(m); default: same as --phi-shell",
    )
    ap.add_argument(
        "--manifold-pairs",
        default=None,
        help='bivector indices for sym(γᵢγⱼ), e.g. "0,1;1,5;0,5" (semicolon-separated)',
    )
    ap.add_argument(
        "--manifold-bivector-sweep",
        action="store_true",
        help="use all pairs 0≤i<j≤5 for manifold builders (overrides default single pair)",
    )
    ap.add_argument(
        "--lambda-mix",
        type=float,
        default=1.0,
        help="mixing λ on (φ(m)/6)·Δ when --lambda-sweep is not set",
    )
    ap.add_argument(
        "--lambda-sweep",
        default=None,
        help='comma-separated λ list, e.g. "0.5,1.0,1.5" (replaces --lambda-mix)',
    )
    ap.add_argument(
        "--zeta-curvature",
        choices=("none", "z3", "z8"),
        default="none",
        help="multiply curvature branch by ζ(3) or ζ(8)",
    )
    ap.add_argument(
        "--zeta-phase",
        choices=("none", "z3", "z8"),
        default="none",
        help="multiply phase / Δ branch by ζ(3) or ζ(8)",
    )
    ap.add_argument(
        "--rank-metric",
        choices=(
            "hqiv_internal",
            "tri_mod3_internal",
            "tri_ham_internal",
            "tri_both_internal",
            "quark_ratio",
            "tri_mod3_quark",
            "tri_ham_quark",
            "tri_both_quark",
            "tri_mod3_lepton",
            "tri_ham_lepton",
            "tri_combo_qlep",
            "tri_allfour",
            "lep_nu_global",
        ),
        default="hqiv_internal",
        help="sort key for ranked_primary and shell-sweep best_primary",
    )
    args = ap.parse_args()
    external_metrics = {
        "quark_ratio",
        "tri_mod3_quark",
        "tri_ham_quark",
        "tri_both_quark",
        "tri_mod3_lepton",
        "tri_ham_lepton",
        "tri_combo_qlep",
        "tri_allfour",
        "lep_nu_global",
    }
    if args.comparison_mode == "hqiv" and args.rank_metric in external_metrics:
        ap.error("--rank-metric using quark/lepton yardsticks requires --comparison-mode external")

    phi_scale, phi_meta = resolve_phi_scale(
        args.phi_mode, phi_manual=args.phi, phi_shell=args.phi_shell
    )
    sweep_max = args.phi_sweep_max if args.phi_sweep else None
    msh = args.manifold_shell if args.manifold_shell is not None else args.phi_shell
    pairs = parse_ij_pairs(args.manifold_pairs, args.manifold_bivector_sweep)
    lambda_list = parse_lambda_list(args.lambda_sweep, args.lambda_mix)
    zc = zeta_multiplier("none" if args.zeta_curvature == "none" else args.zeta_curvature)
    zp = zeta_multiplier("none" if args.zeta_phase == "none" else args.zeta_phase)
    out = run_all(
        phi_scale=phi_scale,
        phi_meta=phi_meta,
        phi_sweep_max=sweep_max,
        shell_index=msh,
        manifold_pairs=pairs,
        lambda_list=lambda_list,
        zeta_curv=zc,
        zeta_phase=zp,
        rank_metric=args.rank_metric,
        comparison_mode=args.comparison_mode,
    )

    if args.json:
        print(json.dumps(out, indent=2))
    else:
        print_human(out, score=args.score)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as e:
        print(f"error: {e}", file=sys.stderr)
        raise SystemExit(1)
