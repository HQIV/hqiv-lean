#!/usr/bin/env python3
"""
Uncertainty (σ) propagation for HEP decay-chain readouts.

Combines:
  • PDG comparison σ from `data/hadron_published_masses.json`
  • Witness/input σ on proton, quark ladder anchors (Monte Carlo)
  • Lean-aligned readout in `hqiv_hep_decay_readout.py`

Outputs per-species predicted σ and n_σ vs reference for benchmarks.
"""

from __future__ import annotations

import json
import math
import random
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Sequence

import hqiv_hep_multichannel_expansion as mc

import hqiv_hep_decay_readout as hdr
import hqiv_hep_decay_chain as hep
import hqiv_lean_physics_primitives as lean
import hqiv_scale_witness as sw


def _repo_root() -> Path:
    """Locate repo-level data when scripts are run from the paper subtree."""
    for parent in Path(__file__).resolve().parents:
        if (parent / "lakefile.toml").exists() and (parent / "data").is_dir():
            return parent
    return Path(__file__).resolve().parents[1]


ROOT = _repo_root()
DEFAULT_PUBLISHED = ROOT / "data" / "hadron_published_masses.json"

MC_SAMPLES = 400
MC_SEED = 42

# Relative σ on ladder witnesses (comparison-layer anchors, not PDG injection into readout).
WITNESS_REL_SIGMA = {
    "derived_proton_mass_mev": 0.002,
    "derived_neutron_mass_mev": 0.002,
    "m_top_gev": 0.008,
    "m_bottom_gev": 0.008,
    "resonance_step": 0.012,
    "chiral_xi": 0.015,
}


@dataclass(frozen=True)
class MassSigmaResult:
    species_id: str
    mass_mev: float
    sigma_mev: float
    sigma_minus_mev: float
    sigma_plus_mev: float
    method: str


def load_pdg_sigma_mev(path: Path = DEFAULT_PUBLISHED) -> dict[str, float]:
    data = json.loads(path.read_text(encoding="utf-8"))
    out: dict[str, float] = {}
    for entry in data.get("entries", []):
        cid = entry.get("config_id")
        if cid and entry.get("uncertainty_MeV") is not None:
            out[str(cid)] = float(entry["uncertainty_MeV"])
    return out


def _percentile(sorted_vals: list[float], p: float) -> float:
    if not sorted_vals:
        return math.nan
    idx = (len(sorted_vals) - 1) * p
    lo = int(math.floor(idx))
    hi = int(math.ceil(idx))
    if lo == hi:
        return sorted_vals[lo]
    w = idx - lo
    return sorted_vals[lo] * (1.0 - w) + sorted_vals[hi] * w


def _summarize_samples(samples: list[float]) -> tuple[float, float, float, float]:
    vals = sorted(samples)
    med = _percentile(vals, 0.50)
    p16 = _percentile(vals, 0.16)
    p84 = _percentile(vals, 0.84)
    sigma = 0.5 * (p84 - p16)
    return med, max(med - p16, 0.0), max(p84 - med, 0.0), sigma


def _sample_quark_gaps_mev(rng: random.Random) -> tuple[float, float, float]:
    """Perturb QuarkMetaResonance ladder gaps (MC)."""
    import cubic_phase_relax_probe as cpr
    import hqiv_mass_calculator_core as hmc

    m_top = rng.gauss(cpr.M_TOP_GEV, cpr.M_TOP_GEV * WITNESS_REL_SIGMA["m_top_gev"])
    m_bottom = rng.gauss(cpr.M_BOTTOM_GEV, cpr.M_BOTTOM_GEV * WITNESS_REL_SIGMA["m_bottom_gev"])
    qm_base = hmc.derived_quark_gev()
    k_perturb = 1.0 + rng.gauss(0.0, WITNESS_REL_SIGMA["resonance_step"])
    up_gap = (qm_base["c"] - qm_base["u"]) * 1000.0 * k_perturb
    down_gap = (qm_base["b"] - qm_base["s"]) * 1000.0 * k_perturb
    # Re-anchor heavy ends to perturbed witnesses while keeping step ratios.
    scale_c = m_top / max(cpr.M_TOP_GEV, 1e-9)
    scale_b = m_bottom / max(cpr.M_BOTTOM_GEV, 1e-9)
    up_gap *= scale_c
    down_gap *= scale_b
    return up_gap, down_gap, m_bottom * 1000.0


def _light_meson_masses(rng: random.Random, xi: float) -> tuple[float, float]:
    xi_j = xi * (1.0 + rng.gauss(0.0, WITNESS_REL_SIGMA["chiral_xi"]))
    m_pi = hep._chiral_pseudoscalar_mass_mev("pi_plus", xi=xi_j) or 139.0
    m_k = hep._chiral_pseudoscalar_mass_mev("K_plus", xi=xi_j) or 486.0
    return m_pi, m_k


def _proton_mass(rng: random.Random) -> float:
    bundle = sw.load_witness_bundle()
    rel = WITNESS_REL_SIGMA["derived_proton_mass_mev"]
    return rng.gauss(bundle.derived_proton_mass_mev, bundle.derived_proton_mass_mev * rel)


def _heavy_kind_for(sid: str) -> tuple[str, dict[str, int]] | None:
    if sid in ("D_plus", "D0"):
        return "open_charm", {"n_charm": 1, "n_strange": 0}
    if sid == "Ds_plus":
        return "open_charm_strange", {"n_charm": 1, "n_strange": 1}
    if sid == "Jpsi":
        return "hidden_charm", {"n_charm": 2, "n_strange": 0}
    if sid in hep.CHARMED_BARYONS:
        cat = hep._catalog_index().get(sid, {})
        counts = hep._valence_flavor_counts(sid)
        return "charmed_baryon", {
            "n_charm": counts.get("c", 0),
            "n_strange": counts.get("s", 0),
        }
    if sid in ("B_plus", "B0"):
        return "open_bottom", {"n_charm": 0, "n_strange": 0}
    if sid == "Bs":
        return "open_bottom_strange", {"n_charm": 0, "n_strange": 1}
    if sid == "Upsilon":
        return "hidden_bottom", {"n_charm": 0, "n_strange": 0}
    if sid in hep.BOTTOM_BARYONS:
        counts = hep._valence_flavor_counts(sid)
        return "bottom_baryon", {
            "n_charm": counts.get("c", 0),
            "n_strange": counts.get("s", 0),
        }
    return None


def predict_mass_with_sigma(
    species_id: str,
    *,
    xi: float = lean.XI_LOCKIN,
    n_samples: int = MC_SAMPLES,
    seed: int = MC_SEED,
) -> MassSigmaResult:
    """MC σ propagation for a catalog species."""
    sid = hep.BEAM_SPECIES.get(species_id, species_id)
    rng = random.Random(seed + hash(sid) % 10_000)
    samples: list[float] = []

    heavy = _heavy_kind_for(sid)
    for _ in range(n_samples):
        m_p = _proton_mass(rng)
        m_pi, m_k = _light_meson_masses(rng, xi)
        up_gap, _, bottom = _sample_quark_gaps_mev(rng)
        xi_j = xi * (1.0 + rng.gauss(0.0, WITNESS_REL_SIGMA["chiral_xi"]))
        if heavy is not None:
            kind, kw = heavy
            samples.append(
                hdr.heavy_species_mass_mev(
                    kind,  # type: ignore[arg-type]
                    m_pi_mev=m_pi,
                    m_k_mev=m_k,
                    m_proton_mev=m_p,
                    n_charm=kw.get("n_charm", 0),
                    n_strange=kw.get("n_strange", 0),
                    up_gap_mev=up_gap,
                    bottom_mev=bottom,
                )
            )
        elif sid in ("p", "proton"):
            samples.append(m_p)
        elif sid in ("n", "neutron"):
            bundle = sw.load_witness_bundle()
            rel = WITNESS_REL_SIGMA["derived_neutron_mass_mev"]
            samples.append(
                rng.gauss(bundle.derived_neutron_mass_mev, bundle.derived_neutron_mass_mev * rel)
            )
        elif sid in hep.STRANGE_BARYON_IDS:
            counts = hep._valence_flavor_counts(sid)
            dec = sid.startswith("sigma_star") or sid in (
                "delta_p",
                "delta_pp",
                "delta_0",
                "delta_m",
            )
            samples.append(
                hdr.strange_baryon_mass_mev(
                    m_p,
                    m_k,
                    m_pi,
                    counts.get("s", 1),
                    decuplet=dec,
                )
            )
        else:
            samples.append(hep.particle_mass_mev(sid, xi=xi_j))

    med, sig_m, sig_p, sigma = _summarize_samples(samples)
    sigma = max(sigma, 0.001 * abs(med))
    return MassSigmaResult(
        species_id=sid,
        mass_mev=med,
        sigma_mev=sigma,
        sigma_minus_mev=sig_m,
        sigma_plus_mev=sig_p,
        method=f"mc_{n_samples}",
    )


@lru_cache(maxsize=256)
def predicted_mass_sigma_mev(species_id: str, *, xi: float = lean.XI_LOCKIN) -> float:
    return predict_mass_with_sigma(species_id, xi=xi).sigma_mev


def combined_sigma_mev(predicted_sigma: float, reference_sigma: float) -> float:
    return math.sqrt(max(predicted_sigma, 0.0) ** 2 + max(reference_sigma, 0.0) ** 2)


def n_sigma(predicted: float, reference: float, *, pred_sigma: float, ref_sigma: float) -> float:
    pred_s = max(pred_sigma, 0.001 * abs(predicted))
    ref_s = max(ref_sigma, 0.0)
    denom = combined_sigma_mev(pred_s, ref_s)
    if denom <= 0.0:
        return math.inf
    return abs(predicted - reference) / denom


def q_sigma_mev(parent_sigma: float, daughter_sigmas: list[float]) -> float:
    """Quadrature for decay Q = m_parent − Σ m_daughters."""
    return math.sqrt(parent_sigma**2 + sum(s**2 for s in daughter_sigmas))


def width_sigma_from_q(q_sigma_mev: float, *, relative: float = 0.35) -> float:
    """Width σ scales with phase-space Q uncertainty (leading slot)."""
    return max(q_sigma_mev * relative, 0.0)


def half_life_sigma_from_width(width_per_s: float, width_sigma_per_s: float) -> float:
    if width_per_s <= 0.0 or width_sigma_per_s <= 0.0:
        return math.inf
    hl = math.log(2.0) / width_per_s
    return hl * width_sigma_per_s / width_per_s


def benchmark_sigma_summary(
    rows: list[dict[str, Any]],
) -> dict[str, float]:
    """Aggregate n_σ for rows that carry sigma fields."""
    vals = [float(r["n_sigma"]) for r in rows if r.get("n_sigma") is not None]
    if not vals:
        return {}
    out = {
        "mean_n_sigma": sum(vals) / len(vals),
        "max_n_sigma": max(vals),
        "count": float(len(vals)),
    }
    branching_vals = [
        float(r["n_sigma"])
        for r in rows
        if r.get("n_sigma") is not None and r.get("panel") in ("branching", "branching_comparison", "decay")
        and r.get("quantity") in ("branching_ratio", "inclusive_branching_ratio")
    ]
    if branching_vals:
        out["mean_branching_n_sigma"] = sum(branching_vals) / len(branching_vals)
        out["max_branching_n_sigma"] = max(branching_vals)
    return out


def _mass_for_species_sample(
    species_id: str,
    *,
    m_p: float,
    m_pi: float,
    m_k: float,
    up_gap: float,
    bottom: float,
    xi: float,
    rng: random.Random,
) -> float:
    sid = hep.BEAM_SPECIES.get(species_id, species_id)
    heavy = _heavy_kind_for(sid)
    if heavy is not None:
        kind, kw = heavy
        return hdr.heavy_species_mass_mev(
            kind,  # type: ignore[arg-type]
            m_pi_mev=m_pi,
            m_k_mev=m_k,
            m_proton_mev=m_p,
            n_charm=kw.get("n_charm", 0),
            n_strange=kw.get("n_strange", 0),
            up_gap_mev=up_gap,
            bottom_mev=bottom,
        )
    if sid in ("p", "proton"):
        return m_p
    if sid in ("n", "neutron"):
        bundle = sw.load_witness_bundle()
        rel = WITNESS_REL_SIGMA["derived_neutron_mass_mev"]
        return rng.gauss(bundle.derived_neutron_mass_mev, bundle.derived_neutron_mass_mev * rel)
    if sid in hep.STRANGE_BARYON_IDS:
        counts = hep._valence_flavor_counts(sid)
        dec = sid.startswith("sigma_star") or sid in ("delta_p", "delta_pp", "delta_0", "delta_m")
        return hdr.strange_baryon_mass_mev(
            m_p,
            m_k,
            m_pi,
            counts.get("s", 1),
            decuplet=dec,
        )
    chiral = hep._chiral_pseudoscalar_mass_mev(sid, xi=xi)
    if chiral is not None:
        return chiral
    return hep.particle_mass_mev(sid, xi=xi)


def species_closure_for_parent(parent_id: str, *, env: hep.ExperimentEnvironment) -> set[str]:
    """Species whose masses can move a parent's branching normalization."""
    parent = hep.build_particle(parent_id)
    edges = hep.edges_from_particle(parent, env=env)
    species = {parent.species_id}
    for edge in edges:
        species.add(edge.parent.species_id)
        for did in edge.mode.daughter_ids:
            species.add(hep.BEAM_SPECIES.get(did, did))
    return species


def sample_mass_overrides(
    species_ids: set[str],
    *,
    xi: float,
    rng: random.Random,
) -> dict[str, float]:
    m_p = _proton_mass(rng)
    m_pi, m_k = _light_meson_masses(rng, xi)
    up_gap, _, bottom = _sample_quark_gaps_mev(rng)
    xi_j = xi * (1.0 + rng.gauss(0.0, WITNESS_REL_SIGMA["chiral_xi"]))
    return {
        sid: _mass_for_species_sample(
            sid,
            m_p=m_p,
            m_pi=m_pi,
            m_k=m_k,
            up_gap=up_gap,
            bottom=bottom,
            xi=xi_j,
            rng=rng,
        )
        for sid in species_ids
    }


def _branching_from_edge(
    parent_id: str,
    channel: str,
    daughter_ids: Sequence[str],
    *,
    env: hep.ExperimentEnvironment,
    aggregate: str | None = None,
    contains_daughter: str | None = None,
) -> float | None:
    parent = hep.build_particle(parent_id)
    edges = hep.edges_from_particle(parent, env=env)
    if aggregate == "strong_neutral_inclusive_contains" and contains_daughter:
        selected = [
            e
            for e in edges
            if e.mode.channel == "strong"
            and contains_daughter in e.mode.daughter_ids
            and mc.strong_neutral_light_cascade(e.mode.daughter_ids)
        ]
        return sum(e.branching_ratio for e in selected) if selected else None
    if aggregate == "sum_daughter_sets":
        wanted = [
            {hep.BEAM_SPECIES.get(d, d) for d in daughter_set}
            for daughter_set in daughter_ids  # type: ignore[assignment]
        ]
        selected = []
        for edge in edges:
            if edge.mode.channel != channel:
                continue
            got = {d.species_id for d in edge.daughters}
            if got in wanted:
                selected.append(edge)
        return sum(e.branching_ratio for e in selected) if selected else None
    want = {hep.BEAM_SPECIES.get(d, d) for d in daughter_ids}
    for edge in edges:
        if edge.mode.channel != channel:
            continue
        got = {d.species_id for d in edge.daughters}
        if got == want:
            return edge.branching_ratio
    return None


def predict_branching_with_sigma(
    parent_id: str,
    channel: str,
    daughter_ids: Sequence[str] | None = None,
    *,
    env: hep.ExperimentEnvironment | None = None,
    aggregate: str | None = None,
    contains_daughter: str | None = None,
    xi: float = lean.XI_LOCKIN,
    n_samples: int = MC_SAMPLES,
    seed: int = MC_SEED,
) -> tuple[float, float]:
    """Monte Carlo σ on branching ratio from witness/mass-input perturbations."""
    env = env or hep.ExperimentEnvironment()
    if aggregate == "sum_daughter_sets":
        daughters = tuple(tuple(str(d) for d in ds) for ds in (daughter_ids or ()))  # type: ignore[union-attr]
    else:
        daughters = tuple(str(d) for d in (daughter_ids or ()))
    species = species_closure_for_parent(parent_id, env=env)
    rng = random.Random(seed + hash((parent_id, channel, daughters, aggregate)) % 10_000)
    samples: list[float] = []
    for _ in range(n_samples):
        overrides = sample_mass_overrides(species, xi=xi, rng=rng)
        with hep.mass_override_context(overrides):
            br = _branching_from_edge(
                parent_id,
                channel,
                daughters,
                env=env,
                aggregate=aggregate,
                contains_daughter=contains_daughter,
            )
        if br is not None:
            samples.append(br)
    if not samples:
        return math.nan, math.nan
    med, _, _, sigma = _summarize_samples(samples)
    sigma = max(sigma, 1e-6 * abs(med))
    return med, sigma
