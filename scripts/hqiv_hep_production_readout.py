#!/usr/bin/env python3
"""
Production rates and branching normalization for HEP new states.

Lean mirror: `Hqiv.Physics.HepDecayReadout` (branching + phase-space slots).

Branching ratios are normalized from partial widths Γ_i with topology/CKM weights:
  BR_i = (w_i Γ_i) / Σ_j (w_j Γ_j)

Production rate proxies (comparison-layer, not PDG σ tables):
  σ_proxy ∝ phase_space(m, √s) × flavor_weight(sector)
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal

import hqiv_hep_decay_readout as hdr
import hqiv_lean_physics_primitives as lean

if TYPE_CHECKING:
    import hqiv_hep_decay_chain as hep

BranchingPolicy = Literal["width_only", "width_topology", "width_prior"]

# Charm / bottom states targeted for branching + production benchmarks.
NEW_STATE_IDS = frozenset(
    {
        "D_plus",
        "D0",
        "Ds_plus",
        "Jpsi",
        "lambda_c",
        "sigma_c",
        "xi_c",
        "omega_c",
        "B_plus",
        "B0",
        "Bs",
        "lambda_b",
        "Upsilon",
    }
)

OPEN_CHARM_MESONS = frozenset({"D_plus", "D0", "Ds_plus"})
OPEN_BOTTOM_MESONS = frozenset({"B_plus", "B0", "Bs"})
HIDDEN_QUARKONIA = frozenset({"Jpsi", "Upsilon"})
CHARMED_BARYONS = frozenset({"lambda_c", "sigma_c", "xi_c", "omega_c"})
BOTTOM_BARYONS = frozenset({"lambda_b", "xi_b", "omega_b"})


def flavor_sector(species_id: str) -> str:
    if species_id in HIDDEN_QUARKONIA:
        return "hidden_quarkonium"
    if species_id in OPEN_BOTTOM_MESONS or species_id in BOTTOM_BARYONS:
        return "open_bottom"
    if species_id in OPEN_CHARM_MESONS or species_id in CHARMED_BARYONS:
        return "open_charm"
    if species_id.startswith("B") or "bottom" in species_id:
        return "open_bottom"
    return "light"


def flavor_production_weight(species_id: str) -> float:
    """Relative production weight from CKM / Fano rung hierarchy (Lean γ slots)."""
    sector = flavor_sector(species_id)
    if sector == "hidden_quarkonium":
        return lean.GAMMA / 16.0 if species_id == "Upsilon" else lean.GAMMA / 8.0
    if sector == "open_bottom":
        return lean.GAMMA / 8.0
    if sector == "open_charm":
        return lean.GAMMA / 4.0
    return 1.0


def phase_space_factor(
    mass_gev: float,
    sqrt_s_gev: float,
    *,
    collision_mode: str = "head_on",
) -> float:
    """
    Kinematic production phase space ∝ (1 − (2m/√s)²)^{3/2} for hadronic collisions;
    e⁺e⁻ uses a narrow on-shell slot near √s/2.
    """
    if sqrt_s_gev <= 0.0 or mass_gev <= 0.0:
        return 0.0
    if collision_mode == "head_on" and sqrt_s_gev < 20.0:
        # e⁺e⁻ annihilation: single on-shell vector state when m ≲ √s.
        if mass_gev > sqrt_s_gev:
            return 0.0
        beta = math.sqrt(max(1.0 - (mass_gev / sqrt_s_gev) ** 2, 0.0))
        pole = math.exp(
            -((sqrt_s_gev - mass_gev) ** 2)
            / max((lean.GAMMA * sqrt_s_gev) ** 2, 1e-6)
        )
        return beta * (1.0 + 3.0 * pole)
    x = 2.0 * mass_gev / sqrt_s_gev
    if x >= 1.0:
        return 0.0
    return max(1.0 - x**2, 0.0) ** 1.5


def ckm_topology_factor(parent_id: str, channel: str) -> float:
    """CKM / weak-rung weight for heavy-flavour decay topology."""
    if channel not in ("weak", "weak_hadron"):
        return 1.0
    if parent_id in OPEN_BOTTOM_MESONS or parent_id in BOTTOM_BARYONS:
        return hdr.ckm_slot_cb_squared()
    if parent_id in OPEN_CHARM_MESONS or parent_id in CHARMED_BARYONS:
        return hdr.ckm_slot_cd_squared()
    if parent_id in ("K_plus", "K_minus", "K0", "K0_bar"):
        return hdr.ckm_slot_us_squared()
    return 1.0


def phase_space_q_weight(q_mev: float, parent_mass_mev: float, n_daughters: int) -> float:
    """Multibody phase-space slot: Q^(n−2) relative to parent mass scale."""
    if q_mev <= 0.0 or parent_mass_mev <= 0.0:
        return 0.0
    q_frac = q_mev / parent_mass_mev
    exponent = max(n_daughters - 2, 0)
    return q_frac**exponent * (1.0 + lean.GAMMA * exponent / 4.0)


def channel_topology_weight(
    *,
    parent_id: str,
    channel: str,
    q_mev: float,
    parent_mass_mev: float,
    n_daughters: int,
    relative_prior: float,
) -> float:
    """Effective topology weight multiplying partial width before BR normalization."""
    ckm = ckm_topology_factor(parent_id, channel)
    ps = phase_space_q_weight(q_mev, parent_mass_mev, n_daughters)
    if channel == "electromagnetic":
        return max(relative_prior, 1e-6)
    if channel == "strong":
        return max(relative_prior, 1e-6) * max(ps, 1e-3)
    return max(relative_prior, 1e-6) * max(ps, 1e-6) * max(ckm, 1e-6)


def normalize_branching_ratios(
    weighted_edges: list[tuple[float, float]],
    *,
    policy: BranchingPolicy = "width_topology",
) -> list[float]:
    """
    Normalize partial widths to branching ratios.

    ``weighted_edges`` is ``[(width_per_s, topology_weight), ...]``.
    """
    if not weighted_edges:
        return []
    if policy == "width_only":
        weights = [w for w, _ in weighted_edges]
    elif policy == "width_prior":
        weights = [w * tw for w, tw in weighted_edges]
    else:
        weights = [w * tw for w, tw in weighted_edges]
    total = sum(weights)
    if total <= 0.0:
        n = len(weights)
        return [1.0 / n] * n if n else []
    return [w / total for w in weights]


def branching_policy_for(parent_id: str) -> BranchingPolicy:
    """New states use topology-weighted widths; quarkonium uses width-only."""
    if parent_id in HIDDEN_QUARKONIA:
        return "width_only"
    if parent_id in NEW_STATE_IDS:
        return "width_topology"
    return "width_prior"


@dataclass(frozen=True)
class ProductionRate:
    species_id: str
    mass_mev: float
    rate_proxy: float
    normalized_fraction: float
    accessible: bool
    flavor_sector: str


def production_rate_proxy(
    species_id: str,
    mass_mev: float,
    *,
    sqrt_s_gev: float,
    accessible_mass_gev: float,
    collision_mode: str = "head_on",
) -> float:
    """Unnormalized production rate proxy at a facility."""
    if mass_mev / 1000.0 > accessible_mass_gev:
        return 0.0
    ps = phase_space_factor(
        mass_mev / 1000.0,
        sqrt_s_gev,
        collision_mode=collision_mode,
    )
    if ps <= 0.0:
        return 0.0
    rate = ps * flavor_production_weight(species_id)
    if flavor_sector(species_id) == "hidden_quarkonium":
        mass_gev = mass_mev / 1000.0
        on_shell = math.exp(
            -((mass_gev - sqrt_s_gev) ** 2)
            / max((0.02 * sqrt_s_gev) ** 2, 1e-9)
        )
        rate *= 1.0 + 100.0 * on_shell
    return rate


def production_rate_table(
    species: list[tuple[str, float]],
    *,
    sqrt_s_gev: float,
    accessible_mass_gev: float,
    collision_mode: str = "head_on",
) -> list[ProductionRate]:
    """Relative production rates for a species list at one collision energy."""
    raw: list[tuple[str, float, float, bool, str]] = []
    for sid, mass in species:
        accessible = mass / 1000.0 <= accessible_mass_gev
        rate = production_rate_proxy(
            sid,
            mass,
            sqrt_s_gev=sqrt_s_gev,
            accessible_mass_gev=accessible_mass_gev,
            collision_mode=collision_mode,
        )
        raw.append((sid, mass, rate, accessible, flavor_sector(sid)))
    total = sum(r for _, _, r, _, _ in raw)
    out: list[ProductionRate] = []
    for sid, mass, rate, accessible, sector in raw:
        frac = rate / total if total > 0 else 0.0
        out.append(
            ProductionRate(
                species_id=sid,
                mass_mev=mass,
                rate_proxy=rate,
                normalized_fraction=frac,
                accessible=accessible,
                flavor_sector=sector,
            )
        )
    return sorted(out, key=lambda r: r.rate_proxy, reverse=True)


def build_production_rates_for_kinematics(
    kin: "hep.CollisionKinematics",
    *,
    species_ids: list[str] | None = None,
    mass_xi: float | None = None,
    collision_mode: str = "head_on",
) -> list[ProductionRate]:
    """Build production table using ``hqiv_hep_decay_chain`` mass readout."""
    import hqiv_hep_decay_chain as hep

    xi = mass_xi if mass_xi is not None else lean.XI_LOCKIN
    if species_ids is None:
        species_ids = sorted(NEW_STATE_IDS)
    species: list[tuple[str, float]] = []
    for sid in species_ids:
        try:
            species.append((sid, hep.particle_mass_mev(sid, xi=xi)))
        except KeyError:
            continue
    return production_rate_table(
        species,
        sqrt_s_gev=kin.sqrt_s_gev,
        accessible_mass_gev=kin.accessible_mass_gev,
        collision_mode=collision_mode,
    )