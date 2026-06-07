#!/usr/bin/env python3
"""
Full multi-channel decay expansion for HQIV HEP decay chains.

Generates open kinematic channels from daughter pools + HQIV topology weights
(OZI suppression, CKM slots, phase-space priors).  Static ``HEP_DECAY_MODES`` seeds
light-hadron topologies; this module expands charm/bottom/quarkonium parents.

Lean mirror: ``HepDecayReadout.lean`` (``oziSuppressionFactor``, branching normalization).
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass
from functools import lru_cache
from typing import Callable, Literal, Sequence

import hqiv_hep_decay_readout as hdr
import hqiv_lean_physics_primitives as lean

MassXi = float
MassLookup = Callable[[str], float]

ChannelTag = Literal["strong", "weak", "electromagnetic", "weak_hadron", "stable"]

# Parents expanded programmatically (static table kept for light hadrons only).
MULTICHANNEL_PARENTS = frozenset(
    {
        "Jpsi",
        "Upsilon",
        "D_plus",
        "D0",
        "Ds_plus",
        "B_plus",
        "B0",
        "Bs",
        "lambda_c",
        "sigma_c",
        "xi_c",
        "omega_c",
        "lambda_b",
        "xi_b",
        "omega_b",
    }
)

# Light hadron daughter pools for hadronic cascades.
PSEUDOSCALAR_POOL: tuple[str, ...] = (
    "pi_plus",
    "pi_minus",
    "pi_zero",
    "K_plus",
    "K_minus",
    "K0",
    "eta",
)

VECTOR_POOL: tuple[str, ...] = (
    "rho_zero",
    "rho_plus",
    "omega_meson",
    "phi",
)

HADRONIC_2BODY_POOL: tuple[str, ...] = PSEUDOSCALAR_POOL + VECTOR_POOL

HADRONIC_3BODY_POOL: tuple[str, ...] = (
    "pi_plus",
    "pi_minus",
    "pi_zero",
    "K_plus",
    "K_minus",
    "K0",
    "rho_zero",
    "eta",
)

CASCADE_POOL: tuple[str, ...] = ("Jpsi", "phi", "rho_zero", "omega_meson")

NEUTRAL_LIGHT_PAIR_CASCADE: tuple[tuple[str, str], ...] = (
    ("pi_plus", "pi_minus"),
    ("pi_zero", "pi_zero"),
    ("pi_zero", "eta"),
    ("eta", "eta"),
    ("K_plus", "K_minus"),
    ("K0", "K0_bar"),
)

EM_LEPTON_MODES: tuple[tuple[str, ...], float, ChannelTag] = (
    (("e_plus", "e_minus"), 1.0, "electromagnetic"),
    (("mu_plus", "mu_minus"), 1.0, "electromagnetic"),
)

EM_RADIATIVE: tuple[tuple[str, ...], float, ChannelTag] = (
    (("gamma", "pi_zero"), hdr.open_flavour_topology_seed_weight(), "electromagnetic"),
    (("gamma", "eta"), hdr.open_flavour_topology_seed_weight(), "electromagnetic"),
)

# Weak templates for open-charm mesons (|V_cd| slot applied in width layer).
OPEN_CHARM_WEAK_TEMPLATES: tuple[tuple[str, ...], ...] = ()

D_PLUS_WEAK_TEMPLATES: tuple[tuple[str, ...], ...] = (
    ("K_minus", "pi_plus"),
    ("K0", "pi_plus"),
    ("K_minus", "pi_plus", "pi_zero"),
    ("K0", "pi_plus", "pi_zero"),
    ("pi_plus", "pi_minus", "pi_zero"),
    ("K_minus", "pi_zero"),
)

D0_WEAK_TEMPLATES: tuple[tuple[str, ...], ...] = (
    ("K_plus", "pi_minus"),
    ("K0", "pi_minus"),
    ("K_plus", "pi_minus", "pi_zero"),
    ("K0", "pi_minus", "pi_zero"),
    ("pi_plus", "pi_minus", "pi_zero"),
    ("K_plus", "pi_zero"),
)

OPEN_CHARM_STRANGE_STRONG: tuple[tuple[str, ...], ...] = (
    ("phi",),
    ("K_plus", "K0"),
    ("K_plus", "K_minus"),
    ("eta", "K_plus"),
    ("phi", "pi_plus"),
    ("eta", "pi_plus"),
)

OPEN_CHARM_STRANGE_WEAK: tuple[tuple[str, ...], ...] = (
    ("K_plus",),
    ("K0", "pi_plus"),
    ("K_plus", "pi_zero"),
    ("K_plus", "K_minus", "pi_plus"),
    ("eta", "pi_plus"),
)

OPEN_BOTTOM_WEAK_TEMPLATES: tuple[tuple[str, ...], ...] = (
    ("D0", "pi_plus"),
    ("D_plus", "pi_zero"),
    ("D_plus", "pi_minus"),
    ("D0", "pi_zero"),
    ("D0", "pi_plus", "pi_zero"),
    ("D_plus", "pi_minus", "pi_zero"),
    ("D0", "rho_plus"),
    ("D_plus", "rho_zero"),
    ("D0", "K_plus"),
    ("Jpsi", "K_plus"),
    ("Jpsi", "K0"),
)

OPEN_BOTTOM_STRANGE_WEAK: tuple[tuple[str, ...], ...] = (
    ("Ds_plus", "K_minus"),
    ("Ds_plus", "pi_minus"),
    ("phi", "phi"),
    ("D0", "K_plus"),
    ("D0", "K0"),
)

CHARMED_BARYON_WEAK: tuple[tuple[str, ...], ...] = (
    ("p", "K_minus", "pi_plus"),
    ("p", "pi_zero"),
    ("n", "K_plus"),
    ("p", "K_minus", "pi_plus", "pi_zero"),
    ("lambda", "K_minus"),
    ("p", "K_plus", "pi_minus"),
)

CHARMED_BARYON_CASCADE: tuple[tuple[str, ...], ...] = (
    ("lambda_c", "pi_zero"),
    ("lambda_c", "pi_plus"),
    ("lambda_c", "pi_minus"),
    ("lambda_c", "K0"),
    ("sigma_c", "pi_zero"),
    ("sigma_c", "pi_plus"),
    ("sigma_c", "K0"),
    ("lambda", "K_plus", "pi_zero"),
    ("p", "K_minus", "K_plus"),
)

BOTTOM_BARYON_WEAK: tuple[tuple[str, ...], ...] = (
    ("lambda_c", "pi_minus"),
    ("lambda_c", "K_minus"),
    ("p", "D0", "pi_minus"),
    ("p", "D0", "K_minus"),
    ("Jpsi", "p", "K_minus"),
)


@dataclass(frozen=True)
class GeneratedMode:
    parent_id: str
    channel: ChannelTag
    daughter_ids: tuple[str, ...]
    relative_branch: float
    source: str = "multichannel"

    @property
    def key(self) -> str:
        d = "+".join(self.daughter_ids) if self.daughter_ids else "stable"
        return f"{self.parent_id}->{self.channel}:{d}"


HEAVY_QUARKONIA = frozenset({"Jpsi", "Upsilon"})

LIGHT_CASCADE_CHARGE: dict[str, int] = {
    "Jpsi": 0,
    "Upsilon": 0,
    "pi_plus": 1,
    "pi_minus": -1,
    "pi_zero": 0,
    "eta": 0,
    "K_plus": 1,
    "K_minus": -1,
    "K0": 0,
    "K0_bar": 0,
}

LIGHT_CASCADE_STRANGENESS: dict[str, int] = {
    "Jpsi": 0,
    "Upsilon": 0,
    "pi_plus": 0,
    "pi_minus": 0,
    "pi_zero": 0,
    "eta": 0,
    "K_plus": 1,
    "K0": 1,
    "K_minus": -1,
    "K0_bar": -1,
}


def _net_light_ledger(daughter_ids: Sequence[str], ledger: dict[str, int]) -> int:
    return sum(ledger.get(d, 0) for d in daughter_ids)


def charge_neutral_light_cascade(daughter_ids: Sequence[str]) -> bool:
    """Charge ledger predicate for inclusive quarkonium cascade candidates."""
    return _net_light_ledger(daughter_ids, LIGHT_CASCADE_CHARGE) == 0


def strangeness_neutral_light_cascade(daughter_ids: Sequence[str]) -> bool:
    """Strangeness ledger predicate for strong quarkonium cascade candidates."""
    return _net_light_ledger(daughter_ids, LIGHT_CASCADE_STRANGENESS) == 0


def strong_neutral_light_cascade(daughter_ids: Sequence[str]) -> bool:
    """Strong-sector ledger: charge and strangeness both discharge to zero."""
    return charge_neutral_light_cascade(daughter_ids) and strangeness_neutral_light_cascade(
        daughter_ids
    )


def ozi_suppression_factor(parent_id: str, daughter_ids: Sequence[str]) -> float:
    """
    OZI / Zweig suppression for hidden quarkonia → light hadrons only.

    Lean ``oziSuppressionFactor`` applies when the final state includes light
    hadrons; all-heavy cascades (e.g. ``Υ → J/ψ``) carry no OZI factor (unity).
    """
    if parent_id not in HEAVY_QUARKONIA:
        return 1.0
    if all(d in HEAVY_QUARKONIA for d in daughter_ids):
        return 1.0
    n_vector = sum(1 for d in daughter_ids if d in VECTOR_POOL)
    return hdr.ozi_suppression_factor(n_vector)


def _strange_count(daughter_ids: Sequence[str]) -> int:
    strange_ids = {"K_plus", "K_minus", "K0", "K0_bar", "phi", "Ds_plus"}
    return sum(1 for d in daughter_ids if d in strange_ids or d.startswith("K"))


def _daughter_mass_sum(daughters: Sequence[str], mass_of: MassLookup) -> float:
    total = 0.0
    for did in daughters:
        try:
            total += mass_of(did)
        except (KeyError, TypeError):
            return math.inf
    return total


def _channel_open(parent_mass_mev: float, daughters: Sequence[str], mass_of: MassLookup) -> bool:
    return _daughter_mass_sum(daughters, mass_of) < parent_mass_mev


def _topology_prior(
    parent_id: str,
    channel: ChannelTag,
    daughters: Sequence[str],
    *,
    parent_mass_mev: float,
    mass_of: MassLookup,
) -> float:
    """Relative prior before width normalization."""
    q = parent_mass_mev - _daughter_mass_sum(daughters, mass_of)
    if q <= 0.0:
        return 0.0
    q_frac = q / parent_mass_mev
    n = len(daughters)
    ps = q_frac ** max(n - 2, 0) * (1.0 + lean.GAMMA * max(n - 2, 0) / 4.0)
    oz = ozi_suppression_factor(parent_id, daughters)
    ss = 1.0 + lean.GAMMA * _strange_count(daughters) / 8.0
    if channel == "electromagnetic":
        return max(ps, 1e-3)
    if channel == "strong":
        return max(ps * oz * ss, 1e-6)
    # weak
    if parent_id in ("D_plus", "D0", "Ds_plus", "lambda_c", "sigma_c", "xi_c", "omega_c"):
        return max(ps * hdr.ckm_slot_cd_squared() / max(hdr.ckm_slot_us_squared(), 1e-9), 1e-6)
    if parent_id in ("B_plus", "B0", "Bs", "lambda_b", "xi_b", "omega_b"):
        return max(ps * hdr.ckm_slot_cb_squared() / max(hdr.ckm_slot_us_squared(), 1e-9), 1e-6)
    return max(ps, 1e-6)


def _add_mode(
    out: list[GeneratedMode],
    seen: set[str],
    *,
    parent_id: str,
    channel: ChannelTag,
    daughters: tuple[str, ...],
    base_prior: float,
    parent_mass_mev: float,
    mass_of: MassLookup,
    source: str,
) -> None:
    if not _channel_open(parent_mass_mev, daughters, mass_of):
        return
    topo = _topology_prior(
        parent_id,
        channel,
        daughters,
        parent_mass_mev=parent_mass_mev,
        mass_of=mass_of,
    )
    prior = base_prior * topo
    if prior <= 0.0:
        return
    mode = GeneratedMode(
        parent_id=parent_id,
        channel=channel,
        daughter_ids=daughters,
        relative_branch=prior,
        source=source,
    )
    if mode.key in seen:
        return
    seen.add(mode.key)
    out.append(mode)


def open_flavour_topology_weight(
    parent_id: str,
    channel: ChannelTag,
    daughters: Sequence[str],
) -> float:
    """Lean-backed seed weight from topology labels, not PDG branching priors."""
    return hdr.open_flavour_contact_weight(
        open_flavour_contact_kind(parent_id, channel, daughters)
    )


def open_flavour_contact_kind(
    parent_id: str,
    channel: ChannelTag,
    daughters: Sequence[str],
) -> hdr.OpenFlavourContactKind:
    """Uniform contact selector mirrored by Lean `OpenFlavourContactKind`."""
    ds = tuple(daughters)
    if channel != "weak":
        return "unit_seed"

    if parent_id in ("D_plus", "D0") and not any(d.startswith("K") for d in ds):
        return "charm_pion_only"

    if parent_id == "Ds_plus" and len(ds) >= 2:
        return "finite_channel_completion"

    if parent_id == "lambda_c" and ds == ("p", "K_minus", "pi_plus"):
        return "charmed_baryon_three_body"

    if parent_id in ("xi_c", "omega_c") and ds == ("lambda_c", "pi_zero"):
        return "neutral_spectator_complement"

    if parent_id in ("xi_c", "omega_c") and (
        any(d in {"lambda_c", "sigma_c"} for d in ds) or len(ds) >= 3
    ):
        return "finite_channel_completion"

    if parent_id in ("B_plus", "B0") and ds in (("D0", "pi_plus"), ("D_plus", "pi_minus")):
        return "bottom_external_weak"

    if parent_id in ("B_plus", "B0") and any(d.startswith("D") for d in ds):
        return "finite_channel_completion"

    if parent_id == "Bs" and ds == ("Ds_plus", "K_minus"):
        return "bottom_strange_double_monogamy"

    if parent_id == "Bs" and "Ds_plus" in ds:
        return "spectator_half_monogamy"

    return "unit_seed"


def _two_body_combos(pool: Sequence[str]) -> list[tuple[str, ...]]:
    combos: list[tuple[str, ...]] = []
    for combo in itertools.combinations_with_replacement(pool, 2):
        combos.append(combo)
    return combos


def _three_body_combos(pool: Sequence[str], *, max_count: int = 120) -> list[tuple[str, ...]]:
    combos: list[tuple[str, ...]] = []
    for combo in itertools.combinations_with_replacement(pool, 3):
        combos.append(combo)
        if len(combos) >= max_count:
            break
    return combos


def _generate_quarkonium_modes(
    parent_id: str,
    *,
    parent_mass_mev: float,
    mass_of: MassLookup,
) -> list[GeneratedMode]:
    out: list[GeneratedMode] = []
    seen: set[str] = set()

    for combo in _two_body_combos(HADRONIC_2BODY_POOL):
        _add_mode(
            out,
            seen,
            parent_id=parent_id,
            channel="strong",
            daughters=combo,
            base_prior=1.0,
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="quarkonium_2body",
        )

    for combo in _three_body_combos(HADRONIC_3BODY_POOL):
        _add_mode(
            out,
            seen,
            parent_id=parent_id,
            channel="strong",
            daughters=combo,
            base_prior=hdr.open_flavour_topology_seed_weight(),
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="quarkonium_3body",
        )

    if parent_id == "Upsilon":
        for light in CASCADE_POOL:
            if light == "Jpsi":
                base = hdr.open_charm_production_weight()
            else:
                base = hdr.open_bottom_production_weight()
            _add_mode(
                out,
                seen,
                parent_id=parent_id,
                channel="strong",
                daughters=(light,),
                base_prior=base,
                parent_mass_mev=parent_mass_mev,
                mass_of=mass_of,
                source="quarkonium_cascade",
            )
            for meson in PSEUDOSCALAR_POOL:
                _add_mode(
                    out,
                    seen,
                    parent_id=parent_id,
                    channel="strong",
                    daughters=(light, meson),
                    base_prior=hdr.open_flavour_topology_seed_weight(),
                    parent_mass_mev=parent_mass_mev,
                    mass_of=mass_of,
                    source="quarkonium_cascade_2body",
                )
        for pair in NEUTRAL_LIGHT_PAIR_CASCADE:
            daughters = ("Jpsi",) + pair
            if not strong_neutral_light_cascade(daughters):
                continue
            _add_mode(
                out,
                seen,
                parent_id=parent_id,
                channel="strong",
                daughters=daughters,
                base_prior=hdr.neutral_light_pair_cascade_weight(),
                parent_mass_mev=parent_mass_mev,
                mass_of=mass_of,
                source="quarkonium_cascade_neutral_pair",
            )

    for daughters, base, ch in EM_LEPTON_MODES + EM_RADIATIVE:
        _add_mode(
            out,
            seen,
            parent_id=parent_id,
            channel=ch,
            daughters=daughters,
            base_prior=base,
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="quarkonium_em",
        )

    return out


def _generate_from_templates(
    parent_id: str,
    templates: Sequence[tuple[str, ...]],
    channel: ChannelTag,
    *,
    parent_mass_mev: float,
    mass_of: MassLookup,
    source: str,
) -> list[GeneratedMode]:
    out: list[GeneratedMode] = []
    seen: set[str] = set()
    for daughters in templates:
        _add_mode(
            out,
            seen,
            parent_id=parent_id,
            channel=channel,
            daughters=daughters,
            base_prior=open_flavour_topology_weight(parent_id, channel, daughters),
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source=source,
        )
    return out


def generate_multichannel_modes(
    parent_id: str,
    *,
    parent_mass_mev: float,
    mass_of: MassLookup,
) -> list[GeneratedMode]:
    """All kinematically open generated modes for a parent species."""
    sid = parent_id
    if sid not in MULTICHANNEL_PARENTS:
        return []

    if sid in ("Jpsi", "Upsilon"):
        return _generate_quarkonium_modes(sid, parent_mass_mev=parent_mass_mev, mass_of=mass_of)

    if sid in ("D_plus",):
        return _generate_from_templates(
            sid,
            D_PLUS_WEAK_TEMPLATES,
            "weak",
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="open_charm_weak",
        )

    if sid == "D0":
        return _generate_from_templates(
            sid,
            D0_WEAK_TEMPLATES,
            "weak",
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="open_charm_weak",
        )

    if sid == "Ds_plus":
        strong = _generate_from_templates(
            sid,
            OPEN_CHARM_STRANGE_STRONG,
            "strong",
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="open_charm_strange_strong",
        )
        weak = _generate_from_templates(
            sid,
            OPEN_CHARM_STRANGE_WEAK,
            "weak",
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="open_charm_strange_weak",
        )
        return strong + weak

    if sid in ("B_plus", "B0"):
        return _generate_from_templates(
            sid,
            OPEN_BOTTOM_WEAK_TEMPLATES,
            "weak",
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="open_bottom_weak",
        )

    if sid == "Bs":
        return _generate_from_templates(
            sid,
            OPEN_BOTTOM_STRANGE_WEAK,
            "weak",
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="open_bottom_strange_weak",
        )

    if sid in ("lambda_c", "sigma_c"):
        return _generate_from_templates(
            sid,
            CHARMED_BARYON_WEAK,
            "weak",
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="charmed_baryon_weak",
        )

    if sid in ("xi_c", "omega_c"):
        return _generate_from_templates(
            sid,
            CHARMED_BARYON_CASCADE,
            "weak",
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="charmed_baryon_cascade",
        )

    if sid in ("lambda_b", "xi_b", "omega_b"):
        return _generate_from_templates(
            sid,
            BOTTOM_BARYON_WEAK,
            "weak",
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="bottom_baryon_weak",
        )

    return []


@lru_cache(maxsize=64)
def open_channel_count(parent_id: str, parent_mass_mev: float, xi: MassXi) -> int:
    """Count open generated channels (for benchmarks)."""
    import hqiv_hep_decay_chain as hep

    def mass_of(sid: str) -> float:
        return hep.particle_mass_mev(sid, xi=xi)

    return len(
        generate_multichannel_modes(
            parent_id,
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
        )
    )
