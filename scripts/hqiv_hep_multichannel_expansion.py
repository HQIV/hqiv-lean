#!/usr/bin/env python3
"""
Full multi-channel decay expansion for HQIV HEP decay chains.

Generates open kinematic channels from daughter pools + HQIV topology weights
(OZI suppression, CKM slots, phase-space priors).  Light hadrons, charm/bottom,
and quarkonium parents are enumerated here from patch-ledger rules.

Lean mirror: ``HepDecayReadout.lean`` (``oziSuppressionFactor``, branching normalization).
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass
from functools import lru_cache
from typing import Callable, Literal, Sequence

import hqiv_hep_decay_certificates as cert
import hqiv_hep_decay_readout as hdr
import hqiv_lean_physics_primitives as lean
import hqiv_mass_calculator_core as hmc

MassXi = float
MassLookup = Callable[[str], float]

ChannelTag = Literal["strong", "weak", "electromagnetic", "weak_hadron", "stable"]

# ---------------------------------------------------------------------------
# Patch ledger: dynamic channel enumeration (charge / S / C / B / baryon number)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class HadronLedger:
    """Integer patch quantum numbers (charge stored as 3× electron charge)."""

    q3: int
    strangeness: int
    charm: int
    bottom: int
    a3: int  # baryon number × 3 (0 meson, 3 baryon)


_QUARK_Q3 = {"u": 2, "d": -1, "s": -1, "c": 2, "b": -1, "t": 2}
_QUARK_S = {"s": 1}
_QUARK_C = {"c": 1}
_QUARK_B = {"b": 1}


def _ledger_from_valence(valence: Sequence[tuple[str, str]]) -> HadronLedger:
    q3 = 0
    s = c = b = 0
    a3 = 0
    for flavor, role in valence:
        sign = 1 if role == "quark" else -1
        a3 += sign
        q3 += sign * _QUARK_Q3.get(flavor, 0)
        c += sign * _QUARK_C.get(flavor, 0)
        if flavor == "s":
            s -= sign
        elif flavor == "b":
            b -= sign
    return HadronLedger(q3=q3, strangeness=s, charm=c, bottom=b, a3=a3)


def _ledger_sum(ledgers: Sequence[HadronLedger]) -> HadronLedger:
    return HadronLedger(
        q3=sum(x.q3 for x in ledgers),
        strangeness=sum(x.strangeness for x in ledgers),
        charm=sum(x.charm for x in ledgers),
        bottom=sum(x.bottom for x in ledgers),
        a3=sum(x.a3 for x in ledgers),
    )


@lru_cache(maxsize=1)
def _species_ledger_index() -> dict[str, HadronLedger]:
    out: dict[str, HadronLedger] = {}
    for row in hmc.parse_hadron_catalog():
        sid = row["config_id"]
        out[sid] = _ledger_from_valence(row.get("valence") or [])
    # Stable / leptonic slots used in pools but absent from hadron catalog.
    out.setdefault("gamma", HadronLedger(0, 0, 0, 0, 0))
    out.setdefault("e_plus", HadronLedger(3, 0, 0, 0, 0))
    out.setdefault("e_minus", HadronLedger(-3, 0, 0, 0, 0))
    out.setdefault("mu_plus", HadronLedger(3, 0, 0, 0, 0))
    out.setdefault("mu_minus", HadronLedger(-3, 0, 0, 0, 0))
    return out


def species_ledger(species_id: str) -> HadronLedger | None:
    import hqiv_hep_patch_species as hps

    sid = hps.resolve_species_alias(species_id)
    manual = _MANUAL_SPECIES_LEDGER.get(sid)
    if manual is not None:
        return manual
    return _species_ledger_index().get(sid)


# Light / vector pool members absent from the hadron catalog JS parse.
_MANUAL_SPECIES_LEDGER: dict[str, HadronLedger] = {
    "pi_zero": HadronLedger(0, 0, 0, 0, 0),
    "eta": HadronLedger(0, 0, 0, 0, 0),
    "K0": HadronLedger(0, 1, 0, 0, 0),
    "K0_bar": HadronLedger(0, -1, 0, 0, 0),
    "rho_zero": HadronLedger(0, 0, 0, 0, 0),
    "rho_plus": HadronLedger(3, 0, 0, 0, 0),
    "omega_meson": HadronLedger(0, 0, 0, 0, 0),
    "phi": HadronLedger(0, 0, 0, 0, 0),
    "Jpsi": HadronLedger(0, 0, 0, 0, 0),
    "Upsilon": HadronLedger(0, 0, 0, 0, 0),
    "gamma": HadronLedger(0, 0, 0, 0, 0),
}


OPEN_CHARM_MESONS = frozenset({"D_plus", "D0", "Ds_plus"})
OPEN_BOTTOM_MESONS = frozenset({"B_plus", "B0", "Bs"})
CHARMED_BARYONS = frozenset({"lambda_c", "sigma_c", "xi_c", "omega_c"})
BOTTOM_BARYONS = frozenset({"lambda_b", "sigma_b", "xi_b", "omega_b"})
OPEN_CHARM_DAUGHTERS = ("D_plus", "D0", "Ds_plus")
CHARMED_BARYON_DAUGHTERS = ("lambda_c", "sigma_c")
LIGHT_BARYON_DAUGHTERS = (
    "p",
    "n",
    "lambda",
    "sigma_plus",
    "sigma_zero",
    "sigma_minus",
    "xi_zero",
    "xi_minus",
)

DECUPLET_BARYONS = frozenset(
    {
        "delta_p",
        "delta_pp",
        "delta_0",
        "delta_m",
        "sigma_star_p",
        "sigma_star_0",
        "sigma_star_m",
    }
)

LIGHT_STRANGE_BARYONS = frozenset(
    {
        "lambda",
        "sigma_plus",
        "sigma_zero",
        "sigma_minus",
        "xi_zero",
        "xi_minus",
        "omega",
    }
)

LIGHT_VECTOR_MESONS = frozenset({"rho_plus", "rho_zero", "omega_meson", "phi"})

LIGHT_KAONS = frozenset({"K_plus", "K_minus", "K0"})

LIGHT_LEPTONIC_WEAK_PARENTS = frozenset(
    {"pi_plus", "pi_minus", "pi_zero", "K_plus", "K_minus", "mu_plus", "mu_minus"}
)

LIGHT_MULTICHANNEL_PARENTS = (
    DECUPLET_BARYONS
    | LIGHT_STRANGE_BARYONS
    | LIGHT_VECTOR_MESONS
    | LIGHT_KAONS
    | LIGHT_LEPTONIC_WEAK_PARENTS
)

# Parents expanded programmatically from patch ledgers (no static channel table).
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
) | LIGHT_MULTICHANNEL_PARENTS

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


def _daughter_ledgers(daughter_ids: Sequence[str]) -> list[HadronLedger] | None:
    ledgers: list[HadronLedger] = []
    for did in daughter_ids:
        ledger = species_ledger(did)
        if ledger is None:
            return None
        ledgers.append(ledger)
    return ledgers


def _ledger_delta(parent: HadronLedger, total: HadronLedger) -> HadronLedger:
    return HadronLedger(
        q3=total.q3 - parent.q3,
        strangeness=total.strangeness - parent.strangeness,
        charm=total.charm - parent.charm,
        bottom=total.bottom - parent.bottom,
        a3=total.a3 - parent.a3,
    )


def _weak_hadronic_allowed(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """
    Single-step weak-hadronic transition on the patch ledger.

    Hadronic charge may fail to close: the implicit W/Fano bridge slot (Ledger III)
    carries the mismatch.  Baryon number and heavy-flavour steps remain exact.
    """
    parent = species_ledger(parent_id)
    parent_patch = _parent_patch(parent_id)
    ledgers = _daughter_ledgers(daughter_ids)
    if parent is None or parent_patch is None or not ledgers:
        return False
    total = _ledger_sum(ledgers)
    if total.a3 != parent.a3:
        return False
    delta = _ledger_delta(parent, total)
    if abs(delta.strangeness) > 1:
        return False

    if parent_patch.is_open_charm_meson_nonstrange:
        return delta.charm == -1 and delta.bottom == 0

    if parent_patch.is_open_charm_strange_meson:
        return delta.charm == -1 and delta.bottom == 0

    if parent_patch.sector == "open_bottom_meson":
        return delta.bottom == -1 and delta.charm in (0, 1)

    if parent_patch.is_open_charm_baryon_cascade:
        return delta.bottom == 0 and delta.charm in (0, -1)

    if parent_patch.is_open_charm_baryon_ground:
        return delta.charm == -1 and delta.bottom == 0

    if parent_patch.is_open_bottom_baryon:
        return delta.bottom == -1 and delta.charm in (0, 1)

    if parent_patch.is_light_kaon:
        ps = parent.strangeness
        return delta.charm == 0 and delta.bottom == 0 and delta.strangeness == -ps

    if parent_patch.is_light_strange_baryon and not parent_patch.is_decuplet_baryon:
        return delta.charm == 0 and delta.bottom == 0 and abs(delta.strangeness) <= 1

    return False


D_WEAK_LIGHT: tuple[str, ...] = (
    "pi_plus",
    "pi_minus",
    "pi_zero",
    "K_plus",
    "K_minus",
    "K0",
    "K0_bar",
)

OPEN_BOTTOM_WEAK_LIGHT: tuple[str, ...] = (
    "pi_plus",
    "pi_minus",
    "pi_zero",
    "rho_plus",
    "rho_zero",
    "K_plus",
    "K_minus",
    "K0",
)


def _hadronic_charge_residual_q3(parent_id: str, daughter_ids: Sequence[str]) -> int | None:
    parent = species_ledger(parent_id)
    ledgers = _daughter_ledgers(daughter_ids)
    if parent is None or not ledgers:
        return None
    return parent.q3 - _ledger_sum(ledgers).q3


def _single_w_charge_load_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """At most one W± bridge unit (|residual charge| ≤ |e|)."""
    residual = _hadronic_charge_residual_q3(parent_id, daughter_ids)
    if residual is None:
        return False
    return abs(residual) <= 3


def _kaon_outlet_sign_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """
    Cabibbo kaon outlet orientation from parent charge class (ledger rule):

    * q₃(parent) > 0 → charged kaon q₃ ≤ 0 (D⁺ → K⁻ / K⁰)
    * q₃(parent) < 0 → charged kaon q₃ ≥ 0
    * q₃(parent) = 0 → charged kaon q₃ ≥ 0 (D⁰ → K⁺ / K⁰)
    """
    import hqiv_hep_patch_species as hps

    parent = species_ledger(parent_id)
    if parent is None:
        return False
    for did in daughter_ids:
        dp = hps.daughter_patch(did)
        if dp is None or not hps.is_charged_kaon_patch(dp):
            continue
        if parent.q3 > 0 and dp.ledger.q3 > 0:
            return False
        if parent.q3 < 0 and dp.ledger.q3 < 0:
            return False
        if parent.q3 == 0 and dp.ledger.q3 < 0:
            return False
    return True


DS_WEAK_LIGHT: tuple[str, ...] = (
    "K_plus",
    "K0",
    "K0_bar",
    "pi_plus",
    "pi_minus",
    "pi_zero",
    "eta",
)


def _parent_charged_pion_id(parent_id: str) -> str | None:
    """Leading-charge pion tag for open-charm / bottom weak outlets."""
    parent = species_ledger(parent_id)
    if parent is None:
        return None
    if parent.q3 > 0:
        return "pi_plus"
    if parent.q3 < 0:
        return "pi_minus"
    if parent_id == "D0":
        return "pi_minus"
    return None


def _open_charm_kaon_vector_mode_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Open-charm K + light-vector / K* two-body weak outlet."""
    import hqiv_hep_patch_species as hps

    ds = tuple(daughter_ids)
    if len(ds) != 2:
        return False
    kaons = _kaon_daughters(ds)
    if len(kaons) != 1:
        return False
    vectors = [
        d
        for d in ds
        if (p := hps.daughter_patch(d)) is not None
        and p.is_light_vector_meson
    ]
    if len(vectors) != 1:
        return False
    if parent_id == "D0" and not hps.daughters_include_property(ds, hps.is_neutral_kaon_patch, count=1):
        return False
    return _single_w_charge_load_ok(parent_id, ds) and _kaon_outlet_sign_ok(parent_id, ds)


def _open_charm_kaon_eta_mode_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Open-charm K + η two-body weak outlet (isoscalar pseudoscalar leak)."""
    import hqiv_hep_patch_species as hps

    ds = tuple(daughter_ids)
    if len(ds) != 2:
        return False
    kaons = _kaon_daughters(ds)
    if len(kaons) != 1:
        return False
    if not hps.daughters_include_property(ds, hps.is_eta_patch, count=1):
        return False
    if not hps.daughters_include_property(ds, hps.is_neutral_kaon_patch, count=1):
        return False
    if hps.daughters_include_property(ds, lambda p: p.nominal_id == "K0_bar"):
        return False
    return _single_w_charge_load_ok(parent_id, ds) and _kaon_outlet_sign_ok(parent_id, ds)


def _open_charm_kaon_mode_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Minimal Kπ / Kππ weak span (one neutral-K representative, fixed charged pion)."""
    import hqiv_hep_patch_species as hps

    ds = tuple(daughter_ids)
    n = len(ds)
    kaons = _kaon_daughters(ds)
    if not kaons:
        return False
    if any(
        (p := hps.daughter_patch(d)) is not None
        and p.nominal_id == "K0_bar"
        for d in ds
    ):
        return False
    if n == 2:
        charged = _parent_charged_pion_id(parent_id)
        return charged is not None and charged in ds
    if n == 3:
        charged = _parent_charged_pion_id(parent_id)
        return (
            charged is not None
            and charged in ds
            and hps.daughters_include_property(ds, hps.is_pi_zero_patch, count=1)
            and len(kaons) == 1
            and all(
                (p := hps.daughter_patch(d)) is not None
                and (hps.is_kaon_discharge_patch(p) or hps.is_pion_discharge_patch(p))
                for d in ds
            )
        )
    return False


def _open_charm_light_pseudoscalar_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Three light-pseudoscalar weak span: one +, one −, one π⁰ (discharge tags)."""
    import hqiv_hep_patch_species as hps

    ds = tuple(daughter_ids)
    plus = sum(
        1
        for d in ds
        if (p := hps.daughter_patch(d)) and p.isospin == "charged" and p.ledger.q3 > 0
    )
    minus = sum(
        1
        for d in ds
        if (p := hps.daughter_patch(d)) and p.isospin == "charged" and p.ledger.q3 < 0
    )
    neutral = hps.daughters_include_property(ds, hps.is_pi_zero_patch, count=1)
    return plus == 1 and minus == 1 and neutral


def _bottom_heavy_daughter_ok(parent_id: str, heavy_id: str) -> bool:
    parent = _parent_patch(parent_id)
    heavy = _parent_patch(heavy_id)
    if parent is None or heavy is None:
        return False
    if parent.is_open_bottom_meson_strange:
        return heavy.is_open_charm_strange_meson
    if parent.sector == "open_bottom_meson":
        return heavy.is_open_charm_meson_nonstrange or (
            heavy.is_hidden_quarkonium and heavy.hidden_content == "charm"
        )
    return True


def _bottom_two_body_ok(parent_id: str, heavy_id: str, light_id: str) -> bool:
    parent = species_ledger(parent_id)
    heavy = species_ledger(heavy_id)
    light = species_ledger(light_id)
    heavy_patch = _daughter_patch(heavy_id)
    if parent is None or heavy is None or light is None:
        return False
    total_q3 = heavy.q3 + light.q3
    if total_q3 == parent.q3:
        return True
    if (
        heavy_patch is not None
        and heavy_patch.is_hidden_quarkonium
        and heavy_patch.hidden_content == "charm"
    ):
        return abs(parent.q3 - total_q3) <= 3
    if heavy.q3 == 0 and light.q3 == parent.q3:
        return True
    if heavy.q3 == parent.q3 and light.q3 == -parent.q3:
        return True
    return False


def _visible_charge_closes(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    residual = _hadronic_charge_residual_q3(parent_id, daughter_ids)
    return residual is not None and residual == 0


def _lambda_c_weak_topology(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Λc weak: property sparse topology."""
    import hqiv_property_spanning as ps

    parent = _parent_patch(parent_id)
    if parent is None:
        return False
    return ps.weak_sparse_topology_ok(parent_id, daughter_ids)


def _ds_weak_topology(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """D_s weak: property sparse topology."""
    import hqiv_property_spanning as ps

    return ps.weak_sparse_topology_ok(parent_id, daughter_ids)


def _bs_weak_topology(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """B_s weak: property sparse topology."""
    import hqiv_property_spanning as ps

    return ps.weak_sparse_topology_ok(parent_id, daughter_ids)


def _xi_cascade_topology(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Ξ_c / Ω_c weak: property sparse topology."""
    import hqiv_property_spanning as ps

    return ps.weak_sparse_topology_ok(parent_id, daughter_ids)


def _bottom_three_body_ok(parent_id: str, heavy_id: str, light_ids: Sequence[str]) -> bool:
    import hqiv_hep_patch_species as hps

    if len(light_ids) != 2 or not _has_pion_discharge(light_ids):
        return False
    if not hps.daughters_include_property(light_ids, hps.is_pi_zero_patch, count=1):
        return False
    other = next(
        d
        for d in light_ids
        if (p := hps.daughter_patch(d)) is None or not hps.is_pi_zero_patch(p)
    )
    parent = species_ledger(parent_id)
    heavy = species_ledger(heavy_id)
    other_l = species_ledger(other)
    heavy_patch = _daughter_patch(heavy_id)
    if parent is None or heavy is None or other_l is None:
        return False
    if parent.q3 == 0:
        return (
            heavy_patch is not None
            and heavy_patch.is_open_charm_meson_nonstrange
            and heavy_patch.ledger.q3 == 0
            and other_l.q3 > 0
        )
    charged = _parent_charged_pion_id(parent_id)
    if (
        heavy_patch is not None
        and heavy_patch.is_open_charm_meson_nonstrange
        and heavy_patch.ledger.q3 == 0
        and other == charged
    ):
        return True
    return heavy.q3 == parent.q3 and other_l.q3 == -parent.q3


def _parent_patch(parent_id: str):
    import hqiv_hep_patch_species as hps

    return hps.patch_from_species_id(parent_id)


def _daughter_patch(daughter_id: str):
    import hqiv_hep_patch_species as hps

    return hps.daughter_patch(daughter_id)


def _has_pion_discharge(daughter_ids: Sequence[str]) -> bool:
    import hqiv_hep_patch_species as hps

    return hps._daughter_predicate_ok(daughter_ids, hps.is_pion_discharge_patch)


def _has_charged_pion_for_parent(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    import hqiv_hep_patch_species as hps

    parent = _parent_patch(parent_id)
    if parent is None:
        return False
    for did in daughter_ids:
        dp = hps.daughter_patch(did)
        if dp is not None and hps.is_charged_pion_for_parent(parent, dp):
            return True
    return False


def _kaon_daughters(daughter_ids: Sequence[str]) -> list[str]:
    import hqiv_hep_patch_species as hps

    return [d for d in daughter_ids if (p := hps.daughter_patch(d)) and hps.is_kaon_discharge_patch(p)]


def _open_charm_daughters(daughter_ids: Sequence[str]) -> list[str]:
    import hqiv_hep_patch_species as hps

    return [
        d
        for d in daughter_ids
        if (p := hps.daughter_patch(d)) and hps.is_open_charm_daughter_patch(p)
    ]


def _nucleon_daughters(daughter_ids: Sequence[str]) -> list[str]:
    import hqiv_hep_patch_species as hps

    return [
        d for d in daughter_ids if (p := hps.daughter_patch(d)) and hps.is_nucleon_patch(p)
    ]


def _lambda_octet_daughters(daughter_ids: Sequence[str]) -> list[str]:
    import hqiv_hep_patch_species as hps

    return [
        d
        for d in daughter_ids
        if (p := hps.daughter_patch(d)) and hps.is_lambda_octet_patch(p)
    ]


def _vector_pion_discharge_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """
    Neutral-vector → ππ: require charged-conjugate discharge (T₃=0 isovector).

    Excludes π⁰π⁰ for ρ⁰ — same charge ledger as π⁺π⁻ but wrong G/HQIV discharge class.
    """
    import hqiv_hep_patch_species as hps

    parent = _parent_patch(parent_id)
    if parent is None:
        return True
    if not hps.is_neutral_isovector_vector(parent):
        return True
    if len(daughter_ids) != 2:
        return True
    if not _has_pion_discharge(daughter_ids):
        return True
    plus = hps.daughters_include_property(
        daughter_ids, lambda p: p.isospin == "charged" and p.ledger.q3 > 0, count=1
    )
    minus = hps.daughters_include_property(
        daughter_ids, lambda p: p.isospin == "charged" and p.ledger.q3 < 0, count=1
    )
    return plus and minus


def _light_strong_topology_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Strong light-hadron topology from discharge classes (not a fitted channel table)."""
    import hqiv_hep_patch_species as hps

    if not _vector_pion_discharge_ok(parent_id, daughter_ids):
        return False
    parent = _parent_patch(parent_id)
    if parent is None:
        return False
    ds = tuple(daughter_ids)
    n = len(ds)
    if parent.is_light_vector_meson:
        if parent.is_isoscalar_vector:
            return n == 3 and _has_pion_discharge(ds)
        return n == 2 and _has_pion_discharge(ds)
    if parent.sector == "meson_hidden_strangeness":
        if n == 2 and all(
            (p := hps.daughter_patch(d)) is not None and p.is_light_kaon for d in ds
        ):
            return True
        return n == 3 and _has_pion_discharge(ds)
    if parent.is_decuplet_baryon:
        if n != 2:
            return False
        baryons = [d for d in ds if (p := hps.daughter_patch(d)) and hps.is_light_baryon_discharge_patch(p)]
        pions = [d for d in ds if (p := hps.daughter_patch(d)) and hps.is_pion_discharge_patch(p)]
        return len(baryons) == 1 and len(pions) == 1
    if parent.is_sigma_octet and parent.ledger.q3 > 0:
        return (
            n == 2
            and hps.daughters_include_property(ds, hps.is_nucleon_patch, count=1)
            and hps.daughters_include_property(
                ds,
                lambda p: hps.is_pion_discharge_patch(p) and p.isospin == "neutral_isovector",
                count=1,
            )
        )
    if parent.is_sigma_octet and parent.ledger.q3 < 0:
        return (
            n == 2
            and hps.daughters_include_property(
                ds,
                lambda p: p.sector == "baryon_nucleon" and p.ledger.q3 < 0,
                count=1,
            )
            and hps.daughters_include_property(
                ds,
                lambda p: hps.is_pion_discharge_patch(p) and p.isospin == "charged" and p.ledger.q3 < 0,
                count=1,
            )
        )
    if parent.is_sigma_octet or parent.is_xi_octet:
        return (
            n == 2
            and hps.daughters_include_property(ds, hps.is_lambda_octet_patch, count=1)
            and _has_pion_discharge(ds)
        )
    return False


def _light_weak_hadronic_topology_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Sparse weak hadronic topology for kaons and hyperons (Lean certificates)."""
    if not _single_w_charge_load_ok(parent_id, daughter_ids):
        return False
    parent = _parent_patch(parent_id)
    if parent is None:
        return False
    if parent.is_lambda_octet or parent.is_light_kaon:
        import hqiv_property_spanning as ps

        return ps.weak_sparse_topology_ok(parent_id, daughter_ids)
    if parent.is_light_strange_baryon and not parent.is_decuplet_baryon:
        import hqiv_hep_patch_species as hps

        ds = tuple(daughter_ids)
        if len(ds) != 2:
            return False
        baryons = [
            d
            for d in ds
            if (p := hps.daughter_patch(d)) and hps.is_light_baryon_discharge_patch(p)
        ]
        pions = [
            d for d in ds if (p := hps.daughter_patch(d)) and hps.is_pion_discharge_patch(p)
        ]
        return len(baryons) == 1 and len(pions) == 1
    return False


def _open_charm_leptonic_weak_modes(parent_id: str) -> tuple[tuple[str, ...], ...]:
    """Visible-lepton weak outlets on open-charm parents (Lean ``*SemileptonicWeakModes``)."""
    parent = _parent_patch(parent_id)
    if parent is None:
        return ()
    if parent.is_open_charm_meson_nonstrange:
        if parent.ledger.q3 > 0:
            return (("mu_plus",), ("e_plus",))
        if parent.ledger.q3 == 0:
            return (("mu_minus",), ("e_minus",))
    if parent.is_open_charm_baryon_ground and parent.nominal_id == "lambda_c":
        return (("mu_plus",), ("e_plus",))
    return ()


def _light_leptonic_weak_modes(parent_id: str) -> tuple[tuple[str, ...], ...]:
    """Semileptonic / radiative weak slots (single-W or EM-tagged readout)."""
    parent = _parent_patch(parent_id)
    if parent is None:
        return ()
    if parent.is_light_pseudoscalar_decay_parent:
        if parent.ledger.q3 > 0:
            return (("mu_plus",),)
        if parent.ledger.q3 < 0:
            return (("mu_minus",),)
        if parent.isospin == "neutral_isovector":
            return (("gamma",), ("e_plus", "e_minus"))
    if parent.is_light_kaon:
        if parent.ledger.q3 > 0:
            return (("mu_plus",),)
        if parent.ledger.q3 < 0:
            return (("mu_minus",),)
    if parent.sector == "lepton" and parent.nominal_id == "mu_plus":
        return (("e_plus",),)
    if parent.sector == "lepton" and parent.nominal_id == "mu_minus":
        return (("e_minus",),)
    return ()


def _light_weak_channel_allowed(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    return _weak_hadronic_allowed(parent_id, daughter_ids) and _light_weak_hadronic_topology_ok(
        parent_id, daughter_ids
    )


def _light_strong_channel_allowed(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    import hqiv_hep_decay_certificates as cert

    parent = _parent_patch(parent_id)
    if parent is not None and cert.has_certified_strong_span(parent):
        return (
            _strong_curvature_allowed(parent_id, daughter_ids)
            and cert.matches_certified_strong(parent, daughter_ids)
            and _light_strong_topology_ok(parent_id, daughter_ids)
        )
    return _strong_curvature_allowed(parent_id, daughter_ids) and _light_strong_topology_ok(
        parent_id, daughter_ids
    )


def _weak_topology_sparse(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """
    Sparse weak topology from patch rules (not a fitted channel table):

    * Open charm: oriented K + π outlets, or ≥3 pions; single-W charge load.
    * Open bottom: one D or J/ψ + light spectators; 3-body pions only.
    * Charmed baryons: p/n + charged K + π three-body; Ξ cascade to Λ_c/Σ_c.
    """
    import hqiv_hep_patch_species as hps

    parent = _parent_patch(parent_id)
    if parent is None:
        return False
    ds = tuple(daughter_ids)
    n = len(ds)
    heavy = [
        d
        for d in ds
        if (p := hps.daughter_patch(d)) is not None
        and (p.is_open_charm or p.is_hidden_quarkonium)
    ]

    if parent.is_open_charm_strange_meson:
        return _ds_weak_topology(parent_id, ds)

    if parent.is_light_kaon or (
        parent.is_light_strange_baryon and not parent.is_decuplet_baryon
    ):
        return _light_weak_hadronic_topology_ok(parent_id, ds)

    if parent.is_open_charm_baryon_ground and parent.ledger.q3 == 3:
        return _lambda_c_weak_topology(parent_id, ds)

    if parent.is_open_charm_baryon_cascade:
        return _xi_cascade_topology(parent_id, ds)

    if n < 2 or n > 3:
        return False

    if parent.is_open_charm_meson_nonstrange:
        if heavy or any(
            (p := hps.daughter_patch(d)) is not None
            and (p.is_light_vector_meson or hps.is_eta_patch(p))
            for d in ds
        ):
            return False
        if not _single_w_charge_load_ok(parent_id, ds):
            return False
        if not _kaon_outlet_sign_ok(parent_id, ds):
            return False
        kaons = _kaon_daughters(ds)
        if kaons:
            return _open_charm_kaon_mode_ok(parent_id, ds)
        return _open_charm_light_pseudoscalar_ok(parent_id, ds)

    if parent.is_open_bottom_meson_nonstrange:
        if len(heavy) != 1:
            return False
        if not _bottom_heavy_daughter_ok(parent_id, heavy[0]):
            return False
        lights = [d for d in ds if d not in heavy]
        if not lights or not all(hps.daughter_in_pool(d, "weak_light_with_vector") for d in lights):
            return False
        if not _single_w_charge_load_ok(parent_id, ds):
            return False
        heavy_patch = hps.daughter_patch(heavy[0])
        if heavy_patch is not None and heavy_patch.hidden_content == "charm":
            return n == 2 and all(
                (p := hps.daughter_patch(d)) is not None
                and (hps.is_kaon_discharge_patch(p) or hps.is_pion_discharge_patch(p))
                for d in lights
            )
        if n == 2:
            if parent.ledger.q3 == 0:
                return _single_w_charge_load_ok(parent_id, ds)
            return _bottom_two_body_ok(parent_id, heavy[0], lights[0])
        if n == 3:
            return _bottom_three_body_ok(parent_id, heavy[0], tuple(lights))
        return False

    if parent.is_open_bottom_meson_strange:
        return _bs_weak_topology(parent_id, ds)

    if parent.is_open_charm_baryon_ground and parent.ledger.q3 != 3:
        return (
            n == 3
            and hps.daughters_include_property(ds, hps.is_nucleon_patch, count=1)
            and _has_charged_kaon(ds)
            and _has_pion_discharge(ds)
            and not heavy
        )

    if parent.is_open_bottom_baryon:
        return len(heavy) <= 1

    return True


def _weak_channel_allowed(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    import hqiv_property_spanning as ps

    return ps.weak_channel_allowed(parent_id, daughter_ids)


def _strong_curvature_allowed(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Strong ledger: conserve visible charge and baryon number on the patch."""
    parent = species_ledger(parent_id)
    ledgers = _daughter_ledgers(daughter_ids)
    if parent is None or not ledgers:
        return False
    total = _ledger_sum(ledgers)
    return total.q3 == parent.q3 and total.a3 == parent.a3


def _weak_daughter_pool(parent_id: str) -> tuple[str, ...]:
    import hqiv_hep_patch_species as hps

    parent = _parent_patch(parent_id)
    if parent is None:
        return ()
    return hps.weak_daughter_pool_for(parent)


def _strong_daughter_pool(parent_id: str) -> tuple[str, ...]:
    import hqiv_hep_patch_species as hps

    parent = _parent_patch(parent_id)
    if parent is None:
        return ()
    return hps.strong_daughter_pool_for(parent)


def _enumerate_body_combos(
    pool: Sequence[str],
    *,
    n_bodies: int,
    max_count: int = 256,
) -> list[tuple[str, ...]]:
    combos: list[tuple[str, ...]] = []
    for combo in itertools.combinations_with_replacement(pool, n_bodies):
        combos.append(combo)
        if len(combos) >= max_count:
            break
    return combos


def _ds_strong_allowed(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Strong Ds: patch charge closure, or OZI φ discharge (1-body)."""
    import hqiv_hep_patch_species as hps

    parent = _parent_patch(parent_id)
    if parent is None or not parent.is_open_charm_strange_meson:
        return False
    if _strong_curvature_allowed(parent_id, daughter_ids):
        return True
    ds = tuple(daughter_ids)
    if len(ds) == 1:
        p = hps.daughter_patch(ds[0])
        return p is not None and hps.is_hidden_strangeness_patch(p)
    return False



def _ds_strong_sparse(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Strong Ds: φ pole or light hadron pair (no fitted channel table)."""
    import hqiv_hep_patch_species as hps

    parent = _parent_patch(parent_id)
    if parent is None or not parent.is_open_charm_strange_meson:
        return False
    ds = tuple(daughter_ids)
    if len(ds) == 1:
        p = hps.daughter_patch(ds[0])
        return p is not None and hps.is_hidden_strangeness_patch(p)
    if len(ds) == 2:
        return hps.daughters_all_in_pool(ds, "light_hadronic_2body")
    return False


def _generate_certified_channel_modes(
    parent_id: str,
    certified: tuple[tuple[str, ...], ...],
    *,
    channel: ChannelTag,
    parent_mass_mev: float,
    mass_of: MassLookup,
    source: str,
    allowed: Callable[[str, Sequence[str]], bool],
) -> list[GeneratedMode]:
    """Enumerate only Lean finite spanning modes (no pool combinatorics)."""
    out: list[GeneratedMode] = []
    seen: set[str] = set()
    for daughters in certified:
        if not allowed(parent_id, daughters):
            continue
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


def _generate_certified_weak_modes(
    parent_id: str,
    certified: tuple[tuple[str, ...], ...],
    *,
    parent_mass_mev: float,
    mass_of: MassLookup,
    source: str,
    allowed: Callable[[str, Sequence[str]], bool],
) -> list[GeneratedMode]:
    return _generate_certified_channel_modes(
        parent_id,
        certified,
        channel="weak",
        parent_mass_mev=parent_mass_mev,
        mass_of=mass_of,
        source=source,
        allowed=allowed,
    )


def _generate_dynamic_modes(
    parent_id: str,
    *,
    channel: ChannelTag,
    parent_mass_mev: float,
    mass_of: MassLookup,
    source: str,
    n_body_min: int = 2,
    n_body_max: int = 3,
    allowed: Callable[[str, Sequence[str]], bool],
) -> list[GeneratedMode]:
    pool = _weak_daughter_pool(parent_id) if channel == "weak" else _strong_daughter_pool(parent_id)
    if not pool:
        return []
    out: list[GeneratedMode] = []
    seen: set[str] = set()
    for n in range(n_body_min, n_body_max + 1):
        for combo in _enumerate_body_combos(pool, n_bodies=n):
            if not allowed(parent_id, combo):
                continue
            _add_mode(
                out,
                seen,
                parent_id=parent_id,
                channel=channel,
                daughters=combo,
                base_prior=open_flavour_topology_weight(parent_id, channel, combo),
                parent_mass_mev=parent_mass_mev,
                mass_of=mass_of,
                source=source,
            )
    return out


def ozi_suppression_factor(parent_id: str, daughter_ids: Sequence[str]) -> float:
    """
    OZI / Zweig suppression for hidden quarkonia → light hadrons only.

    Lean ``oziSuppressionFactor`` applies when the final state includes light
    hadrons; all-heavy cascades (e.g. ``Υ → J/ψ``) carry no OZI factor (unity).
    """
    import hqiv_hep_patch_species as hps

    parent = _parent_patch(parent_id)
    if parent is None or not parent.is_hidden_quarkonium:
        return 1.0
    daughter_patches = [hps.patch_from_species_id(d) for d in daughter_ids]
    if all(p is not None and p.is_hidden_quarkonium for p in daughter_patches):
        return 1.0
    n_vector = sum(
        1
        for p in daughter_patches
        if p is not None
        and (p.is_light_vector_meson or p.sector == "meson_hidden_strangeness")
    )
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
    # Contact seed only; phase space + CKM apply once in channel_topology_weight.
    if base_prior <= 0.0:
        return
    prior = base_prior
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
    """Unified spine discharge product (``SpineDischargeWeight.lean``)."""
    from hqiv_spine_discharge_weight import spine_discharge_weight

    return spine_discharge_weight(parent_id, channel, daughters)


def _has_charged_kaon(daughters: Sequence[str]) -> bool:
    import hqiv_hep_patch_species as hps

    return hps._daughter_predicate_ok(daughters, hps.is_charged_kaon_patch)


def _has_neutral_kaon(daughters: Sequence[str]) -> bool:
    import hqiv_hep_patch_species as hps

    return hps._daughter_predicate_ok(daughters, hps.is_neutral_kaon_patch)


def _has_open_charm(daughters: Sequence[str]) -> bool:
    return bool(_open_charm_daughters(daughters))


def open_flavour_contact_kind(
    parent_id: str,
    channel: ChannelTag,
    daughters: Sequence[str],
) -> hdr.OpenFlavourContactKind:
    """Ledger-derived contact selector (``hqiv_hep_decay_ledger_contact``)."""
    from hqiv_hep_decay_ledger_contact import derive_open_flavour_contact_kind

    return derive_open_flavour_contact_kind(parent_id, channel, daughters)


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
    import hqiv_hep_patch_species as hps

    out: list[GeneratedMode] = []
    seen: set[str] = set()
    hadronic_2body = hps.pool_nominal_ids("light_hadronic_2body")
    hadronic_3body = hps.pool_nominal_ids("light_hadronic_3body")

    for combo in _two_body_combos(hadronic_2body):
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

    for combo in _three_body_combos(hadronic_3body):
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

    parent_patch = _parent_patch(parent_id)
    if parent_patch is not None and parent_patch.hidden_content == "bottom":
        for light in hps.pool_nominal_ids("quarkonium_cascade"):
            if light == "Jpsi":
                base = hdr.hidden_bottom_jpsi_pole_contact()
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
            for meson in hps.pool_nominal_ids("light_pseudoscalar"):
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
        for pair in hps.neutral_light_pair_cascade_pairs():
            daughters = ("Jpsi",) + pair
            if not strong_neutral_light_cascade(daughters):
                continue
            _add_mode(
                out,
                seen,
                parent_id=parent_id,
                channel="strong",
                daughters=daughters,
                base_prior=hdr.hidden_bottom_jpsi_neutral_cascade_contact(),
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


def _generate_light_hadron_modes(
    parent_id: str,
    *,
    parent_mass_mev: float,
    mass_of: MassLookup,
) -> list[GeneratedMode]:
    """Ledger-driven light-hadron channel enumeration (no static mode table)."""
    parent = _parent_patch(parent_id)
    modes: list[GeneratedMode] = []
    strong_parents = parent is not None and (
        parent.is_light_vector_meson
        or parent.sector == "meson_hidden_strangeness"
        or parent.is_decuplet_baryon
        or parent.is_hyperon_strong_discharge_parent
    )
    if parent is not None:
        certified_strong = cert.certified_strong_tuples(parent)
        if certified_strong is not None:
            modes.extend(
                _generate_certified_channel_modes(
                    parent_id,
                    certified_strong,
                    channel="strong",
                    parent_mass_mev=parent_mass_mev,
                    mass_of=mass_of,
                    source="lean_certified_strong_span",
                    allowed=_light_strong_channel_allowed,
                )
            )
        elif strong_parents:
            n_max = 3 if parent.is_isoscalar_vector else 2
            modes.extend(
                _generate_dynamic_modes(
                    parent_id,
                    channel="strong",
                    parent_mass_mev=parent_mass_mev,
                    mass_of=mass_of,
                    source="light_hadron_strong_dynamic",
                    n_body_min=2,
                    n_body_max=n_max,
                    allowed=_light_strong_channel_allowed,
                )
            )

    if parent is not None and (parent.is_light_strange_baryon or parent.is_light_kaon):
        certified = cert.certified_weak_tuples(parent)
        if certified is not None:
            modes.extend(
                _generate_certified_weak_modes(
                    parent_id,
                    certified,
                    parent_mass_mev=parent_mass_mev,
                    mass_of=mass_of,
                    source="lean_light_weak_certificate",
                    allowed=_light_weak_channel_allowed,
                )
            )
        else:
            modes.extend(
                _generate_dynamic_modes(
                    parent_id,
                    channel="weak",
                    parent_mass_mev=parent_mass_mev,
                    mass_of=mass_of,
                    source="light_hadron_weak_dynamic",
                    n_body_min=1 if parent.is_light_kaon else 2,
                    n_body_max=3,
                    allowed=_light_weak_channel_allowed,
                )
            )

    seen = {m.key for m in modes}
    for daughters in _light_leptonic_weak_modes(parent_id):
        _add_mode(
            modes,
            seen,
            parent_id=parent_id,
            channel="weak",
            daughters=daughters,
            base_prior=_mode_topology_seed_leptonic(parent_id, daughters),
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
            source="light_hadron_leptonic_weak",
        )
    return modes


def _mode_topology_seed_leptonic(parent_id: str, daughters: tuple[str, ...]) -> float:
    """Topology seed for semileptonic / radiative weak outlets."""
    if daughters and all(d in ("mu_plus", "mu_minus", "e_plus", "e_minus") for d in daughters):
        return open_flavour_topology_weight(parent_id, "weak", daughters)
    if daughters == ("gamma",):
        return hdr.open_flavour_topology_seed_weight()
    return open_flavour_topology_weight(parent_id, "weak", daughters)


def _is_light_multichannel_parent(parent) -> bool:
    """Light-hadron parents enumerated by sector (not open charm/bottom)."""
    return parent.is_light_multichannel_parent


def generate_multichannel_modes(
    parent_id: str,
    *,
    parent_mass_mev: float,
    mass_of: MassLookup,
) -> list[GeneratedMode]:
    """All kinematically open generated modes for a parent patch (via comparison alias)."""
    sid = parent_id
    parent = _parent_patch(sid)
    if parent is None or not parent.is_decay_capable:
        return []

    if parent.is_hidden_quarkonium:
        return _generate_quarkonium_modes(sid, parent_mass_mev=parent_mass_mev, mass_of=mass_of)

    if _is_light_multichannel_parent(parent):
        return _generate_light_hadron_modes(
            sid,
            parent_mass_mev=parent_mass_mev,
            mass_of=mass_of,
        )

    modes: list[GeneratedMode] = []

    if parent.is_open_charm_strange_meson:
        modes.extend(
            _generate_dynamic_modes(
                sid,
                channel="strong",
                parent_mass_mev=parent_mass_mev,
                mass_of=mass_of,
                source="open_charm_strange_strong_dynamic",
                n_body_min=1,
                n_body_max=2,
                allowed=lambda p, d: _ds_strong_allowed(p, d) and _ds_strong_sparse(p, d),
            )
        )

    if parent.is_open_charm or parent.is_open_bottom:
        certified = cert.certified_weak_tuples(parent)
        if certified is not None:
            modes.extend(
                _generate_certified_weak_modes(
                    sid,
                    certified,
                    parent_mass_mev=parent_mass_mev,
                    mass_of=mass_of,
                    source="lean_heavy_weak_certificate",
                    allowed=_weak_channel_allowed,
                )
            )
        else:
            modes.extend(
                _generate_dynamic_modes(
                    sid,
                    channel="weak",
                    parent_mass_mev=parent_mass_mev,
                    mass_of=mass_of,
                    source="weak_hadronic_dynamic",
                    n_body_min=2,
                    n_body_max=3,
                    allowed=_weak_channel_allowed,
                )
            )

    return modes


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
