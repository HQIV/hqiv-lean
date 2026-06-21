#!/usr/bin/env python3
"""
Property-generated finite spanning sets for certified HEP decay parents.

Replaces static nominal tuple tables: enumerate daughter pools filtered by
ledger closure + sparse topology predicates derived from ``HadronPatch`` classes.

Lean mirror: ``lambdaWeakModes``, ``weakTopologySparse``, etc. in
``HepDecayChannelRouting.lean``.
"""

from __future__ import annotations

import itertools
from typing import Any, Literal, Sequence

import hqiv_hep_patch_species as hps
import hqiv_property_channels as pc

ChannelTag = Literal["weak", "strong"]


def _ledger():
    import hqiv_hep_decay_ledger_contact as ledger

    return ledger


def _mc():
    import hqiv_hep_multichannel_expansion as mc

    return mc


def parent_has_finite_weak_span(parent: hps.HadronPatch) -> bool:
    return (
        parent.is_lambda_octet
        or parent.is_light_kaon
        or (parent.is_open_charm_baryon_ground and parent.ledger.q3 == 3)
        or parent.is_open_bottom_meson_strange
        or parent.is_open_charm_strange_meson
        or parent.is_open_charm_baryon_cascade
        or parent.is_open_charm_meson_nonstrange
        or parent.is_open_bottom_meson_nonstrange
    )


def parent_has_finite_strong_span(parent: hps.HadronPatch) -> bool:
    return (
        parent.is_decuplet_baryon
        or parent.is_light_vector_meson
        or parent.sector == "meson_hidden_strangeness"
        or parent.is_hyperon_strong_discharge_parent
    )


def parent_has_quarkonium_cascade_span(parent: hps.HadronPatch) -> bool:
    return parent.is_hidden_quarkonium and parent.hidden_content == "bottom"


def _parent_id(parent: hps.HadronPatch) -> str:
    if not parent.nominal_id:
        raise ValueError(f"spanning enumeration requires nominal_id on {parent!r}")
    return parent.nominal_id


def _weak_body_bounds(parent: hps.HadronPatch) -> tuple[int, int]:
    if parent.is_light_kaon:
        return (1, 3)
    if parent.is_lambda_octet:
        return (2, 2)
    if parent.is_open_charm_baryon_ground and parent.ledger.q3 == 3:
        return (1, 4)
    if parent.is_open_charm_strange_meson:
        return (1, 3)
    if parent.is_open_charm_baryon_cascade:
        return (2, 2)
    if parent.is_open_bottom_meson_strange:
        return (2, 2)
    if parent.is_open_charm_meson_nonstrange:
        return (1, 3)
    if parent.is_open_bottom_meson_nonstrange:
        return (2, 3)
    return (2, 3)


def _strong_body_bounds(parent: hps.HadronPatch) -> tuple[int, int]:
    if parent.is_isoscalar_vector or parent.sector == "meson_hidden_strangeness":
        return (2, 3)
    return (2, 2)


def _kaon_weak_hadronic_topology(parent: hps.HadronPatch, ds: tuple[str, ...]) -> bool:
    mc = _mc()
    if not mc._single_w_charge_load_ok(_parent_id(parent), ds):
        return False
    n = len(ds)
    if parent.ledger.q3 == 0:
        return n == 1 and hps.daughters_include_property(
            ds, lambda p: hps.is_pion_discharge_patch(p) and p.isospin == "neutral_isovector", count=1
        )
    if n == 1:
        return hps.all_daughters_match(ds, hps.is_pion_discharge_patch)
    if n == 3:
        charged = pc.representative_charged_pion_tag(parent.ledger.q3)
        if charged is None:
            return False
        return (
            charged in ds
            and hps.daughters_include_property(
                ds,
                lambda p: hps.is_pion_discharge_patch(p) and p.isospin == "neutral_isovector",
                count=2,
            )
            and hps.all_daughters_match(ds, hps.is_pion_discharge_patch)
        )
    return False


def _lambda_weak_hadronic_topology(parent: hps.HadronPatch, ds: tuple[str, ...]) -> bool:
    mc = _mc()
    pid = _parent_id(parent)
    if not mc._single_w_charge_load_ok(pid, ds) or len(ds) != 2:
        return False
    if not hps.daughters_include_property(ds, hps.is_nucleon_patch, count=1):
        return False
    if not hps.daughters_include_property(ds, hps.is_pion_discharge_patch, count=1):
        return False
    if parent.is_lambda_octet:
        edge = pc.classify_weak_edge(pid, ds)
        if edge is None:
            return False
        if edge.outlet == "isospin_half_neutral_pion_baryon":
            return hps.daughters_include_property(
                ds, lambda p: p.sector == "baryon_nucleon" and p.ledger.q3 == 0, count=1
            ) and hps.daughters_include_property(ds, hps.is_pi_zero_patch, count=1)
        if edge.outlet == "isospin_half_charged_hadronic":
            return hps.daughters_include_property(
                ds, lambda p: p.sector == "baryon_nucleon" and p.ledger.q3 == 3, count=1
            ) and hps.daughters_include_property(
                ds,
                lambda p: hps.is_pion_discharge_patch(p) and p.ledger.q3 < 0,
                count=1,
            )
        return False
    edge = pc.classify_weak_edge(pid, ds)
    return edge is not None and edge.outlet in (
        "isospin_half_charged_hadronic",
        "isospin_half_neutral_pion_baryon",
    )


def _lambda_c_weak_topology(parent: hps.HadronPatch, ds: tuple[str, ...]) -> bool:
    mc = _mc()
    pid = _parent_id(parent)
    n = len(ds)
    if any(
        (p := hps.daughter_patch(d)) is not None and p.is_open_charm for d in ds
    ):
        return False
    if n == 2:
        return pc.charmed_baryon_two_body_discharge(parent, ds)
    if n == 3:
        if not hps.daughters_include_property(
            ds, lambda p: p.nominal_id == "p", count=1
        ):
            return False
        if not hps.daughters_include_property(ds, hps.is_charged_kaon_patch, count=1):
            return False
        if not hps.daughters_include_property(ds, hps.is_pion_discharge_patch, count=1):
            return False
        kaon_id = next(
            d
            for d in ds
            if (p := hps.daughter_patch(d)) is not None and hps.is_charged_kaon_patch(p)
        )
        pion_id = next(
            d
            for d in ds
            if (p := hps.daughter_patch(d)) is not None and hps.is_pion_discharge_patch(p)
        )
        if kaon_id == "K_minus":
            return pion_id in ("pi_plus", "pi_zero")
        if kaon_id == "K_plus":
            return pion_id == "pi_minus"
        return False
    if n == 4:
        if not hps.daughters_include_property(ds, hps.is_pi_zero_patch, count=1):
            return False
        rest = tuple(
            d
            for d in ds
            if (p := hps.daughter_patch(d)) is not None and not hps.is_pi_zero_patch(p)
        )
        return (
            len(rest) == 3
            and hps.daughters_include_property(rest, lambda p: p.nominal_id == "p", count=1)
            and hps.daughters_include_property(
                rest, lambda p: p.nominal_id == "K_minus", count=1
            )
            and hps.daughters_include_property(
                rest, lambda p: p.nominal_id == "pi_plus", count=1
            )
        )
    return False


def _ds_weak_topology(parent: hps.HadronPatch, ds: tuple[str, ...]) -> bool:
    """Mirror Lean ``dsWeakSparse``."""
    mc = _mc()
    pid = _parent_id(parent)
    n = len(ds)
    if any(
        (p := hps.daughter_patch(d)) is not None and p.is_open_charm for d in ds
    ):
        return False
    if n == 1:
        return ds == ("K_plus",)
    if n not in (2, 3) or not mc._single_w_charge_load_ok(pid, ds):
        return False
    try:
        key = hps.sorted_patch_keys(ds)
    except KeyError:
        return False
    if key == hps.sorted_patch_keys(("K_plus", "pi_zero")):
        return True
    if (
        n == 3
        and hps.daughters_include_property(ds, lambda p: p.nominal_id == "K_plus", count=1)
        and hps.daughters_include_property(ds, lambda p: p.nominal_id == "K_minus", count=1)
    ):
        charged = mc._parent_charged_pion_id(pid)
        return (
            charged is not None
            and charged in ds
            and all(
                (p := hps.daughter_patch(d)) is not None
                and (hps.is_kaon_discharge_patch(p) or hps.is_pion_discharge_patch(p))
                for d in ds
            )
        )
    kaons = [
        d for d in ds if (p := hps.daughter_patch(d)) and hps.is_kaon_discharge_patch(p)
    ]
    if kaons:
        if any(
            (p := hps.daughter_patch(d)) is not None and p.nominal_id == "K0_bar" for d in ds
        ):
            return False
        if not mc._kaon_outlet_sign_ok(pid, ds):
            return False
        if n == 2:
            charged = mc._parent_charged_pion_id(pid)
            if charged is None or charged not in ds:
                return False
            if hps.daughters_include_property(ds, lambda p: p.nominal_id == "K0", count=1):
                return not hps.daughters_include_property(ds, hps.is_pi_zero_patch)
            return (
                hps.daughters_include_property(ds, lambda p: p.nominal_id == "K_plus", count=1)
                and hps.daughters_include_property(ds, hps.is_pi_zero_patch, count=1)
                and len(ds) == 2
            )
        return False
    charged = mc._parent_charged_pion_id(pid)
    return (
        n == 2
        and charged is not None
        and charged in ds
        and hps.daughters_include_property(ds, lambda p: p.nominal_id == "eta", count=1)
    )


def _bs_weak_topology(parent: hps.HadronPatch, ds: tuple[str, ...]) -> bool:
    return pc.bottom_strange_two_body_discharge(parent, ds)


def _open_charm_meson_weak_topology(parent: hps.HadronPatch, ds: tuple[str, ...]) -> bool:
    mc = _mc()
    pid = _parent_id(parent)
    n = len(ds)
    if n < 2 or n > 3:
        return False
    kaons = mc._kaon_daughters(ds)
    if mc._open_charm_kaon_vector_mode_ok(pid, ds):
        return True
    if mc._open_charm_kaon_eta_mode_ok(pid, ds):
        return True
    if any(
        (p := hps.daughter_patch(d)) is not None and p.is_open_charm for d in ds
    ):
        return False
    if not mc._single_w_charge_load_ok(pid, ds):
        return False
    if not mc._kaon_outlet_sign_ok(pid, ds):
        return False
    if kaons:
        return mc._open_charm_kaon_mode_ok(pid, ds)
    return mc._open_charm_light_pseudoscalar_ok(pid, ds)


def _open_bottom_meson_weak_topology(parent: hps.HadronPatch, ds: tuple[str, ...]) -> bool:
    mc = _mc()
    pid = _parent_id(parent)
    n = len(ds)
    if n < 2 or n > 3:
        return False
    heavy = [
        d
        for d in ds
        if (p := hps.daughter_patch(d)) is not None
        and (p.is_open_charm or p.is_hidden_quarkonium)
    ]
    if len(heavy) != 1:
        return False
    if not mc._bottom_heavy_daughter_ok(pid, heavy[0]):
        return False
    lights = [d for d in ds if d not in heavy]
    if not lights or not all(
        hps.daughter_in_pool(d, "weak_light_with_vector") for d in lights
    ):
        return False
    if not mc._single_w_charge_load_ok(pid, ds):
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
            return True
        return mc._bottom_two_body_ok(pid, heavy[0], lights[0])
    if n == 3:
        if not hps.all_daughters_match(tuple(lights), hps.is_pion_discharge_patch):
            return False
        return mc._bottom_three_body_ok(pid, heavy[0], tuple(lights))
    return False


def _xi_c_weak_topology(parent: hps.HadronPatch, ds: tuple[str, ...]) -> bool:
    if len(ds) != 2:
        return False
    if not hps.daughters_include_property(ds, hps.is_charmed_baryon_ground_patch, count=1):
        return False
    if not hps.daughters_include_property(ds, hps.is_pion_discharge_patch, count=1):
        return False
    ground = next(
        d for d in ds if (p := hps.daughter_patch(d)) and hps.is_charmed_baryon_ground_patch(p)
    )
    pion = next(d for d in ds if d != ground)
    gp = hps.daughter_patch(ground)
    pp = hps.daughter_patch(pion)
    if gp is None or pp is None:
        return False
    if gp.nominal_id not in ("lambda_c", "sigma_c"):
        return False
    return hps.is_pion_discharge_patch(pp)


def weak_sparse_topology_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    """Sparse weak topology from patch properties (no static tuple tables)."""
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    ds = tuple(daughter_ids)
    if parent.is_light_kaon:
        return _kaon_weak_hadronic_topology(parent, ds)
    if parent.is_lambda_octet:
        return _lambda_weak_hadronic_topology(parent, ds)
    if parent.is_light_strange_baryon and not parent.is_decuplet_baryon:
        return _lambda_weak_hadronic_topology(parent, ds)
    if parent.is_open_charm_baryon_ground and parent.ledger.q3 == 3:
        return _lambda_c_weak_topology(parent, ds)
    if parent.is_open_charm_strange_meson:
        return _ds_weak_topology(parent, ds)
    if parent.is_open_bottom_meson_strange:
        return _bs_weak_topology(parent, ds)
    if parent.is_open_charm_baryon_cascade:
        return _xi_c_weak_topology(parent, ds)
    if parent.is_open_charm_meson_nonstrange:
        return _open_charm_meson_weak_topology(parent, ds)
    if parent.is_open_bottom_meson_nonstrange:
        return _open_bottom_meson_weak_topology(parent, ds)
    return _mc()._weak_topology_sparse(parent_id, ds)


def weak_channel_allowed(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    mc = _mc()
    ds = tuple(daughter_ids)
    parent = hps.patch_from_species_id(parent_id)
    if parent is not None and pc._visible_lepton_outlet(ds) and mc._single_w_charge_load_ok(
        parent_id, ds
    ):
        if parent.is_open_charm_meson_nonstrange:
            return mc._weak_hadronic_allowed(parent_id, daughter_ids)
        if parent.is_open_charm_baryon_ground and parent.nominal_id == "lambda_c":
            parent_ledger = mc.species_ledger(parent_id)
            ledgers = mc._daughter_ledgers(ds)
            if parent_ledger is None or not ledgers:
                return False
            total = mc._ledger_sum(ledgers)
            delta = mc._ledger_delta(parent_ledger, total)
            return delta.charm == -1 and delta.bottom == 0
    return mc._weak_hadronic_allowed(parent_id, daughter_ids) and weak_sparse_topology_ok(
        parent_id, daughter_ids
    )


def _hidden_strangeness_strong_topology(parent: hps.HadronPatch, ds: tuple[str, ...]) -> bool:
    n = len(ds)
    if n == 2:
        return (
            hps.daughters_include_property(
                ds,
                lambda p: hps.is_charged_kaon_patch(p) and p.ledger.q3 > 0,
                count=1,
            )
            and hps.daughters_include_property(
                ds,
                lambda p: hps.is_charged_kaon_patch(p) and p.ledger.q3 < 0,
                count=1,
            )
        )
    if n == 3:
        return (
            hps.all_daughters_match(ds, hps.is_pion_discharge_patch)
            and hps.daughters_include_property(
                ds,
                lambda p: p.isospin == "charged" and p.ledger.q3 > 0,
                count=1,
            )
            and hps.daughters_include_property(
                ds,
                lambda p: p.isospin == "charged" and p.ledger.q3 < 0,
                count=1,
            )
            and hps.daughters_include_property(ds, hps.is_pi_zero_patch, count=1)
        )
    return False


def strong_channel_allowed(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    mc = _mc()
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    if not mc._strong_curvature_allowed(parent_id, daughter_ids):
        return False
    if parent.sector == "meson_hidden_strangeness":
        return _hidden_strangeness_strong_topology(parent, tuple(daughter_ids))
    return mc._light_strong_topology_ok(parent_id, daughter_ids)


def _span_dedup_key(combo: tuple[str, ...]) -> tuple[Any, ...]:
    """Dedup key for spanning enumeration; leptons keep nominal tags."""
    if len(combo) == 1:
        patch = hps.patch_from_species_id(combo[0])
        if patch is not None and patch.sector == "lepton":
            return ("lepton", combo[0])
    return hps.sorted_patch_keys(combo)


def _enumerate_span(
    parent: hps.HadronPatch,
    channel: ChannelTag,
    *,
    allowed,
    n_min: int,
    n_max: int,
) -> tuple[tuple[str, ...], ...]:
    pid = _parent_id(parent)
    pool = (
        hps.weak_daughter_pool_for(parent)
        if channel == "weak"
        else hps.strong_daughter_pool_for(parent)
    )
    if not pool:
        return ()
    seen: set[tuple[Any, ...]] = set()
    modes: list[tuple[str, ...]] = []
    for n in range(n_min, n_max + 1):
        for combo in itertools.combinations_with_replacement(pool, n):
            if not allowed(pid, combo):
                continue
            try:
                key = _span_dedup_key(combo)
            except KeyError:
                continue
            if key in seen:
                continue
            seen.add(key)
            modes.append(combo)
    return tuple(sorted(modes, key=lambda m: (len(m), _span_dedup_key(m))))


def enumerate_weak_span(parent: hps.HadronPatch) -> tuple[tuple[str, ...], ...]:
    if not parent_has_finite_weak_span(parent):
        return ()
    n_min, n_max = _weak_body_bounds(parent)
    return _enumerate_span(
        parent,
        "weak",
        allowed=weak_channel_allowed,
        n_min=n_min,
        n_max=n_max,
    )


def enumerate_strong_span(parent: hps.HadronPatch) -> tuple[tuple[str, ...], ...]:
    if not parent_has_finite_strong_span(parent):
        return ()
    n_min, n_max = _strong_body_bounds(parent)
    return _enumerate_span(
        parent,
        "strong",
        allowed=strong_channel_allowed,
        n_min=n_min,
        n_max=n_max,
    )


def enumerate_quarkonium_cascade_span(parent: hps.HadronPatch) -> tuple[tuple[str, ...], ...]:
    if not parent_has_quarkonium_cascade_span(parent):
        return ()
    mc = _mc()
    seen: set[tuple[Any, ...]] = set()
    modes: list[tuple[str, ...]] = []
    allowed_pairs = {
        hps.sorted_patch_keys(("pi_plus", "pi_minus")),
        hps.sorted_patch_keys(("pi_zero", "pi_zero")),
    }
    for pair in hps.neutral_light_pair_cascade_pairs():
        if hps.sorted_patch_keys(pair) not in allowed_pairs:
            continue
        if frozenset(pair) == frozenset({"pi_plus", "pi_minus"}):
            pair_ordered = ("pi_plus", "pi_minus")
        else:
            pair_ordered = pair
        combo = ("Jpsi",) + pair_ordered
        if not mc.strong_neutral_light_cascade(combo):
            continue
        try:
            key = hps.sorted_patch_keys(combo)
        except KeyError:
            continue
        if key in seen:
            continue
        seen.add(key)
        modes.append(combo)
    return tuple(sorted(modes, key=hps.sorted_patch_keys))
