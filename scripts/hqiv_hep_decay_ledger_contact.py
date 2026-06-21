#!/usr/bin/env python3
"""Property-channel routing replaces nominal-species contact selection."""

from __future__ import annotations

from typing import Sequence

import hqiv_hep_decay_readout as hdr
import hqiv_hep_patch_species as hps
import hqiv_property_channels as pc

# Re-export pools used by multichannel expansion (property-indexed catalog).
OPEN_CHARM_MESONS = frozenset(
    sid
    for sid, patch in hps._catalog_patch_index().items()
    if patch.is_open_charm_meson_nonstrange or patch.is_open_charm_strange_meson
)
OPEN_BOTTOM_MESONS = frozenset(
    sid
    for sid, patch in hps._catalog_patch_index().items()
    if patch.is_open_bottom_meson_nonstrange or patch.is_open_bottom_meson_strange
)
CHARMED_BARYONS = frozenset(
    sid
    for sid, patch in hps._catalog_patch_index().items()
    if patch.sector == "open_charm_baryon"
)
CHARMED_BARYON_DAUGHTERS = frozenset(
    sid for sid, patch in hps._catalog_patch_index().items() if patch.is_open_charm_baryon_ground
)
LIGHT_BARYONS = frozenset(
    sid for sid, patch in hps._catalog_patch_index().items() if patch.sector == "baryon_nucleon"
)


def _import_mc():
    import hqiv_hep_multichannel_expansion as mc

    return mc


def visible_charge_q3(parent_id: str, daughter_ids: Sequence[str]) -> int | None:
    mc = _import_mc()
    parent = mc.species_ledger(parent_id)
    ledgers = mc._daughter_ledgers(daughter_ids)
    if parent is None or not ledgers:
        return None
    total_q3 = mc._ledger_sum(ledgers).q3
    return parent.q3 - total_q3


def visible_charge_closes(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    residual = visible_charge_q3(parent_id, daughter_ids)
    return residual is not None and residual == 0


def has_charged_kaon(daughter_ids: Sequence[str]) -> bool:
    return hps.daughters_include_property(daughter_ids, hps.is_charged_kaon_patch)


def has_neutral_kaon(daughter_ids: Sequence[str]) -> bool:
    return hps.daughters_include_property(daughter_ids, hps.is_neutral_kaon_patch)


def has_open_charm_hadron(daughter_ids: Sequence[str]) -> bool:
    return hps.daughters_include_property(daughter_ids, hps.is_open_charm_daughter_patch)


def has_light_vector_meson(daughter_ids: Sequence[str]) -> bool:
    return hps.daughters_include_property(
        daughter_ids, lambda p: p.is_light_vector_meson
    )


def has_hidden_strangeness_vector(daughter_ids: Sequence[str]) -> bool:
    return not has_open_charm_hadron(daughter_ids) and all(
        (p := hps.daughter_patch(d)) is not None
        and (
            hps.is_hidden_strangeness_patch(p)
            or hps.is_pion_discharge_patch(p)
            or p.is_light_vector_meson
        )
        for d in daughter_ids
    )


def is_light_hadron_discharge(species_id: str) -> bool:
    patch = hps.daughter_patch(species_id)
    return patch is not None and hps.is_light_hadron_meson_patch(patch)


def is_neutral_light_discharge(species_id: str) -> bool:
    patch = hps.daughter_patch(species_id)
    return (
        patch is not None
        and hps.is_light_hadron_meson_patch(patch)
        and patch.ledger.q3 == 0
    )


def is_charged_light_discharge(species_id: str) -> bool:
    patch = hps.daughter_patch(species_id)
    return (
        patch is not None
        and hps.is_light_hadron_meson_patch(patch)
        and patch.ledger.q3 != 0
    )


def has_neutral_light_discharge(daughter_ids: Sequence[str]) -> bool:
    return any(is_neutral_light_discharge(d) for d in daughter_ids)


def has_charged_light_discharge(daughter_ids: Sequence[str]) -> bool:
    return any(is_charged_light_discharge(d) for d in daughter_ids)


def has_light_pseudoscalar_discharge(daughter_ids: Sequence[str]) -> bool:
    return hps.daughters_include_property(
        daughter_ids,
        lambda p: hps.is_light_hadron_meson_patch(p) and not hps.is_kaon_discharge_patch(p),
    )


def is_charmed_baryon_p_k_light_discharge(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    return pc._charmed_baryon_pk_light_discharge(parent, daughter_ids)


def is_xi_cascade(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    return pc._xi_cascade(parent, daughter_ids)


def is_bottom_external_weak_emission(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    return pc._bottom_external_weak(parent, daughter_ids)


def is_neutral_bottom_spectator(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    return pc._bottom_neutral_spectator(parent, daughter_ids)


def is_hidden_strangeness_pole_discharge(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    parent = hps.patch_from_species_id(parent_id)
    return (
        parent is not None
        and parent.is_open_charm_strange_meson
        and tuple(daughter_ids) == ("phi",)
    )


def is_ozi_suppressed_open_charm_strange_strong(
    parent_id: str,
    channel: str,
    daughter_ids: Sequence[str],
) -> bool:
    if channel != "strong":
        return False
    edge = pc.classify_strong_edge(parent_id, daughter_ids)
    return edge.outlet == "ozi_suppressed_open_charm_strange"


def _is_neutral_isovector_pion_only_outlet(daughter_ids: Sequence[str]) -> bool:
    return pc._neutral_isovector_pion_only_outlet(daughter_ids)


def _is_light_semileptonic_weak_outlet(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    edge = pc.classify_weak_edge(parent_id, daughter_ids)
    return edge is not None and edge.outlet == "semileptonic_visible_lepton"


def _is_isospin_half_weak_parent(parent_id: str) -> bool:
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    return parent.is_lambda_octet or parent.is_light_kaon


def _is_light_strange_baryon_parent(parent_id: str) -> bool:
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    return parent.is_light_strange_baryon and not parent.is_decuplet_baryon


def derive_open_flavour_contact_kind(
    parent_id: str,
    channel: str,
    daughter_ids: Sequence[str],
) -> hdr.OpenFlavourContactKind:
    """Property-channel router → finite γ-spine contact ledger."""
    return pc.derive_contact_kind(parent_id, channel, daughter_ids)
