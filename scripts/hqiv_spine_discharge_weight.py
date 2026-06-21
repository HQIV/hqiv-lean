#!/usr/bin/env python3
"""
Unified spine discharge weight: ledger observables → single multiplicative law.

``W = ∏_k g_k^{e_k(obs)}`` with inactive generators equal to 1.

Light and heavy open-flavour discharge share one finite generator registry; species-specific
``if parent = …`` routing is a diagnostic alias for which exponents fire.

Lean mirror (light sector + uniqueness): ``SpineDischargeWeight.lean``,
``SpineDischargeUniqueness.lean``.  Heavy slots are Python-led until ported to Lean.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from typing import Sequence

import hqiv_hep_decay_readout as hdr
import hqiv_property_channels as pc
from hqiv_hep_decay_ledger_contact import (
    OPEN_CHARM_MESONS,
    derive_open_flavour_contact_kind,
    has_charged_kaon,
    has_charged_light_discharge,
    has_hidden_strangeness_vector,
    has_neutral_kaon,
    has_neutral_light_discharge,
    has_open_charm_hadron,
    has_light_vector_meson,
    is_bottom_external_weak_emission,
    is_charmed_baryon_p_k_light_discharge,
    is_light_hadron_discharge,
    is_neutral_bottom_spectator,
    is_ozi_suppressed_open_charm_strange_strong,
    is_xi_cascade,
    _is_light_semileptonic_weak_outlet,
)

_VISIBLE_LEPTONS = frozenset({"mu_plus", "mu_minus", "e_plus", "e_minus"})
_LIGHT_KAONS = frozenset({"K_plus", "K_minus", "K0", "K0_bar"})
_CHIRAL_PSEUDOSCALAR_FACTOR = (4.0 / 9.0) ** 2


@dataclass(frozen=True)
class DischargeObservables:
    # --- light-sector slots ---
    charged_isospin_outlet: int = 0
    neutral_isospin_outlet: int = 0
    visible_lepton_weak: int = 0
    light_pseudoscalar_tag: int = 0
    monogamy_competition: int = 0
    semileptonic_hadronic_competition: int = 0
    hidden_strangeness_kk: int = 0
    hidden_strangeness_leak: int = 0
    # --- heavy-sector atomic slots (γ-spine ledger) ---
    open_charm_double_monogamy: int = 0
    neutral_spectator: int = 0
    bottom_external_weak: int = 0
    charm_pion_only: int = 0
    finite_channel_completion: int = 0
    charmed_baryon_three_body: int = 0
    spectator_half_monogamy: int = 0
    bottom_strange_double_monogamy: int = 0
    bottom_strange_open_charm: int = 0
    ozi_suppressed_strong: int = 0
    open_charm_vector_leak: int = 0
    lepton_neutrino_weak: int = 0

    def active_generator_labels(self) -> tuple[str, ...]:
        labels: list[str] = []
        for f in fields(self):
            if getattr(self, f.name):
                labels.append(f.name)
        return tuple(labels)


def _parent_admits_semileptonic_weak(parent_id: str) -> bool:
    return parent_id in _LIGHT_KAONS


def _is_visible_lepton(species_id: str) -> bool:
    return species_id in _VISIBLE_LEPTONS


def _count_light_pseudoscalar_daughters(daughter_ids: Sequence[str]) -> int:
    return sum(
        1
        for d in daughter_ids
        if is_light_hadron_discharge(d) and not d.startswith("K")
    )


def _has_light_baryon_daughter(daughter_ids: Sequence[str]) -> bool:
    return any(d in ("p", "n") for d in daughter_ids)


def _light_observables(
    parent_id: str, channel: str, ds: tuple[str, ...]
) -> tuple[int, int, int, int, int, int, int, int]:
    obs = pc.spine_light_observables(parent_id, channel, ds)
    return (
        obs["charged_isospin_outlet"],
        obs["neutral_isospin_outlet"],
        obs["visible_lepton_weak"],
        obs["light_pseudoscalar_tag"],
        obs["monogamy_competition"],
        obs["semileptonic_hadronic_competition"],
        obs["hidden_strangeness_kk"],
        obs["hidden_strangeness_leak"],
    )


def _heavy_observables(
    parent_id: str, channel: str, ds: tuple[str, ...], *, light_active: bool
) -> tuple[int, ...]:
    if light_active:
        return (0,) * 12

    (
        ocdm,
        ns,
        bew,
        cpo,
        fcc,
        cb3,
        shm,
        bsdm,
        bsoc,
        ozi,
        ocvl,
        lnw,
    ) = (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

    if channel == "strong":
        if is_ozi_suppressed_open_charm_strange_strong(parent_id, channel, ds):
            ozi = 1
        return (ocdm, ns, bew, cpo, fcc, cb3, shm, bsdm, bsoc, ozi, ocvl, lnw)

    if channel != "weak":
        return (ocdm, ns, bew, cpo, fcc, cb3, shm, bsdm, bsoc, ozi, ocvl, lnw)

    mc = __import__("hqiv_hep_multichannel_expansion", fromlist=["*"])

    if parent_id in OPEN_CHARM_MESONS - {"Ds_plus"}:
        if has_light_vector_meson(ds) or (
            "eta" in ds and any(d.startswith("K") for d in ds)
        ):
            ocvl = 1
        elif not any(d.startswith("K") for d in ds) and all(
            is_light_hadron_discharge(d) for d in ds
        ):
            cpo = 1
        elif any(d.startswith("K") for d in ds):
            ocdm = 1
    elif parent_id == "Ds_plus" and len(ds) >= 2:
        fcc = 1
    elif is_charmed_baryon_p_k_light_discharge(parent_id, ds):
        if mc._kaon_outlet_sign_ok(parent_id, ds):
            cb3 = 1
            ocdm = 1
        else:
            ocdm = 1
    elif is_xi_cascade(parent_id, ds):
        if has_neutral_light_discharge(ds):
            ns = 1
        elif has_charged_light_discharge(ds):
            ocdm = 1
    elif is_bottom_external_weak_emission(parent_id, ds):
        bew = 1
    elif is_neutral_bottom_spectator(parent_id, ds):
        ns = 1
    elif parent_id == "Bs":
        if len(ds) == 2 and (
            has_open_charm_hadron(ds) or has_hidden_strangeness_vector(ds)
        ):
            bsdm = 1
        elif "Ds_plus" in ds:
            shm = 1
    elif parent_id in ("B_plus", "B0") and has_open_charm_hadron(ds):
        fcc = 1
    elif _is_light_semileptonic_weak_outlet(parent_id, ds):
        if parent_id not in ("K_plus", "K_minus"):
            lnw = 1

    return (ocdm, ns, bew, cpo, fcc, cb3, shm, bsdm, bsoc, ozi, ocvl, lnw)


def discharge_observables(
    parent_id: str,
    channel: str,
    daughter_ids: Sequence[str],
) -> DischargeObservables:
    ds = tuple(daughter_ids)
    charged, neutral, visible, ps_tag, monogamy, semi_had, kk, leak = _light_observables(
        parent_id, channel, ds
    )
    light_active = any((charged, neutral, visible, monogamy, semi_had, kk, leak))
    heavy = _heavy_observables(parent_id, channel, ds, light_active=light_active)
    return DischargeObservables(
        charged_isospin_outlet=charged,
        neutral_isospin_outlet=neutral,
        visible_lepton_weak=visible,
        light_pseudoscalar_tag=ps_tag,
        monogamy_competition=monogamy,
        semileptonic_hadronic_competition=semi_had,
        hidden_strangeness_kk=kk,
        hidden_strangeness_leak=leak,
        open_charm_double_monogamy=heavy[0],
        neutral_spectator=heavy[1],
        bottom_external_weak=heavy[2],
        charm_pion_only=heavy[3],
        finite_channel_completion=heavy[4],
        charmed_baryon_three_body=heavy[5],
        spectator_half_monogamy=heavy[6],
        bottom_strange_double_monogamy=heavy[7],
        bottom_strange_open_charm=heavy[8],
        ozi_suppressed_strong=heavy[9],
        open_charm_vector_leak=heavy[10],
        lepton_neutrino_weak=heavy[11],
    )


def spine_generator_table() -> dict[str, float]:
    """Canonical γ-spine factors (Lean ``HepDecayReadout``)."""
    return {
        "charged_isospin_outlet": hdr.isospin_half_weak_contact(),
        "neutral_isospin_outlet": hdr.isospin_half_neutral_outlet_contact(),
        "monogamy_competition": hdr.double_monogamy_exclusion_factor(),
        "semileptonic_hadronic_competition": hdr.light_hadronic_semileptonic_competition_aperture(),
        "light_pseudoscalar_tag": _CHIRAL_PSEUDOSCALAR_FACTOR,
        "visible_lepton_weak": hdr.semileptonic_neutrino_channel_completion(),
        "hidden_strangeness_kk": hdr.hidden_strangeness_kk_retention_contact(),
        "hidden_strangeness_leak": hdr.hidden_strangeness_vector_leak_contact(),
        "open_charm_double_monogamy": hdr.double_monogamy_exclusion_factor(),
        "neutral_spectator": hdr.neutral_spectator_monogamy_complement(),
        "bottom_external_weak": hdr.bottom_external_weak_contact(),
        "charm_pion_only": hdr.charm_pion_only_suppression(),
        "finite_channel_completion": hdr.finite_channel_completion_aperture(),
        "charmed_baryon_three_body": hdr.charmed_baryon_three_body_contact(),
        "spectator_half_monogamy": hdr.spectator_half_monogamy_contact(),
        "bottom_strange_double_monogamy": hdr.bottom_strange_double_monogamy_coherence(),
        "bottom_strange_open_charm": hdr.bottom_strange_open_charm_contact(),
        "ozi_suppressed_strong": hdr.ozi_suppressed_strong_contact(),
        "open_charm_vector_leak": hdr.hidden_strangeness_vector_leak_contact(),
        "lepton_neutrino_weak": hdr.lepton_neutrino_pair_aperture(),
    }


def _neutral_isospin_generator(parent_id: str, obs: DischargeObservables) -> float:
    if obs.monogamy_competition:
        return hdr.isospin_half_neutral_outlet_contact()
    if obs.neutral_isospin_outlet:
        import hqiv_hep_patch_species as hps

        p = hps.patch_from_species_id(parent_id)
        if p is not None and p.is_light_strange_baryon and not p.is_decuplet_baryon:
            return hdr.light_baryon_neutral_isospin_outlet_contact()
    return hdr.isospin_half_neutral_outlet_contact()


def spine_discharge_product(obs: DischargeObservables, *, parent_id: str = "") -> float:
    gens = spine_generator_table()
    w = 1.0
    for name, base in gens.items():
        exp = getattr(obs, name)
        if exp:
            if name == "neutral_isospin_outlet":
                base = _neutral_isospin_generator(parent_id, obs)
            if name == "visible_lepton_weak" and parent_id in ("K_plus", "K_minus"):
                base = hdr.light_kaon_semileptonic_neutrino_completion()
            w *= base**exp
    return w


def _light_sector_active(obs: DischargeObservables) -> bool:
    return any(
        (
            obs.charged_isospin_outlet,
            obs.neutral_isospin_outlet,
            obs.visible_lepton_weak,
            obs.monogamy_competition,
            obs.semileptonic_hadronic_competition,
            obs.hidden_strangeness_kk,
            obs.hidden_strangeness_leak,
        )
    )


def spine_discharge_weight(
    parent_id: str,
    channel: str,
    daughter_ids: Sequence[str],
) -> float:
    obs = discharge_observables(parent_id, channel, daughter_ids)
    if _light_sector_active(obs):
        return spine_discharge_product(obs, parent_id=parent_id)
    return hdr.open_flavour_contact_weight(
        derive_open_flavour_contact_kind(parent_id, channel, daughter_ids)
    )


def routing_diagnostic_kind(
    parent_id: str,
    channel: str,
    daughter_ids: Sequence[str],
) -> hdr.OpenFlavourContactKind:
    """Legacy ``OpenFlavourContactKind`` label (which generators fired)."""
    return derive_open_flavour_contact_kind(parent_id, channel, daughter_ids)
