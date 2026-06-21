#!/usr/bin/env python3
"""
Property-channel routing for HEP decay edges.

Decay modes are classified by ``HadronPatch`` ledger / sector properties and daughter
outlet topology — not by nominal species whitelists.  Comparison catalog ids appear only
when resolving mass-readout representatives from daughter pools.

Lean mirror target: classify before ``openFlavourContactKind`` in
``HepDecayChannelRouting.lean``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Sequence

import hqiv_hep_decay_readout as hdr
import hqiv_hep_patch_species as hps

StrongOutletChannel = Literal[
    "hidden_strangeness_vector_leak",
    "hidden_strangeness_kk_retention",
    "hidden_strangeness_pole_discharge",
    "ozi_suppressed_open_charm_strange",
    "unit_strong",
]

WeakParentChannel = Literal[
    "isospin_half_weak",
    "strange_kaon_weak",
    "open_charm_meson",
    "open_charm_strange_meson",
    "open_charm_baryon_ground",
    "open_charm_cascade",
    "open_bottom_meson",
    "open_bottom_strange_meson",
    "unit_weak",
]

WeakOutletChannel = Literal[
    "semileptonic_visible_lepton",
    "kaon_hadronic_monogamy_charged",
    "kaon_hadronic_monogamy_neutral",
    "isospin_half_charged_hadronic",
    "isospin_half_neutral_pion_baryon",
    "isospin_half_neutral_pion_meson",
    "charm_pion_only",
    "charm_kaon_vector",
    "charm_kaon_eta",
    "charm_kaon_cabibbo_exclusion",
    "charmed_baryon_pk_light",
    "cascade_lambda_ground",
    "cascade_neutral_spectator",
    "cascade_charged_exclusion",
    "bottom_external_weak",
    "bottom_neutral_spectator",
    "bottom_strange_open_charm",
    "bottom_strange_hidden_phi",
    "bottom_strange_ds_spectator",
    "finite_open_bottom_completion",
    "finite_ds_completion",
    "unit_outlet",
]


@dataclass(frozen=True)
class WeakPropertyEdge:
    parent: WeakParentChannel
    outlet: WeakOutletChannel


@dataclass(frozen=True)
class StrongPropertyEdge:
    outlet: StrongOutletChannel


def representative_charged_pion_tag(q3: int) -> str | None:
    """Charged π discharge tag for a parent q₃ sign (mass-readout representative)."""
    if q3 > 0:
        return "pi_plus"
    if q3 < 0:
        return "pi_minus"
    return None


def representative_visible_lepton_tag(parent_q3: int) -> str | None:
    """Visible lepton tag closing single-W load for a strange kaon parent."""
    if parent_q3 > 0:
        return "mu_plus"
    if parent_q3 < 0:
        return "mu_minus"
    return None


def isospin_half_charged_hadronic_reference(parent: hps.HadronPatch) -> tuple[str, ...] | None:
    """
    Certified ΔI=½ charged-outlet kinematic anchor (property-derived nominal tags).
    """
    if parent.is_light_kaon:
        pi = representative_charged_pion_tag(parent.ledger.q3)
        return (pi,) if pi is not None else None
    if parent.is_lambda_octet:
        return ("p", "pi_minus")
    return None


def certified_light_weak_kinematic_reference(parent: hps.HadronPatch) -> tuple[str, ...] | None:
    """Shared-pole kinematic ratio anchor for certified light-weak parents."""
    if parent.is_light_kaon:
        lep = representative_visible_lepton_tag(parent.ledger.q3)
        return (lep,) if lep else None
    if parent.is_lambda_octet:
        return ("p", "pi_minus")
    return None


def _import_mc():
    import hqiv_hep_multichannel_expansion as mc

    return mc


def _daughter_tuple(daughter_ids: Sequence[str]) -> tuple[str, ...]:
    return tuple(daughter_ids)


def _parent_patch(parent_id: str) -> hps.HadronPatch | None:
    return hps.patch_from_species_id(parent_id)


def _single_w_ok(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    return _import_mc()._single_w_charge_load_ok(parent_id, _daughter_tuple(daughter_ids))


def _has_charged_kaon(daughter_ids: Sequence[str]) -> bool:
    return hps.daughters_include_property(daughter_ids, hps.is_charged_kaon_patch)


def _has_neutral_kaon(daughter_ids: Sequence[str]) -> bool:
    return hps.daughters_include_property(daughter_ids, hps.is_neutral_kaon_patch)


def _has_open_charm_hadron(daughter_ids: Sequence[str]) -> bool:
    return hps.daughters_include_property(daughter_ids, hps.is_open_charm_daughter_patch)


def _has_neutral_light_discharge(daughter_ids: Sequence[str]) -> bool:
    return any(
        (p := hps.daughter_patch(d)) is not None
        and hps.is_light_hadron_meson_patch(p)
        and p.ledger.q3 == 0
        for d in daughter_ids
    )


def _has_charged_light_discharge(daughter_ids: Sequence[str]) -> bool:
    return any(
        (p := hps.daughter_patch(d)) is not None
        and hps.is_light_hadron_meson_patch(p)
        and p.ledger.q3 != 0
        for d in daughter_ids
    )


def _has_light_pseudoscalar_discharge(daughter_ids: Sequence[str]) -> bool:
    return hps.daughters_include_property(
        daughter_ids,
        lambda p: hps.is_light_hadron_meson_patch(p) and not hps.is_kaon_discharge_patch(p),
    )


def _neutral_isovector_pion_only_outlet(daughter_ids: Sequence[str]) -> bool:
    has_pi0 = False
    has_charged_pi = False
    for d in daughter_ids:
        p = hps.daughter_patch(d)
        if p is None or not hps.is_pion_discharge_patch(p):
            continue
        if p.isospin == "neutral_isovector":
            has_pi0 = True
        elif p.isospin == "charged":
            has_charged_pi = True
    return has_pi0 and not has_charged_pi


def _visible_lepton_outlet(daughter_ids: Sequence[str]) -> bool:
    if len(daughter_ids) != 1:
        return False
    p = hps.daughter_patch(daughter_ids[0])
    return p is not None and p.sector == "lepton"


def _isospin_half_charged_hadronic_outlet(
    parent: hps.HadronPatch, daughter_ids: Sequence[str]
) -> bool:
    if _visible_lepton_outlet(daughter_ids):
        return False
    if _neutral_isovector_pion_only_outlet(daughter_ids):
        return False
    has_pi = hps.daughters_include_property(daughter_ids, hps.is_pion_discharge_patch)
    has_baryon = hps.daughters_include_property(
        daughter_ids, hps.is_light_baryon_discharge_patch
    )
    return has_pi or has_baryon


def classify_weak_parent(parent: hps.HadronPatch) -> WeakParentChannel:
    if parent.is_light_kaon:
        return "strange_kaon_weak"
    if parent.is_lambda_octet or (
        parent.is_light_strange_baryon and not parent.is_decuplet_baryon
    ):
        return "isospin_half_weak"
    if parent.is_open_charm_baryon_cascade:
        return "open_charm_cascade"
    if parent.is_open_charm_baryon_ground:
        return "open_charm_baryon_ground"
    if parent.is_open_charm_strange_meson:
        return "open_charm_strange_meson"
    if parent.is_open_charm_meson_nonstrange:
        return "open_charm_meson"
    if parent.is_open_bottom_meson_strange:
        return "open_bottom_strange_meson"
    if parent.is_open_bottom_meson_nonstrange:
        return "open_bottom_meson"
    return "unit_weak"


def _charmed_baryon_pk_light_discharge(
    parent: hps.HadronPatch, daughter_ids: Sequence[str]
) -> bool:
    if not parent.is_open_charm_baryon_ground or parent.ledger.strangeness != 0:
        return False
    ds = _daughter_tuple(daughter_ids)
    if len(ds) != 3:
        return False
    if not hps.daughters_include_property(ds, hps.is_nucleon_patch):
        return False
    if not _has_charged_kaon(ds):
        return False
    return _has_light_pseudoscalar_discharge(ds)


def charmed_baryon_two_body_discharge(
    parent: hps.HadronPatch, daughter_ids: Sequence[str]
) -> bool:
    """Λc two-body weak: proton + π⁰ or neutron + K⁺ (visible charge closes)."""
    mc = _import_mc()
    if not parent.is_open_charm_baryon_ground or parent.ledger.q3 != 3:
        return False
    ds = _daughter_tuple(daughter_ids)
    if len(ds) != 2:
        return False
    if any(
        (p := hps.daughter_patch(d)) is not None and p.is_open_charm for d in ds
    ):
        return False
    pid = parent.nominal_id or ""
    if not mc._visible_charge_closes(pid, ds):
        return False
    if hps.daughters_include_property(ds, lambda p: p.nominal_id == "p", count=1):
        return hps.daughters_include_property(ds, hps.is_pi_zero_patch, count=1)
    if hps.daughters_include_property(ds, lambda p: p.nominal_id == "n", count=1):
        return hps.daughters_include_property(ds, lambda p: p.nominal_id == "K_plus", count=1)
    return False


def bottom_strange_two_body_discharge(
    parent: hps.HadronPatch, daughter_ids: Sequence[str]
) -> bool:
    """B_s weak: hidden-φ pair or D_s spectator + negative charged kaon."""
    mc = _import_mc()
    if not parent.is_open_bottom_meson_strange:
        return False
    ds = _daughter_tuple(daughter_ids)
    if len(ds) != 2:
        return False
    if hps.all_daughters_match(ds, hps.is_hidden_strangeness_patch):
        return True
    if not hps.daughters_include_property(
        ds, hps.is_open_charm_strange_daughter_patch, count=1
    ):
        return False
    pid = parent.nominal_id or ""
    if not mc._single_w_charge_load_ok(pid, ds):
        return False
    light_id = next(
        d
        for d in ds
        if (p := hps.daughter_patch(d)) is not None
        and not hps.is_open_charm_strange_daughter_patch(p)
    )
    lp = hps.daughter_patch(light_id)
    return lp is not None and hps.is_charged_kaon_patch(lp) and lp.ledger.q3 < 0


def _xi_cascade_lambda_ground(parent: hps.HadronPatch, daughter_ids: Sequence[str]) -> bool:
    ds = _daughter_tuple(daughter_ids)
    return parent.is_open_charm_baryon_cascade and ds == ("lambda_c", "pi_zero")


def _xi_cascade(parent: hps.HadronPatch, daughter_ids: Sequence[str]) -> bool:
    return parent.is_open_charm_baryon_cascade and len(daughter_ids) == 2 and hps.daughters_include_property(
        daughter_ids, hps.is_charmed_baryon_ground_patch
    )


def _bottom_external_weak(parent: hps.HadronPatch, daughter_ids: Sequence[str]) -> bool:
    """Lean ``isBottomExternalWeak``: B⁺/B⁰ charged Dπ outlets only."""
    ds = _daughter_tuple(daughter_ids)
    if parent.nominal_id not in ("B_plus", "B0"):
        return False
    return ds == ("D0", "pi_plus") or ds == ("D_plus", "pi_minus")


def _bottom_neutral_spectator(parent: hps.HadronPatch, daughter_ids: Sequence[str]) -> bool:
    """Lean ``isNeutralBottomSpectator``: B⁰ → D⁰π⁰ only."""
    ds = _daughter_tuple(daughter_ids)
    if parent.nominal_id != "B0" or len(ds) != 2:
        return False
    return ds == ("D0", "pi_zero") and _single_w_ok(parent.nominal_id or "", ds)


def _hidden_strangeness_phi_pair(parent: hps.HadronPatch, daughter_ids: Sequence[str]) -> bool:
    if not parent.is_open_bottom_meson_strange or len(daughter_ids) != 2:
        return False
    return hps.all_daughters_match(daughter_ids, hps.is_hidden_strangeness_patch)


def classify_weak_outlet(
    parent: hps.HadronPatch, daughter_ids: Sequence[str]
) -> WeakOutletChannel:
    ds = _daughter_tuple(daughter_ids)

    if parent.is_light_kaon and _visible_lepton_outlet(ds) and _single_w_ok(
        parent.nominal_id or "", ds
    ):
        return "semileptonic_visible_lepton"

    if parent.is_open_charm_meson_nonstrange and _visible_lepton_outlet(ds) and _single_w_ok(
        parent.nominal_id or "", ds
    ):
        return "semileptonic_visible_lepton"

    if (
        parent.is_open_charm_baryon_ground
        and parent.nominal_id == "lambda_c"
        and _visible_lepton_outlet(ds)
        and _single_w_ok(parent.nominal_id or "", ds)
    ):
        return "semileptonic_visible_lepton"

    if parent.is_light_kaon and _single_w_ok(parent.nominal_id or "", ds):
        if _neutral_isovector_pion_only_outlet(ds):
            return "kaon_hadronic_monogamy_neutral"
        if _isospin_half_charged_hadronic_outlet(parent, ds):
            return "kaon_hadronic_monogamy_charged"

    if parent.is_open_charm_meson_nonstrange:
        if not hps.daughters_include_property(ds, hps.is_kaon_discharge_patch) and len(ds) >= 2 and hps.all_daughters_match(
            ds, hps.is_light_hadron_meson_patch
        ):
            return "charm_pion_only"
        mc = _import_mc()
        if mc._open_charm_kaon_vector_mode_ok(parent.nominal_id or "", ds):
            return "charm_kaon_vector"
        if mc._open_charm_kaon_eta_mode_ok(parent.nominal_id or "", ds):
            return "charm_kaon_eta"
        if mc._open_charm_kaon_mode_ok(parent.nominal_id or "", ds):
            return "charm_kaon_cabibbo_exclusion"

    if parent.is_open_charm_strange_meson and len(ds) >= 2:
        return "finite_ds_completion"

    if _charmed_baryon_pk_light_discharge(parent, ds):
        return "charmed_baryon_pk_light"

    if _xi_cascade(parent, ds):
        if _xi_cascade_lambda_ground(parent, ds):
            return "cascade_lambda_ground"
        if _has_neutral_light_discharge(ds):
            return "cascade_neutral_spectator"
        if _has_charged_light_discharge(ds):
            return "cascade_charged_exclusion"

    if _bottom_external_weak(parent, ds):
        return "bottom_external_weak"

    if _bottom_neutral_spectator(parent, ds):
        return "bottom_neutral_spectator"

    if parent.is_open_bottom_meson_strange:
        if _has_open_charm_hadron(ds):
            return "bottom_strange_open_charm"
        if _hidden_strangeness_phi_pair(parent, ds):
            return "bottom_strange_hidden_phi"
        if bottom_strange_two_body_discharge(parent, ds):
            return "bottom_strange_ds_spectator"

    if parent.is_open_bottom_meson_nonstrange and _has_open_charm_hadron(ds):
        return "finite_open_bottom_completion"

    if parent.is_lambda_octet or parent.is_light_strange_baryon:
        if _neutral_isovector_pion_only_outlet(ds):
            return "isospin_half_neutral_pion_baryon"
        if _isospin_half_charged_hadronic_outlet(parent, ds):
            return "isospin_half_charged_hadronic"

    if _neutral_isovector_pion_only_outlet(ds):
        return "isospin_half_neutral_pion_meson"

    if _isospin_half_charged_hadronic_outlet(parent, ds):
        return "isospin_half_charged_hadronic"

    return "unit_outlet"


def classify_weak_edge(parent_id: str, daughter_ids: Sequence[str]) -> WeakPropertyEdge | None:
    parent = _parent_patch(parent_id)
    if parent is None:
        return None
    return WeakPropertyEdge(
        parent=classify_weak_parent(parent),
        outlet=classify_weak_outlet(parent, daughter_ids),
    )


def contact_kind_from_weak_edge(edge: WeakPropertyEdge) -> hdr.OpenFlavourContactKind:
    """Map a property channel to the finite open-flavour contact ledger."""
    outlet = edge.outlet
    if outlet == "semileptonic_visible_lepton":
        return "semileptonic_neutrino_channel_completion"
    if outlet == "kaon_hadronic_monogamy_charged":
        return "isospin_half_hadronic_monogamy_exclusion"
    if outlet == "kaon_hadronic_monogamy_neutral":
        return "isospin_half_neutral_hadronic_monogamy_exclusion"
    if outlet == "isospin_half_neutral_pion_baryon":
        return "light_baryon_neutral_isospin_outlet"
    if outlet == "isospin_half_neutral_pion_meson":
        return "isospin_half_neutral_outlet"
    if outlet == "isospin_half_charged_hadronic":
        return "isospin_half_weak"
    if outlet == "charm_pion_only":
        return "charm_pion_only"
    if outlet == "charm_kaon_vector":
        return "hidden_strangeness_vector_leak"
    if outlet == "charm_kaon_eta":
        return "hidden_strangeness_vector_leak"
    if outlet == "charm_kaon_cabibbo_exclusion":
        return "open_charm_hadronic_monogamy_exclusion"
    if outlet == "finite_ds_completion":
        return "finite_channel_completion"
    if outlet == "charmed_baryon_pk_light":
        return "charmed_baryon_double_monogamy"
    if outlet == "cascade_lambda_ground":
        return "cascade_lambda_ground"
    if outlet == "cascade_neutral_spectator":
        return "neutral_spectator_complement"
    if outlet == "cascade_charged_exclusion":
        return "double_monogamy_exclusion"
    if outlet == "bottom_external_weak":
        return "bottom_external_weak"
    if outlet == "bottom_neutral_spectator":
        return "bottom_neutral_spectator"
    if outlet == "bottom_strange_open_charm":
        # Certified B_s weak span: open-charm and hidden-φ outlets share the φ pole;
        # branching competes on bottom-strange double-monogamy coherence only.
        return "bottom_strange_double_monogamy"
    if outlet == "bottom_strange_hidden_phi":
        return "bottom_strange_double_monogamy"
    if outlet == "bottom_strange_ds_spectator":
        return "spectator_half_monogamy"
    if outlet == "finite_open_bottom_completion":
        return "finite_open_bottom_completion"
    return "unit_seed"


def contact_kind_from_charmed_baryon_pk(
    parent_id: str, daughter_ids: Sequence[str]
) -> hdr.OpenFlavourContactKind:
    """Kaon-outlet sign splits double-monogamy vs exclusion on the same property channel."""
    mc = _import_mc()
    if mc._kaon_outlet_sign_ok(parent_id, _daughter_tuple(daughter_ids)):
        return "charmed_baryon_double_monogamy"
    return "double_monogamy_exclusion"


def derive_weak_contact_kind(
    parent_id: str, daughter_ids: Sequence[str]
) -> hdr.OpenFlavourContactKind:
    edge = classify_weak_edge(parent_id, daughter_ids)
    if edge is None:
        return "unit_seed"
    if edge.outlet == "charmed_baryon_pk_light":
        if parent_id == "lambda_c":
            return "charmed_baryon_semileptonic_hadronic"
        return contact_kind_from_charmed_baryon_pk(parent_id, daughter_ids)
    if edge.outlet == "semileptonic_visible_lepton":
        if parent_id in ("K_plus", "K_minus"):
            return "light_kaon_semileptonic_neutrino_completion"
        if parent_id in ("D_plus", "D0", "lambda_c"):
            return "open_charm_semileptonic_neutrino_completion"
        return "lepton_neutrino_weak_outlet"
    if edge.outlet == "kaon_hadronic_monogamy_charged":
        if parent_id in ("K_plus", "K_minus"):
            return "isospin_half_hadronic_semileptonic_competition"
        return "isospin_half_hadronic_monogamy_exclusion"
    if edge.outlet == "kaon_hadronic_monogamy_neutral":
        if parent_id in ("K_plus", "K_minus"):
            return "isospin_half_neutral_hadronic_semileptonic_competition"
        return "isospin_half_neutral_hadronic_monogamy_exclusion"
    return contact_kind_from_weak_edge(edge)


def classify_strong_edge(parent_id: str, daughter_ids: Sequence[str]) -> StrongPropertyEdge:
    parent = _parent_patch(parent_id)
    ds = _daughter_tuple(daughter_ids)
    if parent is None:
        return StrongPropertyEdge(outlet="unit_strong")

    if parent.sector == "meson_hidden_strangeness":
        if len(ds) == 3 and hps.all_daughters_match(ds, hps.is_pion_discharge_patch):
            return StrongPropertyEdge(outlet="hidden_strangeness_vector_leak")
        if len(ds) == 2 and hps.all_daughters_match(ds, hps.is_kaon_discharge_patch):
            return StrongPropertyEdge(outlet="hidden_strangeness_kk_retention")

    if parent.is_open_charm_strange_meson:
        phi_pole = (
            len(ds) == 1
            and (p := hps.daughter_patch(ds[0])) is not None
            and hps.is_hidden_strangeness_patch(p)
        )
        if phi_pole:
            return StrongPropertyEdge(outlet="hidden_strangeness_pole_discharge")
        if not phi_pole and hps.all_daughters_match(ds, hps.is_light_hadron_meson_patch):
            return StrongPropertyEdge(outlet="ozi_suppressed_open_charm_strange")

    return StrongPropertyEdge(outlet="unit_strong")


def contact_kind_from_strong_edge(edge: StrongPropertyEdge) -> hdr.OpenFlavourContactKind:
    if edge.outlet == "hidden_strangeness_vector_leak":
        return "hidden_strangeness_vector_leak"
    if edge.outlet == "hidden_strangeness_kk_retention":
        return "hidden_strangeness_kk_retention"
    if edge.outlet == "hidden_strangeness_pole_discharge":
        return "hidden_strangeness_pole_discharge"
    if edge.outlet == "ozi_suppressed_open_charm_strange":
        return "ozi_suppressed_strong"
    return "unit_seed"


def derive_contact_kind(
    parent_id: str, channel: str, daughter_ids: Sequence[str]
) -> hdr.OpenFlavourContactKind:
    if channel == "strong":
        return contact_kind_from_strong_edge(classify_strong_edge(parent_id, daughter_ids))
    if channel == "weak":
        return derive_weak_contact_kind(parent_id, daughter_ids)
    return "unit_seed"


def spine_light_observables(
    parent_id: str, channel: str, daughter_ids: Sequence[str]
) -> dict[str, int]:
    """
    Ledger discharge observables from property channels (Lean ``dischargeObservables``).
    """
    parent = _parent_patch(parent_id)
    ds = _daughter_tuple(daughter_ids)
    zero = {
        "charged_isospin_outlet": 0,
        "neutral_isospin_outlet": 0,
        "visible_lepton_weak": 0,
        "light_pseudoscalar_tag": 0,
        "monogamy_competition": 0,
        "semileptonic_hadronic_competition": 0,
        "hidden_strangeness_kk": 0,
        "hidden_strangeness_leak": 0,
    }
    if channel != "weak" or parent is None:
        if channel == "strong" and parent is not None:
            edge = classify_strong_edge(parent_id, ds)
            if edge.outlet == "hidden_strangeness_kk_retention":
                zero["hidden_strangeness_kk"] = 1
            elif edge.outlet == "hidden_strangeness_vector_leak":
                zero["hidden_strangeness_leak"] = 1
        return zero

    edge = classify_weak_edge(parent_id, ds)
    if edge is None:
        return zero

    outlet = edge.outlet
    if outlet == "semileptonic_visible_lepton":
        if parent.is_light_kaon:
            zero["visible_lepton_weak"] = 1
        return zero

    if outlet in (
        "kaon_hadronic_monogamy_charged",
        "isospin_half_charged_hadronic",
    ):
        zero["charged_isospin_outlet"] = 1
    elif outlet in (
        "kaon_hadronic_monogamy_neutral",
        "isospin_half_neutral_pion_baryon",
        "isospin_half_neutral_pion_meson",
    ):
        zero["neutral_isospin_outlet"] = 1

    if outlet in ("kaon_hadronic_monogamy_charged", "kaon_hadronic_monogamy_neutral"):
        zero["monogamy_competition"] = 1
        if parent.is_light_kaon and parent.nominal_id in ("K_plus", "K_minus"):
            zero["semileptonic_hadronic_competition"] = 1
        if hps.daughters_include_property(
            ds,
            lambda p: hps.is_light_hadron_meson_patch(p) and not hps.is_kaon_discharge_patch(p),
        ):
            zero["light_pseudoscalar_tag"] = 1

    return zero
