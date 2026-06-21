#!/usr/bin/env python3
"""
Property-first hadron slots for HEP decay (comparison names are optional aliases).

Physics flow (target architecture):

  1. **Patch** — ledger (q₃, S, C, B, a₃) + discharge sector + excitation on the TUFT ladder
  2. **Mass / width** — HQIV readout from patch properties (not PDG tables)
  3. **Decay enumeration** — open channels from ledger + sector rules
  4. **Nominal tag** — ``nominal_id`` attached only for benchmark / PDG comparison export

Catalog ``config_id`` strings (``delta_p``, ``Ds_plus``, …) are *comparison aliases*, not
generators.  Routing predicates should consult ``HadronPatch`` fields, not string whitelists.

Lean mirror target: finite patch ledger + sector class (``HepDecayReadout`` contact kinds).
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Any, Literal, Sequence

import hqiv_hep_multichannel_expansion as mc
import hqiv_mass_calculator_core as hmc

PatchSector = Literal[
    "gamma",
    "lepton",
    "baryon_nucleon",
    "baryon_octet",
    "baryon_decuplet",
    "meson_pseudoscalar",
    "meson_vector",
    "meson_hidden_strangeness",
    "open_charm_meson",
    "open_charm_strange_meson",
    "open_charm_baryon",
    "open_bottom_meson",
    "open_bottom_baryon",
    "hidden_quarkonium",
    "unknown",
]


IsospinDischarge = Literal["charged", "neutral_isovector", "isoscalar", "strange", "unknown"]

HiddenContent = Literal["none", "charm", "bottom"]

OctetMember = Literal["unknown", "lambda", "sigma", "xi"]

DaughterPoolTag = Literal[
    "light_pseudoscalar",
    "light_vector",
    "light_hidden_strangeness",
    "light_hadronic_2body",
    "light_hadronic_3body",
    "light_baryon_octet",
    "light_nucleon",
    "open_charm_meson",
    "open_charm_strange_meson",
    "charmed_baryon_ground",
    "hidden_quarkonium_charm",
    "hidden_quarkonium_bottom",
    "quarkonium_cascade",
    "weak_light_pseudoscalar",
    "weak_light_with_vector",
    "ds_weak_light",
    "lepton_charged",
    "gamma",
]

# Beam / catalog alias normalisation (keep in sync with ``hep.BEAM_SPECIES``).
_SPECIES_ALIASES: dict[str, str] = {
    "e+": "e_plus",
    "e-": "e_minus",
    "mu+": "mu_plus",
    "mu-": "mu_minus",
    # Comparison-layer shorthand for charmed cascade baryon (catalog: xi_c0 / xi_c_plus).
    "xi_c": "xi_c0",
}


def resolve_species_alias(species_id: str) -> str:
    return _SPECIES_ALIASES.get(species_id, species_id)


@dataclass(frozen=True)
class HadronPatch:
    """Decay-graph node defined by patch quantum numbers and discharge sector."""

    ledger: mc.HadronLedger
    sector: PatchSector
    excitation: int = 0
    isospin: IsospinDischarge = "unknown"
    hidden_content: HiddenContent = "none"
    octet_member: OctetMember = "unknown"
    nominal_id: str | None = None

    @property
    def is_stable(self) -> bool:
        return self.sector in ("gamma", "lepton", "baryon_nucleon")

    @property
    def is_meson(self) -> bool:
        return self.ledger.a3 == 0

    @property
    def is_baryon(self) -> bool:
        return self.ledger.a3 == 3

    @property
    def is_hidden_quarkonium(self) -> bool:
        return self.sector == "hidden_quarkonium"

    @property
    def is_open_charm(self) -> bool:
        return abs(self.ledger.charm) > 0 and abs(self.ledger.bottom) == 0

    @property
    def is_open_bottom(self) -> bool:
        return abs(self.ledger.bottom) > 0 and not self.is_hidden_quarkonium

    @property
    def is_open_charm_strange_meson(self) -> bool:
        return (
            self.is_meson
            and abs(self.ledger.charm) == 1
            and self.ledger.strangeness != 0
            and abs(self.ledger.bottom) == 0
        )

    @property
    def is_light_strange_baryon(self) -> bool:
        return (
            self.sector == "baryon_octet"
            and self.ledger.strangeness < 0
            and abs(self.ledger.charm) == 0
            and abs(self.ledger.bottom) == 0
        )

    @property
    def is_decuplet_baryon(self) -> bool:
        return self.sector == "baryon_decuplet"

    @property
    def is_light_vector_meson(self) -> bool:
        return self.sector == "meson_vector"

    @property
    def is_light_pseudoscalar_meson(self) -> bool:
        return self.sector == "meson_pseudoscalar"

    @property
    def is_light_pseudoscalar_decay_parent(self) -> bool:
        """Charged / neutral-isovector π slots — not isoscalar η."""
        return self.is_light_pseudoscalar_meson and self.isospin in (
            "charged",
            "neutral_isovector",
        )

    @property
    def is_isoscalar_vector(self) -> bool:
        return self.is_light_vector_meson and self.isospin == "isoscalar"

    @property
    def is_sigma_octet(self) -> bool:
        return self.octet_member == "sigma"

    @property
    def is_xi_octet(self) -> bool:
        return self.octet_member == "xi"

    @property
    def is_lambda_octet(self) -> bool:
        return self.octet_member == "lambda"

    @property
    def is_hyperon_strong_discharge_parent(self) -> bool:
        """Σ / Ξ strong two-body hadronic parents (not Λ)."""
        return self.octet_member in ("sigma", "xi") and not self.is_decuplet_baryon

    @property
    def is_open_charm_meson_nonstrange(self) -> bool:
        return self.sector == "open_charm_meson"

    @property
    def is_open_bottom_meson_nonstrange(self) -> bool:
        return self.sector == "open_bottom_meson" and self.ledger.strangeness == 0

    @property
    def is_open_bottom_meson_strange(self) -> bool:
        return self.sector == "open_bottom_meson" and self.ledger.strangeness != 0

    @property
    def is_open_charm_baryon_ground(self) -> bool:
        return self.sector == "open_charm_baryon" and self.ledger.strangeness == 0

    @property
    def is_open_charm_baryon_cascade(self) -> bool:
        return self.sector == "open_charm_baryon" and self.ledger.strangeness < 0

    @property
    def is_open_bottom_baryon(self) -> bool:
        return self.sector == "open_bottom_baryon"

    @property
    def is_light_kaon(self) -> bool:
        return (
            self.sector == "meson_pseudoscalar"
            and self.isospin == "strange"
            and self.ledger.charm == 0
            and self.ledger.bottom == 0
        )

    @property
    def is_light_multichannel_parent(self) -> bool:
        """Light-hadron parents enumerated by sector (not open charm/bottom)."""
        if self.is_open_charm or self.is_open_bottom:
            return False
        return (
            self.is_light_vector_meson
            or self.sector == "meson_hidden_strangeness"
            or self.is_decuplet_baryon
            or self.is_light_strange_baryon
            or self.is_light_kaon
            or self.is_light_pseudoscalar_decay_parent
            or (self.sector == "lepton" and self.nominal_id in ("mu_plus", "mu_minus"))
        )

    @property
    def is_decay_capable(self) -> bool:
        """Patch participates in programmatic multichannel decay expansion."""
        if self.sector in ("gamma", "baryon_nucleon"):
            return False
        if self.sector == "lepton":
            return self.nominal_id in ("mu_plus", "mu_minus")
        if self.is_hidden_quarkonium:
            return True
        if self.sector in (
            "open_charm_meson",
            "open_charm_strange_meson",
            "open_charm_baryon",
            "open_bottom_meson",
            "open_bottom_baryon",
        ):
            return True
        return self.is_light_multichannel_parent

    def patch_key(self) -> tuple[Any, ...]:
        """Hashable identity for dedup (properties only — no nominal_id)."""
        return (
            self.ledger.q3,
            self.ledger.strangeness,
            self.ledger.charm,
            self.ledger.bottom,
            self.ledger.a3,
            self.sector,
            self.excitation,
            self.isospin,
            self.hidden_content,
            self.octet_member,
        )


def _sector_from_catalog_row(row: dict[str, Any]) -> PatchSector:
    sid = row["config_id"]
    structure = row.get("structure", "")
    variety = row.get("variety_id", "")
    note = row.get("note", "")
    ledger = mc.species_ledger(sid)
    if ledger is None:
        return "unknown"
    if sid in ("Jpsi", "Upsilon"):
        return "hidden_quarkonium"
    if ledger.a3 == 0:
        if abs(ledger.charm) == 1 and ledger.strangeness != 0:
            return "open_charm_strange_meson"
        if abs(ledger.charm) == 1:
            return "open_charm_meson"
        if abs(ledger.bottom) == 1:
            return "open_bottom_meson"
        if sid == "phi" or "ss" in row.get("label", ""):
            return "meson_hidden_strangeness"
        if variety == "meson_light_vector" or "vector" in note or sid.startswith("rho_"):
            return "meson_vector"
        return "meson_pseudoscalar"
    if ledger.a3 == 3:
        if "decuplet" in note or variety == "baryon_decuplet":
            return "baryon_decuplet"
        if abs(ledger.charm) == 1:
            return "open_charm_baryon"
        if abs(ledger.bottom) == 1:
            return "open_bottom_baryon"
        if sid in ("p", "n"):
            return "baryon_nucleon"
        return "baryon_octet"
    if structure == "meson":
        return "meson_pseudoscalar"
    if structure == "baryon":
        return "baryon_octet"
    return "unknown"


def _excitation_from_catalog_row(row: dict[str, Any]) -> int:
    note = row.get("note", "")
    variety = row.get("variety_id", "")
    if "decuplet" in note or variety == "baryon_decuplet":
        return 1
    if row.get("config_id", "").startswith("delta_") or row.get("config_id", "").startswith(
        "sigma_star"
    ):
        return 1
    if row.get("structure") == "meson" and row.get("variety_id") == "meson_light_vector":
        return 1
    return 0


def _octet_member_from_sid(sid: str, sector: PatchSector) -> OctetMember:
    if sector != "baryon_octet":
        return "unknown"
    if sid == "lambda":
        return "lambda"
    if sid.startswith("sigma_") and "star" not in sid:
        return "sigma"
    if sid.startswith("xi_") and sid not in ("xi_b", "xi_c", "xi_cc_plus") and "star" not in sid:
        return "xi"
    return "unknown"


_MANUAL_PATCHES: dict[str, HadronPatch] = {
    "gamma": HadronPatch(mc.HadronLedger(0, 0, 0, 0, 0), "gamma", nominal_id="gamma"),
    "e_plus": HadronPatch(mc.HadronLedger(3, 0, 0, 0, 0), "lepton", nominal_id="e_plus"),
    "e_minus": HadronPatch(mc.HadronLedger(-3, 0, 0, 0, 0), "lepton", nominal_id="e_minus"),
    "mu_plus": HadronPatch(mc.HadronLedger(3, 0, 0, 0, 0), "lepton", nominal_id="mu_plus"),
    "mu_minus": HadronPatch(mc.HadronLedger(-3, 0, 0, 0, 0), "lepton", nominal_id="mu_minus"),
    "pi_plus": HadronPatch(
        mc.HadronLedger(3, 0, 0, 0, 0), "meson_pseudoscalar", isospin="charged", nominal_id="pi_plus"
    ),
    "pi_minus": HadronPatch(
        mc.HadronLedger(-3, 0, 0, 0, 0), "meson_pseudoscalar", isospin="charged", nominal_id="pi_minus"
    ),
    "pi_zero": HadronPatch(
        mc.HadronLedger(0, 0, 0, 0, 0), "meson_pseudoscalar", isospin="neutral_isovector", nominal_id="pi_zero"
    ),
    "eta": HadronPatch(
        mc.HadronLedger(0, 0, 0, 0, 0), "meson_pseudoscalar", isospin="isoscalar", nominal_id="eta"
    ),
    "K_plus": HadronPatch(
        mc.HadronLedger(3, 1, 0, 0, 0), "meson_pseudoscalar", isospin="strange", nominal_id="K_plus"
    ),
    "K_minus": HadronPatch(
        mc.HadronLedger(-3, -1, 0, 0, 0), "meson_pseudoscalar", isospin="strange", nominal_id="K_minus"
    ),
    "K0": HadronPatch(
        mc.HadronLedger(0, 1, 0, 0, 0), "meson_pseudoscalar", isospin="strange", nominal_id="K0"
    ),
    "K0_bar": HadronPatch(
        mc.HadronLedger(0, -1, 0, 0, 0), "meson_pseudoscalar", isospin="strange", nominal_id="K0_bar"
    ),
    "rho_plus": HadronPatch(
        mc.HadronLedger(3, 0, 0, 0, 0), "meson_vector", excitation=1, isospin="charged", nominal_id="rho_plus"
    ),
    "rho_zero": HadronPatch(
        mc.HadronLedger(0, 0, 0, 0, 0), "meson_vector", excitation=1, isospin="neutral_isovector", nominal_id="rho_zero"
    ),
    "omega_meson": HadronPatch(
        mc.HadronLedger(0, 0, 0, 0, 0), "meson_vector", excitation=1, isospin="isoscalar", nominal_id="omega_meson"
    ),
    "phi": HadronPatch(
        mc.HadronLedger(0, 0, 0, 0, 0), "meson_hidden_strangeness", nominal_id="phi"
    ),
    "Jpsi": HadronPatch(
        mc.HadronLedger(0, 0, 0, 0, 0),
        "hidden_quarkonium",
        hidden_content="charm",
        nominal_id="Jpsi",
    ),
    "Upsilon": HadronPatch(
        mc.HadronLedger(0, 0, 0, 0, 0),
        "hidden_quarkonium",
        hidden_content="bottom",
        nominal_id="Upsilon",
    ),
    "omega_b": HadronPatch(
        mc.HadronLedger(0, -2, 0, 1, 3),
        "open_bottom_baryon",
        nominal_id="omega_b",
    ),
    "lambda": HadronPatch(
        mc.HadronLedger(0, -1, 0, 0, 3),
        "baryon_octet",
        octet_member="lambda",
        nominal_id="lambda",
    ),
    "sigma_plus": HadronPatch(
        mc.HadronLedger(3, -1, 0, 0, 3),
        "baryon_octet",
        octet_member="sigma",
        isospin="charged",
        nominal_id="sigma_plus",
    ),
    "sigma_zero": HadronPatch(
        mc.HadronLedger(0, -1, 0, 0, 3),
        "baryon_octet",
        octet_member="sigma",
        isospin="neutral_isovector",
        nominal_id="sigma_zero",
    ),
    "sigma_minus": HadronPatch(
        mc.HadronLedger(-3, -1, 0, 0, 3),
        "baryon_octet",
        octet_member="sigma",
        isospin="charged",
        nominal_id="sigma_minus",
    ),
    "xi_zero": HadronPatch(
        mc.HadronLedger(0, -2, 0, 0, 3),
        "baryon_octet",
        octet_member="xi",
        isospin="neutral_isovector",
        nominal_id="xi_zero",
    ),
    "xi_minus": HadronPatch(
        mc.HadronLedger(-3, -2, 0, 0, 3),
        "baryon_octet",
        octet_member="xi",
        isospin="charged",
        nominal_id="xi_minus",
    ),
}


@lru_cache(maxsize=1)
def _catalog_patch_index() -> dict[str, HadronPatch]:
    out: dict[str, HadronPatch] = dict(_MANUAL_PATCHES)
    for row in hmc.parse_hadron_catalog():
        sid = row["config_id"]
        if sid in _MANUAL_PATCHES:
            continue
        ledger = mc.species_ledger(sid)
        if ledger is None:
            continue
        sector = _sector_from_catalog_row(row)
        out[sid] = HadronPatch(
            ledger=ledger,
            sector=sector,
            excitation=_excitation_from_catalog_row(row),
            octet_member=_octet_member_from_sid(sid, sector),
            nominal_id=sid,
        )
    return out


def patch_from_species_id(species_id: str) -> HadronPatch | None:
    """Resolve a comparison alias to its property patch (identity lookup only)."""
    return _catalog_patch_index().get(resolve_species_alias(species_id))


def patch_from_daughters(daughter_ids: tuple[str, ...]) -> tuple[HadronPatch, ...]:
    patches: list[HadronPatch] = []
    for did in daughter_ids:
        p = patch_from_species_id(did)
        if p is None:
            raise KeyError(f"no HadronPatch for daughter {did!r}")
        patches.append(p)
    return tuple(patches)


def nominal_tag(patch: HadronPatch) -> str | None:
    """PDG / catalog alias for comparison export — not used in routing."""
    return patch.nominal_id


def decay_capable_patches() -> tuple[HadronPatch, ...]:
    """Unique decay-capable property patches (one row per ``patch_key``)."""
    seen: set[tuple[Any, ...]] = set()
    out: list[HadronPatch] = []
    for p in _catalog_patch_index().values():
        if not p.is_decay_capable:
            continue
        key = p.patch_key()
        if key in seen:
            continue
        seen.add(key)
        out.append(p)
    return tuple(sorted(out, key=lambda x: (x.sector, x.ledger.q3, x.nominal_id or "")))


@lru_cache(maxsize=1)
def decay_capable_nominal_ids() -> frozenset[str]:
    """All catalog aliases whose property patch can host multichannel decay."""
    return frozenset(
        sid
        for sid, p in _catalog_patch_index().items()
        if p.is_decay_capable
    )


def patch_decay_capable(species_id: str) -> bool:
    """Whether a comparison alias maps to a decay-capable property patch."""
    patch = patch_from_species_id(species_id)
    return patch is not None and patch.is_decay_capable


def sorted_patch_keys(species_ids: tuple[str, ...]) -> tuple[tuple[Any, ...], ...]:
    """Order-independent multiset of daughter patch keys."""
    keys: list[tuple[Any, ...]] = []
    for sid in species_ids:
        patch = patch_from_species_id(resolve_species_alias(sid))
        if patch is None:
            raise KeyError(f"no HadronPatch for species {sid!r}")
        keys.append(patch.patch_key())
    return tuple(sorted(keys))


def daughter_patches_match(
    got_ids: tuple[str, ...],
    want_ids: tuple[str, ...],
) -> bool:
    """Match decay daughters by property patch, not nominal string identity."""
    try:
        return sorted_patch_keys(got_ids) == sorted_patch_keys(want_ids)
    except KeyError:
        return False


def daughter_patch(daughter_id: str) -> HadronPatch | None:
    """Resolve one daughter slot to its property patch."""
    return patch_from_species_id(daughter_id)


def daughter_patches(daughter_ids: Sequence[str]) -> tuple[HadronPatch, ...]:
    """All daughter patches (raises if any slot is unknown)."""
    return patch_from_daughters(tuple(daughter_ids))


def _daughter_predicate_ok(
    daughter_ids: Sequence[str],
    predicate,
    *,
    count: int | None = None,
    at_least: int = 1,
) -> bool:
    patches = [daughter_patch(d) for d in daughter_ids]
    if any(p is None for p in patches):
        return False
    matched = sum(1 for p in patches if predicate(p))
    if count is not None:
        return matched == count
    return matched >= at_least


def all_daughters_match(daughter_ids: Sequence[str], predicate) -> bool:
  patches = [daughter_patch(d) for d in daughter_ids]
  return bool(patches) and all(p is not None and predicate(p) for p in patches)


def is_pion_discharge_patch(patch: HadronPatch) -> bool:
    """Charged or neutral-isovector π discharge (not η)."""
    return patch.is_light_pseudoscalar_decay_parent


def is_kaon_discharge_patch(patch: HadronPatch) -> bool:
    return patch.is_light_kaon


def is_charged_kaon_patch(patch: HadronPatch) -> bool:
    return patch.is_light_kaon and patch.ledger.q3 != 0


def is_neutral_kaon_patch(patch: HadronPatch) -> bool:
    return patch.is_light_kaon and patch.ledger.q3 == 0


def is_nucleon_patch(patch: HadronPatch) -> bool:
    return patch.sector == "baryon_nucleon"


def is_lambda_octet_patch(patch: HadronPatch) -> bool:
    return patch.is_lambda_octet


def is_light_baryon_discharge_patch(patch: HadronPatch) -> bool:
    return patch.sector in ("baryon_octet", "baryon_nucleon") and (
        abs(patch.ledger.charm) == 0 and abs(patch.ledger.bottom) == 0
    )


def is_light_hadron_meson_patch(patch: HadronPatch) -> bool:
    return (
        patch.is_meson
        and abs(patch.ledger.charm) == 0
        and abs(patch.ledger.bottom) == 0
        and patch.sector != "gamma"
    )


def is_open_charm_daughter_patch(patch: HadronPatch) -> bool:
    return patch.is_open_charm


def is_charmed_baryon_ground_patch(patch: HadronPatch) -> bool:
    return patch.is_open_charm_baryon_ground


def is_hidden_strangeness_patch(patch: HadronPatch) -> bool:
    return patch.sector == "meson_hidden_strangeness"


def is_open_charm_strange_daughter_patch(patch: HadronPatch) -> bool:
    return patch.is_open_charm_strange_meson


def is_pi_zero_patch(patch: HadronPatch) -> bool:
    return (
        patch.is_light_pseudoscalar_meson
        and patch.isospin == "neutral_isovector"
    )


def is_eta_patch(patch: HadronPatch) -> bool:
    return patch.is_light_pseudoscalar_meson and patch.isospin == "isoscalar"


def is_charged_pion_for_parent(
    parent: HadronPatch,
    daughter: HadronPatch,
) -> bool:
    """Leading-charge pion tag for weak outlets (ledger-oriented)."""
    if not is_pion_discharge_patch(daughter) or daughter.ledger.q3 == 0:
        return False
    if parent.ledger.q3 > 0:
        return daughter.ledger.q3 > 0
    if parent.ledger.q3 < 0:
        return daughter.ledger.q3 < 0
    if parent.is_open_charm_meson_nonstrange and parent.ledger.q3 == 0:
        return daughter.ledger.q3 < 0
    return False


def daughters_include_property(
    daughter_ids: Sequence[str],
    predicate,
    *,
    count: int = 1,
) -> bool:
    return _daughter_predicate_ok(daughter_ids, predicate, count=count)


def daughters_all_in_pool(daughter_ids: Sequence[str], tag: DaughterPoolTag) -> bool:
    return all_daughters_match(
        daughter_ids, lambda p: patch_in_pool(p, tag)
    )


def patches_matching_ledger(target: mc.HadronLedger) -> tuple[HadronPatch, ...]:
    """All property patches with the same flavor ledger (may differ by sector / excitation)."""
    return tuple(p for p in _catalog_patch_index().values() if p.ledger == target)


def _is_light_flavor_patch(p: HadronPatch) -> bool:
    return abs(p.ledger.charm) == 0 and abs(p.ledger.bottom) == 0


def _is_standard_light_meson(p: HadronPatch) -> bool:
    """Light pseudoscalar discharge slots (exclude exotic catalog resonances)."""
    return (
        p.sector == "meson_pseudoscalar"
        and _is_light_flavor_patch(p)
        and p.isospin != "unknown"
    )


def _is_standard_light_vector(p: HadronPatch) -> bool:
    return p.is_light_vector_meson and _is_light_flavor_patch(p) and p.isospin != "unknown"


def patch_in_pool(patch: HadronPatch, tag: DaughterPoolTag) -> bool:
    """Whether a registry patch belongs to a discharge daughter pool."""
    if tag == "quarkonium_cascade":
        return patch.nominal_id in ("Jpsi", "phi", "rho_zero", "omega_meson")
    if tag == "gamma":
        return patch.sector == "gamma"
    if tag == "lepton_charged":
        return patch.sector == "lepton" and patch.nominal_id in (
            "e_plus",
            "e_minus",
            "mu_plus",
            "mu_minus",
        )
    if not _is_light_flavor_patch(patch):
        if tag == "open_charm_meson":
            return patch.sector == "open_charm_meson"
        if tag == "open_charm_strange_meson":
            return patch.is_open_charm_strange_meson
        if tag == "charmed_baryon_ground":
            return patch.is_open_charm_baryon_ground
        if tag == "hidden_quarkonium_charm":
            return patch.is_hidden_quarkonium and patch.hidden_content == "charm"
        if tag == "hidden_quarkonium_bottom":
            return patch.is_hidden_quarkonium and patch.hidden_content == "bottom"
        return False
    if tag == "light_pseudoscalar":
        return _is_standard_light_meson(patch)
    if tag == "light_vector":
        return _is_standard_light_vector(patch)
    if tag == "light_hidden_strangeness":
        return patch.sector == "meson_hidden_strangeness"
    if tag == "light_hadronic_2body":
        return (
            _is_standard_light_meson(patch)
            or _is_standard_light_vector(patch)
            or patch_in_pool(patch, "light_hidden_strangeness")
        )
    if tag == "light_hadronic_3body":
        return _is_standard_light_meson(patch) or _is_standard_light_vector(patch)
    if tag == "light_baryon_octet":
        return (
            patch.sector == "baryon_octet"
            and _is_light_flavor_patch(patch)
            and patch.octet_member != "unknown"
        )
    if tag == "light_nucleon":
        return patch.sector == "baryon_nucleon"
    if tag == "weak_light_pseudoscalar":
        return _is_standard_light_meson(patch)
    if tag == "weak_light_with_vector":
        return _is_standard_light_meson(patch) or _is_standard_light_vector(patch)
    if tag == "ds_weak_light":
        return _is_standard_light_meson(patch)
    return False


@lru_cache(maxsize=32)
def pool_nominal_ids(tag: DaughterPoolTag) -> tuple[str, ...]:
    """Comparison aliases for one slot per property patch in a daughter pool."""
    seen: set[tuple[Any, ...]] = set()
    out: list[str] = []
    for patch in _catalog_patch_index().values():
        if not patch_in_pool(patch, tag):
            continue
        key = patch.patch_key()
        if key in seen:
            continue
        seen.add(key)
        if patch.nominal_id:
            out.append(patch.nominal_id)
    return tuple(sorted(out))


def daughter_in_pool(daughter_id: str, tag: DaughterPoolTag) -> bool:
    patch = patch_from_species_id(daughter_id)
    return patch is not None and patch_in_pool(patch, tag)


def _pool_union(*tags: DaughterPoolTag) -> tuple[str, ...]:
    seen: set[str] = set()
    out: list[str] = []
    for tag in tags:
        for sid in pool_nominal_ids(tag):
            if sid not in seen:
                seen.add(sid)
                out.append(sid)
    return tuple(out)


def weak_daughter_pool_for(parent: HadronPatch) -> tuple[str, ...]:
    """Property-first weak daughter pool (nominal ids for mass readout only)."""
    ps = pool_nominal_ids("light_pseudoscalar")
    light_2body = pool_nominal_ids("light_hadronic_2body")
    baryon_oct = pool_nominal_ids("light_baryon_octet")
    nucleon = pool_nominal_ids("light_nucleon")
    open_charm = pool_nominal_ids("open_charm_meson")
    open_charm_strange = pool_nominal_ids("open_charm_strange_meson")
    charmed_ground = pool_nominal_ids("charmed_baryon_ground")
    weak_light = pool_nominal_ids("weak_light_pseudoscalar")
    weak_with_vec = pool_nominal_ids("weak_light_with_vector")
    jpsi = pool_nominal_ids("hidden_quarkonium_charm")

    if parent.is_light_kaon:
        return ps
    if parent.is_light_strange_baryon and not parent.is_decuplet_baryon:
        return _pool_union("light_baryon_octet", "light_nucleon", "light_pseudoscalar")
    if parent.is_open_charm_strange_meson:
        return pool_nominal_ids("ds_weak_light")
    if parent.is_open_charm_meson_nonstrange:
        leptons = ("mu_plus", "e_plus") if parent.ledger.q3 > 0 else ("mu_minus", "e_minus")
        return weak_with_vec + leptons
    if parent.is_open_bottom_meson_strange:
        return _pool_union("open_charm_strange_meson", "light_hidden_strangeness", "weak_light_with_vector")
    if parent.is_open_bottom_meson_nonstrange:
        return _pool_union("open_charm_meson", "weak_light_with_vector", "hidden_quarkonium_charm")
    if parent.is_open_charm_baryon_ground:
        base = _pool_union("light_nucleon", "light_pseudoscalar") + (
            "K_plus",
            "K_minus",
        )
        if parent.nominal_id == "lambda_c":
            return base + ("mu_plus", "e_plus")
        return base
    if parent.is_open_charm_baryon_cascade:
        return _pool_union("charmed_baryon_ground", "light_pseudoscalar") + (
            "K_plus",
            "K0",
        )
    if parent.is_open_bottom_baryon:
        return _pool_union(
            "charmed_baryon_ground",
            "open_charm_meson",
            "light_nucleon",
            "light_pseudoscalar",
            "hidden_quarkonium_charm",
        ) + ("K_plus", "K_minus")
    return light_2body


def strong_daughter_pool_for(parent: HadronPatch) -> tuple[str, ...]:
    """Property-first strong daughter pool (nominal ids for mass readout only)."""
    ps = pool_nominal_ids("light_pseudoscalar")
    if parent.is_light_vector_meson or parent.sector == "meson_hidden_strangeness":
        return ps
    if parent.is_decuplet_baryon:
        return _pool_union("light_nucleon", "light_pseudoscalar")
    if parent.is_hyperon_strong_discharge_parent:
        return _pool_union("light_baryon_octet", "light_nucleon", "light_pseudoscalar")
    if parent.is_open_charm_strange_meson:
        return pool_nominal_ids("light_hadronic_2body")
    if parent.is_open_charm_baryon_cascade:
        return _pool_union("charmed_baryon_ground", "light_pseudoscalar")
    return ()


def neutral_light_pair_cascade_pairs() -> tuple[tuple[str, str], ...]:
    """Charge / strangeness neutral light pair discharge tags for quarkonium cascades."""
    pairs: list[tuple[str, str]] = []
    slots = pool_nominal_ids("weak_light_pseudoscalar")
    for a in slots:
        pa = patch_from_species_id(a)
        if pa is None:
            continue
        for b in slots:
            if a > b:
                continue
            pb = patch_from_species_id(b)
            if pb is None:
                continue
            q = pa.ledger.q3 + pb.ledger.q3
            s = pa.ledger.strangeness + pb.ledger.strangeness
            if q == 0 and s == 0:
                pairs.append((a, b))
    return tuple(pairs)


def is_neutral_isovector_vector(patch) -> bool:
    """ρ⁰-like: neutral vector meson on the light vector sector."""
    return (
        patch.is_light_vector_meson
        and patch.isospin == "neutral_isovector"
        and patch.ledger.charm == 0
    )
