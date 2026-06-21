#!/usr/bin/env python3
"""
Lean ``HepDecayChannelRouting.lean`` finite spanning certificates.

Spanning sets are **generated** from patch daughter pools + property topology
(``hqiv_property_spanning.py``).  Legacy named tuples below are regression oracles only.

Mirror: ``lambdaWeakModes``, ``lambdaCWeakModes``, ``KplusWeakModes``, etc.
"""

from __future__ import annotations

from typing import Any, Sequence

# Lazy ``hqiv_property_spanning`` import — avoids cycle with multichannel expansion.
LAMBDA_WEAK: tuple[tuple[str, ...], ...] = (
    ("p", "pi_minus"),
    ("n", "pi_zero"),
)

K_PLUS_WEAK: tuple[tuple[str, ...], ...] = (
    ("pi_plus",),
    ("pi_zero",),
    ("pi_plus", "pi_zero", "pi_zero"),
)

K0_WEAK: tuple[tuple[str, ...], ...] = (("pi_zero",),)

K_MINUS_WEAK: tuple[tuple[str, ...], ...] = (
    ("pi_minus",),
    ("pi_zero",),
    ("pi_minus", "pi_zero", "pi_zero"),
)

K_PLUS_SEMILEPTONIC_WEAK: tuple[tuple[str, ...], ...] = (("mu_plus",),)

K_MINUS_SEMILEPTONIC_WEAK: tuple[tuple[str, ...], ...] = (("mu_minus",),)

LAMBDA_C_WEAK: tuple[tuple[str, ...], ...] = (
    ("p", "pi_zero"),
    ("n", "K_plus"),
    ("p", "K_minus", "pi_plus"),
    ("p", "K_minus", "pi_zero"),
    ("p", "K_plus", "pi_minus"),
    ("p", "K_minus", "pi_plus", "pi_zero"),
    ("mu_plus",),
    ("e_plus",),
)

D_PLUS_SEMILEPTONIC_WEAK: tuple[tuple[str, ...], ...] = (
    ("mu_plus",),
    ("e_plus",),
)

D0_SEMILEPTONIC_WEAK: tuple[tuple[str, ...], ...] = (
    ("mu_minus",),
    ("e_minus",),
)

LAMBDA_C_SEMILEPTONIC_WEAK: tuple[tuple[str, ...], ...] = (
    ("mu_plus",),
    ("e_plus",),
)

BS_WEAK: tuple[tuple[str, ...], ...] = (
    ("Ds_plus", "K_minus"),
    ("phi", "phi"),
)

DS_WEAK: tuple[tuple[str, ...], ...] = (
    ("K_plus",),
    ("K0", "pi_plus"),
    ("K_plus", "pi_zero"),
    ("K_plus", "K_minus", "pi_plus"),
    ("eta", "pi_plus"),
)

XI_C_WEAK: tuple[tuple[str, ...], ...] = (
    ("lambda_c", "pi_zero"),
    ("lambda_c", "pi_plus"),
    ("lambda_c", "pi_minus"),
    ("sigma_c", "pi_zero"),
    ("sigma_c", "pi_plus"),
    ("sigma_c", "pi_minus"),
)

D_PLUS_WEAK: tuple[tuple[str, ...], ...] = (
    ("K_minus", "pi_plus"),
    ("K_minus", "rho_plus"),
    ("K0_bar", "omega_meson"),
    ("K0_bar", "rho_zero"),
    ("K0_bar", "rho_plus"),
    ("K0", "eta"),
    ("K0", "omega_meson"),
    ("K0", "rho_zero"),
    ("K0", "pi_plus"),
    ("K0", "rho_plus"),
    ("K_minus", "pi_plus", "pi_zero"),
    ("pi_minus", "pi_plus", "pi_zero"),
    ("pi_minus", "pi_zero", "rho_plus"),
    ("K0", "pi_plus", "pi_zero"),
) + D_PLUS_SEMILEPTONIC_WEAK

D0_WEAK: tuple[tuple[str, ...], ...] = (
    ("K0", "pi_minus"),
    ("K_plus", "pi_minus"),
    ("K0_bar", "omega_meson"),
    ("K0_bar", "rho_zero"),
    ("K0_bar", "rho_plus"),
    ("K0", "eta"),
    ("K0", "omega_meson"),
    ("K0", "rho_zero"),
    ("K0", "rho_plus"),
    ("K0", "pi_minus", "pi_zero"),
    ("pi_minus", "pi_plus", "pi_zero"),
    ("pi_minus", "pi_zero", "rho_plus"),
    ("K_plus", "pi_minus", "pi_zero"),
) + D0_SEMILEPTONIC_WEAK

B_PLUS_WEAK: tuple[tuple[str, ...], ...] = (
    ("D_plus", "K_minus"),
    ("D_plus", "pi_minus"),
    ("D_plus", "K0_bar"),
    ("D_plus", "eta"),
    ("D_plus", "pi_zero"),
    ("D_plus", "omega_meson"),
    ("D_plus", "rho_zero"),
    ("D0", "pi_plus"),
    ("D0", "rho_plus"),
    ("D0", "K_plus"),
    ("D_plus", "K0"),
    ("D_plus", "pi_minus", "pi_zero"),
    ("D0", "pi_plus", "pi_zero"),
)

B0_WEAK: tuple[tuple[str, ...], ...] = (
    ("D0", "K_minus"),
    ("D_plus", "K_minus"),
    ("D0", "pi_minus"),
    ("D_plus", "pi_minus"),
    ("D0", "K0_bar"),
    ("D_plus", "K0_bar"),
    ("D0", "eta"),
    ("D_plus", "eta"),
    ("D0", "pi_zero"),
    ("D_plus", "pi_zero"),
    ("D0", "omega_meson"),
    ("D_plus", "omega_meson"),
    ("D0", "rho_zero"),
    ("D_plus", "rho_zero"),
    ("D0", "K0"),
    ("D0", "pi_plus"),
    ("D0", "rho_plus"),
    ("D0", "K_plus"),
    ("D_plus", "K0"),
    ("D0", "pi_plus", "pi_zero"),
)

# Strong light-hadron spanning sets.
DELTA_P_STRONG: tuple[tuple[str, ...], ...] = (
    ("p", "pi_zero"),
    ("n", "pi_plus"),
)

DELTA_PP_STRONG: tuple[tuple[str, ...], ...] = (("p", "pi_plus"),)

RHO_ZERO_STRONG: tuple[tuple[str, ...], ...] = (("pi_plus", "pi_minus"),)

RHO_PLUS_STRONG: tuple[tuple[str, ...], ...] = (("pi_plus", "pi_zero"),)

PHI_STRONG: tuple[tuple[str, ...], ...] = (("K_plus", "K_minus"), ("pi_plus", "pi_minus", "pi_zero"))

OMEGA_MESON_STRONG: tuple[tuple[str, ...], ...] = (("pi_plus", "pi_minus", "pi_zero"),)

SIGMA_PLUS_STRONG: tuple[tuple[str, ...], ...] = (("p", "pi_zero"),)

SIGMA_ZERO_STRONG: tuple[tuple[str, ...], ...] = (("lambda", "pi_zero"),)

SIGMA_MINUS_STRONG: tuple[tuple[str, ...], ...] = (("n", "pi_minus"),)

XI_ZERO_STRONG: tuple[tuple[str, ...], ...] = (("lambda", "pi_zero"),)

XI_MINUS_STRONG: tuple[tuple[str, ...], ...] = (("lambda", "pi_minus"),)

UPSILON_NEUTRAL_CASCADE: tuple[tuple[str, ...], ...] = (
    ("Jpsi", "pi_plus", "pi_minus"),
    ("Jpsi", "pi_zero", "pi_zero"),
)


def _ps():
    import hqiv_property_spanning as ps

    return ps


def _hps():
    import hqiv_hep_patch_species as hps

    return hps


def _mode_patch_keys(modes: tuple[tuple[str, ...], ...]) -> frozenset[tuple[Any, ...]]:
    hps = _hps()
    ps = _ps()
    return frozenset(ps._span_dedup_key(m) for m in modes)


def certified_weak_tuples(parent) -> tuple[tuple[str, ...], ...] | None:
    """Property-enumerated weak spanning set for a parent patch, if certificate-gated."""
    ps = _ps()
    if not ps.parent_has_finite_weak_span(parent):
        return None
    span = ps.enumerate_weak_span(parent)
    return span if span else None


def certified_strong_tuples(parent) -> tuple[tuple[str, ...], ...] | None:
    """Property-enumerated strong spanning set for a parent patch, if certificate-gated."""
    ps = _ps()
    if not ps.parent_has_finite_strong_span(parent):
        return None
    span = ps.enumerate_strong_span(parent)
    return span if span else None


def certified_quarkonium_cascade_tuples(parent) -> tuple[tuple[str, ...], ...] | None:
    """Lean ``upsilonNeutralCascadeModes`` — property-enumerated neutral light pairs."""
    ps = _ps()
    if not ps.parent_has_quarkonium_cascade_span(parent):
        return None
    span = ps.enumerate_quarkonium_cascade_span(parent)
    return span if span else None


def certified_weak_patch_keys(parent) -> frozenset[tuple[Any, ...]] | None:
    tuples = certified_weak_tuples(parent)
    if tuples is None:
        return None
    return _mode_patch_keys(tuples)


def matches_certified_weak(parent, daughter_ids: Sequence[str]) -> bool:
    keys = certified_weak_patch_keys(parent)
    if keys is None:
        return True
    ps = _ps()
    try:
        return ps._span_dedup_key(tuple(daughter_ids)) in keys
    except KeyError:
        return False


def matches_certified_weak_parent_id(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    hps = _hps()
    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return False
    return matches_certified_weak(parent, daughter_ids)


def matches_certified_strong(parent, daughter_ids: Sequence[str]) -> bool:
    tuples = certified_strong_tuples(parent)
    if tuples is None:
        return True
    hps = _hps()
    try:
        return hps.sorted_patch_keys(tuple(daughter_ids)) in _mode_patch_keys(tuples)
    except KeyError:
        return False


def has_certified_strong_span(parent) -> bool:
    """Parent has a Lean finite strong spanning certificate."""
    return certified_strong_tuples(parent) is not None


def is_certified_strong_discharge_parent_id(parent_id: str) -> bool:
    parent = _hps().patch_from_species_id(parent_id)
    return parent is not None and has_certified_strong_span(parent)


def has_certified_weak_span(parent) -> bool:
    return certified_weak_tuples(parent) is not None


def is_light_weak_discharge_parent(parent) -> bool:
    """Certified light-weak pole width: kaons only (Λ width uses baryon weak anchor)."""
    return parent.is_light_kaon


def is_light_weak_discharge_parent_id(parent_id: str) -> bool:
    parent = _hps().patch_from_species_id(parent_id)
    return parent is not None and is_light_weak_discharge_parent(parent)


def matches_certified_strong_discharge(parent_id: str, daughter_ids: Sequence[str]) -> bool:
    parent = _hps().patch_from_species_id(parent_id)
    if parent is None:
        return False
    return matches_certified_strong(parent, daughter_ids)
