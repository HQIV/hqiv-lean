#!/usr/bin/env python3
"""Property-first hadron patch registry tests."""

from __future__ import annotations

import hqiv_hep_multichannel_expansion as mc
import hqiv_hep_patch_species as hps


def test_same_ledger_different_sectors() -> None:
    """π⁰ and η share a flavor ledger but differ by isospin discharge class."""
    pi0 = hps.patch_from_species_id("pi_zero")
    eta = hps.patch_from_species_id("eta")
    assert pi0 is not None and eta is not None
    assert pi0.ledger == eta.ledger
    assert pi0.isospin == "neutral_isovector"
    assert eta.isospin == "isoscalar"
    assert pi0.patch_key() != eta.patch_key()


def test_delta_pp_vs_delta_p_sector_and_ledger() -> None:
    dp = hps.patch_from_species_id("delta_p")
    dpp = hps.patch_from_species_id("delta_pp")
    assert dp is not None and dpp is not None
    assert dp.is_decuplet_baryon and dpp.is_decuplet_baryon
    assert dp.ledger.q3 != dpp.ledger.q3


def test_open_charm_strange_from_properties() -> None:
    ds = hps.patch_from_species_id("Ds_plus")
    d0 = hps.patch_from_species_id("D0")
    assert ds is not None and d0 is not None
    assert ds.is_open_charm_strange_meson
    assert not d0.is_open_charm_strange_meson


def test_xi_b_not_light_strange_baryon() -> None:
    xi_b = hps.patch_from_species_id("xi_b")
    xi0 = hps.patch_from_species_id("xi_zero")
    assert xi_b is not None and xi0 is not None
    assert xi_b.is_open_bottom
    assert not xi_b.is_light_strange_baryon
    assert xi0.is_light_strange_baryon


def test_rho_zero_is_neutral_isovector() -> None:
    rho = hps.patch_from_species_id("rho_zero")
    phi = hps.patch_from_species_id("phi")
    assert rho is not None and phi is not None
    assert hps.is_neutral_isovector_vector(rho)
    assert not hps.is_neutral_isovector_vector(phi)


def test_bs_not_light_kaon() -> None:
    """Open-bottom strange mesons must not inherit light-kaon discharge rules."""
    bs = hps.patch_from_species_id("Bs")
    k = hps.patch_from_species_id("K_plus")
    assert bs is not None and k is not None
    assert not bs.is_light_kaon
    assert k.is_light_kaon
    assert not mc._is_light_multichannel_parent(bs)


def test_eta_not_decay_capable() -> None:
    """Isoscalar η shares π ledger but is not a multichannel decay parent."""
    eta = hps.patch_from_species_id("eta")
    pi0 = hps.patch_from_species_id("pi_zero")
    assert eta is not None and pi0 is not None
    assert eta.ledger == pi0.ledger
    assert not eta.is_decay_capable
    assert pi0.is_decay_capable


def test_quarkonium_hidden_content_distinct() -> None:
    j = hps.patch_from_species_id("Jpsi")
    u = hps.patch_from_species_id("Upsilon")
    assert j is not None and u is not None
    assert j.hidden_content == "charm"
    assert u.hidden_content == "bottom"
    assert j.patch_key() != u.patch_key()
    assert j.is_decay_capable and u.is_decay_capable


def test_decay_capable_covers_legacy_multichannel_parents() -> None:
    capable = hps.decay_capable_nominal_ids()
    missing = mc.MULTICHANNEL_PARENTS - capable
    assert not missing, f"decay_capable_nominal_ids missing {missing}"


def test_daughter_patches_match_by_properties() -> None:
    assert hps.daughter_patches_match(("pi_plus", "pi_minus"), ("pi_plus", "pi_minus"))
    assert not hps.daughter_patches_match(("pi_zero",), ("eta",))


def test_lambda_sigma_zero_distinct_patches() -> None:
    lam = hps.patch_from_species_id("lambda")
    sig = hps.patch_from_species_id("sigma_zero")
    assert lam is not None and sig is not None
    assert lam.octet_member == "lambda"
    assert sig.octet_member == "sigma"
    assert lam.patch_key() != sig.patch_key()


def test_property_daughter_pools_non_empty() -> None:
    assert hps.pool_nominal_ids("light_pseudoscalar")
    assert hps.pool_nominal_ids("light_hadronic_2body")
    assert "Jpsi" in hps.pool_nominal_ids("quarkonium_cascade")
    parent = hps.patch_from_species_id("Bs")
    assert parent is not None
    pool = hps.weak_daughter_pool_for(parent)
    assert "Ds_plus" in pool
    assert "phi" in pool


def test_patch_key_daughter_predicates() -> None:
    assert hps.daughters_include_property(("pi_plus",), hps.is_pion_discharge_patch)
    assert hps.daughters_include_property(("p", "pi_minus"), hps.is_nucleon_patch)
    assert hps.daughters_include_property(("lambda", "pi_zero"), hps.is_lambda_octet_patch)
    assert hps.daughters_include_property(("phi", "phi"), hps.is_hidden_strangeness_patch, count=2)
    assert not hps.daughters_include_property(("eta",), hps.is_pion_discharge_patch)


def test_patch_key_ignores_nominal_id() -> None:
    a = hps.HadronPatch(
        mc.HadronLedger(3, 0, 0, 0, 0),
        "meson_pseudoscalar",
        nominal_id="alias_a",
    )
    b = hps.HadronPatch(
        mc.HadronLedger(3, 0, 0, 0, 0),
        "meson_pseudoscalar",
        nominal_id="alias_b",
    )
    assert a.patch_key() == b.patch_key()


if __name__ == "__main__":
    test_same_ledger_different_sectors()
    test_delta_pp_vs_delta_p_sector_and_ledger()
    test_open_charm_strange_from_properties()
    test_xi_b_not_light_strange_baryon()
    test_rho_zero_is_neutral_isovector()
    test_bs_not_light_kaon()
    test_eta_not_decay_capable()
    test_quarkonium_hidden_content_distinct()
    test_decay_capable_covers_legacy_multichannel_parents()
    test_daughter_patches_match_by_properties()
    test_lambda_sigma_zero_distinct_patches()
    test_property_daughter_pools_non_empty()
    test_patch_key_daughter_predicates()
    test_patch_key_ignores_nominal_id()
    print("test_hqiv_hep_patch_species: OK")
