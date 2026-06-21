#!/usr/bin/env python3
"""Cross-check Python weak enumeration + routing against Lean certificates."""

from __future__ import annotations

import unittest

import hqiv_hep_decay_readout as hdr
import hqiv_hep_multichannel_expansion as mc


class TestOutsideMassDressingMirror(unittest.TestCase):
    def test_outside_mass_dressing_rationals(self) -> None:
        self.assertAlmostEqual(hdr.open_charm_outside_mass_dressing(), 21.0 / 20.0)
        self.assertAlmostEqual(hdr.charmed_baryon_outside_mass_dressing(), 43.0 / 40.0)
        self.assertAlmostEqual(hdr.open_bottom_outside_mass_dressing(), 41.0 / 40.0)
        self.assertAlmostEqual(hdr.bottom_baryon_outside_mass_dressing(), 53.0 / 50.0)
        self.assertAlmostEqual(hdr.hidden_quarkonium_outside_mass_dressing(), 41.0 / 40.0)
        self.assertAlmostEqual(hdr.chiral_pseudoscalar_outside_mass_dressing(), 81.0 / 80.0)
        self.assertAlmostEqual(hdr.strange_baryon_octet_outside_mass_dressing(), 79.0 / 80.0)
        self.assertAlmostEqual(
            hdr.hidden_strangeness_vector_outside_mass_dressing(), 61.0 / 60.0
        )


class TestLeanRoutingMirror(unittest.TestCase):
  def test_B0_D0pi0_bottom_neutral_spectator(self) -> None:
    kind = mc.open_flavour_contact_kind("B0", "weak", ("D0", "pi_zero"))
    self.assertEqual(kind, "bottom_neutral_spectator")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 3.0 / 2.0)

  def test_Bplus_D0piplus_external_weak(self) -> None:
    kind = mc.open_flavour_contact_kind("B_plus", "weak", ("D0", "pi_plus"))
    self.assertEqual(kind, "bottom_external_weak")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 7.0 / 2.0)

  def test_Bplus_DplusK_finite_open_bottom(self) -> None:
    kind = mc.open_flavour_contact_kind("B_plus", "weak", ("D_plus", "K_minus"))
    self.assertEqual(kind, "finite_open_bottom_completion")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 1.0 / 15.0)

  def test_lambda_c_PKpi_double_monogamy(self) -> None:
    kind = mc.open_flavour_contact_kind(
      "lambda_c", "weak", ("p", "K_minus", "pi_plus")
    )
    self.assertEqual(kind, "charmed_baryon_semileptonic_hadronic")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 84.0 / 11.0)

  def test_lambda_c_PKpi_sibling_double_monogamy(self) -> None:
    kind = mc.open_flavour_contact_kind("lambda_c", "weak", ("p", "K_minus", "pi_zero"))
    self.assertEqual(kind, "charmed_baryon_semileptonic_hadronic")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 84.0 / 11.0)

  def test_lambda_c_wrong_sign_semileptonic_hadronic(self) -> None:
    kind = mc.open_flavour_contact_kind("lambda_c", "weak", ("p", "K_plus", "pi_minus"))
    self.assertEqual(kind, "charmed_baryon_semileptonic_hadronic")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 84.0 / 11.0)

  def test_xi_c_charged_pion_exclusion(self) -> None:
    kind = mc.open_flavour_contact_kind("xi_c", "weak", ("lambda_c", "pi_plus"))
    self.assertEqual(kind, "double_monogamy_exclusion")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 21.0 / 25.0)

  def test_xi_c_sigma_pi0_neutral_spectator(self) -> None:
    kind = mc.open_flavour_contact_kind("xi_c", "weak", ("sigma_c", "pi_zero"))
    self.assertEqual(kind, "neutral_spectator_complement")

  def test_xi_c_lambda_pi0_cascade_lambda_ground(self) -> None:
    kind = mc.open_flavour_contact_kind("xi_c", "weak", ("lambda_c", "pi_zero"))
    self.assertEqual(kind, "cascade_lambda_ground")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 163.0 / 60.0)

  def test_Ds_strong_phi_pole_discharge(self) -> None:
    kind = mc.open_flavour_contact_kind("Ds_plus", "strong", ("phi",))
    self.assertEqual(kind, "hidden_strangeness_pole_discharge")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 8.0 / 5.0)

  def test_Bs_DsK_bottom_strange(self) -> None:
    kind = mc.open_flavour_contact_kind("Bs", "weak", ("Ds_plus", "K_minus"))
    self.assertEqual(kind, "bottom_strange_double_monogamy")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 25.0 / 4.0)

  def test_Bs_phi_hidden_strangeness(self) -> None:
    kind = mc.open_flavour_contact_kind("Bs", "weak", ("phi", "phi"))
    self.assertEqual(kind, "bottom_strange_double_monogamy")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 25.0 / 4.0)


class TestWeakEnumerationMirror(unittest.TestCase):
  """Mirror Lean ``weakChannelAllowed`` finite spanning sets."""

  LAMBDA_C_MODES = (
    ("p", "pi_zero"),
    ("n", "K_plus"),
    ("p", "K_minus", "pi_plus"),
    ("p", "K_minus", "pi_zero"),
    ("p", "K_plus", "pi_minus"),
    ("p", "K_minus", "pi_plus", "pi_zero"),
  )

  DS_WEAK_MODES = (
    ("K_plus",),
    ("K0", "pi_plus"),
    ("K_plus", "pi_zero"),
    ("K_plus", "K_minus", "pi_plus"),
    ("eta", "pi_plus"),
  )

  BS_WEAK_MODES = (
    ("Ds_plus", "K_minus"),
    ("phi", "phi"),
  )

  XI_C_MODES = (
    ("lambda_c", "pi_zero"),
    ("lambda_c", "pi_plus"),
    ("lambda_c", "pi_minus"),
    ("sigma_c", "pi_zero"),
    ("sigma_c", "pi_plus"),
    ("sigma_c", "pi_minus"),
  )

  def test_lambda_c_spanning_six_modes(self) -> None:
    self.assertEqual(len(self.LAMBDA_C_MODES), 6)
    for ds in self.LAMBDA_C_MODES:
      self.assertTrue(mc._weak_channel_allowed("lambda_c", ds), ds)

  def test_dplus_full_weak_sixteen_modes(self) -> None:
    import hqiv_hep_decay_certificates as cert

    modes = cert.D_PLUS_WEAK
    self.assertEqual(len(modes), 16)
    for ds in modes:
      self.assertTrue(mc._weak_channel_allowed("D_plus", ds), ds)
    self.assertEqual(
        mc.open_flavour_contact_kind("D_plus", "weak", ("mu_plus",)),
        "open_charm_semileptonic_neutrino_completion",
    )
    self.assertEqual(
        mc.open_flavour_contact_kind("D_plus", "weak", ("K_minus", "rho_plus")),
        "hidden_strangeness_vector_leak",
    )
    self.assertEqual(
        mc.open_flavour_contact_kind("D_plus", "weak", ("K0", "eta")),
        "hidden_strangeness_vector_leak",
    )
    self.assertEqual(
        mc.open_flavour_contact_kind("D_plus", "weak", ("pi_minus", "pi_zero", "rho_plus")),
        "charm_pion_only",
    )

  def test_lambda_c_full_weak_eight_modes(self) -> None:
    import hqiv_hep_decay_certificates as cert

    self.assertEqual(len(cert.LAMBDA_C_WEAK), 8)
    self.assertTrue(mc._weak_channel_allowed("lambda_c", ("mu_plus",)))

  def test_bs_spanning_two_modes(self) -> None:
    for ds in self.BS_WEAK_MODES:
      self.assertTrue(mc._weak_channel_allowed("Bs", ds), ds)

  def test_ds_weak_sparse_five_modes(self) -> None:
    for ds in self.DS_WEAK_MODES:
      self.assertTrue(mc._weak_channel_allowed("Ds_plus", ds), ds)

  def test_xi_c_cascade_sparse(self) -> None:
    for ds in self.XI_C_MODES:
      self.assertTrue(mc._weak_channel_allowed("xi_c", ds), ds)

  def test_xi_c_lambda_pi0_routing(self) -> None:
    ds = ("lambda_c", "pi_zero")
    self.assertTrue(mc._weak_channel_allowed("xi_c", ds))
    kind = mc.open_flavour_contact_kind("xi_c", "weak", ds)
    self.assertEqual(kind, "cascade_lambda_ground")


class TestLightHadronEnumerationMirror(unittest.TestCase):
  """Mirror Lean light-hadron strong/weak spanning certificates."""

  DELTA_P_STRONG = (("p", "pi_zero"), ("n", "pi_plus"))
  RHO_ZERO_STRONG = (("pi_plus", "pi_minus"),)
  LAMBDA_WEAK = (("p", "pi_minus"), ("n", "pi_zero"))
  K_PLUS_WEAK = (("pi_plus",), ("pi_zero",), ("pi_plus", "pi_zero", "pi_zero"))

  def test_delta_p_strong_charge_conserving(self) -> None:
    for ds in self.DELTA_P_STRONG:
      self.assertTrue(mc._light_strong_channel_allowed("delta_p", ds), ds)
    self.assertFalse(mc._light_strong_channel_allowed("delta_p", ("p", "pi_plus")))

  def test_delta_pp_strong_p_pi_plus(self) -> None:
    self.assertTrue(mc._light_strong_channel_allowed("delta_pp", ("p", "pi_plus")))

  def test_rho_zero_charged_conjugate_only(self) -> None:
    self.assertTrue(mc._light_strong_channel_allowed("rho_zero", ("pi_plus", "pi_minus")))
    self.assertFalse(mc._light_strong_channel_allowed("rho_zero", ("pi_zero", "pi_zero")))

  def test_rho_zero_single_open_channel(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("rho_zero"), env=env)
    open_edges = [e for e in edges if e.channel_open]
    self.assertEqual(len(open_edges), 1)
    self.assertEqual(
        tuple(sorted(open_edges[0].mode.daughter_ids)),
        ("pi_minus", "pi_plus"),
    )
    self.assertAlmostEqual(open_edges[0].branching_ratio, 1.0, places=6)

  def test_lambda_weak_modes(self) -> None:
    for ds in self.LAMBDA_WEAK:
      self.assertTrue(mc._light_weak_channel_allowed("lambda", ds), ds)

  def test_K_plus_sparse_weak_modes(self) -> None:
    for ds in self.K_PLUS_WEAK:
      self.assertTrue(mc._light_weak_channel_allowed("K_plus", ds), ds)
    self.assertFalse(mc._light_weak_channel_allowed("K_plus", ("pi_plus", "pi_minus")))

  def test_sigma_plus_strong_certificate(self) -> None:
    import hqiv_hep_decay_certificates as cert
    import hqiv_hep_patch_species as hps

    parent = hps.patch_from_species_id("sigma_plus")
    self.assertEqual(cert.certified_strong_tuples(parent), cert.SIGMA_PLUS_STRONG)
    self.assertTrue(mc._light_strong_channel_allowed("sigma_plus", ("p", "pi_zero")))

  def test_xi_minus_strong_certificate(self) -> None:
    import hqiv_hep_decay_certificates as cert
    import hqiv_hep_patch_species as hps

    parent = hps.patch_from_species_id("xi_minus")
    self.assertEqual(cert.certified_strong_tuples(parent), cert.XI_MINUS_STRONG)
    self.assertTrue(mc._light_strong_channel_allowed("xi_minus", ("lambda", "pi_minus")))


class TestIsospinHalfContactRouting(unittest.TestCase):
  def test_lambda_isospin_half_contacts(self) -> None:
    kind_charged = mc.open_flavour_contact_kind("lambda", "weak", ("p", "pi_minus"))
    kind_neutral = mc.open_flavour_contact_kind("lambda", "weak", ("n", "pi_zero"))
    self.assertEqual(kind_charged, "isospin_half_weak")
    self.assertEqual(kind_neutral, "light_baryon_neutral_isospin_outlet")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind_charged), 7.0 / 5.0)
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind_neutral), 18.0 / 23.0)

  def test_K_plus_isospin_half_contacts(self) -> None:
    kind_charged = mc.open_flavour_contact_kind("K_plus", "weak", ("pi_plus",))
    kind_neutral = mc.open_flavour_contact_kind("K_plus", "weak", ("pi_zero",))
    self.assertEqual(kind_charged, "isospin_half_hadronic_semileptonic_competition")
    self.assertEqual(kind_neutral, "isospin_half_neutral_hadronic_semileptonic_competition")
    self.assertAlmostEqual(
        hdr.open_flavour_contact_weight(kind_charged),
        hdr.isospin_half_hadronic_semileptonic_competition(),
    )
    self.assertAlmostEqual(
        hdr.open_flavour_contact_weight(kind_neutral),
        hdr.isospin_half_neutral_hadronic_semileptonic_competition(),
    )

  def test_K_plus_mu_semileptonic_aperture(self) -> None:
    kind = mc.open_flavour_contact_kind("K_plus", "weak", ("mu_plus",))
    self.assertEqual(kind, "light_kaon_semileptonic_neutrino_completion")
    self.assertAlmostEqual(
        hdr.open_flavour_contact_weight(kind), hdr.light_kaon_semileptonic_neutrino_completion()
    )
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 209.0 / 1800.0)

  def test_D_plus_mu_open_charm_semileptonic_outlet(self) -> None:
    kind = mc.open_flavour_contact_kind("D_plus", "weak", ("mu_plus",))
    self.assertEqual(kind, "open_charm_semileptonic_neutrino_completion")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 2.0 / 9.0)

  def test_D_plus_semileptonic_branching_fraction(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("D_plus"), env=env)
    semi = sum(
        e.branching_ratio
        for e in edges
        if e.mode.daughter_ids in (("mu_plus",), ("e_plus",))
    )
    self.assertGreater(semi, 0.14)
    self.assertLess(semi, 0.20)

  def test_lambda_c_mu_open_charm_semileptonic_outlet(self) -> None:
    kind = mc.open_flavour_contact_kind("lambda_c", "weak", ("mu_plus",))
    self.assertEqual(kind, "open_charm_semileptonic_neutrino_completion")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 2.0 / 9.0)


class TestLightVectorStrongCertificates(unittest.TestCase):
  PHI_STRONG = (("K_plus", "K_minus"), ("pi_plus", "pi_minus", "pi_zero"))
  RHO_PLUS_STRONG = (("pi_plus", "pi_zero"),)
  OMEGA_STRONG = (("pi_plus", "pi_minus", "pi_zero"),)

  def test_phi_KK_strong_modes(self) -> None:
    for ds in self.PHI_STRONG:
      self.assertTrue(mc._light_strong_channel_allowed("phi", ds), ds)
    self.assertFalse(mc._light_strong_channel_allowed("phi", ("pi_plus", "pi_minus")))
    self.assertFalse(mc._light_strong_channel_allowed("phi", ("K0", "K0_bar")))

  def test_rho_plus_pipi0_strong(self) -> None:
    self.assertTrue(mc._light_strong_channel_allowed("rho_plus", ("pi_plus", "pi_zero")))
    self.assertFalse(mc._light_strong_channel_allowed("rho_plus", ("pi_zero", "pi_zero")))

  def test_omega_three_pion_strong(self) -> None:
    self.assertTrue(mc._light_strong_channel_allowed("omega_meson", ("pi_plus", "pi_minus", "pi_zero")))
    self.assertFalse(mc._light_strong_channel_allowed("omega_meson", ("pi_plus", "pi_minus")))

  def test_phi_strong_spine_gap_routing(self) -> None:
    kind_kk = mc.open_flavour_contact_kind("phi", "strong", ("K_plus", "K_minus"))
    kind_leak = mc.open_flavour_contact_kind("phi", "strong", ("pi_plus", "pi_minus", "pi_zero"))
    self.assertEqual(kind_kk, "hidden_strangeness_kk_retention")
    self.assertEqual(kind_leak, "hidden_strangeness_vector_leak")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind_kk), 21.0 / 25.0)
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind_leak), 4.0 / 25.0)


class TestKaonWeakCertificateMirror(unittest.TestCase):
  K0_WEAK = (("pi_zero",),)
  K_MINUS_WEAK = (("pi_minus",), ("pi_zero",), ("pi_minus", "pi_zero", "pi_zero"))

  def test_K0_weak_certificate(self) -> None:
    import hqiv_hep_decay_certificates as cert
    import hqiv_hep_patch_species as hps

    parent = hps.patch_from_species_id("K0")
    self.assertEqual(cert.certified_weak_tuples(parent), cert.K0_WEAK)
    for ds in self.K0_WEAK:
      self.assertTrue(mc._light_weak_channel_allowed("K0", ds), ds)
    kind = mc.open_flavour_contact_kind("K0", "weak", ("pi_zero",))
    self.assertEqual(kind, "isospin_half_neutral_hadronic_monogamy_exclusion")

  def test_K_minus_weak_certificate(self) -> None:
    import hqiv_hep_decay_certificates as cert
    import hqiv_hep_patch_species as hps

    parent = hps.patch_from_species_id("K_minus")
    self.assertEqual(cert.certified_weak_tuples(parent), cert.K_MINUS_WEAK)
    for ds in self.K_MINUS_WEAK:
      self.assertTrue(mc._light_weak_channel_allowed("K_minus", ds), ds)
    self.assertEqual(
        mc.open_flavour_contact_kind("K_minus", "weak", ("pi_minus",)),
        "isospin_half_hadronic_semileptonic_competition",
    )
    self.assertEqual(
        mc.open_flavour_contact_kind("K_minus", "weak", ("mu_minus",)),
        "light_kaon_semileptonic_neutrino_completion",
    )


class TestSpineDischargeWeight(unittest.TestCase):
  """Unified product law reconciles with routing kinds on certified rows."""

  def test_K_plus_mu_product(self) -> None:
    import hqiv_spine_discharge_weight as sdw

    w = sdw.spine_discharge_weight("K_plus", "weak", ("mu_plus",))
    kind = mc.open_flavour_contact_kind("K_plus", "weak", ("mu_plus",))
    self.assertAlmostEqual(w, hdr.open_flavour_contact_weight(kind))
    self.assertAlmostEqual(w, 209.0 / 1800.0)
    obs = sdw.discharge_observables("K_plus", "weak", ("mu_plus",))
    self.assertIn("visible_lepton_weak", obs.active_generator_labels())

  def test_K_plus_hadronic_product(self) -> None:
    import hqiv_spine_discharge_weight as sdw

    w = sdw.spine_discharge_weight("K_plus", "weak", ("pi_plus",))
    kind = mc.open_flavour_contact_kind("K_plus", "weak", ("pi_plus",))
    self.assertAlmostEqual(w, hdr.open_flavour_contact_weight(kind))
    self.assertAlmostEqual(w, hdr.isospin_half_hadronic_semileptonic_competition())
    obs = sdw.discharge_observables("K_plus", "weak", ("pi_plus",))
    self.assertEqual(obs.semileptonic_hadronic_competition, 1)

  def test_lambda_plain_isospin_no_monogamy(self) -> None:
    import hqiv_spine_discharge_weight as sdw

    obs = sdw.discharge_observables("lambda", "weak", ("p", "pi_minus"))
    self.assertEqual(obs.monogamy_competition, 0)
    w = sdw.spine_discharge_weight("lambda", "weak", ("p", "pi_minus"))
    self.assertAlmostEqual(w, 7.0 / 5.0)

  def test_phi_hidden_strangeness_product(self) -> None:
    import hqiv_spine_discharge_weight as sdw

    w_kk = sdw.spine_discharge_weight("phi", "strong", ("K_plus", "K_minus"))
    w_leak = sdw.spine_discharge_weight("phi", "strong", ("pi_plus", "pi_minus", "pi_zero"))
    self.assertAlmostEqual(w_kk, 21.0 / 25.0)
    self.assertAlmostEqual(w_leak, 4.0 / 25.0)
    self.assertAlmostEqual(w_kk / (w_kk + w_leak), 0.84, places=2)
    self.assertAlmostEqual(hdr.hidden_strangeness_vector_strong_width_scale(), 4.0 / 25000.0)

  def test_heavy_B0_neutral_spectator(self) -> None:
    import hqiv_spine_discharge_weight as sdw

    w = sdw.spine_discharge_weight("B0", "weak", ("D0", "pi_zero"))
    kind = mc.open_flavour_contact_kind("B0", "weak", ("D0", "pi_zero"))
    self.assertAlmostEqual(w, hdr.open_flavour_contact_weight(kind))
    self.assertAlmostEqual(w, 3.0 / 2.0)


class TestSpineDischargeReconcilesRouting(unittest.TestCase):
  """Product law equals OpenFlavourContactKind weight on routing certificates."""

  ROUTING_ROWS = (
      ("B0", "weak", ("D0", "pi_zero")),
      ("B_plus", "weak", ("D0", "pi_plus")),
      ("lambda_c", "weak", ("p", "K_minus", "pi_plus")),
      ("lambda_c", "weak", ("p", "K_minus", "pi_zero")),
      ("lambda_c", "weak", ("p", "K_plus", "pi_minus")),
      ("xi_c", "weak", ("lambda_c", "pi_plus")),
      ("xi_c", "weak", ("sigma_c", "pi_zero")),
      ("Bs", "weak", ("Ds_plus", "K_minus")),
      ("Bs", "weak", ("phi", "phi")),
      ("K_plus", "weak", ("pi_plus",)),
      ("K_plus", "weak", ("mu_plus",)),
      ("lambda", "weak", ("p", "pi_minus")),
      ("lambda", "weak", ("n", "pi_zero")),
      ("phi", "strong", ("K_plus", "K_minus")),
      ("phi", "strong", ("pi_plus", "pi_minus", "pi_zero")),
  )

  def test_product_matches_routing_kind(self) -> None:
    import hqiv_spine_discharge_weight as sdw

    for parent, channel, ds in self.ROUTING_ROWS:
      kind = mc.open_flavour_contact_kind(parent, channel, ds)
      w_kind = hdr.open_flavour_contact_weight(kind)
      w_prod = sdw.spine_discharge_weight(parent, channel, ds)
      self.assertAlmostEqual(
          w_prod,
          w_kind,
          places=12,
          msg=f"{parent} {channel} {ds} kind={kind}",
      )


class TestSpineGapClosureBranching(unittest.TestCase):
  def test_K_plus_mu_branching_after_gap_closure(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("K_plus"), env=env)
    mu = next(e for e in edges if e.mode.daughter_ids == ("mu_plus",))
    self.assertGreater(mu.branching_ratio, 0.62)
    self.assertLess(mu.branching_ratio, 0.66)

  def test_phi_KK_branching_after_gap_closure(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("phi"), env=env)
    kk = next(
        e
        for e in edges
        if set(e.mode.daughter_ids) == {"K_plus", "K_minus"}
    )
    self.assertAlmostEqual(kk.branching_ratio, 0.84, places=2)


class TestQuarkoniumCascadeCertificates(unittest.TestCase):
  def test_upsilon_neutral_cascade_certificate(self) -> None:
    import hqiv_hep_decay_certificates as cert
    import hqiv_hep_patch_species as hps

    parent = hps.patch_from_species_id("Upsilon")
    tuples = cert.certified_quarkonium_cascade_tuples(parent)
    self.assertEqual(tuples, cert.UPSILON_NEUTRAL_CASCADE)
    for ds in tuples:
      self.assertTrue(mc.strong_neutral_light_cascade(ds), ds)


class TestLeanWeakCertificates(unittest.TestCase):
  """Python finite spanning sets mirror ``HepDecayChannelRouting.lean``."""

  def test_lambda_certified_mode_count(self) -> None:
    import hqiv_hep_decay_certificates as cert
    import hqiv_hep_patch_species as hps

    parent = hps.patch_from_species_id("lambda")
    self.assertIsNotNone(parent)
    tuples = cert.certified_weak_tuples(parent)
    self.assertEqual(tuples, cert.LAMBDA_WEAK)
    self.assertEqual(len(tuples), 2)

  def test_lambda_sparse_enumeration(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("lambda"), env=env)
    weak = [e for e in edges if e.mode.channel == "weak"]
    self.assertEqual(len(weak), 2)
    keys = {tuple(e.mode.daughter_ids) for e in weak}
    self.assertEqual(keys, {("p", "pi_minus"), ("n", "pi_zero")})

  def test_Bs_certified_two_mode_competition(self) -> None:
    import hqiv_hep_decay_certificates as cert
    import hqiv_hep_decay_chain as hep
    import hqiv_hep_multichannel_expansion as mc
    import hqiv_hep_decay_readout as hdr
    import hqiv_hep_patch_species as hps

    parent = hps.patch_from_species_id("Bs")
    self.assertEqual(cert.certified_weak_tuples(parent), cert.BS_WEAK)
    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("Bs"), env=env)
    self.assertEqual(len(edges), 2)
    kinds = {
        e.mode.daughter_ids: mc.open_flavour_contact_kind("Bs", "weak", e.mode.daughter_ids)
        for e in edges
    }
    self.assertEqual(kinds[("Ds_plus", "K_minus")], "bottom_strange_double_monogamy")
    self.assertEqual(kinds[("phi", "phi")], "bottom_strange_double_monogamy")
    self.assertAlmostEqual(
        hdr.open_flavour_contact_weight(kinds[("Ds_plus", "K_minus")]),
        hdr.open_flavour_contact_weight(kinds[("phi", "phi")]),
    )
    dsk = next(e for e in edges if e.mode.daughter_ids == ("Ds_plus", "K_minus"))
    phiphi = next(e for e in edges if e.mode.daughter_ids == ("phi", "phi"))
    self.assertAlmostEqual(dsk.branching_ratio, phiphi.branching_ratio, delta=0.02)
    self.assertGreater(dsk.branching_ratio, 0.45)
    self.assertLess(dsk.branching_ratio, 0.55)

  def test_upsilon_inclusive_jpsi_neutral_cascade(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("Upsilon"), env=env)
    selected = [
        e
        for e in edges
        if e.mode.channel == "strong"
        and "Jpsi" in e.mode.daughter_ids
        and mc.strong_neutral_light_cascade(e.mode.daughter_ids)
    ]
    pred = sum(e.branching_ratio for e in selected)
    self.assertGreater(pred, 0.004)
    self.assertLess(pred, 0.008)


class TestStrongContactRouting(unittest.TestCase):
  def test_Ds_phi_pole_discharge_contact(self) -> None:
    kind = mc.open_flavour_contact_kind("Ds_plus", "strong", ("phi",))
    self.assertEqual(kind, "hidden_strangeness_pole_discharge")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), 8.0 / 5.0)

  def test_Ds_strong_light_pair_ozi_suppressed(self) -> None:
    kind = mc.open_flavour_contact_kind("Ds_plus", "strong", ("pi_plus", "pi_zero"))
    self.assertEqual(kind, "ozi_suppressed_strong")
    self.assertAlmostEqual(hdr.open_flavour_contact_weight(kind), hdr.ozi_suppressed_strong_contact())

  def test_Ds_phi_branching_within_readout_band(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("Ds_plus"), env=env)
    phi = next(e for e in edges if e.mode.daughter_ids == ("phi",))
    self.assertGreater(phi.branching_ratio, 0.25)
    self.assertLess(phi.branching_ratio, 0.55)


class TestLightWeakDischarge(unittest.TestCase):
  def test_inside_outside_curvature_ratio_proton_anchor(self) -> None:
    m_p = 938.272
    self.assertAlmostEqual(
      hdr.light_inside_outside_curvature_ratio(m_p, m_p),
      1.0,
    )
    m_k = 486.0
    io = hdr.light_inside_outside_curvature_ratio(m_k, m_p)
    self.assertGreater(io, 1.0)

  def test_hadronic_coupling_exceeds_semileptonic_at_kaon_mass(self) -> None:
    m_p = 938.272
    m_k = 486.0
    h = hdr.light_hadronic_outside_discharge_coupling(m_k, m_p)
    l = hdr.light_semileptonic_inside_discharge_coupling(m_k, m_p)
    self.assertGreater(h, l)

  def test_Kplus_mu_branching_closer_to_pdg(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("K_plus"), env=env)
    mu = next(e for e in edges if e.mode.daughter_ids == ("mu_plus",))
    self.assertGreater(mu.branching_ratio, 0.62)
    self.assertLess(mu.branching_ratio, 0.66)
    # Shared pole width across weak outlets.
    widths = {tuple(d.species_id for d in e.daughters): e.width_per_s for e in edges if e.mode.channel == "weak"}
    self.assertEqual(len(set(widths.values())), 1)

  def test_collider_raises_light_width_more_than_heavy(self) -> None:
    import hqiv_hep_decay_chain as hep

    lab = hep.ExperimentEnvironment()
    coll = hep.ExperimentEnvironment(magnetic_field_tesla=4.0, collider_reference_tesla=4.0)
    w_k_lab = hep._light_weak_discharge_width_per_s(hep.build_particle("K_plus"), env=lab)
    w_k_col = hep._light_weak_discharge_width_per_s(hep.build_particle("K_plus"), env=coll)
    w_b_lab = hep._hadronic_weak_width_per_s(
      hep.build_particle("B_plus"),
      (hep.build_particle("D0"), hep.build_particle("pi_plus")),
      env=lab,
    )
    w_b_col = hep._hadronic_weak_width_per_s(
      hep.build_particle("B_plus"),
      (hep.build_particle("D0"), hep.build_particle("pi_plus")),
      env=coll,
    )
    k_boost = w_k_col / w_k_lab
    b_boost = w_b_col / w_b_lab
    self.assertGreater(k_boost, b_boost)

  def test_Kplus_lifetime_near_pdg(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("K_plus"), env=env)
    widths = [e.width_per_s for e in edges if e.mode.channel == "weak"]
    self.assertEqual(len(set(widths)), 1)
    half_life_ns = next(
        e.half_life_s for e in edges if e.mode.channel == "weak"
    ) * 1e9
    self.assertGreater(half_life_ns, 10.0)
    self.assertLess(half_life_ns, 16.0)

  def test_lambda_branching_p_pi_near_pdg(self) -> None:
    import hqiv_hep_decay_chain as hep

    env = hep.ExperimentEnvironment()
    edges = hep.edges_from_particle(hep.build_particle("lambda"), env=env)
    p_pi = next(e for e in edges if e.mode.daughter_ids == ("p", "pi_minus"))
    n_pi0 = next(e for e in edges if e.mode.daughter_ids == ("n", "pi_zero"))
    self.assertGreater(p_pi.branching_ratio, 0.60)
    self.assertLess(p_pi.branching_ratio, 0.70)
    self.assertGreater(n_pi0.branching_ratio, 0.30)
    self.assertLess(n_pi0.branching_ratio, 0.40)


if __name__ == "__main__":
  unittest.main()
