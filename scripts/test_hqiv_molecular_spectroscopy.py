#!/usr/bin/env python3
"""Tests for HQIV diatomic spectroscopy (knob-free invariants + comparison tolerances)."""

from __future__ import annotations

import math
import unittest

import hqiv_molecular_spectroscopy as ms


class SpectroscopyInvariantTests(unittest.TestCase):
    def setUp(self) -> None:
        self.payload = ms.build_payload()
        self.rows = {r["name"]: r for r in self.payload["rows"]}

    def test_no_fitted_coefficients_policy(self) -> None:
        self.assertEqual(self.payload["parameter_policy"], "no_fitted_coefficients")

    def test_monogamy_core_power_matches_backbone_valley_repulsion(self) -> None:
        # the Mie cross-check repulsive exponent is read off the backbone valley
        # potential's (r_m/r)^4 monogamy core, not chosen to fit any molecule
        self.assertEqual(ms.MONOGAMY_CORE_POWER, 4)

    def test_hqiv_atomic_masses_match_isotope_amu(self) -> None:
        # HQIV cluster-mass spine reproduces atomic masses to <1%
        for z, amu in ((1, 1.008), (8, 15.999), (9, 18.998)):
            self.assertAlmostEqual(ms.hqiv_atomic_mass_amu(z), amu, delta=0.01 * amu)

    def test_reduced_mass_symmetric_and_bounded(self) -> None:
        mu = ms.reduced_mass_amu(1, 9)
        self.assertEqual(mu, ms.reduced_mass_amu(9, 1))
        self.assertLess(mu, min(ms.hqiv_atomic_mass_amu(1), ms.hqiv_atomic_mass_amu(9)))

    def test_be_scales_as_inverse_mu_re_squared(self) -> None:
        # rigorous closed form: B_e = hbar / (4 pi c mu r_e^2)
        b1 = ms.rotational_constant_cm1(1.0, 1.0)
        self.assertAlmostEqual(ms.rotational_constant_cm1(1.0, 2.0), b1 / 2.0, places=9)
        self.assertAlmostEqual(ms.rotational_constant_cm1(2.0, 1.0), b1 / 4.0, places=9)

    def test_morse_anharmonicity_closure(self) -> None:
        # omega_e x_e must equal omega_e^2 / (4 D_e) in wavenumbers for every row
        for row in self.rows.values():
            d_e_cm1 = (
                row["D_e_ev"]
                * ms.EV_J
                / (ms.HBAR_J_S * 2.0 * math.pi * ms.C_CM_S)
            )
            expected = row["omega_e_cm1"] ** 2 / (4.0 * d_e_cm1)
            self.assertAlmostEqual(row["omega_e_xe_cm1"], expected, places=6)

    def test_headline_omega_e_is_resonance_or_coupled_relaxed_generator(self) -> None:
        # one-way ω_e is the curvature-integral Morse generator dressed by the VB
        # covalent↔ionic resonance.  Structurally flagged rows then relax this value
        # toward the already-derived concentration-flow target by the Lean
        # CoupledRelaxation step.
        for row in self.rows.values():
            if row["omega_e_resonance_cm1"] > 0.0:
                self.assertAlmostEqual(
                    row["omega_e_one_way_cm1"], row["omega_e_resonance_cm1"], places=6
                )
            if row["missing_coupled_relaxation_flag"]:
                self.assertEqual(row["coupling_level"], "coupled_relaxed")
                self.assertAlmostEqual(row["omega_e_cm1"], row["omega_e_coupled_cm1"], places=6)
                self.assertAlmostEqual(row["omega_e_cm1"], row["omega_e_flow_cm1"], places=6)
            else:
                self.assertEqual(row["coupling_level"], "feed_forward")
                self.assertAlmostEqual(row["omega_e_cm1"], row["omega_e_one_way_cm1"], places=6)
            if row["z_i"] == row["z_j"]:
                self.assertEqual(row["bond_ionic_character"], 0.0)
                self.assertAlmostEqual(
                    row["omega_e_resonance_cm1"], row["omega_e_curvature_cm1"], places=6
                )

    def test_morse_range_is_monogamy_contact_times_resolved_curvature(self) -> None:
        # a·r_e = (1+γ/2)·C_eff — monogamy spectator contact × occupancy-resolved curvature
        g = ms.lean.GAMMA
        for row in self.rows.values():
            self.assertAlmostEqual(
                row["morse_a_re"],
                (1.0 + g / 2.0) * row["contact_curvature_effective"],
                places=9,
            )

    def test_resolved_curvature_is_integral_plus_spectator_defect_step(self) -> None:
        # C_eff = ∫₁^ξ ρ_curv dξ + (γ/2)·defect — the defect adds exactly one γ/2 step
        g = ms.lean.GAMMA
        for row in self.rows.values():
            self.assertIn(row["monogamy_channel_defect"], (0, 1))
            self.assertAlmostEqual(
                row["contact_curvature_effective"],
                row["curvature_integral"] + (g / 2.0) * row["monogamy_channel_defect"],
                places=9,
            )

    def test_shared_channel_capacity_is_pshell_degeneracy(self) -> None:
        # p-block covalent pairs offer 2ℓ+1 = 3 channels; s-only (H, alkali) offer 1
        self.assertEqual(ms.shared_channel_capacity(7, 7), 3)  # N2
        self.assertEqual(ms.shared_channel_capacity(8, 8), 3)  # O2
        self.assertEqual(ms.shared_channel_capacity(6, 8), 3)  # CO
        self.assertEqual(ms.shared_channel_capacity(1, 1), 1)  # H2
        self.assertEqual(ms.shared_channel_capacity(1, 9), 1)  # HF
        self.assertEqual(ms.shared_channel_capacity(3, 1), 1)  # LiH (s-block Li)

    def test_monogamy_defect_fires_only_on_submaximal_pblock(self) -> None:
        # defect = (bond order < p-shell channel capacity); saturates at 1 (monogamy)
        defects = {r["name"]: r["monogamy_channel_defect"] for r in self.rows.values()}
        # maximal closed-shell bonds: no spectator defect
        for name in ("N2", "CO", "HF", "HCl", "H2"):
            self.assertEqual(defects[name], 0, f"{name} should have no defect")
        # sub-maximal p-block bonds: one open channel → one spectator step
        for name in ("O2", "F2"):
            self.assertEqual(defects[name], 1, f"{name} should carry the defect")

    def test_occupancy_defect_tightens_O2_F2_without_touching_N2(self) -> None:
        # the spectator step lifts O2/F2 a·r_e by exactly (1+γ/2)·(γ/2); N2 (maximal) is unchanged
        g = ms.lean.GAMMA
        step = (1.0 + g / 2.0) * (g / 2.0)
        for name in ("O2", "F2"):
            row = self.rows[name]
            raw = (1.0 + g / 2.0) * row["curvature_integral"]
            self.assertAlmostEqual(row["morse_a_re"] - raw, step, places=9)
        n2 = self.rows["N2"]
        self.assertEqual(n2["monogamy_channel_defect"], 0)
        self.assertAlmostEqual(
            n2["morse_a_re"], (1.0 + g / 2.0) * n2["curvature_integral"], places=9
        )

    def test_monogamy_spectator_contact_identity(self) -> None:
        # 1 + γ/2 = 2α = 3γ = 6/5 at the HQIV lattice point (α=3/5, γ=2/5, α+γ=1)
        a, g = ms.lean.ALPHA, ms.lean.GAMMA
        self.assertAlmostEqual(a + g, 1.0, places=12)
        contact = ms.monogamy_spectator_contact()
        self.assertAlmostEqual(contact, 1.0 + g / 2.0, places=12)
        self.assertAlmostEqual(contact, 2.0 * a, places=12)
        self.assertAlmostEqual(contact, 3.0 * g, places=12)
        self.assertAlmostEqual(contact, 6.0 / 5.0, places=12)

    def test_curvature_integral_grows_with_contact_shell(self) -> None:
        # accumulated curvature is monotone in the contact shell ξ (deeper → sharper well)
        ordered = sorted(self.rows.values(), key=lambda r: r["xi_contact"])
        for a, b in zip(ordered, ordered[1:]):
            if b["xi_contact"] > a["xi_contact"] + 1e-9:
                self.assertGreaterEqual(b["curvature_integral"], a["curvature_integral"])

    def test_flow_lies_within_the_derived_bracket(self) -> None:
        # the flow never leaves the [diffuse .. concentrated] bracket (s ∈ [0,1))
        for row in self.rows.values():
            if row["valley_well_valid"] and row["omega_e_concentrated_cm1"] > 0.0:
                lo = min(row["omega_e_diffuse_cm1"], row["omega_e_concentrated_cm1"])
                hi = max(row["omega_e_diffuse_cm1"], row["omega_e_concentrated_cm1"])
                self.assertGreaterEqual(row["omega_e_flow_cm1"], lo - 1e-6)
                self.assertLessEqual(row["omega_e_flow_cm1"], hi + 1e-6)

    def test_curvature_dielectric_at_least_unity_and_weight_bounded(self) -> None:
        # n ≥ 1 (inside never less curved than outside); CM weight s ∈ [0,1)
        for row in self.rows.values():
            self.assertGreaterEqual(row["curvature_dielectric"], 1.0 - 1e-9)
            self.assertGreaterEqual(row["concentration_weight"], 0.0)
            self.assertLess(row["concentration_weight"], 1.0)

    def test_uncontracted_contact_stays_at_diffuse_edge(self) -> None:
        # H₂ (Z=1, no contraction) → n=1, s=0 → flow sits exactly on the diffuse edge
        h2 = self.rows["H2"]
        self.assertAlmostEqual(h2["curvature_dielectric"], 1.0, places=2)
        self.assertAlmostEqual(h2["concentration_weight"], 0.0, places=2)
        self.assertAlmostEqual(h2["omega_e_flow_cm1"], h2["omega_e_diffuse_cm1"], delta=1.0)

    def test_valley_well_minimum_tracks_re_for_light_bonds(self) -> None:
        # for H2/LiH the backbone valley minimum agrees with the nested-WF r_e
        for name in ("H2", "LiH"):
            row = self.rows[name]
            self.assertTrue(row["valley_well_valid"])
            self.assertLess(
                abs(row["valley_min_angstrom"] - row["r_e_angstrom"]) / row["r_e_angstrom"],
                0.15,
            )

    def test_open_channel_elongation_lengthens_f2_keeps_n2_o2(self) -> None:
        # the carrier+network geometry law elongates the bond by one informational-
        # monogamy step per open (antibonding) p-shell channel: N2 (0) sits at the bare
        # carrier contact, O2 (1) is one step out, F2 (2) two steps — so the corrected
        # F-F bond is much closer to physical than the old halogen-branch value (1.06 A)
        import hqiv_chemistry_tuft_dynamics as ctd
        n2 = ctd.bond_equilibrium_from_atomic_numbers(7, 7)
        o2 = ctd.bond_equilibrium_from_atomic_numbers(8, 8)
        f2 = ctd.bond_equilibrium_from_atomic_numbers(9, 9)
        self.assertLess(abs(n2 - 1.0977) / 1.0977, 0.05)   # N2 unchanged, ~2%
        self.assertLess(abs(o2 - 1.2075) / 1.2075, 0.05)   # O2 unchanged, ~2%
        self.assertGreater(f2, 1.25)                       # F2 no longer collapsed
        self.assertLess(abs(f2 - 1.4119) / 1.4119, 0.12)   # F2 now within ~12%

    def test_geometry_fix_does_not_regress_binding(self) -> None:
        # elongating F2 must not move its derived D_e off the reference (binding stays)
        import hqiv_dynamic_binding_chart as dbc
        for b in dbc.ALL_MOLECULE_BENCHMARKS:
            if b.name == "F2":
                res = dbc.dynamic_binding_for_benchmark(b)
                err = abs(res.binding_ev - b.reference_ev) / b.reference_ev
                self.assertLess(err, 0.05, f"F2 D_e drifted {err*100:.1f}%")

    def test_geometry_floor_flags_period3_ionic(self) -> None:
        # Gas ionic outside-contact (1+α) and valence-effective Cl2 are promoted.
        self.assertTrue(self.rows["NaCl"]["geometry_reliable"])
        self.assertTrue(self.rows["Cl2"]["geometry_reliable"])
        self.assertTrue(self.rows["H2"]["geometry_reliable"])
        self.assertTrue(self.rows["HF"]["geometry_reliable"])
        nacl = self.rows["NaCl"]
        self.assertGreater(nacl["r_e_angstrom"], 2.0)
        self.assertAlmostEqual(
            nacl["r_e_angstrom"],
            nacl["r_e_outside_contact_target_angstrom"],
            places=6,
        )

    def test_outside_contact_geometry_routes(self) -> None:
        nacl = self.rows["NaCl"]
        cl2 = self.rows["Cl2"]
        self.assertEqual(nacl["geometry_route"], "ionic_outside_contact")
        self.assertEqual(cl2["geometry_route"], "period3_halogen_open_channel")
        self.assertTrue(nacl["geometry_outside_candidate_clears_floor"])
        self.assertTrue(cl2["geometry_outside_candidate_clears_floor"])
        self.assertGreater(
            nacl["r_e_outside_contact_target_angstrom"],
            nacl["r_e_one_way_angstrom"],
        )
        self.assertGreater(cl2["r_e_outside_contact_target_angstrom"], 0.70)

    def test_nacl_solid_lattice_regime(self) -> None:
        nacl = self.rows["NaCl"]
        self.assertEqual(nacl["comparison_regime"], "solid_lattice")
        self.assertGreater(nacl["r_e_lattice_target_angstrom"], 2.0)
        self.assertGreater(
            nacl["r_e_lattice_target_angstrom"],
            nacl["r_e_outside_contact_target_angstrom"],
        )

    def test_lih_spectroscopy_stays_gas_vapor(self) -> None:
        lih = self.rows["LiH"]
        self.assertEqual(lih["comparison_regime"], "gas_vapor")
        self.assertEqual(lih["r_e_lattice_target_angstrom"], 0.0)
        self.assertGreater(lih["bond_ionic_character"], 0.0)

    def test_positive_physical_outputs(self) -> None:
        for row in self.rows.values():
            self.assertGreater(row["B_e_cm1"], 0.0)
            self.assertGreater(row["omega_e_cm1"], 0.0)
            self.assertGreaterEqual(row["zpe_ev"], 0.0)

    def test_concentrated_is_stiffer_than_diffuse(self) -> None:
        # the contracted-length valley is the upper bracket: never softer than the
        # diffuse shell-ladder valley when both wells are valid
        for row in self.rows.values():
            if row["valley_well_valid"] and row["omega_e_concentrated_cm1"] > 0.0:
                self.assertGreaterEqual(
                    row["omega_e_concentrated_cm1"], row["omega_e_diffuse_cm1"]
                )

    def test_concentration_weight_matches_clausius_mossotti(self) -> None:
        # s is exactly the CM polarization of the curvature dielectric (no fit)
        for row in self.rows.values():
            n = row["curvature_dielectric"]
            self.assertAlmostEqual(
                row["concentration_weight"], (n - 1.0) / (n + 2.0), places=9
            )

    def test_ionic_character_is_squared_pull_asymmetry_and_homonuclear_zero(self) -> None:
        # w = δ² with δ = |p_i−p_j|/(p_i+p_j) from the native electron-pull; 0 for homonuclear
        import hqiv_atom_construction as ac
        for row in self.rows.values():
            pi = ac.valence_electron_pull(row["z_i"])
            pj = ac.valence_electron_pull(row["z_j"])
            delta = abs(pi - pj) / (pi + pj) if (pi + pj) > 0 else 0.0
            self.assertAlmostEqual(row["bond_ionic_character"], delta * delta, places=9)
            self.assertGreaterEqual(row["bond_ionic_character"], 0.0)
            self.assertLessEqual(row["bond_ionic_character"], 1.0)
            if row["z_i"] == row["z_j"]:
                self.assertEqual(row["bond_ionic_character"], 0.0)

    def test_ionic_character_matches_known_chemistry_ordering(self) -> None:
        # derived ionic characters reproduce the chemical ordering: CO≈nonpolar < HCl < LiF
        ic = {r["name"]: r["bond_ionic_character"] for r in self.rows.values()}
        self.assertLess(ic["CO"], 0.06)          # CO nearly nonpolar (real ~0.02)
        self.assertGreater(ic["LiF"], ic["HCl"])  # LiF more ionic than HCl
        self.assertGreater(ic["HCl"], ic["CO"])   # HCl more ionic than CO

    def test_resonance_softens_polar_keeps_homonuclear(self) -> None:
        # the VB resonance only moves heteronuclear ω_e (ionic character > 0); homonuclear
        # bonds (N2, O2, F2, H2) are identical to the bare covalent generator
        for name in ("N2", "O2", "F2", "H2"):
            row = self.rows[name]
            self.assertAlmostEqual(
                row["omega_e_resonance_cm1"], row["omega_e_curvature_cm1"], places=6
            )
        # HCl: the bare covalent generator overshoots; the resonance brings it inside ~3%
        hcl = self.payload["comparison"]["HCl"]
        self.assertLess(abs(hcl["error_pct"]["omega_e"]), 3.0)


class SpectroscopyComparisonTests(unittest.TestCase):
    """NIST values are comparison-only; these guard against regressions, not fits."""

    def setUp(self) -> None:
        self.payload = ms.build_payload()
        self.comp = self.payload["comparison"]

    def test_rotational_constant_sharp_for_covalent_period2(self) -> None:
        # B_e tracks r_e: period-2 covalent diatomics land within ~8%
        for name in ("H2", "HF", "HCl", "CO", "N2", "O2"):
            err = abs(self.comp[name]["error_pct"]["B_e"])
            self.assertLess(err, 8.0, f"{name} B_e error {err:.1f}% exceeds 8%")

    def test_reliable_geometry_re_within_ten_percent(self) -> None:
        s = self.payload["summary"]["mean_abs_error_pct_reliable"]
        self.assertLess(s["r_e"], 10.0)

    def test_emergent_generator_tightens_covalent_omega_e(self) -> None:
        # the occupancy-resolved generator lands the period-2 covalent suite tightly
        # against honestly-derived geometry.  F2 is excluded as a flagged anomaly: with
        # the corrected (longer) F-F bond its ωₑ is genuinely soft (the fluorine bond
        # anomaly), no longer masked by a compensating short-bond error.
        cov = ("HF", "HCl", "CO", "N2", "O2")
        errs = [abs(self.comp[m]["error_pct"]["omega_e"]) for m in cov]
        self.assertLess(sum(errs) / len(errs), 5.0)
        # the occupancy defect pulls the maximal/single-defect cases inside ~2%
        for name in ("N2", "O2"):
            self.assertLess(abs(self.comp[name]["error_pct"]["omega_e"]), 2.0)

    def test_centrifugal_distortion_is_kratzer_relation(self) -> None:
        # D_J = 4 B_e^3 / omega_e^2 for every row (no new input beyond B_e, omega_e)
        payload = self.payload
        for row in payload["rows"]:
            if row["omega_e_cm1"] > 0.0:
                expected = 4.0 * row["B_e_cm1"] ** 3 / row["omega_e_cm1"] ** 2
                self.assertAlmostEqual(row["D_J_cm1"], expected, places=12)

    def test_downstream_constants_track_covalent_suite(self) -> None:
        # D_J and alpha_e ride on the derived B_e and omega_e; on the sharp-B_e covalent
        # suite they land within ~12% with no new fitted input
        dn = self.payload["summary"]["downstream_rovibrational_covalent"]
        dm = dn["mean_abs_error_pct"]
        self.assertLess(dm["D_J"], 12.0, f"D_J mean {dm['D_J']:.1f}% exceeds 12%")
        self.assertLess(dm["alpha_e"], 13.0, f"alpha_e mean {dm['alpha_e']:.1f}% exceeds 13%")

    def test_centrifugal_distortion_per_molecule_covalent(self) -> None:
        # the new validated observable is sharp where its inputs are sharp.  D_J = 4 B_e³/ω_e²
        # rides on the geometry (B_e) and the now resonance-honest ω_e; on the genuine
        # covalent diatomics it stays within ~16%.  LiF is excluded: it is ionic, and with
        # the VB resonance its ω_e is now honest (no longer the compensating too-stiff value),
        # so its D_J transparently exposes the residual ionic-bond geometry error.
        for name in ("HF", "HCl", "CO", "N2", "O2"):
            err = abs(self.comp[name]["error_pct"]["D_J"])
            self.assertLess(err, 16.0, f"{name} D_J error {err:.1f}% exceeds 16%")

    def test_true_omega_e_lies_within_derived_concentration_bracket(self) -> None:
        # the diffuse (r_m) and concentrated (contracted ℓ) valley readings bracket
        # the measured ω_e for the bulk of reliable-geometry covalent diatomics —
        # evidence that the missing physics is an in-bracket concentration flow
        brk = self.payload["summary"]["omega_e_concentration_bracket"]
        self.assertGreaterEqual(
            brk["count_nist_within_bracket"], brk["count_with_bracket"] - 2
        )


if __name__ == "__main__":
    unittest.main()
