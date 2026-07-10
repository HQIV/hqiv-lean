#!/usr/bin/env python3
"""Tests: protein–solvent interface f_LDL dress and mixture material response."""

import unittest

import hqiv_phase_material_response as pmr
from hqiv_lab.protein_solvent_phase import (
    PROTEIN_FOLDING_TEMPERATURE_K,
    aqueous_mixture_curvature_at_interface,
    bulk_low_density_fraction,
    interface_exposure_from_contact_kind,
    local_low_density_fraction_at_interface,
)
from hqiv_lab.spec import resolve_spec


class TestProteinInterfaceLDL(unittest.TestCase):
    def test_hydrophobic_boosts_f_ldl(self) -> None:
        f_bulk = 0.4
        f_hydro = local_low_density_fraction_at_interface(f_bulk, "hydrophobic")
        f_neutral = local_low_density_fraction_at_interface(f_bulk, "neutral")
        self.assertGreater(f_hydro, f_neutral)
        self.assertAlmostEqual(f_neutral, f_bulk)

    def test_hydrophilic_reduces_f_ldl(self) -> None:
        f_bulk = 0.4
        f_phil = local_low_density_fraction_at_interface(f_bulk, "hydrophilic")
        self.assertLess(f_phil, f_bulk)

    def test_hydrophobic_interface_rho_at_fold(self) -> None:
        rho_hydro = aqueous_mixture_curvature_at_interface(
            PROTEIN_FOLDING_TEMPERATURE_K, "hydrophobic"
        )
        rho_phil = aqueous_mixture_curvature_at_interface(
            PROTEIN_FOLDING_TEMPERATURE_K, "hydrophilic"
        )
        rho_neutral = aqueous_mixture_curvature_at_interface(
            PROTEIN_FOLDING_TEMPERATURE_K, "neutral"
        )
        # LDL-like dress lowers ρ_curv; hydrophilic stays on HDL branch at cytosolic T.
        self.assertLess(rho_hydro, rho_neutral)
        self.assertAlmostEqual(rho_neutral, rho_phil, places=5)
        self.assertAlmostEqual(rho_neutral, 1.0, places=5)

    def test_supercooled_metastable_interface_bias(self) -> None:
        import hqiv_thermodynamic_phase_from_tp as tptp

        p = 1250.0 * tptp.STP_PRESSURE_PA
        f_bulk = bulk_low_density_fraction(200.0, p)
        self.assertGreater(f_bulk, 0.0)
        f_hydro = local_low_density_fraction_at_interface(f_bulk, "hydrophobic")
        self.assertGreater(f_hydro, f_bulk)

    def test_cytosol_bulk_f_ldl_zero(self) -> None:
        self.assertEqual(bulk_low_density_fraction(PROTEIN_FOLDING_TEMPERATURE_K), 0.0)

    def test_contact_kind_exposure_map(self) -> None:
        self.assertEqual(interface_exposure_from_contact_kind("hydrophobic"), "hydrophobic")
        self.assertEqual(interface_exposure_from_contact_kind("helix_sheet"), "hydrophilic")

    def test_hoh_pivot_dress_hydrophobic_at_fold(self) -> None:
        from hqiv_lab.peptide_shell_dress import aqueous_hbond_pivot_shell_factor
        from hqiv_lab.protein_solvent_phase import (
            aqueous_angle_pivot_dress_factor,
            aqueous_bulk_pivot_at_contact,
            aqueous_hbond_pivot_at_interface,
            bulk_low_density_fraction,
            local_low_density_fraction_at_interface,
        )

        f_bulk = bulk_low_density_fraction(PROTEIN_FOLDING_TEMPERATURE_K)
        self.assertEqual(f_bulk, 0.0)
        f_hydro = local_low_density_fraction_at_interface(f_bulk, "hydrophobic")
        self.assertGreater(f_hydro, f_bulk)
        dress = aqueous_angle_pivot_dress_factor(
            PROTEIN_FOLDING_TEMPERATURE_K, "hydrophobic"
        )
        shell = aqueous_hbond_pivot_shell_factor()
        # dress = (θ_mix/θ_gas) × shell; pivot Å uses angle factor only.
        self.assertGreater(dress / shell, 1.0)
        pivot = aqueous_hbond_pivot_at_interface(f_hydro)
        self.assertAlmostEqual(pivot, 2.8 * (dress / shell), places=4)
        self.assertAlmostEqual(
            aqueous_bulk_pivot_at_contact(
                "hydrophobic", temperature_k=PROTEIN_FOLDING_TEMPERATURE_K
            ),
            pivot,
            places=4,
        )

    def test_hoh_pivot_dress_unity_on_hydrophilic_fold(self) -> None:
        from hqiv_lab.peptide_shell_dress import aqueous_hbond_pivot_shell_factor
        from hqiv_lab.protein_solvent_phase import aqueous_angle_pivot_dress_factor

        dress = aqueous_angle_pivot_dress_factor(
            PROTEIN_FOLDING_TEMPERATURE_K, "hydrophilic"
        )
        # Hydrophilic fold: θ_mix = θ_gas ⇒ angle factor 1; shell factor remains.
        self.assertAlmostEqual(dress, aqueous_hbond_pivot_shell_factor(), places=5)


class TestMaterialResponseMixture(unittest.TestCase):
    def test_mixture_endpoints(self) -> None:
        out_ldl = pmr.material_response_mixture_readout("H2O", 1.0, temperature_k=273.15)
        out_hdl = pmr.material_response_mixture_readout("H2O", 0.0, temperature_k=273.15)
        self.assertAlmostEqual(
            out_ldl["refractive_index"],
            out_ldl["low_density_branch"]["refractive_index"],
            places=5,
        )
        self.assertAlmostEqual(
            out_hdl["refractive_index"],
            out_hdl["high_density_branch"]["refractive_index"],
            places=5,
        )
        self.assertLess(out_ldl["refractive_index"], out_hdl["refractive_index"])

    def test_mixture_interpolates(self) -> None:
        out = pmr.material_response_mixture_readout("H2O", 0.5, temperature_k=273.15)
        lo = out["low_density_branch"]["thermal_conductivity_W_mK"]
        hi = out["high_density_branch"]["thermal_conductivity_W_mK"]
        self.assertGreater(out["thermal_conductivity_W_mK"], min(lo, hi))
        self.assertLess(out["thermal_conductivity_W_mK"], max(lo, hi))


if __name__ == "__main__":
    unittest.main()
