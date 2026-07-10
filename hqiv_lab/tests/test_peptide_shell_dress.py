"""Peptide shell-equation dress parity with chemistry packing language."""

from __future__ import annotations

import math
import unittest

from hqiv_lab.derived_bond_geometry import (
    peptide_bond_length_c_n,
    peptide_bond_length_c_o,
    peptide_bond_length_ca_c,
    peptide_bond_length_n_ca,
)
from hqiv_lab.peptide_shell_dress import (
    PEPTIDE_BOND_SLOTS,
    REGISTER_OCCUPANCY,
    aqueous_hbond_pivot_shell_factor,
    peptide_bond_dress,
    peptide_shell_dress_manifest,
    tertiary_contact_packing_scale,
)


class TestPeptideShellDress(unittest.TestCase):
    def test_backbone_length_scales_near_identity(self) -> None:
        for slot in PEPTIDE_BOND_SLOTS:
            aq = peptide_bond_dress(slot, environment="aqueous").length_scale
            gas = peptide_bond_dress(slot, environment="gas").length_scale
            self.assertGreater(aq, 0.99)
            self.assertLess(aq, 1.02)  # thermal only in aqueous
            self.assertGreater(gas, 1.0)
            self.assertLess(gas, 1.05)

    def test_dressed_bonds_positive(self) -> None:
        for r in (
            peptide_bond_length_n_ca(),
            peptide_bond_length_ca_c(),
            peptide_bond_length_c_n(),
            peptide_bond_length_c_o(),
        ):
            self.assertGreater(r, 1.0)
            self.assertLess(r, 2.0)

    def test_hydrophobic_more_open_than_helix(self) -> None:
        self.assertGreater(
            tertiary_contact_packing_scale("hydrophobic"),
            tertiary_contact_packing_scale("helix_i4"),
        )
        self.assertGreater(REGISTER_OCCUPANCY["helix_i4"], REGISTER_OCCUPANCY["hydrophobic"])

    def test_hbond_pivot_near_identity(self) -> None:
        f = aqueous_hbond_pivot_shell_factor()
        self.assertTrue(math.isfinite(f))
        self.assertGreater(f, 0.99)
        self.assertLess(f, 1.05)

    def test_manifest_keys(self) -> None:
        m = peptide_shell_dress_manifest(environment="aqueous")
        self.assertIn("backbone_bonds", m)
        self.assertIn("tertiary_registers", m)
        self.assertIn("aqueous_hbond", m)
        self.assertIn("aqueous_outside_geometry", m)
        self.assertEqual(m["environment"], "aqueous")
        gas = peptide_shell_dress_manifest(environment="gas")
        self.assertIsNone(gas["aqueous_outside_geometry"])

    def test_aqueous_outside_contracts_vs_gas_identity(self) -> None:
        from hqiv_lab.protein_solvent_phase import aqueous_outside_geometry_scale

        aq = aqueous_outside_geometry_scale(contact_kind="hydrophobic")
        self.assertLess(aq["scale"], 1.0)  # foldXi bulk target < 1 at cytosol T
        self.assertGreater(aq["phase_contact_weight"], 0.9)  # near-full aqueous medium
        self.assertEqual(aq["thermal_channel"], "piezo_stiffness")
        self.assertGreater(aq["thermal"], 1.03)  # Lindemann-seeded > legacy γ/16
        self.assertAlmostEqual(aq["optical_length"], 1.0, places=5)  # not on Cα nn
        self.assertGreater(aq["carrier_thermo"], 0.99)  # reported, not on length
        gasish = aqueous_outside_geometry_scale(
            temperature_k=310.15, exposure="neutral"
        )
        # Neutral hydrophilic liquid branch → ρ=1, bulk_target≈0.835
        self.assertLess(gasish["bulk"], 0.9)

    def test_lindemann_hydrophobic_softer_than_peptide(self) -> None:
        from hqiv_lab.protein_solvent_phase import lindemann_peptide_contact_scale

        hydro = lindemann_peptide_contact_scale(310.15, contact_kind="hydrophobic")
        helix = lindemann_peptide_contact_scale(310.15, contact_kind="helix_i4")
        self.assertGreater(hydro, helix)  # apolar open on hydrophobic

    def test_piezo_stiffness_zero_stress_matches_lindemann(self) -> None:
        from hqiv_lab.packing import lindemann_contact_scale
        from hqiv_lab.coordination import IntermolecularMotif

        base = lindemann_contact_scale(
            310.15, 273.15, motif=IntermolecularMotif.PEPTIDE_LAYER
        )
        stressed0 = lindemann_contact_scale(
            310.15,
            273.15,
            motif=IntermolecularMotif.PEPTIDE_LAYER,
            stress_pa=0.0,
            r0_angstrom=5.4,
            binding_ev=0.4,
        )
        self.assertAlmostEqual(base, stressed0, places=9)

    def test_open_period_fade_identity_on_period2(self) -> None:
        from hqiv_lab.peptide_shell_dress import (
            open_channel_period_fade,
            register_period_channel_weight,
            tertiary_contact_packing_scale,
        )

        w_c = register_period_channel_weight("hydrophobic")
        self.assertAlmostEqual(w_c, 1.0, places=9)
        open_bare = 1.098
        self.assertAlmostEqual(open_channel_period_fade(open_bare, w_c), open_bare, places=9)
        # Sulfur period-3 fades open continuously (no hard gate).
        faded = tertiary_contact_packing_scale("hydrophobic", period_z=16)
        full = tertiary_contact_packing_scale("hydrophobic", period_z=6)
        self.assertLess(faded, full)
        self.assertGreater(faded, 1.0)

    def test_optical_acceptor_softens_energy_not_length(self) -> None:
        from hqiv_lab.peptide_shell_dress import tertiary_contact_energy_weight
        from hqiv_lab.protein_solvent_phase import aqueous_outside_geometry_scale

        helix = aqueous_outside_geometry_scale(contact_kind="helix_i4")
        hydro = aqueous_outside_geometry_scale(contact_kind="hydrophobic")
        self.assertGreater(helix["acceptor_excess"], 0.5)
        self.assertLess(helix["acceptor_softener"], 1.0)
        self.assertAlmostEqual(helix["optical_length"], 1.0, places=5)
        self.assertAlmostEqual(hydro["acceptor_excess"], 0.0, places=5)
        self.assertGreater(helix["carrier_thermo"], 1.0)
        self.assertAlmostEqual(hydro["carrier_thermo"], 1.0, places=5)
        # Energy weight carries softener × thermo × register piezo; hydrophobic
        # gets more thermal compliance than filled helix (higher cage).
        e_helix = tertiary_contact_energy_weight("helix_i4")
        e_hydro = tertiary_contact_energy_weight("hydrophobic")
        self.assertLess(e_helix / helix["acceptor_softener"], e_hydro * 2.0)
        self.assertAlmostEqual(hydro["acceptor_softener"], 1.0, places=5)

    def test_register_piezo_identity_at_zero_temp(self) -> None:
        from hqiv_lab.peptide_shell_dress import (
            register_lindemann_strain,
            register_piezo_cage,
            register_piezo_energy_dress,
            tertiary_contact_piezo_energy_dress,
        )

        self.assertAlmostEqual(register_piezo_cage(1.0), 0.0, places=12)
        self.assertAlmostEqual(register_lindemann_strain(0.0, 273.15, 0.3), 0.0, places=12)
        self.assertAlmostEqual(register_piezo_energy_dress(0.0, 273.15, 0.3), 1.0, places=12)
        # Hydrophobic (open) cages more than helix_i4 (filled).
        from hqiv_lab.peptide_shell_dress import REGISTER_OCCUPANCY

        cage_h = register_piezo_cage(REGISTER_OCCUPANCY["hydrophobic"])
        cage_x = register_piezo_cage(REGISTER_OCCUPANCY["helix_i4"])
        self.assertGreater(cage_h, cage_x)
        piezo_h = tertiary_contact_piezo_energy_dress("hydrophobic")
        piezo_x = tertiary_contact_piezo_energy_dress("helix_i4")
        self.assertGreater(piezo_h, piezo_x)
        self.assertGreater(piezo_x, 1.0)

    def test_staged_pass_step_dress_milder_than_energy(self) -> None:
        from hqiv_lab.miniprotein_contacts import TertiaryContact
        from hqiv_lab.peptide_shell_dress import (
            staged_pass_piezo_step_dress,
            tertiary_contact_piezo_energy_dress,
        )

        contacts = [TertiaryContact(1, 5, 5.0, "hydrophobic")]
        step = staged_pass_piezo_step_dress(contacts)
        energy = tertiary_contact_piezo_energy_dress("hydrophobic")
        self.assertGreater(energy, step)
        self.assertGreater(step, 1.0)
        # Zero-T identity for the closure step dress.
        self.assertAlmostEqual(
            staged_pass_piezo_step_dress(contacts, temperature_k=0.0), 1.0, places=12
        )


if __name__ == "__main__":
    unittest.main()
