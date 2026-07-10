#!/usr/bin/env python3
"""
Voltage-generation ledger (six classical EMF routes).

Lean: ``Hqiv.QuantumChemistry.VoltageGenerationLedger``

Each channel is a dimensionless stress×response factor

  1 + (4/8) · stress · response

that recovers exactly 1 when unstressed.  Product dress multiplies beside
``OutsideContactLedger`` into the promoted n-body second-order factor.

Channels:
  chemo   — galvanic / chemical potential (ionic / μ asymmetry)
  thermo  — thermoelectric / Seebeck (ΔT / ξ contrast)
  photo   — photoelectric / photovoltaic (photon-phase excess)
  piezo   — piezoelectric (strain → polarization)
  tribo   — triboelectric (contact electrification asymmetry)
  faraday — Faraday induction (phase-rate / flux proxy)

Absolute volts = reference eV pin × dress (ionic surplus / contact scale);
this module is the dimensionless EMF dress only — no fitted coefficients.
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Any, Sequence

import hqiv_lean_physics_primitives as lean
import hqiv_molecular_spectroscopy as ms
import hqiv_outside_contact_ledger as ocl
import hqiv_preferred_axis_dress as pad
import hqiv_selection_weights as sw

STRONG = lean.STRONG_CHANNEL_FRACTION


def clamp01(x: float) -> float:
    return max(0.0, min(1.0, float(x)))


def voltage_channel(stress: float, response: float = 1.0) -> float:
    """Lean ``voltageChannel``."""
    return 1.0 + STRONG * clamp01(stress) * float(response)


def chemo_voltage_channel(ionic_asymmetry: float) -> float:
    """Lean ``chemoVoltageChannel`` — galvanic / μ asymmetry."""
    return voltage_channel(ionic_asymmetry, 1.0)


def thermo_voltage_channel(release_contrast: float) -> float:
    """Lean ``thermoVoltageChannel`` — Seebeck / ΔT·ξ contrast."""
    return voltage_channel(release_contrast, 1.0)


def joule_release_contrast(
    carrier_fraction: float,
    *,
    phonon_cage_fraction: float = 0.0,
) -> float:
    """
    Dimensionless Joule / thermal-release contrast for the thermo voltage slot.

    ``clamp01(carrier) · clamp01(phonon_cage) · γ`` — activates only with carriers;
    phonon cage (``1 − B_hom``) is the heat-trapping complement.  No SI mash, no
    molecule case.
    """
    return clamp01(carrier_fraction) * clamp01(phonon_cage_fraction) * lean.GAMMA


def carrier_thermo_conductivity_dress(
    carrier_fraction: float,
    *,
    phonon_cage_fraction: float = 0.0,
) -> float:
    """
    Conductivity ↔ Joule ↔ thermo loop dress.

    ``σ_eff = σ₀ · thermoVoltageChannel(joule_release_contrast(...))``.
    Identity when ``carrier_fraction = 0``.
    """
    return thermo_voltage_channel(
        joule_release_contrast(
            carrier_fraction, phonon_cage_fraction=phonon_cage_fraction
        )
    )


def photo_voltage_channel(photon_phase_excess: float, n_dielectric: float = 1.0) -> float:
    """Lean ``photoVoltageChannel``."""
    return voltage_channel(
        photon_phase_excess, ms.concentration_weight(max(float(n_dielectric), 1.0))
    )


def piezo_voltage_channel(strain_fraction: float, n_dielectric: float = 1.0) -> float:
    """Lean ``piezoVoltageChannel`` — strain × dielectric concentration."""
    return voltage_channel(
        strain_fraction, ms.concentration_weight(max(float(n_dielectric), 1.0))
    )


def lindemann_piezo_amplitude(*, linear_chain: bool = False) -> float:
    """Lean ``lindemannPiezoAmplitude`` / ``lindemannPiezoAmplitudeLinearChain``."""
    return lean.GAMMA / 4.0 if linear_chain else lean.GAMMA / 2.0


def lindemann_thermal_strain(
    temperature_k: float,
    melt_k: float,
    *,
    amplitude: float | None = None,
    phonon_cage: float = 0.0,
    linear_chain: bool = False,
) -> float:
    """
    Lean ``lindemannThermalStrain`` — continuous Brownian / equipartition piezo stress.

    ``ε = clamp01( amp · √(T/T_melt) · (1 + phonon_cage) )`` with ``amp = γ/2``
    (or ``γ/4`` on linear-chain motifs).  Identity at ``T → 0``.
    """
    if melt_k <= 0.0 or temperature_k <= 0.0:
        return 0.0
    amp = (
        float(amplitude)
        if amplitude is not None
        else lindemann_piezo_amplitude(linear_chain=linear_chain)
    )
    return clamp01(amp * math.sqrt(temperature_k / melt_k) * (1.0 + max(phonon_cage, 0.0)))


def piezo_voltage_channel_lindemann(
    temperature_k: float,
    melt_k: float,
    n_dielectric: float = 1.0,
    *,
    phonon_cage: float = 0.0,
    linear_chain: bool = False,
    amplitude: float | None = None,
) -> float:
    """Lean ``piezoVoltageChannelLindemann``."""
    return piezo_voltage_channel(
        lindemann_thermal_strain(
            temperature_k,
            melt_k,
            amplitude=amplitude,
            phonon_cage=phonon_cage,
            linear_chain=linear_chain,
        ),
        n_dielectric,
    )


def ionic_optical_gap_softener(ionic_character: float) -> float:
    """Lean ``ionicOpticalGapSoftener``: ``1 / (1 + (4/8)·γ·δ²)``."""
    return 1.0 / (
        1.0 + lean.STRONG_CHANNEL_FRACTION * lean.GAMMA * max(float(ionic_character), 0.0)
    )


def ionic_optical_gap_piezo_softener(ionic_character: float, strain: float) -> float:
    """Lean ``ionicOpticalGapPiezoSoftener``: ``1 / (1 + (4/8)·ε·δ²)``."""
    return 1.0 / (
        1.0
        + lean.STRONG_CHANNEL_FRACTION
        * max(float(strain), 0.0)
        * max(float(ionic_character), 0.0)
    )


def ionic_optical_gap_softener_with_piezo(
    ionic_character: float, strain: float
) -> float:
    """Lean ``ionicOpticalGapSoftenerWithPiezo`` — character × piezo softeners."""
    return ionic_optical_gap_softener(ionic_character) * ionic_optical_gap_piezo_softener(
        ionic_character, strain
    )


def ionic_anion_period_polarizability_softener(z_anion: int) -> float:
    """Lean ``ionicAnionPeriodPolarizabilitySoftener`` — period-2 anion CM softener."""
    import hqiv_ionic_bond_network as ibn

    return ibn.ionic_anion_period_polarizability_softener(int(z_anion))


def ionic_anion_period_melt_dress(z_cation: int, z_anion: int) -> float:
    """Lean ``ionicAnionPeriodMeltDress`` — mixed-period melt boost."""
    import hqiv_ionic_bond_network as ibn

    return ibn.ionic_anion_period_melt_dress(int(z_cation), int(z_anion))


def thermal_concentration_dress(strain: float) -> float:
    """Lean ``thermalConcentrationDress``: ``1 + (4/8)·ε·(γ/2)``."""
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * max(float(strain), 0.0) * (lean.GAMMA / 2.0)


def brownian_local_defect_channel(strain: float) -> float:
    """Lean ``brownianLocalDefectChannel``: ``1 + γ·(4/8)·ε`` via localDefect."""
    return ocl.outside_local_channel(max(float(strain), 0.0))


def earth_faraday_stress(
    b_tesla: float = 50e-6,
    b_ref_tesla: float | None = None,
) -> float:
    """Ambient Earth-B Faraday stress: ``B/B_ref`` (ppm-scale on the voltage channel)."""
    ref = lean.UCN_TRAP_REFERENCE_FIELD_TESLA if b_ref_tesla is None else float(b_ref_tesla)
    return lean.trap_magnetic_curvature_fraction(b_tesla, ref)


def tribo_voltage_channel(axis_gap: float, coordination_excess: float = 0.0) -> float:
    """Lean ``triboVoltageChannel`` — preferred-axis × local defect."""
    # preferredAxisPlaneLocalDress at η=0 is always 1; use η-independent gap dress:
    # 1 + (1/2)·0·… = 1, so fold gap through voltageChannel + local defect.
    axis = voltage_channel(axis_gap, 1.0)
    local = ocl.outside_local_channel(coordination_excess)
    return axis * local


def faraday_voltage_channel(phase_rate_fraction: float) -> float:
    """Lean ``faradayVoltageChannel`` — dη/dt / flux proxy."""
    return voltage_channel(phase_rate_fraction, 1.0)


@dataclass(frozen=True)
class VoltageGenerationLedger:
    """Lean ``VoltageGenerationLedger``."""

    chemo: float = 1.0
    thermo: float = 1.0
    photo: float = 1.0
    piezo: float = 1.0
    tribo: float = 1.0
    faraday: float = 1.0

    @property
    def dress(self) -> float:
        """Lean ``voltageGenerationLedgerDress``."""
        return (
            self.chemo
            * self.thermo
            * self.photo
            * self.piezo
            * self.tribo
            * self.faraday
        )

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["dress"] = self.dress
        d["channels"] = {
            "chemo": "galvanic / chemical potential (ionic asymmetry)",
            "thermo": "thermoelectric / Seebeck (ΔT / ξ contrast)",
            "photo": "photoelectric / photovoltaic (photon-phase excess)",
            "piezo": "piezoelectric (strain → polarization)",
            "tribo": "triboelectric (contact electrification asymmetry)",
            "faraday": "Faraday induction (phase-rate / flux proxy)",
        }
        return d


def unstressed_voltage_generation_ledger() -> VoltageGenerationLedger:
    """Lean ``unstressedVoltageGenerationLedger`` — all channels = 1."""
    return VoltageGenerationLedger(
        chemo=chemo_voltage_channel(0.0),
        thermo=thermo_voltage_channel(0.0),
        photo=photo_voltage_channel(0.0, 1.0),
        piezo=piezo_voltage_channel(0.0, 1.0),
        tribo=tribo_voltage_channel(0.0, 0.0),
        faraday=faraday_voltage_channel(0.0),
    )


def voltage_generation_ledger_from_stresses(
    *,
    ionic_asymmetry: float = 0.0,
    release_contrast: float = 0.0,
    photon_phase_excess: float = 0.0,
    n_dielectric: float = 1.0,
    strain_fraction: float = 0.0,
    axis_gap: float = 0.0,
    coordination_excess: float = 0.0,
    phase_rate_fraction: float = 0.0,
) -> VoltageGenerationLedger:
    """Lean ``voltageGenerationLedgerFromStresses``."""
    return VoltageGenerationLedger(
        chemo=chemo_voltage_channel(ionic_asymmetry),
        thermo=thermo_voltage_channel(release_contrast),
        photo=photo_voltage_channel(photon_phase_excess, n_dielectric),
        piezo=piezo_voltage_channel(strain_fraction, n_dielectric),
        tribo=tribo_voltage_channel(axis_gap, coordination_excess),
        faraday=faraday_voltage_channel(phase_rate_fraction),
    )


def electro_contact_dress(
    outside: ocl.OutsideContactLedger,
    voltage: VoltageGenerationLedger,
) -> float:
    """Lean ``electroContactDress`` = outside × voltage."""
    return outside.dress * voltage.dress


def ionic_asymmetry_from_bonds(
    fragments: Sequence[object],
    bonds: Sequence[object],
) -> float:
    """Mean bond ionic character as galvanic stress (0 for homonuclear)."""
    if not bonds:
        return 0.0
    ws: list[float] = []
    for b in bonds:
        i = getattr(b, "frag_i", None)
        j = getattr(b, "frag_j", None)
        if i is None or j is None:
            continue
        z_i = int(getattr(fragments[i], "z_nuclear"))
        z_j = int(getattr(fragments[j], "z_nuclear"))
        ws.append(sw.bond_ionic_character(z_i, z_j))
    return sum(ws) / len(ws) if ws else 0.0


def axis_gap_from_bonds(
    fragments: Sequence[object],
    bonds: Sequence[object],
) -> float:
    """Preferred-axis spectral gap of bond polarities (tribo stress)."""
    pols = pad.bond_polarities_from_fragments_bonds(fragments, bonds)
    return pad.preferred_axis_spectral_gap(pols)


def ledger_for_molecule(
    *,
    fragments: Sequence[object],
    bonds: Sequence[object],
    strain_fraction: float = 0.0,
    release_contrast: float = 0.0,
    photon_phase_excess: float = 0.0,
    coordination_excess: float = 0.0,
    phase_rate_fraction: float = 0.0,
    unstressed: bool = True,
) -> VoltageGenerationLedger:
    """
    Build voltage ledger for one molecule.

    Default ``unstressed=True`` recovers identity (GMTKN gas assay).
    Stress piezo/chemo/thermo/… by setting ``unstressed=False`` and supplying
    strain / release / photon / phase-rate / coordination excess.
    """
    if unstressed and strain_fraction == 0.0 and release_contrast == 0.0:
        if (
            photon_phase_excess == 0.0
            and coordination_excess == 0.0
            and phase_rate_fraction == 0.0
        ):
            return unstressed_voltage_generation_ledger()

    n_diel = ocl.mean_dielectric_from_bonds(fragments, bonds)
    return voltage_generation_ledger_from_stresses(
        ionic_asymmetry=ionic_asymmetry_from_bonds(fragments, bonds),
        release_contrast=release_contrast,
        photon_phase_excess=photon_phase_excess,
        n_dielectric=n_diel,
        strain_fraction=strain_fraction,
        axis_gap=axis_gap_from_bonds(fragments, bonds),
        coordination_excess=coordination_excess,
        phase_rate_fraction=phase_rate_fraction,
    )


def stress_demo_rows() -> list[dict[str, Any]]:
    """
    Demonstrate piezo / chemo / thermo / photo / tribo / faraday stresses.

    Each row starts from the unstressed identity and turns on one channel.
    """
    base = unstressed_voltage_generation_ledger()
    demos = [
        ("unstressed", base),
        ("piezo_strain_0.1", voltage_generation_ledger_from_stresses(
            strain_fraction=0.1, n_dielectric=1.5
        )),
        ("chemo_ionic_0.25", voltage_generation_ledger_from_stresses(
            ionic_asymmetry=0.25
        )),
        ("thermo_contrast_0.2", voltage_generation_ledger_from_stresses(
            release_contrast=0.2
        )),
        ("photo_eta_0.15", voltage_generation_ledger_from_stresses(
            photon_phase_excess=0.15, n_dielectric=1.4
        )),
        ("tribo_gap_1", voltage_generation_ledger_from_stresses(
            axis_gap=1.0, coordination_excess=0.2
        )),
        ("faraday_rate_0.1", voltage_generation_ledger_from_stresses(
            phase_rate_fraction=0.1
        )),
        ("piezo+chemo", voltage_generation_ledger_from_stresses(
            strain_fraction=0.1, ionic_asymmetry=0.25, n_dielectric=1.5
        )),
    ]
    return [
        {
            "label": label,
            "dress": V.dress,
            "delta_vs_unstressed": V.dress - 1.0,
            **{k: getattr(V, k) for k in ("chemo", "thermo", "photo", "piezo", "tribo", "faraday")},
        }
        for label, V in demos
    ]


if __name__ == "__main__":
    print("Voltage-generation ledger stress demos")
    print("=" * 72)
    for row in stress_demo_rows():
        print(
            f"{row['label']:<22} dress={row['dress']:.6f} "
            f"Δ={row['delta_vs_unstressed']:+.6f} "
            f"piezo={row['piezo']:.4f} chemo={row['chemo']:.4f}"
        )
