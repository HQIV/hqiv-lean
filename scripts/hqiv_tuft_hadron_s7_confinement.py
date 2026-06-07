#!/usr/bin/env python3
"""
Whole-hadron S⁷ envelope + f^{ijk} confinement dressing on the TUFT vev-pinned hadron chart.

Mirrors `Hqiv/Physics/HadronS7ConfinementReadout.lean`.

Thesis:
  • Confinement = antisymmetric color triple budget (9 sorted nonzero f^{ijk} slots).
  • S⁷ Laplace ratio on combined mode index (n + ℓ), not per-quark S⁷ descent alone.
  • TUFT vev ground + Beltrami increments remain the base (`hqiv_tuft_mass_spectrum_pdg_eval`).
"""

from __future__ import annotations

import math

import hqiv_excited_states as hes

# Lean `derivedProtonMass` (avoid import cycle with `hqiv_tuft_mass_spectrum_pdg_eval`)
DERIVED_PROTON_MEV = 938.27208816

# Lean `colorSu3SortedNonzeroTriples.card`
HADRON_IJK_SORTED_TRIPLE_BUDGET = 9


def laplace_beltrami_eigenvalue_s7(ell: int) -> float:
    """Lean `laplaceBeltramiEigenvalueS7`: λ_ℓ = ℓ(ℓ+6)."""
    return float(ell) * (float(ell) + 6.0)


def hadron_s7_whole_laplace_ratio(n: int, ell: int) -> float:
    """Lean `hadronS7WholeLaplaceRatio`."""
    idx = n + ell
    r_exc = laplace_beltrami_eigenvalue_s7(idx) + 1.0
    r_ref = laplace_beltrami_eigenvalue_s7(ell) + 1.0
    return r_exc / r_ref


def hadron_s7_whole_mode_weight(n: int, ell: int) -> float:
    return math.sqrt(hadron_s7_whole_laplace_ratio(n, ell))


def hadron_ijk_excitation_confinement_factor(
    n: int,
    ell: int,
    *,
    derived_proton_mev: float = DERIVED_PROTON_MEV,
    valence: int = 3,
) -> float:
    """Lean `hadronIjkExcitationConfinementFactor`."""
    rad = hes.delta_m_radial_operational_mev(n, derived_proton_mev=derived_proton_mev)
    orb = hes.delta_m_orbital_operational_mev(ell, derived_proton_mev=derived_proton_mev)
    inc = rad + orb
    return 1.0 + inc / derived_proton_mev / float(HADRON_IJK_SORTED_TRIPLE_BUDGET)


def hadron_ijk_confinement_pressure_mev(
    shell: int,
    valence: int,
    *,
    c: float = 1.0,
) -> float:
    """Lean `hadronIjkConfinementPressure` (diagnostic binding budget)."""
    bind = hes.e_bind_from_nucleon_trace_mev(shell, c) * (float(valence) / 3.0)
    return bind * HADRON_IJK_SORTED_TRIPLE_BUDGET / float(valence)


def hadron_whole_s7_ijk_dressing(base_mev: float, n: int, ell: int) -> float:
    """Lean `hadronWholeS7IjkDressing`."""
    return base_mev * hadron_s7_whole_mode_weight(n, ell) / hadron_ijk_excitation_confinement_factor(
        n, ell
    )


def tuft_hadron_whole_s7_mass_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """TUFT vev base × whole-hadron S⁷ × f^{ijk} confinement dressing (legacy whole-mass)."""
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    base = tmse.tuft_hadron_excited_mass_at_xi_mev(xi, n, ell)
    return hadron_whole_s7_ijk_dressing(base, n, ell)


def build_whole_s7_excited_rows(xi: float | None = None) -> list:
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    if xi is None:
        xi = tmse.XI_LOCKIN
    rows: list[tmse.PdgRow] = []
    for n, ell, pdg_key in tmse.BARYON_EXCITED_GRID:
        vev = tmse.tuft_hadron_excited_mass_at_xi_mev(xi, n, ell)
        dressed = tuft_hadron_whole_s7_mass_at_xi_mev(xi, n, ell)
        tag = pdg_key or f"(n={n}, ℓ={ell})"
        rows.append(
            tmse._row(
                f"baryon {tag} S⁷ whole + ijk",
                dressed,
                pdg_key,
                "hadronWholeS7IjkDressing ∘ tuftHadronExcitedMassAtXi_MeV",
            )
        )
        rows.append(
            tmse._row(
                f"baryon {tag} vev inline (base)",
                vev,
                pdg_key,
                "tuftHadronExcitedMassAtXi_MeV",
            )
        )
    return rows
