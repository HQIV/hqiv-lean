#!/usr/bin/env python3
"""
HQIV atom construction from math (heavy-decay discipline).

**Prediction path (no experimental inputs):**
  1. Fixed carrier: α=3/5, γ=2/5, referenceM=4, proton_lockin mass witness
  2. Electronic discharge registry from `Z` (`hqiv_atom_electronic_discharge`)
  3. Nuclear cluster mass from curvature binding (`hqiv_nuclear_curvature_binding`)
  4. Closed mass: `M_nucleus + Z·m_e − B_electronic + B_out_fight` (electrons fight outside caustic load for Z > H)
  5. Continuous ξ witnesses per discharge shell (`hqiv_atom_continuous_xi`)

**Comparison layer:** NIST/CODATA atomic masses — guardrails only, never in formulas.

Run:
  python3 scripts/hqiv_atom_construction.py
  python3 scripts/hqiv_atom_construction.py --json
  python3 scripts/hqiv_atom_construction.py --element O
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Any

import hqiv_atom_continuous_xi as axi
import hqiv_atom_electronic_discharge as discharge
import hqiv_atom_stable_chart as stable_chart
import hqiv_isotope_hydrogenic_scales as ihs
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_curvature_binding as ncb
import hqiv_nuclear_inside_outside_binding as niob
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_scale_witness as sw
from lih_derivation_scan import lattice_full_mode_energy

LEAN_MODULE = "Hqiv.QuantumChemistry.AtomFromCharge"
LEAN_FIGHT_MODULE = "Hqiv.QuantumChemistry.AtomOutsideCurvatureFight"
LEAN_BINDING_MODULE = "Hqiv.QuantumChemistry.AtomElectronicBinding"
LEAN_NUCLEUS_MODULE = "Hqiv.QuantumChemistry.AtomNucleusCurvatureShell"
LEAN_DISCHARGE_MODULE = "Hqiv.QuantumChemistry.AtomElectronicDischarge"
MEV_PER_AMU = 931.49410242  # CODATA unit conversion for reporting only
# Proton/electron mass ratio is now a DERIVED HQIV readout (TUFT vev->T8 electron
# over the proton lock-in), not the hard-coded CODATA value.  See
# `hqiv_proton_electron_ratio`.  CODATA is retained as a comparison guardrail.
CODATA_PROTON_TO_ELECTRON_MASS_RATIO = 1836.15267343  # comparison only
HARTREE_TO_EV = 27.211386245988  # unit bridge for ionization witnesses only


class AtomComparisonLayer:
    """
    Quarantined experimental guardrails — **never** imported by prediction formulas.

    Mirrors hep_decay_readout comparison discipline (PDG quarantined from spine discharge).
    """

    # NIST standard atomic weights (comparison only)
    NIST_ATOMIC_MASS_AMU: dict[str, float] = {
        "H": 1.00782503223,
        "He": 4.00260325413,
        "Li": 7.0160034366,
        "C": 12.0,
        "N": 14.00307400443,
        "O": 15.999084904,
        "Na": 22.9897692820,
        "Fe": 55.845,
    }

    # NIST first ionization energies [eV] — comparison only
    NIST_FIRST_IONIZATION_EV: dict[str, float] = {
        "H": 13.59843449,
        "He": 24.587387366,
        "Li": 5.391719966,
        "C": 11.260288,
        "N": 14.53413,
        "O": 13.618055,
        "Na": 5.13907696,
        "Fe": 7.9024,
    }

    ELEMENT_Z: dict[str, int] = {
        "H": 1,
        "He": 2,
        "Li": 3,
        "C": 6,
        "N": 7,
        "O": 8,
        "Na": 11,
        "Fe": 26,
    }

    @classmethod
    def z_for_element(cls, symbol: str) -> int:
        sym = symbol.strip().capitalize()
        if sym not in cls.ELEMENT_Z:
            raise KeyError(f"Unknown element {symbol!r} in comparison catalog")
        return cls.ELEMENT_Z[sym]

    @classmethod
    def nist_mass_amu(cls, symbol: str) -> float | None:
        return cls.NIST_ATOMIC_MASS_AMU.get(symbol.strip().capitalize())


    @classmethod
    def nist_first_ionization_ev(cls, symbol: str) -> float | None:
        return cls.NIST_FIRST_IONIZATION_EV.get(symbol.strip().capitalize())


def derived_electron_mass_mev(proton_mev: float | None = None) -> float:
    """Electron mass as a derived HQIV readout (TUFT vev->T8 winding n=1).

    PDG-free and CODATA-free: the electron mass is the framework's own lepton
    chart, not ``proton / 1836.15``.  The ``proton_mev`` argument is retained for
    backward compatibility but no longer enters the electron mass.
    """
    import hqiv_proton_electron_ratio as pe

    return pe.derived_electron_mass_mev()


def reduced_mass_au_from_nuclear_mev(nuclear_mev: float, m_e_mev: float) -> float:
    """μ = M/(M+1) with M = m_nucleus/m_e (electron mass = 1 a.u.)."""
    m_over_me = nuclear_mev / m_e_mev
    return m_over_me / (m_over_me + 1.0)


# Madelung (aufbau) sub-shell filling order and capacities.  The capacities and the
# (n+ℓ) ordering are now DERIVED in the particle-first shell-structure layer
# (`hqiv_particle_shell_structure`): capacity = monogamy-pair × (2ℓ+1), order = Madelung.
# Only the (n+ℓ) ordering rule itself remains a stated principle there.
import hqiv_particle_shell_structure as _pss

SUBSHELL_FILL_ORDER: tuple[tuple[int, int], ...] = tuple(_pss.madelung_fill_order())
SUBSHELL_CAPACITY: dict[int, int] = {l: _pss.subshell_capacity(l) for l in range(7)}


def electron_configuration(z: int) -> list[tuple[int, int]]:
    """Per-electron (n, l) occupancy via the Madelung aufbau order.

    Returns one ``(n, l)`` tuple per electron in filling order.  Period 1-2
    reproduce the previous ``atom_electron_shells`` multiset exactly; period 3+
    are now correct (e.g. Na's valence is the ``3s`` electron at ``n = 3``, not a
    spurious ``n = 2`` slot).
    """
    if z <= 0:
        return []
    cfg: list[tuple[int, int]] = []
    remaining = z
    for (n, l) in SUBSHELL_FILL_ORDER:
        if remaining <= 0:
            break
        k = min(remaining, SUBSHELL_CAPACITY[l])
        cfg.extend([(n, l)] * k)
        remaining -= k
    return cfg


def compton_shell_for_nl(n: int, l: int) -> int:
    """Compton shell index ``m`` for orbital ``(n, l)`` (discharge convention).

    Anchored on the discharge constants (1s→1, 2s→4, 2p→3) and extended by the
    period offset: ``m = n + 2 − l`` for ``n ≥ 2`` (s→n+2, p→n+1, d→n).
    """
    if n == 1 and l == 0:
        return discharge.ELECTRONIC_M_H_1S
    return n + 2 - l


def principal_quantum_from_compton_shell(m: int) -> int:
    """Legacy Compton-shell → principal block map (period ≤ 2 only; kept for compat).

    Ambiguous for period 3+ (``m`` is not injective in ``n``); the prediction path
    now uses :func:`electron_configuration` instead.
    """
    if m <= 1:
        return 1
    if m <= 4:
        return 2
    return 3 + max(0, m - 4) // 2


# --- Screening coefficients DERIVED from the carrier (no empirical Slater table) ------------
# A deeper electron screens by Gauss's law: fully enclosed → one whole unit (FULL = 1).
# A co-radial (same-shell) electron is only *half* enclosed on average → the monogamy half 1/2.
# The valence carrier penetrates any adjacent shell (same or n−1) by the lapse spread over the
# monogamy-core / proton-anchor shell: leak = α / referenceM = (3/5)/4 = 0.15.  Hence
#   same-shell   = 1/2 − α/4 = 0.35,   n−1 shell = 1 − α/4 = 0.85,   deeper = 1.00,
# reproducing the textbook Slater coefficients exactly from α = 3/5 and referenceM = 4.
_SCREEN_FULL_ENCLOSURE = 1.0
_SCREEN_CORADIAL_ENCLOSURE = lean.STRONG_CHANNEL_FRACTION          # monogamy half = 1/2
_SCREEN_PENETRATION_LEAK = lean.ALPHA / float(lean.REFERENCE_M)    # α / 4 = 0.15
SLATER_SAME_SHELL = _SCREEN_CORADIAL_ENCLOSURE - _SCREEN_PENETRATION_LEAK   # 0.35
SLATER_ADJACENT_SHELL = _SCREEN_FULL_ENCLOSURE - _SCREEN_PENETRATION_LEAK   # 0.85
SLATER_DEEP_SHELL = _SCREEN_FULL_ENCLOSURE                                  # 1.00


def config_effective_charge(
    z: int, target_index: int, config: list[tuple[int, int]]
) -> float:
    """Slater effective charge with the *true* principal quantum numbers and DERIVED screening.

    The screening increments are no longer the empirical 0.35/0.85/1.00 table — they are derived
    from the carrier: Gauss full-enclosure (1.00), the monogamy half for a co-radial electron
    (1/2), and the adjacent-shell penetration leak α/referenceM (= 0.15).  See the module
    constants above; the values coincide with Slater's exactly.
    """
    n_t, _l_t = config[target_index]
    shield = 0.0
    for j, (n_j, _l_j) in enumerate(config):
        if j == target_index:
            continue
        if n_j == n_t:
            shield += SLATER_SAME_SHELL
        elif n_j == n_t - 1:
            shield += SLATER_ADJACENT_SHELL
        else:
            shield += SLATER_DEEP_SHELL
    return max(1.0, float(z) - shield)


def slater_effective_charge(z: int, target_index: int, shells: list[int]) -> float:
    """Backward-compatible wrapper: rebuild the (n, l) configuration and screen.

    The ``shells`` argument is accepted for the legacy signature but ``z`` and the
    position fully determine the configuration, so screening now uses true ``n``.
    """
    _ = shells
    cfg = electron_configuration(z)
    idx = min(target_index, len(cfg) - 1) if cfg else 0
    if not cfg:
        return max(1.0, float(z))
    return config_effective_charge(z, idx, cfg)


def bind_energy_ev_for_n(n: int, z_eff: float, mu: float) -> float:
    """Physical-scale hydrogenic binding [eV] for principal quantum number ``n``."""
    e_hartree = mu * z_eff * z_eff / (2.0 * float(n) * float(n))
    return e_hartree * HARTREE_TO_EV


def bind_energy_ev_per_electron(
    m: int,
    z_eff: float,
    mu: float,
    *,
    c: float = 1.0,
) -> float:
    """Legacy shim: hydrogenic binding [eV] with ``n`` inferred from Compton shell ``m``."""
    _ = c
    return bind_energy_ev_for_n(principal_quantum_from_compton_shell(m), z_eff, mu)


def atom_electronic_binding_mev(z: int, *, c: float = 1.0) -> float:
    """Total electronic binding from the aufbau configuration sum."""
    if z <= 0:
        return 0.0
    cfg = electron_configuration(z)
    nuc_mev = atom_nuclear_cluster_mass_mev(z, c=c)
    m_e = derived_electron_mass_mev()
    mu = reduced_mass_au_from_nuclear_mev(nuc_mev, m_e)
    total_ev = sum(
        bind_energy_ev_for_n(n, config_effective_charge(z, i, cfg), mu)
        for i, (n, _l) in enumerate(cfg)
    )
    return total_ev * 1e-6


def atom_first_ionization_ev(z: int, *, c: float = 1.0) -> float:
    """Outermost-electron binding scale with the correct principal quantum number."""
    cfg = electron_configuration(z)
    if not cfg:
        return 0.0
    idx = len(cfg) - 1
    n, _l = cfg[idx]
    nuc_mev = atom_nuclear_cluster_mass_mev(z, c=c)
    m_e = derived_electron_mass_mev()
    mu = reduced_mass_au_from_nuclear_mev(nuc_mev, m_e)
    z_eff = config_effective_charge(z, idx, cfg)
    return bind_energy_ev_for_n(n, z_eff, mu)


def valence_electron_pull(z: int) -> float:
    """Per-atom electron-pull ``p = z_eff(valence) / (m_valence + 1)``.

    This is the inverse nested-WF contact radius evaluated on the *correct* valence
    shell — the native electronegativity coordinate.  Larger ``p`` ⇒ stronger pull
    on a shared bonding electron.  Homonuclear ionicity built from ``p`` vanishes by
    construction.
    """
    cfg = electron_configuration(z)
    if not cfg:
        return 0.0
    idx = len(cfg) - 1
    n, l = cfg[idx]
    z_eff = config_effective_charge(z, idx, cfg)
    return z_eff / float(compton_shell_for_nl(n, l) + 1)


def atom_electronic_outside_curvature_fight_mev(z: int, *, c: float = 1.0) -> float:
    """
    Electrons fight the nuclear **outside** caustic field (Z > H only).

    Nucleons deepen the cluster well via outside ``G_eff`` (lowers nuclear mass).
    Bound electrons sit in that outside chart and carry a compensating load:

      Σ_e  (B_out/A) · (4/8) · G_eff(θ_e) · (α_eff/α_lock)² · max(0, mod_bonded(ξ_e) − 1) · (Z/A)

    Uses the same ``outsideCurvatureBindingModulator`` bonded branch as
    ``NuclearOutsideTemperatureDynamics`` — inverted sign (mass **adds**, not binding deepens).
    Hydrogen (A = 1, no nuclear outside stack) returns zero.
    """
    if z <= 1:
        return 0.0
    a = stable_mass_number_for_charge(z)
    m_nuc = ncb.nucleus_curvature_shell(a) if a > 1 else lean.REFERENCE_M
    _total_bind, _inside, b_out = niob.nuclear_cluster_binding_mev(
        m_nuc, a, m_cluster=m_nuc, c=c
    )
    if b_out <= 0.0:
        return 0.0
    b_out_per_nucleon = b_out / float(a)
    shells = atom_electron_shells(z)
    ae_lock = ihs.alpha_eff_at_shell(lean.REFERENCE_M, c)
    exposure = float(z) / float(a)
    fight = 0.0
    for m_shell in shells:
        xi = float(m_shell + 1)
        theta = niob.contact_phase_theta_rad((m_nuc, m_shell, lean.REFERENCE_M))
        geff = niob.outside_contact_coupling(theta)
        mod = notd.outside_curvature_binding_modulator(xi, bonded=True)
        load = max(0.0, mod - 1.0)
        ae = ihs.alpha_eff_at_shell(m_shell, c)
        fight += (
            lean.STRONG_CHANNEL_FRACTION
            * b_out_per_nucleon
            * load
            * geff
            * (ae / ae_lock) ** 2
            * exposure
        )
    return fight


def atom_closed_mass_mev(z: int, *, c: float = 1.0) -> float:
    """
    M_atom = M_nucleus + Z·m_e − B_electronic + B_out_fight  (mirrors `BoundStates.M_atom` + outside load).
    """
    if z <= 0:
        return 0.0
    m_e = derived_electron_mass_mev()
    nuc = atom_nuclear_cluster_mass_mev(z, c=c)
    bind = atom_electronic_binding_mev(z, c=c)
    fight = atom_electronic_outside_curvature_fight_mev(z, c=c)
    return nuc + float(z) * m_e - bind + fight


def stable_mass_number_for_charge(z: int) -> int:
    """Lean `stableMassNumberForCharge` — neutral-atom chart, not PDG table."""
    return stable_chart.stable_mass_number_for_charge(z)


def atom_electron_shells(z: int) -> list[int]:
    """Per-electron Compton shell indices from the aufbau configuration (prediction path).

    Period 1-2 are identical to the previous slot model; period 3+ now resolve the
    distinct inner (2s/2p) and valence (3s/3p) shells instead of collapsing them.
    """
    return [compton_shell_for_nl(n, l) for (n, l) in electron_configuration(z)]


def atom_site_energy_trace(z: int) -> float:
    """Lean `atomSiteEnergyTrace` mirror."""
    if z == 0:
        return 0.0
    if z == 1:
        return lattice_full_mode_energy(discharge.ELECTRONIC_M_H_1S)
    if z == 2:
        return 2.0 * lattice_full_mode_energy(discharge.ELECTRONIC_M_H_1S)
    slots = discharge.atom_compton_slots_from_charge(z)
    core = 2.0 * lattice_full_mode_energy(discharge.ELECTRONIC_M_H_1S)
    n_val = z - 2
    n_s = min(n_val, 2)
    n_p = n_val - n_s
    return (
        core
        + n_s * lattice_full_mode_energy(slots.m_centre_s)
        + n_p * lattice_full_mode_energy(slots.m_centre_p)
    )


def atom_hydrogenic_binding_mev(z: int, *, c: float = 1.0) -> float:
    """Hydrogenic binding magnitude at 1s discharge shell (α_eff ladder)."""
    if z == 0:
        return 0.0
    alpha_eff = ihs.alpha_eff_at_shell(discharge.ELECTRONIC_M_H_1S, c=c)
    # Atomic units with m_e = 1; the Hartree scale rides on the *derived* electron
    # mass (m_e in a.u. = 1), so report via the derived electron mass directly.
    bind_au = z * z * alpha_eff * alpha_eff / 2.0
    return bind_au * derived_electron_mass_mev()


def atom_nuclear_cluster_mass_mev(z: int, *, c: float = 1.0) -> float:
    a = stable_mass_number_for_charge(z)
    if a == 0:
        return 0.0
    m_nuc = ncb.nucleus_curvature_shell(a) if a > 1 else lean.REFERENCE_M
    return ncb.cluster_mass_mev(m_nuc, a, c=c)


@dataclass(frozen=True)
class AtomReadout:
    nuclear_charge: int
    mass_number: int
    discharge: discharge.AtomElectronicDischargeObs
    compton: discharge.AtomComptonSlots
    triplet: tuple[int, int, int]
    electron_shells: tuple[int, ...]
    shell_xi_readouts: tuple[axi.ShellXiReadout, ...]
    nuclear_mass_mev: float
    electron_mass_total_mev: float
    electronic_binding_mev: float
    electronic_outside_curvature_fight_mev: float
    closed_mass_mev: float
    site_energy_trace: float
    hydrogenic_binding_mev: float
    nuclear_only_mass_amu: float
    derived_atomic_mass_amu: float
    first_ionization_ev: float
    scale_witness: str

    def to_dict(self) -> dict[str, Any]:
        d = asdict(self)
        d["discharge"] = asdict(self.discharge)
        d["compton"] = asdict(self.compton)
        d["shell_xi_readouts"] = [r.to_dict() for r in self.shell_xi_readouts]
        return d


def atom_readout_from_charge(
    z: int,
    *,
    c: float = 1.0,
) -> AtomReadout:
    """Full prediction-path atom readout from `Z` alone."""
    bundle = sw.load_witness_bundle()
    obs = discharge.atom_electronic_discharge_obs(z)
    slots = discharge.atom_compton_slots_from_charge(z)
    triplet = discharge.atom_compton_triplet_from_charge(z)
    nuc_mev = atom_nuclear_cluster_mass_mev(z, c=c)
    site = atom_site_energy_trace(z)
    m_e = derived_electron_mass_mev(bundle.derived_proton_mass_mev)
    bind_mev = atom_electronic_binding_mev(z, c=c)
    fight_mev = atom_electronic_outside_curvature_fight_mev(z, c=c)
    closed_mev = nuc_mev + float(z) * m_e - bind_mev + fight_mev
    shells = tuple(atom_electron_shells(z))
    xi_rows = tuple(axi.shells_xi_panel(shells, c=c))
    return AtomReadout(
        nuclear_charge=z,
        mass_number=stable_mass_number_for_charge(z),
        discharge=obs,
        compton=slots,
        triplet=triplet,
        electron_shells=shells,
        shell_xi_readouts=xi_rows,
        nuclear_mass_mev=nuc_mev,
        electron_mass_total_mev=float(z) * m_e,
        electronic_binding_mev=bind_mev,
        electronic_outside_curvature_fight_mev=fight_mev,
        closed_mass_mev=closed_mev,
        site_energy_trace=site,
        hydrogenic_binding_mev=atom_hydrogenic_binding_mev(z, c=c),
        nuclear_only_mass_amu=nuc_mev / MEV_PER_AMU,
        derived_atomic_mass_amu=closed_mev / MEV_PER_AMU,
        first_ionization_ev=atom_first_ionization_ev(z, c=c),
        scale_witness=bundle.scale_witness_default,
    )


@dataclass(frozen=True)
class AtomComparisonRow:
    element: str
    Z: int
    prediction: AtomReadout
    nist_mass_amu: float | None
    relative_error_vs_nist: float | None
    nist_first_ionization_ev: float | None
    relative_error_ionization_vs_nist: float | None

    def to_dict(self) -> dict[str, Any]:
        return {
            "element": self.element,
            "Z": self.Z,
            "prediction": self.prediction.to_dict(),
            "comparison": {
                "nist_mass_amu": self.nist_mass_amu,
                "relative_error_vs_nist": self.relative_error_vs_nist,
                "nist_first_ionization_ev": self.nist_first_ionization_ev,
                "relative_error_ionization_vs_nist": self.relative_error_ionization_vs_nist,
            },
        }


def comparison_row(symbol: str) -> AtomComparisonRow:
    z = AtomComparisonLayer.z_for_element(symbol)
    pred = atom_readout_from_charge(z)
    nist = AtomComparisonLayer.nist_mass_amu(symbol)
    nist_ie = AtomComparisonLayer.nist_first_ionization_ev(symbol)
    rel: float | None = None
    rel_ie: float | None = None
    if nist is not None and nist > 0:
        rel = (pred.derived_atomic_mass_amu - nist) / nist
    if nist_ie is not None and nist_ie > 0:
        rel_ie = (pred.first_ionization_ev - nist_ie) / nist_ie
    return AtomComparisonRow(
        element=symbol,
        Z=z,
        prediction=pred,
        nist_mass_amu=nist,
        relative_error_vs_nist=rel,
        nist_first_ionization_ev=nist_ie,
        relative_error_ionization_vs_nist=rel_ie,
    )


def export_witness_panel(
    symbols: tuple[str, ...] = ("H", "He", "Li", "C", "N", "O", "Na", "Fe"),
) -> dict[str, Any]:
    rows = [comparison_row(s).to_dict() for s in symbols]
    return {
        "lean_module": LEAN_MODULE,
        "discharge_lean_module": LEAN_DISCHARGE_MODULE,
        "binding_lean_module": LEAN_BINDING_MODULE,
        "nucleus_lean_module": LEAN_NUCLEUS_MODULE,
        "outside_fight_lean_module": LEAN_FIGHT_MODULE,
        "scale_witness": sw.DEFAULT_SCALE_WITNESS,
        "input_policy": "prediction_from_Z_only; NIST_in_comparison_layer_only",
        "factorization_ok": discharge.satisfies_atom_electronic_factorization(
            discharge.atom_compton_slots_canonical
        ),
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--write-json",
        nargs="?",
        const="default",
        default="",
        metavar="PATH",
        help="Write witness panel JSON (default path: data/atom_construction_witnesses.json)",
    )
    parser.add_argument("--element", type=str, default="")
    parser.add_argument(
        "--witness",
        choices=["proton_lockin", "codata_alpha", "cmb_now"],
        default=sw.DEFAULT_SCALE_WITNESS,
    )
    args = parser.parse_args()
    witness: sw.ScaleWitness = args.witness  # type: ignore[assignment]

    if args.element:
        row = comparison_row(args.element)
        payload: dict[str, Any] = row.to_dict()
    else:
        payload = export_witness_panel()

    write_path = args.write_json
    if write_path == "default":
        write_path = "data/atom_construction_witnesses.json"
    if write_path:
        from pathlib import Path

        out = Path(write_path)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload if args.element else export_witness_panel(), indent=2) + "\n")
        print(f"Wrote {out}")

    if args.json:
        print(json.dumps(payload, indent=2))
    elif not write_path:
        if args.element:
            p = row.prediction
            print(f"{row.element} Z={row.Z}")
            print(f"  triplet {p.triplet}  shells {p.electron_shells}")
            print(f"  derived mass amu = {p.derived_atomic_mass_amu:.6f}  (nuclear-only {p.nuclear_only_mass_amu:.6f})")
            print(f"  first ionization ev = {p.first_ionization_ev:.4f}")
            if row.nist_mass_amu is not None:
                print(
                    f"  NIST amu = {row.nist_mass_amu:.6f}  "
                    f"rel err = {100.0 * (row.relative_error_vs_nist or 0.0):+.2f}%"
                )
            if row.nist_first_ionization_ev is not None:
                print(
                    f"  NIST IE = {row.nist_first_ionization_ev:.4f} eV  "
                    f"rel err = {100.0 * (row.relative_error_ionization_vs_nist or 0.0):+.1f}%"
                )
        else:
            panel = export_witness_panel()
            print(f"Lean: {LEAN_MODULE}")
            print(f"Witness: {panel['scale_witness']}")
            print(f"Discharge factorization: {panel['factorization_ok']}")
            for r in panel["rows"]:
                comp = r["comparison"]
                pred = r["prediction"]
                rel = comp["relative_error_vs_nist"]
                rel_s = f"{100.0 * rel:+.2f}%" if rel is not None else "n/a"
                print(
                    f"{r['element']:>2}  mass={pred['derived_atomic_mass_amu']:.4f} amu  "
                    f"NIST={comp['nist_mass_amu']}  Δm={rel_s}  "
                    f"IE={pred['first_ionization_ev']:.2f} eV"
                )


if __name__ == "__main__":
    main()
