"""Crystal lattice contact geometry — Lean mirror of ``CrystalContactGeometry.lean``."""

from __future__ import annotations

import math

from hqiv_lab._scripts import ensure_scripts_on_path

ensure_scripts_on_path()
import hqiv_atom_construction as ac  # noqa: E402
import hqiv_chemistry_tuft_dynamics as ctd  # noqa: E402
import hqiv_electronic_valence_shells as evs  # noqa: E402
import hqiv_lean_physics_primitives as lean  # noqa: E402

BOHR_ANGSTROM = ctd.BOHR_RADIUS_ANGSTROM
CONSTRUCTIVE_VALLEY_CAP = float(lean.CONSTRUCTIVE_VALLEY_CAP)
MEV_PER_AMU = 931.49410242
AVOGADRO = 6.02214076e23


def neutron_surplus_over_pair_floor(a: int, z: int) -> float:
    """Lean ``neutronSurplusOverPairFloor``: ``A/(2Z)``."""
    if z <= 0:
        return 1.0
    return float(a) / (2.0 * float(z))


def nuclear_packing_dress(a: int, z: int) -> float:
    """
    Lean ``nuclearPackingDress``: ``(A/(2Z))^(-γ) = (2Z/A)^γ``.

    Electronic lattice lengths are Z-keyed; nuclear packing tracks A.
    Relative to the α-pairing floor ``A≈2Z``, neutron surplus contracts nn as
    the monogamy complement power ``γ``.
    """
    if a <= 0 or z <= 0:
        return 1.0
    surplus = neutron_surplus_over_pair_floor(a, z)
    return surplus ** (-lean.GAMMA)


def nuclear_packing_dress_for_z(z: int) -> float:
    """Dress from Coulomb ``A(Z)`` chart."""
    import hqiv_atom_stable_chart as asc

    return nuclear_packing_dress(asc.stable_mass_number_for_charge(z), z)


def nuclear_packing_open_dress(pack: float) -> float:
    """
    Lean ``nuclearPackingOpenDress``: ``1 + (4/8)·γ·(1 − pack)``.

    Partial monogamy reopen of the P/N packing contraction on metallic / ionic
    lattices.  Identity when ``pack = 1`` (α-pairing floor).
    """
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * lean.GAMMA * (1.0 - float(pack))


def ionic_character_lattice_dress(ionic_character: float) -> float:
    """
    Lean ``ionicCharacterLatticeDress``: ``1 / (1 + (4/8)·γ·δ²)``.

    Mild nn contraction from bond ionic character (same steric-scale amp as
    molecular steric ρ).  Identity at δ² = 0.
    """
    return 1.0 / (
        1.0 + lean.STRONG_CHANNEL_FRACTION * lean.GAMMA / 8.0 * max(float(ionic_character), 0.0)
    )


def ionic_period_channel_steric_dress(z_cation: int, z_anion: int) -> float:
    """
    Lean ``ionicPeriodChannelStericDress``:
    ``1 / (1 + (4/8)·α·γ/8 · w_a · w_c)``.

    Period-2×period-2 alkali–halide contacts (LiF, ``w_a=w_c=1``) take a mild
    EM×monogamy steric contract; mixed/deeper pairs fade continuously via
    ``(2/P)^cap``.  Identity when either channel weight vanishes.
    """
    import hqiv_ionic_bond_network as ibn

    w_a = float(ibn.ionic_period_channel_weight(z_anion))
    w_c = float(ibn.ionic_period_channel_weight(z_cation))
    return 1.0 / (
        1.0
        + lean.STRONG_CHANNEL_FRACTION
        * lean.ALPHA
        * lean.GAMMA
        / 8.0
        * w_a
        * w_c
    )


def ionic_deep_cation_open_dress(z_cation: int, z_anion: int) -> float:
    """
    Lean ``ionicDeepCationOpenDress``:
    ``1 + (4/8)·(γ/8)·max(0, P_c/P_a − 1)·(1 − w_a)``.

    Deeper cations than a non-period-2 anion (KCl) mildly open nn; NaF
    (period-2 anion, ``w_a=1``) stays at identity so fluoride packing is
    not over-opened.
    """
    import hqiv_ionic_bond_network as ibn

    p_c = float(max(evs.chemical_period(int(z_cation)), 1))
    p_a = float(max(evs.chemical_period(int(z_anion)), 1))
    w_a = float(ibn.ionic_period_channel_weight(z_anion))
    excess = max(0.0, p_c / p_a - 1.0)
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * (lean.GAMMA / 8.0) * excess * (
        1.0 - w_a
    )


def ionic_rocksalt_lattice_dress(n_coord: int = 6) -> float:
    """Lean ``ionicRocksaltLatticeDress``."""
    sc = lean.STRONG_CHANNEL_FRACTION
    g = lean.GAMMA
    return (1.0 + n_coord * sc / 4.0) * (1.0 + g / 4.0)


def ionic_is_hydride_pair(z_i: int, z_j: int) -> bool:
    """Metal hydride: one nucleus is H (Z=1), the other is a donor metal."""
    import hqiv_selection_weights as sw

    if int(z_i) == 1 and sw.donor_weight(int(z_j)) > 0.5:
        return True
    if int(z_j) == 1 and sw.donor_weight(int(z_i)) > 0.5:
        return True
    return False


def ionic_hydride_lattice_dress() -> float:
    """
    Lean ``ionicHydrideLatticeDress``: ``1 + (4/8)·(γ/2)``.

    Metal hydrides (anion Z=1) are not alkali–halide rocksalt: the full
    ``(1+CN·strong/4)·(1+γ/4)`` over-elongates H⁻ contacts.  Half-monogamy
    open keeps the ionic-outside length near the condensed hydride scale.
    """
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * (lean.GAMMA / 2.0)


def ionic_hydride_melt_dress(z_anion: int) -> float:
    """
    Lean ``ionicHydrideMeltDress``: ``(1+α)/γ²`` when anion Z=1, else 1.

    Hydride lattice surplus is gas-scale; the rocksalt ``1/n_coord²`` melt
    slot under-binds H⁻ salts.  The monogamy/EM ratio ``(1+α)/γ²`` restores
    melt cohesive without a salt-name case.
    """
    if int(z_anion) != 1:
        return 1.0
    return (1.0 + lean.ALPHA) / (lean.GAMMA * lean.GAMMA)


def ionic_lattice_dress(z_i: int, z_j: int, *, n_coord: int = 6) -> float:
    """Hydride → mild dress; else rocksalt CN dress.  No salt-name cases."""
    if ionic_is_hydride_pair(z_i, z_j):
        return ionic_hydride_lattice_dress()
    return ionic_rocksalt_lattice_dress(n_coord)


def ionic_lattice_nearest_neighbor_bohr(
    z_i: int,
    z_j: int,
    *,
    n_coord: int = 6,
    c: float = 1.0,
) -> float:
    """Lean ``ionicLatticeNearestNeighborTarget`` (Bohr)."""
    m_i, _ = evs.electronic_compton_shells(z_i)
    m_j, _ = evs.electronic_compton_shells(z_j)
    pair = ctd.ionic_outside_contact_bond_length_bohr(m_i, z_i, m_j, z_j, c=c)
    return pair * ionic_lattice_dress(z_i, z_j, n_coord=n_coord)


def ionic_lattice_nearest_neighbor_angstrom(
    z_i: int,
    z_j: int,
    *,
    n_coord: int = 6,
    c: float = 1.0,
    packed: bool = True,
) -> float:
    """Lean ``ionicLatticeNearestNeighborTarget`` / Packed (Å)."""
    nn = ionic_lattice_nearest_neighbor_bohr(z_i, z_j, n_coord=n_coord, c=c) * BOHR_ANGSTROM
    if packed:
        import hqiv_selection_weights as sw

        ionic = float(sw.bond_ionic_character(z_i, z_j))
        # Orient by donor/acceptor spectrum (not Z order — KCl has Z_c > Z_a).
        if sw.donor_weight(z_i) >= sw.donor_weight(z_j):
            z_c, z_a = z_i, z_j
        else:
            z_c, z_a = z_j, z_i
        # Metal hydrides (anion Z=1): no nuclear-pack / period-channel steric —
        # H⁻ has no inert core; keep ionic-character softener only.
        if ionic_is_hydride_pair(z_i, z_j):
            return nn * ionic_character_lattice_dress(ionic)
        pack = math.sqrt(
            nuclear_packing_dress_for_z(z_i) * nuclear_packing_dress_for_z(z_j)
        )
        return (
            nn
            * pack
            * nuclear_packing_open_dress(pack)
            * ionic_character_lattice_dress(ionic)
            * ionic_period_channel_steric_dress(z_c, z_a)
            * ionic_deep_cation_open_dress(z_c, z_a)
        )
    return nn


# Close-packed metallic reference coordination (FCC CN=12).
METALLIC_CLOSE_PACK_COORD = 12


def metallic_fcc_packing_factor(n_coord: int) -> float:
    """Lean ``metallicFccPackingFactor``."""
    return (max(n_coord, 1) / 2.0) ** (1.0 / 3.0)


def metallic_period_channel_weight(z: int) -> float:
    """Lean ``metallicPeriodChannelWeight``: ``(2/P)^cap`` (period-2 → 1)."""
    period = max(evs.chemical_period(z), 1)
    return (2.0 / float(period)) ** CONSTRUCTIVE_VALLEY_CAP


def metallic_undercoord_open_dress(n_coord: int, *, period_weight: float = 0.0) -> float:
    """
    Lean ``metallicUndercoordOpenDress``:

    ``(CN_close / CN)^{γ·(1−w)·(1−γ²·δ_BCC) + (γ²/2)·w·δ_BCC}``

    At CN=12 the exponent collapses to ``γ·(1−w)`` (identity when w→1).
    At BCC (CN=8) a monogamy residual ``(γ²/2)·w`` keeps period-2 alkalis
    (Li, w=1) from freezing the undercoord open to 1, while the fade term
    is damped by ``(1−γ²)`` so period-3 BCC (Na) does not over-open —
    first-principles, not an alkali Z-case.
    """
    cn = max(int(n_coord), 1)
    w = max(0.0, min(1.0, float(period_weight)))
    bcc = 0.0 if cn == METALLIC_CLOSE_PACK_COORD else 1.0
    exponent = (
        lean.GAMMA * (1.0 - w) * (1.0 - lean.GAMMA * lean.GAMMA * bcc)
        + (lean.GAMMA * lean.GAMMA / 2.0) * w * bcc
    )
    return (float(METALLIC_CLOSE_PACK_COORD) / float(cn)) ** exponent


def metallic_pblock_valence_open_dress(
    z: int,
    *,
    n_coord: int = 12,
    period_weight: float | None = None,
) -> float:
    """
    Lean ``metallicPblockValenceOpenDress``:

    ``1 + (4/8)·γ·((cap−1)/12)·(1−w)·(CN/12)`` for directional p-block metals
    (``1 < bonding_capacity < 4``).  Excess valence above the alkali monovalent
    floor opens the FCC contact; alkali (cap=1) and transition (cap=0) stay at
    identity — they use undercoord / peel spines instead.
    """
    import hqiv_particle_shell_structure as pss

    cap = int(pss.bonding_capacity(int(z)))
    if not (1 < cap < 4):
        return 1.0
    w = (
        metallic_period_channel_weight(z)
        if period_weight is None
        else max(0.0, min(1.0, float(period_weight)))
    )
    close = float(max(int(n_coord), 1)) / float(METALLIC_CLOSE_PACK_COORD)
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * lean.GAMMA * (
        float(cap - 1) / float(METALLIC_CLOSE_PACK_COORD)
    ) * (1.0 - w) * close


def _prev_d_occupancy(z: int) -> int:
    """Electrons in ``(n−1)d`` of the Madelung configuration."""
    import hqiv_atom_construction as ac

    cfg = ac.electron_configuration(int(z))
    if not cfg:
        return 0
    top_n = max(n for n, _l in cfg)
    return sum(1 for n, l in cfg if n == top_n - 1 and l == 2)


def metallic_d10_core_elongation(
    z: int,
    *,
    period_weight: float | None = None,
) -> float:
    """
    Lean ``metallicD10CoreElongation``:

    ``1 + (4/8)·α·γ·(1−w)·max(osp−1, 0)`` when ``(n−1)d`` is closed (10).

    Post-d metals (Zn/Ga) carry a filled d¹⁰ core that elongates the nested/φ
    blend; open-d peel metals and main-group stay at identity.
    """
    import hqiv_particle_shell_structure as pss

    if _prev_d_occupancy(z) != 10:
        return 1.0
    w = (
        metallic_period_channel_weight(z)
        if period_weight is None
        else max(0.0, min(1.0, float(period_weight)))
    )
    osp = float(pss.outer_principal_valence(int(z)))
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * lean.ALPHA * lean.GAMMA * (
        1.0 - w
    ) * max(osp - 1.0, 0.0)


def metallic_open_d_fade(d_prev: int) -> float:
    """
    Lean ``metallicOpenDFade``: ``max(0, (10 − d)/10)`` for ``0 < d < 9``.

    Mid-transition peel (Fe d=6 → 0.4); Ni (d=8 → 0.2); main-group ``d=0``,
    Cu Madelung ``d≥9``, and closed ``d¹⁰`` stay at identity.
    """
    d = int(d_prev)
    if not (0 < d < 9):
        return 0.0
    return max(0.0, (10.0 - float(d)) / 10.0)


def metallic_open_d_peel_contract(
    z: int,
    *,
    period_weight: float | None = None,
) -> float:
    """
    Lean ``metallicOpenDPeelContract``:

    ``1 / (1 + (4/8)·α·γ·(n_peel/Z)·(1−w)·fade(d))`` with
    ``fade = max(0, (10−d)/10)``.

    Mid-transition peel (Fe) contracts nn; Ni (d=8) gets a partial fade;
    closed d¹⁰ stays at identity.
    """
    d_prev = _prev_d_occupancy(z)
    fade = metallic_open_d_fade(d_prev)
    if fade <= 0.0:
        return 1.0
    import hqiv_metallic_bond_network as mbn

    frag = mbn.MetalFragment("M", int(z), int(z))
    w = (
        metallic_period_channel_weight(z)
        if period_weight is None
        else max(0.0, min(1.0, float(period_weight)))
    )
    peel_frac = float(frag.n_peel) / float(max(int(z), 1))
    return 1.0 / (
        1.0
        + lean.STRONG_CHANNEL_FRACTION
        * lean.ALPHA
        * lean.GAMMA
        * peel_frac
        * (1.0 - w)
        * fade
    )


def metallic_deep_bcc_open_dress(
    z: int,
    *,
    n_coord: int = 8,
    period_weight: float | None = None,
) -> float:
    """
    Lean ``metallicDeepBccOpenDress``:

    ``1 + (4/8)·γ·max(0, P−3)/P`` on BCC (CN=8).

    Period-4+ alkalis (K) open beyond the Na undercoord spine; period ≤ 3
    stay at identity.
    """
    if int(n_coord) != 8:
        return 1.0
    period = float(max(evs.chemical_period(int(z)), 1))
    excess = max(0.0, period - 3.0) / period
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * lean.GAMMA * excess


def metallic_alkaline_earth_open_dress(
    z: int,
    *,
    period_weight: float | None = None,
) -> float:
    """
    Lean ``metallicAlkalineEarthOpenDress``:

    ``1 + (4/8)·(γ²)·(1−w)/cap`` for ``cap = 2`` without a filled d¹⁰ core.

    Mild monogamy reopen for Mg-class divalent metals; Zn (d¹⁰) uses the
    d¹⁰ elongation instead (no double count).
    """
    import hqiv_particle_shell_structure as pss

    cap = int(pss.bonding_capacity(int(z)))
    if cap != 2 or _prev_d_occupancy(z) == 10:
        return 1.0
    w = (
        metallic_period_channel_weight(z)
        if period_weight is None
        else max(0.0, min(1.0, float(period_weight)))
    )
    return 1.0 + lean.STRONG_CHANNEL_FRACTION * (lean.GAMMA * lean.GAMMA) * (
        1.0 - w
    ) / float(cap)


def metallic_lattice_nearest_neighbor_bohr(
    z: int,
    *,
    n_coord: int = 12,
    c: float = 1.0,
) -> float:
    """Lean ``metallicLatticeNearestNeighborTarget`` (Bohr)."""
    m_s, _ = evs.electronic_compton_shells(z)
    period = max(evs.chemical_period(z), 1)
    r = ctd.nested_wf_covalent_radius_bohr(m_s, z, c)
    pack = metallic_fcc_packing_factor(n_coord)
    return (
        2.0
        * r
        * (1.0 + lean.ALPHA)
        * pack
        * (float(period) ** 2 / CONSTRUCTIVE_VALLEY_CAP)
    )


def metallic_lattice_nearest_neighbor_angstrom(
    z: int,
    *,
    n_coord: int = 12,
    c: float = 1.0,
) -> float:
    return metallic_lattice_nearest_neighbor_bohr(z, n_coord=n_coord, c=c) * BOHR_ANGSTROM


def metallic_phi_pack_nearest_neighbor_angstrom(
    z: int,
    *,
    n_coord: int = 12,
) -> float:
    """
    φ(m)/Z close-packing branch (network spine).

    Period channel ``w=(2/P)^cap``: period-2 → homonuclear dimer dress;
    deeper periods → ``max(homo, lattice)``.  No alkali Z-set cases.
    Length packing uses the close-pack reference (CN=12); under-coordination
    is applied later via ``metallic_undercoord_open_dress``.
    """
    m_s, _ = evs.electronic_compton_shells(z)
    period = max(evs.chemical_period(z), 1)
    pack = metallic_fcc_packing_factor(METALLIC_CLOSE_PACK_COORD)
    cap = CONSTRUCTIVE_VALLEY_CAP
    phi_m = 2.0 * (float(m_s) + 1.0)
    homo_ang = ctd.homonuclear_bond_equilibrium_bohr(z) * BOHR_ANGSTROM
    homo_dressed = homo_ang * (1.0 + lean.GAMMA / 8.0)
    lattice_ang = (
        phi_m
        / float(z)
        * pack
        * (1.0 + lean.ALPHA)
        * BOHR_ANGSTROM
        * 2.0
        * (float(period) ** 2 / cap)
    )
    w = metallic_period_channel_weight(z)
    # Period-2 homo residual: mild open on the φ/homo branch at w→1
    # (Lean ``metallicPeriod2HomoResidual``).
    homo_dressed *= 1.0 + lean.STRONG_CHANNEL_FRACTION * (lean.GAMMA * lean.GAMMA / 8.0) * w
    if w >= 1.0 - 1e-12:
        return homo_dressed
    return max(homo_dressed, lattice_ang)


def metallic_unified_nearest_neighbor_angstrom(
    z: int,
    *,
    n_coord: int = 12,
    c: float = 1.0,
    packed: bool = True,
) -> float:
    """
    Unified metallic nn: α-weighted blend of nested-WF and φ-pack targets,

    ``nn = nested^α · φ^(1−α) · undercoord · pblock · d¹⁰ · peel · deep-BCC
         · alkaline-earth · (pack × open)``,

    Length packing is always evaluated at the close-pack reference (CN=12);
    Bravais under-coordination (BCC CN=8) opens via ``(12/CN)^{γ·(1−w)}``;
    p-block metals open via excess-over-alkali ``(cap−1)``; post-d d¹⁰ and
    open-d peel are Madelung-keyed.  Families keyed by shell capacity, not
    metal-name cases.
    """
    # Nested / φ length packing at close-pack reference; CN enters only via open dress.
    nn_nested = metallic_lattice_nearest_neighbor_angstrom(
        z, n_coord=METALLIC_CLOSE_PACK_COORD, c=c
    )
    nn_phi = metallic_phi_pack_nearest_neighbor_angstrom(
        z, n_coord=METALLIC_CLOSE_PACK_COORD
    )
    nested = max(nn_nested, 1e-12)
    phi = max(nn_phi, 1e-12)
    uni = (nested ** lean.ALPHA) * (phi ** (1.0 - lean.ALPHA))
    w = metallic_period_channel_weight(z)
    uni *= metallic_undercoord_open_dress(n_coord, period_weight=w)
    uni *= metallic_pblock_valence_open_dress(
        z, n_coord=n_coord, period_weight=w
    )
    uni *= metallic_d10_core_elongation(z, period_weight=w)
    uni *= metallic_open_d_peel_contract(z, period_weight=w)
    uni *= metallic_deep_bcc_open_dress(z, n_coord=n_coord, period_weight=w)
    uni *= metallic_alkaline_earth_open_dress(z, period_weight=w)
    if packed:
        pack = nuclear_packing_dress_for_z(z)
        return uni * pack * nuclear_packing_open_dress(pack)
    return uni


def closed_atomic_mass_amu(z: int, *, c: float = 1.0) -> float:
    """Neutral atom mass from ``atom_closed_mass_mev`` (Aufbau discharge path)."""
    return ac.atom_closed_mass_mev(z, c=c) / MEV_PER_AMU


def mass_reliable_for_crystal(z: int) -> bool:
    """Coulomb A(Z) covers the crystal panel through period 4; still no tabulated A."""
    return True


def covalent_network_inert_core_elongation(z: int) -> float:
    """Lean ``covalentNetworkInertCoreElongation`` with bonding-capacity floor."""
    period = max(evs.chemical_period(z), 1)
    if period <= 2 or z <= 0:
        return 1.0
    import hqiv_particle_shell_structure as pss

    cap = pss.bonding_capacity(z)
    n_participate = max(cap, 4) if cap <= 0 else max(cap, 1)
    return float(z) / float(n_participate)


def covalent_network_bond_length_angstrom(
    z: int,
    *,
    coordination: int = 4,
    packed: bool = False,
) -> float:
    """
    Diamond-cubic bond length from ``AllotropeNetwork`` carrier × inert-core elongation.

    Nuclear packing dress defaults **off**: covalent-network bonds are electronic /
    allotrope-keyed.  P/N packing applies to metallic and ionic lattice contacts.
    Pass ``packed=True`` only for explicit P/N diagnostics.
    """
    import hqiv_allotrope_network as an

    base = an.network_bond_length_angstrom(z, coordination)
    bond = base * covalent_network_inert_core_elongation(z)
    if packed:
        return bond * nuclear_packing_dress_for_z(z)
    return bond


def clausius_mossotti_optical_weight(n_dielectric: float) -> float:
    """Clausius–Mossotti participation ``(n²−1)/(n²+2)`` from curvature dielectric."""
    n2 = max(float(n_dielectric), 1.0) ** 2
    return (n2 - 1.0) / (n2 + 2.0)


def covalent_network_period_channel_weight(z: int) -> float:
    """
    Continuous electronic-channel weight ``(2/P)^{constructiveValleyCap}``.

    Period-2 carriers sit at ``w = 1`` (full EM×open).  Deeper periods fade
    continuously onto the nuclear/optical branch — no hard ``length_reliable`` gate.
    """
    period = max(evs.chemical_period(z), 1)
    return (2.0 / float(period)) ** lean.CONSTRUCTIVE_VALLEY_CAP


def covalent_network_steric_fade_dress(period_weight: float, cm_weight: float) -> float:
    """
    Lean ``covalentNetworkStericFadeDress``:
    ``1 / (1 + (4/8)·(γ²/8)·(1−w)·CM)``.

    Mild nuclear/optical steric contract on deeper covalent networks (Si/Ge).
    Identity at period-2 (``w=1``).
    """
    w = max(0.0, min(1.0, float(period_weight)))
    cm = max(0.0, min(1.0, float(cm_weight)))
    return 1.0 / (
        1.0
        + lean.STRONG_CHANNEL_FRACTION
        * (lean.GAMMA * lean.GAMMA / 8.0)
        * (1.0 - w)
        * cm
    )


def covalent_network_em_packing_dress(
    z: int,
    *,
    coordination: int = 4,
    packed: bool = False,
    em_feedback: bool = True,
) -> dict[str, float | bool | dict[str, float] | None]:
    """
    Generic covalent-network contact dress (no period / motif case branch):

    ``r = r_bare · pack^{(1−w)(2−CM)} · em^{α(w+(1−w)CM)} · open^(w²)
         / (1 + (4/8)·(γ²/8)·(1−w)·CM)``

    with ``w = (2/P)^{constructiveValleyCap}``, ``CM = (n²−1)/(n²+2)``,
    ``pack = nuclearPackingDress``, and ``open`` the two-sided open-channel scale.
    Open enters as ``w²`` so period-2 (``w=1``) keeps full open dress while
    deeper periods fade open faster than the EM/nuclear blend — continuous, no gate.
    The steric fade is identity at period-2 (``w=1``) and mild on Si/Ge.
    """
    import hqiv_allotrope_network as an
    import hqiv_molecular_spectroscopy as ms
    import hqiv_two_way_feedback_dynamics as twf

    r_bare = covalent_network_bond_length_angstrom(
        z, coordination=coordination, packed=packed
    )
    order = float(an.network_bond_order(z, coordination))
    reliable = bool(an.length_is_reliable(z))
    projection = twf.shell_anchor_projection(
        capacity=float(coordination),
        bond_order=order,
        ionic_character=0.0,
    )
    packing = float(projection.network_open_channel_packing_scale)
    w_period = covalent_network_period_channel_weight(z)
    if not em_feedback:
        return {
            "Z": z,
            "coordination": coordination,
            "bond_order": order,
            "length_reliable": reliable,
            "em_feedback_applied": False,
            "period_channel_weight": w_period,
            "bond_length_bare_angstrom": r_bare,
            "bond_length_angstrom": float(r_bare),
            "network_open_channel_packing_scale": packing,
            "em_dress": {"em": 1.0, "note": "feedback off"},
            "feedback_scales": None,
            "shell_projection": projection.to_dict(),
        }

    n = ms.curvature_dielectric_ratio(z, z)
    feedback = twf.em_feedback_from_dielectric(n)
    cm = clausius_mossotti_optical_weight(n)
    pack = nuclear_packing_dress_for_z(z)
    # Electronic branch weight w; nuclear/optical complement (1−w).
    pack_pow = (1.0 - w_period) * (2.0 - cm)
    em_pow = lean.ALPHA * (w_period + (1.0 - w_period) * cm)
    open_pow = w_period * w_period
    steric = covalent_network_steric_fade_dress(w_period, cm)
    r = (
        r_bare
        * (pack ** pack_pow)
        * (feedback.em ** em_pow)
        * (packing ** open_pow)
        * steric
    )
    em_info = {
        "n_curvature_dielectric": n,
        "clausius_mossotti_weight": cm,
        "period_channel_weight": w_period,
        "pack": pack,
        "pack_power": pack_pow,
        "em": feedback.em,
        "em_power": em_pow,
        "open_power": open_pow,
        "steric_fade": steric,
        "r_scale": r / max(r_bare, 1e-30),
        "rho_scale": (r / max(r_bare, 1e-30)) ** -3.0,
        "sigma_scale": (r / max(r_bare, 1e-30)) ** -2.0,
    }
    return {
        "Z": z,
        "coordination": coordination,
        "bond_order": order,
        "length_reliable": reliable,
        "em_feedback_applied": True,
        "period_channel_weight": w_period,
        "bond_length_bare_angstrom": r_bare,
        "bond_length_angstrom": float(r),
        "network_open_channel_packing_scale": packing,
        "em_dress": em_info,
        "feedback_scales": feedback.to_dict(),
        "shell_projection": projection.to_dict(),
    }

def diamond_cubic_lattice_parameter_angstrom(bond_length_ang: float) -> float:
    """Conventional diamond-cubic cell edge ``a = 4 r / √3``."""
    return 4.0 * bond_length_ang / math.sqrt(3.0)


def diamond_cubic_density_g_cm3(mass_amu: float, bond_length_ang: float) -> float:
    """ρ from 8 atoms per conventional diamond cell."""
    a_ang = diamond_cubic_lattice_parameter_angstrom(bond_length_ang)
    a_cm = a_ang * 1e-8
    vol_cm3 = a_cm**3
    mass_g = 8.0 * mass_amu / AVOGADRO
    return float(mass_g / max(vol_cm3, 1e-30))


def rocksalt_lattice_parameter_angstrom(nearest_neighbor_ang: float) -> float:
    """Rocksalt conventional cell edge ``a = 2 r_nn``."""
    return 2.0 * nearest_neighbor_ang


def rocksalt_formula_units_per_cell() -> int:
    return 4


def fcc_lattice_parameter_angstrom(nearest_neighbor_ang: float) -> float:
    """FCC cell edge ``a = r_nn · √2``."""
    return nearest_neighbor_ang * math.sqrt(2.0)


def bcc_lattice_parameter_angstrom(nearest_neighbor_ang: float) -> float:
    """BCC cell edge ``a = 2 r_nn / √3`` (Lean ``bccLatticeParameter``)."""
    return 2.0 * nearest_neighbor_ang / math.sqrt(3.0)


def metallic_is_hcp_candidate(z: int) -> bool:
    """
    Lean ``metallicIsHcpCandidate``: ``cap = 2`` without a filled d¹⁰ core.

    Mg-class alkaline earths take ideal HCP topology; Zn (d¹⁰) stays FCC + d¹⁰
    elongation (no double topology count).
    """
    import hqiv_particle_shell_structure as pss

    return int(pss.bonding_capacity(int(z))) == 2 and _prev_d_occupancy(z) != 10


def metallic_bravais_kind(z: int, *, n_coord: int | None = None) -> str:
    """
    Bravais label from coordination + capacity (no metal-name cases).

    CN=8 → bcc; cap=2 ∧ ¬d¹⁰ → hcp; else fcc.
    """
    import hqiv_metallic_bond_network as mbn

    cn = int(n_coord) if n_coord is not None else int(mbn.metallic_coordination(z))
    if cn == 8:
        return "bcc"
    if metallic_is_hcp_candidate(z):
        return "hcp"
    return "fcc"


def metallic_bravais_from_coordination(
    n_coord: int, *, bravais: str | None = None
) -> tuple[int, float]:
    """
    Atoms/cell and ``a/r_nn`` from coordination / Bravais (no metal-name cases).

    CN=8 → BCC (2, 2/√3); HCP → (6, 1) basal ``a = r_nn``; else FCC (4, √2).

    Ideal HCP packing fraction equals FCC, so density from nn matches FCC when
    volume uses ``V = a²·c·√3/2`` with ``c/a = √(8/3)`` (see ``metallic_density``).
    """
    kind = (bravais or "").lower()
    if int(n_coord) == 8 or kind == "bcc":
        return 2, 2.0 / math.sqrt(3.0)
    if kind == "hcp":
        return 6, 1.0
    return 4, math.sqrt(2.0)


def metallic_lattice_parameter_angstrom(
    nearest_neighbor_ang: float,
    *,
    n_coord: int = 12,
    bravais: str | None = None,
) -> float:
    """Conventional cell edge (cubic) or basal ``a`` (HCP) from nn + Bravais."""
    _, k = metallic_bravais_from_coordination(n_coord, bravais=bravais)
    return float(k) * float(nearest_neighbor_ang)


def fcc_density_g_cm3(mass_amu: float, nearest_neighbor_ang: float, *, atoms_per_cell: int = 4) -> float:
    a_ang = fcc_lattice_parameter_angstrom(nearest_neighbor_ang)
    a_cm = a_ang * 1e-8
    vol_cm3 = a_cm**3
    mass_g = atoms_per_cell * mass_amu / AVOGADRO
    return float(mass_g / max(vol_cm3, 1e-30))


def metallic_density_g_cm3(
    mass_amu: float,
    nearest_neighbor_ang: float,
    *,
    n_coord: int = 12,
    bravais: str | None = None,
    z: int | None = None,
) -> float:
    """
    Metallic solid density from nn + Bravais topology (Lean ``metallicDensity``).

    BCC/FCC: ``ρ = N · M / (N_A · (k · r_nn)³)``.
    Ideal HCP: same packing fraction as FCC (``V/atom = r_nn³ · √2 / 2``).
    """
    kind = bravais
    if kind is None and z is not None:
        kind = metallic_bravais_kind(z, n_coord=n_coord)
    if (kind or "").lower() == "hcp":
        # Ideal HCP: V/atom = r³ · √2 / 2  (= FCC).
        vol_atom_ang3 = (float(nearest_neighbor_ang) ** 3) * math.sqrt(2.0) / 2.0
        vol_cm3 = vol_atom_ang3 * 1e-24
        mass_g = float(mass_amu) / AVOGADRO
        return float(mass_g / max(vol_cm3, 1e-30))
    n_atoms, k = metallic_bravais_from_coordination(n_coord, bravais=kind)
    a_ang = float(k) * float(nearest_neighbor_ang)
    a_cm = a_ang * 1e-8
    vol_cm3 = a_cm**3
    mass_g = float(n_atoms) * float(mass_amu) / AVOGADRO
    return float(mass_g / max(vol_cm3, 1e-30))


def expected_compton_triplet_for_crystal(
    *,
    crystal_kind: str,
    z_values: tuple[int, ...] = (),
    molecule: str = "",
) -> tuple[int, int, int]:
    """Routed Compton triplet for crystal panel species (not the molecular 4-3-1 default)."""
    from fragment_aware_bonded_horizon import FragmentConfig

    if crystal_kind == "ionic" and len(z_values) >= 2:
        from fragment_aware_bonded_horizon import FragmentConfig

        frags = (
            FragmentConfig("c", z_values[0], z_values[0]),
            FragmentConfig("a", z_values[1], z_values[1]),
        )
        return evs.chemistry_compton_triplet(frags)
    if crystal_kind in ("metallic", "covalent_network") and z_values:
        z = z_values[0]
        m_s, _ = evs.electronic_compton_shells(z)
        return (m_s, m_s, m_s)
    if molecule:
        import hqiv_dynamic_binding_chart as chart

        row = next(
            (b for b in chart.GMTKN55_SUITE if b.name.upper() == molecule.upper()),
            None,
        )
        if row is not None:
            return chart.chemistry_compton_triplet(row)
    return (4, 3, 1)


def expected_contact_xi_for_crystal(
    *,
    crystal_kind: str,
    z_values: tuple[int, ...] = (),
    molecule: str = "",
) -> float:
    triplet = expected_compton_triplet_for_crystal(
        crystal_kind=crystal_kind,
        z_values=z_values,
        molecule=molecule,
    )
    return lean.xi_from_compton_triplet(triplet)


def derive_crystal_kind(z_values: tuple[int, ...]) -> str:
    """
    Crystal family from bonding capacity / donor×acceptor (no panel labels).

    * empty Z → molecular
    * binary with ionic-route weight > 1/2 → ionic
    * single Z metal (capacity predicate) → metallic
    * single Z with bonding capacity 4 → covalent_network
    * else molecular
    """
    zs = tuple(int(z) for z in z_values)
    if not zs:
        return "molecular"
    if len(zs) >= 2:
        import hqiv_selection_weights as sw

        if float(sw.ionic_route_weight(zs[0], zs[1])) > 0.5:
            return "ionic"
        return "molecular"
    z = zs[0]
    import hqiv_metallic_bond_network as mbn
    import hqiv_particle_shell_structure as pss

    if mbn.is_metallic_element(z):
        return "metallic"
    if int(pss.bonding_capacity(z)) == 4:
        return "covalent_network"
    return "molecular"


def crystal_nearest_neighbor_angstrom(entry_z: tuple[int, ...], crystal_kind: str) -> float:
    """Primary nn contact for ionic, metallic, or covalent-network panel entries."""
    if crystal_kind == "ionic" and len(entry_z) >= 2:
        return ionic_lattice_nearest_neighbor_angstrom(entry_z[0], entry_z[1])
    if crystal_kind == "metallic" and len(entry_z) >= 1:
        import hqiv_metallic_bond_network as mbn

        n_coord = mbn.metallic_coordination(entry_z[0])
        return metallic_unified_nearest_neighbor_angstrom(entry_z[0], n_coord=n_coord)
    if crystal_kind == "covalent_network" and len(entry_z) >= 1:
        return covalent_network_bond_length_angstrom(entry_z[0], coordination=4)
    raise ValueError(f"unsupported crystal kind {crystal_kind!r} for Z={entry_z}")


def comparison_regime_for_species(
    name: str,
    *,
    z_i: int | None = None,
    z_j: int | None = None,
) -> str:
    """
    Tag comparison rows: gas-phase diatomic spectroscopy vs solid lattice.

    Crystal-panel entries use solid-lattice contacts.  Diatomic spectroscopy rows
    stay gas/vapor even when their bond has ionic character; ionicity is a channel
    weight, not a comparison-regime override.
    """
    key = name.upper()
    if key in ("NACL", "SI", "GE", "CU"):
        return "solid_lattice"
    return "gas_vapor"
