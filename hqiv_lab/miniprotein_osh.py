"""
OSHoracle miniprotein fold path — contact network matrix + sparse carrier refinement.

Lean mirrors:
  ``AtomEnergyOSHoracleBridge``, ``AdditiveFieldAndTorque``, ``OSHoracleHQIVNative``.

Replaces unconstrained Cα Jacobi and complements NeRF coordinate search: tertiary
closure is driven by sparse register evolution and contact-weighted mean-field torque,
with NeRF as the geometry decoder.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any

from hqiv_lab.carrier_peaking import (
    REFERENCE_M_DEFAULT,
    SparseKet,
    apply_gate_sparse_hqiv_native,
    decode_idx,
    detect_flipped_kets,
    local_maxima_bins,
    prune_to_flipped,
    sector_histogram_from_indices,
    sparse_basis_card,
    wrap_idx,
)
from hqiv_lab.miniprotein_backbone import (
    BackboneAtomState,
    SecondaryStructure,
    Vec3,
    dihedral_for_ss,
    place_backbone_atom_state,
    place_ca_trace,
)
from hqiv_lab.miniprotein_atom_sites import (
    AtomContact,
    AtomSiteRef,
    dress_atom_contact_targets,
    expand_atom_contacts_with_backbone,
    flat_site_list,
    residue_from_flat_index,
    site_coord,
    site_flat_index,
    tertiary_to_atom_contacts,
    SITE_KINDS_PER_RESIDUE,
)
from hqiv_lab.miniprotein_contacts import TertiaryContact

# Heavy-atom Z proxy for Compton shell ladder (backbone chemistry readout).
_AA_Z: dict[str, int] = {
    "G": 6,
    "A": 6,
    "S": 6,
    "C": 6,
    "V": 6,
    "L": 6,
    "I": 6,
    "P": 6,
    "F": 6,
    "Y": 6,
    "W": 6,
    "H": 7,
    "N": 7,
    "Q": 7,
    "D": 6,
    "E": 6,
    "K": 7,
    "R": 7,
    "M": 6,
}


def available_modes(m: int) -> float:
    return 4.0 * (m + 2) * (m + 1)


def phi_of_shell(m: int) -> float:
    return 2.0 * (m + 1)


def lattice_full_mode_energy(m: int) -> float:
    return available_modes(m) * (phi_of_shell(m) / 2.0)


def residue_compton_shell(aa: str) -> int:
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_electronic_valence_shells as evs

    z = _AA_Z.get(aa.upper(), 6)
    m_s, _ = evs.electronic_compton_shells(z)
    return m_s


def shells_for_sequence(sequence: str) -> list[int]:
    return [residue_compton_shell(aa) for aa in sequence]


def register_L(n_residues: int, n_bins: int) -> int:
    """Harmonic cutoff so ``n_residues × n_bins²`` slots fit injectively (mod card)."""
    slots = max(1, n_residues) * n_bins * n_bins
    return max(11, int(math.ceil(math.sqrt(slots))) - 1)


@dataclass(frozen=True)
class ContactPairWeight:
    i: int
    j: int
    target_angstrom: float
    weight: float
    kind: str


@dataclass(frozen=True)
class AtomSitePairWeight:
    i_flat: int
    j_flat: int
    i_residue: int
    j_residue: int
    target_angstrom: float
    weight: float
    kind: str


@dataclass(frozen=True)
class AtomContactNetworkMatrix:
    """Sparse atom-site network (diagonal site energies + contact pair weights)."""

    n_residues: int
    n_sites: int
    shells: tuple[int, ...]
    site_energy: tuple[float, ...]
    site_shells: tuple[int, ...]
    pairs: tuple[AtomSitePairWeight, ...]

    def to_dict(self) -> dict[str, Any]:
        return {
            "n_residues": self.n_residues,
            "n_sites": self.n_sites,
            "trace_site_energy": sum(self.site_energy),
            "n_pairs": len(self.pairs),
            "shells": list(self.shells),
        }


@dataclass(frozen=True)
class ContactNetworkMatrix:
    """Diagonal site energies + contact pair weights (OSH mean-field carrier)."""

    n: int
    shells: tuple[int, ...]
    site_energy: tuple[float, ...]
    pairs: tuple[ContactPairWeight, ...]

    def to_dict(self) -> dict[str, Any]:
        return {
            "n": self.n,
            "trace_site_energy": sum(self.site_energy),
            "n_pairs": len(self.pairs),
            "shells": list(self.shells),
        }


def _site_shell_for_kind(kind: str, residue_shell: int) -> int:
    """Atom-site Compton shell proxy (O/N use valence Z=7/8 ladder)."""
    if kind == "O":
        return 8
    if kind == "N":
        return 7
    if kind == "SC":
        return residue_shell
    return residue_shell


def build_atom_contact_network_matrix(
    sequence: str,
    atom_contacts: tuple[AtomContact, ...],
    state: BackboneAtomState,
    *,
    shells: list[int] | None = None,
) -> AtomContactNetworkMatrix:
    """Build sparse atom-site OSH carrier matrix from ``AtomContact`` edges."""
    sh = tuple(shells if shells is not None else shells_for_sequence(sequence))
    n = len(sequence)
    sites_per = 5
    n_sites = n * sites_per
    site_energy: list[float] = []
    site_shells: list[int] = []
    for r in range(n):
        rs = sh[r]
        for kind in ("N", "CA", "C", "O", "SC"):
            ss = _site_shell_for_kind(kind, rs)
            site_shells.append(ss)
            site_energy.append(lattice_full_mode_energy(ss))
    pairs: list[AtomSitePairWeight] = []
    for c in atom_contacts:
        i_flat = site_flat_index(c.i.residue, c.i.kind, n)
        j_flat = site_flat_index(c.j.residue, c.j.kind, n)
        w = 1.0 / max(c.target_angstrom, 0.5)
        pairs.append(
            AtomSitePairWeight(
                i_flat,
                j_flat,
                c.i.residue,
                c.j.residue,
                c.target_angstrom,
                w,
                c.kind,
            )
        )
    return AtomContactNetworkMatrix(
        n_residues=n,
        n_sites=n_sites,
        shells=sh,
        site_energy=tuple(site_energy),
        site_shells=tuple(site_shells),
        pairs=tuple(pairs),
    )


def build_contact_network_matrix(
    sequence: str,
    contacts: tuple[TertiaryContact, ...],
    *,
    shells: list[int] | None = None,
) -> ContactNetworkMatrix:
    sh = tuple(shells if shells is not None else shells_for_sequence(sequence))
    n = len(sequence)
    site = tuple(lattice_full_mode_energy(m) for m in sh)
    pairs: list[ContactPairWeight] = []
    for c in contacts:
        w = 1.0 / max(c.target_angstrom, 0.5)
        pairs.append(ContactPairWeight(c.i, c.j, c.target_angstrom, w, c.kind))
    return ContactNetworkMatrix(n=n, shells=sh, site_energy=site, pairs=tuple(pairs))


def _dist(a: Vec3, b: Vec3) -> float:
    dx = b[0] - a[0]
    dy = b[1] - a[1]
    dz = b[2] - a[2]
    return math.sqrt(dx * dx + dy * dy + dz * dz)


def contact_sse(
    sequence: str,
    ca: list[Vec3],
    contacts: tuple[TertiaryContact, ...],
    *,
    ss: list[str] | None = None,
    macro_ricci_soft: bool = False,
) -> float:
    from hqiv_lab.miniprotein_closure import _contact_sse

    return _contact_sse(
        sequence,
        ca,
        contacts,
        None,
        ss=ss,
        macro_ricci_soft=macro_ricci_soft,
    )


def residue_violation_scores(
    sequence: str,
    ca: list[Vec3],
    contacts: tuple[TertiaryContact, ...],
    *,
    ss: list[str] | None = None,
    macro_ricci_soft: bool = False,
) -> list[float]:
    from hqiv_lab.macro_ricci_flow import macro_ricci_soft_contact_target
    from hqiv_lab.residue_site_physics import macro_ricci_system_dress_amplitude

    n = len(ca)
    scores = [0.0] * n
    system_amp = (
        macro_ricci_system_dress_amplitude(sequence, contacts, ca, ss)
        if macro_ricci_soft
        else 0.0
    )
    for c in contacts:
        d = _dist(ca[c.i], ca[c.j])
        target = (
            macro_ricci_soft_contact_target(
                c, sequence, ca, ss, contacts, system_amp=system_amp
            )
            if macro_ricci_soft
            else c.target_angstrom
        )
        err2 = (d - target) ** 2
        scores[c.i] += err2
        scores[c.j] += err2
    return scores


def atom_contact_sse(
    state: BackboneAtomState,
    atom_contacts: tuple[AtomContact, ...],
    *,
    weights: tuple[float, ...] | None = None,
) -> float:
    """Squared distance error on sparse atom-site contact graph."""
    sse = 0.0
    for k, c in enumerate(atom_contacts):
        pi = site_coord(state, c.i)
        pj = site_coord(state, c.j)
        d = _dist(pi, pj)
        delta = d - c.target_angstrom
        w = 1.0 if weights is None else weights[k]
        sse += w * delta * delta
    return sse


def atom_violation_scores(
    state: BackboneAtomState,
    atom_contacts: tuple[AtomContact, ...],
) -> list[float]:
    """Per-residue violation score aggregated from atom-site contacts."""
    n = state.n_residues
    scores = [0.0] * n
    for c in atom_contacts:
        pi = site_coord(state, c.i)
        pj = site_coord(state, c.j)
        err2 = (_dist(pi, pj) - c.target_angstrom) ** 2
        scores[c.i.residue] += err2
        scores[c.j.residue] += err2
    return scores


def additive_field_at_atom_sites(
    state: BackboneAtomState,
    network: AtomContactNetworkMatrix,
) -> list[float]:
    """Mean-field torque driver on flat atom-site indices."""
    n_sites = network.n_sites
    field = [0.0] * n_sites
    sites = flat_site_list(state)
    coords = [p for _, p in sites]
    for p in network.pairs:
        pi = coords[p.i_flat]
        pj = coords[p.j_flat]
        d = _dist(pi, pj)
        if d < 1e-12:
            continue
        viol = (d - p.target_angstrom) * p.weight
        field[p.i_flat] += viol / d
        field[p.j_flat] -= viol / d
    for i in range(n_sites):
        field[i] += network.site_energy[i] * 1e-9
    return field


def residue_field_from_atom_field(
    atom_field: list[float],
    n_residues: int,
) -> list[float]:
    """Aggregate flat atom-site field back to residue dihedral drivers."""
    n_kinds = len(SITE_KINDS_PER_RESIDUE)
    out = [0.0] * n_residues
    for flat_idx, val in enumerate(atom_field):
        r = flat_idx // n_kinds
        if r < n_residues:
            out[r] += val
    return out


def prepare_atom_contacts(
    contacts: tuple[TertiaryContact, ...],
    state: BackboneAtomState,
    *,
    temperature_k: float | None = None,
    include_backbone: bool = True,
) -> tuple[AtomContact, ...]:
    """Tertiary → atom contacts, optional backbone bonds, solvent dress."""
    atom = tertiary_to_atom_contacts(contacts)
    if include_backbone:
        atom = expand_atom_contacts_with_backbone(atom, state)
    return dress_atom_contact_targets(atom, temperature_k=temperature_k)


def apply_gate_with_atom_contact_torque(
    carrier: DihedralCarrierState,
    state: BackboneAtomState,
    network: AtomContactNetworkMatrix,
    *,
    reference_m: int = REFERENCE_M_DEFAULT,
) -> tuple[list[SparseKet], int]:
    """OSH gate driven by atom-site mean-field torque."""
    atom_field = additive_field_at_atom_sites(state, network)
    residue_field = residue_field_from_atom_field(atom_field, state.n_residues)
    mod = [
        SparseKet(idx=k.idx, amp=k.amp * (1.0 + 1e-3 * residue_field[i]))
        for i, k in enumerate(carrier.register)
    ]
    evolved, pivot = apply_gate_sparse_hqiv_native(
        carrier.L, mod, list(network.shells), reference_m
    )
    flipped = detect_flipped_kets(list(carrier.register), evolved)
    if flipped:
        pruned = prune_to_flipped(flipped, evolved)
    else:
        pruned = evolved
    return pruned, pivot


def additive_field_at_sites(
    ca: list[Vec3],
    shells: list[int],
    pairs: tuple[ContactPairWeight, ...],
) -> list[float]:
    """Mean-field torque driver (Lean ``additiveFieldAtSite`` + contact violations)."""
    n = len(ca)
    field = [0.0] * n
    for p in pairs:
        d = _dist(ca[p.i], ca[p.j])
        if d < 1e-12:
            continue
        viol = (d - p.target_angstrom) * p.weight
        field[p.i] += viol / d
        field[p.j] -= viol / d
    for i in range(n):
        field[i] += lattice_full_mode_energy(shells[i]) * 1e-9
    return field


def _bin_step(n_bins: int, span_rad: float) -> float:
    if n_bins <= 1:
        return span_rad
    return span_rad / (n_bins - 1)


def dihedral_to_bins(
    phi: float,
    psi: float,
    center_phi: float,
    center_psi: float,
    n_bins: int,
    span_rad: float,
) -> tuple[int, int]:
    half = span_rad / 2.0
    step = _bin_step(n_bins, span_rad)
    lo_phi = center_phi - half
    lo_psi = center_psi - half
    phi_bin = int(round((phi - lo_phi) / step)) if step > 0 else 0
    psi_bin = int(round((psi - lo_psi) / step)) if step > 0 else 0
    cap = n_bins - 1
    return max(0, min(cap, phi_bin)), max(0, min(cap, psi_bin))


def bins_to_flat(phi_bin: int, psi_bin: int, n_bins: int) -> int:
    return phi_bin * n_bins + psi_bin


def flat_to_bins(flat: int, n_bins: int) -> tuple[int, int]:
    return flat // n_bins, flat % n_bins


def encode_residue_flat(
    residue_index: int,
    phi_bin: int,
    psi_bin: int,
    *,
    L: int,
    n_bins: int,
) -> int:
    """Injective-ish slot: ``flat + i·(n_bins²+1)`` wrapped on harmonic card."""
    base = bins_to_flat(phi_bin, psi_bin, n_bins)
    return wrap_idx(L, base + residue_index * (n_bins * n_bins + 1))


@dataclass(frozen=True)
class DihedralCarrierState:
    L: int
    n_bins: int
    span_rad: float
    register: tuple[SparseKet, ...]
    bins: tuple[tuple[int, int], ...]
    centers: tuple[tuple[float, float], ...]


def build_dihedral_carrier(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    ss: list[SecondaryStructure],
    *,
    L: int | None = None,
    n_bins: int = 5,
    span_rad: float = 0.5,
    strap_strand: bool = False,
    compact_helix: bool = False,
    violation_scores: list[float] | None = None,
) -> DihedralCarrierState:
    n = len(sequence)
    L_eff = L if L is not None else register_L(n, n_bins)
    scores = violation_scores or [0.0] * n
    kets: list[SparseKet] = []
    bins_list: list[tuple[int, int]] = []
    centers: list[tuple[float, float]] = []
    for i, aa in enumerate(sequence):
        center = dihedral_for_ss(ss[i], strap_strand=strap_strand, compact_helix=compact_helix)
        centers.append(center)
        phi, psi = dihedrals[i]
        pb, ps = dihedral_to_bins(phi, psi, center[0], center[1], n_bins, span_rad)
        bins_list.append((pb, ps))
        slot = encode_residue_flat(i, pb, ps, L=L_eff, n_bins=n_bins)
        amp = 1.0 + scores[i] * 1e-4
        kets.append(SparseKet(idx=slot, amp=amp))
    return DihedralCarrierState(
        L=L_eff,
        n_bins=n_bins,
        span_rad=span_rad,
        register=tuple(kets),
        bins=tuple(bins_list),
        centers=tuple(centers),
    )


def _flat_from_ket(L: int, ket: SparseKet, residue_index: int, n_bins: int) -> int:
    raw = ket.idx - residue_index * (n_bins * n_bins + 1)
    card = sparse_basis_card(L)
    while raw < 0:
        raw += card
    return raw % (n_bins * n_bins)


def decode_carrier_shifts(
    before: DihedralCarrierState,
    after: list[SparseKet],
) -> dict[int, tuple[int, int]]:
    """Per-residue φ/ψ bin deltas from pruned carrier indices."""
    n = len(before.bins)
    after_by_slot = {k.idx: k for k in after}
    shifts: dict[int, tuple[int, int]] = {}
    for i in range(n):
        old_ket = before.register[i]
        new_ket = after_by_slot.get(old_ket.idx)
        if new_ket is None:
            for k in after:
                if abs(k.amp) > 1e-12:
                    new_ket = k
                    break
        if new_ket is None:
            shifts[i] = (0, 0)
            continue
        old_flat = _flat_from_ket(before.L, old_ket, i, before.n_bins)
        new_flat = _flat_from_ket(before.L, new_ket, i, before.n_bins)
        opb, ops = flat_to_bins(old_flat, before.n_bins)
        npb, nps = flat_to_bins(new_flat, before.n_bins)
        shifts[i] = (npb - opb, nps - ops)
    return shifts


def peak_dihedral_hints(
    L: int,
    register: list[SparseKet],
    *,
    peak_min_frac: float = 0.25,
) -> tuple[int, int]:
    """Global 32-sector peak → coarse (Δφ_bin, Δψ_bin) suggestion."""
    h32 = sector_histogram_from_indices(L, register, sectors=32)
    peaks = local_maxima_bins(h32, min_frac=peak_min_frac)
    if not peaks:
        return (0, 0)
    p = peaks[0]
    return (1 if p >= 16 else (-1 if p >= 8 else 0), 1 if (p % 8) >= 4 else (-1 if (p % 8) >= 2 else 0))


def _ordered_dihedral_trials(
    i: int,
    delta: float,
    bin_step: float,
    shifts: dict[int, tuple[int, int]],
    global_hint: tuple[int, int],
) -> tuple[tuple[float, float], ...]:
    """Carrier peak hints first, then standard ±δ grid (OSH torque ordering)."""
    si, sj = shifts.get(i, (0, 0))
    gphi, gpsi = global_hint
    hinted: list[tuple[float, float]] = []
    if si != 0 or sj != 0:
        hinted.append((si * bin_step, sj * bin_step))
        hinted.append((si * bin_step * 0.5, sj * bin_step * 0.5))
    if gphi != 0 or gpsi != 0:
        hinted.append((gphi * delta * 0.5, gpsi * delta * 0.5))
    grid: list[tuple[float, float]] = []
    for dphi in (-delta, 0.0, delta):
        for dpsi in (-delta, 0.0, delta):
            if dphi == 0.0 and dpsi == 0.0:
                continue
            grid.append((dphi, dpsi))
    seen: set[tuple[float, float]] = set()
    ordered: list[tuple[float, float]] = []
    for pair in hinted + grid:
        key = (round(pair[0], 8), round(pair[1], 8))
        if key in seen:
            continue
        seen.add(key)
        ordered.append(pair)
    return tuple(ordered)


def apply_gate_with_contact_torque(
    carrier: DihedralCarrierState,
    shells: list[int],
    ca: list[Vec3],
    network: ContactNetworkMatrix,
    *,
    reference_m: int = REFERENCE_M_DEFAULT,
) -> tuple[list[SparseKet], int]:
    field = additive_field_at_sites(ca, shells, network.pairs)
    mod = [
        SparseKet(idx=k.idx, amp=k.amp * (1.0 + 1e-3 * field[i]))
        for i, k in enumerate(carrier.register)
    ]
    evolved, pivot = apply_gate_sparse_hqiv_native(carrier.L, mod, shells, reference_m)
    flipped = detect_flipped_kets(list(carrier.register), evolved)
    if flipped:
        pruned = prune_to_flipped(flipped, evolved)
    else:
        pruned = evolved
    return pruned, pivot


def select_active_residues(scores: list[float], *, min_score: float = 1e-6, n_cap: int = 24) -> list[int]:
    """Full chain through miniprotein ladder; sparse mask only for longer chains."""
    if not scores:
        return []
    if len(scores) <= n_cap:
        return list(range(len(scores)))
    ranked = sorted(range(len(scores)), key=lambda i: scores[i], reverse=True)
    if scores[ranked[0]] < min_score:
        return list(range(len(scores)))
    threshold = scores[ranked[0]] * 0.15
    active = [i for i in ranked if scores[i] >= threshold]
    return active if active else ranked[: max(1, len(ranked) // 3)]


def apply_osh_contact_refinement(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    contacts: tuple[TertiaryContact, ...],
    ss: list[SecondaryStructure],
    *,
    strap_strand: bool = False,
    compact_helix: bool = False,
    rounds: int | None = None,
    initial_delta_rad: float | None = None,
    min_delta_rad: float = 0.012,
    n_bins: int = 5,
    span_rad: float = 0.5,
    gate_passes: int = 1,
    macro_ricci_soft: bool = False,
    atom_sites: bool = True,
    temperature_k: float | None = None,
) -> tuple[list[Vec3], tuple[tuple[float, float], ...]]:
    """
    Tertiary closure via OSH carrier + sparse atom-site contact network.

    Same outer coordinate-search shape as NeRF refinement, but residue order and
    trial direction are driven by sparse register peaks and contact-weighted torque
    on atom sites (sub-linear active set per round on large targets).
    """
    if not contacts:
        ca = place_ca_trace(sequence, dihedrals)
        return ca, dihedrals

    n = len(sequence)
    if rounds is None:
        rounds = 12 if n <= 8 else 6
    if initial_delta_rad is None:
        initial_delta_rad = 0.4 if n <= 8 else 0.25
    from hqiv_lab.peptide_shell_dress import staged_pass_piezo_step_dress

    initial_delta_rad = float(initial_delta_rad) * staged_pass_piezo_step_dress(
        contacts, temperature_k=temperature_k
    )

    shells = shells_for_sequence(sequence)
    L = register_L(n, n_bins)
    bin_step = _bin_step(n_bins, span_rad)

    best = list(dihedrals)
    best_state = place_backbone_atom_state(sequence, tuple(best))
    best_ca = best_state.ca_trace()
    atom_contacts = prepare_atom_contacts(
        contacts, best_state, temperature_k=temperature_k
    ) if atom_sites else ()
    atom_network = (
        build_atom_contact_network_matrix(sequence, atom_contacts, best_state, shells=shells)
        if atom_sites
        else None
    )
    legacy_network = build_contact_network_matrix(sequence, contacts, shells=shells)
    best_sse = (
        atom_contact_sse(best_state, atom_contacts)
        if atom_sites
        else contact_sse(sequence, best_ca, contacts, ss=ss, macro_ricci_soft=macro_ricci_soft)
    )
    delta = initial_delta_rad

    for _ in range(rounds):
        improved = False
        state = place_backbone_atom_state(sequence, tuple(best))
        best_ca = state.ca_trace()
        if atom_sites and atom_network is not None:
            atom_contacts = prepare_atom_contacts(contacts, state, temperature_k=temperature_k)
            atom_network = build_atom_contact_network_matrix(
                sequence, atom_contacts, state, shells=shells
            )
            scores = atom_violation_scores(state, atom_contacts)
        else:
            scores = residue_violation_scores(
                sequence,
                best_ca,
                contacts,
                ss=ss,
                macro_ricci_soft=macro_ricci_soft,
            )
        active = select_active_residues(scores)

        initial_carrier = build_dihedral_carrier(
            sequence,
            tuple(best),
            ss,
            L=L,
            n_bins=n_bins,
            span_rad=span_rad,
            strap_strand=strap_strand,
            compact_helix=compact_helix,
            violation_scores=scores,
        )
        carrier = initial_carrier
        pruned = list(carrier.register)
        for _gp in range(gate_passes):
            if atom_sites and atom_network is not None:
                pruned, _pivot = apply_gate_with_atom_contact_torque(
                    carrier, state, atom_network
                )
            else:
                pruned, _pivot = apply_gate_with_contact_torque(
                    carrier, shells, best_ca, legacy_network
                )
            carrier = DihedralCarrierState(
                L=carrier.L,
                n_bins=carrier.n_bins,
                span_rad=carrier.span_rad,
                register=tuple(pruned),
                bins=carrier.bins,
                centers=carrier.centers,
            )

        _ = decode_carrier_shifts(initial_carrier, pruned)
        _ = peak_dihedral_hints(L, pruned)

        for i in active:
            for dphi in (-delta, 0.0, delta):
                for dpsi in (-delta, 0.0, delta):
                    if dphi == 0.0 and dpsi == 0.0:
                        continue
                    trial = best[:]
                    phi_i, psi_i = trial[i]
                    trial[i] = (phi_i + dphi, psi_i + dpsi)
                    tstate = place_backbone_atom_state(sequence, tuple(trial))
                    tca = tstate.ca_trace()
                    if atom_sites:
                        t_atom = prepare_atom_contacts(contacts, tstate, temperature_k=temperature_k)
                        sse = atom_contact_sse(tstate, t_atom)
                    else:
                        sse = contact_sse(
                            sequence,
                            tca,
                            contacts,
                            ss=ss,
                            macro_ricci_soft=macro_ricci_soft,
                        )
                    if sse < best_sse:
                        best_sse = sse
                        best = trial
                        best_ca = tca
                        best_state = tstate
                        improved = True

        if not improved:
            delta *= 0.5
        if delta < min_delta_rad:
            break

    return best_ca, tuple(best)


def apply_staged_osh_contact_refinement(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    contacts: tuple[TertiaryContact, ...],
    ss: list[SecondaryStructure],
    *,
    structure_rounds: int = 8,
    hydrophobic_rounds: int = 8,
    terminus_rounds: int = 10,
    final_rounds: int = 10,
    strap_strand: bool = False,
    compact_helix: bool = False,
    macro_ricci_soft: bool = False,
    atom_sites: bool = True,
    temperature_k: float | None = None,
) -> tuple[list[Vec3], tuple[tuple[float, float], ...]]:
    """Staged OSH carrier refinement (same pass order as ``apply_staged_nerf_contact_refinement``)."""
    from hqiv_lab.miniprotein_contacts import partition_tertiary_contacts_staged

    if not contacts:
        ca = place_ca_trace(sequence, dihedrals)
        return ca, dihedrals

    structure, hydrophobic, terminus = partition_tertiary_contacts_staged(contacts)
    best = list(dihedrals)
    osh_kw = {
        "strap_strand": strap_strand,
        "compact_helix": compact_helix,
        "macro_ricci_soft": macro_ricci_soft,
        "atom_sites": atom_sites,
        "temperature_k": temperature_k,
    }

    for stage, rounds in (
        (structure, structure_rounds),
        (hydrophobic, hydrophobic_rounds),
        (terminus, terminus_rounds),
        (contacts, final_rounds),
    ):
        if not stage or rounds <= 0:
            continue
        stage_kw = dict(osh_kw)
        if stage is not contacts:
            stage_kw["macro_ricci_soft"] = False
        _, best = apply_osh_contact_refinement(
            sequence,
            tuple(best),
            stage,
            ss,
            rounds=rounds,
            **stage_kw,
        )

    best_ca = place_ca_trace(sequence, tuple(best))
    return best_ca, tuple(best)


def osh_atom_refinement_manifest(
    sequence: str,
    contacts: tuple[TertiaryContact, ...],
    *,
    temperature_k: float | None = None,
) -> dict[str, Any]:
    """Audit payload for atom-site OSH fold path."""
    from hqiv_lab.miniprotein_basin import dihedrals_from_spine
    from hqiv_lab.miniprotein_contacts import ss_per_residue

    ss_map: dict = {"C": tuple(range(1, len(sequence) + 1))}
    dihedrals = dihedrals_from_spine(sequence, ss_map) if sequence else ()
    state = place_backbone_atom_state(sequence, dihedrals)
    atom = prepare_atom_contacts(contacts, state, temperature_k=temperature_k)
    net = build_atom_contact_network_matrix(sequence, atom, state)
    return {
        "register_L": register_L(len(sequence), 5),
        "sparse_basis_card": sparse_basis_card(register_L(len(sequence), 5)),
        "atom_contact_network": net.to_dict(),
        "n_atom_contacts": len(atom),
        "reference_m": REFERENCE_M_DEFAULT,
    }


def osh_refinement_manifest(
    sequence: str,
    contacts: tuple[TertiaryContact, ...],
) -> dict[str, Any]:
    """Audit payload for OSH fold path."""
    shells = shells_for_sequence(sequence)
    net = build_contact_network_matrix(sequence, contacts, shells=shells)
    L = register_L(len(sequence), 5)
    return {
        "register_L": L,
        "sparse_basis_card": sparse_basis_card(L),
        "contact_network": net.to_dict(),
        "reference_m": REFERENCE_M_DEFAULT,
    }
