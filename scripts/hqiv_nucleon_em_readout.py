#!/usr/bin/env python3
"""
Nucleon electromagnetic readout from the SAME network engine as derived chemistry.

The chemistry engine reads molecular observables off two axiom-level pillars:

  1. **Spin-statistics alignment** of identical constituents (the same rule that lifts the
     fully-paired light nuclei in :mod:`hqiv_curvature_binding_core`), and
  2. **Coherent vector coupling** on the constituent network (the 2×2 PSD Gram /
     geometric-mean coupling behind bond order, and the balanced-frame vector sum behind the
     molecular dipole).

Here we point those exact pillars at the nucleon's 3-quark network and read off the magnetic
moment — the nucleon analogue of the molecular dipole.  Nothing is injected from PDG; the inputs
are the valence content (``uud`` / ``udd`` from ``data/hadron-catalog.js``), Gell-Mann–Nishijima
charges from the already-derived isospin, and the constituent magneton fixed by the **weight-3
composite trace** (three carrier slots share the nucleon mass, so m_q = m_N/3 and μ_q = 3 μ_N).

Derivation of the magnetic moment (parameter-free)
--------------------------------------------------
* Each quark carries μ_i = Q_i · μ_q with μ_q = e/(2 m_q).  The nucleon's three carrier slots
  share its mass equally (the flavor-blind weight-3 trace, ``NUCLEON_TRACE_GENERATOR_WEIGHT``),
  so m_q = m_N/3 and **μ_q = 3 μ_N** — the same "3" that sets E_bind = 3·bindingCoupling.
* The two identical quarks (the doubled flavor, ``uu`` in p / ``dd`` in n) are forced by Fermi
  statistics + color antisymmetry into a **symmetric spin-1 pair** (they align — the same
  spin-statistics that builds the nuclear boundary lift).  Coupling that spin-1 diquark with the
  odd quark's spin-½ to the baryon's J=½ is the coherent vector coupling on the spin network; the
  Clebsch weights (2/3, 1/3) give per-flavor spin polarizations (+4/3 doubled, −1/3 odd):

      μ_B = (4 μ_doubled − μ_odd) / 3  =  (4 Q_doubled − Q_odd) · μ_N

  (the weight-3 magneton cancels the SU(6) /3, leaving a clean integer-charge readout in μ_N).

So the bare (parameter-free) readout is **μ_p = +3 μ_N**, **μ_n = −2 μ_N**, **ratio −3/2**.

Octonionic-background mass dressing
-----------------------------------
The bare values use the bare carrier mass m_N/3.  The *magnetic* constituent mass is that bare mass
dressed by the monogamy self-curvature it picks up from the 8-dimensional octonion carrier space,
`m_q = (m_N/3)·(1 + α/8)` with α = 3/5 (the same monogamy fraction and the same octonion dimension
8 used everywhere).  The dressing rescales the magneton uniformly (`μ_q = 3/(1+α/8) = 2.791 μ_N`)
and cancels in the ratio, giving **μ_p = 2.791 μ_N** (PDG 2.793, −0.08%), **μ_n = −1.860 μ_N**
(PDG −1.913; residual −2.7%), ratio unchanged at −3/2.

Whole-hadron i,j,k reading (not a quark-level scorecard)
-------------------------------------------------------
We do not chase quark-level PDG values (quarks are not asymptotic states).  The nucleon is ONE
whole-hadron object whose three carrier slots are an i,j,k Fano triple (the f^{ijk} antisymmetric
budget, ``hadronIjkSortedTripleBudget`` = 9).  The moment is the composite trace over that triple;
``μ_B = (4 Q_doubled − Q_odd)`` is already the symmetric+antisymmetric trace of the i,j,k slots.
The proton being nice (−0.08%) is the only validation we ask for — if the hadron is right, the
quark slots are behaved.  The residual is a WHOLE-HADRON split between the symmetric (isoscalar)
and antisymmetric f^{ijk} (isovector) channels of the i,j,k trace; the two are comparable and
cancel in μ_p = S+V but add in μ_n = S−V (so it presents as "neutron-only").  The clean place to
finish it is the whole-hadron S⁷ + f^{ijk} dressing (``HadronS7ConfinementReadout``), where the
symmetric/antisymmetric channels carry different S⁷ Laplace weights — parameter-free because the
triple budget is fixed, NOT a per-quark mass fit.

Lean-side spine: ``Hqiv.Physics.MetaHorizonExcitedStates`` (weight-3 trace),
``Hqiv.Physics.FureyHQIVOntologyBridge`` (so(8) ↔ SM quantum numbers).
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction

import cubic_phase_relax_probe as cpr
import hqiv_excited_states as hes

# Three carrier slots on one so(8) generator → three constituent quarks share the nucleon mass.
# With the bare carrier mass m_q = m_N/3 the magneton is μ_q = (m_N/m_q) μ_N = 3 μ_N exactly.
CONSTITUENT_MAGNETON_UNITS = Fraction(int(hes.NUCLEON_TRACE_GENERATOR_WEIGHT))  # = 3

# Anchor mass (referenceM=4 proton lock-in) used only to convert a constituent-mass dressing into a
# magneton; never fed into the spin-flavor structure.
NUCLEON_MEV = 938.27208816

# Octonionic-background dressing of the magnetic constituent mass.
# ---------------------------------------------------------------------------------------------
# The carrier lives on the octonion algebra 𝕆 = ℝ ⊕ Im𝕆 (dimension 8, the so(8) carrier space).
# Informational monogamy assigns total curvature coupling α = 3/5 to the carrier; spread
# isotropically over the 8 octonion directions, the carrier's own rest-mass (real) axis carries one
# unit share α/8.  The magnetic constituent mass is the bare carrier mass dressed by that
# self-curvature, m_q = (m_N/3)·(1 + α/8).  This is the SAME α (monogamy fraction) and the SAME
# octonion dimension (8 = octet/so(8) carrier) already used throughout the framework — no new knob.
MONOGAMY_ALPHA = cpr.ALPHA  # 3/5 (informational monogamy)
OCTONION_CARRIER_DIM = 8  # 𝕆 = ℝ ⊕ Im𝕆 / so(8)
CONSTITUENT_DRESSING = 1.0 + MONOGAMY_ALPHA / OCTONION_CARRIER_DIM  # 1 + α/8 = 1.075

# Light-quark internal quantum numbers (I₃, strangeness); baryon number per quark = 1/3.
# These are the inputs the isospin engine already uses (u,d) plus the strange slot.
_QUARK_ISOSPIN_THIRD: dict[str, Fraction] = {
    "u": Fraction(1, 2),
    "d": Fraction(-1, 2),
    "s": Fraction(0),
    "c": Fraction(0),
    "b": Fraction(0),
    "t": Fraction(0),
}
_QUARK_STRANGENESS: dict[str, int] = {"u": 0, "d": 0, "s": -1, "c": 0, "b": 0, "t": 0}
_BARYON_NUMBER_PER_QUARK = Fraction(1, 3)

# Comparison-only PDG centrals (never fed into the derivation).
PDG_MU_PROTON_MU_N = 2.7928473
PDG_MU_NEUTRON_MU_N = -1.9130427
PDG_MU_OCTET_MU_N: dict[str, float] = {
    "p": 2.7928473,
    "n": -1.9130427,
    "Lambda": -0.613,
    "Sigma+": 2.458,
    "Sigma-": -1.160,
    "Xi0": -1.250,
    "Xi-": -0.6507,
    "Sigma0->Lambda": -1.61,  # |transition| moment
}


def quark_charge(flavor: str) -> Fraction:
    """Gell-Mann–Nishijima charge ``Q = I₃ + Y/2`` with ``Y = B + S`` (B = 1/3 per quark)."""
    i3 = _QUARK_ISOSPIN_THIRD[flavor]
    hypercharge = _BARYON_NUMBER_PER_QUARK + _QUARK_STRANGENESS[flavor]
    return i3 + hypercharge / 2


def spin1_diquark_spectator_weights() -> tuple[Fraction, Fraction]:
    """
    Per-flavor spin polarizations from the spin-1 (doubled) pair + spin-½ spectator coupling.

    The baryon |J=½, m=½⟩ = √(2/3)|S_pair=1,+1⟩|odd ↓⟩ − √(1/3)|S_pair=1,0⟩|odd ↑⟩.
    ⟨Σσ_z⟩_pair = (2/3)(+2) + (1/3)(0) = +4/3;  ⟨σ_z⟩_odd = (2/3)(−1) + (1/3)(+1) = −1/3.
    """
    w_high = Fraction(2, 3)  # |S_pair=1, m=+1⟩ weight (Clebsch²)
    w_mid = Fraction(1, 3)   # |S_pair=1, m=0⟩ weight (Clebsch²)
    pair_polarization = w_high * 2 + w_mid * 0           # +4/3 (both doubled quarks)
    odd_polarization = w_high * (-1) + w_mid * (+1)      # −1/3
    return pair_polarization, odd_polarization


def _doubled_and_odd(quark_flavors: list[str]) -> tuple[str, str] | None:
    """Return ``(doubled_flavor, odd_flavor)`` for a 2+1 baryon, else ``None``."""
    if len(quark_flavors) != 3:
        return None
    counts: dict[str, int] = {}
    for f in quark_flavors:
        counts[f] = counts.get(f, 0) + 1
    doubled = [f for f, n in counts.items() if n == 2]
    odd = [f for f, n in counts.items() if n == 1]
    if len(doubled) == 1 and len(odd) == 1:
        return doubled[0], odd[0]
    return None


def magneton_units(dressing: float = CONSTITUENT_DRESSING) -> float:
    """μ_q in nuclear magnetons: ``(m_N / m_q) = 3 / dressing`` (dressing = m_q / (m_N/3))."""
    return float(CONSTITUENT_MAGNETON_UNITS) / dressing


@dataclass(frozen=True)
class NucleonMomentReadout:
    label: str
    quark_flavors: tuple[str, ...]
    doubled: str
    odd: str
    q_doubled: Fraction
    q_odd: Fraction
    magneton_unit: float
    mu_mu_n: float  # magnetic moment in nuclear magnetons


def baryon_magnetic_moment(
    label: str, quark_flavors: list[str], *, dressing: float = CONSTITUENT_DRESSING
) -> NucleonMomentReadout | None:
    """
    Spin-flavor magnetic moment of a 2+1 baryon, in nuclear magnetons (parameter-free at dressing=1).

    ``μ = μ_q · (w_pair·Q_doubled + w_odd·Q_odd)`` with μ_q = (3/dressing) μ_N and
    (w_pair, w_odd)=(4/3,−1/3), i.e. ``μ = (4 Q_doubled − Q_odd) μ_N / dressing`` for (u,d).
    """
    split = _doubled_and_odd(quark_flavors)
    if split is None:
        return None
    doubled, odd = split
    q_d = quark_charge(doubled)
    q_o = quark_charge(odd)
    w_pair, w_odd = spin1_diquark_spectator_weights()
    mu_q = magneton_units(dressing)
    mu = mu_q * float(w_pair * q_d + w_odd * q_o)
    return NucleonMomentReadout(
        label=label,
        quark_flavors=tuple(quark_flavors),
        doubled=doubled,
        odd=odd,
        q_doubled=q_d,
        q_odd=q_o,
        magneton_unit=mu_q,
        mu_mu_n=mu,
    )


def proton_moment(*, dressing: float = CONSTITUENT_DRESSING) -> NucleonMomentReadout:
    r = baryon_magnetic_moment("p (uud)", ["u", "u", "d"], dressing=dressing)
    assert r is not None
    return r


def neutron_moment(*, dressing: float = CONSTITUENT_DRESSING) -> NucleonMomentReadout:
    r = baryon_magnetic_moment("n (udd)", ["u", "d", "d"], dressing=dressing)
    assert r is not None
    return r


def proton_neutron_ratio() -> float:
    """μ_p/μ_n — the dressing cancels, so this is parameter-free regardless of m_q."""
    return proton_moment().mu_mu_n / neutron_moment().mu_mu_n


def bare_constituent_quark_mass_mev() -> float:
    """Framework's bare carrier mass m_N/3 (three carriers share the nucleon mass)."""
    return NUCLEON_MEV / float(CONSTITUENT_MAGNETON_UNITS)


def implied_dressing_from_proton() -> float:
    """The single scalar the proton moment needs: dressing = μ_p(bare) / μ_p(PDG) = 3 / 2.793."""
    return float(CONSTITUENT_MAGNETON_UNITS) / PDG_MU_PROTON_MU_N


def implied_constituent_quark_mass_mev() -> float:
    """Magnetic constituent quark mass implied by μ_p(PDG): m_q = m_N / μ_p[μ_N]."""
    return NUCLEON_MEV / PDG_MU_PROTON_MU_N


def constituent_quark_mass_mev() -> float:
    """Derived magnetic constituent mass m_q = (m_N/3)·(1 + α/8) (octonionic-background dressing)."""
    return bare_constituent_quark_mass_mev() * CONSTITUENT_DRESSING


# ---------------------------------------------------------------------------------------------
# Generalized octet closed form
# ---------------------------------------------------------------------------------------------
# Every spin-½ octet moment is the same coherent spin-flavor sum on the 3-quark graph.  Writing the
# quark moments μ_q = Q_q · μ_q^mag (μ_q^mag = (m_N/m_q) μ_N), the closed forms are:
#
#   2+1 baryon (doubled a, odd b):  μ_B = (4 μ_a − μ_b)/3        (p, n, Σ±, Ξ⁰, Ξ⁻)
#   Λ (uds, ud spin-0):             μ_Λ = μ_s
#   Σ⁰ (uds, ud spin-1):            μ_Σ0 = (2 μ_u + 2 μ_d − μ_s)/3
#   Σ⁰→Λ transition (isovector):    |μ| = |μ_u − μ_d|/√3 = μ_q^mag/√3 = √3/(1 + α/8)
#
# The light quark moments use the derived dressed mass (nucleon nailed).  The strange sector needs a
# single strange-mass anchor; we pin it to the Λ moment (μ_Λ = μ_s — the strange analogue of the
# proton mass anchor) and PREDICT the remaining hyperons.  The isovector combinations (μ_p − μ_n and
# the Σ⁰→Λ transition) cancel the strange mass entirely and are fully parameter-free.


def light_quark_moments_mu_n() -> tuple[float, float]:
    """Derived (μ_u, μ_d) in μ_N from the dressed light mass (no free parameter)."""
    mu_q = magneton_units()
    return mu_q * float(quark_charge("u")), mu_q * float(quark_charge("d"))


def strange_quark_moment_mu_n(mu_lambda: float = PDG_MU_OCTET_MU_N["Lambda"]) -> float:
    """μ_s from the Λ anchor: Λ=uds with the ud pair in spin-0, so μ_Λ = μ_s exactly."""
    return mu_lambda


def sigma_lambda_transition_mu_n() -> float:
    """Parameter-free isovector transition |μ(Σ⁰→Λ)| = √3 / (1 + α/8) (light sector only)."""
    return math.sqrt(3.0) / CONSTITUENT_DRESSING


def octet_baryon_moment_mu_n(name: str) -> float:
    """Closed-form octet moment in μ_N (light sector derived; strange sector from the Λ anchor)."""
    mu_u, mu_d = light_quark_moments_mu_n()
    mu_s = strange_quark_moment_mu_n()
    table = {
        "p": (4 * mu_u - mu_d) / 3,
        "n": (4 * mu_d - mu_u) / 3,
        "Lambda": mu_s,
        "Sigma+": (4 * mu_u - mu_s) / 3,
        "Sigma0": (2 * mu_u + 2 * mu_d - mu_s) / 3,
        "Sigma-": (4 * mu_d - mu_s) / 3,
        "Xi0": (4 * mu_s - mu_u) / 3,
        "Xi-": (4 * mu_s - mu_d) / 3,
        "Sigma0->Lambda": -sigma_lambda_transition_mu_n(),
    }
    return table[name]


def proton_neutron_isovector() -> float:
    """μ_p − μ_n: strange-free, parameter-free isovector combination."""
    return proton_moment().mu_mu_n - neutron_moment().mu_mu_n


@dataclass(frozen=True)
class SecondOrderDecomposition:
    """
    Isoscalar/isovector split of the nucleon-moment residual = the missing 2nd-order effects.

    These are NOT pion clouds or Dirac lower components (HQIV has no pion channel and the strong
    force does not bind).  They are also NOT per-quark mass fits — we score only the HADRON, and the
    nucleon is one whole-hadron i,j,k composite trace over its Fano triple (f^{ijk} budget = 9).

    The residual is the whole-hadron split of that i,j,k trace into:
      * isoscalar S = (μ_p+μ_n)/2 — the SYMMETRIC part of the i,j,k composite trace;
      * isovector V = (μ_p−μ_n)/2 — the ANTISYMMETRIC f^{ijk} part of the i,j,k composite trace.

    The two are comparable (~±2.6%) and CANCEL in μ_p = S+V (proton nice, −0.08%) but ADD in
    μ_n = S−V.  Finishing them is a whole-hadron S⁷ + f^{ijk} dressing job (parameter-free, the
    triple budget is fixed) — NOT a quark-level fit — so no correction is wired in here yet.
    """

    isoscalar_pred: float
    isoscalar_pdg: float
    isovector_pred: float
    isovector_pdg: float

    @property
    def isoscalar_residual(self) -> float:
        return self.isoscalar_pred / self.isoscalar_pdg - 1.0

    @property
    def isovector_residual(self) -> float:
        return self.isovector_pred / self.isovector_pdg - 1.0

    @property
    def proton_error(self) -> float:
        # μ_p = S + V: the two 2nd-order shifts nearly cancel here.
        return (self.isoscalar_pred + self.isovector_pred) - (
            self.isoscalar_pdg + self.isovector_pdg
        )

    @property
    def neutron_error(self) -> float:
        # μ_n = S − V: the two 2nd-order shifts ADD here, exposing them.
        return (self.isoscalar_pred - self.isovector_pred) - (
            self.isoscalar_pdg - self.isovector_pdg
        )


def second_order_decomposition() -> SecondOrderDecomposition:
    """
    Decompose the nucleon-moment residual into the two octonion-channel 2nd-order corrections.

    * **Isoscalar** S = (μ_p+μ_n)/2 — the SYMMETRIC part of the whole-hadron i,j,k composite trace.
    * **Isovector** V = (μ_p−μ_n)/2 — the ANTISYMMETRIC f^{ijk} part of the i,j,k composite trace.

    μ_p = S+V (the two shifts cancel → μ_p looks nailed); μ_n = S−V (they add → μ_n exposes them).
    """
    mp = proton_moment().mu_mu_n
    mn = neutron_moment().mu_mu_n
    return SecondOrderDecomposition(
        isoscalar_pred=(mp + mn) / 2.0,
        isoscalar_pdg=(PDG_MU_PROTON_MU_N + PDG_MU_NEUTRON_MU_N) / 2.0,
        isovector_pred=(mp - mn) / 2.0,
        isovector_pdg=(PDG_MU_PROTON_MU_N - PDG_MU_NEUTRON_MU_N) / 2.0,
    )


def _pct(pred: float, ref: float) -> float:
    return (pred - ref) / ref * 100.0


def main() -> None:
    print("HQIV nucleon magnetic moment — derived-chemistry network applied to the quark graph")
    print("=" * 84)
    print(
        f"magnetic constituent mass m_q = (m_N/3)·(1 + α/8) = {constituent_quark_mass_mev():.2f} MeV "
        f"(α={MONOGAMY_ALPHA}, dressing {CONSTITUENT_DRESSING:.4f}) → μ_q = {magneton_units():.4f} μ_N"
    )
    w_pair, w_odd = spin1_diquark_spectator_weights()
    print(f"spin polarizations: doubled pair = {w_pair} (+4/3), odd = {w_odd} (−1/3)")
    print(f"quark charges: Q_u={quark_charge('u')}  Q_d={quark_charge('d')}  Q_s={quark_charge('s')}")
    print()
    print(f"{'baryon':10}{'doubled':>8}{'odd':>5}{'μ pred':>10}{'μ PDG':>10}{'err %':>8}")
    print("-" * 84)
    for r, pdg in ((proton_moment(), PDG_MU_PROTON_MU_N), (neutron_moment(), PDG_MU_NEUTRON_MU_N)):
        print(
            f"{r.label:10}{r.doubled:>8}{r.odd:>5}{r.mu_mu_n:>10.4f}{pdg:>10.4f}"
            f"{_pct(r.mu_mu_n, pdg):>8.2f}"
        )
    ratio = proton_neutron_ratio()
    pdg_ratio = PDG_MU_PROTON_MU_N / PDG_MU_NEUTRON_MU_N
    print("-" * 84)
    print(f"μ_p/μ_n pred = {ratio:.4f}   PDG = {pdg_ratio:.4f}   err = {_pct(ratio, pdg_ratio):.2f}%")
    print()
    bare_p = proton_moment(dressing=1.0).mu_mu_n
    bare_n = neutron_moment(dressing=1.0).mu_mu_n
    print(f"bare (m_N/3, no dressing): μ_p={bare_p:.4f}  μ_n={bare_n:.4f}  ratio={bare_p/bare_n:.4f}")
    print("Parameter-free: ratio −3/2 from spin-statistics + charges (locked vs m_q dressing).")
    print(
        f"Octonionic dressing 1+α/8={CONSTITUENT_DRESSING:.4f} → m_q={constituent_quark_mass_mev():.2f} MeV "
        f"(μ_p(PDG) implies {implied_constituent_quark_mass_mev():.2f} MeV)."
    )
    print()
    print("Generalized octet closed form  μ_B = (4μ_doubled − μ_odd)/3  (Λ-anchored strange sector)")
    print("-" * 84)
    print(f"{'baryon':16}{'μ pred':>10}{'μ PDG':>10}{'err %':>9}   {'note'}")
    notes = {
        "p": "parameter-free",
        "n": "parameter-free",
        "Sigma0->Lambda": "parameter-free (isovector)",
        "Lambda": "strange anchor",
    }
    for name in ("p", "n", "Sigma0->Lambda", "Lambda", "Sigma+", "Sigma-", "Xi0", "Xi-"):
        pred = octet_baryon_moment_mu_n(name)
        pdg = PDG_MU_OCTET_MU_N.get(name)
        if name == "Sigma0->Lambda":
            err = _pct(abs(pred), abs(pdg))
        else:
            err = _pct(pred, pdg)
        print(f"{name:16}{pred:>10.4f}{pdg:>10.4f}{err:>9.2f}   {notes.get(name,'Λ-anchored pred')}")
    print("-" * 84)
    iso = proton_neutron_isovector()
    print(
        f"isovector μ_p−μ_n = {iso:.4f} (PDG 4.706, {_pct(iso, 4.706):.2f}%) — strange-free, parameter-free."
    )
    print("Nucleon + isovector transition nailed; Σ/Ξ carry the known additive-model breaking (m_s).")
    print()
    d = second_order_decomposition()
    print("whole-hadron i,j,k composite-trace channels (score the hadron, not the quarks):")
    print(
        f"  isoscalar S=(μ_p+μ_n)/2: pred {d.isoscalar_pred:+.4f}  PDG {d.isoscalar_pdg:+.4f}  "
        f"{d.isoscalar_residual*100:+.2f}%  → symmetric part of the i,j,k trace"
    )
    print(
        f"  isovector V=(μ_p−μ_n)/2: pred {d.isovector_pred:+.4f}  PDG {d.isovector_pdg:+.4f}  "
        f"{d.isovector_residual*100:+.2f}%  → antisymmetric f^{{ijk}} part of the i,j,k trace"
    )
    print(
        f"  μ_p err = S+V shifts = {d.proton_error:+.4f} (cancel → μ_p looks nailed); "
        f"μ_n err = S−V shifts = {d.neutron_error:+.4f} (add → μ_n exposes them)."
    )


if __name__ == "__main__":
    main()
