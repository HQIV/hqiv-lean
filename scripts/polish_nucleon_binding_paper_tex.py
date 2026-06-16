#!/usr/bin/env python3
"""One-shot body-text polish for nucleon_binding paper (reader-first Lean links)."""
from __future__ import annotations

from pathlib import Path

TEX = Path(__file__).resolve().parents[1] / "papers/nucleon_binding/hqiv_nucleon_binding_from_composite_trace.tex"

REPLACEMENTS_BEFORE_APPENDIX = [
    # Upstream Lagrangian discharge paragraph
    (
        r"""obligations (\leanfile{Hqiv/Algebra/AnomalyCancellation.lean},
\leanfile{Hqiv/QuantumMechanics/PatchTopologicalObstruction.lean}),
plus rapidity-phase and spatial-rotation Lorentz closure on the flat patch chart
(\leanfile{Hqiv/Geometry/RapidityLorentzClosure.lean}, witness
\leanid{rapidity_lorentz_closure_discharged};
\leanfile{Hqiv/Geometry/SpatialRotationLorentzClosure.lean}, witness
\leanid{full_lorentz_closure_discharged}),
full four-edge SO(8) Wilson plaquettes, abelian Wilson--kinetic equivalence, and a partial
strong-interacting discrete-action Poincaré bundle
(\leanfile{Hqiv/Physics/SO8PlaquetteHolonomy.lean},
\leanfile{Hqiv/Physics/ActionHolonomyGlue.lean},
\leanfile{Hqiv/Physics/DiscreteActionStrongPoincareBridge.lean};
witnesses \leanid{so8PlaquetteHolonomyDischarged_holds},
\leanid{wilsonKineticPlaquetteEquivalence_discharged},
\leanid{fullActionStrongPoincare_discharged})---not a continuum path-integral or
smooth-bundle upgrade. What remains open on the discrete spine are
\emph{extensions} of the same upstream bridge---Haar measure on rotated charts, general
flat HQVM kinetic invariance under \texttt{boostDiscretePotential41}, forbidden transitions, radiative normalization,""",
        r"""obligations (\hyperref[lean:anomaly-cancellation]{anomaly cancellation},
\hyperref[lean:patch-topology-discharge]{patch topology discharge}),
plus rapidity-phase and spatial-rotation Lorentz closure on the flat patch chart
(\hyperref[lean:rapidity-lorentz-closure]{rapidity--Lorentz closure},
\hyperref[lean:spatial-rotation-lorentz-closure]{spatial-rotation Lorentz closure}),
full four-edge SO(8) Wilson plaquettes, abelian Wilson--kinetic equivalence, and a partial
strong-interacting discrete-action Poincaré bundle
(\hyperref[lean:so8-plaquette]{SO(8) plaquette holonomy},
\hyperref[lean:action-holonomy-glue]{action holonomy glue},
\hyperref[lean:discrete-action-poincare]{discrete action Poincaré programme})---not a continuum path-integral or
smooth-bundle upgrade. What remains open on the discrete spine are
\emph{extensions} of the same upstream bridge---Haar measure on rotated charts, general
flat HQVM kinetic invariance under the strong-Poincaré bridge, forbidden transitions, radiative normalization,""",
    ),
    (
        r"with trimer-width and stoichiometric D-budget slots in Lean\n(\texttt{BBNStoichiometricIntegrator}).",
        r"with trimer-width and stoichiometric D-budget slots\n(\hyperref[lean:bbn-stoichiometric]{BBN stoichiometric integrator}).",
    ),
    (
        r"(\leanid{fresnelCaustic}, \leanid{sphericalFresnelEnvelope}): vacuum-mode density",
        r"(\hyperref[lean:hqiv-nuclei]{Fresnel caustic envelope}): vacuum-mode density",
    ),
    (
        r"\leanid{valleyPotential} is the scalar reduction",
        r"the \hyperref[lean:hqiv-nuclei]{valley potential} is the scalar reduction",
    ),
    (
        r"(\leanid{valleyCount}, proved additive in \leanid{valleys\_are\_additive}).",
        r"(\hyperref[lean:hqiv-nuclei-valley-scaffold]{valley count}, proved additive).",
    ),
    (
        r"Witness export: \path{scripts/hqiv\_nuclear\_caustic\_binding.py},\n\path{scripts/hqiv\_nuclear\_inside\_outside\_binding.py},\n\path{data/isotope\_pdg\_benchmark.json}.",
        r"Witness export: \hyperref[app:scripts]{nuclear caustic binding script},\n\hyperref[app:scripts]{inside/outside binding script},\n\hyperref[app:scripts]{isotope benchmark JSON}.",
    ),
    (
        r"(\leanid{deuteronBindingScale}$\,=\gamma\cdot\texttt{modes}/R_m$), then the",
        r"(\hyperref[lean:hqiv-nuclei]{deuteron binding scale}$\,=\gamma\cdot\texttt{modes}/R_m$), then the",
    ),
    (
        r"(\leanid{helium4\_valleyCount}, \leanid{tetrahedralClosureCausticScale}).",
        r"(\hyperref[lean:hqiv-nuclei]{helium-4 valley count}, \hyperref[lean:hqiv-nuclei]{tetrahedral closure caustic}).",
    ),
    (
        r"(\leanfile{Hqiv/Algebra/PhaseLiftDelta.lean}, \leanid{phaseLiftDelta\_antisymm}); ledger separation",
        r"(\hyperref[lean:phase-lift-delta]{phase-lift skew generator}); ledger separation",
    ),
    (
        r"\leanid{TrapWeakBridgeDecoherenceSlot}.",
        r"\hyperref[lean:neutron-lifetime-method]{trap weak-bridge decoherence slot}.",
    ),
    (
        r"\leanid{weakBetaChannelOpen} and Fano/Hopf bridge steps.",
        r"\hyperref[lean:weak-channel-open]{weak beta channel open} and Fano/Hopf bridge steps.",
    ),
    (
        r"(\leanid{temperature\_ppm\_insufficient\_for\_bottle\_beam\_split}).",
        r"(\hyperref[lean:neutron-lifetime-method]{bottle/beam temperature insensitivity}).",
    ),
    (
        r"(\path{scripts/hqiv\_dynamic\_nucleon\_pn.py},\n\path{scripts/hqiv\_dynamic\_beta\_isotope.py}):",
        r"(\hyperref[app:scripts]{dynamic nucleon p/n script},\n\hyperref[app:scripts]{dynamic beta isotope script}):",
    ),
    (
        r"\path{scripts/hqiv\_isotope\_stability\_halflife.py}.",
        r"\hyperref[app:scripts]{isotope stability half-life script}.",
    ),
    (
        r"Witness export: \path{scripts/hqiv\_isotope\_pdg\_benchmark.py}\n(\texttt{curvature\_imprint\_control} in \path{data/isotope\_pdg\_benchmark.json}).",
        r"Witness export: \hyperref[app:scripts]{isotope PDG benchmark script}\n(curvature-imprint control in \hyperref[app:scripts]{benchmark JSON}).",
    ),
    (
        r"\path{scripts/hqiv\_homogeneous\_curvature\_feedback.py}):",
        r"\hyperref[app:scripts]{homogeneous curvature feedback script}):",
    ),
    (
        r"(\path{scripts/hqiv\_thermodynamic\_phase\_from\_tp.py}). Cell constants remain derived",
        r"(\hyperref[app:scripts]{thermodynamic phase script}). Cell constants remain derived",
    ),
    (
        r"``phaseParticipationEta''; Lean \leanid{localFieldDivisorFromEta},\n\leanid{solidOnsagerLocalFieldDivisor}, \leanid{phaseOrientationCmFactorTetrahedralIh})---a",
        r"optical phase participation; \hyperref[lean:phase-material-response]{local-field divisor from $\eta$},\n\hyperref[lean:phase-material-response]{Onsager solid divisor}, \hyperref[lean:phase-material-response]{ice Ih orientation factor})---a",
    ),
    (
        r"\item HQIV witnesses from \path{scripts/hqiv_phase_geometry_density.py} and\n  \path{scripts/hqiv_phase_material_response.py} at the species solidification temperature.",
        r"\item HQIV witnesses from \hyperref[app:scripts]{phase geometry density script} and\n  \hyperref[app:scripts]{phase material response script} at the species solidification temperature.",
    ),
    (
        r"\path{scripts/hqiv_phase_geometry_density.py} and\n\path{scripts/hqiv_phase_material_response.py} accept any GMTKN55 name",
        r"\hyperref[app:scripts]{phase geometry density script} and\n\hyperref[app:scripts]{phase material response script} accept any GMTKN55 name",
    ),
    (
        r"\path{scripts/hqiv_phase_geometry_density.py},\n\path{scripts/hqiv_phase_material_response.py},\n\path{scripts/hqiv_thermodynamic_phase_from_tp.py},\n\path{scripts/hqiv_homogeneous_curvature_feedback.py}.",
        r"\hyperref[app:scripts]{phase geometry density script},\n\hyperref[app:scripts]{phase material response script},\n\hyperref[app:scripts]{thermodynamic phase script},\n\hyperref[app:scripts]{homogeneous curvature feedback script}.",
    ),
    (
        r"from \path{scripts/hqiv_curvature_contact_network.py}, and glass branches from",
        r"from \hyperref[app:scripts]{curvature contact network script}, and glass branches from",
    ),
    (
        r"Python: \path{scripts/hqiv_nuclear_outside_temperature_dynamics.py}\n(\path{local\_curvature\_neutrino\_opacity\_barn},\n\path{local\_curvature\_weak\_width\_factor\_band}).\n(\path{scripts/hqiv\_bbn\_integrator.py}, \path{scripts/hqiv\_bbn\_condition\_decay.py};\nwitness \texttt{data/bbn\_integrator.json}).",
        r"Python: \hyperref[app:scripts]{outside temperature dynamics script}\n(local $\nu$-opacity and weak-width factor bands).\n(\hyperref[app:scripts]{BBN integrator script}, \hyperref[app:scripts]{BBN condition-decay script};\nwitness \hyperref[app:scripts]{BBN integrator JSON}).",
    ),
    (
        r"Witness scripts (\path{scripts/hqiv_isotope_stability_halflife.py},\n\path{scripts/hqiv_isotope_pdg_benchmark.py}) export comparison tables with",
        r"Witness scripts (\hyperref[app:scripts]{isotope stability script},\n\hyperref[app:scripts]{isotope PDG benchmark script}) export comparison tables with",
    ),
    (
        r"(\leanid{trapWeakWidthFactorFromMagnetic}), distinct from neV Zeeman energy;",
        r"(\hyperref[lean:neutron-lifetime-method]{trap magnetic width factor}), distinct from neV Zeeman energy;",
    ),
    (
        r"(\leanid{temperature\_ppm\_insufficient\_for\_bottle\_beam\_split});",
        r"(\hyperref[lean:neutron-lifetime-method]{bottle/beam temperature insensitivity});",
    ),
    (
        r"references (\leanid{central\_brackets\_bottle\_beam\_refs});",
        r"references (\hyperref[lean:neutron-lifetime-method]{bottle/beam reference band});",
    ),
    (
        r"(\leanid{beam\_tau\_gt\_bottle\_from\_magnetic\_trap\_dressing}).",
        r"(\hyperref[lean:neutron-lifetime-method]{beam exceeds bottle from trap dressing}).",
    ),
    (
        r"\leanid{TrapWeakBridgeDecoherenceSlot} beyond the structural $f(B)$ slot.\nWitness export: \path{scripts/hqiv\_isotope\_pdg\_benchmark.py}.",
        r"\hyperref[lean:neutron-lifetime-method]{trap weak-bridge decoherence slot} beyond the structural $f(B)$ slot.\nWitness export: \hyperref[app:scripts]{isotope PDG benchmark script}.",
    ),
    (
        r"\item Quantitative magnitudes for \leanid{TrapWeakBridgeDecoherenceSlot} and UCN",
        r"\item Quantitative magnitudes for \hyperref[lean:neutron-lifetime-method]{trap weak-bridge decoherence slot} and UCN",
    ),
    (
        r"  \leanid{TrapWeakBridgeDecoherenceSlot} beyond the structural $f(B)$ slot;",
        r"  \hyperref[lean:neutron-lifetime-method]{trap weak-bridge decoherence slot} beyond the structural $f(B)$ slot;",
    ),
    (
        r"is the same Pauli/meta ledger that odd--odd nuclei book in \texttt{HQIVNuclei}.",
        r"is the same Pauli/meta ledger that odd--odd nuclei book in the \hyperref[lean:hqiv-nuclei]{HQIV nuclei module}.",
    ),
    (
        r"Recompute: \texttt{hqiv\_bbn\_integrator.py}; tables: \texttt{hqiv\_bbn\_paper\_tables.py}.",
        r"Recompute: \hyperref[app:scripts]{BBN integrator script}; tables: \hyperref[app:scripts]{BBN paper tables script}.",
    ),
    (
        r"$\beta$ width qualification (`betaWidthLedgerQualified`) & proved wiring",
        r"$\beta$ width qualification & proved wiring",
    ),
]


def main() -> None:
    text = TEX.read_text(encoding="utf-8")
    appendix = text.find(r"\appendix")
    if appendix < 0:
        raise SystemExit("appendix marker not found")
    head, tail = text[:appendix], text[appendix:]
    for old, new in REPLACEMENTS_BEFORE_APPENDIX:
        if old not in head:
            print(f"WARN: pattern not found ({old[:60]!r}...)")
        else:
            head = head.replace(old, new)
    TEX.write_text(head + tail, encoding="utf-8")
    print(f"polished {TEX}")


if __name__ == "__main__":
    main()
