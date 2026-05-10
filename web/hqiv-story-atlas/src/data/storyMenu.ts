/**
 * Physics-first map of `Hqiv/Story/*.lean`.
 * Omitted on purpose: Plastic-phase and RH bridges, Arity/FTA/power-presentation/zeta-zero spines,
 * NearDiagonalThreeCubes, test shards — pure-math tracks that do not carry physics narrative.
 */

export type CategoryId =
  | "foundations"
  | "gr"
  | "gut"
  | "nuclear"
  | "thermo"
  | "qm"
  | "qft";

export interface StoryItem {
  id: string;
  title: string;
  leanPath: string;
  summary: string;
  derivationId?: string;
  tentPole?: boolean;
  /** Short chips for hover / search later */
  tags?: string[];
}

export interface CategoryDef {
  id: CategoryId;
  navLabel: string;
  headline: string;
  intro: string;
  items: StoryItem[];
}

const rawCategories: CategoryDef[] = [
  {
    id: "foundations",
    navLabel: "TD",
    headline: "ThermoDynamics foundation: ladder substrate, shells, and conserved readouts",
    intro:
      "Null-lattice mode counts, temperature ladder T(m), auxiliary field φ, reference shell, and the SO(8) Lie-algebra hook that later closes with G₂ and Δ in the gauge story.",
    items: [
      {
        id: "ch01",
        title: "Chapter 1 — Light cone and auxiliary field",
        leanPath: "Hqiv/Story/Chapter01_Foundation.lean",
        derivationId: "lightcone-foundation",
        summary:
          "Discrete null data, δ_E ladder, referenceM, and φ on T(m)=1/(m+1). Feeds the entire mass-gap spine (`MassGap.step01_…`).",
        tentPole: true,
        tags: ["light cone", "φ ladder", "reference shell"],
      },
      {
        id: "lc-3d-intuition",
        title: "Chapter 1A — 3D light cone intuition",
        leanPath: "Hqiv/Geometry/OctonionicLightCone.lean",
        derivationId: "lightcone-3d-intuition",
        summary:
          "Why shell counting uses triples: each shell is a nonnegative integer decomposition x+y+z=m in three spatial directions.",
        tags: ["3D light cone", "shells", "x+y+z=m"],
      },
      {
        id: "lc-simplex",
        title: "Chapter 1B — Light-cone simplex count",
        leanPath: "Hqiv/Geometry/OctonionicLightCone.lean",
        derivationId: "lightcone-simplex-count",
        summary:
          "Stars-and-bars count on shell m: latticeSimplexCount(m) = (m+2)(m+1), then available mode scaling on the same lattice.",
        tags: ["stars and bars", "mode count", "latticeSimplexCount"],
      },
      {
        id: "aux-temp-phi",
        title: "Chapter 1C — Temperature ladder and auxiliary field",
        leanPath: "Hqiv/Geometry/AuxiliaryField.lean",
        derivationId: "auxiliary-field-ladder",
        summary:
          "Temperature ladder T(m)=1/(m+1) and φ(m)=2/T(m), with positivity and closed form φ(m)=2(m+1).",
        tags: ["temperature ladder", "auxiliary field", "phi_of_shell"],
      },
      {
        id: "lc-cumulative",
        title: "Chapter 1D — Cumulative count and hockey-stick",
        leanPath: "Hqiv/Geometry/OctonionicLightCone.lean",
        derivationId: "lightcone-cumulative-hockeystick",
        summary:
          "Cumulative simplex count and closed form: 3*cum(n)=(n+1)(n+2)(n+3), giving integer divisibility and monotonic growth.",
        tags: ["cumulative", "hockey stick", "monotone"],
      },
      {
        id: "lc-modes",
        title: "Chapter 1E — Available and new modes",
        leanPath: "Hqiv/Geometry/OctonionicLightCone.lean",
        derivationId: "lightcone-available-new-modes",
        summary:
          "From simplex count to available modes and shell increments: available_modes(m)=4(m+2)(m+1), new_modes(m+1)=8(m+2).",
        tags: ["available_modes", "new_modes", "increments"],
      },
      {
        id: "lc-alpha",
        title: "Chapter 1F — Alpha calibration and lattice check",
        leanPath: "Hqiv/Geometry/OctonionicLightCone.lean",
        derivationId: "lightcone-alpha-ratio",
        summary:
          "α is set in this file and then validated against a lattice ratio identity and limit behavior (consistency check, not first-principles derivation here).",
        tags: ["alpha", "3/5", "ratio", "limit"],
      },
      {
        id: "lc-reference-shell",
        title: "Chapter 1G — QCD and reference shell indexing",
        leanPath: "Hqiv/Geometry/OctonionicLightCone.lean",
        derivationId: "lightcone-reference-shell",
        summary:
          "Defines qcdShell, latticeStepCount, and referenceM alignment used as lock-in pin.",
        tags: ["qcdShell", "referenceM", "lock-in"],
      },
      {
        id: "lc-curvature-norm",
        title: "Chapter 1H — Curvature norm from cube structure",
        leanPath: "Hqiv/Geometry/OctonionicLightCone.lean",
        derivationId: "lightcone-curvature-norm",
        summary:
          "Curvature normalization built from cube directions and octonion dimension; combinatorial norm chain.",
        tags: ["curvature norm", "cube", "octonion"],
      },
      {
        id: "lc-deltaE",
        title: "Chapter 1I — DeltaE shell imprint",
        leanPath: "Hqiv/Geometry/OctonionicLightCone.lean",
        derivationId: "lightcone-deltaE-imprint",
        summary:
          "δE shell imprint formulas tie shell shape to curvature normalization choices.",
        tags: ["deltaE", "shell_shape", "imprint"],
      },
      {
        id: "lc-omega-k",
        title: "Chapter 1J — Horizon-dependent Omega_k",
        leanPath: "Hqiv/Geometry/OctonionicLightCone.lean",
        derivationId: "lightcone-omega-k-horizon",
        summary:
          "Curvature integral readouts define Ω_k at horizon N; explicitly horizon-dependent and dynamic.",
        tags: ["Omega_k", "horizon", "curvature integral"],
      },
      {
        id: "lattice-continuum",
        title: "Lattice ↔ continuum spacetime interface",
        leanPath: "Hqiv/Story/LatticeContinuumSpacetimeInterface.lean",
        derivationId: "lattice-continuum-interface",
        summary:
          "Discrete indices vs continuous ℝ⁴ (`SpacetimeEuclidean4`) — vocabulary where patch QFT meets the bulk.",
        tags: ["Fin 4", "chart", "interface"],
      },
      {
        id: "octonion-lie",
        title: "Octonion SO(8) Lie DOF",
        leanPath: "Hqiv/Story/OctonionLieDOF.lean",
        derivationId: "so8-closure-backbone",
        summary:
          "28 = dim so(8): matrix generator closure packaged for the Story spine (same mathematics as SO8 closure shards).",
        tentPole: true,
        tags: ["SO(8)", "octonion", "Lie algebra"],
      },
      {
        id: "td-three-laws",
        title: "TD Capstone — Derivation of the three laws",
        leanPath: "Hqiv/Physics/ThermodynamicLawsFromLadder.lean",
        derivationId: "td-three-laws-capstone",
        summary:
          "Concrete Zeroth/First/Second law packaging from T(m), finite-window conserved temperature redistribution, and discrete heat dissipation/CFL monotonicity.",
        tentPole: true,
        tags: ["thermodynamics", "zeroth", "first", "second", "capstone"],
      },
    ],
  },
  {
    id: "gr",
    navLabel: "GR",
    headline: "HQVM metric and horizon-scale effective gravity",
    intro:
      "Lapse N = 1 + Φ + φ·t, monogamy coefficient γ, and the Friedmann-side interface built on the same substrate as Chapter 1.",
    items: [
      {
        id: "ch02",
        title: "Chapter 2 — HQVM metric",
        leanPath: "Hqiv/Story/Chapter02_Metric.lean",
        derivationId: "hqvm-time-angle",
        summary:
          "Time-angle monotonicity along each shell’s φ(m); bridges to conservations and the harmonic ladder (`MassGap.step02_…`).",
        tentPole: true,
        tags: ["lapse", "Friedmann", "time angle", "γ"],
      },
    ],
  },
  {
    id: "gut",
    navLabel: "GUT",
    headline: "Conservations, action, and covariance on the light-cone substrate",
    intro:
      "This section now follows derivation order: start from conservations, then build action on those conserved structures, then derive O-Maxwell form through source and continuum/covariant closures.",
    items: [
      {
        id: "gut-why-this-section",
        title: "GUT Prelude — What problem are we solving?",
        leanPath: "Hqiv/Physics/Action.lean",
        derivationId: "gut-derivation-motivation",
        summary:
          "State the target before symbols: derive a field equation from conserved structure, not from late force labels.",
        tags: ["motivation", "derivation target", "O-Maxwell"],
      },
      {
        id: "gut-why-conservations-first",
        title: "GUT Prelude — Why conservations come first",
        leanPath: "Hqiv/Conservations.lean",
        derivationId: "gut-why-conservations-first",
        summary:
          "Explain derivation logic: invariants first, dynamics second, equation-of-motion last.",
        tags: ["invariants", "ordering", "derivation logic"],
      },
      {
        id: "gut-complex",
        title: "GUT S1 — Complex numbers as phase language",
        leanPath: "Hqiv/Algebra/OctonionBasics.lean",
        derivationId: "gut-complex-phase-language",
        summary:
          "Introduce i and phase rotation first, so later gauge-phase statements are readable instead of symbolic jumps.",
        tags: ["complex numbers", "phase", "rotation"],
      },
      {
        id: "gut-quaternion",
        title: "GUT S2 — Quaternions as 3D rotation algebra",
        leanPath: "Hqiv/Algebra/OctonionBasics.lean",
        derivationId: "gut-quaternion-rotation-bridge",
        summary:
          "Move from one imaginary unit to three (i,j,k) and show why non-commutativity appears before octonions.",
        tags: ["quaternion", "rotation", "non-commutative"],
      },
      {
        id: "gut-octonion",
        title: "GUT S3 — Octonions and the 8D basis",
        leanPath: "Hqiv/Algebra/OctonionBasics.lean",
        derivationId: "gut-octonion-basis-bridge",
        summary:
          "Upgrade quaternion intuition to octonion basis e0..e7 used in the O-indexed field equations.",
        tags: ["octonion", "basis", "Fin 8"],
      },
      {
        id: "gut-fano-plane",
        title: "GUT S4 — Fano plane multiplication map",
        leanPath: "Hqiv/OctonionLeftMultiplication.lean",
        derivationId: "gut-fano-plane-multiplication",
        summary:
          "Use the Fano-plane multiplication wiring to explain how imaginary-unit products are organized.",
        tags: ["Fano plane", "multiplication", "unit triples"],
      },
      {
        id: "gut-nonassociative",
        title: "GUT S5 — Loss of associativity and associator",
        leanPath: "Hqiv/Algebra/OctonionBasics.lean",
        derivationId: "gut-nonassociativity-associator",
        summary:
          "Define the associator explicitly and explain why octonion non-associativity matters for structure-level conservation packaging.",
        tags: ["associator", "non-associative", "octonion"],
      },
      {
        id: "gut-conservations",
        title: "GUT A0 — Conservations in structure from O",
        leanPath: "Hqiv/Conservations.lean",
        derivationId: "gut-conservations-structure-from-o",
        summary:
          "Lay out the conserved structure first (phase/metric-constrained channel) before introducing action and Euler-Lagrange packaging.",
        tags: ["conservations", "structure from O", "phase"],
      },
      {
        id: "gut-phase-anchor-start",
        title: "GUT A0a — Phase anchor at start",
        leanPath: "Hqiv/Conservations.lean",
        derivationId: "gut-phase-anchor-start",
        summary:
          "Visualize and interpret δθ′(0)=0 as the initial anchor in phase evolution.",
        tags: ["phase", "initial condition", "anchor"],
      },
      {
        id: "gut-phase-anchor-cycle",
        title: "GUT A0b — Phase anchor at cycle endpoint",
        leanPath: "Hqiv/Conservations.lean",
        derivationId: "gut-phase-anchor-cycle",
        summary:
          "Visualize δθ′(2π/ϕ)=2π as full-cycle closure in phase space.",
        tags: ["phase", "cycle closure", "2pi"],
      },
      {
        id: "gut-phase-bounded",
        title: "GUT A0c — Bounded phase evolution",
        leanPath: "Hqiv/Conservations.lean",
        derivationId: "gut-phase-bounded-evolution",
        summary:
          "Show that all intermediate times stay inside the conserved phase band [0,2π].",
        tags: ["phase band", "bounded evolution", "conservation"],
      },
      {
        id: "gut-action-core",
        title: "GUT A1 — Action core objects",
        leanPath: "Hqiv/Physics/Action.lean",
        derivationId: "gut-action-core-terms",
        summary:
          "Introduce A, F, source J, phi-coupling, and EL slots one object at a time before full covariant packaging.",
        tags: ["Action", "A_O", "F_from_A", "EL"],
      },
      {
        id: "gut-action-plasma",
        title: "GUT A2 — Plasma source bridge",
        leanPath: "Hqiv/Physics/ActionPlasmaBridge.lean",
        derivationId: "gut-action-plasma-bridge",
        summary:
          "Specialize generic source J_src to schematic plasma current and show action/EL slots remain structurally aligned.",
        tags: ["plasma", "J_O_plasma", "source bridge"],
      },
      {
        id: "gut-continuum-closure",
        title: "GUT A3 — Continuum O-Maxwell closure",
        leanPath: "Hqiv/Physics/ContinuumOmaxwellClosure.lean",
        derivationId: "gut-continuum-omaxwell-closure",
        summary:
          "Replace placeholder grad_phi with continuum chart gradients and keep action/EL correspondence explicit.",
        tags: ["continuum chart", "grad phi", "closure"],
      },
      {
        id: "gut-covariant",
        title: "GUT A4 — Covariant solution packaging",
        leanPath: "Hqiv/Physics/CovariantSolution.lean",
        derivationId: "gut-covariant-packaging",
        summary:
          "Move from pre-metric surrogates to metric-aware divergence/Christoffel forms on HQVM background.",
        tags: ["covariant", "HQVM metric", "divergence"],
      },
    ],
  },
  {
    id: "nuclear",
    navLabel: "Nuclear",
    headline: "Shell-resolved couplings and binding (mass ladder)",
    intro:
      "Harmonic ladder, α_eff at shell, and hydrogenic-style binding magnitudes — the particle-mass tent pole without PDG fitting in the Story layer.",
    items: [
      {
        id: "ch04",
        title: "Chapter 4 — Harmonic ladder and mass couplings",
        leanPath: "Hqiv/Story/Chapter04_MassLadder.lean",
        derivationId: "harmonic-mass-ladder",
        summary:
          "m → T → φ → shell_shape → α_eff and E_bind on shell (`harmonic_ladder_mass_coupling_chain`). Feeds QCD / lock-in geometry.",
        tentPole: true,
        tags: ["particle masses", "α_eff", "binding", "shell"],
      },
      {
        id: "lattice-spectral",
        title: "Lattice-primary spectral bridge",
        leanPath: "Hqiv/Story/LatticePrimarySpectralBridge.lean",
        summary: "Spectral-side bridge tying lattice-primary data to the Story spine.",
        tags: ["spectrum", "lattice"],
      },
    ],
  },
  {
    id: "qm",
    navLabel: "QM",
    headline: "Patch Hilbert space, Schwartz analysis, and toy quantum carriers",
    intro:
      "Schwartz lifts, patch carriers, and minimal unitary / Wightman toy witnesses that prefigure the QFT layer.",
    items: [
      {
        id: "schwartz-lift",
        title: "Schwartz ℝ → ℂ lift",
        leanPath: "Hqiv/Story/SchwartzRealToComplexLift.lean",
        summary: "Real Schwartz functions as complex-valued Schwartz functions — analytic spine for pairing.",
        tags: ["Schwartz", "test functions"],
      },
      {
        id: "patch-hilbert",
        title: "Patch Hilbert bridge",
        leanPath: "Hqiv/Story/PatchHilbertBridge.lean",
        summary: "Patch Hilbert space ↔ Dojo-style carrier bridge.",
        tags: ["Hilbert", "carrier"],
      },
      {
        id: "patch-wightman-toy",
        title: "Patch Hilbert ↔ 1D Wightman toy",
        leanPath: "Hqiv/Story/PatchToWightmanToyHilbertBridge.lean",
        summary: "Toy bridge between patch Hilbert scaffolding and one-dimensional Wightman data.",
        tags: ["Wightman", "toy"],
      },
      {
        id: "mill-poincare",
        title: "Millennium — Poincaré unitary rep + 1D Wightman scaffold",
        leanPath: "Hqiv/Story/MillenniumBridgePoincareWightman.lean",
        summary: "Trivial Poincaré representation packaged with a one-line Wightman-style scaffold.",
        tags: ["Poincaré", "Wightman"],
      },
    ],
  },
  {
    id: "qft",
    navLabel: "QFT",
    headline: "Patch nets, SO(8) gauge packaging, Yang–Mills, and Clay witness wiring",
    intro:
      "Local patch algebra, SO(8) compact gauge group construction, non-abelian fields, YM interface witnesses, mass-gap completion packaging, and Chapter 8’s formal Problem wiring.",
    items: [
      {
        id: "gauge-sketch",
        title: "Gauge group from HQIV sketch (G₂ / 14D story)",
        leanPath: "Hqiv/Story/GaugeGroupFromHQIVSketch.lean",
        summary: "Gauge-slot sketch aligned with the G₂ and fourteen-dimensional narrative.",
        tags: ["G₂", "gauge"],
      },
      {
        id: "hqiv-gauge-blueprint",
        title: "HQIV gauge construction blueprint",
        leanPath: "Hqiv/Story/HQIVGaugeConstructionBlueprint.lean",
        derivationId: "rapidity-aux-to-gauge",
        summary: "O–Maxwell + SO(8) closure + rapidity → `CompactSimpleGaugeGroup` roadmap.",
        tentPole: true,
        tags: ["SO(8)", "rapidity", "closure", "Δ"],
      },
      {
        id: "so8-gauge-group",
        title: "SO(8) as compact simple gauge group",
        leanPath: "Hqiv/Story/HQIVSO8GaugeGroupConstruction.lean",
        summary: "SO(8) realized as a `CompactSimpleGaugeGroup` carrier for Dojo-facing statements.",
        tentPole: true,
        tags: ["SO(8)", "gauge group"],
      },
      {
        id: "lie-feed",
        title: "Matrix Lie data for HQIV QFT",
        leanPath: "Hqiv/Story/HQIVQFTLieAlgebraFeed.lean",
        summary: "Lie algebra matrices feeding QFT without importing the full SO(8) closure proof chain.",
        tags: ["Lie algebra", "matrices"],
      },
      {
        id: "so8-core-witness",
        title: "SO(8) completion-core witness",
        leanPath: "Hqiv/Story/SO8CompletionCoreWitness.lean",
        summary: "Witness scaffold at the SO(8) completion core used in YM packaging.",
        tags: ["SO(8)", "completion"],
      },
      {
        id: "so8-core-candidate",
        title: "SO(8) completion-core candidate",
        leanPath: "Hqiv/Story/SO8CompletionCoreCandidate.lean",
        summary: "Candidate endpoint lemmas for the completion core.",
        tags: ["SO(8)"],
      },
      {
        id: "ym-core-so8",
        title: "YM completion core (SO(8))",
        leanPath: "Hqiv/Story/YMCompletionCoreSO8.lean",
        summary: "SO(8) completion-core endpoint specialized for Yang–Mills.",
        tags: ["YM", "SO(8)"],
      },
      {
        id: "o-maxwell-hub",
        title: "O–Maxwell + patch QM → Dojo slot",
        leanPath: "Hqiv/Story/OMaxwellQMToDojoSlot.lean",
        summary: "Construction hub linking O–Maxwell, patch quantum mechanics, and Dojo / YM slots.",
        tags: ["O–Maxwell", "patch QM", "Dojo"],
      },
      {
        id: "ym-inputs-well",
        title: "YM inputs from well dynamics",
        leanPath: "Hqiv/Story/YMInputsFromWellDynamics.lean",
        summary: "Yang–Mills input scaffold extracted from well dynamics hypotheses.",
        tags: ["YM", "well"],
      },
      {
        id: "ym-helpers",
        title: "YM bridge — proved helpers",
        leanPath: "Hqiv/Story/YMBridgeProvedHelpers.lean",
        summary: "Small discharged lemmas for Clay / Dojo spectral packaging.",
        tags: ["YM", "spectral"],
      },
      {
        id: "ym-obligations",
        title: "YM — remaining bridge obligations",
        leanPath: "Hqiv/Story/YMRemainingObligations.lean",
        summary: "Explicit promotion queue for the HQIV-facing `QuantumYangMillsTheory` interface witness.",
        tentPole: true,
        tags: ["YM", "mass gap", "promotion"],
      },
      {
        id: "qym-interface",
        title: "Quantum Yang–Mills HQIV interface witness",
        leanPath: "Hqiv/Story/QuantumYangMillsHQIVInterface.lean",
        summary: "Alignment witness between HQIV hypotheses and Dojo’s Yang–Mills interface.",
        tags: ["YM", "interface"],
      },
      {
        id: "qym-poincare-toy",
        title: "Quantum Yang–Mills from Poincaré toy",
        leanPath: "Hqiv/Story/QuantumYangMillsFromPoincareToy.lean",
        summary: "Minimal Schwartz-spine `QuantumYangMillsTheory` certificate on the toy spine.",
        tags: ["YM", "Schwartz", "toy"],
      },
      {
        id: "qym-patch",
        title: "Quantum Yang–Mills from patch HQIV",
        leanPath: "Hqiv/Story/QuantumYangMillsFromPatchHQIV.lean",
        summary: "Patch-layer data promoted into the same minimal YM interface as the toy constructor.",
        tags: ["YM", "patch"],
      },
      {
        id: "patch-qft-so8",
        title: "HQIV patch-QFT inputs (SO(8))",
        leanPath: "Hqiv/Story/HQIVPatchQFTInputsSO8.lean",
        summary: "SO(8)-aware package of patch-QFT hypotheses feeding downstream constructors.",
        tags: ["patch QFT", "SO(8)"],
      },
      {
        id: "ch07",
        title: "Chapter 7 — Patch QFT",
        leanPath: "Hqiv/Story/Chapter07_PatchQFT.lean",
        derivationId: "patch-commutator-locality",
        summary:
          "Support-restricted net on Fin 4 patches; abelian smeared fields; Minkowski hooks toward microcausality (`step07_patchAbelianCommutator`).",
        tentPole: true,
        tags: ["patch", "locality", "microcausality"],
      },
      {
        id: "nonabelian-patch",
        title: "Non-abelian SO(8) smeared patch field",
        leanPath: "Hqiv/Story/NonabelianSO8SmearedPatchField.lean",
        summary: "First non-abelian smeared field on the patch carrier — beyond abelian commutator zeros.",
        tags: ["SO(8)", "non-abelian", "smeared field"],
      },
      {
        id: "mill-schwartz",
        title: "Millennium — Schwartz jets at the origin",
        leanPath: "Hqiv/Story/MillenniumBridgePatchSchwartzJets.lean",
        summary: "Patch smearing: Schwartz jet surjectivity at the origin.",
        tags: ["Schwartz", "jets", "smearing"],
      },
      {
        id: "mill-patch-pw",
        title: "Millennium — patch Hilbert + Wightman + ladder Hamiltonian",
        leanPath: "Hqiv/Story/MillenniumBridgePatchPoincareWightman.lean",
        summary: "Patch Hilbert Wightman layer with ladder-scaled Hamiltonian packaging.",
        tags: ["Wightman", "Hamiltonian", "patch"],
      },
      {
        id: "mill-patch-vacuum",
        title: "Millennium — patch vacuum vector",
        leanPath: "Hqiv/Story/MillenniumBridgePatchVacuum.lean",
        summary: "Concrete gauge group G, patch Hilbert slot, and vacuum vector witness.",
        tags: ["vacuum", "Hilbert"],
      },
      {
        id: "mill-toy",
        title: "Millennium — toy witness",
        leanPath: "Hqiv/Story/MillenniumBridgeToyWitness.lean",
        summary: "Explicit Hilbert slot with assumed Clay body — pedagogical witness.",
        tags: ["toy", "Clay"],
      },
      {
        id: "mill-finite-mass",
        title: "Millennium — finite mass spectrum obstruction note",
        leanPath: "Hqiv/Story/MillenniumFiniteMassObstruction.lean",
        summary: "`FiniteMassSpectrum` vs unbounded mass-gap parameters — conceptual guardrail.",
        tags: ["mass spectrum", "Clay"],
      },
      {
        id: "mass-gap-wiring",
        title: "Mass-gap wiring",
        leanPath: "Hqiv/Story/MassGapWiring.lean",
        summary: "What is proved, where the analytic gap remains, and how chapters close around it.",
        tentPole: true,
        tags: ["mass gap", "roadmap"],
      },
      {
        id: "mass-gap-bundle",
        title: "Mass-gap completion bundle",
        leanPath: "Hqiv/Story/MassGapCompletionBundle.lean",
        summary: "Assembling HQIV substrate with the Clay `Prop` packaging.",
        tags: ["mass gap", "Clay"],
      },
      {
        id: "mass-gap-scaffold",
        title: "Mass-gap completion scaffold",
        leanPath: "Hqiv/Story/MassGapCompletionScaffold.lean",
        summary: "Partial `QuantumYangMillsTheory` builder from HQIV + completion hypotheses.",
        tags: ["YM", "scaffold"],
      },
      {
        id: "hqiv-no-stable-gap",
        title: "No stable continuum mass gap (ontology note)",
        leanPath: "Hqiv/Story/HQIVNoStableContinuumMassGap.lean",
        summary: "Specification of emergent-HQIV mass-gap ontology vs continuum idealization.",
        tags: ["ontology", "mass gap"],
      },
      {
        id: "ch08",
        title: "Chapter 8 — Clay Millennium wiring",
        leanPath: "Hqiv/Story/Chapter08_ClayMillennium.lean",
        summary:
          "Vendored Yang–Mills / Navier–Stokes Problems + `Hqiv.Bridge.LeanDojo`: sufficient conditions, witness bundles, and explicit import of HQIV YM interface constructors.",
        tentPole: true,
        tags: ["Clay", "YM", "NS", "Dojo"],
      },
    ],
  },
];

const categoryOrder: CategoryId[] = ["foundations", "gut", "gr", "qm", "qft"];

export const categories: CategoryDef[] = rawCategories
  .filter((category) => category.id !== "nuclear" && category.id !== "thermo")
  .sort((a, b) => categoryOrder.indexOf(a.id) - categoryOrder.indexOf(b.id));

export function categoryById(id: CategoryId): CategoryDef | undefined {
  return categories.find((c) => c.id === id);
}

export function itemById(itemId: string): { category: CategoryDef; item: StoryItem } | undefined {
  for (const category of categories) {
    const item = category.items.find((i) => i.id === itemId);
    if (item) return { category, item };
  }
  return undefined;
}
