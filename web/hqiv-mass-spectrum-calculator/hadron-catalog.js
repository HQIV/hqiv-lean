/**
 * Hadron variety catalog: 12 structural classes → valid valence configurations
 * (meson through pentaquark). Filters enforce SM/HQIV color-composed bookkeeping:
 * baryons = 3 quarks; mesons = q + q̄; tetraquarks = 2q+2q̄; pentaquarks = 4q+1q̄ or 5q patterns.
 */
(function (root) {
  "use strict";

  const FLAVORS = ["u", "d", "s", "c", "b", "t"];

  /** @typedef {{ flavor: string, role: 'quark'|'antiquark' }} ValenceSlot */

  /**
   * @typedef {object} HadronConfig
   * @property {string} id
   * @property {string} label
   * @property {string} pdgName
   * @property {ValenceSlot[]} valence
   * @property {string} [note]
   */

  /**
   * @typedef {object} HadronVariety
   * @property {string} id
   * @property {string} label
   * @property {'baryon'|'meson'|'tetraquark'|'pentaquark'} structure
   * @property {number} valenceCount
   * @property {string} closureClass
   * @property {string} description
   * @property {HadronConfig[]} configs
   */

  function v(flavor, role) {
    return { flavor, role };
  }

  function baryonConfigs(lightOnly) {
    const all = [
      { id: "p", label: "p (uud)", pdgName: "proton", valence: [v("u", "quark"), v("u", "quark"), v("d", "quark")] },
      { id: "n", label: "n (udd)", pdgName: "neutron", valence: [v("u", "quark"), v("d", "quark"), v("d", "quark")] },
      { id: "lambda", label: "Λ (uds)", pdgName: "Lambda", valence: [v("u", "quark"), v("d", "quark"), v("s", "quark")] },
      { id: "sigma_plus", label: "Σ⁺ (uus)", pdgName: "Sigma+", valence: [v("u", "quark"), v("u", "quark"), v("s", "quark")] },
      { id: "sigma_zero", label: "Σ⁰ (uds)", pdgName: "Sigma0", valence: [v("u", "quark"), v("d", "quark"), v("s", "quark")] },
      { id: "sigma_minus", label: "Σ⁻ (dds)", pdgName: "Sigma-", valence: [v("d", "quark"), v("d", "quark"), v("s", "quark")] },
      { id: "xi_zero", label: "Ξ⁰ (uss)", pdgName: "Xi0", valence: [v("u", "quark"), v("s", "quark"), v("s", "quark")] },
      { id: "xi_minus", label: "Ξ⁻ (dss)", pdgName: "Xi-", valence: [v("d", "quark"), v("s", "quark"), v("s", "quark")] },
      { id: "omega", label: "Ω⁻ (sss)", pdgName: "Omega-", valence: [v("s", "quark"), v("s", "quark"), v("s", "quark")] },
    ];
    if (!lightOnly) {
      all.push(
        { id: "lambda_c", label: "Λ⁺_c (udc)", pdgName: "Lambda_c+", valence: [v("u", "quark"), v("d", "quark"), v("c", "quark")] },
        { id: "sigma_c", label: "Σ⁺_c (uuc)", pdgName: "Sigma_c+", valence: [v("u", "quark"), v("u", "quark"), v("c", "quark")] },
        { id: "xi_c", label: "Ξ⁰_c (usc)", pdgName: "Xi_c0", valence: [v("u", "quark"), v("s", "quark"), v("c", "quark")] },
        { id: "omega_c", label: "Ω⁰_c (ssc)", pdgName: "Omega_c0", valence: [v("s", "quark"), v("s", "quark"), v("c", "quark")] },
        { id: "lambda_b", label: "Λ⁰_b (udb)", pdgName: "Lambda_b0", valence: [v("u", "quark"), v("d", "quark"), v("b", "quark")] },
        { id: "xi_b", label: "Ξ⁻_b (dsb)", pdgName: "Xi_b-", valence: [v("d", "quark"), v("s", "quark"), v("b", "quark")] }
      );
    }
    return all;
  }

  const HADRON_VARIETIES = [
    {
      id: "baryon_octet",
      label: "Baryon — spin-½ octet (qqq)",
      structure: "baryon",
      valenceCount: 3,
      closureClass: "colorComposed · 3 channels",
      description: "Ground baryon octet; all valence quarks (no antiquarks).",
      configs: baryonConfigs(true),
    },
    {
      id: "baryon_decuplet",
      label: "Baryon — spin-¾ decuplet (qqq)",
      structure: "baryon",
      valenceCount: 3,
      closureClass: "colorComposed · excited J=3/2 scaffold",
      description: "Same flavor content as octet; excitation noted in trace (meta-horizon harmonic).",
      configs: [
        { id: "delta_pp", label: "Δ⁺⁺ (uuu)", pdgName: "Delta++", valence: [v("u", "quark"), v("u", "quark"), v("u", "quark")], note: "decuplet" },
        { id: "delta_p", label: "Δ⁺ (uud)", pdgName: "Delta+", valence: [v("u", "quark"), v("u", "quark"), v("d", "quark")], note: "decuplet" },
        { id: "delta_0", label: "Δ⁰ (udd)", pdgName: "Delta0", valence: [v("u", "quark"), v("d", "quark"), v("d", "quark")], note: "decuplet" },
        { id: "delta_m", label: "Δ⁻ (ddd)", pdgName: "Delta-", valence: [v("d", "quark"), v("d", "quark"), v("d", "quark")], note: "decuplet" },
        { id: "sigma_star_p", label: "Σ*⁺ (uus)", pdgName: "Sigma*+", valence: [v("u", "quark"), v("u", "quark"), v("s", "quark")], note: "decuplet" },
        { id: "sigma_star_0", label: "Σ*⁰ (uds)", pdgName: "Sigma*0", valence: [v("u", "quark"), v("d", "quark"), v("s", "quark")], note: "decuplet" },
        { id: "sigma_star_m", label: "Σ*⁻ (dds)", pdgName: "Sigma*-", valence: [v("d", "quark"), v("d", "quark"), v("s", "quark")], note: "decuplet" },
        { id: "xi_star_0", label: "Ξ*⁰ (uss)", pdgName: "Xi*0", valence: [v("u", "quark"), v("s", "quark"), v("s", "quark")], note: "decuplet" },
        { id: "xi_star_m", label: "Ξ*⁻ (dss)", pdgName: "Xi*-", valence: [v("d", "quark"), v("s", "quark"), v("s", "quark")], note: "decuplet" },
        { id: "omega_star", label: "Ω*⁻ (sss)", pdgName: "Omega*-", valence: [v("s", "quark"), v("s", "quark"), v("s", "quark")], note: "decuplet" },
      ],
    },
    {
      id: "baryon_charm",
      label: "Baryon — charmed (qqc)",
      structure: "baryon",
      valenceCount: 3,
      closureClass: "colorComposed",
      description: "Single heavy charm valence; includes doubly-charmed candidates.",
      configs: baryonConfigs(false).filter((c) => c.valence.some((x) => x.flavor === "c")),
    },
    {
      id: "baryon_bottom",
      label: "Baryon — bottom (qqb)",
      structure: "baryon",
      valenceCount: 3,
      closureClass: "colorComposed",
      description: "Bottom baryons (Λ_b, Ξ_b, …).",
      configs: baryonConfigs(false).filter((c) => c.valence.some((x) => x.flavor === "b")),
    },
    {
      id: "baryon_double_charm",
      label: "Baryon — doubly charmed (qqc)",
      structure: "baryon",
      valenceCount: 3,
      closureClass: "colorComposed · exotic count",
      description: "Two charm quarks in the same baryon (e.g. Ξ_cc+).",
      configs: [
        { id: "xi_cc_plus", label: "Ξ_cc+ (ucc)", pdgName: "Xi_cc+", valence: [v("u", "quark"), v("c", "quark"), v("c", "quark")] },
        { id: "xi_cc_plus_plus", label: "Ξ_cc++ (ucc) alt", pdgName: "Xi_cc++", valence: [v("u", "quark"), v("c", "quark"), v("c", "quark")] },
        { id: "omega_cc", label: "Ω_cc (scc)", pdgName: "Omega_cc", valence: [v("s", "quark"), v("c", "quark"), v("c", "quark")] },
        { id: "ccd", label: "ccd (ccd)", pdgName: "ccd", valence: [v("c", "quark"), v("c", "quark"), v("d", "quark")] },
      ],
    },
    {
      id: "meson_light_ps",
      label: "Meson — light pseudoscalar (q q̄)",
      structure: "meson",
      valenceCount: 2,
      closureClass: "colorComposed · qq̄ pair",
      description: "Pion / kaon / eta sector; one quark + one antiquark.",
      configs: [
        { id: "pi_plus", label: "π⁺ (u d̄)", pdgName: "pi+", valence: [v("u", "quark"), v("d", "antiquark")] },
        { id: "pi_minus", label: "π⁻ (d ū)", pdgName: "pi-", valence: [v("d", "quark"), v("u", "antiquark")] },
        { id: "K_plus", label: "K⁺ (u s̄)", pdgName: "K+", valence: [v("u", "quark"), v("s", "antiquark")] },
        { id: "K_minus", label: "K⁻ (s ū)", pdgName: "K-", valence: [v("s", "quark"), v("u", "antiquark")] },
        { id: "K0", label: "K⁰ (d s̄)", pdgName: "K0", valence: [v("d", "quark"), v("s", "antiquark")] },
        { id: "eta", label: "η (uū+dđ mix)", pdgName: "eta", valence: [v("u", "quark"), v("u", "antiquark")], note: "isosinglet proxy" },
      ],
    },
    {
      id: "meson_light_vector",
      label: "Meson — light vector (q q̄)",
      structure: "meson",
      valenceCount: 2,
      closureClass: "colorComposed · excited meson",
      description: "ρ, ω, φ — same valence as pseudoscalar; spin noted in trace.",
      configs: [
        { id: "rho_plus", label: "ρ⁺ (u d̄)", pdgName: "rho+", valence: [v("u", "quark"), v("d", "antiquark")], note: "vector" },
        { id: "rho_zero", label: "ρ⁰ (ūd mix)", pdgName: "rho0", valence: [v("u", "quark"), v("d", "antiquark")], note: "vector" },
        { id: "omega", label: "ω (ūd mix)", pdgName: "omega", valence: [v("u", "quark"), v("d", "antiquark")], note: "vector" },
        { id: "phi", label: "φ (s s̄)", pdgName: "phi", valence: [v("s", "quark"), v("s", "antiquark")], note: "vector" },
      ],
    },
    {
      id: "meson_charm",
      label: "Meson — open charm (q q̄)",
      structure: "meson",
      valenceCount: 2,
      closureClass: "colorComposed",
      description: "D, D_s, D* sector.",
      configs: [
        { id: "D_plus", label: "D⁺ (c d̄)", pdgName: "D+", valence: [v("c", "quark"), v("d", "antiquark")] },
        { id: "D0", label: "D⁰ (c ū)", pdgName: "D0", valence: [v("c", "quark"), v("u", "antiquark")] },
        { id: "Ds_plus", label: "D⁺_s (c s̄)", pdgName: "Ds+", valence: [v("c", "quark"), v("s", "antiquark")] },
        { id: "Jpsi", label: "J/ψ (c c̄)", pdgName: "J/psi", valence: [v("c", "quark"), v("c", "antiquark")] },
      ],
    },
    {
      id: "meson_bottom",
      label: "Meson — bottom (q q̄)",
      structure: "meson",
      valenceCount: 2,
      closureClass: "colorComposed",
      description: "B mesons and Υ.",
      configs: [
        { id: "B_plus", label: "B⁺ (u b̄)", pdgName: "B+", valence: [v("u", "quark"), v("b", "antiquark")] },
        { id: "B0", label: "B⁰ (d b̄)", pdgName: "B0", valence: [v("d", "quark"), v("b", "antiquark")] },
        { id: "Bs", label: "B⁰_s (s b̄)", pdgName: "Bs0", valence: [v("s", "quark"), v("b", "antiquark")] },
        { id: "Upsilon", label: "ϒ (b b̄)", pdgName: "Upsilon", valence: [v("b", "quark"), v("b", "antiquark")] },
      ],
    },
    {
      id: "tetraquark",
      label: "Tetraquark — 2q + 2q̄",
      structure: "tetraquark",
      valenceCount: 4,
      closureClass: "colorComposed · 4-body network",
      description: "Molecular, hidden-charm, and T_cc layouts (valid 2q+2q̄ valence).",
      configs: [
        { id: "X3872", label: "X(3872) (c c̄ q q̄)", pdgName: "X(3872)", valence: [v("c", "quark"), v("c", "antiquark"), v("u", "quark"), v("d", "antiquark")] },
        { id: "Zc3900", label: "Z_c(3900) (c c̄ u ū)", pdgName: "Zc(3900)", valence: [v("c", "quark"), v("c", "antiquark"), v("u", "quark"), v("u", "antiquark")] },
        { id: "Tcc", label: "T_cc (c c ū d̄)", pdgName: "Tcc", valence: [v("c", "quark"), v("c", "quark"), v("u", "antiquark"), v("d", "antiquark")] },
        { id: "dsds", label: "(ds)(d̄s̄)", pdgName: "tetraquark-light", valence: [v("d", "quark"), v("s", "quark"), v("d", "antiquark"), v("s", "antiquark")] },
        { id: "ccqq", label: "(cc)(q̄q̄)", pdgName: "hidden-charm", valence: [v("c", "quark"), v("c", "quark"), v("u", "antiquark"), v("d", "antiquark")] },
        { id: "bbqq", label: "(bb)(q̄q̄)", pdgName: "hidden-bottom", valence: [v("b", "quark"), v("b", "quark"), v("u", "antiquark"), v("d", "antiquark")] },
        { id: "bcqq", label: "(bc)(q̄q̄)", pdgName: "hidden-mixed", valence: [v("b", "quark"), v("c", "quark"), v("u", "antiquark"), v("s", "antiquark")] },
      ],
    },
    {
      id: "pentaquark_charm",
      label: "Pentaquark — charm (4q + q̄)",
      structure: "pentaquark",
      valenceCount: 5,
      closureClass: "colorComposed · 5-body scaffold",
      description: "Observed P_c states: uudsc-type valence.",
      configs: [
        { id: "Pc4312", label: "P_c(4312)⁺ (u u d s c)", pdgName: "Pc(4312)+", valence: [v("u", "quark"), v("u", "quark"), v("d", "quark"), v("s", "quark"), v("c", "quark")] },
        { id: "Pc4440", label: "P_c(4440)⁺ (u u d s c)*", pdgName: "Pc(4440)+", valence: [v("u", "quark"), v("u", "quark"), v("d", "quark"), v("c", "quark"), v("s", "quark")] },
        { id: "Pc4457", label: "P_c(4457)⁺ (u u d c c)", pdgName: "Pc(4457)+", valence: [v("u", "quark"), v("u", "quark"), v("d", "quark"), v("c", "quark"), v("c", "quark")] },
        { id: "uuddc", label: "uuddc (u u d d c)", pdgName: "pentaquark-uuddc", valence: [v("u", "quark"), v("u", "quark"), v("d", "quark"), v("d", "quark"), v("c", "quark")] },
      ],
    },
    {
      id: "pentaquark_light",
      label: "Pentaquark — light (4q + q̄)",
      structure: "pentaquark",
      valenceCount: 5,
      closureClass: "colorComposed · 5-body scaffold",
      description: "Strange pentaquarks and uudud-style molecular candidates.",
      configs: [
        { id: "P_s", label: "P_s (u u d d s)", pdgName: "pentaquark-strange", valence: [v("u", "quark"), v("u", "quark"), v("d", "quark"), v("d", "quark"), v("s", "quark")] },
        { id: "uudus", label: "uudus (u u d ū s)", pdgName: "molecular-5q", valence: [v("u", "quark"), v("u", "quark"), v("d", "quark"), v("u", "antiquark"), v("s", "quark")] },
        { id: "ududs", label: "ududs (u d ū d s)", pdgName: "molecular-alt", valence: [v("u", "quark"), v("d", "quark"), v("u", "antiquark"), v("d", "quark"), v("s", "quark")] },
      ],
    },
  ];

  function validateValence(structure, valence) {
    const n = valence.length;
    const nQ = valence.filter((x) => x.role === "quark").length;
    const nQbar = valence.filter((x) => x.role === "antiquark").length;
    if (structure === "baryon") {
      return n === 3 && nQbar === 0 && nQ === 3;
    }
    if (structure === "meson") {
      return n === 2 && nQ === 1 && nQbar === 1;
    }
    if (structure === "tetraquark") {
      return n === 4 && nQ === 2 && nQbar === 2;
    }
    if (structure === "pentaquark") {
      return n === 5 && (nQ === 4 && nQbar === 1) || (nQ === 5 && nQbar === 0);
    }
    return false;
  }

  function valenceString(valence) {
    return valence
      .map((s) => (s.role === "antiquark" ? s.flavor + "̄" : s.flavor))
      .join(" ");
  }

  function getVariety(id) {
    return HADRON_VARIETIES.find((h) => h.id === id) || null;
  }

  function getConfig(varietyId, configId) {
    const variety = getVariety(varietyId);
    if (!variety) return null;
    return variety.configs.find((c) => c.id === configId) || null;
  }

  root.HQIVHadronCatalog = {
    FLAVORS,
    HADRON_VARIETIES,
    getVariety,
    getConfig,
    validateValence,
    valenceString,
  };
})(typeof globalThis !== "undefined" ? globalThis : window);
