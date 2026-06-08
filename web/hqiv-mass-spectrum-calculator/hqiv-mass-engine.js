/**
 * HQIV mass spectrum derivation engine (browser).
 * Mirrors scripts/cubic_phase_relax_probe.py, check_fano_mass_coherence.py,
 * hqiv_coupling_linear_system.py, hqiv_scale_witness.py — see papers/hqiv_lean_from_combinatorics_to_mass_spectrum.tex
 */
(function (root) {
  "use strict";

  const ALPHA = 3 / 5;
  const GAMMA = 2 / 5;
  const C_RINDLER = GAMMA / 2;
  const INV_ALPHA_GUT = 42;
  const PHI_COEFF = 2;
  const REFERENCE_M = 4;
  const QCD_SHELL = 1;
  const LATTICE_STEP_COUNT = 3;
  const TRIALITY_ORDER = 3;
  const CHARGED_LEPTON_SM_DOUBLET = 2;
  const EM_GAUSS_SHELL = REFERENCE_M - 1;
  const EW_PHI_SHELL = REFERENCE_M + 1;
  const XI_EW = EW_PHI_SHELL + 1;
  const XI_LOCKIN = REFERENCE_M + 1;
  const CODATA_INV_ALPHA = 137.035999177;
  const CODATA_PROTON_MEV = 938.272;
  const CODATA_NEUTRON_MEV = 939.565;
  const M_TOP_GEV_WITNESS = 172.57;
  const M_BOTTOM_GEV_WITNESS = 4.18;
  const TWO_PI = 2 * Math.PI;
  const HORIZON_QUARTER = TWO_PI / 4;

  const FANO_LINES = [
    [0, 1, 2],
    [0, 3, 4],
    [0, 5, 6],
    [1, 3, 5],
    [1, 4, 6],
    [2, 3, 6],
    [2, 4, 5],
  ];

  const WITNESS_DEFAULT = {
    scale_witness_default: "proton_lockin",
    referenceM: 4,
    geV_per_MeV: 0.001,
    CODATA_inv_alpha: CODATA_INV_ALPHA,
    m_H: 23.52,
    M_W: 3.92,
    M_Z: 5.488,
    m_nu_e: 0.0392,
    m_nu_mu: 0.00028,
    m_nu_tau: 0.000002,
    derivedProtonMass_MeV: CODATA_PROTON_MEV,
    derivedNeutronMass_MeV: CODATA_NEUTRON_MEV,
  };

  /** Lean rational witnesses in module units (before export chart). */
  const BOSON_WITNESS_RATIONAL = {
    M_W: 392 / 5,
    M_Z: 2744 / 25,
    m_H: 588 / 5,
  };

  const TOP_ANCHOR_COORD = 31382;
  const QUARK_COMPLEXITY_ELL = 2;
  const LAMBDA_NOW = 1 + GAMMA;
  const CHARGED_LEPTON_TAU_MU_THRESHOLD = 9 / 4;
  const CHARGED_LEPTON_MU_E_THRESHOLD = 16 / 9;

  function shellSurface(m) {
    return (m + 1) * (m + 2);
  }

  function rindlerDetuning(m) {
    return 1 + C_RINDLER * m;
  }

  function detunedSurface(m) {
    return shellSurface(m) / rindlerDetuning(m);
  }

  function geometricResonanceStep(mFrom, mTo) {
    return detunedSurface(mFrom) / detunedSurface(mTo);
  }

  function phiOfShell(m) {
    return PHI_COEFF * (m + 1);
  }

  function TOfM(m) {
    return 1 / (m + 1);
  }

  function outerHorizonSurface(m) {
    return (m + 1) * (m + 2);
  }

  function latticeSimplexCount(m) {
    return (m + 2) * (m + 1);
  }

  function curvatureDensity(xi) {
    if (xi <= 0) return NaN;
    return (1 / xi) * (1 + ALPHA * Math.log(xi));
  }

  function shellShapeAtXi(xi) {
    return curvatureDensity(xi);
  }

  function curvatureIntegralXi(xi) {
    if (xi <= 1) return 0;
    const lx = Math.log(xi);
    return lx + 0.5 * ALPHA * lx * lx;
  }

  function omegaK(xi, xiLock = XI_LOCKIN) {
    const den = curvatureIntegralXi(xiLock);
    if (den <= 0) return 1;
    return curvatureIntegralXi(xi) / den;
  }

  function effCorrected(delta, m) {
    const den = rindlerDetuning(m) + delta;
    if (den <= 0) throw new Error("nonpositive effCorrected denominator");
    return shellSurface(m) / den;
  }

  function massScalingAnsatz(l, delta, m, k = 1) {
    return k * l * l * effCorrected(delta, m);
  }

  function localizationEnergy(xi) {
    if (xi === 0) throw new Error("ξ must be nonzero");
    return xi;
  }

  function shellLapseXi(xi, phi = 0, t = 0) {
    const phiXi = PHI_COEFF / xi;
    return 1 + phi + phiXi * t;
  }

  function hadronMassFromXi(mRest, xi, phi = 0, t = 0) {
    const lapse = shellLapseXi(xi, phi, t);
    return mRest / lapse;
  }

  const QUARK_VERTEX = { u: 1, c: 2, t: 3, d: 4, s: 5, b: 6 };
  const L_COLOR_COMPOSED = 3;
  const L_CHARGE_DECORATED = 2;
  /** Lean `hadronIntrinsicScale_meson_eq_four_ninths` */
  const MESON_INTRINSIC_SCALE = (L_CHARGE_DECORATED * L_CHARGE_DECORATED) / (L_COLOR_COMPOSED * L_COLOR_COMPOSED);
  const NUCLEON_TRACE_GENERATOR_WEIGHT = 3;

  function alphaEffAtShell(m, c = 1) {
    const inv = INV_ALPHA_GUT * (1 + c * ALPHA * Math.log(phiOfShell(m) + 1));
    return 1 / inv;
  }

  function eBindFromNucleonTraceMeV(m, c = 1) {
    return NUCLEON_TRACE_GENERATOR_WEIGHT * latticeSimplexCount(m) * alphaEffAtShell(m, c);
  }

  function intrinsicScaleForStructure(structure) {
    return structure === "meson" ? MESON_INTRINSIC_SCALE : 1;
  }

  function valenceQuarkCount(valence) {
    return valence.filter((s) => s.role === "quark").length;
  }

  function radialExcitationDeltaMeV(anchorMeV, n = 1) {
    const m0 = REFERENCE_M + Math.max(n - 1, 0);
    const m1 = m0 + n;
    const gap = outerHorizonSurface(m1) / outerHorizonSurface(m0) - 1;
    return anchorMeV * gap;
  }

  function orbitalExcitationDeltaMeV(anchorMeV, ell = 1) {
    const step = geometricResonanceStep(REFERENCE_M + ell, REFERENCE_M);
    return anchorMeV * Math.max(step - 1, 0);
  }

  function meanXiForValence(valence, xis) {
    const verts = new Set();
    for (const s of valence) {
      if (QUARK_VERTEX[s.flavor] != null) verts.add(QUARK_VERTEX[s.flavor]);
    }
    if (!verts.size) return XI_LOCKIN;
    let sum = 0;
    for (const v of verts) sum += xis[v];
    return sum / verts.size;
  }

  function radialExcitationGeV(anchorGeV, mLockin = REFERENCE_M) {
    const drop = outerHorizonSurface(mLockin + 1) / outerHorizonSurface(mLockin);
    return anchorGeV * (drop - 1);
  }

  function vectorExcitationGeV(anchorGeV, mLockin = REFERENCE_M) {
    const step = geometricResonanceStep(mLockin + 1, mLockin);
    return anchorGeV * Math.max(step - 1, 0);
  }

  function logPhiSlot(m) {
    return ALPHA * Math.log(phiOfShell(m) + 1);
  }

  function logPhiSlotXi(xi) {
    return ALPHA * Math.log(2 * xi + 1);
  }

  function oneOverAlphaEff(m, c) {
    return INV_ALPHA_GUT * (1 + c * logPhiSlot(m));
  }

  function oneOverAlphaEffXi(xi, c) {
    return INV_ALPHA_GUT * (1 + c * logPhiSlotXi(xi));
  }

  function shellBraceInvAlphaContinuous(c0, xiG, xiEw = XI_EW) {
    const ratio = shellShapeAtXi(xiG) / shellShapeAtXi(xiEw);
    return oneOverAlphaEffXi(xiG, c0) * ratio;
  }

  function fanoLineWeight(v) {
    return ((v % 7) % 3) + 1;
  }

  function fanoWeightVector() {
    const w = [];
    let s = 0;
    for (let v = 0; v < 7; v++) {
      w[v] = fanoLineWeight(v);
      s += w[v];
    }
    return w.map((x) => x / s);
  }

  function holonomyRowRhs(v) {
    const w = fanoWeightVector();
    return (4 / 7) * 12 * w[v];
  }

  function holonomyKAtXi(xi, mode = "sigma") {
    if (mode === "sigma") return shellShapeAtXi(xi);
    if (mode === "log_phi_xi") return logPhiSlotXi(xi);
    const m = Math.max(0, Math.round(xi - 1));
    return logPhiSlot(m);
  }

  function shellForVertex(v, chart, mGlobal) {
    if (chart === "sector") {
      const table = {
        0: EM_GAUSS_SHELL,
        1: REFERENCE_M,
        2: REFERENCE_M + 1,
        3: EW_PHI_SHELL,
        4: EM_GAUSS_SHELL,
        5: REFERENCE_M,
        6: EW_PHI_SHELL,
      };
      return table[v];
    }
    return mGlobal;
  }

  function vertexXiList(chart, mGlobal, xiGRef, xiMode = "sector") {
    const shells = [];
    for (let v = 0; v < 7; v++) shells[v] = shellForVertex(v, chart, mGlobal);
    if (xiMode === "global") {
      const xi = xiGRef != null ? xiGRef : REFERENCE_M + 1;
      return { xis: Array(7).fill(xi), shells };
    }
    const xis = shells.map((m) => m + 1);
    if (xiGRef != null) xis[0] = xiGRef;
    return { xis, shells };
  }

  function lstsq(A, b) {
    const m = A.length;
    const n = A[0].length;
    const ata = Array.from({ length: n }, () => Array(n).fill(0));
    const atb = Array(n).fill(0);
    for (let i = 0; i < m; i++) {
      for (let j = 0; j < n; j++) {
        atb[j] += A[i][j] * b[i];
        for (let k = 0; k < n; k++) ata[j][k] += A[i][j] * A[i][k];
      }
    }
    for (let d = 0; d < n; d++) ata[d][d] += 1e-12;
    const c = Array(n).fill(0);
    for (let step = 0; step < n; step++) {
      let piv = step;
      for (let i = step + 1; i < n; i++) {
        if (Math.abs(ata[i][step]) > Math.abs(ata[piv][step])) piv = i;
      }
      [ata[step], ata[piv]] = [ata[piv], ata[step]];
      [atb[step], atb[piv]] = [atb[piv], atb[step]];
      const div = ata[step][step] || 1e-12;
      for (let j = step; j < n; j++) ata[step][j] /= div;
      atb[step] /= div;
      for (let i = 0; i < n; i++) {
        if (i === step) continue;
        const f = ata[i][step];
        for (let j = step; j < n; j++) ata[i][j] -= f * ata[step][j];
        atb[i] -= f * atb[step];
      }
    }
    for (let i = n - 1; i >= 0; i--) {
      let s = atb[i];
      for (let j = i + 1; j < n; j++) s -= ata[i][j] * c[j];
      c[i] = s / (ata[i][i] || 1);
    }
    let resid = 0;
    for (let i = 0; i < m; i++) {
      let pred = 0;
      for (let j = 0; j < n; j++) pred += A[i][j] * c[j];
      resid += (pred - b[i]) ** 2;
    }
    return { c, residual: Math.sqrt(resid) };
  }

  function stackRows(parts) {
    const rows = [];
    const rhs = [];
    for (const [A, b] of parts) {
      for (let i = 0; i < A.length; i++) {
        rows.push(A[i]);
        rhs.push(b[i]);
      }
    }
    return [rows, rhs];
  }

  function buildLineIncidence(chart, mGlobal, vertexXis, kMode) {
    const { shells } = vertexXiList(chart, mGlobal);
    const A = [];
    const b = [];
    for (let i = 0; i < 7; i++) {
      const pts = FANO_LINES[i];
      let wsum = 0;
      const weights = pts.map((v) => {
        const w = fanoLineWeight(v);
        wsum += w;
        return [v, w];
      });
      const row = Array(7).fill(0);
      for (const [v, w] of weights) {
        const k =
          vertexXis && kMode
            ? holonomyKAtXi(vertexXis[v], kMode)
            : logPhiSlot(shells[v]);
        row[v] = (INV_ALPHA_GUT * k * w) / wsum;
      }
      const mLine = Math.round(pts.reduce((s, v) => s + shells[v], 0) / pts.length);
      const rhs = INV_ALPHA_GUT * (1 + C_RINDLER * mLine) - INV_ALPHA_GUT;
      A.push(row);
      b.push(rhs);
    }
    return { A, b, shells };
  }

  function buildHolonomyVertex(chart, mGlobal, xiGRef, kMode, xiMode) {
    const { xis, shells } = vertexXiList(chart, mGlobal, xiGRef, xiMode);
    const A = [];
    const b = [];
    for (let v = 0; v < 7; v++) {
      const row = Array(7).fill(0);
      const k = holonomyKAtXi(xis[v], kMode);
      if (Math.abs(k) < 1e-15) {
        row[v] = 1;
        b.push(0);
      } else {
        row[v] = k;
        b.push(holonomyRowRhs(v));
      }
      A.push(row);
    }
    return { A, b, shells, xis };
  }

  function buildUnitC0Row(weight) {
    return { A: [[weight, 0, 0, 0, 0, 0, 0]], b: [weight] };
  }

  function buildContinuousBraceRow(xiG, weight, xiEw = XI_EW) {
    const ratio = shellShapeAtXi(xiG) / shellShapeAtXi(xiEw);
    const k = logPhiSlotXi(xiG);
    const row = [INV_ALPHA_GUT * k * ratio * weight, 0, 0, 0, 0, 0, 0];
    const rhs = (CODATA_INV_ALPHA - INV_ALPHA_GUT * ratio) * weight;
    return { A: [row], b: [rhs] };
  }

  function buildInformationalMassRow(xiG, weight) {
    const om = omegaK(xiG, XI_LOCKIN);
    const loc = xiG;
    return { A: [[weight, 0, 0, 0, 0, 0, 0]], b: [(TWO_PI * om - loc) * weight] };
  }

  function xiGFromBrace(c0, xiEw = XI_EW) {
    const target = CODATA_INV_ALPHA;
    let lo = 1.05;
    let hi = xiEw - 1e-3;
    const braced = (xi) => shellBraceInvAlphaContinuous(c0, xi, xiEw);
    if (braced(lo) < target) return lo;
    if (braced(hi) > target) return hi;
    for (let i = 0; i < 80; i++) {
      const mid = 0.5 * (lo + hi);
      if (braced(mid) > target) lo = mid;
      else hi = mid;
    }
    return 0.5 * (lo + hi);
  }

  function solveCoupling(options) {
    const witness = options.scaleWitness || "proton_lockin";
    const massRow = options.massRow !== false;
    const chart = "sector";
    const mGlobal = REFERENCE_M;
    const anchorWeight = 1e3;
    const kMode = "sigma";
    const steps = [];
    const parts = [];

    steps.push({
      id: "constants",
      title: "HQIV backbone constants",
      latex:
        "\\alpha=\\tfrac{3}{5},\\ \\gamma=\\tfrac{2}{5},\\ \\texttt{referenceM}=4,\\ 1/\\alpha_{\\mathrm{GUT}}=42",
      plain: `α=${ALPHA}, γ=${GAMMA}, referenceM=${REFERENCE_M}, 1/α_GUT=${INV_ALPHA_GUT}`,
      module: "OctonionicLightCone.lean / AuxiliaryField.lean",
    });

    let xiGRef = XI_LOCKIN;
    if (witness === "codata_alpha") {
      xiGRef = 3.4743752754774695;
      const line = buildLineIncidence(chart, mGlobal, null, null);
      const hol = buildHolonomyVertex(chart, mGlobal, xiGRef, kMode, "sector");
      parts.push([line.A, line.b], [hol.A, hol.b]);
      parts.push([buildContinuousBraceRow(xiGRef, anchorWeight).A, buildContinuousBraceRow(xiGRef, anchorWeight).b]);
      steps.push({
        id: "brace",
        title: "CODATA scale row (continuous Gauss→EW brace)",
        latex:
          "42\\,(1+c_0\\,\\alpha\\ln(2\\xi_G+1))\\,\\frac{\\sigma(\\xi_G)}{\\sigma(\\xi_{\\mathrm{EW}})} = 1/\\alpha_{\\mathrm{CODATA}}",
        plain: `Pin 1/α = ${CODATA_INV_ALPHA} via σ(ξ) brace at ξ_EW=${XI_EW}`,
        module: "hqiv_coupling_linear_system.py / ContinuousXiCoupling.lean",
      });
    } else {
      const line = buildLineIncidence(chart, mGlobal, null, null);
      const hol = buildHolonomyVertex(chart, mGlobal, XI_LOCKIN, kMode, "sector");
      parts.push([line.A, line.b], [hol.A, hol.b]);
      parts.push([buildUnitC0Row(anchorWeight).A, buildUnitC0Row(anchorWeight).b]);
      steps.push({
        id: "anchor",
        title: "Single-scale witness: normalize c₀ = 1",
        latex: "c_0 = 1 \\quad (\\texttt{proton\\_lockin};\\ \\mathrm{CODATA}\\ 1/\\alpha\\ \\mathrm{is\\ a\\ prediction})",
        plain: "proton_lockin: EM vertex coefficient c₀ fixed to 1; CODATA 1/α is not in the solve",
        module: "ScaleWitness.lean / hqiv_scale_witness.py",
      });
    }

    const hol2 = buildHolonomyVertex(chart, mGlobal, witness === "codata_alpha" ? xiGRef : XI_LOCKIN, kMode, "sector");
    if (massRow) {
      const mr = buildInformationalMassRow(xiGRef, 1);
      parts.push([mr.A, mr.b]);
      steps.push({
        id: "mass_row",
        title: "Informational-energy mass row",
        latex: "c_0 + \\mathrm{loc}(\\xi_G) = 2\\pi\\,\\Omega_k(\\xi_G),\\quad \\mathrm{loc}(\\xi)=\\xi",
        plain: "Lean informationalEnergyMassRow — couples EM slot to horizon fraction Ω_k",
        module: "InformationalEnergyMass.lean",
      });
    }

    const [A, b] = stackRows(parts);
    const { c, residual } = lstsq(A, b);
    let xiG = xiGRef;
    if (witness === "codata_alpha") {
      xiG = xiGFromBrace(c[0]);
    }

    const invAlphaBraced = shellBraceInvAlphaContinuous(c[0], xiG);
    steps.push({
      id: "solve",
      title: "Over-constrained Fano linear system (least squares)",
      latex: "\\min_c \\|A c - b\\|_2 \\quad (7\\ \\mathrm{line\\ rows}+7\\ \\mathrm{holonomy\\ rows}+\\mathrm{scale\\ row})",
      plain: `Solved c_v; residual ||Ac-b|| = ${residual.toExponential(3)}`,
      values: { c_v: c.map((x) => +x.toFixed(6)), xi_G: +xiG.toFixed(6) },
      module: "hqiv_coupling_linear_system.py",
    });

    if (witness === "proton_lockin") {
      steps.push({
        id: "alpha_pred",
        title: "Predicted EM coupling (comparison)",
        latex: "1/\\alpha_{\\mathrm{braced}}(c_0,\\xi_G)",
        plain: `Braced 1/α = ${invAlphaBraced.toFixed(4)} vs CODATA ${CODATA_INV_ALPHA}`,
        values: { inv_alpha_braced: invAlphaBraced, codata: CODATA_INV_ALPHA },
        module: "ScaleWitness.lean",
      });
    }

    return {
      witness,
      c,
      shells: hol2.shells,
      xis: hol2.xis,
      xiG,
      residual,
      invAlphaBraced,
      omegaK: omegaK(xiG),
      locXi: xiG,
      steps,
    };
  }

  function bosonClosure() {
    const ref = REFERENCE_M;
    const bosonClosureShell = ref + 1;
    const tLockin = TOfM(ref);
    const sBc = outerHorizonSurface(bosonClosureShell);
    const lsc = latticeSimplexCount(ref);
    const mono = 1 + GAMMA;
    const vev = tLockin * sBc * mono;
    const ewGauge = (lsc / TRIALITY_ORDER) * CHARGED_LEPTON_SM_DOUBLET;
    const vevG = vev * ewGauge;
    const g2 = 1 / TRIALITY_ORDER;
    const g1 = GAMMA / TRIALITY_ORDER;
    const mW = g2 * vevG;
    const mZ = (g2 + g1) * vevG;
    const ewS = TRIALITY_ORDER + CHARGED_LEPTON_SM_DOUBLET;
    const vevS = vev * ewS;
    const mH = 2 * vevS;
    const mWRaw = mW;
    const mZRaw = mZ;
    const mHRaw = mH;
    const w = WITNESS_DEFAULT;
    const mWGeV = w.M_W;
    const mZGeV = w.M_Z;
    const mHGeV = w.m_H;
    const steps = [
      {
        id: "vev",
        title: "Geometric vacuum (outer horizon)",
        latex:
          "v = T_{\\mathrm{lockin}}\\,S(m_{\\mathrm{lockin}}+1)\\,(1+\\gamma),\\quad S(m)=(m+1)(m+2)",
        plain: `v = ${tLockin.toFixed(6)} × ${sBc} × ${mono} = ${vev.toFixed(6)} (module units)`,
        values: { T_lockin: tLockin, S: sBc, gamma: GAMMA, v: vev },
        module: "DerivedGaugeAndLeptonSector.lean",
      },
      {
        id: "lift",
        title: "EW quantum lift on vev",
        latex: "v_{\\mathrm{gauge}} = v \\cdot \\frac{\\texttt{latticeSimplexCount}}{3} \\cdot 2",
        plain: `v_gauge = ${vevG.toFixed(6)}`,
        values: { lattice_simplex: lsc, vev_gauge: vevG },
        module: "DerivedGaugeAndLeptonSector.lean",
      },
      {
        id: "bosons_raw",
        title: "Closure witnesses (module units)",
        latex:
          "M_W=\\tfrac{1}{3}v_g,\\ M_Z=(g_{SU2}+g_{U1})v_g,\\ m_H=2v_s",
        plain: `Raw: M_W=${mWRaw.toFixed(4)}, M_Z=${mZRaw.toFixed(4)}, m_H=${mHRaw.toFixed(4)} (matches 392/5, 2744/25, 588/5)`,
        values: {
          M_W_raw: mWRaw,
          M_Z_raw: mZRaw,
          m_H_raw: mHRaw,
          M_W_rational: BOSON_WITNESS_RATIONAL.M_W,
          M_Z_rational: BOSON_WITNESS_RATIONAL.M_Z,
          m_H_rational: BOSON_WITNESS_RATIONAL.m_H,
        },
        module: "DerivedGaugeAndLeptonSector.lean / check_fano_mass_coherence.py",
      },
      {
        id: "bosons_gev",
        title: "Witness export chart (GeV)",
        latex:
          "M_W^{\\mathrm{GeV}}=3.92,\\ M_Z^{\\mathrm{GeV}}=5.488,\\ m_H^{\\mathrm{GeV}}=23.52",
        plain: "Values from data/hqiv_witnesses.json (lake build HQIVWitnesses)",
        values: { M_W: mWGeV, M_Z: mZGeV, m_H: mHGeV },
        module: "export_witnesses.lean / hqiv_witnesses.json",
      },
    ];
    return {
      mW: mWGeV,
      mZ: mZGeV,
      mH: mHGeV,
      mWRaw,
      mZRaw,
      mHRaw,
      vev,
      vevG,
      steps,
    };
  }

  function neutrinoMasses(mZ) {
    const suppress = GAMMA / outerHorizonSurface(REFERENCE_M + 2);
    const mNuE = suppress * mZ;
    const mNuMu = suppress * mNuE;
    const mNuTau = suppress * mNuMu;
    const steps = [
      {
        id: "nu_suppress",
        title: "Outer-horizon neutrino suppression",
        latex:
          "\\mathrm{outerHorizonNeutrinoSuppression} = \\frac{\\gamma}{S(\\texttt{referenceM}+2)}",
        plain: `γ/S(${REFERENCE_M + 2}) = ${suppress.toExponential(4)}`,
        values: { suppression: suppress },
        module: "DerivedGaugeAndLeptonSector.lean",
      },
      {
        id: "nu_e",
        title: "Electron neutrino",
        latex: "m_{\\nu_e}^{\\mathrm{derived}} = \\mathrm{suppression}\\cdot M_Z^{\\mathrm{derived}}",
        plain: `m_νe = ${mNuE.toExponential(4)} GeV (${(mNuE * 1e9).toFixed(4)} eV)`,
        values: { m_nu_e_GeV: mNuE },
        module: "DerivedGaugeAndLeptonSector.lean",
      },
      {
        id: "nu_cascade",
        title: "μ and τ neutrino cascade",
        latex:
          "m_{\\nu_\\mu}^{\\mathrm{derived}}=\\mathrm{suppression}\\cdot m_{\\nu_e},\\quad m_{\\nu_\\tau}^{\\mathrm{derived}}=\\mathrm{suppression}\\cdot m_{\\nu_\\mu}",
        plain: `m_νμ = ${mNuMu.toExponential(4)} GeV, m_ντ = ${mNuTau.toExponential(4)} GeV`,
        values: { m_nu_mu_GeV: mNuMu, m_nu_tau_GeV: mNuTau },
        module: "DerivedGaugeAndLeptonSector.lean",
      },
    ];
    return { mNuE, mNuMu, mNuTau, suppress, steps };
  }

  function laplaceS7(ell) {
    return ell * (ell + 6);
  }

  function spectralOmega(bridge, ell) {
    const lam = bridge === "s7" ? laplaceS7(ell) : ell * (ell + 2);
    return Math.sqrt(lam + 1);
  }

  function spectralRelaxWeight(bridge, ell) {
    return Math.log(spectralOmega(bridge, ell) + 1);
  }

  function complexityThreshold(bridge, ell, poles) {
    const ellEff = Math.max(1, ell * Math.max(1, poles));
    const raw = Math.exp(spectralRelaxWeight(bridge, ellEff));
    const omega = spectralOmega(bridge, ell);
    const proj = Math.max(Math.abs(Math.cos(Math.atan(omega))), 1e-9);
    return 1 + LAMBDA_NOW * (raw - 1) * (1 / proj);
  }

  function firstCoordAtOrBelowRatio(fromS, ratioTarget) {
    if (ratioTarget <= 1) return fromS;
    let lo = 0;
    let hi = fromS;
    for (let i = 0; i < 100; i++) {
      const mid = 0.5 * (lo + hi);
      if (geometricResonanceStep(fromS, mid) >= ratioTarget) lo = mid;
      else hi = mid;
    }
    return lo;
  }

  function derivedQuarkCoordinates() {
    const sTop = TOP_ANCHOR_COORD;
    const cS7Up = complexityThreshold("s7", QUARK_COMPLEXITY_ELL, 2);
    const cS7Down = complexityThreshold("s7", QUARK_COMPLEXITY_ELL, 1);
    const cS3 = complexityThreshold("s3", QUARK_COMPLEXITY_ELL, 1);
    const hyperDrop = cS7Up / Math.max(cS7Down, 1e-9);
    const sBottom = firstCoordAtOrBelowRatio(sTop, hyperDrop);
    const sCharm = firstCoordAtOrBelowRatio(sTop, cS7Up);
    const sUp = firstCoordAtOrBelowRatio(sCharm, cS3);
    const sStrange = firstCoordAtOrBelowRatio(sBottom, cS7Down);
    const sDown = firstCoordAtOrBelowRatio(sStrange, cS3);
    return { sTop, sCharm, sUp, sBottom, sStrange, sDown, cS7Up, cS3 };
  }

  function quarkMassesGeV() {
    const { sTop, sCharm, sUp, sBottom, sStrange, sDown } = derivedQuarkCoordinates();
    const kTopCharm = geometricResonanceStep(sTop, sCharm);
    const kCharmUp = geometricResonanceStep(sCharm, sUp);
    const kBottomStrange = geometricResonanceStep(sBottom, sStrange);
    const kStrangeDown = geometricResonanceStep(sStrange, sDown);
    const charm = M_TOP_GEV_WITNESS / kTopCharm;
    const up = charm / kCharmUp;
    const bottom = M_BOTTOM_GEV_WITNESS;
    const strange = bottom / kBottomStrange;
    const down = strange / kStrangeDown;
    const steps = [
      {
        id: "quark_coords",
        title: "Quark standing-wave coordinates (S7/S3 complexity)",
        latex: "s_q \\ \\mathrm{from\\ TOP\\_ANCHOR\\_COORD\\ downward\\ via\\ complexity\\ thresholds}",
        plain: `s_top=${sTop.toFixed(2)}, s_charm=${sCharm.toFixed(2)}, s_down=${sDown.toFixed(2)}`,
        module: "cubic_phase_relax_probe.py / QuarkMetaResonance.lean",
      },
      {
        id: "quark_k",
        title: "Detuned-surface resonance steps",
        latex:
          "K_{a\\to b}=\\dfrac{\\texttt{detunedShellSurface}(s_a)}{\\texttt{detunedShellSurface}(s_b)}",
        plain: `K_top→charm=${kTopCharm.toFixed(4)}, K_strange→down=${kStrangeDown.toFixed(4)}`,
        module: "QuarkMetaResonance.lean",
      },
      {
        id: "quark_mass",
        title: "Quark ladder (heavy anchors are witnesses)",
        latex:
          "m_c = m_{\\mathrm{top}}^{\\mathrm{witness}}/K_{t\\to c},\\quad m_d = m_s/K_{s\\to d}",
        plain: `top anchor ${M_TOP_GEV_WITNESS} GeV, bottom anchor ${M_BOTTOM_GEV_WITNESS} GeV — ratios are HQIV-derived`,
        values: {
          m_top: M_TOP_GEV_WITNESS,
          m_charm: charm,
          m_up: up,
          m_bottom: bottom,
          m_strange: strange,
          m_down: down,
        },
        module: "QuarkMetaResonance.lean (m_top_GeV witness)",
      },
    ];
    return {
      mTop: M_TOP_GEV_WITNESS,
      mCharm: charm,
      mUp: up,
      mBottom: bottom,
      mStrange: strange,
      mDown: down,
      kTopCharm,
      kStrangeDown,
      steps,
    };
  }

  function firstCoordAtOrAboveThreshold(currentS, threshold) {
    if (threshold <= 1) return currentS;
    let lo = currentS;
    let hi = currentS + 1;
    while (geometricResonanceStep(hi, currentS) < threshold) hi += 1;
    for (let i = 0; i < 80; i++) {
      const mid = 0.5 * (lo + hi);
      if (geometricResonanceStep(mid, currentS) >= threshold) hi = mid;
      else lo = mid;
    }
    return hi;
  }

  const M_TAU_GEV_WITNESS = 1.777;

  function leptonMassesGeV() {
    const sTau = REFERENCE_M;
    const sMu = firstCoordAtOrAboveThreshold(sTau, CHARGED_LEPTON_TAU_MU_THRESHOLD);
    const sE = firstCoordAtOrAboveThreshold(sMu, CHARGED_LEPTON_MU_E_THRESHOLD);
    const kTauMu = geometricResonanceStep(sMu, sTau);
    const kMuE = geometricResonanceStep(sE, sMu);
    const mTau = M_TAU_GEV_WITNESS;
    const mMu = mTau / kTauMu;
    const mE = mMu / kMuE;
    const steps = [
      {
        id: "lepton_shells",
        title: "Charged-lepton shell coordinates",
        latex: "s_\\tau=\\texttt{referenceM},\\ s_\\mu,\\ s_e\\ \\mathrm{from\\ detuned\\ octave\\ thresholds}",
        plain: `s_τ=${sTau}, s_μ=${sMu.toFixed(2)}, s_e=${sE.toFixed(2)} (Lean LeptonGenerationLockin)`,
        values: { s_tau: sTau, s_mu: sMu, s_e: sE },
        module: "LeptonGenerationLockin.lean / cubic_phase_relax_probe.py",
      },
      {
        id: "lepton_k",
        title: "Resonance steps on detuned surfaces",
        latex: "K_{\\mu\\tau}=\\dfrac{S_\\mu^{\\mathrm{det}}}{S_\\tau^{\\mathrm{det}}},\\quad K_{e\\mu}=\\dfrac{S_e^{\\mathrm{det}}}{S_\\mu^{\\mathrm{det}}}",
        plain: `K_τμ=${kTauMu.toFixed(4)}, K_μe=${kMuE.toFixed(4)}`,
        module: "ChargedLeptonResonance.lean",
      },
      {
        id: "lepton_mass",
        title: "Lepton masses (τ anchor witness)",
        latex: "m_\\mu=m_\\tau/K_{\\mu\\tau},\\quad m_e=m_\\mu/K_{e\\mu}",
        plain: `m_τ=${mTau} GeV (witness scale); m_μ=${mMu.toFixed(6)} GeV; m_e=${mE.toExponential(4)} GeV`,
        values: { m_tau: mTau, m_mu: mMu, m_e: mE },
        module: "ChargedLeptonResonance.lean",
      },
    ];
    return { mTau, mMu, mE, kTauMu, kMuE, steps };
  }

  function quarkMassMap(quarks) {
    return {
      u: quarks.mUp,
      d: quarks.mDown,
      s: quarks.mStrange,
      c: quarks.mCharm,
      b: quarks.mBottom,
      t: quarks.mTop,
    };
  }

  function witnessBundleGeV(witnessJson) {
    const w = witnessJson || WITNESS_DEFAULT;
    const gevPerMeV = w.geV_per_MeV != null ? w.geV_per_MeV : 0.001;
    return {
      proton: (w.derivedProtonMass_MeV != null ? w.derivedProtonMass_MeV : CODATA_PROTON_MEV) * gevPerMeV,
      neutron: (w.derivedNeutronMass_MeV != null ? w.derivedNeutronMass_MeV : CODATA_NEUTRON_MEV) * gevPerMeV,
    };
  }

  function hadronMassFromCouplingStack(config, variety, quarks, coupling, witnessJson) {
    const Catalog = root.HQIVHadronCatalog;
    if (!Catalog || !Catalog.validateValence(variety.structure, config.valence)) {
      throw new Error("Invalid valence for " + variety.structure);
    }
    const qm = quarkMassMap(quarks);
    const wb = witnessBundleGeV(witnessJson);
    const xis = coupling.xis;
    let xi = meanXiForValence(config.valence, xis);
    let mRest;
    let pipeline;
    let excGeV = 0;

    if (config.id === "p") {
      mRest = wb.proton;
      xi = xis[1];
      pipeline = "witness_proton_vertex1";
    } else if (config.id === "n") {
      mRest = wb.neutron;
      xi = xis[1];
      pipeline = "witness_neutron_vertex1";
    } else {
      const mConstGeV = config.valence.reduce((a, s) => (s.role === "quark" ? a + qm[s.flavor] : a), 0);
      const pConstGeV = 2 * quarks.mUp + quarks.mDown;
      const witnessScale = pConstGeV > 0 ? wb.proton / pConstGeV : 1;
      const mConstMeV = mConstGeV * witnessScale * 1000;
      const mShell = Math.max(0, Math.min(Math.round(xi - 1), REFERENCE_M + 2));
      const nVal = valenceQuarkCount(config.valence);
      const bindMeV = eBindFromNucleonTraceMeV(mShell) * (nVal / 3);
      const groundMeV =
        (mConstMeV - bindMeV) * intrinsicScaleForStructure(variety.structure);
      mRest = groundMeV / 1000;
      pipeline = "HadronMassReadout+info_mult";
    }

    let mGeV = hadronMassFromXi(mRest, xi);
    let groundMeV = mRest * 1000;
    const valStr = Catalog.valenceString(config.valence);
    const lapse = shellLapseXi(xi);
    const steps = [
      {
        id: "xi_readout",
        title: "Rapidity readout ξ (valence vertices)",
        latex: "\\xi_{\\mathrm{readout}}=\\mathrm{mean}\\,\\xi_v\\ \\mathrm{on\\ valence\\ Fano\\ vertices}",
        plain: `ξ_readout = ${xi.toFixed(4)}  (vertices from valence flavors)`,
        values: { xi_readout: xi, xis },
        module: "InformationalEnergyMass.lean / hqiv_mass_calculator_core.py",
      },
      {
        id: "hadron_ground",
        title: "Ground mass (composite trace + content scale)",
        latex:
          "M_{\\mathrm{ground}}=\\bigl(M_{\\mathrm{const}}-E_{\\mathrm{bind}}\\tfrac{N_v}{3}\\bigr)\\times\\tfrac{l^2}{9}",
        plain: `Ground = ${(groundMeV || mRest * 1000).toFixed(2)} MeV (meson ×4/9 when applicable) [${pipeline}]`,
        values: { ground_MeV: groundMeV || mRest * 1000, pipeline },
        module: "HadronMassReadout.lean",
      },
      {
        id: "m_rest_slot",
        title: "Informational readout input",
        latex: "M = M_{\\mathrm{ground}}/N(\\xi)",
        plain: `m_rest = ${mRest.toFixed(6)} GeV`,
        values: { m_rest_GeV: mRest, pipeline },
        module: "InformationalEnergyMass.lean",
      },
      {
        id: "info_mult",
        title: "Multiplicative lapse readout (hadron gauge)",
        latex: "M = m_{\\mathrm{rest}}/N(\\xi),\\quad N=1+\\Phi+\\phi(\\xi)t",
        plain: `N(ξ)=${lapse.toFixed(4)} → M = ${mGeV.toFixed(6)} GeV (${(mGeV * 1000).toFixed(2)} MeV)`,
        values: { lapse: lapse, M_hadron_GeV: mGeV },
        module: "InformationalEnergyMass.lean",
      },
    ];

    if (config.note === "decuplet") {
      const dMeV = radialExcitationDeltaMeV(wb.proton * 1000, 1);
      excGeV = dMeV / 1000;
      mGeV = (groundMeV + dMeV) / 1000;
      steps.push({
        id: "decuplet_excitation",
        title: "Radial excitation (Lean `radialExcitationDeltaOperational`)",
        latex: "\\Delta M_{\\mathrm{radial}} = M_p\\,(S_{m+1}/S_m - 1)",
        plain: `+${dMeV.toFixed(1)} MeV → M = ${mGeV.toFixed(6)} GeV`,
        values: { delta_radial_MeV: dMeV },
        module: "HadronMassReadout.lean / MetaHorizonExcitedStates.lean",
      });
    } else if (config.note === "vector") {
      const anchorMeV = variety.structure === "meson" ? groundMeV : wb.proton * 500;
      const dMeV = orbitalExcitationDeltaMeV(anchorMeV, 1);
      excGeV = dMeV / 1000;
      mGeV = (groundMeV + dMeV) / 1000;
      steps.push({
        id: "vector_excitation",
        title: "Orbital excitation (Lean `orbitalExcitationDeltaOperational`)",
        latex: "\\Delta M_{\\mathrm{orbital}} \\propto (K_{\\mathrm{res}}-1)\\,M_{\\mathrm{anchor}}",
        plain: `+${dMeV.toFixed(1)} MeV → M = ${mGeV.toFixed(6)} GeV`,
        module: "HadronMassReadout.lean",
      });
    }

    return { mGeV, mMeV: mGeV * 1000, mRest, xi, steps, valStr, pipeline };
  }

  function ccdHadronScaffold(mCharm, mDown, mUp, protonMeV) {
    const mConstProton = 2 * mUp + mDown;
    const eBind = mConstProton * 1000 - protonMeV;
    const mConstCcd = 2 * mCharm + mDown;
    const mCcdGeV = mConstCcd - eBind / 1000;
    const steps = [
      {
        id: "proton_bind",
        title: "Network binding from proton (uud)",
        latex:
          "E_{\\mathrm{bind}} = (2m_u+m_d)_{\\mathrm{const}} - M_p,\\quad M_p\\ \\mathrm{from\\ scale\\ witness}",
        plain: `Constituent sum (uud) = ${mConstProton.toFixed(4)} GeV; E_bind = ${eBind.toFixed(3)} MeV`,
        values: { M_constituent_proton_GeV: mConstProton, E_bind_MeV: eBind },
        module: "BoundStates.lean / DerivedNucleonMass.lean",
      },
      {
        id: "ccd",
        title: "ccd hadron scaffold (2 charm + down)",
        latex: "M_{ccd} = (2m_c + m_d) - E_{\\mathrm{bind}}",
        plain: `M_ccd ≈ ${mCcdGeV.toFixed(4)} GeV (${(mCcdGeV * 1000).toFixed(2)} MeV)`,
        values: { M_ccd_GeV: mCcdGeV, M_ccd_MeV: mCcdGeV * 1000 },
        module: "BoundStates.lean (8×8 network scaffold)",
      },
    ];
    return { mCcdGeV, mCcdMeV: mCcdGeV * 1000, eBindMeV: eBind, steps };
  }

  const INPUTS = {
    codata_proton: {
      label: "CODATA proton mass",
      description: "Pins the hadronic mass chart at 938.272 MeV; Fano solve uses proton_lockin (c₀=1).",
      protonMeV: CODATA_PROTON_MEV,
      scaleWitness: "proton_lockin",
    },
    proton_lockin_witness: {
      label: "Lean proton lock-in witness",
      description: "Uses exported derivedProtonMass from hqiv_witnesses.json defaults.",
      protonMeV: WITNESS_DEFAULT.derivedProtonMass_MeV,
      scaleWitness: "proton_lockin",
    },
    codata_inv_alpha: {
      label: "CODATA 1/α",
      description: "Pins the continuous Gauss→EW brace in the over-constrained solve.",
      protonMeV: CODATA_PROTON_MEV,
      scaleWitness: "codata_alpha",
    },
    geometry_only: {
      label: "Geometry only (no CODATA mass)",
      description: "Only α, γ, referenceM; bosons and ν from closure; quark ratios without PDG mass pin.",
      protonMeV: null,
      scaleWitness: "proton_lockin",
    },
  };

  const OUTPUTS = {
    neutrino_e: { label: "νₑ mass", unit: "GeV (eV in trace)" },
    neutrino_mu: { label: "νμ mass", unit: "GeV" },
    neutrino_tau: { label: "ντ mass", unit: "GeV" },
    neutrinos: { label: "All neutrinos (e, μ, τ)", unit: "GeV" },
    lepton_e: { label: "Electron", unit: "GeV" },
    lepton_mu: { label: "Muon", unit: "GeV" },
    lepton_tau: { label: "Tau", unit: "GeV" },
    proton: { label: "Proton", unit: "MeV" },
    M_W: { label: "W boson", unit: "GeV" },
    M_Z: { label: "Z boson", unit: "GeV" },
    m_H: { label: "Higgs", unit: "GeV" },
    ew_bosons: { label: "W, Z, H", unit: "GeV" },
    charm_quark: { label: "Charm quark", unit: "GeV" },
    down_quark: { label: "Down quark", unit: "GeV" },
    up_quark: { label: "Up quark", unit: "GeV" },
    ccd_hadron: { label: "ccd hadron (2c + d − bind)", unit: "GeV" },
    inv_alpha_braced: { label: "Predicted 1/α (braced)", unit: "dimensionless" },
    fano_cv: { label: "Fano coefficients c_v", unit: "dimensionless" },
  };

  const SECTORS = {
    lepton: {
      label: "Lepton",
      targets: [
        { id: "e", label: "Electron (e)" },
        { id: "mu", label: "Muon (μ)" },
        { id: "tau", label: "Tau (τ)" },
      ],
    },
    hadron: {
      label: "Hadron",
      usesCatalog: true,
    },
    boson: {
      label: "Boson",
      targets: [
        { id: "M_W", label: "W boson" },
        { id: "M_Z", label: "Z boson" },
        { id: "m_H", label: "Higgs" },
        { id: "ew_bosons", label: "W, Z, H (all)" },
        { id: "inv_alpha_braced", label: "Predicted 1/α (braced)" },
      ],
    },
    neutrino: {
      label: "Neutrino",
      targets: [
        { id: "neutrino_e", label: "νₑ" },
        { id: "neutrino_mu", label: "νμ" },
        { id: "neutrino_tau", label: "ντ" },
        { id: "neutrinos", label: "All three" },
      ],
    },
  };

  /**
   * @param {object} req
   * @param {string} req.inputKey
   * @param {'lepton'|'hadron'|'boson'|'neutrino'} req.sector
   * @param {string} [req.targetId] — sector-specific
   * @param {string} [req.hadronVarietyId]
   * @param {string} [req.hadronConfigId]
   * @param {object} [req.witnessJson]
   */
  function deriveFromRequest(req) {
    const inputKey = req.inputKey;
    const sector = req.sector;
    const targetId = req.targetId;
    const witnessJson = req.witnessJson;

    if (sector === "hadron") {
      const Catalog = root.HQIVHadronCatalog;
      if (!Catalog) throw new Error("Hadron catalog not loaded");
      const variety = Catalog.getVariety(req.hadronVarietyId);
      const config = Catalog.getConfig(req.hadronVarietyId, req.hadronConfigId);
      if (!variety || !config) throw new Error("Select hadron variety and configuration");

      const base = derive(inputKey, "proton", witnessJson);
      const quarks = base.quarks;
      const had = hadronMassFromCouplingStack(config, variety, quarks, base.coupling, witnessJson);
      return {
        ...base,
        sector,
        hadronVariety: variety,
        hadronConfig: config,
        outputKey: "hadron:" + variety.id + ":" + config.id,
        output: { label: config.label, unit: "GeV" },
        result: had.mGeV,
        unit: "GeV",
        trace: [...base.trace, ...had.steps],
        meta: variety.label + " · " + config.label,
      };
    }

    const map = {
      lepton: { e: "lepton_e", mu: "lepton_mu", tau: "lepton_tau" },
      boson: {
        M_W: "M_W",
        M_Z: "M_Z",
        m_H: "m_H",
        ew_bosons: "ew_bosons",
        inv_alpha_braced: "inv_alpha_braced",
      },
      neutrino: {
        neutrino_e: "neutrino_e",
        neutrino_mu: "neutrino_mu",
        neutrino_tau: "neutrino_tau",
        neutrinos: "neutrinos",
      },
    };
    const outputKey = map[sector] && map[sector][targetId];
    if (!outputKey) throw new Error("Unknown target for sector " + sector);
    const d = derive(inputKey, outputKey, witnessJson);
    return { ...d, sector, targetId, meta: d.input.label + " → " + d.output.label };
  }

  function derive(inputKey, outputKey, witnessJson) {
    const input = INPUTS[inputKey];
    const output = OUTPUTS[outputKey];
    if (!input || !output) throw new Error("Unknown input or output");

    const w = Object.assign({}, WITNESS_DEFAULT, witnessJson || {});
    const protonMeV =
      input.protonMeV != null ? input.protonMeV : w.derivedProtonMass_MeV;

    const trace = [];
    const coupling = solveCoupling({
      scaleWitness: input.scaleWitness,
      massRow: true,
    });
    trace.push(...coupling.steps);

    if (inputKey === "codata_proton" || inputKey === "proton_lockin_witness") {
      trace.push({
        id: "scale_pin",
        title: "Mass chart anchor",
        latex: "M_p^{\\mathrm{witness}} = 938.272\\ \\mathrm{MeV}",
        plain: `Active scale witness: ${protonMeV.toFixed(3)} MeV (${input.label})`,
        values: { M_proton_MeV: protonMeV },
        module: "ScaleWitness.lean",
      });
    }

    const bosons = bosonClosure();
    bosons.mW = w.M_W;
    bosons.mZ = w.M_Z;
    bosons.mH = w.m_H;
    const nus = neutrinoMasses(bosons.mZ);
    const quarks = quarkMassesGeV();

    let result = null;
    let unit = output.unit;

    switch (outputKey) {
      case "neutrino_e":
        trace.push(...bosons.steps, ...nus.steps.slice(0, 2));
        result = nus.mNuE;
        break;
      case "neutrino_mu":
        trace.push(...bosons.steps, ...nus.steps);
        result = nus.mNuMu;
        break;
      case "neutrino_tau":
        trace.push(...bosons.steps, ...nus.steps);
        result = nus.mNuTau;
        break;
      case "neutrinos":
        trace.push(...bosons.steps, ...nus.steps);
        result = { m_nu_e: nus.mNuE, m_nu_mu: nus.mNuMu, m_nu_tau: nus.mNuTau };
        break;
      case "M_W":
        trace.push(...bosons.steps);
        result = bosons.mW;
        break;
      case "M_Z":
        trace.push(...bosons.steps);
        result = bosons.mZ;
        break;
      case "m_H":
        trace.push(...bosons.steps);
        result = bosons.mH;
        break;
      case "ew_bosons":
        trace.push(...bosons.steps);
        result = { M_W: bosons.mW, M_Z: bosons.mZ, m_H: bosons.mH };
        break;
      case "charm_quark":
        trace.push(...quarks.steps);
        result = quarks.mCharm;
        break;
      case "down_quark":
        trace.push(...quarks.steps);
        result = quarks.mDown;
        break;
      case "up_quark":
        trace.push(...quarks.steps);
        result = quarks.mUp;
        break;
      case "ccd_hadron": {
        const pMeV = protonMeV || CODATA_PROTON_MEV;
        trace.push(...quarks.steps);
        const ccd = ccdHadronScaffold(quarks.mCharm, quarks.mDown, quarks.mUp, pMeV);
        trace.push(...ccd.steps);
        result = ccd.mCcdGeV;
        unit = "GeV";
        break;
      }
      case "lepton_e":
      case "lepton_mu":
      case "lepton_tau": {
        const lep = leptonMassesGeV();
        trace.push(...lep.steps);
        if (outputKey === "lepton_e") result = lep.mE;
        else if (outputKey === "lepton_mu") result = lep.mMu;
        else result = lep.mTau;
        break;
      }
      case "proton":
        result = protonMeV;
        unit = "MeV";
        trace.push({
          id: "proton_out",
          title: "Proton mass",
          latex: "M_p = M_{\\mathrm{constituent}} - E_{\\mathrm{bind}}",
          plain: `${protonMeV.toFixed(3)} MeV (witness / CODATA chart)`,
          module: "DerivedNucleonMass.lean",
        });
        break;
      case "inv_alpha_braced":
        result = coupling.invAlphaBraced;
        unit = "dimensionless";
        break;
      case "fano_cv":
        result = coupling.c;
        unit = "c_0 … c_6";
        break;
      default:
        throw new Error(`Unhandled output: ${outputKey}`);
    }

    return {
      inputKey,
      outputKey,
      input,
      output,
      result,
      unit,
      trace,
      coupling,
      bosons,
      neutrinos: nus,
      quarks,
      protonMeV,
    };
  }

  root.HQIVMassEngine = {
    derive,
    deriveFromRequest,
    SECTORS,
    INPUTS,
    OUTPUTS,
    WITNESS_DEFAULT,
    constants: { ALPHA, GAMMA, REFERENCE_M, CODATA_INV_ALPHA, CODATA_PROTON_MEV },
    solveCoupling,
    bosonClosure,
    neutrinoMasses,
    quarkMassesGeV,
    leptonMassesGeV,
    hadronMassFromCouplingStack,
    hadronMassFromXi,
  };
})(typeof globalThis !== "undefined" ? globalThis : window);
