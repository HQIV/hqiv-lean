export interface DerivationTerm {
  key: string;
  label: string;
  english?: string;
  meaning: string;
  derivedFrom: string;
  firstIntroduced?: {
    cardTitle: string;
    anchor: string;
  };
}

export interface DerivationStep {
  title: string;
  latex: string;
  note: string;
}

export interface DerivationCard {
  id: string;
  audienceTitle: string;
  sourceStatus?: "derived-here" | "imported-from-paper" | "consistency-check";
  teachingDescription?: string;
  oneLine: string;
  equationLatex: string;
  equationPhrase?: string;
  symbolGlossary?: DerivationTerm[];
  canvas?: {
    type:
      | "lightcone-shells"
      | "lightcone-3d-intuition"
      | "hockey-stick"
      | "tvphi"
      | "reference-shell-map"
      | "curvature-stack"
      | "deltaE-shells"
      | "omega-horizon"
      | "alpha-overlap"
      | "lattice-real-time"
      | "rapidity-aux-bridge"
      | "so8-closure-map"
      | "conservation-flow"
      | "action-stationarity"
      | "covariant-balance"
      | "plasma-bridge"
      | "continuum-bridge"
      | "mass-layers"
      | "forces-map"
      | "thermo-laws"
      | "algebra-ladder"
      | "fano-wheel"
      | "associator-map"
      | "phase-anchor-start"
      | "phase-anchor-cycle"
      | "phase-band";
    title: string;
    caption: string;
  };
  formalSource?: {
    leanSymbol?: string;
    snippet?: string;
  };
  paperReference?: {
    path: string;
    sectionHint: string;
    note: string;
  };
  nextLeanStep?: {
    label: string;
    itemId: string;
  };
  terms: DerivationTerm[];
  steps: DerivationStep[];
}

export const derivations: Record<string, DerivationCard> = {
  "lightcone-foundation": {
    id: "lightcone-foundation",
    audienceTitle: "Light cone and shell ladder",
    sourceStatus: "derived-here",
    teachingDescription:
      "This chapter introduces the shell ladder used throughout the model. A shell is one step in the discrete sequence indexed by m, and each shell gets a temperature from a simple reciprocal rule. The key result here is that every shell temperature is positive, so the starting structure is physically well-defined.",
    oneLine:
      "Each shell is indexed by a natural number, and the shell temperature formula stays positive for every shell.",
    equationLatex: String.raw`\forall m\in\mathbb{N}: \; T(m)=\frac{1}{m+1}>0`,
    equationPhrase:
      "For all shells m belonging to the natural numbers, the shell temperature is one over (m plus one), which is always positive.",
    canvas: {
      type: "lightcone-shells",
      title: "Spacetime light cone with shell steps",
      caption:
        "The origin event is at the center. As you move upward in shell index m, the temperature follows T(m)=1/(m+1), so the shell colors shift from hot to cool over time.",
    },
    formalSource: {
      leanSymbol: "step01_lightConeAuxiliarySubstrate_holds",
      snippet: String.raw`namespace Hqiv.Story.MassGap

open Hqiv

def step01_lightConeAuxiliarySubstrate : Prop :=
  (∀ m : ℕ, 0 < T m) ∧ (∀ m : ℕ, 0 < phi_of_shell m)

theorem step01_lightConeAuxiliarySubstrate_holds : step01_lightConeAuxiliarySubstrate :=
  ⟨fun m => T_pos m, fun m => phi_of_shell_pos m⟩

end Hqiv.Story.MassGap`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1A 3D light-cone intuition",
      itemId: "lc-3d-intuition",
    },
    symbolGlossary: [
      {
        key: "forall",
        label: "∀",
        english: "for all",
        meaning: "the statement applies to every allowed shell index",
        derivedFrom: "quantifier in the chapter proposition",
        firstIntroduced: {
          cardTitle: "Chapter 1 - Light cone and shell ladder",
          anchor: "chapter-1-core-equation",
        },
      },
      {
        key: "m",
        label: "m",
        english: "shell index",
        meaning: "integer shell step number starting at 0",
        derivedFrom: "discrete shell ladder indexing",
        firstIntroduced: {
          cardTitle: "Chapter 1 - Light cone and shell ladder",
          anchor: "chapter-1-core-equation",
        },
      },
      {
        key: "in",
        label: "∈",
        english: "belongs to",
        meaning: "membership relation between an element and a set",
        derivedFrom: "standard set notation",
        firstIntroduced: {
          cardTitle: "Chapter 1 - Light cone and shell ladder",
          anchor: "chapter-1-core-equation",
        },
      },
      {
        key: "N",
        label: "ℕ",
        english: "natural numbers",
        meaning: "whole numbers used to index shells",
        derivedFrom: "domain restriction for m",
        firstIntroduced: {
          cardTitle: "Chapter 1 - Light cone and shell ladder",
          anchor: "chapter-1-core-equation",
        },
      },
      {
        key: "T(m)",
        label: "T(m)",
        english: "temperature at shell m",
        meaning: "temperature assigned to shell index m",
        derivedFrom: "reciprocal ladder formula",
        firstIntroduced: {
          cardTitle: "Chapter 1 - Light cone and shell ladder",
          anchor: "chapter-1-core-equation",
        },
      },
      {
        key: "gt",
        label: ">",
        english: "is greater than",
        meaning: "strict positivity comparison",
        derivedFrom: "positivity statement",
        firstIntroduced: {
          cardTitle: "Chapter 1 - Light cone and shell ladder",
          anchor: "chapter-1-core-equation",
        },
      },
    ],
    terms: [
      {
        key: "T(m)",
        label: "T(m)",
        english: "temperature at shell m",
        meaning: "temperature at shell index m",
        derivedFrom: "defined as 1/(m+1), so denominator is always positive",
      },
    ],
    steps: [
      {
        title: "Temperature ladder",
        latex: String.raw`T(m)=\frac{1}{m+1}`,
        note: "Using natural units, each higher shell lowers the scale smoothly.",
      },
      {
        title: "Positivity",
        latex: String.raw`m\ge 0 \Rightarrow m+1>0 \Rightarrow T(m)>0`,
        note: "No shell has negative or undefined temperature.",
      },
      {
        title: "Readout sentence",
        latex: String.raw`\forall m\in\mathbb{N}: T(m)=\frac{1}{m+1}>0`,
        note: "In plain English: for every shell index m, temperature is positive.",
      },
    ],
  },
  "lightcone-3d-intuition": {
    id: "lightcone-3d-intuition",
    audienceTitle: "3D light-cone intuition",
    sourceStatus: "derived-here",
    teachingDescription:
      "Before counting formulas, we need the geometric picture: a shell is a fixed-time slice of a 3D causal cone. The triple (x,y,z) appears because we track nonnegative integer contributions in three spatial directions on that shell. So x+y+z=m is not arbitrary bookkeeping; it is the discrete 3D shell decomposition used by the model.",
    oneLine: "Triples appear because shell counting is done across three spatial coordinates.",
    equationLatex: String.raw`x+y+z=m,\qquad x,y,z\ge 0`,
    equationPhrase:
      "A shell at index m is represented by all nonnegative triples whose components add to m.",
    canvas: {
      type: "lightcone-3d-intuition",
      title: "3D cone to shell decomposition",
      caption:
        "The cone suggests causal expansion; each shell index m is a discrete radius/time layer. Points on one layer are decomposed as x+y+z=m, which is why triples appear. This view is a 2 space, 1 time, view of the cone. While in 3D it would look more like a Jawbreaker cross section... And in 4D like a firework. Very hot center, expanding and cooling down.",
    },
    symbolGlossary: [
      {
        key: "x+y+z",
        label: "x+y+z",
        english: "three spatial components",
        meaning: "three-direction decomposition on a shell",
        derivedFrom: "3D shell coordinate split",
        firstIntroduced: {
          cardTitle: "Chapter 1A - 3D light-cone intuition",
          anchor: "chapter-1a-core-equation",
        },
      },
      {
        key: "m",
        label: "m",
        english: "shell index",
        meaning: "discrete shell/time layer number",
        derivedFrom: "null-lattice shell ladder",
        firstIntroduced: {
          cardTitle: "Chapter 1 - Light cone and shell ladder",
          anchor: "chapter-1-core-equation",
        },
      },
    ],
    formalSource: {
      leanSymbol: "latticeSimplexCount",
      snippet: String.raw`def latticeSimplexCount (m : Nat) : Nat :=
  (m + 2) * (m + 1)

/- stars-and-bars numerator for x + y + z = m, x,y,z >= 0 -/`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1B simplex count + hockey-stick",
      itemId: "lc-simplex",
    },
    terms: [
      {
        key: "triple",
        label: "(x,y,z)",
        english: "3D shell coordinate triple",
        meaning: "one lattice state on shell m",
        derivedFrom: "nonnegative integer decomposition with sum m",
      },
    ],
    steps: [
      {
        title: "Shell layer",
        latex: String.raw`m=0,1,2,\dots`,
        note: "Each m selects one discrete shell layer in the cone picture.",
      },
      {
        title: "3D decomposition",
        latex: String.raw`x+y+z=m`,
        note: "Three coordinates are used because the shell decomposition is 3D.",
      },
      {
        title: "Nonnegativity",
        latex: String.raw`x,y,z\ge 0`,
        note: "Coordinates are counted as nonnegative integer allocations on the shell.",
      },
    ],
  },
  "lightcone-simplex-count": {
    id: "lightcone-simplex-count",
    audienceTitle: "Light-cone simplex counting",
    sourceStatus: "derived-here",
    teachingDescription:
      "Now we count how many triples live on shell m. Using stars-and-bars, the number of nonnegative integer triples solving x+y+z=m becomes a closed expression, and cumulative shell growth follows the hockey-stick identity in Lean.",
    canvas: {
      type: "hockey-stick",
      title: "Hockey-stick growth of cumulative shell count",
      caption:
        "Per-shell counts grow with m, and the cumulative curve follows the hockey-stick closed form used in cumLatticeSimplexCount proofs.",
    },
    oneLine: "The shell m mode count follows a closed stars-and-bars numerator.",
    equationLatex: String.raw`\mathrm{latticeSimplexCount}(m) = (m+2)(m+1)`,
    equationPhrase:
      "At shell m, the lattice simplex count equals (m plus 2) times (m plus 1).",
    symbolGlossary: [
      {
        key: "lsc",
        label: "latticeSimplexCount(m)",
        english: "simplex lattice count at shell m",
        meaning: "integer count of shell combinatorics on x+y+z=m",
        derivedFrom: "stars-and-bars count in OctonionicLightCone",
        firstIntroduced: {
          cardTitle: "Chapter 1A - Light-cone simplex count",
          anchor: "chapter-1a-core-equation",
        },
      },
      {
        key: "m",
        label: "m",
        english: "shell index",
        meaning: "nonnegative integer radial shell step",
        derivedFrom: "null-lattice readout coordinate",
        firstIntroduced: {
          cardTitle: "Chapter 1 - Light cone and shell ladder",
          anchor: "chapter-1-core-equation",
        },
      },
    ],
    formalSource: {
      leanSymbol: "latticeSimplexCount_eq",
      snippet: String.raw`def latticeSimplexCount (m : Nat) : Nat :=
  (m + 2) * (m + 1)

theorem latticeSimplexCount_eq (m : Nat) :
  latticeSimplexCount m = (m + 2) * (m + 1) := rfl`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1C temperature + auxiliary field",
      itemId: "aux-temp-phi",
    },
    terms: [
      {
        key: "count",
        label: "count",
        english: "mode count",
        meaning: "number of combinatorial lattice states on shell m",
        derivedFrom: "stars-and-bars structure",
      },
    ],
    steps: [
      {
        title: "Shell equation",
        latex: String.raw`x+y+z=m,\quad x,y,z\ge 0`,
        note: "Shell m is represented by nonnegative integer triples summing to m.",
      },
      {
        title: "Stars-and-bars count",
        latex: String.raw`\#\{(x,y,z)\}=\binom{m+2}{2}`,
        note: "Standard combinatorics for three nonnegative components.",
      },
      {
        title: "Hockey-stick cumulative relation",
        latex: String.raw`3\cdot \mathrm{cum}(n)=(n+1)(n+2)(n+3)`,
        note: "Lean proves cumulative shell growth with the closed-form cubic numerator identity.",
      },
    ],
  },
  "auxiliary-field-ladder": {
    id: "auxiliary-field-ladder",
    audienceTitle: "Temperature ladder and auxiliary field",
    sourceStatus: "derived-here",
    teachingDescription:
      "With shell indexing fixed, we define temperature and the auxiliary field at each shell. Temperature decays as 1/(m+1), while the auxiliary field is scaled as phi(m)=2/T(m). The factor 2 is explicit in Lean as phiTemperatureCoeff and corresponds to the model's homogeneous-limit normalization, so it is not an arbitrary fitting knob.",
    canvas: {
      type: "tvphi",
      title: "Temperature and phi over shell time",
      caption:
        "Across shells, T(m) cools as 1/(m+1) while φ(m)=2/T(m)=2(m+1) rises linearly; this visual explains why one decreases and the other increases.",
    },
    oneLine: "Temperature decreases with shell index, while phi grows linearly.",
    equationLatex: String.raw`T(m)=\frac{1}{m+1},\qquad \phi(m)=\frac{2}{T(m)}=2(m+1)`,
    equationPhrase:
      "At shell m, temperature is one over (m plus one), and the auxiliary field equals two divided by temperature, so phi grows like two times (m plus one).",
    symbolGlossary: [
      {
        key: "T(m)",
        label: "T(m)",
        english: "temperature at shell m",
        meaning: "shell temperature in natural Planck units",
        derivedFrom: "AuxiliaryField temperature ladder definition",
        firstIntroduced: {
          cardTitle: "Chapter 1 - Light cone and shell ladder",
          anchor: "chapter-1-core-equation",
        },
      },
      {
        key: "phi(m)",
        label: "φ(m)",
        english: "auxiliary field at shell m",
        meaning: "homogeneous-limit auxiliary field tied to temperature ladder",
        derivedFrom: "phi_of_shell = phiTemperatureCoeff / T(m), coeff=2",
        firstIntroduced: {
          cardTitle: "Chapter 1C - Temperature ladder and auxiliary field",
          anchor: "chapter-1c-core-equation",
        },
      },
    ],
    formalSource: {
      leanSymbol: "phi_of_shell_closed_form",
      snippet: String.raw`noncomputable def T (m : Nat) : ℝ := T_Pl / (m + 1 : ℝ)

noncomputable def phi_of_shell (m : Nat) : ℝ :=
  phiTemperatureCoeff / T m

theorem phi_of_shell_closed_form (m : Nat) :
    phi_of_shell m = phiTemperatureCoeff * (m + 1 : ℝ) := by
  unfold phi_of_shell T T_Pl phiTemperatureCoeff
  field_simp
  norm_num`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1D cumulative hockey-stick",
      itemId: "lc-cumulative",
    },
    terms: [
      {
        key: "phi",
        label: "φ(m)",
        english: "auxiliary field",
        meaning: "shell-wise scalar field tied to temperature ladder",
        derivedFrom: "phiTemperatureCoeff/T(m) with coeff = 2",
      },
    ],
    steps: [
      {
        title: "Temperature definition",
        latex: String.raw`T(m)=\frac{1}{m+1}`,
        note: "Natural-unit ladder from the shell index.",
      },
      {
        title: "Auxiliary field definition",
        latex: String.raw`\phi(m)=\frac{2}{T(m)}`,
        note: "The coefficient is `phiTemperatureCoeff = 2` in Lean; it is a fixed model normalization, not a tuned parameter.",
      },
      {
        title: "Closed form",
        latex: String.raw`\phi(m)=2(m+1)`,
        note: "Substitute T(m)=1/(m+1) into phi(m)=2/T(m).",
      },
    ],
  },
  "lightcone-cumulative-hockeystick": {
    id: "lightcone-cumulative-hockeystick",
    audienceTitle: "Cumulative shell growth",
    sourceStatus: "derived-here",
    teachingDescription:
      "After single-shell counting, Lean builds cumulative growth by summing shell counts. The key identity is the hockey-stick relation, which gives a closed form and proves integer divisibility and monotonic increase across shells.",
    oneLine: "Cumulative count follows a cubic numerator closed form.",
    equationLatex: String.raw`3\cdot \mathrm{cumLatticeSimplexCount}(n)=(n+1)(n+2)(n+3)`,
    equationPhrase:
      "Three times the cumulative count up to shell n equals the product (n plus 1)(n plus 2)(n plus 3).",
    canvas: {
      type: "hockey-stick",
      title: "Hockey-stick cumulative shell growth",
      caption: "Per-shell additions accumulate into the cubic closed form proved in `cumLatticeSimplexCount_hockey_stick`.",
    },
    formalSource: {
      leanSymbol: "cumLatticeSimplexCount_hockey_stick",
      snippet: String.raw`theorem cumLatticeSimplexCount_hockey_stick (n : Nat) :
  3 * cumLatticeSimplexCount n = (n + 1) * (n + 2) * (n + 3) := by
  induction n with
  | zero => simp [cumLatticeSimplexCount, latticeSimplexCount]
  | succ n ih =>
    simp only [cumLatticeSimplexCount, latticeSimplexCount]
    rw [Nat.mul_add 3, ih]
    ring_nf`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1E available/new mode laws",
      itemId: "lc-modes",
    },
    terms: [
      { key: "cum", label: "cum(n)", meaning: "sum of shell counts from 0 to n", derivedFrom: "recursive cumulative definition" },
    ],
    steps: [
      { title: "Define cumulative sum", latex: String.raw`\mathrm{cum}(n)=\sum_{m=0}^n \mathrm{latticeSimplexCount}(m)`, note: "Each shell count contributes once." },
      { title: "Apply induction", latex: String.raw`3\cdot \mathrm{cum}(n)= (n+1)(n+2)(n+3)`, note: "Lean proves this exactly via recursion + ring normalization." },
    ],
  },
  "lightcone-available-new-modes": {
    id: "lightcone-available-new-modes",
    audienceTitle: "Available modes and shell increments",
    sourceStatus: "derived-here",
    teachingDescription:
      "The combinatorial count is scaled into physically interpreted available modes, then differenced into new modes per shell step. This gives a simple linear increment law for successive shells.",
    oneLine: "Available modes scale quadratically, while new modes grow linearly by shell index.",
    equationLatex: String.raw`\mathrm{available\_modes}(m)=4(m+2)(m+1),\quad \mathrm{new\_modes}(m+1)=8(m+2)`,
    equationPhrase:
      "Available modes at shell m are quadratic in m, and the shell-to-shell increment is linear in m.",
    formalSource: {
      leanSymbol: "new_modes_succ",
      snippet: String.raw`def available_modes (m : Nat) : ℝ := (4 : ℝ) * (latticeSimplexCount m : ℝ)

theorem available_modes_eq (m : Nat) :
  available_modes m = (4 : ℝ) * ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
  unfold available_modes latticeSimplexCount
  ring

theorem new_modes_succ (m : Nat) :
  new_modes (m + 1) = 8 * (m + 2 : ℝ) := by
  unfold new_modes available_modes
  ring`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1F alpha lattice ratio",
      itemId: "lc-alpha",
    },
    terms: [
      { key: "avail", label: "available_modes", meaning: "total unlocked modes at shell m", derivedFrom: "scaled simplex count" },
      { key: "new", label: "new_modes", meaning: "incremental shell unlock count", derivedFrom: "difference between successive available values" },
    ],
    steps: [
      { title: "Scale simplex count", latex: String.raw`\mathrm{available\_modes}(m)=4\cdot\mathrm{latticeSimplexCount}(m)`, note: "Uses the model's mode-scaling convention." },
      { title: "Difference adjacent shells", latex: String.raw`\mathrm{new\_modes}(m)=\mathrm{available\_modes}(m)-\mathrm{available\_modes}(m-1)`, note: "Increment law extracted from adjacent shell totals." },
    ],
  },
  "lightcone-alpha-ratio": {
    id: "lightcone-alpha-ratio",
    audienceTitle: "Alpha calibration and lattice consistency",
    sourceStatus: "imported-from-paper",
    teachingDescription:
      "This card now includes the paper-level derivation path inline. The HQIV paper derives the controlling overlap/combinatorial structure from horizon monogamy and discrete shell counting, then fixes alpha by matching the shell-imprint form to the lattice growth law. The Lean module then verifies the resulting alpha value against exact lattice identities.",
    oneLine:
      "Alpha is derived in the paper and then verified in Lean through exact lattice-ratio checks.",
    equationLatex: String.raw`\alpha=\frac{3}{5},\qquad \frac{(n+1)(n+2)(n+3)}{5\cdot \mathrm{cum}(n)}=\alpha`,
    equationPhrase:
      "The paper route yields alpha as three-fifths, and the Lean shell ratio identity confirms that value across lattice shells.",
    canvas: {
      type: "alpha-overlap",
      title: "Monogamy overlap and alpha calibration",
      caption:
        "The overlap geometry motivates the coefficient structure (including the 1/6 overlap factor), while discrete shell counting fixes the lattice side. Matching these structures yields alpha=3/5 in the paper route and then Lean verifies consistency.",
    },
    formalSource: {
      leanSymbol: "latticeAlphaRatio_eq_alpha",
      snippet: String.raw`def alpha : ℝ := 0.60

theorem alpha_eq_3_5 : alpha = 3/5 := by unfold alpha; norm_num

theorem latticeAlphaRatio_eq_alpha (n : Nat) :
  (((n + 1) * (n + 2) * (n + 3) : ℝ) / (5 * (cumLatticeSimplexCount n : ℝ))) = alpha := by
  simp [alpha_eq_3_5]`,
    },
    paperReference: {
      path: "HQIV/paper/main.tex",
      sectionHint: "Spherical Harmonics Bridge / curvatureDensity discussion",
      note:
        "Alpha's physical derivation is treated in the HQIV paper context; this Lean module sets alpha and verifies lattice consistency identities.",
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1G reference shell indexing",
      itemId: "lc-reference-shell",
    },
    terms: [
      {
        key: "alpha",
        label: "α",
        meaning: "HQIV varying-G exponent constant used in this module",
        derivedFrom:
          "introduced as a fixed value in `OctonionicLightCone`; physically motivated derivation is referenced outside this file (see project README companion-theory note)",
      },
    ],
    steps: [
      {
        title: "Paper overlap input (monogamy geometry)",
        latex: String.raw`f(a_{\mathrm{loc}},\phi)=\frac{a_{\mathrm{loc}}}{a_{\mathrm{loc}}+\phi/6}`,
        note: "In the paper, the key overlap/monogamy coefficient appears as the geometric 1/6 factor.",
      },
      {
        title: "Discrete shell counting law",
        latex: String.raw`dN_{\mathrm{new}}(m)=8\binom{m+2}{2}=4(m+2)(m+1)`,
        note: "From stars-and-bars on x+y+z=m with octonionic lift in the paper + Lean definitions.",
      },
      {
        title: "Cumulative hockey-stick growth",
        latex: String.raw`N_{\mathrm{cum}}(m)=\sum_{k\le m} dN_{\mathrm{new}}(k)=\frac{4}{3}(m+1)(m+2)(m+3)`,
        note: "Exact cubic growth law used in both the paper narrative and Lean theorem chain.",
      },
      {
        title: "Curvature-imprint ansatz matched to lattice growth",
        latex: String.raw`\delta_E(m)\propto \frac{1}{m+1}\!\left(1+\alpha\ln\!\frac{T_{\mathrm{Pl}}}{T(m)}\right)`,
        note: "Paper fixes alpha by requiring this shell-imprint form to match the discrete-lattice growth behavior consistently.",
      },
      {
        title: "Result used throughout",
        latex: String.raw`\alpha=\frac{3}{5}`,
        note: "Paper-derived value; Lean encodes `alpha := 0.60` and proves `alpha_eq_3_5` and lattice-ratio compatibility.",
      },
      {
        title: "Lean verification identity",
        latex: String.raw`\frac{(n+1)(n+2)(n+3)}{5\cdot \mathrm{cum}(n)}=\alpha`,
        note: "This is the module-level exact check (`latticeAlphaRatio_eq_alpha`) once alpha is imported from the paper derivation.",
      },
    ],
  },
  "lightcone-reference-shell": {
    id: "lightcone-reference-shell",
    audienceTitle: "Reference shell alignment",
    sourceStatus: "derived-here",
    teachingDescription:
      "This is the first place where shell indexing becomes physically staged instead of purely combinatorial. We define a QCD-side anchor shell and then step forward a fixed number of lattice layers to get a reproducible reference shell. That reference shell is the bookkeeping bridge between early-shell counting and later thermodynamic/curvature readouts such as T_QCD and lock-in quantities.",
    oneLine: "Reference shell is built from qcdShell plus fixed step count.",
    equationLatex: String.raw`\mathrm{referenceM}=\mathrm{qcdShell}+\mathrm{stepsFromQCDToLockin}`,
    equationPhrase:
      "Reference shell equals the QCD shell plus the configured number of lock-in steps.",
    canvas: {
      type: "reference-shell-map",
      title: "Shell staging map (QCD anchor to reference shell)",
      caption:
        "This diagram motivates why shell indexing matters physically: QCD-side shell anchoring, fixed step advancement, and a reproducible reference shell for later T_QCD and curvature sections.",
    },
    formalSource: {
      leanSymbol: "referenceM",
      snippet: String.raw`def qcdShell : Nat := 1
def latticeStepCount : Nat := 3
def stepsFromQCDToLockin : Nat := latticeStepCount
def referenceM : Nat := qcdShell + stepsFromQCDToLockin`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1H curvature norm chain",
      itemId: "lc-curvature-norm",
    },
    terms: [
      { key: "referenceM", label: "referenceM", meaning: "lock-in alignment shell index", derivedFrom: "qcdShell + stepsFromQCDToLockin" },
    ],
    steps: [
      { title: "Set base shell", latex: String.raw`\mathrm{qcdShell}=1`, note: "QCD anchor index." },
      { title: "Set step count", latex: String.raw`\mathrm{latticeStepCount}=3`, note: "Discrete step depth for lock-in staging." },
      { title: "Compute reference shell", latex: String.raw`\mathrm{referenceM}=1+3=4`, note: "Reference shell evaluates to 4 in this configuration." },
    ],
  },
  "lightcone-curvature-norm": {
    id: "lightcone-curvature-norm",
    audienceTitle: "Curvature norm from cube and octonion structure",
    sourceStatus: "consistency-check",
    teachingDescription:
      "Curvature here is not dropped in as a free cosmology parameter. This block constructs the normalization from discrete geometric ingredients (cube directions, octonion dimension, projection factors), then passes that fixed normalization into shell imprints. The motivation is: if Omega_k is claimed first-principles, its normalization pipeline must also be first-principles.",
    oneLine: "Curvature norm is structurally fixed by discrete geometry inputs.",
    equationLatex: String.raw`\mathrm{curvatureNormBase}=6,\quad \mathrm{curvatureNormExponent}=7,\quad \mathrm{norm}\sim 6^7`,
    equationPhrase:
      "The normalization uses base six and exponent seven from the geometric structure chain.",
    canvas: {
      type: "curvature-stack",
      title: "First-principles curvature construction stack",
      caption:
        "Curvature normalization is assembled layer-by-layer from combinatorics and geometry before entering shell imprints; this is the groundwork for any Omega_k first-principles claim.",
    },
    formalSource: {
      leanSymbol: "curvature_norm_from_lightcone_axiom",
      snippet: String.raw`def curvatureNormBase : ℕ := 6
def curvatureNormExponent : ℕ := 7

theorem curvatureNormBase_pow_exponent :
  curvatureNormBase ^ curvatureNormExponent = 6^7 := by simp [curvatureNormBase, curvatureNormExponent]

theorem curvature_norm_from_lightcone_axiom :
  curvature_norm_combinatorial = (6^7 : ℝ) * Real.sqrt 3 := by
  -- theorem chain in file
  sorry`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1I deltaE shell imprint",
      itemId: "lc-deltaE",
    },
    terms: [
      { key: "norm", label: "curvature_norm_combinatorial", meaning: "global normalization entering shell imprint", derivedFrom: "cube + octonion dimension chain" },
    ],
    steps: [
      { title: "Set base/exponent", latex: String.raw`6,\;7`, note: "Definitions fixed in the file." },
      { title: "Build norm", latex: String.raw`6^7\sqrt{3}`, note: "Combined normalization used in imprint formulas." },
    ],
  },
  "lightcone-deltaE-imprint": {
    id: "lightcone-deltaE-imprint",
    audienceTitle: "DeltaE shell imprint formulas",
    sourceStatus: "derived-here",
    teachingDescription:
      "With shell shape and curvature normalization in place, the file defines and compares shell imprint variants (`deltaE`, quaternionic candidate, scaling relations).",
    oneLine: "DeltaE is shell-shaped and normalization-weighted.",
    equationLatex: String.raw`\delta_E(m)\propto \mathrm{shell\_shape}(m)\cdot \mathrm{curvature\_norm}`,
    equationPhrase:
      "At each shell, deltaE combines the shell-shape factor with curvature normalization.",
    canvas: {
      type: "deltaE-shells",
      title: "DeltaE across shells",
      caption:
        "Once curvature normalization is fixed, each shell gets an imprint weight δE(m). This is the immediate bridge from geometry to physically weighted shell dynamics.",
    },
    formalSource: {
      leanSymbol: "deltaE_eq",
      snippet: String.raw`theorem deltaE_eq (m : Nat) :
  deltaE m = shell_shape m * curvature_norm_combinatorial := by
  simp [deltaE]

theorem deltaE_exact_norm (m : Nat) :
  deltaE m = shell_shape m * ((6^7 : ℝ) * Real.sqrt 3) := by
  -- via curvature norm theorems
  simp`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 1J horizon-dependent Omega_k",
      itemId: "lc-omega-k",
    },
    terms: [
      { key: "deltaE", label: "δE(m)", meaning: "shell curvature imprint readout", derivedFrom: "shell_shape multiplied by normalization" },
    ],
    steps: [
      { title: "Define imprint relation", latex: String.raw`\delta_E(m)=\mathrm{shell\_shape}(m)\cdot C`, note: "C is curvature normalization constant in theorem chain." },
      { title: "Substitute exact norm", latex: String.raw`C=(6^7)\sqrt{3}`, note: "Exact norm theorem feeds this substitution." },
    ],
  },
  "lightcone-omega-k-horizon": {
    id: "lightcone-omega-k-horizon",
    audienceTitle: "Horizon-dependent Omega_k",
    sourceStatus: "derived-here",
    teachingDescription:
      "This is the key physical bridge: Omega_k is computed as a shell/horizon ratio, so curvature is dynamic and observer-horizon dependent, not a fixed constant. The lattice shell index and real cosmic time are linked through shell evolution, and that dynamic coupling is what makes the curvature readout physically meaningful rather than a static fit parameter.",
    oneLine:
      "Omega_k is dynamic: it depends on shell index and chosen horizon, connecting discrete lattice evolution to real-time curvature readout.",
    equationLatex: String.raw`\Omega_k(n;N)=\frac{\mathrm{curvature\_integral}(n)}{\mathrm{curvature\_integral}(N)}`,
    equationPhrase:
      "Omega_k at shell n and horizon N is a ratio of curvature integrals, so changing shell or horizon changes the value: curvature is dynamic, not a single constant.",
    canvas: {
      type: "omega-horizon",
      title: "Horizon-relative Omega_k ratio",
      caption:
        "Same shell n, different horizon N gives different Omega_k; same horizon N, evolving shell n also changes Omega_k. This shell-time-horizon dependence is the core reason the derivation maps to physical evolving cosmology.",
    },
    formalSource: {
      leanSymbol: "omega_k_at_horizon_eq",
      snippet: String.raw`theorem omega_k_at_horizon_eq (n N : Nat) (hN : 0 < curvature_integral N) :
  omega_k_at_horizon n N = curvature_integral n / curvature_integral N := by
  simp [omega_k_at_horizon, hN]

theorem omega_k_at_horizon_self (N : Nat) (hN : 0 < curvature_integral N) :
  omega_k_at_horizon N N = 1 := by
  simp [omega_k_at_horizon_eq, hN]`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 2 metric monotonicity",
      itemId: "ch02",
    },
    terms: [
      { key: "Omega_k", label: "Ω_k(n;N)", meaning: "horizon-relative curvature ratio", derivedFrom: "curvature integral ratio at shell and horizon indices" },
    ],
    steps: [
      { title: "Define ratio", latex: String.raw`\Omega_k(n;N)=\frac{I(n)}{I(N)}`, note: "I is curvature integral over shell ladder." },
      { title: "Self-horizon normalization", latex: String.raw`\Omega_k(N;N)=1`, note: "When shell and horizon match, ratio is exactly 1." },
      { title: "Horizon dependence", latex: String.raw`N_1\neq N_2\Rightarrow \Omega_k(n;N_1)\neq \Omega_k(n;N_2)\;\text{(in general)}`, note: "File theorem states dependence on horizon choice." },
    ],
  },
  "lattice-continuum-interface": {
    id: "lattice-continuum-interface",
    audienceTitle: "Lattice to continuum interface and counter-claim",
    sourceStatus: "derived-here",
    teachingDescription:
      "This interface is exactly where the counter-claim story lives: the native HQIV shell/manifold bookkeeping is discrete on natural-number lattice sites, while continuum test-function layers are real-valued spacetime charts. The Clay-on-R manifold mismatch is not ignored; it is exposed as an interface boundary, while still preserving accurate mathematical physics through chart embeddings and measure-level bridge objects.",
    oneLine:
      "Space bookkeeping is lattice-natural, time charting is real-valued, and the bridge is explicit rather than assumed away.",
    equationLatex: String.raw`\text{Integer lattice site }n:\mathrm{Fin}\,4\to\mathbb{Z},\qquad x_i = a\,n_i \in \mathbb{R}`,
    equationPhrase:
      "A discrete lattice site is mapped into real chart coordinates by scaling each integer component with mesh a.",
    canvas: {
      type: "lattice-real-time",
      title: "Discrete lattice index to real-time chart",
      caption:
        "Left: discrete shell/lattice sites (natural/integer indexing). Right: real chart coordinates and continuum tests. The bridge is explicit (embedding + Dirac-comb approximation), which is why the counter-claim can still preserve predictive physics.",
    },
    formalSource: {
      leanSymbol: "latticePointScaled / latticeDiracCombChartApprox",
      snippet: String.raw`abbrev IntegerLatticeSite4 := Fin 4 → ℤ

noncomputable def latticePointScaled (a : ℝ) (n : IntegerLatticeSite4) : SpacetimeEuclidean4 :=
  spacetimeOfCoords (fun i => a * (n i : ℝ))

noncomputable def latticeDiracCombChartApprox (ε : ℝ) (sites : Finset IntegerLatticeSite4) :
    Measure (Fin 4 → ℝ) :=
  ∑ n ∈ sites, Measure.dirac (spacetimeCoordsEquiv (latticePointScaled ε n))`,
    },
    nextLeanStep: {
      label: "Next Lean step: rapidity + auxiliary field phase bridge",
      itemId: "hqiv-gauge-blueprint",
    },
    terms: [
      {
        key: "bridge",
        label: "bridge objects",
        meaning: "typed embeddings between lattice and continuum layers",
        derivedFrom: "LatticeContinuumSpacetimeInterface theorems/defs",
      },
    ],
    steps: [
      {
        title: "Discrete native layer",
        latex: String.raw`n:\mathrm{Fin}\,4\to\mathbb{Z},\quad m\in\mathbb{N}`,
        note: "Shell and lattice indices are discrete by construction.",
      },
      {
        title: "Continuum chart layer",
        latex: String.raw`x\in\mathbb{R}^4`,
        note: "Clay/Dojo test-function layers are phrased on real spacetime charts.",
      },
      {
        title: "Explicit bridge",
        latex: String.raw`n \mapsto x(a,n),\quad \sum\delta_{x(a,n)}`,
        note: "Embedding plus finite Dirac-comb approximation gives a controlled interface rather than an implicit identification.",
      },
    ],
  },
  "rapidity-aux-to-gauge": {
    id: "rapidity-aux-to-gauge",
    audienceTitle: "Rapidity and auxiliary field to gauge phase",
    sourceStatus: "derived-here",
    teachingDescription:
      "This is the missing pedagogical bridge before printing closure: rapidity/time-angle scalars and the auxiliary-field phase channel are what feed CP-breaking and downstream dynamics. The gauge blueprint card should read as: first build the rapidity-phase identity, then use it in the SO(8)-closure-facing package.",
    oneLine: "Rapidity-phase identity is the dynamic scalar bridge into the gauge closure narrative.",
    equationLatex: String.raw`i\,\phi\,t\,\delta\theta'(m)=i\,\mathrm{polarAngleFromRapidity}(\phi,t,m)`,
    equationPhrase:
      "The phase term from phi, time, and shell rapidity equals the polar-angle rapidity expression used in the gauge bridge theorem.",
    canvas: {
      type: "rapidity-aux-bridge",
      title: "Time-angle/rapidity scalar bridge",
      caption:
        "Auxiliary field and time-angle scalars drive rapidity-phase structure; this is the bridge into CP-sensitive downstream physics and the SO(8)-facing gauge package.",
    },
    formalSource: {
      leanSymbol: "hqiv_gauge_rapidity_zeta_phase",
      snippet: String.raw`theorem hqiv_gauge_rapidity_zeta_phase (φ t : ℝ) (m : ℕ) :
    Complex.I * φ * t * Hqiv.delta_theta_prime (m : ℝ) =
      Complex.I * (Hqiv.Geometry.polarAngleFromRapidity φ t m : ℂ) :=
  Hqiv.Physics.zetaHQIVTerm_phase_arg_eq_polarAngleFromRapidity φ t m`,
    },
    nextLeanStep: {
      label: "Next Lean step: full SO(8) closure backbone",
      itemId: "octonion-lie",
    },
    terms: [
      {
        key: "rapidity",
        label: "rapidity phase",
        meaning: "phase-angle scalar channel tied to shell index and time-angle",
        derivedFrom: "RapidityZetaPhaseBridge theorem identity",
      },
    ],
    steps: [
      {
        title: "Time-angle scalar channel",
        latex: String.raw`\phi\,t\,\delta\theta'(m)`,
        note: "Shell-indexed phase contribution from auxiliary field and time.",
      },
      {
        title: "Rapidity angle form",
        latex: String.raw`\mathrm{polarAngleFromRapidity}(\phi,t,m)`,
        note: "Equivalent expression used by the bridge theorem.",
      },
      {
        title: "Gauge bridge identity",
        latex: String.raw`i\phi t\delta\theta' = i\,\mathrm{polarAngleFromRapidity}`,
        note: "This is the exact theorem feed into HQIVGaugeConstructionBlueprint.",
      },
    ],
  },
  "so8-closure-backbone": {
    id: "so8-closure-backbone",
    audienceTitle: "Full SO(8) closure printable backbone",
    sourceStatus: "derived-here",
    teachingDescription:
      "This card is the printable algebra backbone: 28 generators, skew symmetry, Lie-bracket closure in span, and linear independence. Together with the gauge blueprint and rapidity bridge, this is the section you can present as the complete SO(8)/G2∪Δ closure-facing scaffold.",
    oneLine: "SO(8) closure is certified by antisymmetry + bracket closure + independence in 28 dimensions.",
    equationLatex: String.raw`\forall k,\;G_k+G_k^T=0,\qquad [G_i,G_j]=\sum_k f_k G_k,\qquad \mathrm{LinInd}\{G_k\}_{k=1}^{28}`,
    equationPhrase:
      "Each generator is skew, every bracket stays inside the generator span, and the 28 generators are linearly independent.",
    canvas: {
      type: "so8-closure-map",
      title: "SO(8), G2 and Delta closure map",
      caption:
        "Rapidity/phase bridge + octonion generator backbone + closure witness gives the full Story-facing SO(8) closure package (including G2∪Delta narrative context).",
    },
    formalSource: {
      leanSymbol: "octonion_so8_lie_backbone",
      snippet: String.raw`theorem octonion_so8_lie_dim : lieClosureDim = 28 := rfl

theorem octonion_so8_lie_backbone :
    (∀ k : Fin 28, so8Generator k + transpose (so8Generator k) = 0) ∧
    (∀ i j : Fin 28, ∃ f : Fin 28 → ℝ,
      lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k) ∧
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) := by
  ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: SO(8) gauge group construction",
      itemId: "so8-gauge-group",
    },
    terms: [
      {
        key: "closure",
        label: "closure witness",
        meaning: "matrix Lie algebra closure and independence certification",
        derivedFrom: "SO8ClosureInterface re-exported via Story.OctonionLieDOF",
      },
    ],
    steps: [
      {
        title: "Dimension certificate",
        latex: String.raw`\dim \mathfrak{so}(8)=28`,
        note: "Lean definitional theorem pins lieClosureDim to 28.",
      },
      {
        title: "Skew-generator property",
        latex: String.raw`G_k+G_k^T=0`,
        note: "Each generator is antisymmetric.",
      },
      {
        title: "Bracket span closure",
        latex: String.raw`[G_i,G_j]\in \mathrm{span}\{G_k\}`,
        note: "Lie closure remains in generated algebra.",
      },
      {
        title: "Independence",
        latex: String.raw`\mathrm{LinInd}\{G_k\}_{k=1}^{28}`,
        note: "No redundant generator directions.",
      },
    ],
  },
  "td-three-laws-capstone": {
    id: "td-three-laws-capstone",
    audienceTitle: "ThermoDynamics capstone: deriving the three laws from the ladder",
    sourceStatus: "derived-here",
    teachingDescription:
      "This is written for a first-time learner: we first define temperature on shells, then define what equilibrium means, then show a conservation balance, then show dissipation. Each law is a theorem, not a slogan. The only inputs are the ladder formulas and the toy discrete heat identities already introduced.",
    oneLine:
      "Start from shell temperature; derive equilibrium, conservation, and dissipation in sequence.",
    equationLatex: String.raw`\text{Zeroth: }T(m)=T(n),\qquad \text{First: }\sum_{m<N}T_{\mathrm{cons}}(m)\,w_m=T_{\mathrm{ref}},\qquad \text{Second: }\Sigma_i\,u_i\Delta u_i\le 0`,
    equationPhrase:
      "Equal temperatures define equilibrium; weighted shell redistribution gives conservation; discrete Laplacian sign gives irreversible dissipation direction.",
    canvas: {
      type: "thermo-laws",
      title: "Three-law derivation map from shell ladder",
      caption:
        "Same ladder substrate feeds all three laws: relation level (zeroth), balance level (first), and dissipation level (second).",
    },
    formalSource: {
      leanSymbol: "zerothLaw_trans / firstLaw_tempLadder_dimShellWeight / secondLaw_entropyProduction_nonneg",
      snippet: String.raw`def thermalEquilibrium (m n : ℕ) : Prop := Hqiv.T m = Hqiv.T n
theorem zerothLaw_trans ... : thermalEquilibrium m k := ...
theorem firstLaw_tempLadder_dimShellWeight ... :
  ∑ m in Finset.range N, tempLadderConserved T_ref m * dimShellWeight p N m = T_ref := ...
theorem secondLaw_entropyProduction_nonneg ... : 0 ≤ entropyProductionCycle3 u := ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: GUT prelude (what are we solving?)",
      itemId: "gut-why-this-section",
    },
    terms: [
      {
        key: "Teq",
        label: "thermalEquilibrium",
        meaning: "equilibrium statement saying two shells have the same temperature value",
        derivedFrom: "ThermodynamicLawsFromLadder zeroth-law package",
      },
      {
        key: "Tcons",
        label: "tempLadderConserved",
        meaning: "temperature-like conserved quantity on a finite shell window",
        derivedFrom: "DivisionAlgebraZetaScaffold conservation identities",
      },
      {
        key: "Sigma",
        label: "entropyProductionCycle3",
        meaning: "entropy-production proxy that is provably nonnegative",
        derivedFrom: "ToyDiscreteHeat + ThermodynamicLawsFromLadder second-law theorems",
      },
    ],
    steps: [
      {
        title: "Start from the ladder definition",
        latex: String.raw`T(m)=\frac{1}{m+1}`,
        note: "Every thermodynamic statement in this capstone starts from this explicit shell temperature.",
      },
      {
        title: "Zeroth law (equilibrium as relation)",
        latex: String.raw`T(m)=T(n)\;\Rightarrow\;\text{equilibrium}(m,n),\quad \text{with reflexive/symmetric/transitive closure}`,
        note: "We show equilibrium is mathematically consistent as an equivalence relation, not just a phrase.",
      },
      {
        title: "First law (finite-window balance)",
        latex: String.raw`\sum_{m<N}\mathrm{tempLadderConserved}(T_{\mathrm{ref}},m)\,\mathrm{dimShellWeight}(p,N,m)=T_{\mathrm{ref}}`,
        note: "This is the conservation balance statement: redistributed contribution equals the reference total.",
      },
      {
        title: "Second law (dissipation sign)",
        latex: String.raw`\sum_i u_i\,\Delta u_i=-\sum_i(u_i-u_{i+1})^2\le 0`,
        note: "Because squares are nonnegative, the sign is fixed: dissipation is one-way in this toy mesh.",
      },
      {
        title: "CFL monotonicity witness",
        latex: String.raw`\|u^+\|_2^2\le \|u\|_2^2\quad\text{when }3\,\Delta t\,\nu\le 2`,
        note: "A concrete time-step condition guarantees energy does not increase after one update.",
      },
    ],
  },
  "gut-derivation-motivation": {
    id: "gut-derivation-motivation",
    audienceTitle: "GUT Prelude: what are we trying to derive?",
    sourceStatus: "derived-here",
    teachingDescription:
      "Before definitions, we set the target in plain language. Goal: derive an equation of motion on the HQIV substrate by a controlled chain (conserved structure -> action -> EL residual -> O-Maxwell form). This card prevents symbol overload by naming the destination first.",
    oneLine: "Goal first: derive O-Maxwell dynamics from conserved structure.",
    equationLatex: String.raw`\text{Target chain:}\quad \text{Conserved structure}\rightarrow \text{Action}\rightarrow \mathrm{EL}=0\rightarrow \text{O-Maxwell form}`,
    equationPhrase:
      "We are not classifying forces yet; we are deriving equation structure step-by-step.",
    canvas: {
      type: "action-stationarity",
      title: "Roadmap before symbols",
      caption:
        "Learner contract: every next card introduces one new layer, keeps prior layers visible, and points to the equation target.",
    },
    formalSource: {
      leanSymbol: "equations_from_action",
      snippet: String.raw`theorem equations_from_action ... :
  (S_HQVM_grav ... = 0 ↔ HQVM_Friedmann_eq ...) ∧
  (∀ a ν, EL_O ... = (∑ μ, F_from_A ... ) - 4π J_O ... - ... ) := by ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: why conservations first",
      itemId: "gut-why-conservations-first",
    },
    terms: [
      { key: "target", label: "derivation target", meaning: "final equation shape we aim to justify step-by-step", derivedFrom: "Action.lean theorem packaging" },
    ],
    steps: [
      { title: "State the destination", latex: String.raw`\mathrm{EL}=0\;\leadsto\;\text{field equation form}`, note: "Tell the student where we are going before introducing notation." },
      { title: "Choose derivation order", latex: String.raw`\text{invariants first, dynamics second}`, note: "Order matters for understanding and avoids circular explanations." },
      { title: "Scope control", latex: String.raw`\text{no force-sector labels yet}`, note: "We delay classification vocabulary until equation structure is derived." },
    ],
  },
  "gut-why-conservations-first": {
    id: "gut-why-conservations-first",
    audienceTitle: "GUT Prelude: why conservations come first",
    sourceStatus: "derived-here",
    teachingDescription:
      "A beginner question is: why not start with force equations directly? Answer: without conserved quantities, action terms are unmotivated and arbitrary. Conservations tell us what balances must be respected, then action writes those balances in a derivable equation form.",
    oneLine: "Conservations define what must be preserved before writing dynamics.",
    equationLatex: String.raw`\text{If }Q\text{ is conserved, dynamics must preserve }Q\;\Rightarrow\;\text{action terms are constrained}`,
    equationPhrase:
      "Conservation laws are the constraints; action is the machinery that encodes those constraints into equations.",
    canvas: {
      type: "conservation-flow",
      title: "Why this ordering works",
      caption:
        "Conserved quantities are the rails; action and EL travel on those rails to produce the equation of motion.",
    },
    formalSource: {
      leanSymbol: "conservations_in_structure_from_O_holds",
      snippet: String.raw`def conservations_in_structure_from_O : Prop := ...
theorem conservations_in_structure_from_O_holds : conservations_in_structure_from_O := by ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: complex numbers as phase language",
      itemId: "gut-complex",
    },
    terms: [
      { key: "Q", label: "conserved quantity", meaning: "a quantity that remains bounded/controlled by the model rules", derivedFrom: "Conservations.lean statements" },
    ],
    steps: [
      { title: "Ask the motivation question", latex: String.raw`\text{What must not be violated?}`, note: "This reframes derivation as constraint-driven rather than symbol-driven." },
      { title: "Identify conserved channels", latex: String.raw`\text{phase interval + endpoint anchors}`, note: "These are explicit, testable conservation statements in the code." },
      { title: "Translate to dynamics plan", latex: String.raw`\text{conservations}\to\text{action}\to\text{EL}`, note: "Now the next cards feel necessary, not arbitrary." },
    ],
  },
  "gut-complex-phase-language": {
    id: "gut-complex-phase-language",
    audienceTitle: "GUT S1 — Complex numbers as phase language",
    sourceStatus: "derived-here",
    teachingDescription:
      "Before higher algebras, we introduce the minimal phase tool: complex numbers. This makes later terms like i*phase and rotation factors readable for a first-time student.",
    oneLine: "Complex numbers encode 2D phase rotation with one imaginary unit i.",
    equationLatex: String.raw`z=a+bi,\quad i^2=-1,\quad e^{i\theta}=\cos\theta+i\sin\theta`,
    equationPhrase:
      "A complex number combines amplitude and phase; multiplying by e^{i theta} rotates phase.",
    canvas: {
      type: "algebra-ladder",
      title: "Number-system ladder: R to C",
      caption: "First new ingredient is one imaginary axis i, used to express phase cleanly.",
    },
    formalSource: {
      leanSymbol: "Complex phase usage in rapidity bridge",
      snippet: String.raw`theorem hqiv_gauge_rapidity_zeta_phase (φ t : ℝ) (m : ℕ) :
  Complex.I * φ * t * Hqiv.delta_theta_prime (m : ℝ) =
    Complex.I * (Hqiv.Geometry.polarAngleFromRapidity φ t m : ℂ) := ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: quaternions as 3D rotation algebra",
      itemId: "gut-quaternion",
    },
    terms: [
      { key: "i", label: "i", meaning: "imaginary unit with i^2 = -1", derivedFrom: "complex-number definition" },
      { key: "phase", label: "phase angle θ", meaning: "rotation angle in the complex plane", derivedFrom: "Euler form e^{iθ}" },
    ],
    steps: [
      { title: "Start with two real coordinates", latex: String.raw`z=(a,b)\leftrightarrow a+bi`, note: "Complex numbers package two real components into one object." },
      { title: "Define imaginary unit", latex: String.raw`i^2=-1`, note: "This single rule generates phase rotations." },
      { title: "Connect to rotations", latex: String.raw`e^{i\theta}=\cos\theta+i\sin\theta`, note: "Phase becomes algebraically manipulable." },
    ],
  },
  "gut-quaternion-rotation-bridge": {
    id: "gut-quaternion-rotation-bridge",
    audienceTitle: "GUT S2 — Quaternions as 3D rotation algebra",
    sourceStatus: "derived-here",
    teachingDescription:
      "Next we add three imaginary directions (i,j,k). This is the first place students see non-commutativity naturally, preparing them for octonion multiplication structure.",
    oneLine: "Quaternions add three imaginary units and become non-commutative.",
    equationLatex: String.raw`q=a+bi+cj+dk,\quad i^2=j^2=k^2=ijk=-1,\quad ij\neq ji`,
    equationPhrase:
      "Quaternion multiplication keeps normed-rotation intuition but order now matters.",
    canvas: {
      type: "algebra-ladder",
      title: "Number-system ladder: C to H",
      caption: "From one imaginary unit to three; multiplication order starts to matter.",
    },
    formalSource: {
      leanSymbol: "Octonion basis inherits quaternion-like substructure",
      snippet: String.raw`def e1 : OctonionVec := octonionBasis 1
def e2 : OctonionVec := octonionBasis 2
def e3 : OctonionVec := octonionBasis 3`,
    },
    nextLeanStep: {
      label: "Next Lean step: octonions and 8D basis",
      itemId: "gut-octonion",
    },
    terms: [
      { key: "noncomm", label: "non-commutative", meaning: "ab may differ from ba", derivedFrom: "quaternion multiplication rule" },
    ],
    steps: [
      { title: "Add extra imaginary axes", latex: String.raw`i,j,k`, note: "Three perpendicular imaginary directions support 3D rotation algebra." },
      { title: "Define multiplication rules", latex: String.raw`ij=k,\;jk=i,\;ki=j`, note: "Cyclic multiplication gives directional structure." },
      { title: "Observe order dependence", latex: String.raw`ij=-ji`, note: "This is the first structural warning for later octonion algebra." },
    ],
  },
  "gut-octonion-basis-bridge": {
    id: "gut-octonion-basis-bridge",
    audienceTitle: "GUT S3 — Octonions and the 8D basis",
    sourceStatus: "derived-here",
    teachingDescription:
      "Now we lift to octonions: one real unit plus seven imaginary units. Think of each state as an 8-slot vector. Later, field equations use one label to pick the octonion slot and another label to pick spacetime direction. Structurally, this is the endpoint of normed division algebras: real -> complex -> quaternion -> octonion, with no further normed-division extension beyond this rung.",
    oneLine: "Octonions are 8-component states, and they are the final normed-division rung.",
    equationLatex: String.raw`x=\sum_{r=0}^{7}x_r e_r,\qquad x\in\mathbb{R}^8`,
    equationPhrase:
      "Each octonion is an 8-component real vector in a fixed basis.",
    canvas: {
      type: "algebra-ladder",
      title: "Number-system ladder: H to O",
      caption: "Octonion basis e0..e7 becomes the 8-slot component label used later in field equations.",
    },
    formalSource: {
      leanSymbol: "OctonionVec / octonionBasis",
      snippet: String.raw`def OctonionVec := Fin 8 → ℝ
def octonionBasis (i : Fin 8) : OctonionVec := fun j => if j = i then 1 else 0
def e0 : OctonionVec := octonionBasis 0`,
    },
    nextLeanStep: {
      label: "Next Lean step: Fano plane multiplication map",
      itemId: "gut-fano-plane",
    },
    terms: [
      { key: "e0e7", label: "e0..e7", meaning: "octonion basis vectors (1 real + 7 imaginary)", derivedFrom: "OctonionBasics basis definitions" },
      { key: "slot8", label: "8 component slots", meaning: "positions 0..7 used to store octonion coefficients", derivedFrom: "OctonionVec type (Lean implementation detail hidden here)" },
    ],
    steps: [
      { title: "Define carrier space", latex: String.raw`\mathbb{O}\cong\mathbb{R}^8`, note: "Represent octonions as 8 real coefficients." },
      { title: "Name basis vectors", latex: String.raw`e_0,\ldots,e_7`, note: "e0 is real unit; e1..e7 are imaginary directions." },
      { title: "Structural endpoint fact", latex: String.raw`\mathbb{R}\rightarrow\mathbb{C}\rightarrow\mathbb{H}\rightarrow\mathbb{O}\quad(\text{stop})`, note: "For normed division algebras, octonions are the last step in this ladder." },
      { title: "Prepare equation labels", latex: String.raw`\text{field component label }a\in\{0,\dots,7\},\ \text{direction labels }(\mu,\nu)\in\{0,\dots,3\}`, note: "Later symbols use: one label for octonion slot, two labels for spacetime directions." },
    ],
  },
  "gut-fano-plane-multiplication": {
    id: "gut-fano-plane-multiplication",
    audienceTitle: "GUT S4 — Fano plane multiplication map",
    sourceStatus: "derived-here",
    teachingDescription:
      "With 7 imaginary units, multiplication needs an organizational map. The Fano plane provides that map: each oriented line gives a multiplication triple and sign convention.",
    oneLine: "Fano-plane lines encode which imaginary-unit products are positive/negative.",
    equationLatex: String.raw`e_i e_j = \pm e_k\quad\text{(from oriented Fano triples)}`,
    equationPhrase:
      "Unit multiplication is not arbitrary; it is wired by oriented triples in the Fano diagram.",
    canvas: {
      type: "fano-wheel",
      title: "Fano-plane multiplication wheel",
      caption: "Each oriented triple gives a product rule; reversing order flips sign.",
    },
    formalSource: {
      leanSymbol: "leftMulMatrix / octonionLeftMul_*",
      snippet: String.raw`def leftMulMatrix : Fin 8 → Matrix (Fin 8) (Fin 8) ℝ
  | 1 => Hqiv.octonionLeftMul_1
  | 2 => Hqiv.octonionLeftMul_2
  | ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: loss of associativity (associator)",
      itemId: "gut-nonassociative",
    },
    terms: [
      { key: "triple", label: "oriented triple", meaning: "ordered unit triple defining a product direction", derivedFrom: "Fano-plane multiplication convention" },
    ],
    steps: [
      { title: "Need a multiplication map", latex: String.raw`7\text{ imaginary units } \Rightarrow \text{structured rule table}`, note: "Too many pairings to memorize without geometry." },
      { title: "Use Fano triples", latex: String.raw`(i,j,k)\text{ line } \Rightarrow e_i e_j = e_k`, note: "Orientation determines sign/order behavior." },
      { title: "Connect to Lean matrices", latex: String.raw`L(e_i)\text{ acts on vectors}`, note: "Implementation stores multiplication by left-action matrices." },
    ],
  },
  "gut-nonassociativity-associator": {
    id: "gut-nonassociativity-associator",
    audienceTitle: "GUT S5 — Loss of associativity and associator",
    sourceStatus: "derived-here",
    teachingDescription:
      "Final structural step before conservations: octonions are non-associative, so bracket placement matters. We quantify that with the associator, then carry that structural awareness into conservation packaging.",
    oneLine: "Octonions are non-associative; associator measures the mismatch.",
    equationLatex: String.raw`[x,y,z]=(xy)z-x(yz)`,
    equationPhrase:
      "If the associator is nonzero, multiplication order-grouping changes the result.",
    canvas: {
      type: "associator-map",
      title: "Associativity loss map",
      caption: "Two multiplication paths give different outputs; associator is their vector difference.",
    },
    formalSource: {
      leanSymbol: "octonionAssociator",
      snippet: String.raw`def octonionAssociator (x y z : OctonionVec) : OctonionVec :=
  leftMulVec (leftMulVec x y) z - leftMulVec x (leftMulVec y z)`,
    },
    nextLeanStep: {
      label: "Next Lean step: GUT conservations in structure from O",
      itemId: "gut-conservations",
    },
    terms: [
      { key: "assoc", label: "associator [x,y,z]", meaning: "difference between left-grouped and right-grouped products", derivedFrom: "OctonionBasics associator definition" },
    ],
    steps: [
      { title: "Compare two groupings", latex: String.raw`(xy)z\ \text{vs}\ x(yz)`, note: "Associativity asks whether these are always equal." },
      { title: "Define mismatch vector", latex: String.raw`[x,y,z]=(xy)z-x(yz)`, note: "This is zero in associative algebras, not generally in octonions." },
      { title: "Why this matters for derivations", latex: String.raw`\text{order bookkeeping becomes structural data}`, note: "Conservation and action packaging must respect ordering-sensitive algebra." },
    ],
  },
  "gut-conservations-structure-from-o": {
    id: "gut-conservations-structure-from-o",
    audienceTitle: "GUT A0 — Conservations in structure from O",
    sourceStatus: "derived-here",
    teachingDescription:
      "Freshman-level ordering: before writing any action, we first answer what must stay conserved. This card now has two structural pillars: (1) conserved phase evolution on a bounded interval with anchored endpoints, and (2) closed SO(8)-side algebra backbone so the component space does not leak. Together they motivate why EL/O-Maxwell is a constrained derivation, not an arbitrary formula.",
    oneLine: "Conserved phase channel + closed SO(8) structure are fixed before EL/O-Maxwell.",
    equationLatex: String.raw`\mathrm{structure\_from\_O\_dim}=28,\quad \delta\theta'(t)\in[0,2\pi],\;\delta\theta'(0)=0,\;\delta\theta'(2\pi/\phi)=2\pi`,
    equationPhrase:
      "We first lock the component structure and phase-evolution constraints, then derive dynamics that must respect those locks.",
    canvas: {
      type: "conservation-flow",
      title: "Conservations before action",
      caption:
        "Counted O-structure and phase conservation are established first; action/Euler-Lagrange cards come afterward.",
    },
    formalSource: {
      leanSymbol: "conservations_in_structure_from_O_holds + octonion_so8_lie_backbone",
      snippet: String.raw`def conservations_in_structure_from_O : Prop :=
  structure_from_O_dim = 28 ∧
  ∀ φ : ℝ, 0 < φ →
    timeAngle φ 0 = 0 ∧ timeAngle φ (twoPi / φ) = twoPi ∧
    ∀ t, t ∈ Set.Icc 0 (twoPi / φ) → timeAngle φ t ∈ Set.Icc 0 twoPi

theorem conservations_in_structure_from_O_holds : conservations_in_structure_from_O := by
  ...

theorem octonion_so8_lie_backbone :
  (∀ k : Fin 28, so8Generator k + transpose (so8Generator k) = 0) ∧
  (∀ i j : Fin 28, ∃ f : Fin 28 → ℝ, lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k) ∧
  LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) := by ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: phase anchor at start",
      itemId: "gut-phase-anchor-start",
    },
    terms: [
      {
        key: "conservation",
        label: "conserved phase channel",
        meaning: "phase variable stays in a bounded interval with fixed start and end anchors",
        derivedFrom: "Conservations.lean structure theorem",
      },
      {
        key: "so8closure",
        label: "SO(8) closure witness",
        meaning: "generator bracket algebra stays closed and independent in 28 directions",
        derivedFrom: "OctonionLieDOF/SO8 closure backbone theorem",
      },
    ],
    steps: [
      {
        title: "Fix the algebraic carrier",
        latex: String.raw`\dim(\text{structure from O})=28`,
        note: "We identify the full component arena first, so later equations have a defined domain.",
      },
      {
        title: "Pin phase anchor at the start",
        latex: String.raw`\delta\theta'(0)=0`,
        note: "Initial boundary condition: phase channel starts from the neutral anchor.",
      },
      {
        title: "Pin phase anchor at the cycle endpoint",
        latex: String.raw`\delta\theta'(2\pi/\phi)=2\pi`,
        note: "Cycle-end boundary condition: one full turn is explicitly fixed, not inferred.",
      },
      {
        title: "Bound phase channel for all intermediate times",
        latex: String.raw`\delta\theta'(0)=0,\;\delta\theta'(2\pi/\phi)=2\pi,\;\delta\theta'(t)\in[0,2\pi]`,
        note: "Intermediate evolution is constrained to the same interval, so the channel cannot drift outside the conserved range.",
      },
      {
        title: "Add closure guardrail on component algebra",
        latex: String.raw`[G_i,G_j]\in\mathrm{span}\{G_k\},\ \dim=28`,
        note: "SO(8) closure means operations stay inside the declared component space; no algebraic leakage.",
      },
      {
        title: "Monotone-constrained derivation intent",
        latex: String.raw`\text{anchored + bounded phase, closed component algebra}\Rightarrow \text{constrained EL/O-Maxwell build}`,
        note: "With structural constraints fixed, EL/O-Maxwell is derived as the compatible dynamics layer.",
      },
      {
        title: "Explain why this comes first",
        latex: String.raw`\text{Conservations}\Rightarrow \text{Action}\Rightarrow \text{EL/O-Maxwell}`,
        note: "We only introduce action after the conserved quantities are explicitly defined.",
      },
    ],
  },
  "gut-phase-anchor-start": {
    id: "gut-phase-anchor-start",
    audienceTitle: "GUT A0a — Phase anchor at start",
    sourceStatus: "derived-here",
    teachingDescription:
      "This is the first boundary condition in the phase story: at start time, phase is anchored at zero. Visually, this is the left endpoint pin that fixes where evolution begins.",
    oneLine: "Initial time starts at phase zero: δθ′(0)=0.",
    equationLatex: String.raw`\delta\theta'(0)=0`,
    equationPhrase:
      "At the start, phase has no accumulated turn yet.",
    canvas: {
      type: "phase-anchor-start",
      title: "Initial phase anchor",
      caption: "The evolution curve is pinned at the origin in phase-time space.",
    },
    formalSource: {
      leanSymbol: "conservations_in_structure_from_O_holds",
      snippet: String.raw`... timeAngle φ 0 = 0 ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: phase anchor at cycle endpoint",
      itemId: "gut-phase-anchor-cycle",
    },
    terms: [
      { key: "start", label: "start anchor", meaning: "fixed initial point of phase trajectory", derivedFrom: "timeAngle φ 0 = 0" },
    ],
    steps: [
      { title: "Choose time origin", latex: String.raw`t=0`, note: "We need a common start reference for all trajectories." },
      { title: "Pin initial phase", latex: String.raw`\delta\theta'(0)=0`, note: "No arbitrary offset is allowed at the initial point." },
    ],
  },
  "gut-phase-anchor-cycle": {
    id: "gut-phase-anchor-cycle",
    audienceTitle: "GUT A0b — Phase anchor at cycle endpoint",
    sourceStatus: "derived-here",
    teachingDescription:
      "Second boundary condition: at the endpoint time 2π/ϕ, phase lands exactly at 2π. This makes one full cycle explicit and prevents drift in cycle closure.",
    oneLine: "Endpoint closes at full turn: δθ′(2π/ϕ)=2π.",
    equationLatex: String.raw`\delta\theta'(2\pi/\phi)=2\pi`,
    equationPhrase:
      "One full cycle in time-angle corresponds to one full phase turn.",
    canvas: {
      type: "phase-anchor-cycle",
      title: "Cycle-end phase anchor",
      caption: "A second pin enforces full-cycle closure instead of free endpoint drift.",
    },
    formalSource: {
      leanSymbol: "conservations_in_structure_from_O_holds",
      snippet: String.raw`... timeAngle φ (twoPi / φ) = twoPi ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: bounded phase evolution",
      itemId: "gut-phase-bounded",
    },
    terms: [
      { key: "cycle", label: "cycle endpoint", meaning: "time value where one full phase turn is enforced", derivedFrom: "timeAngle φ (2π/φ) = 2π" },
    ],
    steps: [
      { title: "Define cycle-end time", latex: String.raw`t_\star=2\pi/\phi`, note: "This is the designated closure time for the phase channel." },
      { title: "Pin closure value", latex: String.raw`\delta\theta'(t_\star)=2\pi`, note: "Endpoint is fixed at a full turn, not estimated." },
    ],
  },
  "gut-phase-bounded-evolution": {
    id: "gut-phase-bounded-evolution",
    audienceTitle: "GUT A0c — Bounded phase evolution",
    sourceStatus: "derived-here",
    teachingDescription:
      "With both endpoints fixed, we still need an in-between guarantee: the phase trajectory must stay inside the band [0,2π] at all intermediate times. This is the conservation band that later action terms must respect.",
    oneLine: "Intermediate phase values stay in the conserved band [0,2π].",
    equationLatex: String.raw`\delta\theta'(t)\in[0,2\pi]\quad \text{for }t\in[0,2\pi/\phi]`,
    equationPhrase:
      "Phase starts at 0, ends at 2π, and never exits the allowed interval in between.",
    canvas: {
      type: "phase-band",
      title: "Phase-space conservation band",
      caption: "The full trajectory remains trapped between lower and upper phase rails.",
    },
    formalSource: {
      leanSymbol: "conservations_in_structure_from_O_holds",
      snippet: String.raw`... ∀ t, t ∈ Set.Icc 0 (twoPi / φ) → timeAngle φ t ∈ Set.Icc 0 twoPi`,
    },
    nextLeanStep: {
      label: "Next Lean step: GUT action core objects",
      itemId: "gut-action-core",
    },
    terms: [
      { key: "band", label: "phase band [0,2π]", meaning: "allowed interval that trajectory cannot leave", derivedFrom: "interval membership theorem" },
    ],
    steps: [
      { title: "Specify allowed range", latex: String.raw`0\le \delta\theta'(t)\le 2\pi`, note: "Defines the conservation corridor for the whole interval." },
      { title: "Apply to all intermediate times", latex: String.raw`t\in[0,2\pi/\phi]`, note: "Constraint is global over the interval, not only at endpoints." },
      { title: "Use as dynamics constraint", latex: String.raw`\text{later EL terms must respect this band}`, note: "Action is derived on top of this bounded channel." },
    ],
  },
  "gut-action-core-terms": {
    id: "gut-action-core-terms",
    audienceTitle: "GUT A1 — Action core objects",
    sourceStatus: "derived-here",
    teachingDescription:
      "Now that conserved structure is fixed, we introduce the action symbols in the smallest possible steps. Each new symbol appears once with a plain meaning, then gets reused. No hidden metric machinery appears yet.",
    oneLine: "Define A, F, source J, and EL terms one-by-one.",
    equationLatex: String.raw`F_{a\mu\nu}=A_{a\nu}-A_{a\mu},\qquad \mathrm{EL}_{O,\text{general}}= \sum_{\mu}F_{a\mu\nu}-4\pi J_{a\nu}-\mathbf{1}_{a=0}\,\alpha\log(\phi+1)\,\partial_\nu\phi`,
    equationPhrase:
      "Potential first, then field strength, then source coupling, then EL residual that yields O-Maxwell shape.",
    canvas: {
      type: "action-stationarity",
      title: "A -> F -> L -> EL ladder",
      caption:
        "Every later GUT card reuses these slots; this is the base object graph before covariant metric machinery.",
    },
    formalSource: {
      leanSymbol: "EL_O_general_eq_F_divergence_sub_sources",
      snippet: String.raw`def F_from_A (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (μ ν : Fin 4) : ℝ := A a ν - A a μ
def L_O_source_general (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) : ℝ := ∑ a, ∑ ν, J_src a ν * A a ν
noncomputable def EL_O_general (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) : ℝ := ...
theorem EL_O_general_eq_F_divergence_sub_sources ... := rfl`,
    },
    nextLeanStep: {
      label: "Next Lean step: plasma source specialization",
      itemId: "gut-action-plasma",
    },
    terms: [
      { key: "A", label: "A_{a\\nu}", meaning: "octonion-indexed gauge potential component", derivedFrom: "Action.lean A_O/F_from_A scaffold" },
      { key: "F", label: "F_{a\\mu\\nu}", meaning: "discrete antisymmetric field strength built from A", derivedFrom: "Action.lean F_from_A" },
      { key: "J", label: "J_{a\\nu}", meaning: "generic source slot for forcing terms", derivedFrom: "L_O_source_general J_src" },
      { key: "EL", label: "EL_O", meaning: "residual combining divergence, source, and phi coupling", derivedFrom: "EL_O_general definition" },
    ],
    steps: [
      { title: "Introduce the field variable", latex: String.raw`A:\mathrm{Fin}\,8\to\mathrm{Fin}\,4\to\mathbb{R}`, note: "This is the object we vary later; think of it as the primary unknown." },
      { title: "Define field strength from differences", latex: String.raw`F_{a\mu\nu}=A_{a\nu}-A_{a\mu}`, note: "No extra assumption: F is built directly from A." },
      { title: "Add interaction with source", latex: String.raw`L_{\text{source}}=\sum_{a,\nu}J_{a\nu}A_{a\nu}`, note: "This term says where external/current input enters the model." },
      { title: "Assemble EL residual", latex: String.raw`\mathrm{EL}=\sum_\mu F_{a\mu\nu}-4\pi J_{a\nu}-\mathbf{1}_{a=0}\alpha\log(\phi+1)\partial_\nu\phi`, note: "This is the equation shape we preserve in every later bridge card." },
      { title: "Interpretation checkpoint", latex: String.raw`\mathrm{EL}=0`, note: "Dynamics means: divergence-like term balanced by source and phi-coupling corrections." },
      { title: "O-Maxwell correspondence statement", latex: String.raw`\mathrm{EL}_O=0\ \Longleftrightarrow\ \text{inhomogeneous O-Maxwell form (same source slot)}`, note: "This is the bridge from action language to field-equation language." },
    ],
  },
  "gut-action-plasma-bridge": {
    id: "gut-action-plasma-bridge",
    audienceTitle: "GUT A2 — Action plasma bridge",
    sourceStatus: "derived-here",
    teachingDescription:
      "Instead of changing the whole equation, we change only one slot: the source J. This teaches an important derivation habit: specialize one ingredient at a time and track what stays invariant.",
    oneLine: "Specialize J_src to plasma while preserving EL/action form.",
    equationLatex: String.raw`J_{\mathrm{src}}:=J_{O,\mathrm{plasma}}(j_0,\mathrm{coord}),\qquad L_{\mathrm{source}}=\sum_\nu \mathrm{schematicPlasmaScalar}(j_0,\mathrm{coord}_\nu)\,A_{0\nu}`,
    equationPhrase:
      "Plasma specialization changes source content but keeps equation architecture unchanged.",
    canvas: {
      type: "plasma-bridge",
      title: "Generic source to plasma source",
      caption:
        "Only the source slot is specialized; kinetic and phi terms are unchanged from Action.lean.",
    },
    formalSource: {
      leanSymbol: "L_O_source_general_J_O_plasma",
      snippet: String.raw`theorem L_O_source_general_J_O_plasma ... :
  L_O_source_general (J_O_plasma j₀ coord) A =
    ∑ ν : Fin 4, schematicPlasmaScalar j₀ (coord ν) * A 0 ν := by ...
theorem EL_O_plasma_eq_emergent_shape ... := ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: continuum phi-gradient closure",
      itemId: "gut-continuum-closure",
    },
    terms: [
      { key: "j0", label: "j_0", meaning: "plasma amplitude knob in source definition", derivedFrom: "ActionPlasmaBridge J_O_plasma" },
      { key: "Jplasma", label: "J_{O,plasma}", meaning: "concrete current instance for J_src slot", derivedFrom: "ActionPlasmaBridge source specialization" },
    ],
    steps: [
      { title: "Choose a concrete source", latex: String.raw`J_{\mathrm{src}}\mapsto J_{O,\mathrm{plasma}}(j_0,\mathrm{coord})`, note: "Only the source function changes; A and F definitions do not." },
      { title: "Track where source appears", latex: String.raw`L_{\mathrm{source}}=\sum_{a,\nu}J_{a\nu}A_{a\nu}`, note: "This is the exact slot where specialization propagates." },
      { title: "Compute specialization result", latex: String.raw`L_{\mathrm{source}}\to \sum_\nu \mathrm{schematicPlasmaScalar}(j_0,\mathrm{coord}_\nu)\,A_{0\nu}`, note: "In this model, contribution collapses to the EM channel." },
      { title: "Architecture invariance check", latex: String.raw`\mathrm{EL}\text{ form unchanged; only }J\text{ term updated}`, note: "Key derivation principle: same equation skeleton, new source content." },
    ],
  },
  "gut-continuum-omaxwell-closure": {
    id: "gut-continuum-omaxwell-closure",
    audienceTitle: "GUT A3 — Continuum O-Maxwell closure",
    sourceStatus: "derived-here",
    teachingDescription:
      "This card answers: how do we move from placeholder gradients to real chart gradients without rewriting the whole model? We upgrade only the gradient slot and keep all other action/EL pieces fixed.",
    oneLine: "Replace placeholder grad_phi by continuum/chart gradients, then by metric-raised gradients.",
    equationLatex: String.raw`\partial_\nu\phi\;\leadsto\;\mathrm{coordsGradientComponents}(\phi_F,c,\nu)\;\leadsto\;g^{\nu\mu}\partial_\mu\phi`,
    equationPhrase:
      "We replace the gradient meaning in two stages: chart gradient first, metric-raised gradient second.",
    canvas: {
      type: "continuum-bridge",
      title: "Pre-metric to metric-ready phi channel",
      caption:
        "ContinuumOmaxwellClosure keeps equation shape fixed while upgrading only the gradient semantics.",
    },
    formalSource: {
      leanSymbol: "EL_O_general_coordsField",
      snippet: String.raw`noncomputable def EL_O_general_coordsField ... :=
  (∑ μ, F_from_A A a μ ν) - 4 * Real.pi * J_src a ν
    - (if a = 0 then alpha * Real.log (φ_val + 1) * coordsGradientComponents φF c ν else 0)
noncomputable def EL_O_general_coordsField_metric ... := ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: covariant HQVM packaging",
      itemId: "gut-covariant",
    },
    terms: [
      { key: "phiF", label: "\\phi_F", meaning: "continuum scalar field on chart coordinates", derivedFrom: "ContinuumSpacetimeChart interface" },
      { key: "gradcoords", label: "\\mathrm{coordsGradientComponents}", meaning: "chart-based gradient components at basepoint c", derivedFrom: "ContinuumOmaxwellClosure definitions" },
      { key: "gInv", label: "g^{\\nu\\mu}", meaning: "inverse metric used to raise gradient index", derivedFrom: "contravariantGradientComponentsAt" },
    ],
    steps: [
      { title: "Identify the placeholder slot", latex: String.raw`\partial_\nu\phi\ \text{(placeholder in earlier card)}`, note: "We explicitly point to the one place being upgraded." },
      { title: "Chart-level upgrade", latex: String.raw`\partial_\nu\phi\to \mathrm{coordsGradientComponents}(\phi_F,c,\nu)`, note: "Now gradient is computed from a continuum field at a basepoint." },
      { title: "Metric-aware upgrade", latex: String.raw`\mathrm{coordsGradient}\to g^{\nu\mu}\partial_\mu\phi`, note: "Index raising adds metric dependence while staying in same equation slot." },
      { title: "Structural invariance check", latex: String.raw`L_O,\mathrm{EL}_O\ \text{keep same algebraic skeleton}`, note: "Only gradient semantics changed; source/divergence packaging remains aligned." },
    ],
  },
  "gut-covariant-packaging": {
    id: "gut-covariant-packaging",
    audienceTitle: "GUT A4 — Covariant solution packaging",
    sourceStatus: "derived-here",
    teachingDescription:
      "This is the final pre-GR derivation step. We make metric dependence explicit, build a covariant-style divergence, and show how this connects to the O-Maxwell residual form introduced earlier.",
    oneLine: "Introduce explicit metric-aware divergence before full GR development.",
    equationLatex: String.raw`\nabla_\mu F^{\mu\nu}\;\sim\;\frac{1}{\sqrt{-g}}\sum_\mu \sqrt{-g}\,F^{\mu\nu},\qquad g^{-1}=g^{-1}_{\mathrm{HQVM}}(N,a,\Phi)`,
    equationPhrase:
      "The covariant divergence form is represented with explicit HQVM metric factors, tying field equations to the metric background data.",
    canvas: {
      type: "covariant-balance",
      title: "Covariant balance on HQVM metric",
      caption:
        "Action-level equations are lifted into metric-aware divergence form with HQVM inverse metric and volume factor terms, providing the explicit covariance bridge.",
    },
    formalSource: {
      leanSymbol: "covariant_O_Maxwell_residual_HQVM_explicit",
      snippet: String.raw`noncomputable def covariant_div_F_O ... :=
  (1 / sqrt_neg_g) * ∑ μ, sqrt_neg_g * raisedFieldStrength_O ...

theorem covariant_div_F_O_HQVM ... :
  covariant_div_F_O ... = ∑ μ, HQVM_inverseMetric ... * ... * F ... := by ...

theorem covariant_O_Maxwell_residual_HQVM_explicit ... := by ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: Chapter 2 HQVM metric",
      itemId: "ch02",
    },
    terms: [
      { key: "Fup", label: "F^{\\mu\\nu}", meaning: "field-strength components after index-raising with inverse metric", derivedFrom: "raisedFieldStrength_O definitions" },
      { key: "sqrtg", label: "√(-g)", meaning: "HQVM volume factor in divergence packaging", derivedFrom: "CovariantSolution definitions" },
      { key: "residual", label: "covariant residual", meaning: "full metric-aware balance expression set to zero for equation of motion", derivedFrom: "covariant_O_Maxwell_residual definitions" },
    ],
    steps: [
      { title: "Raise field indices", latex: String.raw`F^{\mu\nu}=g^{\mu\rho}g^{\nu\sigma}F_{\rho\sigma}`, note: "This introduces explicit metric geometry into the field tensor." },
      { title: "Build weighted divergence", latex: String.raw`\frac{1}{\sqrt{-g}}\sum_\mu \sqrt{-g}F^{\mu\nu}`, note: "Volume-factor weighting is the covariant-style divergence surrogate." },
      { title: "Attach source and phi channels", latex: String.raw`\text{covariant residual}=\text{(divergence)}-4\pi J-\phi\text{-term}`, note: "Same physical channels as earlier EL form, now metric-aware." },
      { title: "Equation form", latex: String.raw`\text{covariant residual}=0`, note: "This is the derived O-Maxwell-on-background equation used just before GR chapter." },
    ],
  },
  "gut-conserved-content-mass-bridge": {
    id: "gut-conserved-content-mass-bridge",
    audienceTitle: "GUT A5 — Conserved content to mass hierarchy",
    sourceStatus: "derived-here",
    teachingDescription:
      "This bridge classifies fermion content by conserved decorations and turns that classification into an ordered complexity proxy. It is a narrative bridge for masses, not a metric tensor derivation.",
    oneLine: "Conserved-content class -> closure layer -> intrinsic complexity ordering.",
    equationLatex: String.raw`l(c)\in\{1,2,3\},\qquad \mathrm{intrinsicWaveComplexity}(c)=l(c)^2,\qquad \nu<\ell<q`,
    equationPhrase:
      "Neutrino, charged lepton, and quark classes map to increasing closure rank and squared complexity.",
    canvas: {
      type: "mass-layers",
      title: "Closure-layer mass ordering scaffold",
      caption:
        "Classification and strict ordering are proved first; detailed mass pipelines can then attach to this scaffold.",
    },
    formalSource: {
      leanSymbol: "closureLayer_rank_matches_triple_count",
      snippet: String.raw`def conservedTripleCount : FermionContentClass → ℕ
  | .neutrino => 1 | .chargedLepton => 2 | .quark => 3
noncomputable def intrinsicWaveComplexity (c : FermionContentClass) : ℝ :=
  (conservedTripleCount c : ℝ) ^ 2
theorem closureLayer_rank_matches_triple_count ... := by ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: forces and unit correspondence",
      itemId: "gut-forces",
    },
    terms: [
      { key: "l", label: "l(c)", meaning: "conserved triple count per content class", derivedFrom: "ConservedContentMassBridge conservedTripleCount" },
      { key: "iwc", label: "intrinsicWaveComplexity", meaning: "squared closure complexity proxy", derivedFrom: "intrinsicWaveComplexity definition" },
    ],
    steps: [
      { title: "Classify content", latex: String.raw`c\in\{\nu,\ell,q\}`, note: "Three closure-decoration classes." },
      { title: "Assign closure ranks", latex: String.raw`l(\nu)=1,\;l(\ell)=2,\;l(q)=3`, note: "Rank matches conserved triple count." },
      { title: "Build complexity proxy", latex: String.raw`\mathrm{intrinsicWaveComplexity}=l^2`, note: "Monotone ordering supports hierarchy narrative." },
    ],
  },
  "gut-forces-assignment": {
    id: "gut-forces-assignment",
    audienceTitle: "GUT A6 — Forces assignment and units",
    sourceStatus: "derived-here",
    teachingDescription:
      "This card closes the ladder by mapping O-components to force sectors and showing metric-vs-SI equation correspondence. It also states the weak-tipping geometric interpretation as a downstream physical narrative.",
    oneLine: "Map O-components to EM/Weak/Strong and preserve equation form across unit systems.",
    equationLatex: String.raw`\text{sector}(a)\in\{\mathrm{EM},\mathrm{Weak},\mathrm{Strong}\},\qquad \mathcal{R}_{\mathrm{metric}}=0\Leftrightarrow \mathcal{R}_{\mathrm{SI}}=0`,
    equationPhrase:
      "Force-sector assignment is explicit, and metric/SI conversions preserve the same residual-zero statement.",
    canvas: {
      type: "forces-map",
      title: "Sector map and unit bridge",
      caption:
        "From conserved structure to named force sectors, with explicit metric-to-SI conversion scaffolding.",
    },
    formalSource: {
      leanSymbol: "equation_metric_iff_SI",
      snippet: String.raw`inductive ForceSector | EM | Weak | Strong
def O_component_to_sector (a : Fin 8) : ForceSector := ...
theorem equation_metric_iff_SI (a : Fin 8) (ν : Fin 4) :
  emergentMaxwellInhomogeneous_O_metric a ν = 0 ↔
  emergentMaxwellInhomogeneous_O_SI a ν (J_O · ·) = 0 := by ...`,
    },
    nextLeanStep: {
      label: "Next Lean step: rapidity and aux-field gauge bridge",
      itemId: "hqiv-gauge-blueprint",
    },
    terms: [
      { key: "sector", label: "ForceSector", meaning: "EM/Weak/Strong assignment target", derivedFrom: "Forces.lean ForceSector" },
      { key: "units", label: "UnitSystem", meaning: "Metric or SI equation interpretation", derivedFrom: "Forces.lean unit scaffolding" },
    ],
    steps: [
      { title: "Assign sectors", latex: String.raw`a=0\mapsto \mathrm{EM},\;a\in\{1,2,3\}\mapsto \mathrm{Weak},\;a\ge4\mapsto \mathrm{Strong}`, note: "Component-to-sector map is explicit." },
      { title: "Define conversion carriers", latex: String.raw`\mathrm{UnitSystem}\in\{\mathrm{Metric},\mathrm{SI}\}`, note: "Values are interpreted in either unit frame." },
      { title: "Residual equivalence", latex: String.raw`\mathcal{R}_{\mathrm{metric}}=0\Leftrightarrow \mathcal{R}_{\mathrm{SI}}=0`, note: "Equation form survives unit conversion bookkeeping." },
    ],
  },
  "hqvm-time-angle": {
    id: "hqvm-time-angle",
    audienceTitle: "HQVM time-angle monotonicity",
    oneLine: "If time increases, the HQVM time-angle also increases for each shell.",
    equationLatex: String.raw`t_1\le t_2 \Rightarrow \operatorname{timeAngle}(\phi(m),t_1)\le \operatorname{timeAngle}(\phi(m),t_2)`,
    terms: [
      {
        key: "timeAngle",
        label: "timeAngle(φ,t)",
        meaning: "effective HQVM angle-of-time map",
        derivedFrom: "metric layer built with positive phi(m)",
      },
      {
        key: "phi(m)",
        label: "phi(m)",
        meaning: "positive shell field from Chapter 1",
        derivedFrom: "step01 light-cone auxiliary substrate",
      },
    ],
    steps: [
      {
        title: "Assume shell positivity",
        latex: String.raw`\phi(m)>0`,
        note: "Pulled from the Chapter 1 foundation proof.",
      },
      {
        title: "Monotone map",
        latex: String.raw`t_1\le t_2\Rightarrow \operatorname{timeAngle}(\phi(m),t_1)\le\operatorname{timeAngle}(\phi(m),t_2)`,
        note: "Gives the conservation gate for the next chapter.",
      },
    ],
  },
  "harmonic-mass-ladder": {
    id: "harmonic-mass-ladder",
    audienceTitle: "Mass coupling on shell ladder",
    oneLine: "Binding energy scales with reduced mass, charge, and shell-effective coupling.",
    equationLatex: String.raw`E_{\text{bind}}(m)=\frac{\mu Z^2}{2}\,\alpha_{\text{eff}}(m)^2,\quad \alpha_{\text{eff}}(m)=\big(\alpha_{\text{eff}}^{-1}(m)\big)^{-1}`,
    terms: [
      {
        key: "mu",
        label: "μ",
        meaning: "reduced mass for the bound system",
        derivedFrom: "standard two-body reduction in the shell model",
      },
      {
        key: "Z",
        label: "Z",
        meaning: "effective charge number",
        derivedFrom: "appears quadratically in hydrogenic-style scaling",
      },
      {
        key: "alpha_eff",
        label: "α_eff(m)",
        meaning: "effective coupling at shell m",
        derivedFrom: "computed from shell ladder quantities",
      },
    ],
    steps: [
      {
        title: "Effective coupling",
        latex: String.raw`\alpha_{\text{eff}}(m)=\left(\alpha_{\text{eff}}^{-1}(m)\right)^{-1}`,
        note: "Sets shell-resolved coupling from inverse form used in code.",
      },
      {
        title: "Binding law",
        latex: String.raw`E_{\text{bind}}=\frac{\mu Z^2}{2}\alpha_{\text{eff}}^2`,
        note: "Hydrogenic shape on each shell; drives particle mass estimates.",
      },
    ],
  },
  "baryogenesis-shell-imprint": {
    id: "baryogenesis-shell-imprint",
    audienceTitle: "QCD shell baryogenesis anchor",
    oneLine: "Baryogenesis readouts attach at QCD and lock-in shells via shell imprint and curvature calibration.",
    equationLatex: String.raw`\lvert \text{shell\_shape}(m_{\text{lockin}})\rvert>0,\quad \Omega_k(m_{\text{lockin}},m_{\text{lockin}})=1,\quad T_{\text{QCD}}=T(m_{\text{QCD}})`,
    terms: [
      {
        key: "m_qcd",
        label: "m_QCD",
        meaning: "shell index where QCD-scale readout is taken",
        derivedFrom: "temperature ladder identification",
      },
      {
        key: "m_lockin",
        label: "m_lockin",
        meaning: "lock-in shell where curvature is normalized",
        derivedFrom: "Omega_k calibration theorem at lock-in",
      },
      {
        key: "Omega_k",
        label: "Ω_k",
        meaning: "curvature term on shell geometry",
        derivedFrom: "set to 1 at lock-in by calibration identity",
      },
    ],
    steps: [
      {
        title: "Temperature identities",
        latex: String.raw`T_{\text{QCD}}=T(m_{\text{QCD}}),\;T_{\text{lockin}}=T(m_{\text{lockin}})`,
        note: "Connects named scales to the same shell ladder function.",
      },
      {
        title: "Curvature lock-in",
        latex: String.raw`\Omega_k(m_{\text{lockin}},m_{\text{lockin}})=1`,
        note: "Sets normalized reference point for later readouts.",
      },
    ],
  },
  "ns-eddy-viscosity-scaffold": {
    id: "ns-eddy-viscosity-scaffold",
    audienceTitle: "Navier-Stokes effective viscosity scaffold",
    oneLine: "At lock-in shell, the HQIV eddy viscosity term is nonnegative, giving a stable fluid-side sign condition.",
    equationLatex: String.raw`\nu_{\text{eddy}}^{\text{HQIV}}(m_{\text{lockin}},0,0)\ge 0`,
    terms: [
      {
        key: "nu_eddy",
        label: "ν_eddy^HQIV",
        meaning: "effective eddy viscosity in HQIV fluid closure",
        derivedFrom: "Debye-scale scaffold and shell closure assumptions",
      },
      {
        key: "m_lockin",
        label: "m_lockin",
        meaning: "lock-in reference shell",
        derivedFrom: "baryogenesis chapter reference shell",
      },
    ],
    steps: [
      {
        title: "Lock-in evaluation",
        latex: String.raw`\nu_{\text{eddy}}^{\text{HQIV}}(m_{\text{lockin}},u,v)`,
        note: "Evaluate near baseline state u=v=0.",
      },
      {
        title: "Sign theorem",
        latex: String.raw`\nu_{\text{eddy}}^{\text{HQIV}}(m_{\text{lockin}},0,0)\ge 0`,
        note: "Gives a fluid bridge toward NS formulation (not full Clay proof).",
      },
    ],
  },
  "so8-g2-delta-closure": {
    id: "so8-g2-delta-closure",
    audienceTitle: "SO(8) closure from G2 plus Delta",
    oneLine: "The gauge story is built by extending G2 with a phase-lift sector Δ to reach full SO(8)-class closure used in the YM pipeline.",
    equationLatex: String.raw`\mathfrak{g}_2 \oplus \Delta \;\Longrightarrow\; \mathfrak{so}(8)\;\text{(closure package)}`,
    terms: [
      {
        key: "g2",
        label: "g2",
        meaning: "exceptional Lie algebra preserving octonion structure",
        derivedFrom: "octonion algebra backbone in HQIV",
      },
      {
        key: "Delta",
        label: "Δ",
        meaning: "phase-lift generator sector",
        derivedFrom: "added degrees of freedom completing gauge closure",
      },
      {
        key: "so8",
        label: "so(8)",
        meaning: "target Lie algebra with 28 generators",
        derivedFrom: "closure and independence witnesses in SO(8) path",
      },
    ],
    steps: [
      {
        title: "Start from octonionic symmetry",
        latex: String.raw`\mathfrak{g}_2`,
        note: "Captures automorphism-side structure of octonion sector.",
      },
      {
        title: "Add phase-lift sector",
        latex: String.raw`\mathfrak{g}_2\oplus \Delta`,
        note: "Introduces missing direction used by HQIV gauge blueprint.",
      },
      {
        title: "Closure target",
        latex: String.raw`\operatorname{LieClosure}(\mathfrak{g}_2\oplus\Delta)=\mathfrak{so}(8)`,
        note: "Feeds compact simple gauge group constructions.",
      },
    ],
  },
  "patch-commutator-locality": {
    id: "patch-commutator-locality",
    audienceTitle: "Patch-QFT locality hook",
    oneLine: "In the abelian patch layer, smeared operators commute, giving a concrete locality hook before full non-abelian YM packaging.",
    equationLatex: String.raw`A\in\mathcal{A}(R),\,B\in\mathcal{A}(S)\Rightarrow [A,B]=0`,
    terms: [
      {
        key: "A(R)",
        label: "A(R)",
        meaning: "operator in patch algebra over region R",
        derivedFrom: "support-restricted patch net definition",
      },
      {
        key: "comm",
        label: "[A,B]",
        meaning: "operator commutator AB - BA",
        derivedFrom: "vanishes in abelian patch construction",
      },
    ],
    steps: [
      {
        title: "Patch algebra membership",
        latex: String.raw`A\in\mathcal{A}(R),\;B\in\mathcal{A}(S)`,
        note: "Operators belong to local patch algebras.",
      },
      {
        title: "Abelian commutator theorem",
        latex: String.raw`[A,B]=0`,
        note: "Locality-style constraint used as an entry hook to QFT narrative.",
      },
    ],
  },
};
