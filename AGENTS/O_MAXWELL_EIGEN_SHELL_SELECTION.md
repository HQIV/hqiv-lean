# Toward modal-frequency/horizon emergence from lifted O-Maxwell

**Status:** design note (research direction + repo alignment). **Not** a proved theorem bundle.

This document captures a single coherent target: **one dynamics** (modified octonionic Maxwell + \(\varphi\)), **multiple sectors** (Fano projections), with **modal frequencies / horizons upstream** and **null-lattice readout indices as derived outputs** (modes / eigenconditions), instead of treating **hand-picked \(\mathbb{N}\)** tables plus GeV anchors as the fundamental strong-sector story.

---

## 1. Current state (what the repo already has)

### Electroweak and outer-horizon closure

- `DerivedGaugeAndLeptonSector.lean` builds the geometric vacuum and boson witnesses from the light-cone spine: \(T_{\mathrm{lockin}}\), outer-horizon surfaces \(S(m)=(m+1)(m+2)\), monogamy (\(\alpha,\gamma\)), triality, and adjacent-shell suppression for neutrinos.
- **No PDG literals** are imported to *define* those objects; comparison theorems to PDG centrals are separate.

### Strong / color and quark ladders (still witness-heavy)

- `QuarkMetaResonance.lean` uses the **same** detuned-area ratios (`geometricResonanceStep`, `detunedShellSurface`) as leptons, but **absolute GeV normalization** (`m_top_GeV`, legacy `m_bottom_GeV`) and **explicit readout coordinates** (`m_quark_up_*`, `m_quark_down_*`) remain calibration inputs.
- Hadrons reuse composite-trace binding at `referenceM`, but **readout placement** for flavor rungs is not derived from a variational principle in Lean.

So the honest split today: **EW closure is geometrically centralized**; **strong-sector masses still route through tables and anchors** even though the *ratio machinery* is shared.

---

## 2. Desired future state (one equation, many projections)

### Lifted dynamics

- **Full 8-component** octonionic gauge theory with the **same** \(\varphi\)-correction as in `Action.lean` / `ModifiedMaxwell.lean` / `ContinuumOmaxwellClosure.lean` (O-Maxwell + source + \(\varphi\)–\(A\) coupling).
- \(\varphi(m)\) (or its continuum avatar) **dresses all directions**; projections onto different **Fano lines / imaginary units** recover **different effective couplings**—already the narrative in `SM_GR_Unification.lean` for EM vs weak vs strong at “now.”

### Fano plane as sector selector, not only a label

- `SMEmbedding.lean`, `Generators.lean`, and related modules assign quantum numbers from octonionic structure.
- **Target:** extend that split from **static labels** to **dynamical sectors**: same EL / action, different **component restrictions** or **current channels** → EM+EW vs color+strong.

### Modes as frequencies/horizons; shells as readout

- **Target:** modal objects from the coupled O-Maxwell + \(\varphi\) + null-lattice substrate primarily set **frequencies** (Compton-like scales) and **interaction horizons** (quarter-period / phase interfaces), with natural readout indices used only as **downstream evaluation coordinates** for those readouts.
- **Heavy generations** then correspond to lower-frequency / stronger-localization modes in that coupled spectrum, while the existing `ℕ` API remains the finite chart where those evaluations are sampled today.

Existing objects such as `resonanceProduct`, `geometricResonanceStep`, and `detunedShellSurface` are then reinterpreted as **effective summaries/readouts** of that spectrum until the modal layer is fully derived.

### 2.1 Detuned surfaces as *emergent* (first-order) law (target)

Today, `FanoResonance.lean` **defines** the detuned law in closed form,
\[
  \texttt{detunedShellSurface}(m) \;=\; \frac{S(m)}{1 + \frac{\gamma}{2}\,m},
  \qquad S(m)=(m+1)(m+2),
\]
and builds `geometricResonanceStep` from **ratios** of these objects. The factor \(1 + \frac{\gamma}{2}m\) is not “wrong”—but in the **clean long-term picture** it is **not fundamental**: it is the **leading effective correction** you expect when the **fundamental** object is the full **8-component** O-Maxwell + \(\varphi\) dynamics on the octonion sector, the coupled **seven imaginaries** set up **standing waves / localization**, and you then **project** (or restrict to a resonance peak on) a **single Fano line** and expand to first order in the **readout index** \(m\) along that chart.

In that program:

- The **standing-wave / modal-frequency + horizon** story is *upstream*.
- The **Rindler denominator** is *downstream*—a convenient **emergent** two-parameter summary (\(S\), one slope tied to the monogamy split), not a separately postulated “surface law” on its own.

**Lean status:** `detunedShellSurface` remains a `def` in `FanoResonance.lean` until a theorem recharacterizes it as, e.g., the first term of a discrete expansion of a **named** mode energy or a **resonance determinant** from `EL_O` / `action_O` data on the bundle. Success would look like:  
`detunedShellSurface m = f_emergent(O_maxwell, φ, Fano_project m)` up to a proved remainder bound—or replace the def entirely by that right-hand side once the functional is in Lean.

**Proved first-order packaging (not spectral emergence):** `Hqiv/Physics/FanoDetuningFirstOrder.lean` proves the closed form is **first-order affine** in the shell index with slope \(\gamma/2\), rewrites `detunedShellSurface` as \(S(m)/(1+(\gamma/2)m)\), and wires the named hook `omaxwellFanoDetuning1Jet` to the direct spectral source `spectralFanoRindler1Jet` on a canonical incidence line. The conditional `FanoOmaxwell_detuning1Jet_eq_spectralFanoRindlerLimit` is still kept as the reusable emergence interface: *if* a candidate 1-jet agrees with that hook on every natural shell, *then* it is forced to the same affine law on those points.

`QuarkOMaxwellBridge.lean` remains valid as the **structural** link to \((\alpha,\gamma)\) and O-Maxwell; it does **not** assert full emergence—it only says what the code **currently** implements.

**New interface layer:** `Hqiv/Physics/ModalFrequencyHorizon.lean` now packages a modal-first
object (`ModalFrequencyHorizonSpec`) with:
- nominal angular frequency,
- interaction horizon quarter-period relation (`ω·Δt_quarter = horizonQuarterPeriod`),
- detuning 1-jet map.

It provides constructors from shell-nominal self-clock frequencies, direct Fano spectral source,
and Compton parameters. This is the active bridge for consuming modules that should speak
frequency/horizon first while preserving existing shell formulas as readouts.

### 2.2 Constant term `1` from triality + Fano (research sketch; Lean scaffold)

**Narrative (not yet a Spin(8) theorem in Lean):** the affine denominator `1 + \frac{\gamma}{2}m` splits into a **constant** and a **slope**. The slope \(\gamma/2\) is already packaged with monogamy in `FanoDetuningFirstOrder.lean`. The **constant `1`** is the piece that should come from **octonionic bookkeeping**: projecting the coupled dynamics onto a **single Fano line** (a \(2\)-dimensional split inside \(\mathbb{O}\)) and requiring **compatibility with the triality automorphism** that cycles the three \(8\)-dimensional irreps (`Hqiv.Algebra.Triality`). The intended argument is that any **non-unit** additive constant in the normalized projected denominator would fail to be **triality-equivariant** across cycled lines—so the unique invariant normalization fixes the leading term to \(1\), in the same spirit as Lorentz invariance fixing Minkowski normalization (informal analogy only).

**Lean scaffold:** `Hqiv/Physics/FanoTrialityDetuningScaffold.lean` now routes `trialityProjectedDenominator line m` through the direct spectral layer in `Hqiv/Physics/FanoOmaxwellSpectrum.lean` (`trialityProjectedDenominator L m := spectralFanoRindler1Jet L m`) and proves `detunedShellSurface_eq_shell_div_trialityProjectedDenominator`, `trialityProjectedDenominator_stub_eq_affine_shell`, `trialityProjectedDenominator_firstOrder`, and `trialityProjected_denominator_at_shell_zero_eq_one`. Public tags are incidence-driven (`FanoLineTag = FanoVertex`, `FanoLine.ofTag` chooses a canonical incident line). The **hard** part—deriving the same constant `1` from `Triality.lean` equivariance plus explicit Fano-line projection constraints rather than from the current normalization scaffold—is still **explicitly open**.

### 2.3 Three hypercharge paths over one well (scaffold)

`Hqiv/Physics/HyperchargePathBarrierScaffold.lean` formalizes the "single well, three path complexities"
picture in minimal Lean form:

- `HyperchargePath = {straight, plusTurn, minusTwoTurn}` with labels `{0, +1, -1}`,
- `universalDetunedWell m := detunedShellSurface m`,
- `hyperchargePathBarrier line m path = base + turns(path) * increment(line,m)`.

The scaffold now exposes a `Δ`-facing interface object `DeltaTurnIncrementModel` with active map
`deltaTurnIncrement`; this is the designated replacement point for a future algebraic derivation.
In the current instance, `deltaTurnIncrement line m` is set equal to the same projected detuned well
(`shellSurface m / trialityProjectedDenominator line m`), so the expected ordering
`straight < plusTurn < minusTwoTurn` is **proved** for every shell and line tag. This gives a
formal placeholder for the "turn-complexity hierarchy" while keeping the unresolved physics explicit:
the increment and line-dependence are **not yet** derived from explicit `Δ`/triality/Fano structure.

### 2.4 Triality-vs-rapidity well check (equivalence scaffold)

`Hqiv/Physics/TrialityRapidityWellEquivalence.lean` now provides an explicit comparison harness:

- `trialityRepTurnIncrement line rep m` (triality-indexed view; currently rep-neutral),
- `rapidityLiftedDenominator m := 1 + (γ/4) * (phi_of_shell m - phiTemperatureCoeff)`,
- `rapidityLiftedWell m := shellSurface m / rapidityLiftedDenominator m`.

Using `phi_of_shell m = 2(m+1)`, the rapidity denominator is proved equal to
`1 + (γ/2)m`, and then to `trialityProjectedDenominator line m` for all line tags. The resulting
residual
`trialityRapidityWellResidual line rep m = trialityRepTurnIncrement line rep m - rapidityLiftedWell m`
is proved exactly `0`, so "near equivalence" holds at any nonnegative tolerance as a corollary.

Interpretation: in the **current scaffold**, triality-indexed and rapidity-written wells are not merely
close; they are definitionally/algebraically aligned. The open research step is still to replace the
rep-neutral map by a nontrivial `Δ`/triality/Fano-derived increment and re-run the same residual test.

`TrialityRapidityWellEquivalence.lean` now also includes that replacement candidate:

- `rapidityCPBias m := omega_k_at_horizon m m_lockin - 1` from `Baryogenesis.lean` (same lockin/curvature channel, no fitted `eta_paper` anchor),
- triality orientation weights on the three irreps: `8v ↦ 0`, `8s⁺ ↦ +1`, `8s⁻ ↦ -1`,
- `cpSensitiveTrialityIncrement line rep m := baseline * (1 + rapidityCPBias m * orientation rep)`.

This yields a **rep-sensitive** residual formula
`cpSensitiveTrialityRapidityResidual = baseline * rapidityCPBias * orientation`.
So the vector channel remains exactly aligned (`= 0` residual), spinor channels are opposite-sign
deviations, and the three-rep average returns the rapidity well exactly. A bound theorem ties
near-equivalence directly to the baryogenesis bias magnitude.

---

## 3. Interface sketch (how to wire Lean without big-bang refactor)

1. **Lepton precedent:** `LeptonGenerationLockin.lean` already separates `OuterHorizonLeptonShellSelection` (interface) from provisional exact-shell witnesses. The physical endgame there is **support bands**, not necessarily one integer per generation.
2. **Color analogue:** introduce a parallel interface—call it `InnerMetaColorShellSelection` or similar—whose fields are **either** exact shells **or** bands / predicates on \(m\), eventually constrained by a **single variational principle** (action cell, Rayleigh quotient, or discrete dispersion relation).
3. **Quark module:** `QuarkMetaResonance` should eventually **import** shell data only through that interface, with theorems of the form “this witness satisfies the Euler–Lagrange / dispersion inequality” rather than “we assert these naturals.”
4. **Single dimensionful bridge:** long-term goal remains one overall mass unit (e.g. Planck-normalized \(\tau\) scale) with **top GeV** as a **theorem** from geometry + conversion, not a second axiom—see `MASS_DERIVATION_ROADMAP.md` milestones.

---

## 4. Honest gap (what is *not* proved)

The gap is **not** “we forgot quarks.” The gap is **modal calculus**:

> Until masses and interaction horizons are **characterized** from the **full** coupled O-Maxwell + octonion + lattice problem, current shell ladders and GeV anchors remain **witness/readout scaffolds**.

That is a **genuine research direction**: PDE / discrete spectral theory on a deliberately minimal HQIV scaffold, not a small refactor.

---

## 5. Pointers into the codebase

| Topic | Lean / docs |
|--------|----------------|
| O-Maxwell + \(\varphi\) | `Hqiv/Physics/Action.lean`, `ModifiedMaxwell.lean`, `ContinuumOmaxwellClosure.lean` |
| Modal frequency/horizon interface (modal-first packaging) | `Hqiv/Physics/ModalFrequencyHorizon.lean`, `ComptonHorizonPhase.lean`, `SurfaceWaveSelfClock.lean` |
| Fano / SM embedding | `Hqiv/Algebra/SMEmbedding.lean`, `HqivGenerators/Hqiv/Generators.lean` |
| EW vs strong narrative | `Hqiv/Physics/SM_GR_Unification.lean` (doc blocks on Fano + O-Maxwell) |
| Lepton shell interface | `Hqiv/Physics/LeptonGenerationLockin.lean` |
| Quark ladder + honesty | `Hqiv/Physics/QuarkMetaResonance.lean` |
| Quark ↔ O-Maxwell **proved** spine (Fano vertices, `geometricResonanceStep`, `α`/`γ` split) | `Hqiv/Physics/QuarkOMaxwellBridge.lean` |
| Direct Fano-projected spectral denominator source (`Δ` selector + 1-jet) | `Hqiv/Physics/FanoOmaxwellSpectrum.lean` |
| Mass milestone table | `AGENTS/MASS_DERIVATION_ROADMAP.md` |
| Survey note (PDF) | `papers/hqiv_lean_from_combinatorics_to_mass_spectrum.tex` |

---

## 6. Success criterion (for closing this design note)

Treat the program as **done enough to archive this note into “achieved partial”** when:

1. At least one **color or quark** mass/horizon readout is proved to arise from a closed modal functional built only from O-Maxwell + lattice + Fano data; **or**
2. A **dispersion relation** on the discrete lattice is proved whose solutions force the documented readout ladder (shell/band table then becomes **certified output**, not input).

Until then, keep the split visible: **geometry-first EW**, **table-assisted strong**, **roadmap** tracks shrinkage of anchors.
