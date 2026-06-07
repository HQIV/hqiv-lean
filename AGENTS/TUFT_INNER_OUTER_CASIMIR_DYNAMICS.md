# Inner/Outer Casimir Dynamics: Dynamic Mass Spectrum from Geometry

**Core claim (HQIV Lean, 2026):**

The overall mass scale (effective vev) at any cosmic temperature is not a fixed external input. It is the instantaneous balance between **inner trapped-Casimir** (T12 Hopf contact shells) and **outer Casimir suppression** (T13 fluctuations on the neutral singlet extension of the same 8+8 carrier).

This inside/outside asymmetry on one carrier is the symmetry-breaking mechanism. The charged-lepton spectrum — absolute scale + generation ratios + temperature dependence — is read out from that balance plus the TUFT Hopf/Beltrami determinant scalar on the heavy winding sector.

**Single source of truth for TUFT mining history:** [`TUFT_HOPF_SPECTRAL_MINING.md`](./TUFT_HOPF_SPECTRAL_MINING.md) (T1–T13 milestones). This file is the **current synthesis + accuracy audit + fix tracker**.

---

## 0. Critical convention: `referenceM = 4` is **not derived**

`referenceM` in `OctonionicLightCone.lean` is **fixed by two bookkeeping pins**:

```lean
def referenceM : Nat := qcdShell + stepsFromQCDToLockin   -- currently 1 + 3 = 4
```

That is a **calibration and export convention** on the discrete null-lattice grid. It names which row is used for hadronic network formulas, Ω_k partial normalization, and proton MeV export. It is **not** the output of a deeper numeric search or a TUFT Hopf-winding theorem inside this module.

**Do not conflate:**

| Object | Meaning | Currently evaluates to |
|--------|---------|------------------------|
| `referenceM` | HQIV hadronic / QCD-onset **export pin** on the null-lattice grid | `4` |
| `tuftHeavyChartShell` | TUFT lock-in chart sample `m = n + 1` for heavy Hopf winding `n = 3` | `4` |
| `tuftWeakHopfShellIndex` | TUFT weak-sector Hopf label `n = 1` | `1` |
| `xiLockin = xiOfShell referenceM` | HQIV lock-in coordinate on the ξ ladder | `5` |

Lean proves `referenceM = tuftHeavyChartShell` **as a numeric coincidence** under the current pins (`referenceM_eq_tuftHeavyChartShell_numeric` in `HopfShellBeltramiMassBridge.lean`). That equality is **not** a chart identification: hadronic binding stays on `referenceM`; lepton/TUFT/κ₆ lapse readouts use `tuftHeavyChartShell`.

Changing `qcdShell` or `latticeStepCount` moves `referenceM` without moving the TUFT Hopf chart. The theory must remain honest when those numerals diverge.

---

## 1. The mechanism

- **Inner surfaces** (T12 three integrable Hopf shells, contact-Beltrami + phase-lift torsion): trapped zero-point / Casimir energy → binding and heavy stabilization gap.
- **Outer surface** (T13 outer-shell fluctuations, mode count 140): lattice **witness** for neutral suppression arithmetic. The coarse factor `1/140` is proved as shell bookkeeping (`outerHorizonNeutrinoSuppression_eq_inv_140`); it is **not** a validated neutrino mass prediction (see §2 audit — same retired class as legacy lepton quotients). TUFT-dressed readouts (`m_nu_e_at_xi`) remain diagnostic until a genuine S⁹ / PMNS derivation exists.

```lean
noncomputable def effective_casimir_scale_at_xi (ξ : ℝ) : ℝ :=
  let inner := trappingSelectionFromHeavyHopfShellWithAlpha
    (Hqiv.Topology.HopfShell.curvatureImprintAlpha t12_heavy_shell)
    (c := omegaK_xi ξ)
  let outer := t13_outer_suppression_at_xi ξ
  inner / outer
```

Dynamic heavy gap (normalized at ξ_lock):

```lean
heavy_lepton_gap_at_xi ξ =
  (4/5) * (ξ/5) * (effective_casimir_scale_at_xi ξ / effective_casimir_scale_at_xi 5)
```

Physical charged-lepton MeV chart:

```lean
Λ_Hopf = sqrt(2π) * v(ξ) * κ₆(ξ)
m_n(ξ) = Λ_Hopf * tuftLeptonGeometricScalar n
```

where `κ₆` lapse concentration is evaluated on **`tuftHeavyChartShell`**, not `referenceM`.

---

## 2. PDG accuracy audit (ξ_lock = 5, May 2026)

Reproduce: `python3 scripts/hqiv_tuft_mass_spectrum_pdg_eval.py`

| Observable | Model/PDG | Status |
|------------|-----------|--------|
| τ (T8 full @ ξ_lock) | 1.000 | **Calibration** (vev + κ₆ anchor) |
| μ (T8 full) | **0.999** | **Closed** — `tuftSectorZetaSubleadingCoeff` |
| e (T8 full) | **0.998** | **Closed** — electron uses `γ/(2·d_n²)` not `1/4π` |
| μ/e (leading T8 only) | 1.015 / 1.018 | Diagnostic — missing generation-indexed subleading |
| proton (derived) | 1.000 | **Hadronic convention** at `referenceM` |
| Δ(1232) trapped Planck | 1.00–1.02 | Best hadronic readout layer |
| Δ(1232) meta-horizon operational | 1.066 | Catalog layer overshoot |
| N(1520) meta-horizon | 1.05–1.16 | Worse at higher radial n |
| ρ vector (strong-chart ℓ=1) | ~1.14 | TUFT strong/heavy chart ratio |
| ρ vector (legacy ½m_p) | 0.76 | **Retired** diagnostic |
| legacy μ shell quotient | 7.3× | **Retired** — proved ≠ TUFT Beltrami chart |
| legacy e shell quotient | 842× | **Retired** |
| Σm_ν TUFT outer-T8 @ ξ_lock | ~0.007 eV ≪ caps | **Pass** — m > 0, Σm ≪ 0.12 eV and ≪ ~6 eV; not a precision target |
| Δm²21 TUFT holonomy split | vs oscillation ref | **Diagnostic** — hierarchy shape; PMNS phases open |
| ν_e (`1/140 · M_Z` witness) | ~3×10⁸× vs cosmology | **Retired** — same class as legacy lepton quotients |
| ν_μ/ν_e, ν_τ/ν_μ (`(1/140)^n` ladder) | inverted hierarchy | **Retired** — not PMNS / not observed ordering |
| lepton-seeded “TUFT tower” | 2.0–2.9× | **Misleading for hadrons** — see §4 |
| $W$ (`tuftMW_atXi_GeV` @ ξ_lock) | **0.998** | **Closed** — closure × vev bridge × heavy-gap |
| $Z$ (`tuftMZ_atXi_GeV` geometric) | **1.004** | **Closed** — $W/\cos\theta_W$, not naive $g_{\mathrm{SU2}}+g_{\mathrm{U1}}$ |
| $H$ (`tuftMH_atXi_GeV` primary) | **1.003** | **Closed** — $\sqrt{2\lambda}\,v$ + $\gamma\cdot(1/\Theta_{\mathrm{local}})$ |
| $Z$ naive $(g_{\mathrm{SU2}}+g_{\mathrm{U1}})$ | 1.204 | **Retired** diagnostic |
| $H$ scalar closure $2v_{\mathrm{scalar}}$ | 0.940 | **Retired** diagnostic |

Reproduce EW bosons: `python3 scripts/hqiv_tuft_electroweak_boson_readout.py`  
Lean: `Hqiv/Physics/TuftElectroweakBosonReadout.lean`

---

## 3. Known structural gaps vs Nielsen TUFT

### 3.1 Two incompatible lepton ratio charts (proved)

| Chart | τ/μ step | μ/e step | Shells |
|-------|----------|----------|--------|
| HQIV legacy `resonance_k_*` | 175/76 | 4484/2499 | m = 33, 58 (distant ladder) |
| TUFT Beltrami winding | 4/3 | 3/2 | Hopf n = 3→2, 2→1 |
| TUFT determinant scalar | ~1.015× PDG | ~1.018× PDG | heavy winding n = 3 |

Lean proves the legacy factors ≠ Beltrami ratios ≠ holonomy vertex ratios (`LeptonResonanceChartComposite.lean`). The **executable** lepton chart uses the TUFT Beltrami scalar, not the legacy shell quotient.

The **outer neutrino suppression `1/140`** belongs in the same retired bucket. It is a proved lattice identity (`outerHorizonNeutrinoSuppression_eq_inv_140`: `γ / S(referenceM+2)` with mode-count bookkeeping), not a neutrino mass prediction. With witness `M_Z_derived ≈ 5.49 GeV`, the derived ladder gives `m_νe ≈ 39 MeV` — roughly **10⁸× above** the cosmological `<0.12 eV` bound. Repeated `(1/140)` steps produce **ν_τ < ν_μ < ν_e**, the opposite of the normal mass ordering. The TUFT-scaled readout `m_nu_e_at_xi` (multiply by `κ₆`) can land near eV-scale only by importing the baryogenesis matter fraction `η`; that is a separate normalization pin, not a derived absolute neutrino mass.

### 3.2 Not yet imported from TUFT

- ~~Full Ray–Singer / ζ(3) sector determinant (T8 has leading term only)~~ → **T8 leading + `(1/4π)·Δτ` subleading landed** (`FanoSectorSpectralMassEmergence.lean`: `hopfShellT8TorsionSubleading`, `leptonMassSpectrum_at_xi_from_vev_T8_MeV`). Higher orders / electron-specific phase still open.
- Single Fermi-constant / vev derivation (HQIV inputs electroweak vev)
- CKM/PMNS from admissible-cycle overlaps (T10 scaffold only)
- Per-shell α_n proved equal to `alphaEffAtShell` (Hopf trapping **derives** binding coupling shell-by-shell — still open; structural factorization is in `TrappedCasimirBindingBridge.lean`)

### 3.3 Normalization vs prediction

- τ exact at lock-in is **by construction** (vev + κ₆ chosen once)
- Lock-in dynamic scale is **normalized** to recover legacy heavy gap 4/5
- Away from lock-in, scale runs ~183× at CMB — geometry-driven but **unvalidated** against observation

### 3.4 Beltrami label caveat

TUFT fundamental coexact λ₁ = 2; Peter–Weyl ℓ = 1 gives 3. Both labels are kept; no silent identification.

---

## 4. Ontology fixes (2026-05-31)

### 4.1 Hadronic vs lepton excited towers — **separated**

**Wrong (retired for PDG comparison):** `tuftExcitedHeavyMassAtXi` scales the meta-horizon baryon tower from the **lepton heavy ground** → 2–3× overshoot vs Δ, ρ.

**Correct for hadrons:** `tuftExcitedBaryonMassReadout n ℓ = metaHorizonExcitedMassReadout n ℓ` — proton-ground catalog, no lepton seeding.

**Correct for leptons:** `tuftExcitedHeavyMassAtXi` remains the lepton-sector bridge (dynamic τ-scale + meta-horizon increment shape).

### 4.2 κ₆ lapse row — **decoupled from `referenceM`**

`tuftLapseConcentrationAtXi` now evaluates Rindler detuning on `tuftHeavyChartShell` (TUFT heavy winding chart), not `referenceM`. Numerically both are 4 today; the API no longer encodes a false derivation link.

### 4.4 Strong-chart vector meson readout (2026-05-31)

Replaced the deprecated `0.5 · m_p` meson anchor with a TUFT chart ratio:

`mesonVectorGroundAnchor = m_p · (tuftStrongChartShell / tuftHeavyChartShell) = 3/4 · m_p`

Vector excitation uses the same scaled orbital ℓ = 1 step (`mesonVectorExcitedMassReadout`).
PDG ρ ratio improves from **0.76×** (half-proton) to **~1.14×** (strong-chart).
Still open: full strong-sector trapped-planck or T8 determinant on the quark–antiquark channel.

### 4.3 Trapped Casimir ↔ binding coupling — **structural layer landed**

`TrappedCasimirBindingBridge.lean` proves the binding cell factorizes as trapped zero-point × normalized SO(8) selection:

- `normalizedSO8TraceSelection m c = alphaEffAtShell m c / casimirPerModeZeroPoint m`
- `trappedCasimirCouplingCell_eq_alphaEffAtShell`
- `bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection`
- `T11T12TrappedCasimirWitness` + heavy-chart witness at shell 4
- `heavyHopfTorsionCoefficient_gt_outerHorizonNeutrinoSuppression` (T11 contact > T13 outer **witness** — ordering only; does not validate `1/140` as a neutrino mass)

**Still open:** proving `hopfTrappedSelectionFromShell` (T11/T12 contact amplification) equals `normalizedSO8TraceSelection` / `alphaEffAtShell/(φ/2)` on each shell — that would close the “no independent gluon” reading. Today the identification is structural + witness at the heavy chart, not a shell-by-shell derivation from Hopf data.

---

## 5. Key Lean entry points

| File | Role |
|------|------|
| `FanoSectorSpectralMassEmergence.lean` | T8 leading + full (`tuftSectorZetaDetFullWeight`, `leptonMassSpectrum_at_xi_from_vev_T8_MeV`) |
| `TrappedCasimirBindingBridge.lean` | Trapped Casimir ↔ `alphaEffAtShell` factorization, T11/T12 witness |
| `HopfShellBeltramiMassBridge.lean` | Dynamic scale, κ₆, vev–Hopf lepton chart, **vev-pinned hadrons** (`tuftHadronExcitedMassAtXi_MeV`) |
| `LeptonResonanceChartComposite.lean` | Proved chart separation |
| `MetaHorizonExcitedStates.lean` | Proton-ground baryon/meson catalog |
| `MetaHorizonTrappedPlanckMass.lean` | Best Δ(1232) readout (~1%) |
| `ContinuousXiPath.lean` | ξ ladder, `omegaK_xi` |
| `HopfShellComplex.lean` | T12 witness, per-shell imprints |
| `OctonionicLightCone.lean` | `referenceM` convention (not derived) |

---

## 6. Open fix targets (priority order)

1. ~~**T8 full sector determinant** — close μ/e ~2% gap~~ → **Charged leptons closed** via generation-indexed `tuftSectorZetaSubleadingCoeff` (`1/4π` for `n≥2`, `γ/(2d_n²)` for electron). Primary chart: `leptonMassSpectrum_at_xi_from_vev_T8_MeV`.
2. **Hopf → alphaEffAtShell** — prove `hopfTrappedSelectionFromShell` reproduces `normalizedSO8TraceSelection` shell-by-shell (structural bridge landed in `TrappedCasimirBindingBridge.lean`)
3. **Neutrino absolute scale + hierarchy** — outer T8 anchor + T10 `middleToLight=3` on ν₁–ν₂ split. Lean: `neutrinoMassSpectrum_at_xi_from_T10_MeV`, `assembleT10PMNSMixingReadout`, `t10NeutrinoOverlapMatrix`, `t10PMNSUnitaryReal`. **Absolute scale passes caps** (Σm_ν ~0.007 eV). T10 steepens oscillation Δm²21 diagnostic (~0.08× lab ref vs ~0.06× bare holonomy). **Closed:** holonomy×torsion bridge, PMNS θ₁₂/θ₂₃ from phase ratios, δ=π/5, witness export uses TUFT T10 masses (retired `m_nu_e_derived` from JSON).
4. ~~**Meson readout**~~ — strong-chart anchor landed (`mesonVectorExcitedMassReadout`); refine with trapped-planck on strong shell
4b. **Vev-pinned hadrons + inline excitations** — Phase 1 landed: `tuftHadronGroundAtXi_MeV`, `tuftHadronExcitedMassAtXi_MeV`, `tuftMesonVectorMassAtXi_MeV` (see [`TUFT_VEV_HADRON_PROGRAM.md`](./TUFT_VEV_HADRON_PROGRAM.md)). **Next:** geometry-only proton/τ pin; decouple excitation shell from `referenceM`.
5. **Remove external vev input** — derive scale from single TUFT/Fermi channel once κ₆ closure is complete
6. **Per-imprint α_n** — wire T12 witness alphas into `leptonMassSpectrum_at_xi_lepton_optimized` with proved effect
7. **Theorem layer** — positivity / monotonicity of `effective_casimir_scale_at_xi`; make computable where possible

---

## 7. Temperature behavior (reference)

At ξ = 5 (lock-in): `effective_casimir_scale` multiplier = 1.0 by construction; heavy gap = 4/5.

At CMB (ξ ≈ 5.2×10³¹): `omegaK_xi` ≈ 701; dynamic scale multiplier vs lock-in ≈ **183.5**.

At ξ = 1: multiplier ≈ 0.74; smaller splittings.

Physical-T API: `heavy_lepton_gap_at_physical_T_MeV`, `leptonMassSpectrum_at_physical_T_MeV`, `xi_for_target_heavy_mass`.

---

## 8. Ecosystem split (post-audit)

1. **Hadronic export (stays on `referenceM`):** `CosmologicalShellLadder`, `ConservedContentMassBridge`, `QuarkMetaResonance`, `DerivedNucleonMass`, nucleon binding networks.
2. **Lepton / gauge / neutral (TUFT dynamic chart):** `HopfShellBeltramiMassBridge` vev–κ₆ path, T12/T13 Casimir balance, `ModalFrequencyHorizon` T13 witness.

Both lake targets (`HQIVLEAN`, `HQIVPhysics`) should remain green after chart decoupling changes.

---

## 9. Related work

- **BBN dynamic C₂ lab:** inverse lapse clock `(κ₆_ref/κ₆)^w` — `DynamicBBNBaryogenesis`
- **Post-α binding:** sphere-touching on α compound surface — `HQIVNuclei`, `hqiv_post_alpha_sphere_touching.py`
- **Paper table:** `papers/tuft_sm_lagrangian/hqiv_tuft_sm_lagrangian_synthesis.tex` § PDG comparison
