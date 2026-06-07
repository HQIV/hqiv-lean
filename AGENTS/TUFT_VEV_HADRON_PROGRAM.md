# Vev-pinned hadrons + inline Beltrami excitations

**Status:** Phase 1 scaffold landed (Lean + Python eval).  
**Parent synthesis:** [`TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md`](./TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md)

---

## Goal

Move the hadronic mass chart off the static `referenceM` / `derivedProtonMass` export pin and onto the same **`T → vev → Λ_Hopf → mass`** chain that closes charged leptons — with **excited states inline** on that dynamic ground.

| Layer | Legacy (export pin) | Primary (vev-pinned) |
|-------|---------------------|----------------------|
| Baryon ground | `derivedProtonMass` | `tuftHadronGroundAtXi_MeV ξ` |
| Excitation | `metaHorizonExcitedMassReadout n ℓ` | `tuftHadronExcitedMassAtXi_MeV ξ n ℓ` |
| Vector meson | `mesonVectorExcitedMassReadout` | `tuftMesonVectorMassAtXi_MeV ξ` |
| Shell index | `referenceM + n + ℓ` (HQIV legacy catalog) | **`tuftHadronModeShell n ℓ`** = `tuftHeavyChartShell + n + ℓ` |

At `ξ = ξ_lock` the new readouts **provably match** the legacy catalog when pins align
(`totalModeShell_eq_tuftHadronModeShell`). See [`TUFT_SHELL_ONTOLOGY.md`](./TUFT_SHELL_ONTOLOGY.md).

---

## Mechanism (Phase 1)

### Ground

```lean
tuftProtonToTauPinAtLockin :=
  derivedProtonMass / tuftLeptonMassFromVevAtXi_MeV xiLockin 3

tuftHadronGroundAtXi_MeV ξ :=
  tuftLeptonMassFromVevAtXi_MeV ξ 3 * tuftProtonToTauPinAtLockin
```

All ξ dependence flows through the τ mass on the vev chain. The single dimensionless pin `proton/τ` at lock-in is the **only** calibration constant (eventually to be derived from strong/heavy chart ratio × baryon content, not imported PDG).

### Inline excitations

Beltrami radial + sector-Gaussian orbital increments are applied **directly to the vev ground**:

```lean
tuftHadronBeltramiRadialDeltaAtXi ξ n :=
  (tuftHadronGroundAtXi_MeV ξ / derivedProtonMass) * radialExcitationDeltaOperational n

tuftHadronExcitedMassAtXi_MeV ξ n ℓ :=
  tuftHadronGroundAtXi_MeV ξ
    + tuftHadronBeltramiRadialDeltaAtXi ξ n
    + tuftHadronBeltramiOrbitalDeltaAtXi ξ ℓ
```

The operational ratios use `tuftHeavyChartShell` (= `referenceM` numerically today).

### Mesons

Strong-chart vector ground on the vev ladder:

```lean
tuftMesonVectorGroundAtXi_MeV ξ :=
  tuftHadronGroundAtXi_MeV ξ * (3/4)   -- tuftStrongChartShell / tuftHeavyChartShell
```

---

## Python mirror

`scripts/hqiv_tuft_quark_vev.py` — six-flavor spectrum from τ pin + `QuarkMetaResonance` shell ratios.

`scripts/hqiv_tuft_mass_spectrum_pdg_eval.py` (sectioned printout):

- `tuft_hadron_ground_at_xi_mev` / `tuft_hadron_excited_mass_at_xi_mev`
- `tuft_meson_vector_mass_at_xi_mev` / `tuft_meson_excited_mass_at_xi_mev`
- `tuft_quark_spectrum_at_xi_mev` — **t, c, u, b, s, d**

Sections: leptons → neutrinos → **quark family** → baryon ground → **baryon excited grid** → **meson excited grid** → diagnostics.

### Global excitation correction (Phase 1b)

Keep vev ground; apply one factor **only to the Beltrami increment**:

```lean
tuftHadronExcitedMassWithGlobalCorrectionAtXi_MeV ξ n ℓ :=
  g(ξ) + (g(ξ)/g₀) · Δ_lockin(n,ℓ) · G(ξ,n,ℓ)

G(ξ,n,ℓ) := metaHorizonExcitedChannelTwistAtEpoch ξ n ℓ
             / metaHorizonExcitedChannelTwistAtEpoch ξ_lock n ℓ   -- = 1 at lock-in
```

Lean: `HopfShellBeltramiMassBridge.lean` (`tuftHadronExcitedMassWithGlobalCorrectionAtXi_MeV`)  
Python: `scripts/hqiv_hadron_global_excitation.py`

The legacy `hadronWholeS7IjkDressing` multiplies the **full** mass and overshoots; the global
form applies correction **only to the increment** and is pinned to unity at lock-in (matches vev inline).

### Unified inside closure (Phase 2 — primary global)

Algebraic merge of vev ground + trapped inside ratio + epoch twist:

```lean
tuftHadronExcitedMassUnifiedInsideAtXi_MeV ξ n ℓ :=
  g(ξ) · [ 1 + (R_in(m) − 1) · G_twist(ξ,n,ℓ) ]
```

At `ξ = ξ_lock`, `G_twist = 1`: `m = g(ξ_lock) · R_in(m)` — matches trapped readout with vev pin.
Lean: `HopfShellBeltramiMassBridge.lean` · Python: `hqiv_hadron_global_excitation.py` ·
Benchmark: `scripts/hqiv_hadron_unified_pdg_benchmark.py`

**Phase refinement** (`tuftHadronExcitedMassUnifiedPhaseAtXi_MeV`): `R_in_interp(m_eff)` with
`m_eff = totalModeShell − Σ 1/(4ξ_j)` (Compton quarter-leak).  Δ(1232) on P-wave `(0,1)` → ~100.5%.

**Split refinement** (Python only): invert radial/orbital Beltrami increments separately on the
trapped curve (`ξ_split`); breaks `n` vs `ℓ` degeneracy.  Best median |residual| ~3.8% on nucleon PDG set.

**Still open:** principled `(n,ℓ)` assignment from spin-parity (not per-state search); Lean split inversion.

---

## Relation to `MetaHorizonExcitedXiScale`

`MetaHorizonExcitedXiScale.lean` already scales `derivedProtonMass` by `heavy_lepton_gap_at_xi` and adds **curvature × detuning twist** on excited channels. That module is complementary:

| Module | Ground source | Excitation twist |
|--------|---------------|------------------|
| `tuftHadronExcitedMassAtXi_MeV` | vev → τ × pin | inline Beltrami on heavy chart |
| `metaHorizonExcitedBaryonMassAtXi` | `derivedProtonMass × gap(ξ)/gap(5)` | channel ξ + Fano jet twist |

**Phase 2:** merge twists into the vev-pinned tower; replace `tuftProtonToTauPinAtLockin` with a pure geometry ratio (strong-shell Beltrami scalar, no `derivedProtonMass` in the pin).

---

## Phase roadmap

1. **Done:** Lean defs + lock-in catalog bridge + Python eval primary rows.
2. **Done (research):** `HadronS7ConfinementReadout` — whole-hadron `S⁷` + `f^{ijk}` dressing on TUFT vev base.
3. **Next:** Derive `tuftProtonToTauPinAtLockin` from geometry (strong/heavy chart × baryon composite trace).
4. **Next:** Prove confinement binding = closed `f^{ijk}` triple budget (not independent gluon DOF) in Lean certificate.
5. **Next:** Replace per-quark `S⁷` pole descent in excited spacing with whole-hadron envelope as primary.
6. **Import-cycle fix:** wire `hadronWholeS7IjkDressing` directly to `tuftHadronExcitedMassAtXi_MeV` in Lean (split minimal TUFT hadron module out of `HopfShellBeltramiMassBridge` ↔ `FanoSectorSpectralMassEmergence` cycle).

---

## Confinement + whole-hadron S⁷ thesis (2026)

| Old split | Target |
|-----------|--------|
| Quark masses from per-quark `S⁷` pole descent | Quark **ratios** from resonance ladder; **absolute** scale from TUFT vev |
| Radial excitations from `S⁴` Beltrami drum only | **`S⁷` Laplace on combined index `n+ℓ`** on the whole hadron wavefunction |
| Confinement as fitted binding / gluon shorthand | Confinement as **`f^{ijk}` antisymmetric triple budget** × composite trace (`HadronMassReadout`) |

Lean: `Hqiv/Physics/HadronS7ConfinementReadout.lean`  
Python: `scripts/hqiv_tuft_hadron_s7_confinement.py`  
Printout section: **Baryon S⁷ whole-envelope + f^{ijk} confinement (TUFT base)**

---

## Verify

```bash
lake env lean Hqiv/Physics/HopfShellBeltramiMassBridge.lean
python3 scripts/hqiv_tuft_mass_spectrum_pdg_eval.py
```
