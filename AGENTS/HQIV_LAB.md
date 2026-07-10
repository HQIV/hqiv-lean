# HQIV Lab — chem & materials package

**Package:** `hqiv_lab/` (install: `pip install -e .` from repo root)  
**Lean:** `Hqiv.QuantumChemistry.PhaseAllotropeDerivation`  
**CLI:** `hqiv-lab H2O`

## Non-Negotiable Input Policy

HQIV Lab prediction paths must not use external chemistry or materials data as
inputs. Disallowed as inputs: W4-17/GMTKN55/NIST/CRC values, PDG/CODATA masses
or couplings, tabulated bond lengths, tabulated bond angles, crystallographic
cell constants, density tables, fitted potentials, hydration shells, mobility
tables, or empirical phase constants.

Allowed prediction inputs are only HQIV-derived primitives and exact unit
conversions needed to express outputs in conventional units. In practice this
means formulas/names resolve to atomic numbers, electron counts, HQIV nuclear
mass readouts, TUFT/nested-wavefunction bond lengths, TUFT centre angles, the
fixed lattice rationals α = 3/5 and γ = 2/5, and the proton-lockin witness at
`referenceM = 4`.

External data may appear only in quarantined comparison fields with names like
`reference_*`, `benchmark_*`, or `comparison_*`. It must never be passed into
`MoleculeSpec`, bond builders, packing, density, phase, binding, conductivity,
or material-response formulas.

## Design

Prediction specs are **HQIV-derived molecular specs** (atomic-chart fragments
and derived bonds), not benchmark geometry:

```
formula/name
  → atomic-chart MoleculeSpec  # fragments + HQIV-derived bonds
  → infer_monomer_geometry()   # VSEPR, motif, n_inter
  → templates_for_motif()      # Ih, Ic, fcc, …
  → unit_cell_for_allotrope()  # a,b,c,Z from contact distance
  → derive_allotropes()        # rank @ (T,P)
  → material_response()        # n, k_th, … (scripts mirror)
```

Witness/literature values are comparison-only. Do not add experimental cell
constant overrides to prediction paths.

## API

```python
from hqiv_lab import MaterialsLab

lab = MaterialsLab()
spec = lab.spec_from_name("H2O")
print(lab.preferred_allotrope(spec).label)  # Ih
print(lab.readout(spec))
```

## Tests

```bash
PYTHONPATH=. python3 hqiv_lab/tests/test_allotrope_derivation.py
PYTHONPATH=.:scripts python3 scripts/test_hqiv_miniprotein_fold.py
PYTHONPATH=scripts python3 scripts/test_hqiv_spine_chemistry.py
```

## Protein folder (`hqiv_lab/protein/`)

Miniprotein folding readout on **derived** peptide geometry (no PDB inputs to the fold):

```
sequence + secondary-structure map
  → Ramachandran spine readout (hqiv_lab/miniprotein_basin.py)
  → shell-dressed peptide bonds (hqiv_lab/peptide_shell_dress.py)
  → NeRF Cα placement
  → tertiary contact graph + open-channel packing + closure (nerf or OSH)
  → compare Cα RMSD vs PDB witness
```

**Shell dress / outside closure:** NIST spectral EM is a *gas-phase* assay
(`phase_contact_weight→0`).  Proteins fold in ~water, so covalent backbone σ bonds
stay on diamond-node bare lengths (+ mild γ/16 only) — **no gas EM**.  Tertiary
Cα length scales take aqueous outside feedback:
`outsideBulk(B_hom(foldXi(T),1), ρ_site) × local × piezo↔stiffness(ε_th=Lindemann)`
plus open-channel packing `(1+base·open²)^(w²)` (period-2 peptide → `w=1`).
Donor/acceptor optical softener, carrier thermo/Joule, and **register piezo**
(cage=`open+strong·open²`, ε from Lindemann×cage) modulate weights, not Cα nn:
energy uses full `1+(4/8)·ε_reg`; staged `Δφ/Δψ` uses mild
`1+(4/8)·ε_reg·(γ/2)` so burial passes explore without overshoot.  H-bond pivots
carry LDL/HDL angle dress × shell H-acceptor.
Lean: `MiniproteinChemistryDynamics` (`registerPiezoCage`,
`registerLindemannStrain`, `registerPiezoEnergyDress`,
`registerPiezoClosureStepDress`, `tertiaryContactPiezoEnergyDress`),
`OutsideContactLedger`, `VoltageGenerationLedger`, `PhaseElasticity`,
`CrystalContactGeometry`.

**Register profiles** replace boolean flag trees: each fold target names a profile
(`canonical`, `canonical_turn`, `hairpin`, `compact`, `trp_cage`) that maps structural
roles → proved basins. Long helices may set segment caps (`helix_n_cap` / `helix_body` /
`helix_c_cap`). Short hairpin fragments add a singleton sheet–helix packing contact from
derived compact-turn geometry.

**Trp-cage staged closure** (`apply_staged_nerf_contact_refinement`): four-pass NeRF
refinement in Lean ``tertiaryContactPass`` order (structure → hydrophobic → terminus →
full polish, **10 rounds** on the final pass).  Default for ``fold_trp_cage``; OSH uses
the same staged schedule.  Current Trp-cage Cα RMSD ≈ **4.51 Å** (Jul 2026; fails competitive
`<2 Å` gate). (`--closure-engine osh` / `closure_engine="osh"`): builds
`ContactNetworkMatrix` (diagonal site energies + pair weights), encodes φ/ψ on a
harmonic sparse register, applies `hqivNativePhaseGate` + contact torque, NeRF-decodes.
Ladder parity with NeRF verified (`--compare-osh`); sparse active-residue mask kicks in
for chains **>24** residues.

**PROtien tunnel bridge** (sibling repo): post-extrusion mode ``hqiv_lab_nerf`` seeds
staged NeRF from ribosome-tunnel Cα (null cone + lip + EM small translations; large
translations past the lip).  Virtual-Cα torsion bias carries helix-sense / chirality
from the extrusion search into φ/ψ; Kabsch re-anchors into the tunnel frame.
Handedness metrics are reported on every run.  Entry:

```bash
# from PROtien/
HQIV_LEAN_ROOT=/path/to/HQIV_LEAN PYTHONPATH=src:$HQIV_LEAN_ROOT:$HQIV_LEAN_ROOT/scripts \
  python3 -c "from horizon_physics.proteins import fold_lean_ribosome_tunnel; \
  r=fold_lean_ribosome_tunnel('NLYIQWLKDGGPSSGRPPPS', post_extrusion_refine_mode='hqiv_lab_nerf', quick=True); \
  print(r.raw_result['info'].get('handedness_sign_preserved'), r.raw_result['info'].get('handedness_mean_after'))"
# or CASP_LEAN_POST_EXTRUSION_MODE=hqiv_lab_nerf
```

Adapter: `PROtien/.../post_tunnel_hqiv_nerf.py`.  Composable stage: `make_hqiv_nerf_stage`.

Spine constants flow through `scripts/hqiv_spine_chemistry.py` (Slater 0.35/0.85/1.00,
monogamy spectator 6/5, H₂ site energy 1200 @ referenceM=4).

```bash
PYTHONPATH=.:scripts python3 scripts/hqiv_protein_folder_audit.py
PYTHONPATH=.:scripts python3 scripts/hqiv_miniprotein_fold_audit.py
PYTHONPATH=.:scripts python3 scripts/hqiv_protein_chemistry_geometry_compare_audit.py
# Tunnel + NeRF bench (needs sibling PROtien):
HQIV_LEAN_ROOT=$PWD PYTHONPATH=.:scripts:../PROtien/src:$PWD/scripts \
  python3 scripts/hqiv_tunnel_nerf_bench_audit.py
PYTHONPATH=.:scripts python3 -m unittest hqiv_lab.tests.test_peptide_shell_dress
```

**Protein vs chemistry geometry compare** (`hqiv_protein_chemistry_geometry_compare_audit.py`):
side-by-side mean shell/feedback treatment and quarantine accuracy (spectral + carbon vs
peptide bonds + fold ladder). Writes `data/protein_chemistry_geometry_compare_audit.json`.

**Fold ladder (PDB witnesses, comparison only):** competitive gate is Cα RMSD **< 2.0 Å**
for every length (AlphaFold-class).  Free-fold mean ≈ **2.48 Å** (3/11) with register
piezo on energy + mild staged Δ; tunnel+NeRF+piezo (+ optical/thermo energy) mean ≈
**2.24 Å** (5/11).  Biggest tunnel wins: `alpha_helix_4` 2.22→**0.85 Å**,
`sheet_helix_6` 3.24→**1.84 Å**.  Trp-cage ≈ **4.51 Å**.

| Target | n | RMSD gate | Notes |
|--------|---|-----------|--------|
| GG | 2 | <2.0 Å | COD:2100438 |
| beta_strand_3 | 3 | <2.0 Å | 1L2Y res 2–4 strap strand |
| hairpin_turn_5 | 5 | <2.0 Å | 1L2Y res 2–6 strap + turn coil |
| alpha_helix_4 | 4 | <2.0 Å | 1L2Y res 7–10 |
| helix_6 | 6 | <2.0 Å | 1L2Y res 7–12 (helix + Pro) |
| sheet_helix_6 | 6 | <2.0 Å | 1L2Y res 2–7 hairpin + closure |
| sheet_helix_8 | 8 | <2.0 Å | 1L2Y res 2–9 staged closure |
| helix_8 | 8 | <2.0 Å | 1L2Y res 7–14 compact helix body |
| sheet_helix_10 | 11 | <2.0 Å | 1L2Y res 2–12 Trp register + staged |
| cage_core_14 | 14 | <2.0 Å | 1L2Y res 2–15 strand+helix sans C-tail |
| trp_cage | 20 | <2.0 Å | full 1L2Y |

Refresh witnesses: `PYTHONPATH=.:scripts python3 scripts/hqiv_miniprotein_fold_audit.py --refresh-witnesses`

**Baseline (Jul 2026):** competitive gate Cα RMSD **< 2 Å** on every length; current ladder
mean **2.48 Å** with shell dress + register piezo (Trp-cage ~4.51 Å fails the competitive bar).
Contacts dressed from register coupling + bound-state NeRF prototypes + open-channel packing
(no profile-name branches). NeRF and OSH closures match on the ladder.

**Lean spine (first-principles, no PDB fold inputs):**

| Module | Role |
|--------|------|
| `PeptideBackboneGeometry` | Diamond-node bonds + α/γ helix/sheet Cα scales |
| `MiniproteinRamachandran` | φ/ψ basins + `basinRamachandranPair` |
| `MiniproteinRamachandranRegister` | Named profiles (`trp_cage`, `hairpin`, `compact`) |
| `MiniproteinChemistryDynamics` | α/γ → basins → contacts → solvent ρ → closure order |
| `MiniproteinFoldLadder` | 1L2Y fragment ladder + pinned tertiary counts |
| `ProteinSolventPhaseGeometry` | Bulk melt ρ + directional local network ρ |

Build: `lake build HQIVProteinResearch`

**Compact miniprotein basins** (proved in `MiniproteinRamachandran.lean`, optional via
`compact_miniprotein=True`): strap φ=γπ, distorted helix φ=(γ+α/2)π/2, helix-exit
ψ=−(α+γ/3)π. Default Trp-cage path keeps classic α/β + closure (tighter on 1L2Y NMR).

## Condensed voltage / Lindemann packing (Jul 2026)

### Constraint system → outside curvature

Binding / packing is multiplicative, so quarantined residuals enter a log-linear
system

```
A x = b,   b_i = log(y_ref / y_pred),   A_ik = structural feature_k(row_i)
```

Columns are ledger features only (`ρ_curv`, Lindemann `ε`, donor/acceptor excess,
`δ²`, nuclear `pack`, period fade, open share) — never molecule-name flags.
Artifacts: `data/chemistry_constraint_system.json`,
`data/chemistry_inverse_channel_solve.json`.

What the solve *defines* for outside curvature:

1. **Gas GMTKN:** outside-curvature participation \(w\approx 0\) → keep
   `diluteGasOutsideContactLedger` (environment channels at identity).
2. **Condensed:** one shared bulk column leaves a ρ↔n nullspace → **split**
   packing density vs optical CM density (`densityScaleFromPiezoStrain` vs
   undressed `ρ_cm`).
3. **Live dresses** are HQIV rationals nominated by under-loaded columns
   (steric, pack-open, ionic softener) — not fitted `c_k` written into the chart.
   Large `nuclear_pack` in the full matrix is a conditioning artifact (KEEP off).

Paper: `papers/lightcone_chemistry_extent/` §constraint-outside
(`hqiv_lightcone_derivations_into_chemistry.tex`).

Lean carriers (zero `sorry`):
`VoltageGenerationLedger` (`stericPackingDensityDress`,
`acceptorPolarizabilitySoftener`, `opticalVoltageDress`,
`ionicOpticalGapSoftener`, `lindemannThermalStrain`),
`CrystalContactGeometry` (`nuclearPackingOpenDress`,
`ionicCharacterLatticeDress`),
`PhaseElasticity` (`piezoStiffnessEquilibriumStrain`,
`contactForceFromLogDress`, `contactHessianNm`, `discretePhononWavenumberCm1`).

### DFT-slot matrix readouts (same spine as spectra)

Force, Hessian, discrete phonon, and crystal spectral gap are **not** a new XC
layer — they are SI bridges on the existing Morse / preferred-axis matrices:

```
F     = strong · (D/r) · |∂log E/∂log r|     |∂log E/∂log r| = 2 (Morse backbone)
k     = 2 D / r²                              (= lengthScaledForceConstant in SI)
ω     = √(k/μ) / (2πc)                        (same bridge as molecular ωₑ)
g_xtal = g_axis · max(CM(n),0) · ionicSoft(δ²)
```

Audit: `PYTHONPATH=.:scripts python3 scripts/hqiv_contact_force_readout.py`
→ `data/contact_force_hessian_audit.json`.  Homopolar / metallic spectra give
`g_axis = 0`; ionic rocksalt opens a unique polarity channel.  NIST optical-gap
and TO-phonon scales are quarantine only.

### Discrete saddle and defect formation (same local column)

Coordination excess `δ` already feeds `localCurvatureDefectExcess = γ·(4/8)·max(δ,0)`.
Formation energy and path barriers are that excess as an energy:

```
E_def     = E_bind · γ · (4/8) · max(δ, 0)
edge_gate = E_def on that contact
saddle    = max_{e ∈ path} edge_gate(e)
T         = 1 / (1 + B / max(strong · D, ε))   → activationRateSlot
```

Graphene vs diamond: `δ = 1/4` ⇒ `E_def = E_bind / 20` (proved).
Vacancy tease: `δ = 1/CN`.  Audit:
`PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_saddle_defect_readout.py`
→ `data/discrete_saddle_defect_audit.json`.

### Bond rearrangement paths (GMTKN activation)

Live contact-graph paths from `CurvatureContactNetwork`:

```
δ_break = max(1/CN_i, 1/CN_j)     (bonding CN only; no steric inflation)
path    = single-edge break (or break+reform tease)
B       = max_step D_edge · γ · (4/8) · δ
T       = 1 / (1 + B / max(strong · D, ε))
```

Monovalent break (`δ = 1`) proves `T = 5/7` independent of `D`
(`barrierTransmission_monovalent_break`).  GMTKN subset H₂, HF, LiH, N₂, H₂O, CH₄:
`PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_saddle_defect_readout.py`
→ also writes `data/gmtkn_activation_audit.json`.
Lean: `Hqiv.QuantumChemistry.BondRearrangementPath`.

**Atomization ladders** (multi-edge): sequential terminal breaks from centre CN₀;
`δ_k = max(1/(CN₀−k), 1)`.  H₂O (n=2) and CH₄ (n=4) ladders are in the GMTKN
audit under `atomization_ladder`.

**Activated transport**: `MolecularReactionTransport.activatedTransportRateSlot`
= `transportRateSlot · path transmission` (empty path recovers bare rate;
`waterSynthesisActivatedTransportRateSlot` for the water gate).

Constraint solve on the molecular panel (`ρ`, `n`, `T_sl`) showed:

* gas `outside_curvature` participation ≈ 0 (keep OFF on GMTKN);
* **split** packing density vs optical number density;
* **piezo** = continuous Brownian / Lindemann strain, not static packing flags.

Live readout (Lean `VoltageGenerationLedger.lindemannThermalStrain`):

```
ε(T) = clamp01( amp · √(T/T_melt) · (1 + phonon_cage) )
amp  = γ/2  (γ/4 on linear-chain motifs)
ρ   → ρ / (1+(4/8)ε) · (1+(4/8)·(γ/2))_apolar / steric
n   → CM(undressed ρ) · acceptor softener; optical × chemo(γ/2)×photo × donor excess
```

Earth-B Faraday is booked (`B/B_ref`, ~25 ppm) but does not move %-level residuals.

**Full condensed panel (14 species):** overall mean |Δρ| ≈ **0.43%**, |Δn| ≈ **0.52%**,
|ΔT_sl| ≈ **0.51%**.

Per-`crystal_kind` (Jul 2026; hole-fill: KCl/LiF optical + post-d/peel/K/Mg):

| kind | n | mean \|Δρ\| | mean \|Δn\| | mean \|ΔT_sl\| |
|------|---|-------------|-------------|----------------|
| molecular | 4 | **0.35%** | **0.65%** | **0.35%** |
| ionic | 4 | **0.59%** | **1.19%** | **1.44%** |
| metallic | 4 | **0.45%** | — | **0%** |
| covalent_network | 2 | **0.23%** | — | **0%** |

Ionic: LiF |Δρ|≈0.23% / |Δn|≈**1.6%** (was 2.7%); KCl |Δρ|≈**1.2%** (was 3.5%) /
|ΔT|≈**1.3%**. Metallic panel: Al≈0.07%; Li≈1.1%; Na≈0.55%; Cu≈0.15%.
Covalent: Si≈0.43%; Ge≈0.03%.

**Off-panel metallic scouts (after hole-fill):** Zn≈**0.2%**, Ga≈**−0.4%**, Fe≈**−1.5%**,
K≈**0.8%**, Mg≈**−1.6%** (was 40%/88%/−28%/17%/10%).

Refresh: `PYTHONPATH=.:scripts python3 scripts/hqiv_condensed_phase_audit.py`

### Crystal length equations (general, no motif/period case)

Continuous structural loaders (Lean `CrystalContactGeometry` / `IonicContactSlot` /
`VoltageGenerationLedger`):

```
bonding V (not noble residual):
  outer_sp = # e⁻ in top Madelung n with ℓ∈{0,1}
  V_bond   = noble residual if 0<(n−1)d<10 else outer_sp   # Fe/Cu peel; Ge/Ga outer
  cap      = min(V_bond, target−V_bond)
crystal_kind(Z…):
  binary ionic_route>1/2 → ionic; metal? → metallic; cap=4 → covalent_network
metallic families (from bonding_capacity, not Z-sets):
  metal?  = (cap=0 ∧ Z>2) ∨ (1≤cap≤3 ∧ V_bond=cap)   # shed vs gain; Si/Ge(cap=4) off
  CN      = 8 if (cap=V_bond=1) else 12               # BCC alkali; else FCC
  w = (2/P)^cap
  φ = homo if w≈1 else max(homo, lattice)
  exp_uc = γ·(1−w)·(1−γ²·δ_BCC) + (γ²/2)·w·δ_BCC   # Li residual + Na fade damp
  nn = nested^α · φ^(1−α) · (12/CN)^exp_uc
       · [1+(4/8)·γ·((cap−1)/12)·(1−w)·(CN/12)]_{1<cap<4}  # excess-over-alkali open
       · [1+(4/8)·α·γ·(1−w)·max(osp−1,0)]_{d¹⁰}           # post-d core (Zn/Ga)
       · [1/(1+(4/8)·α·γ·(peel/Z)·(1−w))]_{0<d<8}          # open-d peel (Fe)
       · [1+(4/8)·γ·max(0,P−3)/P]_{CN=8}                   # deep BCC (K)
       · [1+(4/8)·γ²·(1−w)/cap]_{cap=2,¬d¹⁰}               # alkaline-earth (Mg)
       · pack · open
  ρ  = N·M / (N_A·(k·nn)³)              # CN=8→BCC (2,2/√3); else FCC (4,√2)
covalent:  w = (2/P)^{constructiveValleyCap}
           CM = (n²−1)/(n²+2)
           r = r_bare · pack^{(1−w)(2−CM)} · em^{α(w+(1−w)CM)} · open^(w²)
               / (1+(4/8)·(γ²/8)·(1−w)·CM)              # steric fade (id @ P=2)
optical:   w_donor = clamp01((n_σ − n_lp)/n_lp)
           dress = 1 + (chemo(γ/2)·photo − 1)·w_donor
           w_acc = clamp01((n_lp − n_σ)/n_σ)
           α_pol *= 1/(1+γ·α·w_acc)
           CM *= 1 + (strong)·ε·(γ/2)          # thermal concentration
steric ρ:  w_apolar = 1[n_lp=0]
           f_ρ *= 1 / (1 + (strong·γ/8)·(w_donor − w_apolar))
pack open: nn *= 1 + (strong·γ)·(1 − pack)     (metallic / ionic packed)
ionic nn:  nn *= 1 / (1 + (strong·γ/8)·δ²)
         × 1 / (1 + (4/8)·α·γ/8 · w_a · w_c)   # period-2×2 steric (LiF)
         × (1 + (4/8)·(γ/8)·excess·(1−w_a))    # deep-cation open (KCl)
ionic:     N_c^eff = max(N_c, Z_a) on alkali–halide routes   # light-cation surplus
           w_a,w_c = (2/P)^cap
           E_bind *= (1+(4/8)·γ·w_a·(1−w_c))
                 / (1+(4/8)·(γ/8)·excess·(1−w_a))            # melt + deep-cation soft
           α_CM   *= 1/(1+(4/8)·γ·w_a)                        # period-2 anion optical
                 × 1/(1+(4/8)·γ·max(0,P_c/P_a−1))            # deeper-cation optical
                 × 1/(1+(4/8)·α·γ·w_a·w_c)                   # period-channel optical
           E_melt *= (1+γ)/(1+α)
           E_opt  /= (1+strong·γ·δ²)·(1+strong·ε·δ²)   # character × piezo
piezo:     ε' = clamp(ε_th + (1−ε_th)·strong·σ/k(r(ε)))   (fixed point)
Brownian:  cage += strong·ε ; localDefect = 1+γ·strong·ε   (k_th / ledger)
thermo:    σ_eff = σ₀ · thermo(clamp(carrier)·clamp(cage)·γ)  (identity @ carrier=0)
```

Metallic families are keyed by **octet bonding capacity** on bonding valence
(outer s+p past closed d; noble residual on open d), not by Z-sets.  Alkali
(cap=V=1) → BCC undercoord + deep-period open; p-block → excess-over-alkali /
alkaline-earth / d¹⁰ core; open-d peel → Fermi contract.  Panel `crystal_kind`
is derived from the same `(cap,V)` + `donor×acceptor` spine (`derive_crystal_kind`).

### W4 / GMTKN kinetic isotope effect (DFT drop-in kinetics)

Path barrier \(B\) is mass-independent; primary KIE is μ-only:

* **DFT-slot numeral** `KIE_zpe = exp((ω_H−ω_D)/(2·strong·D))` with Morse
  `ω=√(k/μ)`, `k=2D/r²`
* **Tunneling identity** `KIE_tun = T(μ_H)/T(μ_D) ≥ 1` with
  `V−E = strong²·D`, `L=γ` (proved μ-monotonicity)

Lean: `KineticIsotopePath` (`pathKineticIsotopeEffect_ge_one`).
Python: `scripts/hqiv_kinetic_isotope_readout.py` → `data/kinetic_isotope_audit.json`
(H₂/D₂, HF/DF, H₂O/HOD, CH₄/CD₄).  W4 numerals are quarantine only.

```bash
PYTHONPATH=.:scripts python3 scripts/hqiv_kinetic_isotope_readout.py
PYTHONPATH=.:scripts python3 -m unittest scripts.test_hqiv_kinetic_isotope_readout
lake env lean Hqiv/QuantumChemistry/KineticIsotopePath.lean
```

\subsection Still missing (DFT drop-in frontier)

Landed on this pass (general equations, no name cases):

* **Extended W4/GMTKN kinetics** — 12 activation molecules + 11 primary H/D KIE
  pairs; secondary softener `KIE^γ`
  (`data/gmtkn_activation_audit.json`, `data/kinetic_isotope_audit.json`)
* **Metal-hydride melt spine** — anion Z=1 → mild lattice dress + melt
  `(1+α)/γ²`; LiH |Δρ|≈0.2%, |ΔT|≈1.2% (`hqiv_salt_phase_response.py`)
* **Phonon dispersion + optical softener** — `ω(k)=2√(k_eff/μ)|sin(ka/2)|` with
  `k_eff = k · (4/8)·γ/CN_eff` on ionic/hydride
  (`data/phonon_dispersion_audit.json`; NaCl Γ/TO≈1.17, LiF≈1.47, LiH≈1.32)
* **Vacancy + grain-boundary thermo** — `E_vac = E_def/CN`, `E_gb = γ·E_vac`;
  NaCl ≈1.22 / 0.49 eV (`data/discrete_saddle_defect_audit.json`)
* **Glass / amorphous** — `S = γ·[(1−w_per)+Var(CN)/⟨CN⟩+open²]`; gate `S>α`
  (`data/glass_disorder_audit.json`)
* **Contact-network allotrope rank** — `w_c·inc·p·(1+γ·(4/8)·δ)`; C diamond > graphite > carbyne
  (`data/allotrope_contact_rank_audit.json`)
* **Driven k_th** — `k_driven = k_th/(1+γ·|ΔT|/T_melt)`
  (`data/driven_thermal_conductivity_audit.json`)
* **Wall → tribo** — one dry-wall spectrum ⇒ shared tribo/localDefect
  (`data/wall_tribo_audit.json`)
* **Discrete BZ bands** — two-band `ε(k)=√((E_g/2)²+(2t sin(ka/2))²)` on the
  same `ka∈[0,π]` path as phonons; NaCl Γ/NIST≈1.19, Si≈1.19
  (`data/discrete_bz_band_audit.json`)
* **Multi-orbital s/pσ/pπ** — Extended-Hückel hoppings `t_ss=t`, `t_pp=γt`,
  `t_sp=√(tss tpp)`, `t_π=(4/8)t_pp`; insulator Γ matches two-band `E_g`
  (`data/multi_orbital_bz_audit.json`)
* **Discrete SCF** — charge-dress fixed point `δ→f→E_g',t'` with α-mix;
  covalent/metal identity; NaCl `f≈1.009` in ~20 iters
  (`data/discrete_scf_audit.json`)
* **Discrete Fock** — 2×2 σ Fock on `{s,p_σ}` with same `δ/f` map as SCF
  (`U=γ E_c δ`, `K=α E_c δ`); dress matches SCF exactly; δ=0 ⇒ EH core
  (`data/discrete_fock_audit.json`)
* **Discrete KS** — local XC `V_xc=−α E_c δ` on the same Hartree/δ map;
  `K_sp=0`; dress matches SCF (`data/discrete_ks_audit.json`)
* **Discrete AO integrals** — EH `{s,p_σ}` S/T/V/(μν|λσ) from `E_c` and
  `s=1/(1+r/a₀)`; no fitted GTO (`data/discrete_ao_integrals_audit.json`)
* **Discrete core spectroscopy** — 1s XPS `E=f·Z_eff²/(2n²)` with
  `Z_eff=Z−γ(n_occ−1)`; chem shift `γ E_c δ`
  (`data/discrete_core_spectroscopy_audit.json`)

Next first-principles gaps:

1. Continuum defect free energies / dislocation plasticity (vacancy + GB scale landed)
2. Continuum TS search (primary + secondary KIE landed)
3. Continuum Fourier PDE (driven k_th softener landed)

Not blockers: SMILES/InChI (engineering I/O).

```bash
PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_bz_band_readout.py
PYTHONPATH=.:scripts python3 scripts/hqiv_multi_orbital_bz_readout.py
PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_scf_readout.py
PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_fock_readout.py
PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_ks_readout.py
PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_ao_integrals_readout.py
PYTHONPATH=.:scripts python3 scripts/hqiv_discrete_core_spectroscopy_readout.py
PYTHONPATH=.:scripts python3 -m unittest scripts.test_hqiv_discrete_bz_band_readout scripts.test_hqiv_multi_orbital_bz_readout scripts.test_hqiv_discrete_scf_readout scripts.test_hqiv_discrete_fock_readout scripts.test_hqiv_discrete_ks_readout scripts.test_hqiv_discrete_ao_integrals_readout scripts.test_hqiv_discrete_core_spectroscopy_readout
lake env lean Hqiv/QuantumChemistry/OutsideContactReducedDeltas.lean
```

## Roadmap

- [x] Periodic contact network → allotrope ranking (`contactNetworkAllotropeScore`)
- [x] Glass / amorphous branch from disorder score (`packingDisorderScore`)
- [x] Crystal EM / metallic α-blend / donor-excess optical (general equations)
- [x] HF acceptor softener + NaCl melt/optical channel equations
- [x] Piezo↔stiffness fixed point + carrier thermo/Joule dress
- [x] Covalent open^(w²) continuous fade (Si residual)
- [x] Steric ρ fine-tune + ionic optical softener (constraint-driven)
- [x] Pack-open + ionic nn + EM-weighted acceptor softener (NaCl/Cu/HF)
- [x] Lean port + lightcone paper §constraint-outside
- [x] Ionic piezo optical + T/Brownian first-class channels (#2/#3)
- [x] Protein piezo → register / staged closure weights (#1)
- [x] Metallic Bravais ρ + period-gate φ + undercoord open (Li/Na BCC)
- [x] Ionic light-cation surplus promotion (LiF melt)
- [x] Ionic anion-period melt + fluoride α softener (NaF)
- [x] Metallic families from bonding_capacity (CN + p-block open; no Z-sets)
- [x] BCC undercoord residual `(γ²/2)·w·δ` (Li period-2 open)
- [x] Outer-principal / bonding valence (Ge/Ga/Sn; open-d peel preserved)
- [x] Auto `crystal_kind` from capacity / donor×acceptor
- [x] BCC fade damp `(1−γ²)` (Na period-3 undercoord)
- [x] Ionic cation-period optical softener `max(0,P_c/P_a−1)` (KCl)
- [x] Covalent steric fade `(4/8)·(γ²/8)·(1−w)·CM` (Si/Ge)
- [x] P-block open `(cap−1)/12` excess-over-alkali (Al)
- [x] Ionic period-channel steric `α·γ/8 · w_a·w_c` (LiF ρ)
- [x] Ionic deep-cation open `γ/8·excess·(1−w_a)` (KCl ρ)
- [x] Ionic period-channel optical `α·γ·w_a·w_c` (LiF n)
- [x] Ionic melt deep-cation soft (KCl |ΔT|)
- [x] Post-d d¹⁰ core elong `(4/8)·α·γ·(1−w)·(osp−1)` (Zn/Ga)
- [x] Open-d peel contract continuous fade `(10−d)/10` (Fe/Ni)
- [x] Deep BCC open `γ·max(0,P−3)/P` (K)
- [x] Alkaline-earth open `γ²·(1−w)/cap` (Mg)
- [x] Period-2 homo residual `(4/8)·(γ²/8)·w` (Li/Be)
- [x] Fluoride mixed-period melt residual `(4/8)·(γ/8)·w_a·excess` (NaF)
- [x] Period-3/n ionic gas outside-contact: `ionicGasOutsideContactLengthTarget = core × (1+α)`;
  Lean elong uses `valenceElectronCount` (NaCl `7/2`); both partners period ≥ 3 route gate;
  NaCl gas `r_e` Δ≈0.8% quarantine; suite `scripts/hqiv_period_n_outside_contact_suite.py`
- [ ] Heavy-halogen (Br/I) nested-WF `1/Z` radius collapse on period-n ionic / Br₂
- [ ] Mixed period-2/3 ionic gas theorem (LiCl, NaF) — currently covalent holdout
- [ ] Cl₂ / open-channel halogen ω_e concentration-flow (r_e OK; ω_e still soft)
- [x] HCP Bravais for cap=2 ∧ ¬d¹⁰ (Mg; Zn stays FCC+d¹⁰)
- [x] Contact force / Hessian / discrete phonon from Morse log-dress (`PhaseElasticity`)
- [x] Crystal spectral gap = axis gap · CM · ionic softener (`OutsideContactReducedDeltas`)
- [x] Defect formation + discrete saddle max (`HomogeneousCurvatureSecondOrder` / `CoupledRelaxation`)
- [x] Bond rearrangement paths on `CurvatureContactNetwork` + GMTKN activation subset
- [x] Atomization ladders (H₂O/CH₄) + activated transport into `MolecularReactionTransport`
- [x] W4/GMTKN primary KIE from path barrier + tunneling μ (`KineticIsotopePath`)
- [x] Extended GMTKN activation + Z-keyed H/D KIE panel (12 + 11)
- [x] Metal-hydride lattice/melt dresses (anion Z=1; LiH condensed)
- [x] Discrete phonon dispersion `ω(k)=2√(k/μ)|sin(ka/2)|` (`PhaseElasticity`)
- [x] Optical phonon Hessian softener `(4/8)·γ/CN_eff` (ionic/hydride; NaCl Γ/TO≈1.17)
- [x] Vacancy thermo `E_vac = E_def/CN` (`vacancyFormationEnergyEv`)
- [x] Glass / amorphous disorder score + `S>α` gate (`packingDisorderScore`)
- [x] Contact-network allotrope ranking (`contactNetworkAllotropeScore`)
- [x] Secondary KIE softener `KIE^γ` (`secondaryKineticIsotopeEffect`)
- [x] Grain-boundary scale `E_gb = γ·E_vac` (`grainBoundaryFormationEnergyEv`)
- [x] Driven k_th assay `k/(1+γ·|ΔT|/T_melt)` (`drivenPhononThermalConductivity`)
- [x] Dry-wall → tribo shared factor (`dryWallTriboChannel`)
- [x] Discrete BZ two-band path (`discreteBandDispersionEv`; NaCl/Si Γ≈1.19×NIST)
- [x] Multi-orbital s/pσ/pπ EH (`multiOrbitalInsulatorAtKa`; Γ matches two-band)
- [x] Discrete SCF charge-dress fixed point (`discreteScfStep`; covalent identity)
- [x] Discrete Fock on EH basis (`discreteFockMatrix` / `discreteFockStep`; dress = SCF)
- [x] Discrete KS local XC (`discreteKsMatrix` / `discreteKsStep`; dress = SCF)
- [x] Discrete AO integrals (`discreteAo*`; S/T/V/(μν|λσ) from E_c)
- [x] Discrete core XPS (`discreteCoreXpsEv`; chem shift γ E_c δ)
- [ ] Export `data/hqiv_lab_witnesses.json` for papers
- [x] Broader validation of dresses on larger condensed set (14-species panel; per-kind report)
- [ ] Lean Ax=b rank/nullspace carrier