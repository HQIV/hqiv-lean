# Chemistry dynamics proof program (post-TUFT integration)

**Status:** Pre-TUFT chemistry targets (site energy, bond length, centre angles) were
scaffolded on `HQIVAtoms` / `HQIVMolecules` / `FiniteSiteQuantumChemistry` with
**external** geometry and numeric anchors (`waterBondAngleDeg = 104.5` by `rfl`).

After T12/T13 + `HopfShellBeltramiMassBridge` + `TrappedCasimirBindingBridge` +
`DynamicBindingChart`, the **same ξ-ladder dynamics** that closes leptons, EW bosons,
and vev-pinned hadrons should close **molecular** readouts — no new fitted `κ_bind`.

**Parent docs:** [`TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md`](./TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md),
[`TUFT_SHELL_ONTOLOGY.md`](./TUFT_SHELL_ONTOLOGY.md),
[`TUFT_HOPF_SPECTRAL_MINING.md`](./TUFT_HOPF_SPECTRAL_MINING.md),
[`CURVATURE_CONTACT_NETWORK.md`](./CURVATURE_CONTACT_NETWORK.md).

---

## 1. One dynamic spine (what changed)

| Layer | Pre-TUFT | Post-TUFT (use now) |
|-------|----------|---------------------|
| Per-shell coupling | `alphaEffAtShell m` (φ ladder) | Same, plus **`trappedCasimirCouplingCell m = alphaEffAtShell m`** (`TrappedCasimirBindingBridge`) |
| Scale / vev | bare `tuft_vev_factor_at_xi` | **`heavy_lepton_gap_at_xi`** × **`effective_casimir_scale_at_xi`** (inner T12 / outer T13) |
| Contact ξ | ad hoc `m+1` mean | **`dynamicComptonXiMean`** on electronic triplet; BBN **`curvature_budget_at_xi`** |
| Second order | none / fitted κ | **`tuftLapseConcentrationAtXi`** (κ₆), **`dynamicComptonEtaSecondOrder`** (p shell) |
| Shell labels | nuclear `m_nuc(A)` confused with valence | **TUFT chart** `tuftWeak/Strong/HeavyChartShell` + Compton slots `(4,3,1)` |

**Chemistry binding formula (already in Lean/Python, now fully TUFT-dressed):**

```text
E_bind = η₂(η, triplet) · surplus · geomean(tuftVevNetworkedAtCluster) · geom(θ) · (1 + κ(ξ)·C_rel)
```

All factors are rational/HQIV except **comparison** to GMTKN55 (external benchmark only).

---

## 2. Electronic Compton slots ↔ TUFT chart (ontology target)

Prove **assignments** as theorem targets, not Python tables.

| Chemist slot | Compton `m` (LiH/H₂O spine) | TUFT chart row | Hopf winding |
|--------------|----------------------------|----------------|--------------|
| H `1s` | **1** | below weak chart (anchor rung) | — |
| Centre `2p` | **3** | `tuftStrongChartShell` | 2 |
| Centre `2s` | **4** | `tuftHeavyChartShell` | 3 |
| Homonuclear period-2 | **4** | heavy | 3 |

Lean home: new `Hqiv.QuantumChemistry.ElectronicValenceFromTuftChart`.

**Target theorem E-TUFT:**

```lean
def electronicComptonShell (slot : ElectronicSlot) : ℕ :=
  match slot with
  | .h1s => 1
  | .centre2s => tuftHeavyChartShell
  | .centre2p => tuftStrongChartShell
```

**Target theorem E-TUFT-ξ:** `latticeFullModeEnergy m = latticeFullModeEnergy_xi (xiOfShell m)` (already `ContinuousXiPath`).

**Target theorem E-TUFT-site:** `lihValenceSiteEnergyTrace 4 3 1` equals orbital-weighted sum of `trappedCasimirEnergyAtShell` on those rows (link site energy to trapped Casimir, not only φ·modes).

---

## 3. Site energy — proof chain (nail down first)

### Already proved

- `latticeFullModeEnergy_closed_form`: `4·(m+2)·(m+1)²`
- `latticeFullModeEnergy_nonneg`
- `lihValenceSiteEnergyTrace_eq` with `p` degeneracy **3**
- `h2SiteEnergyTrace_eq`, `h2oOutput_eq_sum_siteEnergies`
- `trappedCasimirCouplingCell_eq_alphaEffAtShell`

### Post-TUFT targets (priority S1–S6)

| ID | Theorem | Module |
|----|---------|--------|
| **S-TUFT-1** | `siteEnergyAtShell m = trappedCasimirEnergyAtShell m` (same φ/2 × modes spine) | `TrappedCasimirBindingBridge` → `FiniteSiteQuantumChemistry` |
| **S-TUFT-2** | `comptonSiteEnergyDimless m = latticeFullModeEnergy m` is the **IR window driver** for `omegaCompton` in `ComptonIRWindow` | `ComptonIRWindow` + `LiHDerivation` imprint lemmas |
| **S-TUFT-3** | `orbitalWeightedSiteEnergyTrace` degeneracy = `s2Degeneracy ℓ` (proved bridge to `SphericalHarmonicsBridge`) | `FiniteSiteQuantumChemistry` + `S2BindingGeometry` |
| **S-TUFT-4** | `h2oOrbitalSiteEnergyTrace` = `E(4) + 3·E(3) + 2·E(1)` from `ElectronicValenceFromTuftChart` | new `H2O.lean` |
| **S-TUFT-5** | `tuftVevFactorAtComptonShell m A` = `tuft_vev_factor_at_xi (ξ(m)) · (clusterMass/A·m_p)^(1/3)` with **proved** monotonicity in deficit | `DynamicBindingChart` + `NuclearCurvatureBinding` witness |
| **S-TUFT-6** | No external `ℏ` in **dimensionless** chart: Compton ω from site energy + `phaseTheta` only; ℏ only in SI export lemma | `ComptonNuclearTorus` bridge |

**Python alignment:** `hqiv_electronic_valence_shells.py` becomes a witness exporter for proved `ElectronicValenceFromTuftChart`, not a policy table.

---

## 4. Bond lengths — dynamics from ξ and valley EM

### Existing HQIV structure

```lean
valleyPotentialEM m n₁ n₂ Z_eff r =
  valleyPotential n₁ n₂ + α_EM·Z_eff/r

bohrRadiusOfShell m Z μ = ℏ² / (μ · coulombStrengthShell m · Z)
-- coulombStrengthShell m = alphaEffAtShell m
```

`foldEnergy` on `TorqueTree` sums `bondValleyEM` + atomic field energies.

### Post-TUFT dynamic closure

**Replace** Python `1/(1 + r/a₀)` with a theorem:

| ID | Theorem | Content |
|----|---------|---------|
| **L-TUFT-1** | `bondEquilibriumRadius m Z_eff μ` | Stationary point of `r ↦ valleyPotentialEM … Z_eff r` for fixed Casimir surfaces |
| **L-TUFT-2** | `bondEquilibriumRadius_eq_bohrShell` | Leading term matches `bohrRadiusOfShell m Z μ` when valley overlap balances at `R_m m` |
| **L-TUFT-3** | `distanceWeight r m = R_m m / r` (or `G_eff` contact phase at `θ(r)`) | `HQIVNuclei` + `ComptonIRWindow` |
| **L-TUFT-4** | `foldEnergy_minimizing_radius` | `∂(foldEnergy)/∂r = 0` on two-leaf `TorqueTree` with **dynamic** `alphaEffAtShell (electronicComptonShell …)` |
| **L-TUFT-5** | `h2_bond_length_angstrom` / `oh_bond_length_angstrom` | **Corollaries** after unit bridge `eVPerLambdaUnit`; compare to chemistry within X% (witness, not `rfl`) |

**ξ dress:** contact radius uses `ξ_contact = dynamicComptonXiMean triplet` and

```lean
alphaEffAtContact m c = alphaEffAtShell m c * effective_casimir_scale_at_xi (xiOfShell m) / effective_casimir_scale_at_xi xiLockin
```

(open target; structurally required for temperature-run bonds).

Lean home: `Hqiv.Physics.TorqueTreeEquilibrium` (new).

---

## 5. Centre angles — wavefunctions + torque tree + TUFT κ₆

### Existing (pre-TUFT)

- `hydrogenGroundStateOfShell`, `atomOrbital`, `slaterDetTwo` — **exchange proved**, eigenpair still `Prop`
- `allowed_binding_angles_minimize_budget` — **θ = 0** minimizes `κ(1 - cos θ)` (local)
- `valleyAlignmentWeight` — dihedral on **Δθ**
- `water_bond_angle_from_minimization` — **anchor `rfl`**, not dynamics

### Post-TUFT dynamic closure

Centre angle = **stationary phase** of peripheral bonds on a `TorqueTree.branch` with:

1. **κ** from `tuftHopfKappa6AtXi ξ_contact` (same as binding feedback spine)
2. **Ideal angle** from **repulsion** of `n` equivalent `bondValleyEM` legs in **p** channel (degeneracy 3)
3. **Wavefunction** input: `atomActivePairSlater` on `AtomicShellSpec` for O centre (2s, 2p₁, 2p₂ indices)

| ID | Theorem | Content |
|----|---------|---------|
| **A-TUFT-1** | Promote `groundStateEigenpairAtShellTarget` → theorem (radial 1D lemma first) | `Schrodinger.lean` |
| **A-TUFT-2** | `foldEnergyWithDihedral κ θ` global minimum at **θ* = θ_VSEPR(n_bonds, n_lp)** for 2-leaf water tree | `TorqueTreeEquilibrium` |
| **A-TUFT-3** | `θ_VSEPR` matches **104.5°** from HQIV-only inputs (witness bound, replace `waterBondAngleDeg` anchor) | `HQIVMolecules` refactor |
| **A-TUFT-4** | `idealCentreAngle` = argmin **Σᵢ κ · (1 - cos(θᵢ))** subject to `Σ ℓᵢ = 1` on p subspace | `CentreGeometryFromTuft.lean` |
| **A-TUFT-5** | Link `axisAngle k = π/(2k)` to **p₁/p₂** splitting when `Ω m = k` on `tuftStrongChartShell` | `OctonionSphereFourierPatch` → chemistry |
| **A-TUFT-6** | `valleyAlignmentWeight θ θ* = 1` at stationary `θ*` (already `valleyAlignmentWeight_at_ideal`; need `θ*` derived) | `S2BindingGeometry` |

**η participation:** keep `ComptonIRWindow` for **radial** IR time; **angular** participation is **torque-tree** + **κ₆**, not a second fitted angle table.

---

## 6. Module graph (build order)

```text
TuftShellChart.lean                    [exists]
TrappedCasimirBindingBridge.lean       [exists]
HopfShellBeltramiMassBridge.lean       [exists]
        ↓
ElectronicValenceFromTuftChart.lean    [NEW — E-TUFT]
        ↓
FiniteSiteQuantumChemistry.lean        [extend S-TUFT-1..3]
H2O.lean / CentreGeometryFromTuft.lean [NEW — S-TUFT-4, A-TUFT-4]
TorqueTreeEquilibrium.lean             [NEW — L-TUFT-*, A-TUFT-2/3]
DynamicBindingChart.lean               [link second-order ↔ Tuft explicitly]
        ↓
BondedHorizonCasimirMoleculeBench.lean [surplus splits with proved geometry]
```

**Python:** one witness script `hqiv_chemistry_tuft_dynamics_witness.py` exports only proved lemmas (radii, angles, site energies) — chart stops hard-coding Å and degrees except in **comparison** columns.

---

## 7. What to retire in Python (as proofs land)

| Current import | Replace with |
|----------------|--------------|
| `BondGeometry.distance_angstrom` fixed | `bond_equilibrium_radius_angstrom(m, Z, …)` witness |
| `infer_centre_bond_angle_rad("H2O", …)` preset | `ideal_centre_angle_rad(VSEPR_spec)` witness |
| `valence_shells_for_nucleus(z, m_nuc)` for contacts | `electronic_compton_shells` from TUFT chart |
| `surplus_dress` lone-pair / hyperclosure heuristics | theorems from `foldEnergy` stationary excess on atomization split |
| Nuclear `m_nuc` on **Compton** nodes | nuclear rows **diagnostics only**; dynamics on electronic `m` |

---

## 8. Immediate next Lean PR (smallest shippable)

1. **`ElectronicValenceFromTuftChart.lean`** — defs + `lihCompton_eq_tuftChart` + `h2oOrbitalSiteEnergyTrace`
2. **`TorqueTreeEquilibrium.lean`** — state `minimizesFoldEnergy` + prove `allowed_binding_angles_minimize_budget` is 1D subcase
3. Refactor **`water_bond_angle_from_minimization`** to implication `θ_VSEPR_water = 104.5` **from** `minimizesFoldEnergy`, deprecate raw anchor def
4. Wire **`dynamicBindingCurvatureFeedbackSecondOrderAtXi`** into chart docstring as default for bulk; chemistry uses first-order at `ξ_contact` + H₂ `C₂` dress (already Python)

---

## 9. Success criteria (dynamics “nailed down”)

- [ ] **Site energy:** LiH / H₂O traces proved from `latticeFullModeEnergy` on TUFT-chart shells; Python matches closed form with **zero** geometry imports for energy terms.
- [ ] **Bond length:** H₂ and O–H `r*` from `foldEnergy` stationary point; GMTKN55 comparison column only.
- [ ] **Angle:** H₂O `θ*` from `foldEnergyWithDihedral` on 2-leaf tree; within agreed witness band of 104.5° without `rfl` on the definition.
- [ ] **Binding chart:** GMTKN55 errors unchanged or better with **derived** `r, θ`; no new scalar parameters.
- [ ] **Docs:** `CURVATURE_CONTACT_NETWORK.md` points here; TUFT papers cite **electronic** chart, not nuclear drum.

---

## 10. One-sentence thesis

**Molecular geometry is not input data; it is the stationary configuration of the same
inner/outer Casimir + Hopf κ₆ dynamics that already fix the mass ladder at ξ_lock — evaluated
on the weak/strong/heavy electronic chart rows instead of imported Å and VSEPR tables.**
