# Phase geometry → curvature density

**Lean:** `Hqiv.QuantumChemistry.PhaseGeometryDensity`  
**Homogeneous κ₆:** `Hqiv.Physics.HomogeneousCurvatureSecondOrder`  
**Python:** `scripts/hqiv_phase_geometry_density.py`  
**Paper:** `papers/nucleon_binding/hqiv_nucleon_binding_from_composite_trace.tex` §phase-geometry-density (v3)

## Pipeline

```
molecule + allotrope (e.g. H2O + Ih)
  → PhaseUnitCell (a, b, c, Z, M)
  → ρ_mass = Z·M / (N_A·V_cell)
  → ρ_curv = clamp(ρ_mass / ρ_liquid_ref)
  → homogeneousCurvatureBudgetAtXi(ξ, ρ_curv)
  → bindingCurvatureFeedbackSecondOrderHomogeneous (melt / chart)
```

**Orbital extension** (same spine, no shell-4 readout pin):

```
(M, R, r_encounter)
  → w_bulk = 1 / (1 + (r/R)²)
  → ρ_local = clamp((R/r)²)
  → ρ_orb = w_bulk + (1 − w_bulk)·ρ_local
  → B_hom(ξ_prop, ρ_orb)   with ξ_prop = 1 (solar-system band)
  → flybyDynamicKappaPhiFromPhase, orbitalCurvatureMassDeltaFraction
```

Lean bridge: `Hqiv.Physics.OrbitalFlybyScaffold`.
Python: `orbital_flyby_readout()` / `hqiv_orbital_flyby_omaxwell.phase_geometry_source`.

No Avogadro atom counting; geometry witnesses only.

## Material response (n, ε_r, k_th, σ)

**Python:** `scripts/hqiv_phase_material_response.py`  
**Tests:** `scripts/test_hqiv_phase_material_response.py`  
**Lean:** `Hqiv.QuantumChemistry.PhaseMaterialResponse`

| Target | HQIV inputs |
|--------|-------------|
| Refractive index n | Clausius–Mossotti + binding-softness α + ρ_curv + Ih opening (4/3) |
| Dielectric ε_r | n² |
| Thermal k_th | phonon slot: ρ, c_spec, v_s, ℓ, G_eff(θ), B_hom |
| Ionic σ | carrier_fraction × exp(−E_a/kT); pure water → 0 |
| C_p,mol | (3 n_atoms) R × (1+α if solid) × B_hom |
| L_fusion | E_melt × N_A × n_inter × (4/3)²/(1+α) |
| η (liquid) | Eyring: (ℏ/kT) exp(E_melt/kT) × contact stiffness / span³ |
| Δn (ice Ih) | CM split ±(c/a−1)·c_Rindler/20 → n_o, n_e |

```bash
PYTHONPATH=scripts python3 scripts/test_hqiv_phase_material_response.py
python3 scripts/hqiv_phase_material_response.py H2O --phase solid
python3 scripts/hqiv_phase_material_response.py H2O --phase liquid
lake build Hqiv.QuantumChemistry.PhaseMaterialResponse
```

## Build

```bash
lake build Hqiv.QuantumChemistry.PhaseGeometryDensity
python3 scripts/hqiv_phase_geometry_density.py H2O
```
