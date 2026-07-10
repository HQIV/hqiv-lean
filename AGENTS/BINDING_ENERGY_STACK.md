# Binding-energy stack (canonical vs superseded)

## Canonical quantitative readout (use this)

| Layer | Python | Lean | Data witness |
|-------|--------|------|--------------|
| **GMTKN55 / W4-17 binding** | `scripts/hqiv_dynamic_binding_chart.py` | `Hqiv.QuantumChemistry.DynamicBindingChart` | `data/dynamic_binding_chart.json` |
| Shell routing | `scripts/hqiv_shell_aware_binding.py` | `DynamicBindingChart`, `LiHDynamicBinding` | (in chart JSON `shell_readout`) |
| Contact / phase network | `scripts/hqiv_curvature_contact_network.py` | `Hqiv.QuantumChemistry.CurvatureContactNetwork` | — |
| Spectroscopy (Dₑ, ωₑ, …) | `scripts/hqiv_molecular_spectroscopy.py` | `Hqiv.QuantumChemistry.MolecularSpectroscopy` | — |
| Hartree / QPE bridge | `scripts/hqiv_molecular_hamiltonian.py` | `Hqiv.QuantumChemistry.MolecularEnergyBridge` | `scripts/hqiv_targets_h2_lih.py` |
| OSH sparse quantum carrier | `scripts/hqiv_osh_integrated.py`, `osh_gate_factorization.py` | `Hqiv.QuantumComputing.OSHoracle`, `AtomEnergyOSHoracleBridge` | — |

**Formula (parameter-free):**

```
E_bind = η₂ · surplus_dimless · geomean(tuftVev) · geometry_alignment · dynamicBindingCurvatureFeedbackAtXi(ξ) · EV_per_λ
```

H₂ @ reference: **4.495 eV pred vs 4.478 eV NIST (+0.38%)**; tier-0 suite mean |err| ≈ 2.5%.

Foundation program runs the chart via `scripts/hqiv_foundation_program.py`.

## Superseded for quantitative eV (bookkeeping only)

| Layer | Python | Lean | Notes |
|-------|--------|------|-------|
| Inside/outside curvature projection | `scripts/hqiv_bond_state_network.py` | `Hqiv.QuantumChemistry.BondStateNetwork` | **Not** the GMTKN55 readout; retains network trace identity `closed − separated = edge + hyper` |

`BondStateNetwork` remains valid Lean **structure** (trace bookkeeping). Do **not** use `data/bond_state_network_chart.json` for binding benchmarks — it omits η_p, TUFT vev geomean, and curvature feedback.

See `archive/bond_state_network/README.md`.

## OSH oracle ↔ molecular energy

The OSH pipeline is the **quantum** execution path on the same diagonal site-energy spine:

1. `AtomEnergyOSHoracleBridge.sparseRegisterOfShells` — one sparse ket per fragment shell.
2. `OSHoracle` — expand → gate → flip-detect → prune; norm preserved (`SparseCertifiedGate.preserves_discreteNormSq`).
3. `MolecularEnergyBridge.oshSparseMolecularEnergyObservable` — diagonal energy sum on that register (QPE target observable).
4. `MolecularEnergyBridge.qpeTargetTotalEnergyHartree` — dissociation BE (eV, chemist) → total Hartree for comparison with STO-3G FCI / hardware QPE papers.

Classical FCI reference: `hqiv_molecular_hamiltonian.example_h2_sto3g_fci` (−1.137 Ha total @ R ≈ 1.4 Bohr).
