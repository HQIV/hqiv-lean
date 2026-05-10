# Quantum Chemistry Outputs Roadmap (Target Architecture)

This document records the intended output architecture for the quantum-chemistry stack.

Design goal split:

- **Lean side:** prove qualitative structure and conservation constraints (informational consistency, compositional laws, formal identities).
- **Python/numerical side:** produce quantitative observables that match experiment-like behavior, with explicit uncertainty propagation.

The layers below define what we want to build toward.

## 1) Foundational Outputs (Low-Level Primitives)

These are raw outputs required by every higher layer.

### One- and two-electron integrals

- Overlap matrix: `S_{μν} = <φ_μ | φ_ν>`
- Kinetic energy matrix: `T_{μν}`
- Nuclear attraction matrix: `V_{μν}`
- Two-electron repulsion: `(μν|λσ)` (chemist or physicist notation)
- Output format target: dense/sparse arrays; AO and/or MO basis.

### Basis-set data

- Contracted GTO/STO primitives
- Shell metadata (`s,p,d,...`), exponents, contraction coefficients
- Nuclear coordinates + charges (geometry + basis = full molecular specification)

### Core matrix outputs

- Core Hamiltonian: `H_core = T + V`
- Density matrices (initial and converged):
  - 1-RDM (`P` / `D`)
  - optional 2-RDM for post-HF
- Fock matrix (or KS matrix for DFT) at each SCF iteration
- Orbital coefficients `C` and orbital energies `ε_i`

Requirement: these outputs should be public APIs / reusable values (no forced recomputation).

## 2) Intermediate Outputs (Derived Quantities)

Computed from foundational outputs; reused by high-level properties.

- Total electronic energy and components:
  - HF / DFT energy
  - correlation energy (MP2, CCSD, ...)
  - nuclear repulsion energy
- Molecular orbital data:
  - occupied/virtual orbital energies
  - HOMO/LUMO and gap
  - MO coefficients
- Natural orbitals + occupations (from 1-RDM diagonalization)
- Population analyses:
  - Mulliken / Lowdin / Hirshfeld / NBO
- Multipole properties:
  - dipole (and higher multipoles if requested)
- Response properties:
  - polarizability / hyperpolarizability
- Vibrational layer:
  - Hessian
  - harmonic frequencies + normal modes
- Thermodynamic corrections:
  - ZPE, H, S, G (with specified `T`, `P`)

## 3) High-Level User-Facing Outputs

Top-level deliverables for users and publications.

- Optimized geometry + convergence diagnostics
- Reaction energies and barriers
- Spectroscopy:
  - IR / Raman
  - UV-Vis (TD-DFT/EOM-CC)
  - NMR shifts/couplings
  - ESR/EPR (`g`-tensor, hyperfine)
- Excited-state outputs:
  - vertical excitations
  - oscillator strengths
  - state-specific geometries (if supported)
- Standard-condition thermochemistry (298.15 K, 1 atm)
- Wavefunction exports:
  - Molden / wfn / wfx / checkpoint
  - cube files (density/orbitals/ESP)
- Human-readable summary table:
  - energy breakdown
  - population summary
  - key orbital energies
  - vibrational outputs
  - thermochemistry

## 4) Practical Outputs and Interoperability

### File I/O targets

- Inputs: XYZ, Gaussian `.com/.gjf`, ORCA `.inp`, PySCF-like Python dict inputs
- Outputs: Molden, wfn, fchk, XYZ, log-style text, JSON, HDF5

### Logging and runtime diagnostics

- SCF convergence table
- timing breakdown
- memory usage

### Python-facing object model

Target return object should expose standard attributes such as:

- `.energy`
- `.mo_energies`
- `.dipole`
- `.frequencies`
- `.thermochemistry`

### Visualization hooks

- Orbital/density data products
- Normal-mode animation payloads
- Data-ready hooks for Py3Dmol, VMD, Matplotlib

## Error-Bar Policy (Cross-Cutting)

Uncertainty bars should propagate from foundational parameters to intermediate and high-level outputs.

- Maintain explicit uncertainty metadata on input and derived quantities.
- Report uncertainty alongside central values (`±σ` / interval-based summaries).
- Keep propagation reproducible (deterministic seeds for Monte Carlo or transparent analytic propagation when available).

