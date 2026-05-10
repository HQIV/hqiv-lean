# Quantum-circuit mapping for the lattice next-prime generator (probe only)

## 0. Does **not** work as an end-to-end algorithm

The **composed** classical procedure is **not** a correct or meaningful “next prime” / next-shell algorithm in any proved sense: `decompose_to_fano_moduli` is a fuel-bounded greedy **real** product walk, **not** a decomposition of `x`; `phi_t_step` is ignored in that walk; `spherePackingAtShell` and `rapidity_effect_on_sphere` are **not** wired into `next_prime_generator`; and `next_prime_generator` only feeds `decompose_last_shell` into `next_lattice_prime`. Treat the tables below as **metaphor** for future work, not a specification of something that runs correctly today.

---

This note is **design language for agents and implementers**: it relates the **combinatorial** pipeline in `Hqiv.Physics.LatticeNextPrimeGenerator` to a **possible** quantum-circuit layout and sparse-simulation story. **Nothing here is a Lean theorem** about quantum complexity, Grover speedup, or the correctness of a concrete gate set.

**Formal anchors (classical, in-repo):** `decompose_to_fano_moduli`, `decompose_last_shell`, `Hqiv.Geometry.spherePackingAtShell`, `rapidity_effect_on_sphere`, `next_prime_generator` / `next_lattice_prime` (`OctonionicZeta`). See [THEOREMS.md](./THEOREMS.md) for names.

**Lean QC fragments (actually proved):** `Hqiv.QuantumComputing.LatticeNextPrimeQCAlgorithm` — `fano_line_probability_mass_invariant` (cyclic `finRotate 7` preserves \(\sum_i p_i\) on `Fin 7`), `hqiv_gate_trans_preserves_ip` (composition of `HQIVGate`s preserves `discreteIp`), `lattice_next_prime_pipeline_stages_eq_four`. **Not** a full circuit equivalence to `next_prime_generator`.

---

## 1. Why the classical algorithm suggests a sparse circuit picture

The pipeline is deliberately **short and structured**:

- A **greedy walk** along shells `m = 0, 1, …` with Fano-tagged weights `l_f ∈ {1,2,3}` (`fanoLineWeight` / `fanoLineWeight_fano_vertex_of_shell_eq`).
- **Local arithmetic** on `effCorrected` (global detuning `δ` from `delta_auxiliary_phi_per_shell`), **divisor counts** on `m+1` (`Nat.divisors` in `spherePackingAtShell`), and a **scalar** rapidity–curvature slot in `rapidity_effect_on_sphere`.
- A **threshold jump** to the next shell via `next_lattice_prime` (ratio test on `eff`, not classical primality).

That structure invites a **register-based** story: a small Fano-related space, a shell counter, and phase / diagonal operations—**not** a claim that entanglement or Hilbert-space dimension has been analyzed in Mathlib.

---

## 2. Proposed quantum-gate mapping (high level)

| Stage | Classical scaffold | Circuit metaphor (not formalized) |
|-------|-------------------|-----------------------------------|
| **Decomposition** | `decompose_to_fano_moduli` (fuel-bounded; `phi_t_step` ignored in current Lean) | Prepare `x` (classical or controlled); unrolled loop of **controlled multiplies** by sparse `eff^l_f` factors; **7 residue classes** → unary or one-hot on **7 lines**; at most **fuel** steps, not “magically 7 gates” unless you fix unrolling. |
| **Sphere probe** | `spherePackingAtShell` | Comparator / **phase kickback** for divisor-count parity; **cyclic_outer_order = 7** is **fixed in Lean** (Fano partition story), not computed from `m`. |
| **Rapidity** | `phi_t_step`, `δslot` in `rapidity_effect_on_sphere`; zeta layer uses `cexp (I * phi_t_step m * δslot m)` elsewhere | **Diagonal** phase \(\exp(i\,\phi t(m)\,\delta_{\mathrm{slot}}(m))\) in the computational basis, controlled by shell (and optionally loaded classically). Maxwell `delta_theta_prime` is a **different** channel unless you **identify** slots. |
| **Next lattice prime** | `next_lattice_prime` = `Nat.find` on `eff` ratio | **Minimum-finding** / comparator tree on a **bounded** shell range; narrative may mention Grover-style search—**not** proved in this repository. |

**Registers (paper labels only):**

- **Fano line:** 7 lines / one-hot or unary encoding (Lean: `FanoVertex = Fin 7`).
- **Shell index:** \(\lceil \log_2 M \rceil\) bits for a user-chosen cap `M` (Lean: `fuel` and `next_lattice_prime` search space are separate parameters).
- **Phase / rapidity:** real scalars or classical controls (`phi_t_step`, `IntegratedScalarCurvatureSlot` / `δslot` in other modules).

---

## 3. Sparse simulation (narrative)

**Design intent:** if most amplitude stays on a **low-dimensional** subspace (sparse Fano configuration + localized shell updates), **tensor-network / MPS** or **sparse state-vector** methods may be practical in **implementation** work. This is **engineering expectation**, not a **proved** bond dimension or entanglement bound tied to `decompose_to_fano_moduli`.

---

## 4. Fit with the rest of HQIV

- **Oracles:** The Lean functions above are **classical** definitions; a circuit would **call** them as classical reversible logic or **compile** arithmetic into gates—outside Mathlib’s scope here.
- **Already typed:** `phi_t_step`, curvature slots (`SpatialSliceRapidityScaffold`, `DivisionAlgebraZetaScaffold`), Fano residues (`zeta_HQIV_eq_sum_Fano_residue_classes`, mod-7 split).
- **Complexity claims:** Statements like “\(\mathcal{O}(\log x)\) classically” or “\(\mathcal{O}(\mathrm{polylog}\, x)\) quantumly with Grover” are **not** formalized; `next_lattice_prime` is `Nat.find` with **existence** lemmas from `OctonionicZeta`, not a complexity certificate.

---

## 5. Related docs

- [MANIFOLD_ZETA_ROADMAP.md](./MANIFOLD_ZETA_ROADMAP.md) — lattice vs manifold scope.
- [QUANTUM_CHEMISTRY_OUTPUTS.md](./QUANTUM_CHEMISTRY_OUTPUTS.md) — broader quantum-chemistry output architecture (orthogonal to this circuit sketch).
- `Hqiv/QuantumComputing/*` — existing discrete / octonionic tooling; **no** automatic bridge to `LatticeNextPrimeGenerator` unless you add imports and proofs elsewhere.
