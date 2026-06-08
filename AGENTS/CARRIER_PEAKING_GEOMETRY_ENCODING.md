# Carrier peaking × geometry encoding (deferred for chemistry)

**Status:** Research note — **not wired** into `hqiv_qcomp_qaoa.py` or GMTKN55 binding charts.  
**Lean:** `Hqiv/QuantumComputing/CarrierPeaking`, `OSHoracleHQIVNative`, `ReverseShorClassicalOSHPeriodSelector`  
**Python:** `hqiv_quantum_gate_alias_probe.py`, `hqiv_reverse_shor_period_selector.py`

## Why this exists

QAOA today uses **computational qubits** (default 2 bits per DOF → 4 Å/angle levels). Carrier peaking operates on a **harmonic sparse register** `(L+1)²` with HQIV-native π-phase, flip/prune, logic-mirror witnesses, and 16/32-sector alias readout. **The same 6-bit geometry label can carry more bond-length structure in the carrier than in raw qubit measurement** — if and only if the **encoding** matches the gate basis.

## Encoding rules (from H₂O probes, Jun 2026)

| Encoding | Collisions (64 states) | Flip signal (L=11) | Bond₀ → 32-sector |
|----------|------------------------|----------------------|-------------------|
| Full card `0…63` on L=7 (Z₆₄) | 0 | **0** (closed under +1) | — |
| Bit-spread on L=11 | 0 | 64 | mixed |
| Sum of ℓ² bands | 45 | partial | poor |
| **Mixed-radix** `la·36 + lb0·9 + lb1` | **0** | 16 | **0,8,16,24** vs **2,10,18,26** vs … per Å bin |
| Contact-ℓ from Å | 31 | partial | physics-aligned (future) |

**Takeaway:** Bond lengths should map to **ℓ / sector / contact ξ**, not to bit order alone. Use **L ≥ 11**, **sparse** support, **injective** flat map. Shells `[4,3,1]` + `referenceM=4` for HQIV pivot.

## Suggested bridge (when chemistry is ready)

1. `decode_bitstring` → `(r₀, r₁, θ)` (unchanged).  
2. `geometry_to_carrier_flat(spec, x, L)` — prefer mixed-radix or TUFT contact-ℓ from `CentreGeometryFromTuft` / `contact_xi`.  
3. Seed amplitudes from QAOA probabilities; one `apply_gate_sparse_hqiv_native` step.  
4. Read 32-sector peaks + mirror witnesses → refine geometry before brute force.

## Not ready for production molecules yet

GMTKN55 **intramolecular** binding (~3–4% mean error on H₂, H₂O after `z_centre` fix) does **not** imply carrier readout is validated on bulk phases. Peaking was developed for **OSH / period-mirror** bookkeeping, not condensed-matter phase diagrams.

**Phase-transition goals** use a separate spine: `hqiv_thermodynamic_phase_from_tp.py` + `CURVATURE_CONTACT_NETWORK.md` (T,P → derived phase). See that doc for melt/boil limits; triple-point search is **not** implemented.

## Related

- `AGENTS/CURVATURE_CONTACT_NETWORK.md` — network binding, `(T,P)` phase output  
- `scripts/hqiv_qcomp_qaoa.py` — classical QAOA over discretized geometry  
- `papers/thermodynamics_arrow/` — arrow-of-time / shell-opening narrative (distinct from triple-point numerics)
