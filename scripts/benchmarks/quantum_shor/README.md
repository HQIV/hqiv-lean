# Quantum Shor layout benchmark (reference data)

Transpiled comparison of **textbook Shor** vs **orthogonal-diagonal sparse** schedules with real Fourier modular exponentiation (`../../shor_modexp.py`).

## Files

| File | Description |
|------|-------------|
| `shor_layout_benchmark.csv` | Machine-readable reference table |
| `shor_layout_benchmark.md` | Human-readable table + metadata |
| `shor_layout_benchmark.json` | Full run metadata + rows |
| `generate_reference_benchmark.py` | Regenerate all three |

## Reproduce

```bash
# Unified table (structural + gate-expanded columns)
python3 HQIV_LEAN/scripts/benchmarks/quantum_shor/generate_reference_benchmark.py \
  --min-bits 15 --max-bits 25

# Gate pass only (merge into existing JSON after structural run)
python3 HQIV_LEAN/scripts/benchmarks/quantum_shor/generate_reference_benchmark.py \
  --gate-only --min-bits 15 --max-bits 25

# Push to 28–32 bits (mod-exp disk cache under scripts/.cache/modexp/)
python3 HQIV_LEAN/scripts/benchmarks/quantum_shor/generate_reference_benchmark.py \
  --min-bits 28 --max-bits 32

# Noisy Aer (20- and 25-bit representatives)
python3 HQIV_LEAN/scripts/benchmarks/quantum_shor/quantum_shor_noise_sim.py --shots 512
```

Requires `qiskit` in the active environment.

## Hybrid CLI

Classical factorization with optional quantum metrics:

```bash
python3 HQIV_LEAN/scripts/hqiv_reverse_shor_period_selector.py 143 --quantum-metrics
```
